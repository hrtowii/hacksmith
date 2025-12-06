definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"

definition n2s :: "nat list ⇒ nat" where
  "n2s pkt = (if length pkt ≥ 3 then pkt ! 1 * 256 + pkt ! 2 else 0)"

fun heartbeat_process :: "nat list ⇒ (nat × nat × nat)" where
  "heartbeat_process pkt = (
    let padding = 16 in
    if pkt ≠ [] ∧ pkt ! 0 = TLS1_HB_REQUEST then
      let payload = n2s pkt in
      let buffer_alloc = 1 + 2 + payload + padding in
      (* Return (response_payload_length, allocated_memory, response_padding) *)
      (payload, buffer_alloc, padding)
    else
      (0, 0, padding))"

lemma payload_length_check:
  assumes "length pkt ≥ 3"
  and "pkt ! 0 = TLS1_HB_REQUEST"
  shows "fst (heartbeat_process pkt) ≤ length pkt - 3"
  using assms by (simp add: n2s_def TLS1_HB_REQUEST_def)

lemma memory_allocation_check:
  assumes "length pkt ≥ 3"
  and "pkt ! 0 = TLS1_HB_REQUEST"
  shows "fst (snd (heartbeat_process pkt)) = 1 + 2 + n2s pkt + 16"
  using assms by (simp add: n2s_def TLS1_HB_REQUEST_def)

lemma padding_check:
  shows "snd (snd (heartbeat_process pkt)) ≥ 16"
  by simp