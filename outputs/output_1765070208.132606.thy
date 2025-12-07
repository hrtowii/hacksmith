definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"
definition TLS1_HB_RESPONSE :: nat where "TLS1_HB_RESPONSE = 2"

fun heartbeat_response :: "nat list ⇒ nat list" where
"heartbeat_response packet = (
    if length packet < 3 then [] 
    else
    let hbtype = packet ! 0 in
    if hbtype = TLS1_HB_REQUEST then
        let payload_len = (packet ! 1) * 256 + (packet ! 2) in
        (* The vulnerability: The code reads 'payload_len' bytes from payload pointer 
           without checking if the request packet is actually that long. *)
        let payload = take payload_len (drop 3 packet) in
        let padding = replicate 16 0 in
        [TLS1_HB_RESPONSE, packet ! 1, packet ! 2] @ payload @ padding
    else [])"

lemma payload_length_matches_request:
  assumes "length packet ≥ 3" "packet ! 0 = TLS1_HB_REQUEST"
  shows "let resp = heartbeat_response packet in 
         length resp ≥ 3 ∧ (resp ! 1) * 256 + (resp ! 2) = (packet ! 1) * 256 + (packet ! 2)"
  using assms by (simp add: Let_def)

lemma response_includes_exact_payload_bytes:
  assumes "length packet ≥ 3" "packet ! 0 = TLS1_HB_REQUEST"
  let specified_len = (packet ! 1) * 256 + (packet ! 2) in
  shows "length (take specified_len (drop 3 (heartbeat_response packet))) = specified_len"
  using assms by (simp add: Let_def)

lemma memory_allocated_correct_size:
  assumes "length packet ≥ 3" "packet ! 0 = TLS1_HB_REQUEST"
  let specified_len = (packet ! 1) * 256 + (packet ! 2) in
  shows "length (heartbeat_response packet) = 1 + 2 + specified_len + 16"
  using assms by (simp add: Let_def)