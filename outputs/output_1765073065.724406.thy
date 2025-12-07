definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"

fun n2s :: "nat list ⇒ nat" where
  "n2s (b1 # b2 # _) = b1 * 256 + b2" |
  "n2s _ = 0"

fun s2n :: "nat ⇒ nat list" where
  "s2n n = [n div 256, n mod 256]"

fun heartbeat :: "nat list ⇒ nat list" where
  "heartbeat request = (
    if request ≠ [] ∧ hd request = TLS1_HB_REQUEST then
      if length request ≥ 3 then
        let payload_len = n2s (drop 1 request) in
        let pl = drop 3 request in
        let response_payload = take payload_len pl in
        let padding = replicate 16 0 in
          [TLS1_HB_REQUEST] @ s2n payload_len @ response_payload @ padding
      else []
    else []
  )"

lemma response_payload_length_correct:
  assumes "request ≠ []"
  and "hd request = TLS1_HB_REQUEST"
  and "length request ≥ 3"
  shows "length (heartbeat request) = 1 + 2 + n2s (drop 1 request) + 16"
  using assms by simp