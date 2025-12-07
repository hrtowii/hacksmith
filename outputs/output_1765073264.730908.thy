definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"
definition TLS1_HB_RESPONSE :: nat where "TLS1_HB_RESPONSE = 2"
definition padding_length :: nat where "padding_length = 16"

fun n2s :: "nat ⇒ nat ⇒ nat" where
  "n2s h l = h * 256 + l"

fun heartbeat_process :: "nat list ⇒ nat list" where
  "heartbeat_process packet = (
    if packet ≠ [] then
        let hbtype = packet ! 0 in
        if hbtype = TLS1_HB_REQUEST then
            if length packet ≥ 3 then
                let payload_len = n2s (packet ! 1) (packet ! 2) in
                let pl = drop 3 packet in
                (* Model the memory copy operation *)
                let response_payload = take payload_len pl in
                (* Construct the response buffer *)
                [TLS1_HB_RESPONSE] @ 
                [packet ! 1, packet ! 2] @ 
                response_payload @ 
                replicate padding_length 0
            else []
        else []
    else [])"

lemma payload_length_matches_request:
  assumes "packet ≠ []"
  and "packet ! 0 = TLS1_HB_REQUEST"
  and "length packet ≥ 3"
  shows "length (take (n2s (packet ! 1) (packet ! 2)) (drop 3 packet)) = n2s (packet ! 1) (packet ! 2)"
  using assms by simp