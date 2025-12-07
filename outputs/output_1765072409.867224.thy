definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"
definition TLS1_HB_RESPONSE :: nat where "TLS1_HB_RESPONSE = 2"

fun n2s :: "nat ⇒ nat ⇒ nat" where
"n2s hi lo = hi * 256 + lo"

fun s2n :: "nat ⇒ nat list" where
"s2n n = [n div 256, n mod 256]"

fun process_heartbeat :: "nat list ⇒ nat list" where
"process_heartbeat packet = (
    if length packet ≥ 3 then
        let hbtype = packet ! 0 in
        let payload_len = n2s (packet ! 1) (packet ! 2) in
        
        if hbtype = TLS1_HB_REQUEST then
            (* Translation of the C logic: copy payload_len bytes from payload pointer *)
            (* pl points to packet start + 3 *)
            let pl = drop 3 packet in
            (* copy payload bytes: Isabelle take is memory safe, C memcpy was not *)
            let copied_payload = take payload_len pl in
            let padding = replicate 16 0 in
            (* Construct response: Type + Length + Payload + Padding *)
            [TLS1_HB_RESPONSE] @ s2n payload_len @ copied_payload @ padding
        else []
    else [])"

lemma heartbeat_len_check:
    assumes "length packet ≥ 3"
    assumes "packet ! 0 = TLS1_HB_REQUEST"
    (* The response should include exactly the number of payload bytes specified in the request *)
    (* This lemma will fail if payload_len > length(pl), exposing the missing bounds check *)
    shows "length (take (n2s (packet ! 1) (packet ! 2)) (drop 3 (process_heartbeat packet))) = n2s (packet ! 1) (packet ! 2)"
    using assms by (simp add: TLS1_HB_REQUEST_def TLS1_HB_RESPONSE_def Let_def)