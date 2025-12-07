fun n2s :: "nat ⇒ nat ⇒ nat" where
  "n2s h l = h * 256 + l"

fun s2n :: "nat ⇒ nat list" where
  "s2n n = [n div 256, n mod 256]"

definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"
definition TLS1_HB_RESPONSE :: nat where "TLS1_HB_RESPONSE = 2"
definition padding_len :: nat where "padding_len = 16"

fun process_heartbeat :: "nat list ⇒ nat list" where
  "process_heartbeat packet = (
    if length packet < 3 then []
    else
      let hbtype = packet ! 0;
          payload = n2s (packet ! 1) (packet ! 2);
          pl = drop 3 packet
      in
      if hbtype = TLS1_HB_REQUEST then
        let response_type = TLS1_HB_RESPONSE;
            response_payload_len = s2n payload;
            response_payload = take payload pl;
            response_padding = replicate padding_len 0
        in [response_type] @ response_payload_len @ response_payload @ response_padding
      else []
  )"

lemma heartbeat_response_length_correct:
  assumes "length packet ≥ 3"
  and "packet ! 0 = TLS1_HB_REQUEST"
  shows "length (process_heartbeat packet) = 3 + n2s (packet ! 1) (packet ! 2) + padding_len"
  using assms by (simp add: TLS1_HB_REQUEST_def TLS1_HB_RESPONSE_def padding_len_def Let_def)