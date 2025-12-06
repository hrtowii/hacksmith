fun n2s :: "nat list ⇒ nat" where
  "n2s (b1 # b2 # xs) = b1 * 256 + b2" |
  "n2s _ = 0"

fun s2n :: "nat ⇒ nat list" where
  "s2n len = [len div 256, len mod 256]"

definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"
definition TLS1_HB_RESPONSE :: nat where "TLS1_HB_RESPONSE = 2"
definition PADDING_LEN :: nat where "PADDING_LEN = 16"

fun openssl_heartbeat :: "nat list ⇒ nat list" where
  "openssl_heartbeat msg = (
    if length msg < 3 then [] else
    let hbtype = msg ! 0;
        payload_len = n2s (tl msg);
        pl = drop 3 msg
    in
    if hbtype = TLS1_HB_REQUEST then
      let buffer = [TLS1_HB_RESPONSE] @ (s2n payload_len) @ (take payload_len pl) @ (replicate PADDING_LEN 0)
      in buffer
    else []
  )"

lemma payload_length_matches_request:
  assumes "length msg ≥ 3"
  and "hd msg = TLS1_HB_REQUEST"
  shows "n2s (tl (openssl_heartbeat msg)) = n2s (tl msg)"
  using assms
  apply (simp add: TLS1_HB_RESPONSE_def TLS1_HB_REQUEST_def PADDING_LEN_def Let_def)
  done

lemma payload_bytes_count_exact:
  assumes "length msg ≥ 3"
  and "hd msg = TLS1_HB_REQUEST"
  let payload_len = n2s (tl msg) in
  shows "length (take payload_len (drop 3 (openssl_heartbeat msg))) = payload_len"
  using assms
  apply (simp add: TLS1_HB_RESPONSE_def TLS1_HB_REQUEST_def PADDING_LEN_def Let_def)
  done

lemma allocated_memory_size_correct:
  assumes "length msg ≥ 3"
  and "hd msg = TLS1_HB_REQUEST"
  let payload_len = n2s (tl msg) in
  shows "length (openssl_heartbeat msg) = 1 + 2 + payload_len + PADDING_LEN"
  using assms
  apply (simp add: TLS1_HB_RESPONSE_def TLS1_HB_REQUEST_def PADDING_LEN_def Let_def)
  done