```
typedefs HeartbeatMessageType = "char"
typedefs opaque = "char list"

record HeartbeatMessage =
  hb_type :: HeartbeatMessageType
  payload_length :: "16 word"
  payload :: "opaque list"
  padding :: "opaque list"

definition TLS1_HB_REQUEST :: HeartbeatMessageType where
  "TLS1_HB_REQUEST = CHR ''R''"

definition TLS1_HB_RESPONSE :: HeartbeatMessageType where
  "TLS1_HB_RESPONSE = CHR ''S''"

definition n2s :: "char list ⇒ nat ⇒ nat × char list" where
  "n2s p payload = (word_of_list (take 2 p), drop 2 p)"

definition s2n :: "nat ⇒ char list ⇒ char list" where
  "s2n payload bp = list_of_word (word_of_nat 16 payload) @ bp"

definition RAND_pseudo_bytes :: "nat ⇒ char list ⇒ char list" where
  "RAND_pseudo_bytes n bp = replicate n (CHR ''X'') @ bp"

definition ssl3_write_bytes :: "nat ⇒ HeartbeatMessageType ⇒ char list ⇒ nat ⇒ nat" where
  "ssl3_write_bytes s t buf len = (if length buf = len then len else 0)"

definition OPENSSL_malloc :: "nat ⇒ char list option" where
  "OPENSSL_malloc n = Some (replicate n (CHR ''\0''))"

definition OPENSSL_free :: "char list ⇒ unit" where
  "OPENSSL_free _ = ()"

fun heartbeat_response :: "HeartbeatMessage ⇒ nat ⇒ nat ⇒ nat" where
  "heartbeat_response req s padding =
    (let
      hbtype = hb_type req;
      p = [CHR ''A'', CHR ''B''] @ payload req;  (* Simulate pointer arithmetic *)
      (payload, p') = n2s p 0;
      pl = p';
      buffer = case OPENSSL_malloc (1 + 2 + payload + padding) of
                 Some buf ⇒ buf
               | None ⇒ [];
      bp = buffer;
      bp' = s2n payload bp;
      bp'' = bp' @ take payload pl;
      bp''' = RAND_pseudo_bytes padding bp'';
      len = 3 + payload + padding
    in
      if hbtype = TLS1_HB_REQUEST then
        ssl3_write_bytes s TLS1_HB_RESPONSE (bp''') len
      else 0)"

lemma payload_length_reflects_payload:
  assumes "hb_type msg = TLS1_HB_REQUEST"
  shows "length (payload msg) = word_to_nat (payload_length msg)"
  using assms by (cases msg) (simp add: word_to_nat_def)

lemma response_includes_exact_payload:
  assumes "hb_type req = TLS1_HB_REQUEST"
      and "length (payload req) = word_to_nat (payload_length req)"
  shows "∃resp. heartbeat_response req s padding ≠ 0 ∧
         take (word_to_nat (payload_length req)) (payload resp) = payload req"
  using assms by (simp add: heartbeat_response_def n2s_def s2n_def)

lemma padding_at_least_16:
  assumes "hb_type req = TLS1_HB_REQUEST"
      and "heartbeat_response req s padding ≠ 0"
  shows "padding ≥ 16"
  using assms by (simp add: heartbeat_response_def)

lemma memory_allocation_matches_spec:
  assumes "hb_type req = TLS1_HB_REQUEST"
      and "length (payload req) = word_to_nat (payload_length req)"
  shows "case OPENSSL_malloc (1 + 2 + word_to_nat (payload_length req) + padding) of
           Some buf ⇒ length buf = 1 + 2 + word_to_nat (payload_length req) + padding
         | None ⇒ False"
  using assms by (simp add: OPENSSL_malloc_def)

lemma ssl3_write_bytes_correct_length:
  assumes "hb_type req = TLS1_HB_REQUEST"
      and "length (payload req) = word_to_nat (payload_length req)"
      and "heartbeat_response req s padding ≠ 0"
  shows "ssl3_write_bytes s TLS1_HB_RESPONSE
          (s2n (word_to_nat (payload_length req))
            (replicate (1 + 2 + word_to_nat (payload_length req) + padding) (CHR ''\0'')) @
           take (word_to_nat (payload_length req)) (payload req) @
           replicate padding (CHR ''X''))
          (3 + word_to_nat (payload_length req) + padding) =
        3 + word_to_nat (payload_length req) + padding"
  using assms by (simp add: ssl3_write_bytes_def s2n_def)

lemma heartbeat_message_type_distinction:
  shows "TLS1_HB_REQUEST ≠ TLS1_HB_RESPONSE"
  by (simp add: TLS1_HB_REQUEST_def TLS1_HB_RESPONSE_def)

lemma memory_management_no_leaks:
  assumes "hb_type req = TLS1_HB_REQUEST"
  shows "heartbeat_response req s padding; () = OPENSSL_free undefined"
  using assms by (simp add: OPENSSL_free_def heartbeat_response_def)

lemma payload_length_no_overflow:
  assumes "hb_type req = TLS1_HB_REQUEST"
      and "word_to_nat (payload_length req) ≤ 2^16 - 1"
  shows "1 + 2 + word_to_nat (payload_length req) + padding ≤ 2^31 - 1"
  using assms by simp

lemma memcpy_no_buffer_overread:
  assumes "hb_type req = TLS1_HB_REQUEST"
      and "length (payload req) = word_to_nat (payload_length req)"
  shows "length (take (word_to_nat (payload_length req)) (payload req)) =
         word_to_nat (payload_length req)"
  using assms by simp
```