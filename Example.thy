```isabelle
theory Example
imports Main
begin

definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"
definition TLS1_HB_RESPONSE :: nat where "TLS1_HB_RESPONSE = 2"

fun n2s :: "nat list ⇒ nat" where
  "n2s (b1 # b2 # _) = b1 * 256 + b2" |
  "n2s _ = 0"

fun ssl_heartbeat :: "nat list ⇒ nat list" where
  "ssl_heartbeat p = (
    if length p < 3 then []
    else
      let hbtype = p ! 0;
          payload = n2s (drop 1 p);
          pl = drop 3 p
      in
        if hbtype = TLS1_HB_REQUEST then
          (* The C code allocates buffer based on 'payload' and copies 'payload' bytes 
             from 'pl' pointer via memcpy, regardless of actual 'pl' size. 
             In Isabelle, 'take' truncates if the list is too short. *)
          let response_payload = take payload pl;
              padding = replicate 16 0
          in
          [TLS1_HB_RESPONSE] @ (take 2 (drop 1 p)) @ response_payload @ padding
        else []
  )"

lemma heartbeat_response_exact_length:
  assumes "length p ≥ 3"
  and "p ! 0 = TLS1_HB_REQUEST"
  shows "length (ssl_heartbeat p) = 1 + 2 + n2s (drop 1 p) + 16"
  using assms by simp

end
```