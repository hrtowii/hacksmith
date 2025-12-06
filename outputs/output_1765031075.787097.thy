```
definition heartbeat_message :: "nat ⇒ nat ⇒ nat ⇒ (nat × nat × nat list × nat list)" where
  "heartbeat_message hbtype payload_length payload padding =
    (hbtype, payload_length, take payload_length payload, take padding (replicate padding 0))"

fun n2s :: "nat list ⇒ nat" where
  "n2s (a # b # _) = a * 256 + b"

fun s2n :: "nat ⇒ nat list ⇒ nat list" where
  "s2n x xs = (x div 256) # (x mod 256) # xs"

fun process_heartbeat :: "nat list ⇒ nat ⇒ nat ⇒ (nat × nat list)" where
  "process_heartbeat p padding hbtype =
    (let payload = n2s (tl p);
         pl = tl (tl p);
         buffer = 1 + 2 + payload + padding;
         bp = s2n payload (replicate payload (hd pl) @ replicate padding 0)
     in if hbtype = 1 then (buffer, bp) else (0, []))"

lemma payload_length_response_matches_request:
  assumes "process_heartbeat (hbtype # p_len # payload) padding 1 = (_, response)"
      and "length p_len = 2"
  shows "n2s p_len = length (take (n2s p_len) (tl (tl (hbtype # p_len # payload))))"
  using assms by (simp add: process_heartbeat.simps n2s.simps)

lemma response_includes_exact_payload_bytes:
  assumes "process_heartbeat (1 # p_len # payload) padding 1 = (_, response)"
      and "length p_len = 2"
      and "payload_length = n2s p_len"
  shows "take payload_length response = take payload_length (tl (tl (1 # p_len # payload)))"
  using assms by (simp add: process_heartbeat.simps n2s.simps)

lemma memory_allocation_exact:
  assumes "process_heartbeat (1 # p_len # payload) padding 1 = (buffer_size, _)"
      and "length p_len = 2"
  shows "buffer_size = 1 + 2 + n2s p_len + padding"
  using assms by (simp add: process_heartbeat.simps n2s.simps)
```