
theory Scratch_1765038409
    imports Main
begin

typedef HeartbeatMessageType = "UNIV :: 1 word"

record HeartbeatMessage =
  type :: HeartbeatMessageType
  payload_length :: "16 word"
  payload :: "byte list"
  padding :: "byte list"

definition n2s :: "byte list ⇒ 16 word" where
  "n2s p = (case p of [a, b] ⇒ word_of_nat (nat_of_byte a * 256 + nat_of_byte b))"

definition s2n :: "16 word ⇒ byte list ⇒ byte list" where
  "s2n len bp = [byte_of_nat (nat_of_word len div 256), byte_of_nat (nat_of_word len mod 256)] @ bp"

definition ssl3_write_bytes :: "nat ⇒ HeartbeatMessageType ⇒ byte list ⇒ nat ⇒ int" where
  "ssl3_write_bytes s t buf len = (if length buf = len then 0 else -1)"

fun process_heartbeat :: "byte list ⇒ (byte list × int)" where
  "process_heartbeat p =
    (let hbtype = hd p;
         payload = n2s (take 2 (tl p));
         pl = drop 3 p;
         padding = 16;
         buffer = [TLS1_HB_RESPONSE] @ s2n payload [] @ take (nat_of_word payload) pl @ replicate padding 0;
         r = ssl3_write_bytes 0 TLS1_RT_HEARTBEAT buffer (3 + nat_of_word payload + padding)
     in (buffer, r))"

lemma payload_length_response_matches_request:
  assumes "process_heartbeat p = (buffer, 0)"
  shows "take 2 (tl buffer) = take 2 (tl p)"
  using assms by (auto simp: process_heartbeat_def Let_def n2s_def s2n_def split: list.split)

lemma response_includes_exact_payload_bytes:
  assumes "process_heartbeat p = (buffer, 0)"
      and "length pl ≥ nat_of_word (n2s (take 2 (tl p)))"
  shows "take (nat_of_word (n2s (take 2 (tl p)))) (drop 3 buffer) = take (nat_of_word (n2s (take 2 (tl p)))) (drop 3 p)"
  using assms by (auto simp: process_heartbeat_def Let_def n2s_def s2n_def split: list.split)

lemma memory_allocation_exact:
  assumes "process_heartbeat p = (buffer, 0)"
  shows "length buffer = 1 + 2 + nat_of_word (n2s (take 2 (tl p))) + 16"
  using assms by (auto simp: process_heartbeat_def Let_def n2s_def s2n_def split: list.split)

lemma buffer_overread_vulnerability:
  assumes "length pl < nat_of_word (n2s (take 2 (tl p)))"
  shows "∃buffer r. process_heartbeat p = (buffer, r) ∧ length (drop 3 buffer) > length pl"
  using assms by (auto simp: process_heartbeat_def Let_def n2s_def s2n_def split: list.split)

end
        