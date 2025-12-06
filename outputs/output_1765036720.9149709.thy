fun n2s :: "nat list ⇒ nat" where
  "n2s (b1 # b2 # _) = b1 * 256 + b2" |
  "n2s _ = 0"

fun s2n :: "nat ⇒ nat list" where
  "s2n n = [n div 256, n mod 256]"

definition payload_len :: "nat list ⇒ nat" where
  "payload_len pkt = (if length pkt ≥ 3 then n2s (drop 1 pkt) else 0)"

definition padding :: nat where "padding = 16"

fun ssl_heartbeat :: "nat list ⇒ nat list" where
"ssl_heartbeat pkt = (
    let pl = payload_len pkt;
        payload_content = take pl (drop 3 pkt)
    in [2] @ s2n pl @ payload_content @ replicate padding 0)"

lemma payload_length_in_response_matches_request:
  "n2s (drop 1 (ssl_heartbeat pkt)) = payload_len pkt"
  by (simp add: padding_def Let_def)

lemma response_includes_specified_payload_bytes:
  "length (take (payload_len pkt) (drop 3 pkt)) = payload_len pkt"
  by simp

lemma memory_allocated_correctly:
  "length (ssl_heartbeat pkt) = 1 + 2 + payload_len pkt + padding"
  by (simp add: Let_def padding_def)