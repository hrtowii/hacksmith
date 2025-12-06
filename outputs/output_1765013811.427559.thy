
theory Heartbleed
imports Main
begin

datatype HeartbeatMessageType = TLS1_HB_REQUEST | TLS1_HB_RESPONSE

record HeartbeatMessage =
  hb_type :: HeartbeatMessageType
  payload_length :: nat
  payload :: "nat list"
  padding :: "nat list"

fun process_heartbeat :: "HeartbeatMessageType ⇒ nat ⇒ nat list ⇒ nat list option" where
  "process_heartbeat hbtype payload pl =
    (if hbtype = TLS1_HB_REQUEST then
      let padding = 16;
          buffer_size = 1 + 2 + payload + padding;
          response_payload = take payload pl;
          response_size = 3 + payload + padding
      in Some response_payload
    else None)"

lemma no_unchecked_memory_copies:
  assumes "process_heartbeat hbtype payload pl = Some response"
  assumes "length pl ≥ payload"
  shows "length response ≤ length pl"
  apply(cases hbtype)
   apply(simp add: assms)
   apply(simp add: min_def)
  apply(simp)
  done

end
