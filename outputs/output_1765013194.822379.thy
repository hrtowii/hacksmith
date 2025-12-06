
theory Heartbleed
imports Main
begin

datatype HeartbeatMessageType = TLS1_HB_REQUEST | TLS1_HB_RESPONSE

record HeartbeatMessage =
  hb_type :: HeartbeatMessageType
  payload_length :: nat
  payload :: "nat list"
  padding :: "nat list"

fun process_heartbeat :: "HeartbeatMessageType ⇒ nat ⇒ nat list ⇒ (nat × nat list) option" where
  "process_heartbeat hbtype payload pl =
    (if hbtype = TLS1_HB_REQUEST then
      let padding = 16;
          response_type = TLS1_HB_RESPONSE;
          response_payload = take payload pl
      in Some (3 + payload + padding, response_payload)
    else None)"

lemma no_unchecked_memory_copies:
  assumes "process_heartbeat hbtype payload pl = Some (response_size, response_payload)"
  shows "length response_payload ≤ length pl"
  apply (cases hbtype)
   apply (simp add: assms)
   apply (metis length_take min_absorb2 order_refl)
  apply (simp add: assms)
  done

end
