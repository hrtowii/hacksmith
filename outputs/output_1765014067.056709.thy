
theory Heartbleed
imports Main
begin

datatype HeartbeatMessageType = TLS1_HB_REQUEST | TLS1_HB_RESPONSE

record HeartbeatMessage =
  msg_type :: HeartbeatMessageType
  payload_length :: nat
  payload :: "nat list"
  padding :: "nat list"

fun heartbleed_process :: "HeartbeatMessageType ⇒ nat ⇒ nat list ⇒ nat ⇒ (nat list) option" where
  "heartbleed_process hbtype payload pl_data padding =
    (if hbtype = TLS1_HB_REQUEST then
      let buffer_size = 1 + 2 + payload + padding;
          response_type = TLS1_HB_RESPONSE;
          copied_payload = take payload pl_data;
          total_response = 3 + payload + padding
      in Some copied_payload
    else None)"

fun memory_safe :: "nat ⇒ nat list ⇒ bool" where
  "memory_safe payload pl_data = (payload ≤ length pl_data)"

lemma no_unchecked_memory_copies:
  assumes "hbtype = TLS1_HB_REQUEST"
  shows "∀payload pl_data padding. 
    heartbleed_process hbtype payload pl_data padding ≠ None ⟶ 
    memory_safe payload pl_data"
  apply (simp add: assms)
  apply (rule allI)+
  apply (rule impI)
  apply (simp)
  oops

end
