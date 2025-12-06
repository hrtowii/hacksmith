
theory Heartbleed
imports Main
begin

datatype HeartbeatMessageType = TLS1_HB_REQUEST | TLS1_HB_RESPONSE

record HeartbeatMessage =
  msg_type :: HeartbeatMessageType
  payload_length :: nat
  payload :: "nat list"
  padding :: "nat list"

fun process_heartbeat :: "nat ⇒ nat ⇒ nat ⇒ nat list ⇒ (nat list) option" where
  "process_heartbeat hbtype payload padding_len pl =
    (if hbtype = 1 then  
      let buffer_size = 1 + 2 + payload + padding_len;
          response_type = 2;
          response_payload = take payload pl
      in Some response_payload
    else None)"

definition memcpy_safe :: "nat ⇒ nat list ⇒ bool" where
  "memcpy_safe payload pl ≡ payload ≤ length pl"

lemma no_unchecked_memory_copies:
  assumes "hbtype = 1"
  assumes "padding_len = 16"
  shows "∀pl payload. process_heartbeat hbtype payload padding_len pl ≠ None 
         ⟶ memcpy_safe payload pl"
  apply(auto simp: memcpy_safe_def)
  done

end
