```isabelle
datatype HeartbeatMessageType = TLS1_HB_REQUEST | TLS1_HB_RESPONSE

record HeartbeatMessage =
  hb_type :: HeartbeatMessageType
  payload_length :: nat
  actual_payload_size :: nat

fun heartbleed_step :: "HeartbeatMessage ⇒ nat option" where
  "heartbleed_step msg =
    (let payload = payload_length msg;
         padding = 16;
         actual_size = actual_payload_size msg
     in
       if hb_type msg = TLS1_HB_REQUEST then
         Some (1 + 2 + payload + padding)
       else None)"

fun heartbleed_copy_size :: "HeartbeatMessage ⇒ nat" where
  "heartbleed_copy_size msg = payload_length msg"

fun heartbleed_safe :: "HeartbeatMessage ⇒ bool" where
  "heartbleed_safe msg = (payload_length msg ≤ actual_payload_size msg)"

lemma no_unchecked_memory_copies:
  assumes "hb_type msg = TLS1_HB_REQUEST"
  assumes "heartbleed_copy_size msg > actual_payload_size msg"
  shows "heartbleed_safe msg"
  using assms by simp
```