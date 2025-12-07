definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"

fun heartbeat_alloc_logic :: "nat ⇒ nat ⇒ nat" where
  "heartbeat_alloc_logic hbtype payload =
    (if hbtype = TLS1_HB_REQUEST then
       let padding = 16 in
       1 + 2 + payload + padding
     else 0)"

lemma heartbeat_response_alloc_correct:
  assumes "hbtype = TLS1_HB_REQUEST"
  shows "heartbeat_alloc_logic hbtype payload = 1 + 2 + payload + 16"
  using assms by simp