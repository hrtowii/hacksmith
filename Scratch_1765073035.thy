theory Scratch_1765073035
    imports Main
begin

definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"

fun heartbeat_alloc :: "nat ⇒ nat ⇒ nat ⇒ nat" where
  "heartbeat_alloc hbtype payload padding =
    (if hbtype = TLS1_HB_REQUEST then
       1 + 2 + payload + padding
     else 0)"

lemma correct_allocation_size:
  assumes "hbtype = TLS1_HB_REQUEST"
  shows "heartbeat_alloc hbtype payload padding = 1 + 2 + payload + padding"
  using assms by simp

end