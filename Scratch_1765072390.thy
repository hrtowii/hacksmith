theory Scratch_1765072390
    imports Main
begin

definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"
definition padding :: nat where "padding = 16"

fun heartbeat_alloc_size :: "nat ⇒ nat ⇒ nat" where
"heartbeat_alloc_size hbtype payload =
    (if hbtype = TLS1_HB_REQUEST then
        1 + 2 + payload + padding
    else 0)"

lemma heartbeat_allocation_correct:
    assumes "hbtype = TLS1_HB_REQUEST"
    shows "heartbeat_alloc_size hbtype payload = 1 + 2 + payload + padding"
    using assms by simp

end