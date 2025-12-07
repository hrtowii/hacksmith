theory Scratch_1765073268
    imports Main
begin

fun n2s :: "nat list ⇒ nat ⇒ nat" where
"n2s bytes p = (if p + 1 < length bytes then (bytes ! p) * 256 + (bytes ! (p + 1)) else 0)"

definition TLS1_HB_REQUEST :: nat where
"TLS1_HB_REQUEST = 1"

definition padding :: nat where
"padding = 16"

fun heartbeat_alloc :: "nat list ⇒ nat option" where
"heartbeat_alloc packet = (
    let p = 0 in
    let hbtype = if p < length packet then packet ! p else 0 in
    let p = p + 1 in
    let payload = n2s packet p in
    if hbtype = TLS1_HB_REQUEST then
        Some (1 + 2 + payload + padding)
    else None)"

lemma allocation_size_exact:
    assumes "length packet ≥ 3"
    and "packet ! 0 = TLS1_HB_REQUEST"
    shows "heartbeat_alloc packet = Some (1 + 2 + n2s packet 1 + padding)"
    using assms by simp

end