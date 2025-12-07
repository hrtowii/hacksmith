theory Scratch_1765072405
    imports Main
begin

type_synonym byte = nat

definition TLS1_HB_REQUEST :: byte where "TLS1_HB_REQUEST = 1"
definition TLS1_HB_RESPONSE :: byte where "TLS1_HB_RESPONSE = 2"
definition padding :: nat where "padding = 16"

fun heartbeat :: "byte list ⇒ byte list" where
"heartbeat buffer = (
    if length buffer < 3 then []
    else
        let hbtype = buffer ! 0 in
        let payload = (buffer ! 1) * 256 + (buffer ! 2) in
        let pl = drop 3 buffer in
        if hbtype = TLS1_HB_REQUEST then
            (* Construct response: type + length + payload copy + padding *)
            [TLS1_HB_RESPONSE, buffer ! 1, buffer ! 2] @
            take payload pl @
            replicate padding 0
        else [])"

lemma payload_length_matches_request:
    assumes "length buffer ≥ 3"
    and "buffer ! 0 = TLS1_HB_REQUEST"
    shows "length (take ((buffer ! 1) * 256 + (buffer ! 2)) (drop 3 buffer)) = (buffer ! 1) * 256 + (buffer ! 2)"
    using assms by simp

end