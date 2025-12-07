theory Scratch_1765073047
    imports Main
begin

definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 24"
definition TLS1_HB_RESPONSE :: nat where "TLS1_HB_RESPONSE = 25"

fun tls_heartbeat :: "nat list ⇒ nat list" where
"tls_heartbeat packet = (
    if packet ≠ [] then
        let hbtype = packet ! 0 in
        let payload = (packet ! 1) * 256 + (packet ! 2) in
        let pl = drop 3 packet in
        
        if hbtype = TLS1_HB_REQUEST then
            let bp_type = [TLS1_HB_RESPONSE] in
            let bp_len = [payload div 256, payload mod 256] in
            let bp_payload = take payload pl in
            let bp_padding = replicate 16 0 in
            bp_type @ bp_len @ bp_payload @ bp_padding
        else []
    else [])"

lemma heartbeat_payload_length_matches_request:
    assumes "packet ≠ []"
    and "packet ! 0 = TLS1_HB_REQUEST"
    shows "length (tls_heartbeat packet) = 1 + 2 + ((packet ! 1) * 256 + (packet ! 2)) + 16"
    using assms by simp

end