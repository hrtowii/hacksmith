theory Scratch_1765072274
    imports Main
begin

definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"
definition TLS1_HB_RESPONSE :: nat where "TLS1_HB_RESPONSE = 2"
definition PADDING_LEN :: nat where "PADDING_LEN = 16"

fun openssl_heartbeat :: "nat list ⇒ nat list" where
"openssl_heartbeat request =
    (if length request < 3 then []
    else
        let hbtype = request ! 0 in
        let payload = (request ! 1) * 256 + (request ! 2) in
        let pl = drop 3 request in
        if hbtype = TLS1_HB_REQUEST then
            let buffer = [TLS1_HB_RESPONSE, payload div 256, payload mod 256] @ (take payload pl) @ (replicate PADDING_LEN 0)
            in buffer
        else [])"

lemma heartbeat_resp_length_match:
    assumes "length request ≥ 3"
    and "request ! 0 = TLS1_HB_REQUEST"
    shows "length (openssl_heartbeat request) = 1 + 2 + ((request ! 1) * 256 + (request ! 2)) + PADDING_LEN"
    using assms by simp

end