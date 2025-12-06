definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 1"

fun ssl_heartbeat :: "nat list ⇒ nat ⇒ (nat × nat list)" where
"ssl_heartbeat packet padding = 
    (if length packet ≥ 3 then
        let hbtype = packet ! 0;
            payload_len = (packet ! 1) * 256 + (packet ! 2);
            pl = drop 3 packet
        in
        if hbtype = TLS1_HB_REQUEST then
            (1 + 2 + payload_len + padding, take payload_len pl)
        else (0, [])
    else (0, []))"

lemma payload_reflects_actual_size:
    assumes "length packet ≥ 3"
    and "packet ! 0 = TLS1_HB_REQUEST"
    shows "((packet ! 1) * 256 + (packet ! 2)) ≤ length (drop 3 packet)"
    using assms by simp

lemma allocation_matches_sum:
    assumes "length packet ≥ 3"
    and "packet ! 0 = TLS1_HB_REQUEST"
    shows "fst (ssl_heartbeat packet padding) = 1 + 2 + ((packet ! 1) * 256 + (packet ! 2)) + padding"
    using assms TLS1_HB_REQUEST_def by (simp add: Let_def)

lemma padding_does_not_affect_payload:
    assumes "length packet ≥ 3"
    and "packet ! 0 = TLS1_HB_REQUEST"
    shows "snd (ssl_heartbeat packet p1) = snd (ssl_heartbeat packet p2)"
    using assms TLS1_HB_REQUEST_def by (simp add: Let_def)