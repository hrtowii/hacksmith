definition TLS1_HB_REQUEST :: nat where
"TLS1_HB_REQUEST = 1"

definition TLS1_HB_RESPONSE :: nat where
"TLS1_HB_RESPONSE = 2"

definition PADDING_LEN :: nat where
"PADDING_LEN = 16"

fun n2s :: "nat list ⇒ nat" where
"n2s (b1 # b2 # xs) = b1 * 256 + b2" |
"n2s _ = 0"

fun s2n :: "nat ⇒ nat list" where
"s2n n = [n div 256, n mod 256]"

fun heartbleed :: "nat list ⇒ nat list" where
"heartbleed packet = (
  if length packet < 3 then []
  else let hbtype = packet ! 0 in
       let payload = n2s (drop 1 packet) in
       let pl = drop 3 packet in
       if hbtype = TLS1_HB_REQUEST then
         let vector = take payload pl in
         [TLS1_HB_RESPONSE] @ s2n payload @ vector @ replicate PADDING_LEN 0
       else [])"

lemma payload_length_match:
  assumes "length packet ≥ 3"
  assumes "packet ! 0 = TLS1_HB_REQUEST"
  shows "n2s (drop 1 (heartbleed packet)) = n2s (drop 1 packet)"
  using assms by (simp add: div_mult_mod_eq)

lemma response_content_length:
  assumes "length packet ≥ 3"
  assumes "packet ! 0 = TLS1_HB_REQUEST"
  let payload = "n2s (drop 1 packet)" in
  shows "length (take payload (drop 3 (heartbleed packet))) = payload"
  using assms by simp

lemma allocation_size_check:
  assumes "length packet ≥ 3"
  assumes "packet ! 0 = TLS1_HB_REQUEST"
  let payload = "n2s (drop 1 packet)" in
  shows "length (heartbleed packet) = 1 + 2 + payload + PADDING_LEN"
  using assms by simp