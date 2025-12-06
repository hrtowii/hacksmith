definition TLS1_HB_REQUEST :: nat where "TLS1_HB_REQUEST = 24"

fun hb_payload :: "nat list ⇒ nat" where
  "hb_payload packet = (packet ! 1) * 256 + (packet ! 2)"

lemma no_unchecked_memory_vulnerabilities:
  assumes "length packet ≥ 3"
  and "packet ! 0 = TLS1_HB_REQUEST"
  shows "3 + hb_payload packet ≤ length packet"
  using assms by simp