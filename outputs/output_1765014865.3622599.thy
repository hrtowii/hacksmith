 :: "int ⇒ int ⇒ int" where
  "deposit amount balance = balance + amount"

fun withdraw :: "int ⇒ int ⇒ int" where
  "withdraw amount balance = balance - amount"

fun getBalance :: "int ⇒ int" where
  "getBalance balance = balance"

lemma balance_never_below_zero:
  assumes "balance ≥ 0"
  shows "getBalance (withdraw amount balance) ≥ 0"
  using assms by s