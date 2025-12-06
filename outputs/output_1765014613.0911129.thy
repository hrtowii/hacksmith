
datatype account = Account (balance: int)

fun deposit :: "account ⇒ int ⇒ account" where
  "deposit (Account bal) amount = Account (bal + amount)"

fun withdraw :: "account ⇒ int ⇒ account" where
  "withdraw (Account bal) amount = Account (bal - amount)"

fun getBalance :: "account ⇒ int" where
  "getBalance (Account bal) = bal"

lemma balance_never_negative:
  assumes "getBalance acc ≥ 0"
  shows "getBalance (deposit acc amount) ≥ 0 ∧ getBalance (withdraw acc amount) ≥ 0"
  apply(cases acc)
  apply(simp)
