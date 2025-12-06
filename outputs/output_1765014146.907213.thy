
datatype bank_account = BankAccount (balance: int)

fun deposit :: "bank_account ⇒ int ⇒ bank_account" where
  "deposit (BankAccount bal) amount = BankAccount (bal + amount)"

fun withdraw :: "bank_account ⇒ int ⇒ bank_account" where
  "withdraw (BankAccount bal) amount = BankAccount (bal - amount)"

fun getBalance :: "bank_account ⇒ int" where
  "getBalance (BankAccount bal) = bal"

lemma balance_never_negative:
  "getBalance account ≥ 0"
  apply(cases account)
  apply(simp)
  oops
