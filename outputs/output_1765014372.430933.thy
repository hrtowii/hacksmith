
datatype bank_account = BankAccount "int"

fun get_balance :: "bank_account ⇒ int" where
  "get_balance (BankAccount balance) = balance"

fun deposit :: "bank_account ⇒ int ⇒ bank_account" where
  "deposit (BankAccount balance) amount = BankAccount (balance + amount)"

fun withdraw :: "bank_account ⇒ int ⇒ bank_account" where
  "withdraw (BankAccount balance) amount = BankAccount (balance - amount)"

lemma balance_never_negative:
  "get_balance account ≥ 0"
  apply (cases account)
  apply simp
  oops
