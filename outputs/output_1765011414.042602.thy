```isabelle
record BankAccount =
  balance :: int

definition initial_account :: BankAccount where
  "initial_account = ⦇ balance = 0 ⦈"

definition deposit :: "BankAccount ⇒ int ⇒ BankAccount" where
  "deposit acc amount = acc ⦇ balance := balance acc + amount ⦈"

definition withdraw :: "BankAccount ⇒ int ⇒ BankAccount" where
  "withdraw acc amount = acc ⦇ balance := balance acc - amount ⦈"

definition getBalance :: "BankAccount ⇒ int" where
  "getBalance acc = balance acc"

inductive account_ops :: "BankAccount ⇒ BankAccount ⇒ bool" where
  initial: "account_ops initial_account initial_account"
| do_deposit: "account_ops acc1 acc2 ⟹ account_ops acc1 (deposit acc2 amount)"
| do_withdraw: "account_ops acc1 acc2 ⟹ account_ops acc1 (withdraw acc2 amount)"

lemma balance_non_negative:
  assumes "account_ops initial_account acc"
  shows "balance acc ≥ 0"
  nitpick
  oops
```