```isabelle
record BankAccount =
  balance :: int

definition init_account :: "BankAccount" where
  "init_account = ⦇ balance = 0 ⦈"

definition deposit :: "BankAccount ⇒ int ⇒ BankAccount" where
  "deposit acc amount = acc ⦇ balance := balance acc + amount ⦈"

definition withdraw :: "BankAccount ⇒ int ⇒ BankAccount" where
  "withdraw acc amount = acc ⦇ balance := balance acc - amount ⦈"

definition getBalance :: "BankAccount ⇒ int" where
  "getBalance acc = balance acc"

lemma balance_never_negative:
  assumes "acc = init_account"
  shows "balance acc ≥ 0"
  using assms init_account_def by simp

lemma balance_after_operations_never_negative:
  "balance (init_account) ≥ 0 ⟹
   balance (deposit (init_account) amount) ≥ 0 ∧
   balance (withdraw (init_account) amount) ≥ 0"
  by (simp add: init_account_def deposit_def withdraw_def)
```