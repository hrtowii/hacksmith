
record bank_account =
  balance :: int

definition initial_account :: bank_account where
  "initial_account = ⦇balance = 0⦈"

definition deposit :: "bank_account ⇒ int ⇒ bank_account" where
  "deposit acc amount = acc⦇balance := balance acc + amount⦈"

definition withdraw :: "bank_account ⇒ int ⇒ bank_account" where
  "withdraw acc amount = acc⦇balance := balance acc - amount⦈"

definition getBalance :: "bank_account ⇒ int" where
  "getBalance acc = balance acc"

lemma bank_balance_never_negative:
  assumes "acc = initial_account"
  shows "getBalance acc ≥ 0"
  using assms by (simp add: initial_account_def getBalance_def)
