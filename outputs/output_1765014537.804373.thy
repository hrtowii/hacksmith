
datatype operation = Deposit int | Withdraw int | GetBalance

record bank_account =
  balance :: int

definition initial_account :: bank_account where
  "initial_account = ⟦ balance = 0 ⟧"

fun apply_operation :: "bank_account ⇒ operation ⇒ bank_account" where
  "apply_operation acc (Deposit amount) = acc ⟦ balance := balance acc + amount ⟧"
| "apply_operation acc (Withdraw amount) = acc ⟦ balance := balance acc - amount ⟧"
| "apply_operation acc GetBalance = acc"

fun apply_operations :: "bank_account ⇒ operation list ⇒ bank_account" where
  "apply_operations acc [] = acc"
| "apply_operations acc (op#ops) = apply_operations (apply_operation acc op) ops"

definition get_balance :: "bank_account ⇒ int" where
  "get_balance acc = balance acc"

lemma balance_never_negative:
  "balance (apply_operations initial_account ops) ≥ 0"
  apply (induct ops arbitrary: initial_account)
  apply (simp add: initial_account_def)
  apply auto
  done
