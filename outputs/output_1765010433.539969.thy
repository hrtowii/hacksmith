```isabelle
datatype operation = Deposit int | Withdraw int | GetBalance

fun apply_operation :: "int ⇒ operation ⇒ int" where
  "apply_operation balance (Deposit amount) = balance + amount" |
  "apply_operation balance (Withdraw amount) = balance - amount" |
  "apply_operation balance GetBalance = balance"

fun apply_operations :: "int ⇒ operation list ⇒ int" where
  "apply_operations balance [] = balance" |
  "apply_operations balance (op # ops) = apply_operations (apply_operation balance op) ops"

lemma balance_never_negative:
  assumes "balance ≥ 0"
    and "∀op ∈ set ops. (case op of Deposit amt ⇒ amt ≥ 0 | Withdraw amt ⇒ amt ≤ balance | GetBalance ⇒ True)"
  shows "apply_operations balance ops ≥ 0"
  sorry
```