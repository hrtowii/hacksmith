```isabelle
datatype operation = Deposit int | Withdraw int | GetBalance

fun apply_operation :: "int ⇒ operation ⇒ int" where
  "apply_operation balance (Deposit amount) = balance + amount" |
  "apply_operation balance (Withdraw amount) = balance - amount" |
  "apply_operation balance GetBalance = balance"

fun apply_operations :: "int ⇒ operation list ⇒ int" where
  "apply_operations balance [] = balance" |
  "apply_operations balance (op # ops) = apply_operations (apply_operation balance op) ops"

definition initial_balance :: int where
  "initial_balance = 0"

lemma balance_can_go_negative:
  shows "∃ops. apply_operations initial_balance ops < 0"
proof -
  let ?ops = "[Withdraw 1]"
  have "apply_operations initial_balance ?ops = initial_balance - 1"
    by (simp add: initial_balance_def)
  then have "apply_operations initial_balance ?ops < 0"
    by (simp add: initial_balance_def)
  then show ?thesis by blast
qed
```