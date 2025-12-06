```isabelle
datatype operation = Deposit int | Withdraw int

fun apply_operation :: "int ⇒ operation ⇒ int" where
  "apply_operation balance (Deposit amount) = balance + amount"
| "apply_operation balance (Withdraw amount) = balance - amount"

fun apply_operations :: "int ⇒ operation list ⇒ int" where
  "apply_operations balance [] = balance"
| "apply_operations balance (op # ops) = apply_operations (apply_operation balance op) ops"

lemma bank_account_can_go_negative:
  shows "∃ops. apply_operations 0 ops < 0"
proof -
  let ?ops = "[Withdraw 1]"
  have "apply_operations 0 ?ops = -1"
    by simp
  thus ?thesis
    by (metis neg_less_0_iff_less zero_less_one)
qed

lemma bank_account_negative_example:
  assumes "amount > 0"
  shows "apply_operations 0 [Withdraw amount] < 0"
  using assms by simp
```