
theory Scratch
    imports Main
begin

fun deposit :: "int ⇒ int ⇒ int" where
  "deposit balance amount = (if amount > 0 then balance + amount else balance)"

fun withdraw :: "int ⇒ int ⇒ int" where
  "withdraw balance amount = (if amount ≤ balance then balance - amount else balance)"

datatype transaction = Deposit int | Withdraw int

fun step :: "int ⇒ transaction ⇒ int" where
  "step balance (Deposit amount) = deposit balance amount"
| "step balance (Withdraw amount) = withdraw balance amount"

fun run :: "int ⇒ transaction list ⇒ int" where
  "run balance [] = balance"
| "run balance (t # ts) = run (step balance t) ts"

lemma step_preserves_non_negative:
  assumes "balance ≥ 0"
  shows "step balance t ≥ 0"
  using assms
proof (cases t)
  case (Deposit amount)
  then show ?thesis 
    using assms by (auto simp: deposit.simps)
next
  case (Withdraw amount)
  then show ?thesis 
    using assms by (auto simp: withdraw.simps)
qed

lemma run_preserves_non_negative:
  assumes "balance ≥ 0"
  shows "run balance ts ≥ 0"
  using assms
proof (induction ts arbitrary: balance)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have "step balance t ≥ 0" 
    using step_preserves_non_negative[OF `balance ≥ 0`] .
  then show ?case 
    using Cons.IH by simp
qed

lemma bank_balance_never_negative: "run 0 ts ≥ 0"
  using run_preserves_non_negative by simp

end
            