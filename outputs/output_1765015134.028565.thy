definition start_balance :: int where
  "start_balance = 0"

definition deposit :: "int ⇒ int ⇒ int" where
  "deposit amount balance = balance + amount"

definition withdraw :: "int ⇒ int ⇒ int" where
  "withdraw amount balance = (if amount ≤ balance then balance - amount else balance)"

lemma start_balance_nonneg:
  "start_balance ≥ 0"
  unfolding start_balance_def by simp

lemma withdraw_preserves_nonneg:
  assumes "balance ≥ 0"
  shows "withdraw amount balance ≥ 0"
  using assms unfolding withdraw_def by simp

lemma deposit_preserves_nonneg:
  assumes "balance ≥ 0"
  shows "deposit amount balance ≥ 0"
  using assms unfolding deposit_def by simp