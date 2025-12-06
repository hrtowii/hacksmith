fun deposit :: "int ⇒ int ⇒ int" where
  "deposit amount balance = balance + amount"

fun withdraw :: "int ⇒ int ⇒ int" where
  "withdraw amount balance = balance - amount"

fun getBalance :: "int ⇒ int" where
  "getBalance balance = balance"

datatype transaction = Deposit int | Withdraw int

fun run_account :: "transaction list ⇒ int ⇒ int" where
  "run_account [] balance = balance" |
  "run_account (t # ts) balance =
     (case t of
        Deposit amount ⇒ run_account ts (deposit amount balance) |
        Withdraw amount ⇒ run_account ts (withdraw amount balance))"

lemma balance_never_negative:
  "run_account transactions 0 ≥ 0"
  apply (induct transactions)
   apply simp
  apply auto
  done