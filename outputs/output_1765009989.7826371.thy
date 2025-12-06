```isabelle
fun isLeapYear :: "int ⇒ bool" where
  "isLeapYear year = ((year mod 4 = 0 ∧ year mod 100 ≠ 0) ∨ (year mod 400 = 0))"

fun zune_step :: "int ⇒ int ⇒ (int × int)" where
  "zune_step days year =
    (if days > 365 then
      (if isLeapYear year then
        (if days > 366 then (days - 366, year + 1)
        else (days, year))
      else (days - 365, year + 1))
    else (days, year))"

fun zune_loop :: "nat ⇒ int ⇒ int ⇒ (int × int)" where
  "zune_loop fuel days year =
    (if fuel = 0 then (days, year)
    else let (d', y') = zune_step days year
        in if d' = days ∧ y' = year then (d', y')
          else zune_loop (fuel - 1) d' y')"

lemma zune_bug_stuck:
  assumes "isLeapYear year" and "days = 366"
  shows "zune_step days year = (days, year)"
  using assms by simp
```