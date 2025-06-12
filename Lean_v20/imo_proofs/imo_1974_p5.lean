import Mathlib

set_option linter.unusedVariables.analyzeTactics true
set_option pp.instanceTypes true
set_option pp.numericTypes true
set_option pp.coercions.types true
set_option pp.letVarTypes true
set_option pp.structureInstanceTypes true
set_option pp.instanceTypes true
set_option pp.mvars.withType true
set_option pp.coercions true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true



/- Determine all possible values of $S = \\frac{a}{a+b+d}+\\frac{b}{a+b+c}+\\frac{c}{b+c+d}+\\frac{d}{a+c+d}$
  where $a, b, c, d,$ are arbitrary positive numbers.
  Prove that S is always greater than one and less than two.
  -/

open Real

theorem imo_1974_p5
  (a b c d s : ℝ)
  (hp : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₀ : s = a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)) :
  1 < s ∧ s < 2 := by
  constructor
  . have h₁: a / (a + b + c + d) + b / (a + b + c + d) + c / (a + b + c + d) + d / (a + b + c + d) < s := by
      rw [h₀]
      refine add_lt_add ?_ ?_
      . refine add_lt_add ?_ ?_
        . refine add_lt_add ?_ ?_
          . refine (div_lt_div_iff_of_pos_left hp.1 ?_ ?_).mpr ?_
            all_goals try linarith
          . refine (div_lt_div_iff_of_pos_left hp.2.1 ?_ ?_).mpr ?_
            all_goals try linarith
        . refine (div_lt_div_iff_of_pos_left hp.2.2.1 ?_ ?_).mpr ?_
          all_goals try linarith
      . refine (div_lt_div_iff_of_pos_left hp.2.2.2 ?_ ?_).mpr ?_
        all_goals try linarith
    rw [← add_div, ← add_div, ← add_div, div_self (by linarith)] at h₁
    exact h₁
  . have h₁: s < a / (a + b) + b / (a + b) + c / (c + d) + d / (c + d) := by
      rw [h₀]
      refine add_lt_add ?_ ?_
      . refine add_lt_add ?_ ?_
        . refine add_lt_add ?_ ?_
          . refine (div_lt_div_iff_of_pos_left hp.1 ?_ ?_).mpr ?_
            all_goals try linarith
          . refine (div_lt_div_iff_of_pos_left hp.2.1 ?_ ?_).mpr ?_
            all_goals try linarith
        . refine (div_lt_div_iff_of_pos_left hp.2.2.1 ?_ ?_).mpr ?_
          all_goals try linarith
      . refine (div_lt_div_iff_of_pos_left hp.2.2.2 ?_ ?_).mpr ?_
        all_goals try linarith
    rw [← add_div, div_self (by linarith), add_assoc, ← add_div, div_self (by linarith)] at h₁
    ring_nf at h₁
    assumption
