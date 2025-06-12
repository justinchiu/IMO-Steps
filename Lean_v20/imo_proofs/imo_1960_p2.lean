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

open Real


/-- For what values of the variable $x$ does the following inequality hold:\n\n$\\dfrac{4x^2}{(1 - \\sqrt {2x + 1})^2} < 2x + 9 \\ ?$
  Show that x must satisfy both of the following conditions:
   condition 1: x must be greater than or equal to \\frac{-1}{2}
   condition 2: x must be less than \\frac{45}{8}
-/

theorem imo_1960_p2
  (x : ℝ)
  (h₀ : 0 ≤ 1 + 2 * x)
  (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9) :
  -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  apply And.intro
  . linarith
  . have h₃: 4 * x ^ 2 < (2 * x + 9) * (1 - sqrt (1 + 2 * x) ) ^ 2 := by
      refine' (div_lt_iff₀ _).mp h₂
      refine Ne.lt_of_le (id (Ne.symm h₁)) ?_
      exact sq_nonneg (1 - sqrt (1 + 2 * x))
    have h₄: (1 - sqrt (1 + 2 * x)) ^ 2 = (2 + 2 * x) - 2 * sqrt (1 + 2 * x) := by
      ring_nf at *
      rw [Real.sq_sqrt h₀]
      ring_nf
    have h₅: (2 * x + 9) ^ 2 * (sqrt (1 + 2 * x)) ^ 2 < (11 * x + 9) ^ 2 := by
      rw [← mul_pow]
      refine' pow_lt_pow_left₀ _  _ (by norm_num)
      rw [h₄] at h₃
      simp_all only [ne_eq, zero_lt_two]
      . linarith
      . refine' mul_nonneg _ _
        linarith
        exact sqrt_nonneg (1 + 2 * x)
    have h₆: 8 * x^3 < 45 * x^2 := by
      rw [Real.sq_sqrt h₀] at h₅
      ring_nf at h₅
      linarith
    have h₇₁: 0 ≤ x^2 := by exact sq_nonneg x
    have h₇: 8 * x < 45 := by
      refine' lt_of_mul_lt_mul_right ?_ h₇₁
      ring_nf at *
      exact h₆
    linarith
