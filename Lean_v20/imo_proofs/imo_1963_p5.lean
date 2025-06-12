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


/-- Prove that $\\cos{\\frac{\\pi}{7}}-\\cos{\\frac{2\\pi}{7}}+\\cos{\\frac{3\\pi}{7}}=\\frac{1}{2}$.-/

lemma sin_mul_cos
  (x y : ℝ) :
  Real.sin x * Real.cos y = (sin (x + y) + sin (x - y)) / 2 := by
    rw [sin_add, sin_sub]
    simp

theorem imo_1963_p5 :
  Real.cos (π / 7) - Real.cos (2 * π / 7) + Real.cos (3 * π / 7) = 1 / 2 := by
  let S:ℝ := Real.cos (π / 7) - Real.cos (2 * π / 7) + Real.cos (3 * π / 7)
  have h₀: Real.sin (π / 7) * (S * 2) = Real.sin (π / 7) := by
    have h₀₀: sin (π * (1 / 7)) * cos (π * (1 / 7)) * 2 = sin (2 * (π * (1 / 7))) := by
      rw [Real.sin_two_mul]
      exact (mul_rotate 2 (sin (π * (1 / 7))) (cos (π * (1 / 7)))).symm
    rw [mul_comm _ 2, ← mul_assoc]
    rw [mul_add, mul_sub]
    ring_nf at h₀₀
    ring_nf
    rw [h₀₀, sin_mul_cos, sin_mul_cos]
    rw [← mul_add, ← mul_sub, ← mul_add, ← mul_sub]
    norm_num
    ring_nf
    have h₀₁: -sin (π * (3 / 7)) + sin (π * (4 / 7)) = 0 := by
      rw [add_comm]
      refine add_neg_eq_of_eq_add ?_
      rw [zero_add]
      refine sin_eq_sin_iff.mpr ?_
      use 0
      right
      ring
    linarith
  have h₁: S = 1 / 2 := by
    refine eq_div_of_mul_eq (by norm_num) ?_
    nth_rewrite 2 [← mul_one (sin (π / 7))] at h₀
    refine (mul_right_inj' ?_).mp h₀
    refine sin_ne_zero_iff.mpr ?_
    intro n
    ring_nf
    rw [mul_comm]
    simp
    push_neg
    constructor
    . by_contra! hc₀
      have hc₁: 7 * (↑n:ℝ) = 1 := by
        rw [mul_comm]
        exact (mul_eq_one_iff_eq_inv₀ (by norm_num)).mpr hc₀
      norm_cast at hc₁
      have g₀: 0 < n := by linarith
      linarith
    . exact pi_ne_zero
  exact h₁
