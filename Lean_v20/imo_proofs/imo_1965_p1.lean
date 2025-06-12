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


/- Determine all values $x$ in the interval $0\\leq x\\leq 2\\pi $
  which satisfy the inequality\n$2\\cos x \\leq \\left| \\sqrt{1+\\sin 2x} - \\sqrt{1-\\sin 2x } \\right| \\leq \\sqrt{2}.$
  Prove that x must be
  1. \\pi / 4 ≤ x
  2. x ≤ 7 * \\pi / 4
   -/

open Real


lemma pi_div_four_lt_arcsin {x} : π / 4 < arcsin x ↔ √2 / 2 < x := by
  rw [← sin_pi_div_four, lt_arcsin_iff_sin_lt']
  have := pi_pos
  constructor <;> linarith

lemma arccos_lt_pi_div_four {x} : arccos x < π / 4 ↔ √2 / 2 < x := by
  rw [arccos, ← pi_div_four_lt_arcsin]
  constructor <;>
    · intro
      linarith


theorem imo_1965_p1_short
  (x : ℝ)
  (h₀ : 0 ≤ x)
  (h₁ : x ≤ 2 * π)
  (h₂ : 2 * Real.cos x ≤ abs (Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))))
  (h₃ : abs (Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))) ≤ Real.sqrt 2) :
  π / 4 ≤ x ∧ x ≤ 7 * π / 4 := by
  by_contra! hc
  by_cases hx₀: π / 4 ≤ x
  . have hx₁: 7 * π / 4 < x := by exact hc hx₀
    let y : ℝ := 2 * π - x
    have hy₀: cos x = cos y := by
      refine cos_eq_cos_iff.mpr ?_
      use 1
      right
      norm_cast
    have hy₂: 0 ≤ y := by exact sub_nonneg_of_le h₁
    have hy₃: y < π/4 := by linarith
    have h₆: sqrt 2 / 2 < cos x := by
      rw [hy₀]
      refine arccos_lt_pi_div_four.mp ?_
      rw [arccos_cos hy₂ ?_]
      . exact hy₃
      . refine le_of_lt ?_
        refine lt_trans hy₃ ?_
        linarith
    linarith
  . push_neg at hx₀
    have h₅: sqrt 2 / 2 < cos x := by
      refine arccos_lt_pi_div_four.mp ?_
      rw [arccos_cos h₀ (by linarith)]
      exact hx₀
    clear hx₀ hc h₀ h₁
    linarith [h₂, h₃, h₅]



theorem imo_1965_p1
  (x : ℝ)
  (h₀ : 0 ≤ x)
  (h₁ : x ≤ 2 * π)
  (h₂ : 2 * Real.cos x ≤ abs (Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))))
  (h₃ : abs (Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))) ≤ Real.sqrt 2) :
  π / 4 ≤ x ∧ x ≤ 7 * π / 4 := by
  have h₄ : 0 ≤ cos x → 2 * (cos x) ^ 2 ≤ 1 - abs (cos (2 * x)) := by
    intro h₄₀
    have h₄₁: 0 ≤ 1 + sin (2 * x) := by
      refine le_add_of_sub_left_le ?_
      rw [zero_sub]
      exact neg_one_le_sin (2 * x)
    have h₄₂: 0 ≤ 1 - sin (2 * x) := by
      refine le_sub_left_of_add_le ?_
      rw [add_zero]
      exact sin_le_one (2 * x)
    have h₄₃: (2 * cos x) ^ 2 ≤ (√(1 + sin (2 * x)) - √(1 - sin (2 * x))) ^ 2 := by
      rw [← sq_abs (√(1 + sin (2 * x)) - √(1 - sin (2 * x)))]
      refine sq_le_sq.mpr ?_
      rw [abs_abs]
      refine le_trans ?_ h₂
      rw [abs_of_nonneg ?_]
      exact mul_nonneg (by linarith) h₄₀
    rw [mul_pow, sub_sq, sq_sqrt h₄₁, sq_sqrt h₄₂, mul_assoc 2, ← sqrt_mul h₄₁, ← sq_sub_sq, one_pow] at h₄₃
    nth_rw 2 [← sin_sq_add_cos_sq (2 * x)] at h₄₃
    rw [add_sub_cancel_left (sin (2 * x) ^ 2), sqrt_sq_eq_abs] at h₄₃
    ring_nf at h₄₃
    ring_nf
    linarith
  by_contra! hc
  by_cases hx₀: π / 4 ≤ x
  . have hx₁: 7 * π / 4 < x := by exact hc hx₀
    let y : ℝ := 2 * π - x
    have hy₀: cos x = cos y := by
      refine cos_eq_cos_iff.mpr ?_
      use 1
      right
      norm_cast
    have hy₁: cos (2 * x) = cos (2 * y) := by
      refine cos_eq_cos_iff.mpr ?_
      use 2
      right
      have hy₁ : y = 2 * π - x := by rfl
      rw [hy₁]
      ring_nf
    have hy₂: 0 ≤ y := by exact sub_nonneg_of_le h₁
    have hy₃: y < π/4 := by linarith
    have hx₂: 0 ≤ cos x := by
      rw [hy₀]
      refine cos_nonneg_of_mem_Icc ?_
      refine Set.mem_Icc.mpr ?_
      constructor
      . linarith
      . linarith
    have hx₃: 0 ≤ cos (2 * x) := by
      rw [hy₁]
      refine cos_nonneg_of_mem_Icc ?_
      refine Set.mem_Icc.mpr ?_
      constructor
      . linarith
      . linarith
    have hx₄: 2 * cos x ^ 2 ≤ 1 - (2 * cos x ^ 2 - 1) := by
      rw [abs_of_nonneg hx₃, cos_two_mul] at h₄
      exact h₄ hx₂
    have h₅: cos x ^ 2 ≤ 1 / 2 := by linarith
    have h₆: sqrt 2 / 2 < cos x := by
      rw [hy₀]
      refine arccos_lt_pi_div_four.mp ?_
      rw [arccos_cos hy₂ ?_]
      . exact hy₃
      . refine le_of_lt ?_
        refine lt_trans hy₃ ?_
        linarith
    have h₇: (sqrt 2 / 2) ^ 2 < cos x ^ 2 := by
      refine sq_lt_sq' ?_ h₆
      refine neg_lt.mp ?_
      refine lt_trans ?_ h₆
      linarith
    have h₈: (√2 / 2) ^ 2 < 1 / 2 := by exact gt_of_ge_of_gt h₅ h₇
    rw [div_pow] at h₈
    simp at h₈
    linarith
  . push_neg at hx₀
    have h₅: sqrt 2 / 2 < cos x := by
      refine arccos_lt_pi_div_four.mp ?_
      rw [arccos_cos h₀ (by linarith)]
      exact hx₀
    clear h₄ hx₀ hc h₀ h₁
    linarith [h₂, h₃, h₅]
