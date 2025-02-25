import Mathlib
set_option linter.unusedVariables.analyzeTactics true

open Real

theorem imo_1960_p2_1
  (x : ℝ)
  (h₀ : 0 ≤ 1 + 2 * x)
  -- (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  -- (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9)
  (h₃ : 7 * x ≤ -(7/4)) :
  x ^ 3 + x ^ 2 * (2 / 5) ≤ (15/400) ∧ x / 16 + 3 / 160 ≤ (5/100) * x ^ 2 := by
  have h₄: -(1/2) ≤ x := by linarith
  have h₅: x ≤ -(1/4) := by linarith
  have h₆: x ^ 2 ≤ (-(1 / 2)) ^ 2 := by
    refine sq_le_sq.mpr ?_
    norm_num
    have h₆₁: x < 0 := by linarith
    rw [abs_of_neg h₆₁]
    rw [abs_of_pos (by norm_num)]
    exact neg_le.mp h₄
  have h₇: (-(1 / 4)) ^ 2 ≤ x ^ 2 := by
    refine sq_le_sq.mpr ?_
    have h₆₁: x < 0 := by linarith
    rw [abs_of_neg h₆₁]
    rw [abs_of_neg (by norm_num)]
    norm_num
    exact le_neg_of_le_neg h₅
  norm_num at h₆ h₇
  constructor
  . have h₈: x + (4/10) ≤ (15/100) := by linarith
    have h₉: (x + (4/10)) * x ^ 2 ≤ (15/100) * (1 / 4) := by
      refine mul_le_mul h₈ h₆ ?_ ?_
      . exact sq_nonneg x
      . norm_num
    linarith
  . linarith


theorem imo_1960_p2_2
  (x : ℝ)
  -- (h₀ : 0 ≤ 1 + 2 * x)
  (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9) :
  4 * x ^ 2 < (2 * x + 9) * (1 - √(1 + 2 * x)) ^ 2 := by
  refine' (div_lt_iff₀ ?_).mp h₂
  refine Ne.lt_of_le (id (Ne.symm h₁)) ?_
  exact sq_nonneg (1 - sqrt (1 + 2 * x))

theorem imo_1960_p2_3
  (x : ℝ)
  (h₀ : 0 ≤ 1 + 2 * x) :
  -- (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  -- (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9) :
  (1 - sqrt (1 + 2 * x)) ^ 2 = (2 + 2 * x) - 2 * sqrt (1 + 2 * x) := by
  ring_nf
  ring_nf at h₀
  rw [Real.sq_sqrt h₀]
  ring_nf

theorem imo_1960_p2_4
  (x : ℝ)
  (h₀ : 0 ≤ 1 + 2 * x)
  -- (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  -- (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9)
  (h₃: 4 * x ^ 2 < (2 * x + 9) * (1 - sqrt (1 + 2 * x) ) ^ 2)
  (h₄: (1 - sqrt (1 + 2 * x)) ^ 2 = (2 + 2 * x) - 2 * sqrt (1 + 2 * x)) :
  (2 * x + 9) ^ 2 * (sqrt (1 + 2 * x)) ^ 2 < (11 * x + 9) ^ 2 := by
  rw [← mul_pow]
  refine' pow_lt_pow_left₀ ?_  ?_ (by norm_num)
  . rw [h₄] at h₃
    linarith
  . refine' mul_nonneg ?_ ?_
    . linarith
    . exact sqrt_nonneg (1 + 2 * x)


theorem imo_1960_p2_5
  (x : ℝ)
  (h₀ : 0 ≤ 1 + 2 * x)
  -- (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  -- (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9)
  (h₃: (2 * x + 9) ^ 2 * (sqrt (1 + 2 * x)) ^ 2 < (11 * x + 9) ^ 2) :
  8 * x^3 < 45 * x^2 := by
  rw [Real.sq_sqrt h₀] at h₃
  ring_nf at h₃
  linarith


theorem imo_1960_p2_6
  (x : ℝ)
  -- (h₀ : 0 ≤ 1 + 2 * x)
  -- (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  -- (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9)
  (h₃: x^3 * 8 < x^2 * 45) :
  x < 45/8 := by
  have h₇₁: 0 ≤ x^2 := by exact sq_nonneg x
  refine (lt_div_iff₀ (by norm_num)).mpr ?_
  refine' lt_of_mul_lt_mul_right ?_ h₇₁
  ring_nf
  exact h₃


theorem imo_1960_p2_7
  (x : ℝ)
  (h₀ : 0 ≤ 1 + 2 * x)
  (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9) :
  0 < x ^ 2 ∨ x ^ 2 = 0 := by
  have h₄: 0 ≤ x ^ 2 := by
    exact sq_nonneg x
  exact LE.le.gt_or_eq h₄


theorem imo_1960_p2_8
  (x : ℝ)
  -- (h₀ : 0 ≤ 1 + 2 * x)
  -- (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  -- (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9)
  (h₃: 4 * x ^ 2 < (2 * x + 9) * (1 - sqrt (1 + 2 * x) ) ^ 2)
  (h₄: (1 - sqrt (1 + 2 * x)) ^ 2 = (2 + 2 * x) - 2 * sqrt (1 + 2 * x)) :
  (2 * x + 9) * √(1 + 2 * x) < 11 * x + 9 := by
  rw [h₄] at h₃
  linarith


theorem imo_1960_p2_9
  (x : ℝ)
  (h₀ : 0 ≤ 1 + 2 * x) :
  -- (h₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0)
  -- (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9) :
  0 ≤ (2 * x + 9) * √(1 + 2 * x) := by
  refine' mul_nonneg ?_ ?_
  . linarith
  . exact sqrt_nonneg (1 + 2 * x)
