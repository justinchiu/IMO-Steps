import ImoSteps

open Real
set_option linter.unusedVariables.analyzeTactics true


theorem imo_1962_p2
  (x : ℝ)
  (h₀ : 0 ≤ 3 - x)
  (h₁ : 0 ≤ x + 1)
  (h₂ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)) :
  -1 ≤ x ∧ x < 1 - Real.sqrt 31 / 8 := by
  constructor
  . exact neg_le_iff_add_nonneg.mpr h₁
  have h₃: (2 * sqrt (3 - x) * sqrt (x + 1)) ^ 2 < (15/4) ^ 2 := by
    refine' pow_lt_pow_left₀ _ _ (by norm_num)
    . rw [← complete_square_sub (sqrt (3 - x)) (sqrt (x + 1))]
      simp [sq_sqrt h₀, sq_sqrt h₁]
      exact pow_lt_pow_left₀ h₂ (by norm_num) (by norm_num)
    . exact mul_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _)) (sqrt_nonneg _)
  have h₄: 4 * (x + 1) * (3 - x) < 225 / 16 := by
    norm_num at h₃
    rw [← sq_sqrt h₀, ← sq_sqrt h₁] at h₃
    simp [mul_pow] at h₃
    rwa [mul_right_comm 4]
  have hx1: x < 1 := by
    suffices g₀: x + 1 < 3 - x by linarith
    rw [← sq_sqrt h₀, ← sq_sqrt h₁]
    exact pow_lt_pow_left₀ h₂ (sqrt_nonneg _) (by norm_num)
  have h₅: x < 1 - sqrt 31 / 8 ∨ 1 + sqrt 31 / 8 < x := by
    ring_nf at h₄
    have g₀: 0 < (x - 1)^2 + 31/64 := by linarith
    rw [add_comm] at g₀
    have g₁: (x - 1)^2 + 31/64 = (x - (1 - sqrt 31 / 8)) * (x - (1 + sqrt 31 / 8)) := by ring
    rw [g₁] at g₀
    by_cases g₂: x < 1 - sqrt 31 / 8
    · left; exact g₂
    · right; linarith [pos_of_mul_pos_left g₀ (le_of_not_gt g₂)]
  exact h₅.elim id (fun h => absurd h (not_lt.2 (le_trans (le_refl _) (le_of_lt hx1))))
