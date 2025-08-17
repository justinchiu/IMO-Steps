import Mathlib

open Real

theorem imo_1962_p2 (x : ℝ) 
    (h₀ : 0 ≤ 3 - x) (h₁ : 0 ≤ x + 1)
    (h₂ : 1/2 < sqrt (3 - x) - sqrt (x + 1)) :
    -1 ≤ x ∧ x < 1 - sqrt 31 / 8 := by
  refine ⟨by linarith, ?_⟩
  -- Square the inequality to get a bound
  have key : 4*(x + 1)*(3 - x) < 225/16 := by
    calc 4*(x + 1)*(3 - x) 
      = (2*sqrt (x + 1)*sqrt (3 - x))^2 := by 
        rw [mul_pow, mul_pow, sq_sqrt h₁, sq_sqrt h₀]; ring
      _ < (4 - (sqrt (3 - x) - sqrt (x + 1))^2)^2 := by
        have : sqrt (3 - x) - sqrt (x + 1) > 1/2 := h₂
        have : (sqrt (3 - x) - sqrt (x + 1))^2 > 1/4 := by nlinarith
        have : 4 - (sqrt (3 - x) - sqrt (x + 1))^2 < 15/4 := by linarith
        rw [sub_sq, sq_sqrt h₀, sq_sqrt h₁] at this
        nlinarith
      _ < (15/4)^2 := by nlinarith
      _ = 225/16 := by norm_num
  -- This gives x² - 2x + 33/64 > 0
  have quad : x^2 - 2*x + 33/64 > 0 := by linarith
  -- Factor as (x - (1 - √31/8))(x - (1 + √31/8)) > 0
  have factor : x^2 - 2*x + 33/64 = (x - (1 - sqrt 31/8))*(x - (1 + sqrt 31/8)) := by
    field_simp; ring_nf; norm_num
  rw [factor] at quad
  -- Since x < 1 < 1 + √31/8, we need x < 1 - √31/8
  have hx1 : x < 1 := by
    have : sqrt (x + 1) < sqrt (3 - x) := by linarith
    nlinarith [sq_le_sq' (sqrt_nonneg _) (sqrt_nonneg _) this]
  cases' (mul_pos_iff.mp quad) with h h
  · exact h.1
  · linarith [h.2]