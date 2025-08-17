import Mathlib

open Real

theorem imo_1960_p2 (x : ℝ) (h₀ : 0 ≤ 1 + 2*x)
    (h₁ : (1 - sqrt (1 + 2*x))^2 ≠ 0)
    (h₂ : 4*x^2 / (1 - sqrt (1 + 2*x))^2 < 2*x + 9) :
    -1/2 ≤ x ∧ x < 45/8 := by
  refine ⟨by linarith, ?_⟩
  -- Clear denominator and expand
  have h3 := (div_lt_iff (sq_pos_of_ne_zero _ h₁)).mp h₂
  rw [sq_sub, sq_sqrt h₀] at h3
  -- Simplify to get key inequality
  have : (2*x + 9)^2 * (1 + 2*x) > (11*x + 9)^2 := by nlinarith
  -- This gives 8x³ < 45x²
  have : 8*x^3 < 45*x^2 := by nlinarith
  -- Factor out x² to get 8x < 45
  calc x = x^2 / x := by field_simp
    _ < 45*x^2 / (8*x) := by apply div_lt_div_of_pos_right this; linarith
    _ = 45/8 := by field_simp