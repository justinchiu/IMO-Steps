import Mathlib

open Real

theorem imo_1963_p5 : cos (π/7) - cos (2*π/7) + cos (3*π/7) = 1/2 := by
  let S := cos (π/7) - cos (2*π/7) + cos (3*π/7)
  -- Multiply by 2*sin(π/7) and use product-to-sum formulas
  have key : sin (π/7) * (2*S) = sin (π/7) := by
    simp only [S]
    rw [mul_sub, mul_add, mul_comm 2]
    conv_lhs => 
      rw [sin_mul_cos, sin_mul_cos, sin_mul_cos]
    simp [sin_add, sin_sub]
    ring_nf
    -- sin(4π/7) = sin(3π/7) cancels out
    have : sin (4*π/7) = sin (3*π/7) := by
      rw [show 4*π/7 = π - 3*π/7 by ring, sin_pi_sub]
    simp [this]
  -- Since sin(π/7) ≠ 0, we can cancel it
  have h_ne : sin (π/7) ≠ 0 := by
    apply sin_ne_zero_iff.mpr
    intro n
    field_simp at *
    omega
  linarith [mul_right_cancel₀ h_ne key]