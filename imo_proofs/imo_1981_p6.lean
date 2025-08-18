import Mathlib
import ImoSteps
set_option linter.unusedVariables.analyzeTactics true


open Nat ImoSteps

theorem imo_1981_p6
  (f : ℕ → ℕ → ℕ)
  (h₀ : ∀ y, f 0 y = y + 1)
  (h₁ : ∀ x, f (x + 1) 0 = f x 1)
  (h₂ : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) :
  ∀ y, f 4 (y + 1) = 2 ^ (f 4 y + 3) - 3 := by
  have ⟨_, h₄⟩ := ackermann_pattern f h₀ h₁ h₂
  have h₅: ∀ y, f 3 y =  2 ^ (y + 3) - 3 := by
    intro y
    induction' y with n hn
    . simp_all only [zero_eq, zero_add, mul_zero]
      omega
    . rw [h₂, h₄, hn]
      rw [Nat.mul_sub_left_distrib]
      ring_nf
      by_cases hn₀: 0 < n
      . rw [← Nat.add_sub_assoc, add_comm]
        . omega
        . have hn₂: 2 ^ 1 ≤ 2 ^ n := by exact Nat.pow_le_pow_of_le (by norm_num) hn₀
          linarith
      . have hn₁: n = 0 := by linarith
        rw [hn₁]
        omega
  intro y
  induction' y with n hn
  . simp
    rw [h₂, h₁, h₅]
  . rw [hn, h₂, h₅, h₂, h₅]
