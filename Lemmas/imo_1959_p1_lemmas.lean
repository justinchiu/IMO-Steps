import Mathlib
set_option linter.unusedVariables.analyzeTactics true

open Nat

lemma imo_1959_p1_1
  (n : ℕ) :
  Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (7 * n + 1) (14 * n + 3) := by
  have g₀: (21 * n + 4) = (7*n + 1) + 1 * (14 * n + 3) := by linarith
  rw [g₀]
  exact gcd_add_mul_right_left (7 * n + 1) (14 * n + 3) 1


lemma imo_1959_p1_2
  (n : ℕ) :
  Nat.gcd (7 * n + 1) (14 * n + 3) = Nat.gcd (7 * n + 1) 1 := by
  have g₁: 14 * n + 3 = (7 * n + 1) * 2 + 1 := by linarith
  rw [g₁]
  exact gcd_mul_left_add_right (7 * n + 1) 1 2


lemma imo_1959_p1_3
  (n : ℕ) :
  Nat.gcd (7 * n + 1) 1 = 1 := by
  exact Nat.gcd_one_right (7 * n + 1)


lemma imo_1959_p1_4
  (n : ℕ)
  (h₁ : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (7 * n + 1) (14 * n + 3))
  (h₂ : Nat.gcd (7 * n + 1) (14 * n + 3) = Nat.gcd (7 * n + 1) 1)
  (h₃ : Nat.gcd (7 * n + 1) 1 = 1) :
  Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  rw [← h₃, ← h₂, ← h₁]
