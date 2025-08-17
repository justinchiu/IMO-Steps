import Mathlib

open Nat BigOperators Finset

namespace ImoSteps

-- Prime divisor helpers
lemma prime_divisor_cases {p : ℕ} {x y : ℤ} (hp : Nat.Prime p) (h : x * y = ↑p) :
    x = -1 ∨ x = 1 ∨ x = -↑p ∨ x = ↑p := by
  have ha := Int.natAbs_eq x
  have : x.natAbs * y.natAbs = p := by
    rw [← Int.natAbs_mul, h]
    simp
  have hab := Nat.Prime.eq_one_or_self_of_dvd hp x.natAbs ⟨y.natAbs, this.symm⟩
  cases hab with
  | inl h1 => 
    rw [h1] at ha
    cases ha <;> simp [*]
  | inr hp' =>
    rw [hp'] at ha
    cases ha <;> simp [*]

-- Factorial helpers
lemma factorial_bound_helper (n k : ℕ) (h : k ≤ n) :
    (k.factorial : ℚ) * (n - k).factorial ≤ n.factorial := by
  norm_cast
  have := Nat.factorial_mul_factorial_dvd_factorial h
  exact Nat.le_of_dvd (Nat.factorial_pos _) this

-- Recurrence relation helpers (for IMO 1985 P6)
lemma recurrence_positive (f : ℕ → ℝ → ℝ)
    (h₀ : ∀ x, f 1 x = x)
    (h₁ : ∀ n x, 0 < n → f (n + 1) x = f n x * (f n x + 1 / n))
    (n : ℕ) (x : ℝ) (hn : 0 < n) (hx : 0 < x) : 
    0 < f n x := by
  induction n, hn using Nat.le_induction with
  | base => rw [h₀]; exact hx
  | succ n hn ih =>
    rw [h₁ n x hn]
    apply mul_pos ih
    apply add_pos ih
    exact div_pos one_pos (Nat.cast_pos.mpr hn)

-- AM-GM inequality for 2 terms  
lemma two_mul_le_add_sq (a b : ℝ) : 2 * a * b ≤ a^2 + b^2 := by
  have : 0 ≤ (a - b)^2 := sq_nonneg _
  linarith [this]

end ImoSteps