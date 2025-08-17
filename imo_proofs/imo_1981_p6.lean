import Mathlib

open Nat

theorem imo_1981_p6 (f : ℕ → ℕ → ℕ)
    (h₀ : ∀ y, f 0 y = y + 1)
    (h₁ : ∀ x, f (x + 1) 0 = f x 1)
    (h₂ : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) :
    ∀ y, f 4 (y + 1) = 2^(f 4 y + 3) - 3 := by
  -- Compute f for small x values
  have f1 : ∀ y, f 1 y = y + 2 := by
    intro y; induction y with
    | zero => simp [h₁, h₀]
    | succ n ih => rw [h₂, h₀, ih]
  
  have f2 : ∀ y, f 2 y = 2*y + 3 := by
    intro y; induction y with
    | zero => simp [h₁, f1]
    | succ n ih => rw [h₂, f1, ih]; ring
  
  have f3 : ∀ y, f 3 y = 2^(y + 3) - 3 := by
    intro y; induction y with
    | zero => simp [h₁, f2]; norm_num
    | succ n ih => 
      rw [h₂, f2, ih, mul_sub, mul_comm 2, ← pow_succ]
      congr 1; ring
  
  -- Main result for f 4
  intro y; induction y with
  | zero => simp [h₁, f3]
  | succ n ih => rw [h₂, f3, ih, h₂, f3]