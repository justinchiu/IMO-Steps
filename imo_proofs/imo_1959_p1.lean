import Mathlib

open Nat

theorem imo_1959_p1 (n : ℕ) (h : 0 < n) : gcd (21*n + 4) (14*n + 3) = 1 := by
  -- Use the Euclidean algorithm
  calc gcd (21*n + 4) (14*n + 3)
    = gcd (14*n + 3) ((21*n + 4) % (14*n + 3)) := gcd_rec _ _
    _ = gcd (14*n + 3) (7*n + 1) := by
      congr
      have : 21*n + 4 = 1*(14*n + 3) + (7*n + 1) := by ring
      rw [this, add_mod_right]
      simp [Nat.mod_eq_of_lt]
      omega
    _ = gcd (7*n + 1) ((14*n + 3) % (7*n + 1)) := gcd_rec _ _
    _ = gcd (7*n + 1) 1 := by
      congr
      have : 14*n + 3 = 2*(7*n + 1) + 1 := by ring
      rw [this, add_mod_right]
      simp [Nat.mod_eq_of_lt]
      omega
    _ = 1 := gcd_one_right _