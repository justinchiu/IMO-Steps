import Mathlib

open Nat

theorem imo_1959_p1 (n : ℕ) (h : 0 < n) : gcd (21*n + 4) (14*n + 3) = 1 := by
  calc gcd (21*n + 4) (14*n + 3)
    = gcd (14*n + 3) (7*n + 1) := by
      rw [gcd_comm, gcd_rec]
      congr
      have : 21*n + 4 = 1*(14*n + 3) + (7*n + 1) := by ring
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    _ = 1 := by
      rw [gcd_rec]
      congr
      have : 14*n + 3 = 2*(7*n + 1) + 1 := by ring
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      simp