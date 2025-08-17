import Mathlib
import ImoSteps

open Nat ImoSteps

theorem imo_1959_p1 (n : ℕ) (h : 0 < n) : gcd (21*n + 4) (14*n + 3) = 1 := by
  calc gcd (21*n + 4) (14*n + 3)
    = gcd ((14*n + 3) + (7*n + 1)) (14*n + 3) := by ring_nf
    _ = gcd (7*n + 1) (14*n + 3) := by rw [gcd_comm]; exact gcd_reduction _ _ _
    _ = gcd (7*n + 1) 1 := by
      conv_rhs => rw [show 14*n + 3 = 1 + 2*(7*n + 1) by ring]
      exact gcd_reduction _ _ _
    _ = 1 := gcd_one_right _