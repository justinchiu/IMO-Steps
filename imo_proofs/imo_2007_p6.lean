import Mathlib

open NNReal Nat BigOperators Finset

/- IMO 2007 Problem 6
Given a sequence a : ℕ → NNReal that is cyclic with period 100 and satisfies
∑_{i=1}^{100} a_i^2 = 1, prove that ∑_{i=1}^{100} a_i^2 * a_{i+1} < 12/25.

The proof uses Cauchy-Schwarz and cyclic symmetry to bound the sum.
-/

theorem imo_2007_p6 (a : ℕ → NNReal)
    (h_sum : ∑ x ∈ range 100, a (x + 1)^2 = 1)
    (h_cyclic : ∀ x y, x % 100 = y % 100 → a (x + 1) = a (y + 1)) :
    ∑ x ∈ range 99, a (x + 1)^2 * a (x + 2) + a 100^2 * a 1 < 12/25 := by
  -- The sum is cyclic, so we can write it as a sum over all 100 terms
  have sum_cyclic : ∑ x ∈ range 99, a (x + 1)^2 * a (x + 2) + a 100^2 * a 1 = 
                    ∑ x ∈ range 100, a (x + 1)^2 * a (x + 2) := by
    rw [sum_range_succ]; simp
    congr 1; exact h_cyclic 100 0 rfl
  rw [sum_cyclic]
  
  -- The proof requires sophisticated analysis of cyclic sums
  -- Key steps involve:
  -- 1. Applying Cauchy-Schwarz to bound the sum
  -- 2. Using the cyclic structure to simplify
  -- 3. Optimizing to get the bound 12/25
  sorry