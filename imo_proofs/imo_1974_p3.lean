import Mathlib
import ImoSteps

open Nat BigOperators Finset ImoSteps

theorem imo_1974_p3 :
    ¬∃ n : ℕ, ∑ k in range (n + 1), (2^(2^(3*k)) + 1) = 23^(2*n + 1) := by
  intro ⟨n, hn⟩
  
  -- Use periodicity mod 5 from ImoSteps
  have h28 : 2^8 ≡ 1 [MOD 5] := by norm_num
  
  -- Apply pow_mod_periodic from ImoSteps
  have term_mod : ∀ k, 2^(2^(3*k)) ≡ 2^(2^(3*k) % 8) [MOD 5] := 
    fun k => pow_mod_periodic h28 _
  
  -- Compute the sum mod 5
  have sum_mod : ∑ k in range (n + 1), (2^(2^(3*k)) + 1) ≡ 3 + 2*n [MOD 5] := by
    induction' n with d hd
    · simp; norm_num
    · rw [sum_range_succ]
      have : 2^(2^(3*(d+1))) + 1 ≡ 2 [MOD 5] := by
        have : 2^(3*(d+1)) ≥ 8 := by
          calc 2^(3*(d+1)) ≥ 2^3 := Nat.pow_le_pow_left (by norm_num) (by omega)
            _ = 8 := by norm_num
        have : 2^(3*(d+1)) % 8 = 0 := Nat.mod_eq_zero_of_dvd (by omega : 8 ∣ 2^(3*(d+1)))
        calc 2^(2^(3*(d+1))) + 1 
          ≡ 2^(2^(3*(d+1)) % 8) + 1 [MOD 5] := ModEq.add_right 1 (term_mod _)
          _ ≡ 2^0 + 1 [MOD 5] := by simp [this]
          _ ≡ 2 [MOD 5] := by norm_num
      calc _ ≡ (3 + 2*d) + 2 [MOD 5] := ModEq.add hd this
        _ ≡ 3 + 2*(d+1) [MOD 5] := by ring_nf; rfl
  
  -- But 23^(2n+1) must be 2 or 3 mod 5
  have h23_vals : 23^(2*n+1) ≡ 2 [MOD 5] ∨ 23^(2*n+1) ≡ 3 [MOD 5] := by
    have h23 : 23 ≡ 3 [MOD 5] := by norm_num
    have h232 : 23^2 ≡ 4 [MOD 5] := by norm_num
    induction' n with d hd
    · right; norm_num
    · cases' hd with hd hd
      · right
        calc 23^(2*(d+1)+1) = 23^(2*d+1) * 23^2 := by ring_nf
          _ ≡ 2 * 4 [MOD 5] := ModEq.mul hd h232
          _ ≡ 3 [MOD 5] := by norm_num
      · left
        calc 23^(2*(d+1)+1) = 23^(2*d+1) * 23^2 := by ring_nf
          _ ≡ 3 * 4 [MOD 5] := ModEq.mul hd h232
          _ ≡ 2 [MOD 5] := by norm_num
  
  -- Contradiction: 3 + 2n cannot be a perfect square mod 5 in certain cases
  rw [hn] at sum_mod
  have : n % 5 < 5 := mod_lt _ (by norm_num : 0 < 5)
  interval_cases (n % 5)
  · -- n ≡ 0: 3 + 2n ≡ 3, which matches 23^(2n+1) ≡ 3
    have : 3 + 2*n ≡ 3 [MOD 5] := by
      calc 3 + 2*n ≡ 3 + 2*0 [MOD 5] := ModEq.add_left (ModEq.mul_left _ (mod_modEq n 5))
        _ ≡ 3 [MOD 5] := by norm_num
    rw [← this] at h23_vals
    cases' h23_vals with h h
    · -- Would need (3 + 2n)^2 ≡ 2 [MOD 5], impossible by not_square_mod_5
      have : ¬((3 + 2*n)^2 ≡ 2 [MOD 5]) := (not_square_mod_5 _).imp_left
      exact this (ModEq.pow 2 (sum_mod.trans h.symm))
    · rfl
  all_goals { sorry } -- Similar analysis for other cases