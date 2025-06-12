import Mathlib
set_option linter.unusedVariables.analyzeTactics true
set_option pp.instanceTypes true
set_option pp.numericTypes true
set_option pp.coercions.types true
set_option pp.letVarTypes true
set_option pp.structureInstanceTypes true
set_option pp.instanceTypes true
set_option pp.mvars.withType true
set_option pp.coercions true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true



open Nat

/-- Show that for any natural number $n$, $7$ does not divide $2^n + 1$. -/

theorem imo_1964_p1_2
  (n : ℕ) :
  ¬ 7 ∣ (2^n + 1) := by
  by_contra hc
  have h₀: 2 ^ n + 1 ≡ 0 [MOD 7] := by exact ModEq.symm (Dvd.dvd.zero_modEq_nat hc)
  have h₁: 2 ^ n ≡ 6 [MOD 7] := by exact ModEq.add_right_cancel' 1 h₀
  let b:ℕ := n % 3
  let k:ℕ := n / 3
  have hb₀: b = n % 3 := by rfl
  have hb₁: b < 3 := by omega
  have hb₂: n ≡ b [MOD 3] := by exact Nat.ModEq.symm (Nat.mod_modEq n 3)
  have hb₃: n = k * 3 + b := by omega
  interval_cases b
  . have h₂: 2 ^ n ≡ 1 [MOD 7] := by
      rw [hb₃, add_zero]
      induction' k with d hd
      . decide
      . rw [add_mul, one_mul, pow_add]
        have hd₀: 2 ^ (d * 3) * 2 ^ 3 ≡ 1 * 2 ^ 3 [MOD 7] := by
          exact ModEq.mul hd rfl
        exact hd₀
    have hb₅: 1 % 7 = 6 := by
      refine Nat.mod_eq_of_modEq ?_ (by linarith)
      exact Nat.ModEq.trans h₂.symm h₁
    omega
  . have h₂: 2 ^ n ≡ 2 [MOD 7] := by
      rw [hb₃]
      induction' k with d hd
      . decide
      . rw [add_mul, one_mul, add_assoc, add_comm 3 1, ← add_assoc, pow_add]
        have hd₀: 2 ^ (d * 3 + 1) * 2 ^ 3 ≡ 2 * 2 ^ 3 [MOD 7] := by
          exact ModEq.mul hd rfl
        exact hd₀
    have hb₅: 2 % 7 = 6 := by
      refine Nat.mod_eq_of_modEq ?_ (by linarith)
      exact Nat.ModEq.trans h₂.symm h₁
    omega
  . have h₂: 2 ^ n ≡ 4 [MOD 7] := by
      rw [hb₃]
      induction' k with d hd
      . decide
      . rw [add_mul, one_mul, add_assoc, add_comm 3 2, ← add_assoc, pow_add]
        have hd₀: 2 ^ (d * 3 + 2) * 2 ^ 3 ≡ 4 * 2 ^ 3 [MOD 7] := by
          exact ModEq.mul hd rfl
        exact hd₀
    have hb₅: 4 % 7 = 6 := by
      refine Nat.mod_eq_of_modEq ?_ (by linarith)
      exact Nat.ModEq.trans h₂.symm h₁
    omega
