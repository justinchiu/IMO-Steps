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


/-- Let $n$ be a natural number. Show that if $7$ divides $2^n-1$, then $3$ divides $n$.-/

theorem imo_1964_p1_1
  (n : ℕ)
  (h₀ : 7 ∣ (2^n - 1)) :
  3 ∣ n := by
  have h₁: 2^n - 1 ≡ 0 [MOD 7] := by exact modEq_zero_iff_dvd.mpr h₀
  apply Nat.ModEq.add_right 1 at h₁
  have h₂: 1 ≤ 2 ^ n := by exact Nat.one_le_two_pow
  rw [Nat.sub_add_cancel h₂, zero_add] at h₁
  have h₃: n ≡ 0 [MOD 3] := by
    let b:ℕ := n % 3
    let k:ℕ := n / 3
    have hb₀: b = n % 3 := by rfl
    have hb₁: b < 3 := by omega
    have hb₂: n ≡ b [MOD 3] := by exact Nat.ModEq.symm (Nat.mod_modEq n 3)
    have hb₃: n = k * 3 + b := by omega
    interval_cases b
    . exact hb₂
    . exfalso
      have hb₄: 2 ^ n ≡ 2 [MOD 7] := by
        rw [hb₃]
        induction' k with d hd
        . decide
        . rw [add_mul, one_mul, add_assoc, add_comm 3 1, ← add_assoc, pow_add]
          have hd₀: 2 ^ (d * 3 + 1) * 2 ^ 3 ≡ 2 * 2 ^ 3 [MOD 7] := by
            exact ModEq.mul hd rfl
          exact hd₀
      have hb₅: 2 % 7 = 1:= by
        refine Nat.mod_eq_of_modEq ?_ (by linarith)
        exact Nat.ModEq.trans hb₄.symm h₁
      omega
    . exfalso
      have hb₄: 2 ^ n ≡ 4 [MOD 7] := by
        rw [hb₃]
        induction' k with d hd
        . decide
        . rw [add_mul, one_mul, add_assoc, add_comm 3 2, ← add_assoc, pow_add]
          have hd₀: 2 ^ (d * 3 + 2) * 2 ^ 3 ≡ 4 * 2 ^ 3 [MOD 7] := by
            exact ModEq.mul hd rfl
          exact hd₀
      have hb₅: 4 % 7 = 1:= by
        refine Nat.mod_eq_of_modEq ?_ (by linarith)
        exact Nat.ModEq.trans hb₄.symm h₁
      omega
  exact dvd_of_mod_eq_zero h₃
