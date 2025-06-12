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


/- Consider a pair of positive integers $a,b$ such that $a * b * (a+b)$ is not divisible by $7$, but $(a+b)^7-a^7-b^7$ is divisible by $7^7$.
  Prove that the following will hold for any such pair: 19 <= a + b. -/


theorem imo_1984_p2
  (a b : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : ¬ 7 ∣ a * b * (a + b))
  (h₂ : (7^7) ∣ ((a + b)^7 - a^7 - b^7)) :
  19 ≤ a + b := by
  have h₃: ¬ 7 ∣ (a + b) := by
    by_contra! hh₀
    have hh₁: 7 ∣ a * b * (a + b) := by exact Dvd.dvd.mul_left hh₀ (a * b)
    exact h₁ hh₁
  have h₄: ¬ 7 ∣ b := by
    by_contra! hh₀
    have hh₁: 7 ∣ a * b * (a + b) := by
      rw [mul_comm a b, mul_assoc]
      exact Dvd.dvd.mul_right hh₀ (a * (a + b))
    exact h₁ hh₁
  have h₁₁: ¬ 7 ∣ a := by
    by_contra! hh₀
    have hh₁: 7 ∣ a * b * (a + b) := by
      rw [mul_assoc]
      exact Dvd.dvd.mul_right hh₀ (b * (a + b))
    exact h₁ hh₁
  have h₅: (a + b) ^ 7 - a ^ 7 - b ^ 7 = 7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 := by
    ring_nf
    rw [add_assoc, Nat.sub_sub, Nat.add_sub_cancel]
  rw [h₅] at h₂
  have h₆: 7 ^ 6 ∣ (a ^ 2 + a * b + b ^ 2) ^ 2 := by
    rw [pow_succ'] at h₂
    repeat rw [mul_assoc] at h₂
    apply (Nat.mul_dvd_mul_iff_left (by linarith)).mp at h₂
    have h₆₀: (a ^ 2 + a * b + b ^ 2) ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 ?_
      refine Nat.ne_zero_iff_zero_lt.mpr ?_
      refine add_pos ?_ ?_
      . refine add_pos ?_ ?_
        . refine Nat.pow_pos h₀.1
        . exact mul_pos h₀.1 h₀.2
      . refine Nat.pow_pos h₀.2
    have h₆₁: a * b * (a + b) ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      . refine mul_ne_zero (by linarith) (by linarith)
      . refine Nat.ne_zero_iff_zero_lt.mpr ?_
        refine add_pos h₀.1 h₀.2
    have h₆₂: a * (b * ((a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2)) ≠ 0 := by
      refine mul_ne_zero (by linarith) ?_
      refine mul_ne_zero (by linarith) ?_
      refine mul_ne_zero (by linarith) h₆₀
    have h₆₃: Nat.Prime 7 := by decide
    refine (Nat.Prime.pow_dvd_iff_le_factorization h₆₃ h₆₀).mpr ?_
    have h₆₄: ((a ^ 2 + a * b + b ^ 2) ^ 2).factorization 7 =
      (a * (b * ((a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2))).factorization 7 := by
      rw [← mul_assoc, ← mul_assoc]
      rw [Nat.factorization_mul h₆₁ h₆₀]
      simp
      refine (Nat.factorization_eq_zero_iff _ 7).mpr ?_
      right
      left
      refine Nat.Prime.not_dvd_mul h₆₃ ?_ h₃
      exact Nat.Prime.not_dvd_mul h₆₃ h₁₁ h₄
    rw [h₆₄]
    refine (Nat.Prime.pow_dvd_iff_le_factorization h₆₃ h₆₂).mp ?_
    exact h₂
  have h₇: 7 ^ 3 ∣ (a ^ 2 + a * b + b ^ 2) := by
    have h₇₀: 2 ≠ 0 := by linarith
    exact (Nat.pow_dvd_pow_iff h₇₀).mp h₆
  have h₈: 343 < (a + b) ^ 2 := by
    have h₈₀: 0 < a ^ 2 + a * b + b ^ 2 := by
      refine add_pos ?_ ?_
      . refine add_pos ?_ ?_
        . exact sq_pos_of_pos h₀.1
        . exact mul_pos h₀.1 h₀.2
      . exact sq_pos_of_pos h₀.2
    apply (Nat.le_of_dvd h₈₀) at h₇
    refine lt_of_le_of_lt h₇ ?_
    ring_nf
    simp
    nth_rw 1 [← mul_one (a * b)]
    refine (mul_lt_mul_left ?_).mpr (by linarith)
    exact mul_pos h₀.1 h₀.2
  have h₉: 18 < (a + b) := by
    by_contra! hc
    have hc₀: (a + b) ^ 2 ≤ 18 ^ 2 := by
      exact Nat.pow_le_pow_left hc 2
    linarith
  exact Nat.succ_le_of_lt h₉
