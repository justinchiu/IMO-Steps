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


/- Let $a,b$ be two natural numbers. When we divide $a^2+b^2$ by $a+b$, we the the remainder $r$ and the quotient $q.$
  Determine all pairs $(a, b)$ for which $q^2 + r = 1977.$
  Show that (a,b) can take only one of these values: (7, 50) or (37,50) or (50, 7) or (50, 37) .-/



open Nat

theorem imo_1977_p5_minif2f
  (a b q r : ℕ)
  (hp: 0 < a ∧ 0 < b)
  (h₀ : r = (a ^ 2 + b ^ 2) % (a + b))
  (h₁ : q = (a ^ 2 + b ^ 2) / (a + b))
  (h₂ : q ^ 2 + r = 1977) :
  (abs ((a:ℤ) - 22) = 15 ∧ abs ((b:ℤ) - 22) = 28) ∨ (abs ((a:ℤ) - 22) = 28 ∧ abs ((b:ℤ) - 22) = 15) := by
  have h₅: a ^ 2 + b ^ 2 = 44 * (a + b) + 41 := by
    have h₅₀: r = 1977 - q ^ 2 := by exact Nat.eq_sub_of_add_eq' h₂
    have h₅₁: 0 < a + b := by linarith
    have h₅₂: a ^ 2 + b ^ 2 = q * (a + b) + r := by
      rw [h₀, h₁,]
      exact Eq.symm (div_add_mod' (a ^ 2 + b ^ 2) (a + b))
    have h₅₃: q ≤ 44 := by
      by_contra hc₀
      push_neg at hc₀
      apply Nat.succ_le_iff.mpr at hc₀
      have hc₁: 45 ^ 2 ≤ q ^ 2 := by exact Nat.pow_le_pow_left hc₀ 2
      linarith
    have h₅₄: 43 < q := by
      have g₀: (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by exact add_sq_le
      have g₁: 2 * (a ^ 2 + b ^ 2) < 2 * (45 * (a + b)) := by
        refine (Nat.mul_lt_mul_left (by linarith)).mpr ?_
        have g₁₀: 45 = 44 + 1 := by linarith
        rw [h₅₂, g₁₀, add_mul, one_mul]
        refine add_lt_add_of_le_of_lt ?_ ?_
        . exact Nat.mul_le_mul_right (a + b) h₅₃
        . rw [h₀]
          exact Nat.mod_lt (a ^ 2 + b ^ 2) h₅₁
      have g₂: a + b < 90 := by
        apply lt_of_le_of_lt g₀ at g₁
        rw [pow_two] at g₁
        rw [← mul_assoc] at g₁
        simp at g₁
        exact (Nat.mul_lt_mul_right h₅₁).mp g₁
      have g₃: r < 90 := by
        rw [h₀]
        refine lt_trans ?_ g₂
        exact Nat.mod_lt (a ^ 2 + b ^ 2) h₅₁
      by_contra hc₀
      push_neg at hc₀
      have hc₁: q ^ 2 ≤ 43 ^ 2 := by exact Nat.pow_le_pow_left hc₀ 2
      apply Nat.succ_le_iff.mp at g₃
      linarith
    interval_cases q
    simp at *
    rw [h₅₀] at h₅₂
    exact h₅₂
  have h₆: ((a:ℤ) - 22) ^ 2 + ((b:ℤ) - 22) ^ 2 = 1009 := by
    ring_nf
    linarith
  have h₇: Nat.Prime 1009 := by bound
  have h₈: 15 ^ 2 + 28 ^ 2 = 1009 := by linarith
  have h₉: ((a:ℤ) - 22) ^ 2 = 15 ^ 2 ∨ ((a:ℤ) - 22) ^ 2 = 28 ^ 2 := by
    by_contra hc
    push_neg at hc
    cases' hc with hc₀ hc₁
    have h₈₀: 0 ≤ ((a:ℤ) - 22) ^ 2 := by exact sq_nonneg ((a:ℤ) - 22)
    have h₈₂: IsSquare (((a:ℤ) - 22) ^ 2) := by exact IsSquare.sq ((a:ℤ) - 22)
    have h₈₃: IsSquare (((b:ℤ) - 22) ^ 2) := by exact IsSquare.sq ((b:ℤ) - 22)
    apply Nat.Prime.prime at h₇
    apply eq_sub_of_add_eq' at h₆
    by_cases ha₀: 53 < a
    . apply Nat.succ_le_iff.mpr at ha₀
      simp at ha₀
      have ha₁: 32 ^ 2 ≤ ((a:ℤ) - 22) ^ 2 := by
        refine pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hb₁: 0 ≤ ((b:ℤ) - 22) ^ 2 := by exact sq_nonneg ((b:ℤ) - 22)
      linarith
    . push_neg at ha₀
      let s : ℤ := 1009 - (↑(a:ℤ) - 22) ^ 2
      have hs: s = 1009 - (↑(a:ℤ) - 22) ^ 2 := by rfl
      have ha₁: ∀ k n:ℤ, n^2 < k ∧ k < (n + 1) ^ 2 → ¬ IsSquare k := by
        intros k n hk₀
        cases' hk₀ with hk₀ hk₁
        by_contra hc₂
        apply (isSquare_iff_exists_sq k).mp at hc₂
        let ⟨d, hd₀⟩ := hc₂
        rw [hd₀] at hk₀ hk₁
        apply sq_lt_sq.mp at hk₀
        apply sq_lt_sq.mp at hk₁
        by_cases hn: 0 ≤ n
        . rw [abs_of_nonneg hn] at hk₀
          nth_rw 2 [abs_of_nonneg (by linarith)] at hk₁
          linarith
        . push_neg at hn
          have hn₁: n + 1 ≤ 0 := by linarith
          rw [abs_of_neg hn] at hk₀
          rw [abs_of_nonpos hn₁] at hk₁
          linarith
      have ha₂: ∀ k:ℤ, 31^2 < k ∧ k < 32 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 31 a
      have ha₃: ∀ k:ℤ, 30^2 < k ∧ k < 31 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 30 a
      have ha₄: ∀ k:ℤ, 29^2 < k ∧ k < 30 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 29 a
      have ha₅: ∀ k:ℤ, 28^2 < k ∧ k < 29 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 28 a
      have ha₆: ∀ k:ℤ, 27^2 < k ∧ k < 28 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 27 a
      have ha₇: ∀ k:ℤ, 26^2 < k ∧ k < 27 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 26 a
      have ha₈: ∀ k:ℤ, 25^2 < k ∧ k < 26 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 25 a
      have ha₉: ∀ k:ℤ, 24^2 < k ∧ k < 25 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 24 a
      have ha₁₀: ∀ k:ℤ, 23^2 < k ∧ k < 24 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 23 a
      interval_cases a
      all_goals try simp at h₆ hs
      all_goals try rw [h₆, ← hs] at h₈₃
      all_goals try exact (ha₂ s (by omega)) h₈₃
      all_goals try exact (ha₃ s (by omega)) h₈₃
      all_goals try exact (ha₄ s (by omega)) h₈₃
      all_goals try exact (ha₅ s (by omega)) h₈₃
      all_goals try exact (ha₆ s (by omega)) h₈₃
      all_goals try exact (ha₇ s (by omega)) h₈₃
      all_goals try exact (ha₈ s (by omega)) h₈₃
      all_goals try exact (ha₉ s (by omega)) h₈₃
      all_goals try exact (ha₁₀ s (by omega)) h₈₃
      all_goals try contrapose! h₈₃
      all_goals clear h₈₃
      . exact ha₁ s 22 (by omega)
      . exact ha₁ s 21 (by omega)
      . exact ha₁ s 20 (by omega)
      . exact ha₁ s 19 (by omega)
      . exact ha₁ s 18 (by omega)
      . exact ha₁ s 16 (by omega)
      . exact ha₁ s 12 (by omega)
      . exact ha₁ s 10 (by omega)
      . exact ha₁ s 6 (by omega)
  cases' h₉ with h₉ h₉
  . left
    constructor
    . have h₉₀: 0 ≤ (15:ℤ) := by decide
      rw [← abs_of_nonneg h₉₀]
      exact (sq_eq_sq_iff_abs_eq_abs (↑(a:ℤ) - 22) 15).mp h₉
    . rw [h₉] at h₆
      have h₉₀: ((b:ℤ) - 22) ^ 2 = 28 ^ 2 := by linarith
      have h₉₁: 0 ≤ (28:ℤ) := by decide
      rw [← abs_of_nonneg h₉₁]
      exact (sq_eq_sq_iff_abs_eq_abs _ 28).mp h₉₀
  . right
    constructor
    . have h₉₀: 0 < (28:ℤ) := by decide
      rw [← abs_of_pos h₉₀]
      exact (sq_eq_sq_iff_abs_eq_abs _ 28).mp h₉
    . rw [h₉] at h₆
      have h₉₀: ((b:ℤ) - 22) ^ 2 = 15 ^ 2 := by linarith
      have h₉₁: 0 ≤ (15:ℤ) := by decide
      rw [← abs_of_nonneg h₉₁]
      exact (sq_eq_sq_iff_abs_eq_abs _ 15).mp h₉₀



theorem imo_1977_p5
  (a b q r : ℕ)
  (hp: 0 < a ∧ 0 < b)
  (h₀ : r = (a ^ 2 + b ^ 2) % (a + b))
  (h₁ : q = (a ^ 2 + b ^ 2) / (a + b))
  (h₂ : q ^ 2 + r = 1977) :
  (a = 7 ∧ b = 50) ∨ (a = 37 ∧ b = 50) ∨ (a = 50 ∧ b = 7) ∨ (a = 50 ∧ b = 37) := by
  have hr₀: r = 1977 - q ^ 2 := by exact Nat.eq_sub_of_add_eq' h₂
  have h₅₁: 0 < a + b := by linarith
  have h₅₂: a ^ 2 + b ^ 2 = q * (a + b) + r := by
    rw [h₀, h₁,]
    exact Eq.symm (div_add_mod' (a ^ 2 + b ^ 2) (a + b))
  have h₅₃: q ≤ 44 := by
    by_contra hc₀
    push_neg at hc₀
    apply Nat.succ_le_iff.mpr at hc₀
    have hc₁: 45 ^ 2 ≤ q ^ 2 := by exact Nat.pow_le_pow_left hc₀ 2
    linarith
  have h₅₄: 43 < q := by
    have g₀: (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by exact add_sq_le
    have g₁: 2 * (a ^ 2 + b ^ 2) < 2 * (45 * (a + b)) := by
      refine (Nat.mul_lt_mul_left (by linarith)).mpr ?_
      have g₁₀: 45 = 44 + 1 := by linarith
      rw [h₅₂, g₁₀, add_mul, one_mul]
      refine add_lt_add_of_le_of_lt ?_ ?_
      . exact Nat.mul_le_mul_right (a + b) h₅₃
      . rw [h₀]
        exact Nat.mod_lt (a ^ 2 + b ^ 2) h₅₁
    have g₂: a + b < 90 := by
      apply lt_of_le_of_lt g₀ at g₁
      rw [pow_two] at g₁
      rw [← mul_assoc] at g₁
      simp at g₁
      exact (Nat.mul_lt_mul_right h₅₁).mp g₁
    have g₃: r < 90 := by
      rw [h₀]
      refine lt_trans ?_ g₂
      exact Nat.mod_lt (a ^ 2 + b ^ 2) h₅₁
    by_contra hc₀
    push_neg at hc₀
    have hc₁: q ^ 2 ≤ 43 ^ 2 := by exact Nat.pow_le_pow_left hc₀ 2
    apply Nat.succ_le_iff.mp at g₃
    linarith
  have hq₀: q = 44 := by bound
  rw [hq₀] at hr₀
  norm_num at hr₀
  rw [hq₀, hr₀] at h₅₂
  have h₆: ((a:ℤ) - 22) ^ 2 + ((b:ℤ) - 22) ^ 2 = 1009 := by
    ring_nf
    linarith
  have h₇: Prime (1009:ℤ) := by bound
  apply eq_sub_of_add_eq' at h₆
  by_cases ha₀: 53 < a
  . exfalso
    apply Nat.succ_le_iff.mpr at ha₀
    simp at ha₀
    have ha₁: 32 ^ 2 ≤ ((a:ℤ) - 22) ^ 2 := by
      refine pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hb₁: 0 ≤ ((b:ℤ) - 22) ^ 2 := by exact sq_nonneg ((b:ℤ) - 22)
    linarith
  . push_neg at ha₀
    let s : ℤ := 1009 - (↑(a:ℤ) - 22) ^ 2
    have hs: s = 1009 - (↑(a:ℤ) - 22) ^ 2 := by rfl
    have h₈₀: IsSquare (((a:ℤ) - 22) ^ 2) := by exact IsSquare.sq ((a:ℤ) - 22)
    have h₈₁: IsSquare (((b:ℤ) - 22) ^ 2) := by exact IsSquare.sq ((b:ℤ) - 22)
    have h₈₂: IsSquare s := by
      rw [hs, ← h₆]
      exact IsSquare.sq ((b:ℤ) - 22)
    have ha₁: ∀ k n:ℤ, n^2 < k ∧ k < (n + 1) ^ 2 → ¬ IsSquare k := by
      intros k n hk₀
      cases' hk₀ with hk₀ hk₁
      by_contra hc₂
      apply (isSquare_iff_exists_sq k).mp at hc₂
      let ⟨d, hd₀⟩ := hc₂
      rw [hd₀] at hk₀ hk₁
      apply sq_lt_sq.mp at hk₀
      apply sq_lt_sq.mp at hk₁
      by_cases hn: 0 ≤ n
      . rw [abs_of_nonneg hn] at hk₀
        nth_rw 2 [abs_of_nonneg (by linarith)] at hk₁
        linarith
      . push_neg at hn
        have hn₁: n + 1 ≤ 0 := by linarith
        rw [abs_of_neg hn] at hk₀
        rw [abs_of_nonpos hn₁] at hk₁
        linarith
    have ha₂: ∀ k:ℤ, 31^2 < k ∧ k < 32 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 31 a
    have ha₃: ∀ k:ℤ, 30^2 < k ∧ k < 31 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 30 a
    have ha₄: ∀ k:ℤ, 29^2 < k ∧ k < 30 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 29 a
    have ha₅: ∀ k:ℤ, 28^2 < k ∧ k < 29 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 28 a
    have ha₆: ∀ k:ℤ, 27^2 < k ∧ k < 28 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 27 a
    have ha₇: ∀ k:ℤ, 26^2 < k ∧ k < 27 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 26 a
    have ha₈: ∀ k:ℤ, 25^2 < k ∧ k < 26 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 25 a
    have ha₉: ∀ k:ℤ, 24^2 < k ∧ k < 25 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 24 a
    have ha₁₀: ∀ k:ℤ, 23^2 < k ∧ k < 24 ^ 2 → ¬ IsSquare k := by exact fun k a => ha₁ k 23 a
    have ha₁₁: abs ((↑a : ℤ) - (22 : ℤ)) ≤ 31 := by
      refine abs_le.mpr ?_
      simp
      constructor
      . bound
      . exact ha₀
    rw [← sq_abs ((↑a : ℤ) - (22 : ℤ))] at h₆ hs h₈₀
    have ha₁₂: 0 ≤ abs ((↑a : ℤ) - (22 : ℤ)) := by exact abs_nonneg ((↑a : ℤ) - (22 : ℤ))
    by_cases ha₁₃: abs ((↑a : ℤ) - (22 : ℤ)) < 15
    . exfalso
      interval_cases abs ((↑a : ℤ) - (22 : ℤ))
      . have hh₀: IsSquare (1009:ℤ) := by
          rw [zero_pow (by norm_num), sub_zero] at h₆
          rw [← h₆]
          exact h₈₁
        have hh₁: ¬ IsSquare (1009:ℤ) := by exact Prime.not_isSquare h₇
        exact hh₁ hh₀
      all_goals try exact (ha₂ s (by omega)) h₈₂
      all_goals try exact (ha₃ s (by omega)) h₈₂
      . exact (ha₄ s (by omega)) h₈₂
      . exact (ha₄ s (by omega)) h₈₂
      . exact (ha₅ s (by omega)) h₈₂
      . exact (ha₅ s (by omega)) h₈₂
    . push_neg at ha₁₃
      by_cases ha₁₄: abs ((↑a : ℤ) - (22 : ℤ)) = 15
      . apply (abs_eq (by norm_num)).mp at ha₁₄
        cases' ha₁₄ with ha₁₄ ha₁₄
        . right; left
          have hh₀: a = 37 := by bound
          rw [hh₀] at h₆
          simp at h₆
          have hh₁: (784:ℤ) = 28 ^ 2 := by bound
          rw [hh₁] at h₆
          apply pow_eq_pow_iff_cases.mp at h₆
          simp at h₆
          bound
        . left
          have hh₀: a = 7 := by bound
          rw [hh₀] at h₆
          simp at h₆
          have hh₁: (784:ℤ) = 28 ^ 2 := by bound
          rw [hh₁] at h₆
          apply pow_eq_pow_iff_cases.mp at h₆
          simp at h₆
          bound
      . by_cases ha₁₅: abs ((↑a : ℤ) - (22 : ℤ)) < 28
        . exfalso
          interval_cases abs ((↑a : ℤ) - (22 : ℤ))
          . exact (ha₅ s (by omega)) h₈₂
          . exact (ha₆ s (by omega)) h₈₂
          . exact (ha₇ s (by omega)) h₈₂
          . exact (ha₇ s (by omega)) h₈₂
          . exact (ha₈ s (by omega)) h₈₂
          . exact (ha₉ s (by omega)) h₈₂
          . exact (ha₁₀ s (by omega)) h₈₂
          . exact (ha₁ s 22 (by omega)) h₈₂
          . exact (ha₁ s 21 (by omega)) h₈₂
          . exact (ha₁ s 20 (by omega)) h₈₂
          . exact (ha₁ s 19 (by omega)) h₈₂
          . exact (ha₁ s 18 (by omega)) h₈₂
          . exact (ha₁ s 16 (by omega)) h₈₂
        . by_cases ha₁₆: abs ((↑a : ℤ) - (22 : ℤ)) = 28
          . right; right
            have ha₁₇: a = 50 := by
              apply (abs_eq (by norm_num)).mp at ha₁₆
              cases' ha₁₆ with ha₁₆ ha₁₆
              . bound
              . exfalso
                bound
            rw [ha₁₇]
            simp
            rw [ha₁₇] at h₆
            simp at h₆
            have hh₀: (225:ℤ) = 15 ^ 2 := by bound
            rw [hh₀] at h₆
            apply pow_eq_pow_iff_cases.mp at h₆
            simp at h₆
            cases' h₆ with h₆ h₆
            . right
              apply eq_add_of_sub_eq at h₆
              norm_cast at h₆
            . left
              apply eq_add_of_sub_eq at h₆
              norm_num at h₆
              norm_cast at h₆
          . exfalso
            interval_cases abs ((↑a : ℤ) - (22 : ℤ))
            . exact (ha₁ s 14 (by omega)) h₈₂
            . exact (ha₁ s 12 (by omega)) h₈₂
            . exact (ha₁ s 10 (by omega)) h₈₂
            . exact (ha₁ s 6 (by omega)) h₈₂
