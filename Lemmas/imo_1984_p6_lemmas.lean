import Mathlib
set_option linter.unusedVariables.analyzeTactics true

open Nat

lemma imo_1984_p6_1
  (a b : ℕ)
  -- (hap: 0 < a)
  -- (hbp: 0 < b)
  (h₀: b < a) :
  ((a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b) := by
  have h₁: b^2 ≤ a * b := by
    rw [pow_two]
    refine Nat.mul_le_mul_right ?_ ?_
    exact Nat.le_of_lt h₀
  have h₂: a * b ≤ a ^ 2 := by
    rw [pow_two]
    refine Nat.mul_le_mul_left ?_ ?_
    exact Nat.le_of_lt h₀
  repeat rw [pow_two]
  repeat rw [Nat.mul_sub_left_distrib]
  repeat rw [Nat.mul_sub_right_distrib a b a]
  rw [Nat.sub_right_comm]
  repeat rw [Nat.mul_sub_right_distrib a b b]
  ring_nf
  have h₃: a ^ 2 - (a * b - b ^ 2) = a ^ 2 - a * b + b ^ 2 := by
    refine tsub_tsub_assoc ?h₁ h₁
    exact h₂
  rw [h₃]
  rw [← Nat.sub_add_comm h₂]
  . rw [← Nat.sub_add_eq, ← mul_two]


lemma imo_1984_p6_2
  (a b c d k m : ℕ)
  (h₂ : a < b ∧ b < c ∧ c < d)
  (h₃ : a * d = b * c)
  (h₄ : a + d = 2 ^ k)
  (h₅ : b + c = 2 ^ m) :
  (m < k) := by
  have h₆: (c - b) ^ 2 < (d - a) ^ 2 := by
    refine Nat.pow_lt_pow_left ?_ (by norm_num)
    have h₈₀: c - a < d - a := by
      have g₀: c - a + a < d - a + a := by
        rw [Nat.sub_add_cancel ?_]
        rw [Nat.sub_add_cancel ?_]
        . exact h₂.2.2
        . linarith
        . linarith
      exact Nat.lt_of_add_lt_add_right g₀
    refine lt_trans ?_ h₈₀
    refine Nat.sub_lt_sub_left ?_ h₂.1
    exact lt_trans h₂.1 h₂.2.1
  have h₇: (b + c) ^ 2 < (a + d) ^ 2 := by
    rw [add_sq b c, add_sq a d]
    have hda: a < d := by
      refine lt_trans h₂.1 ?_
      exact lt_trans h₂.2.1 h₂.2.2
    rw [imo_1984_p6_1 d a hda] at h₆
    rw [imo_1984_p6_1 c b h₂.2.1] at h₆
    rw [mul_assoc 2 b c, ← h₃, ← mul_assoc]
    rw [mul_assoc 2 c b, mul_comm c b, ← h₃, ← mul_assoc] at h₆
    rw [add_assoc, add_comm _ (c ^ 2), ← add_assoc]
    rw [add_assoc (a ^ 2), add_comm _ (d ^ 2), ← add_assoc]
    rw [mul_assoc 2 d a, mul_comm d a, ← mul_assoc] at h₆
    rw [add_comm (d ^ 2) (a ^ 2)] at h₆
    rw [add_comm (c ^ 2) (b ^ 2)] at h₆
    have g₀: 2 * a * d ≤ 4 * a * d := by
      ring_nf
      exact Nat.mul_le_mul_left (a * d) (by norm_num)
    have g₁: 2 * a * d = 4 * a * d - 2 * a * d := by
      ring_nf
      rw [← Nat.mul_sub_left_distrib]
      norm_num
    have g₂: 2 * a * d ≤ b ^ 2 + c ^ 2 := by
      rw [mul_assoc, h₃, ← mul_assoc]
      exact two_mul_le_add_sq b c
    have g₃: 2 * a * d ≤ a ^ 2 + d ^ 2 := by
      exact two_mul_le_add_sq a d
    rw [g₁, ← Nat.add_sub_assoc (g₀) (b ^ 2 + c ^ 2)]
    rw [← Nat.add_sub_assoc (g₀) (a ^ 2 + d ^ 2)]
    rw [Nat.sub_add_comm g₂, Nat.sub_add_comm g₃]
    exact (Nat.add_lt_add_iff_right).mpr h₆
  have h2 : 1 < 2 := by norm_num
  refine (Nat.pow_lt_pow_iff_right h2).mp ?_
  rw [← h₄, ← h₅]
  exact (Nat.pow_lt_pow_iff_left (by norm_num) ).mp h₇


lemma imo_1984_p6_3
  (a b c d : ℕ)
  (h₀ : a < b ∧ b < c ∧ c < d) :
  (c - b) ^ 2 < (d - a) ^ 2 := by
  refine Nat.pow_lt_pow_left ?_ (by norm_num)
  have h₁: c - a < d - a := by
    have g₀: c - a + a < d - a + a := by
      rw [Nat.sub_add_cancel ?_]
      rw [Nat.sub_add_cancel ?_]
      . exact h₀.2.2
      . linarith
      . linarith
    exact Nat.lt_of_add_lt_add_right g₀
  refine lt_trans ?_ h₁
  refine Nat.sub_lt_sub_left ?_ h₀.1
  exact lt_trans h₀.1 h₀.2.1


lemma imo_1984_p6_4
  (a b c d : ℕ)
  (h₀ : a < b ∧ b < c ∧ c < d)
  (h₁ : a * d = b * c)
  (h₂ : (c - b) ^ 2 < (d - a) ^ 2) :
  (b + c) ^ 2 < (a + d) ^ 2 := by
  rw [add_sq b c, add_sq a d]
  have hda: a < d := by
    refine lt_trans h₀.1 ?_
    exact lt_trans h₀.2.1 h₀.2.2
  rw [imo_1984_p6_1 d a hda] at h₂
  rw [imo_1984_p6_1 c b h₀.2.1] at h₂
  rw [mul_assoc 2 b c, ← h₁, ← mul_assoc]
  rw [mul_assoc 2 c b, mul_comm c b, ← h₁, ← mul_assoc] at h₂
  rw [add_assoc, add_comm _ (c ^ 2), ← add_assoc]
  rw [add_assoc (a ^ 2), add_comm _ (d ^ 2), ← add_assoc]
  rw [mul_assoc 2 d a, mul_comm d a, ← mul_assoc] at h₂
  rw [add_comm (d ^ 2) (a ^ 2)] at h₂
  rw [add_comm (c ^ 2) (b ^ 2)] at h₂
  have g₀: 2 * a * d ≤ 4 * a * d := by
    ring_nf
    exact Nat.mul_le_mul_left (a * d) (by norm_num)
  have g₁: 2 * a * d = 4 * a * d - 2 * a * d := by
    ring_nf
    rw [← Nat.mul_sub_left_distrib]
    norm_num
  have g₂: 2 * a * d ≤ b ^ 2 + c ^ 2 := by
    rw [mul_assoc, h₁, ← mul_assoc]
    exact two_mul_le_add_sq b c
  have g₃: 2 * a * d ≤ a ^ 2 + d ^ 2 := by
    exact two_mul_le_add_sq a d
  rw [g₁, ← Nat.add_sub_assoc (g₀) (b ^ 2 + c ^ 2)]
  rw [← Nat.add_sub_assoc (g₀) (a ^ 2 + d ^ 2)]
  rw [Nat.sub_add_comm g₂, Nat.sub_add_comm g₃]
  exact (Nat.add_lt_add_iff_right).mpr h₂


lemma imo_1984_p6_5
  (a b c d : ℕ)
  -- (h₀ : a < b ∧ b < c ∧ c < d)
  (h₁ : a * d = b * c)
  (h₂ : b ^ 2 + c ^ 2 - 2 * a * d < a ^ 2 + d ^ 2 - 2 * a * d) :
  b ^ 2 + c ^ 2 + 2 * a * d < a ^ 2 + d ^ 2 + 2 * a * d := by
  have g₀: 2 * a * d ≤ 4 * a * d := by
    ring_nf
    exact Nat.mul_le_mul_left (a * d) (by norm_num)
  have g₁: 2 * a * d = 4 * a * d - 2 * a * d := by
    ring_nf
    rw [← Nat.mul_sub_left_distrib]
    norm_num
  have g₂: 2 * a * d ≤ b ^ 2 + c ^ 2 := by
    rw [mul_assoc, h₁, ← mul_assoc]
    exact two_mul_le_add_sq b c
  have g₃: 2 * a * d ≤ a ^ 2 + d ^ 2 := by
    exact two_mul_le_add_sq a d
  rw [g₁, ← Nat.add_sub_assoc (g₀) (b ^ 2 + c ^ 2)]
  rw [← Nat.add_sub_assoc (g₀) (a ^ 2 + d ^ 2)]
  rw [Nat.sub_add_comm g₂, Nat.sub_add_comm g₃]
  exact (Nat.add_lt_add_iff_right).mpr h₂


lemma imo_1984_p6_6
  (a b c d : ℕ)
  (h₁ : a * d = b * c) :
  -- (h₂ : b ^ 2 + c ^ 2 - 2 * a * d < a ^ 2 + d ^ 2 - 2 * a * d)
  -- (g₀ : 2 * a * d ≤ 4 * a * d)
  -- (g₁ : 2 * a * d = 4 * a * d - 2 * a * d) :
  (2 * a * d ≤ b ^ 2 + c ^ 2) := by
  rw [mul_assoc, h₁, ← mul_assoc]
  exact two_mul_le_add_sq b c


lemma imo_1984_p6_7
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : m < k)
  (h₂ : a < b ∧ b < c ∧ c < d)
  (h₃ : a * d = b * c)
  (h₄ : a + d = 2 ^ k)
  (h₅ : b + c = 2 ^ m)
  (hkm : k ≤ m) :
  a = 99 := by
  linarith [h₁, hkm]



lemma imo_1984_p6_8
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  -- (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h₂ : a < b ∧ b < c ∧ c < d)
  (h₃ : a * d = b * c)
  (h₄ : a + d = 2 ^ k)
  (h₅ : b + c = 2 ^ m) :
  -- (hkm : m < k) :
  b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a) := by
  have h₆₀: c = 2 ^ m - b := by exact (tsub_eq_of_eq_add_rev (id h₅.symm)).symm
  have h₆₁: d = 2 ^ k - a := by exact (tsub_eq_of_eq_add_rev (id h₄.symm)).symm
  rw [h₆₀, h₆₁] at h₃
  repeat rw [Nat.mul_sub_left_distrib, ← pow_two] at h₃
  have h₆₂: b * 2 ^ m - a * 2 ^ k =  b ^ 2 - a ^ 2 := by
    symm at h₃
    refine Nat.sub_eq_of_eq_add ?_
    rw [add_comm, ← Nat.add_sub_assoc]
    . rw [Nat.sub_add_comm]
      . refine Nat.eq_add_of_sub_eq ?_ h₃
        rw [pow_two]
        refine le_of_lt ?_
        refine mul_lt_mul' (by linarith) ?_ (le_of_lt h₀.2.1) h₀.2.1
        linarith
      . rw [pow_two]
        refine le_of_lt ?_
        refine mul_lt_mul' (by linarith) ?_ (le_of_lt h₀.1) h₀.1
        linarith
    . refine le_of_lt ?_
      rw [pow_two, pow_two]
      exact mul_lt_mul h₂.1 (le_of_lt h₂.1) h₀.1 (le_of_lt h₀.2.1)
  rw [Nat.sq_sub_sq b a] at h₆₂
  rw [mul_comm (b - a) _]
  exact h₆₂


lemma imo_1984_p6_8_1
(a b c d k m : ℕ)
-- (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
-- (h₂ : a < b ∧ b < c ∧ c < d)
(h₃ : a * d = b * c)
(h₄ : a + d = 2 ^ k)
(h₅ : b + c = 2 ^ m) :
-- (h₆₀ : c = 2 ^ m - b)
-- (h₆₁ : d = 2 ^ k - a) :
a * (2 ^ k - a) = b * (2 ^ m - b) := by
have h₆₀: c = 2 ^ m - b := by exact (tsub_eq_of_eq_add_rev (id h₅.symm)).symm
have h₆₁: d = 2 ^ k - a := by exact (tsub_eq_of_eq_add_rev (id h₄.symm)).symm
rw [h₆₀, h₆₁] at h₃
exact h₃



lemma imo_1984_p6_8_2
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₂ : a < b)
  (h₃ : a * 2 ^ k - a ^ 2 = b * 2 ^ m - b ^ 2)
  (h₄ : a + d = 2 ^ k)
  (h₅ : b + c = 2 ^ m) :
  -- (h₆₀ : c = 2 ^ m - b)
  -- (h₆₁ : d = 2 ^ k - a) :
  b * 2 ^ m - a * 2 ^ k = b ^ 2 - a ^ 2 := by
  symm at h₃
  refine Nat.sub_eq_of_eq_add ?_
  rw [add_comm, ← Nat.add_sub_assoc]
  . rw [Nat.sub_add_comm]
    . refine Nat.eq_add_of_sub_eq ?_ h₃
      rw [pow_two]
      refine le_of_lt ?_
      refine mul_lt_mul' (by linarith) ?_ (le_of_lt h₀.2.1) h₀.2.1
      linarith
    . rw [pow_two]
      refine le_of_lt ?_
      refine mul_lt_mul' (by linarith) ?_ (le_of_lt h₀.1) h₀.1
      linarith
  . refine le_of_lt ?_
    rw [pow_two, pow_two]
    exact mul_lt_mul h₂ (le_of_lt h₂) h₀.1 (le_of_lt h₀.2.1)


lemma imo_1984_p6_8_3
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  -- (h₂ : a < b)
  (h₃ : b * 2 ^ m - b ^ 2 = a * 2 ^ k - a ^ 2)
  -- (h₄ : a + d = 2 ^ k)
  (h₅ : b + c = 2 ^ m) :
  -- (h₆₀ : c = 2 ^ m - b)
  -- (h₆₁ : d = 2 ^ k - a) :
  b * 2 ^ m = a * 2 ^ k - a ^ 2 + b ^ 2 := by
  refine Nat.eq_add_of_sub_eq ?_ h₃
  rw [pow_two]
  refine le_of_lt ?_
  refine mul_lt_mul' (by linarith) ?_ (le_of_lt h₀.2.1) h₀.2.1
  linarith


lemma imo_1984_p6_8_4
  (a b c d k : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  -- (h₂ : a < b)
  -- (h₃ : b * 2 ^ m - b ^ 2 = a * 2 ^ k - a ^ 2)
  (h₄ : a + d = 2 ^ k) :
  -- (h₅ : b + c = 2 ^ m) :
  a ^ 2 ≤ a * 2 ^ k := by
  rw [pow_two]
  refine le_of_lt ?_
  refine mul_lt_mul' (by linarith) ?_ (le_of_lt h₀.1) h₀.1
  linarith


lemma imo_1984_p6_8_5
  (a b : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₂ : a < b) :
  -- h₃ : b * 2 ^ m - b ^ 2 = a * 2 ^ k - a ^ 2
  -- h₄ : a + d = 2 ^ k
  -- h₅ : b + c = 2 ^ m
  -- h₆₀ : c = 2 ^ m - b
  -- h₆₁ : d = 2 ^ k - a
  a ^ 2 < b ^ 2 := by
  exact Nat.pow_lt_pow_left h₂ (by norm_num)


lemma imo_1984_p6_8_6
  (a b k m : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  -- (h₂ : a < b ∧ b < c ∧ c < d)
  -- (h₃ : a * 2 ^ k - a ^ 2 = b * 2 ^ m - b ^ 2)
  -- (h₄ : a + d = 2 ^ k)
  -- (h₅ : b + c = 2 ^ m)
  -- (h₆₀ : c = 2 ^ m - b)
  -- (h₆₁ : d = 2 ^ k - a)
  (h₆₂ : b * 2 ^ m - a * 2 ^ k = b ^ 2 - a ^ 2) :
  b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a) := by
  rw [Nat.sq_sub_sq b a] at h₆₂
  rw [mul_comm (b - a) _]
  exact h₆₂




lemma imo_1984_p6_9
  (a b k m : ℕ)
  (hkm : m < k)
  (h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a)) :
  2 ^ m ∣ (b - a) * (b + a) := by
  have h₇₀: k = (k - m) + m := by exact (Nat.sub_add_cancel (le_of_lt hkm)).symm
  rw [h₇₀, pow_add] at h₆
  have h₇₁: (b - a * 2 ^ (k - m)) * (2 ^ m) = (b - a) * (b + a) := by
    rw [Nat.mul_sub_right_distrib]
    rw [mul_assoc a _ _]
    exact h₆
  exact Dvd.intro_left (b - a * 2 ^ (k - m)) h₇₁




lemma imo_1984_p6_10
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h₂ : a < b ∧ b < c ∧ c < d)
  -- (h₃ : a * d = b * c)
  -- (h₄ : a + d = 2 ^ k)
  (h₅ : b + c = 2 ^ m)
  (hkm : m < k)
  (h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a))
  (h₇ : 2 ^ m ∣ (b - a) * (b + a)) :
  b + a = 2 ^ (m - 1) := by
  have h₇₁: ∃ y z, y ∣ b - a ∧ z ∣ b + a ∧ y * z = 2 ^ m := by
    exact Nat.dvd_mul.mp h₇
  let ⟨p, q, hpd⟩ := h₇₁
  cases' hpd with hpd hqd
  cases' hqd with hqd hpq
  have hm1: 1 ≤ m := by
    by_contra! hc
    interval_cases m
    linarith
  have h₈₀: b - a < 2 ^ (m - 1) := by
    have g₀: b < (b + c) / 2 := by
      refine (Nat.lt_div_iff_mul_lt' ?_ b).mpr ?_
      . refine even_iff_two_dvd.mp ?_
        exact Odd.add_odd h₁.2.1 h₁.2.2.1
      . linarith
    have g₁: (b + c) / 2 = 2 ^ (m-1) := by
      rw [h₅]
      rw [← Nat.pow_sub_mul_pow 2 hm1]
      simp
    rw [← g₁]
    refine lt_trans ?_ g₀
    exact Nat.sub_lt h₀.2.1 h₀.1
  have hp: p = 2 := by
    have hp₀: 2 * b < 2 ^ m := by
      rw [← h₅, two_mul]
      exact Nat.add_lt_add_left h₂.2.1 b
    have hp₁: b + a < 2 ^ (m) := by
      have g₀: b + a < b + b := by
        exact Nat.add_lt_add_left h₂.1 b
      refine Nat.lt_trans g₀ ?_
      rw [← two_mul]
      exact hp₀
    have hp₂: q < 2 ^ m := by
      refine Nat.lt_of_le_of_lt (Nat.le_of_dvd ?_ hqd) hp₁
      exact Nat.add_pos_right b h₀.1
    have hp₃: 1 < p := by
      rw [← hpq] at hp₂
      exact one_lt_of_lt_mul_left hp₂
    have h2prime: Nat.Prime 2 := by exact prime_two
    have hp₅: ∀ i j:ℕ , 2 ^ i ∣ (b - a) ∧ 2 ^ j ∣ (b + a) → (i < 2 ∨ j < 2) := by
      by_contra! hc
      let ⟨i, j, hi⟩ := hc
      have hti: 2 ^ 2 ∣ 2 ^ i := by exact Nat.pow_dvd_pow 2 hi.2.1
      have htj: 2 ^ 2 ∣ 2 ^ j := by exact Nat.pow_dvd_pow 2 hi.2.2
      norm_num at hti htj
      have hi₄: 4 ∣ b - a := by exact Nat.dvd_trans hti hi.1.1
      have hi₅: 4 ∣ b + a := by exact Nat.dvd_trans htj hi.1.2
      have hi₆: 4 ∣ (b - a) + (b + a) := by exact Nat.dvd_add hi₄ hi₅
      have hi₇: 2 ∣ b := by
        have g₀: 0 < 2 := by norm_num
        refine Nat.dvd_of_mul_dvd_mul_left g₀ ?_
        rw [← Nat.add_sub_cancel (2 * b) a, Nat.two_mul b]
        rw [add_assoc, Nat.sub_add_comm (le_of_lt h₂.1)]
        exact hi₆
      have hi₈: Even b := by
        exact even_iff_two_dvd.mpr hi₇
      apply Nat.not_odd_iff_even.mpr hi₈
      exact h₁.2.1
    have hp₆: ∀ i j:ℕ , i + j = m ∧ 2 ^ i ∣ (b - a) ∧ 2 ^ j ∣ (b + a) → (¬ j < 2) := by
      by_contra! hc
      let ⟨i, j, hi⟩ := hc
      have hi₀: m - 1 ≤ i := by
        rw [← hi.1.1]
        simp
        exact Nat.le_pred_of_lt hi.2
      have hi₁: 2 ^ (m - 1) ≤ 2 ^ i := by exact Nat.pow_le_pow_right (by norm_num) hi₀
      have hi₂: 2 ^ i < 2 ^ (m - 1) := by
        refine lt_of_le_of_lt ?_ h₈₀
        refine Nat.le_of_dvd ?_ hi.1.2.1
        exact Nat.sub_pos_of_lt h₂.1
      -- j must be ≤ 1 which gives i ≥ m - 1
      -- however from h₈₀ we have i < m - 1 leading to a contradiction
      linarith [hi₁, hi₂]
    have hi₀: ∃ i ≤ m, p = 2 ^ i := by
      have g₀: p ∣ 2 ^ m := by
        rw [← hpq]
        exact Nat.dvd_mul_right p q
      exact (Nat.dvd_prime_pow h2prime).mp g₀
    let ⟨i, hp⟩ := hi₀
    cases' hp with him hp
    let j:ℕ := m - i
    have hj₀: j = m - i := by linarith
    have hj₁: i + j = m := by
      rw [add_comm, ← Nat.sub_add_cancel him]
    have hq: q = 2 ^ j := by
      rw [hp] at hpq
      rw [hj₀, ← Nat.pow_div him (by norm_num)]
      refine Nat.eq_div_of_mul_eq_right ?_ hpq
      refine Nat.ne_of_gt ?_
      rw [← hp]
      linarith [hp₃]
    rw [hp] at hpd
    rw [hq] at hqd
    have hj₃: ¬ j < 2 := by
      exact hp₆ i j {left:= hj₁ , right:= { left := hpd , right:= hqd} }
    have hi₂: i < 2 := by
      have g₀: i < 2 ∨ j < 2 := by
        exact hp₅ i j { left := hpd , right:= hqd }
      omega
    have hi₃: 0 < i := by
      rw [hp] at hp₃
      refine Nat.zero_lt_of_ne_zero ?_
      exact (Nat.one_lt_two_pow_iff).mp hp₃
    have hi₄: i = 1 := by
      interval_cases i
      rfl
    rw [hi₄] at hp
    exact hp
  have hq: q = 2 ^ (m - 1) := by
    rw [hp, ← Nat.pow_sub_mul_pow 2 hm1, pow_one, mul_comm] at hpq
    exact Nat.mul_right_cancel (by norm_num) hpq
  rw [hq] at hqd
  have h₈₂: ∃ c, (b + a) = c * 2 ^ (m - 1) := by
    exact exists_eq_mul_left_of_dvd hqd
  let ⟨f, hf⟩ := h₈₂
  have hfeq1: f = 1 := by
    have hf₀: f * 2 ^ (m - 1) < 2 * 2 ^ (m - 1) := by
      rw [← hf, ← Nat.pow_succ', ← Nat.succ_sub hm1]
      rw [Nat.succ_sub_one, ← h₅]
      refine Nat.add_lt_add_left ?_ b
      exact lt_trans h₂.1 h₂.2.1
    have hf₁: f < 2 := by
      exact Nat.lt_of_mul_lt_mul_right hf₀
    interval_cases f
    . simp at hf
      exfalso
      linarith [hf]
    . linarith
  rw [hfeq1, one_mul] at hf
  exact hf


lemma imo_1984_p6_10_1
  (a b c d m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h₂ : a < b ∧ b < c ∧ c < d)
  (h₅ : b + c = 2 ^ m)
  -- hkm : m < k
  -- h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a)
  -- h₇ : 2 ^ m ∣ (b - a) * (b + a)
  -- h₇₁ : ∃ y z, y ∣ b - a ∧ z ∣ b + a ∧ y * z = 2 ^ m
  -- p q : ℕ
  -- hpd : p ∣ b - a
  -- hqd : q ∣ b + a
  -- hpq : p * q = 2 ^ m
  (hm1 : 1 ≤ m) :
  b - a < 2 ^ (m - 1) := by
  have g₀: b < (b + c) / 2 := by
    refine (Nat.lt_div_iff_mul_lt' ?_ b).mpr ?_
    . refine even_iff_two_dvd.mp ?_
      exact Odd.add_odd h₁.2.1 h₁.2.2.1
    . linarith
  have g₁: (b + c) / 2 = 2 ^ (m-1) := by
    rw [h₅]
    rw [← Nat.pow_sub_mul_pow 2 hm1]
    simp
  rw [← g₁]
  refine lt_trans ?_ g₀
  exact Nat.sub_lt h₀.2.1 h₀.1


lemma imo_1984_p6_10_2
  (b c: ℕ)
  (h₁ : Odd b ∧ Odd c)
  (h₂ : b < c) :
  b < (b + c) / 2 := by
  refine (Nat.lt_div_iff_mul_lt' ?_ b).mpr ?_
  . refine even_iff_two_dvd.mp ?_
    exact Odd.add_odd h₁.1 h₁.2
  . linarith

lemma imo_1984_p6_10_3
  (b c m : ℕ)
  (h₅ : b + c = 2 ^ m)
  (hm1 : 1 ≤ m) :
  (b + c) / 2 = 2 ^ (m - 1) := by
  rw [h₅]
  rw [← Nat.pow_sub_mul_pow 2 hm1]
  simp


lemma imo_1984_p6_10_4
  (a b c m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (g₀ : b < (b + c) / 2)
  (g₁ : (b + c) / 2 = 2 ^ (m - 1)) :
  b - a < 2 ^ (m - 1) := by
  rw [← g₁]
  refine lt_trans ?_ g₀
  exact Nat.sub_lt h₀.2.1 h₀.1

lemma imo_1984_p6_10_5
  (a b c m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₅ : b + c = 2 ^ m) :
  1 ≤ m := by
  by_contra! hc
  interval_cases m
  linarith


lemma imo_1984_p6_10_6
  (a b c m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : Odd a ∧ Odd b ∧ Odd c)
  (h₂ : a < b ∧ b < c)
  (h₅ : b + c = 2 ^ m)
  (p q : ℕ)
  (hpd : p ∣ b - a)
  (hqd : q ∣ b + a)
  (hpq : p * q = 2 ^ m)
  (h₈₀ : b - a < 2 ^ (m - 1)) :
  p = 2 := by
  have hp₀: 2 * b < 2 ^ m := by
    rw [← h₅, two_mul]
    exact Nat.add_lt_add_left h₂.2 b
  have hp₁: b + a < 2 ^ (m) := by
    have g₀: b + a < b + b := by
      exact Nat.add_lt_add_left h₂.1 b
    refine Nat.lt_trans g₀ ?_
    rw [← two_mul]
    exact hp₀
  have hp₂: q < 2 ^ m := by
    refine Nat.lt_of_le_of_lt (Nat.le_of_dvd ?_ hqd) hp₁
    exact Nat.add_pos_right b h₀.1
  have hp₃: 1 < p := by
    rw [← hpq] at hp₂
    exact one_lt_of_lt_mul_left hp₂
  have h2prime: Nat.Prime 2 := by exact prime_two
  have hp₅: ∀ i j:ℕ , 2 ^ i ∣ (b - a) ∧ 2 ^ j ∣ (b + a) → (i < 2 ∨ j < 2) := by
    by_contra! hc
    let ⟨i, j, hi⟩ := hc
    have hti: 2 ^ 2 ∣ 2 ^ i := by exact Nat.pow_dvd_pow 2 hi.2.1
    have htj: 2 ^ 2 ∣ 2 ^ j := by exact Nat.pow_dvd_pow 2 hi.2.2
    norm_num at hti htj
    have hi₄: 4 ∣ b - a := by exact Nat.dvd_trans hti hi.1.1
    have hi₅: 4 ∣ b + a := by exact Nat.dvd_trans htj hi.1.2
    have hi₆: 4 ∣ (b - a) + (b + a) := by exact Nat.dvd_add hi₄ hi₅
    have hi₇: 2 ∣ b := by
      have g₀: 0 < 2 := by norm_num
      refine Nat.dvd_of_mul_dvd_mul_left g₀ ?_
      rw [← Nat.add_sub_cancel (2 * b) a, Nat.two_mul b]
      rw [add_assoc, Nat.sub_add_comm (le_of_lt h₂.1)]
      exact hi₆
    have hi₈: Even b := by
      exact even_iff_two_dvd.mpr hi₇
    apply Nat.not_odd_iff_even.mpr hi₈
    exact h₁.2.1
  have hp₆: ∀ i j:ℕ , i + j = m ∧ 2 ^ i ∣ (b - a) ∧ 2 ^ j ∣ (b + a) → (¬ j < 2) := by
    by_contra! hc
    let ⟨i, j, hi⟩ := hc
    have hi₀: m - 1 ≤ i := by
      rw [← hi.1.1]
      simp
      exact Nat.le_pred_of_lt hi.2
    have hi₁: 2 ^ (m - 1) ≤ 2 ^ i := by exact Nat.pow_le_pow_right (by norm_num) hi₀
    have hi₂: 2 ^ i < 2 ^ (m - 1) := by
      refine lt_of_le_of_lt ?_ h₈₀
      refine Nat.le_of_dvd ?_ hi.1.2.1
      exact Nat.sub_pos_of_lt h₂.1
    -- j must be ≤ 1 which gives i ≥ m - 1
    -- however from h₈₀ we have i < m - 1 leading to a contradiction
    linarith [hi₁, hi₂]
  have hi₀: ∃ i ≤ m, p = 2 ^ i := by
    have g₀: p ∣ 2 ^ m := by
      rw [← hpq]
      exact Nat.dvd_mul_right p q
    exact (Nat.dvd_prime_pow h2prime).mp g₀
  let ⟨i, hp⟩ := hi₀
  cases' hp with him hp
  let j:ℕ := m - i
  have hj₀: j = m - i := by linarith
  have hj₁: i + j = m := by
    rw [add_comm, ← Nat.sub_add_cancel him]
  have hq: q = 2 ^ j := by
    rw [hp] at hpq
    rw [hj₀, ← Nat.pow_div him (by norm_num)]
    refine Nat.eq_div_of_mul_eq_right ?_ hpq
    refine Nat.ne_of_gt ?_
    rw [← hp]
    linarith [hp₃]
  rw [hp] at hpd
  rw [hq] at hqd
  have hj₃: ¬ j < 2 := by
    exact hp₆ i j {left:= hj₁ , right:= { left := hpd , right:= hqd} }
  have hi₂: i < 2 := by
    have g₀: i < 2 ∨ j < 2 := by
      exact hp₅ i j { left := hpd , right:= hqd }
    omega
  have hi₃: 0 < i := by
    rw [hp] at hp₃
    refine Nat.zero_lt_of_ne_zero ?_
    exact (Nat.one_lt_two_pow_iff).mp hp₃
  have hi₄: i = 1 := by
    interval_cases i
    rfl
  rw [hi₄] at hp
  exact hp

lemma imo_1984_p6_10_6_1
  (a b c m : ℕ)
  (h₂ : a < b ∧ b < c)
  (h₅ : b + c = 2 ^ m) :
  2 * b < 2 ^ m := by
  rw [← h₅, two_mul]
  exact Nat.add_lt_add_left h₂.2 b


lemma imo_1984_p6_10_6_2
  (a b c m : ℕ)
  -- h₀ : 0 < a ∧ 0 < b ∧ 0 < c
  -- h₁ : Odd a ∧ Odd b ∧ Odd c
  (h₂ : a < b ∧ b < c)
  -- h₅ : b + c = 2 ^ m
  -- p q : ℕ
  -- hpd : p ∣ b - a
  -- hqd : q ∣ b + a
  -- hpq : p * q = 2 ^ m
  -- h₈₀ : b - a < 2 ^ (m - 1)
  (hp₀ : 2 * b < 2 ^ m) :
  b + a < 2 ^ m := by
  have g₀: b + a < b + b := by
    exact Nat.add_lt_add_left h₂.1 b
  refine Nat.lt_trans g₀ ?_
  rw [← two_mul]
  exact hp₀

lemma imo_1984_p6_10_6_3
  -- (a b c m : ℕ)
  -- h₀ : 0 < a ∧ 0 < b ∧ 0 < c
  -- h₁ : Odd a ∧ Odd b ∧ Odd c
  -- h₂ : a < b ∧ b < c
  -- h₅ : b + c = 2 ^ m
  (m p q : ℕ)
  -- hpd : p ∣ b - a
  -- hqd : q ∣ b + a
  (hpq : p * q = 2 ^ m)
  -- h₈₀ : b - a < 2 ^ (m - 1)
  -- hp₀ : 2 * b < 2 ^ m
  -- hp₁ : b + a < 2 ^ m
  (hp₂ : q < 2 ^ m) :
  1 < p := by
  rw [← hpq] at hp₂
  exact one_lt_of_lt_mul_left hp₂


lemma imo_1984_p6_10_6_4
  (a b: ℕ)
  -- h₀ : 0 < a ∧ 0 < b ∧ 0 < c
  (h₁ : Odd a ∧ Odd b)
  (h₂ : a < b) :
  -- h₅ : b + c = 2 ^ m
  -- p q : ℕ
  -- hpd : p ∣ b - a
  -- hqd : q ∣ b + a
  -- hpq : p * q = 2 ^ m
  -- h₈₀ : b - a < 2 ^ (m - 1)
  -- hp₀ : 2 * b < 2 ^ m
  -- hp₁ : b + a < 2 ^ m
  -- hp₂ : q < 2 ^ m
  -- hp₃ : 1 < p
  -- h2prime : Nat.Prime 2
  ∀ (i j : ℕ), 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a → i < 2 ∨ j < 2 := by
  by_contra! hc
  let ⟨i, j, hi⟩ := hc
  have hti: 2 ^ 2 ∣ 2 ^ i := by exact Nat.pow_dvd_pow 2 hi.2.1
  have htj: 2 ^ 2 ∣ 2 ^ j := by exact Nat.pow_dvd_pow 2 hi.2.2
  norm_num at hti htj
  have hi₄: 4 ∣ b - a := by exact Nat.dvd_trans hti hi.1.1
  have hi₅: 4 ∣ b + a := by exact Nat.dvd_trans htj hi.1.2
  have hi₆: 4 ∣ (b - a) + (b + a) := by exact Nat.dvd_add hi₄ hi₅
  have hi₇: 2 ∣ b := by
    have g₀: 0 < 2 := by norm_num
    refine Nat.dvd_of_mul_dvd_mul_left g₀ ?_
    rw [← Nat.add_sub_cancel (2 * b) a, Nat.two_mul b]
    rw [add_assoc, Nat.sub_add_comm (le_of_lt h₂)]
    exact hi₆
  have hi₈: Even b := by
    exact even_iff_two_dvd.mpr hi₇
  apply Nat.not_odd_iff_even.mpr hi₈
  exact h₁.2

lemma imo_1984_p6_10_6_5
  (a b c : ℕ)
  (h₁ : Odd a ∧ Odd b ∧ Odd c)
  (h₂ : a < b ∧ b < c)
  -- (hc : ∃ i j, (2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ 2 ≤ i ∧ 2 ≤ j)
  (i j : ℕ)
  (hi : (2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ 2 ≤ i ∧ 2 ≤ j)
  (hti : 4 ∣ 2 ^ i)
  (htj : 4 ∣ 2 ^ j) :
  False := by
  have hi₄: 4 ∣ b - a := by exact Nat.dvd_trans hti hi.1.1
  have hi₅: 4 ∣ b + a := by exact Nat.dvd_trans htj hi.1.2
  have hi₆: 4 ∣ (b - a) + (b + a) := by exact Nat.dvd_add hi₄ hi₅
  have hi₇: 2 ∣ b := by
    have g₀: 0 < 2 := by norm_num
    refine Nat.dvd_of_mul_dvd_mul_left g₀ ?_
    rw [← Nat.add_sub_cancel (2 * b) a, Nat.two_mul b]
    rw [add_assoc, Nat.sub_add_comm (le_of_lt h₂.1)]
    exact hi₆
  have hi₈: Even b := by
    exact even_iff_two_dvd.mpr hi₇
  apply Nat.not_odd_iff_even.mpr hi₈
  exact h₁.2.1

lemma imo_1984_p6_10_6_6
  (a b: ℕ)
  -- (h₁ : Odd a ∧ Odd b ∧ Odd c)
  -- (h₂ : a < b ∧ b < c)
  -- hc : ∃ i j, (2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ 2 ≤ i ∧ 2 ≤ j
  (i j : ℕ)
  (hi : (2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ 2 ≤ i ∧ 2 ≤ j)
  (hti : 4 ∣ 2 ^ i)
  (htj : 4 ∣ 2 ^ j) :
  4 ∣ b - a + (b + a) := by
  have hi₄: 4 ∣ b - a := by exact Nat.dvd_trans hti hi.1.1
  have hi₅: 4 ∣ b + a := by exact Nat.dvd_trans htj hi.1.2
  exact Nat.dvd_add hi₄ hi₅


lemma imo_1984_p6_10_6_7
  (a b c : ℕ)
  -- (h₁ : Odd a ∧ Odd b ∧ Odd c)
  (h₂ : a < b ∧ b < c)
  -- hc : ∃ i j, (2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ 2 ≤ i ∧ 2 ≤ j
  (i j : ℕ)
  (hi : (2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ 2 ≤ i ∧ 2 ≤ j)
  (hti : 4 ∣ 2 ^ i)
  (htj : 4 ∣ 2 ^ j) :
  2 ∣ b := by
  have hi₄: 4 ∣ b - a := by exact Nat.dvd_trans hti hi.1.1
  have hi₅: 4 ∣ b + a := by exact Nat.dvd_trans htj hi.1.2
  have hi₆: 4 ∣ (b - a) + (b + a) := by exact Nat.dvd_add hi₄ hi₅
  have g₀: 0 < 2 := by norm_num
  refine Nat.dvd_of_mul_dvd_mul_left g₀ ?_
  rw [← Nat.add_sub_cancel (2 * b) a, Nat.two_mul b]
  rw [add_assoc, Nat.sub_add_comm (le_of_lt h₂.1)]
  exact hi₆


lemma imo_1984_p6_10_6_8
  (a b c : ℕ)
  -- (h₁ : Odd a ∧ Odd b ∧ Odd c)
  (h₂ : a < b ∧ b < c)
  -- hc : ∃ i j, (2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ 2 ≤ i ∧ 2 ≤ j
  -- i j : ℕ
  -- hi : (2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ 2 ≤ i ∧ 2 ≤ j
  -- hti : 4 ∣ 2 ^ i
  -- htj : 4 ∣ 2 ^ j
  -- (hi₄ : 4 ∣ b - a)
  -- (hi₅ : 4 ∣ b + a)
  (hi₆ : 4 ∣ b - a + (b + a)) :
  2 ∣ b := by
  have g₀: 0 < 2 := by norm_num
  refine Nat.dvd_of_mul_dvd_mul_left g₀ ?_
  rw [← Nat.add_sub_cancel (2 * b) a, Nat.two_mul b]
  rw [add_assoc, Nat.sub_add_comm (le_of_lt h₂.1)]
  exact hi₆

lemma imo_1984_p6_10_6_9
  (a b c : ℕ)
  -- (h₁ : Odd a ∧ Odd b ∧ Odd c)
  (h₂ : a < b ∧ b < c)
  -- hc : ∃ i j, (2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ 2 ≤ i ∧ 2 ≤ j
  -- i j : ℕ
  -- hi : (2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ 2 ≤ i ∧ 2 ≤ j
  -- hti : 4 ∣ 2 ^ i
  -- htj : 4 ∣ 2 ^ j
  -- (hi₄ : 4 ∣ b - a)
  -- (hi₅ : 4 ∣ b + a)
  (hi₆ : 4 ∣ b - a + (b + a)) :
  Even b := by
  refine even_iff_two_dvd.mpr ?_
  have g₀: 0 < 2 := by norm_num
  refine Nat.dvd_of_mul_dvd_mul_left g₀ ?_
  rw [← Nat.add_sub_cancel (2 * b) a, Nat.two_mul b]
  rw [add_assoc, Nat.sub_add_comm (le_of_lt h₂.1)]
  exact hi₆

lemma imo_1984_p6_10_6_10
  (a b m : ℕ)
  -- h₀ : 0 < a ∧ 0 < b ∧ 0 < c
  -- (h₁ : Odd a ∧ Odd b)
  (h₂ : a < b)
  -- (a b c m : ℕ)
  -- h₀ : 0 < a ∧ 0 < b ∧ 0 < c
  -- h₁ : Odd a ∧ Odd b ∧ Odd c
  -- h₂ : a < b ∧ b < c
  -- h₅ : b + c = 2 ^ m
  -- p q : ℕ
  -- hpd : p ∣ b - a
  -- hqd : q ∣ b + a
  -- hpq : p * q = 2 ^ m
  (h₈₀ : b - a < 2 ^ (m - 1)) :
  -- hp₀ : 2 * b < 2 ^ m
  -- hp₁ : b + a < 2 ^ m
  -- hp₂ : q < 2 ^ m
  -- hp₃ : 1 < p
  -- h2prime : Nat.Prime 2
  -- hp₅ : ∀ (i j : ℕ), 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a → i < 2 ∨ j < 2
  ∀ (i j : ℕ), i + j = m ∧ 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a → ¬j < 2 := by
  by_contra! hc
  let ⟨i, j, hi⟩ := hc
  have hi₀: m - 1 ≤ i := by
    rw [← hi.1.1]
    simp
    exact Nat.le_pred_of_lt hi.2
  have hi₁: 2 ^ (m - 1) ≤ 2 ^ i := by exact Nat.pow_le_pow_right (by norm_num) hi₀
  have hi₂: 2 ^ i < 2 ^ (m - 1) := by
    refine lt_of_le_of_lt ?_ h₈₀
    refine Nat.le_of_dvd ?_ hi.1.2.1
    exact Nat.sub_pos_of_lt h₂
  linarith [hi₁, hi₂]


lemma imo_1984_p6_10_6_11
  (m a b : ℕ)
  -- h₁ : Odd a ∧ Odd b
  -- h₂ : a < b
  -- h₈₀ : b - a < 2 ^ (m - 1)
  -- hc : ∃ i j, (i + j = m ∧ 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ j < 2
  (i j : ℕ)
  (hi : (i + j = m ∧ 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ j < 2) :
  2 ^ (m - 1) ≤ 2 ^ i := by
  refine Nat.pow_le_pow_right (by norm_num) ?_
  rw [← hi.1.1]
  simp
  exact Nat.le_pred_of_lt hi.2


lemma imo_1984_p6_10_6_12
  (m a b : ℕ)
  -- h₁ : Odd a ∧ Odd b
  (h₂ : a < b)
  (h₈₀ : b - a < 2 ^ (m - 1))
  -- hc : ∃ i j, (i + j = m ∧ 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ j < 2
  (i j : ℕ)
  (hi : (i + j = m ∧ 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a) ∧ j < 2) :
  -- hi₀ : m - 1 ≤ i
  -- (hi₁ : 2 ^ (m - 1) ≤ 2 ^ i) :
  2 ^ i < 2 ^ (m - 1) := by
  refine lt_of_le_of_lt ?_ h₈₀
  refine Nat.le_of_dvd ?_ hi.1.2.1
  exact Nat.sub_pos_of_lt h₂



lemma imo_1984_p6_10_6_13
  -- (a b c : ℕ)
  (m p q : ℕ)
  (hpq : p * q = 2 ^ m)
  -- h₈₀ : b - a < 2 ^ (m - 1)
  -- hp₀ : 2 * b < 2 ^ m
  -- hp₁ : b + a < 2 ^ m
  -- hp₂ : q < 2 ^ m
  -- hp₃ : 1 < p
  (h2prime : Nat.Prime 2) :
  -- hp₅ : ∀ (i j : ℕ), 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a → i < 2 ∨ j < 2
  -- hp₆ : ∀ (i j : ℕ), i + j = m ∧ 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a → ¬j < 2
  ∃ i ≤ m, p = 2 ^ i := by
  have g₀: p ∣ 2 ^ m := by
    rw [← hpq]
    exact Nat.dvd_mul_right p q
  exact (Nat.dvd_prime_pow h2prime).mp g₀


lemma imo_1984_p6_10_6_14
  (i m : ℕ)
  (him : i ≤ m)
  (j : ℕ := m - i)
  (hj₀ : j = m - i) :
  i + j = m := by
  rw [add_comm, hj₀]
  exact Nat.sub_add_cancel him


lemma imo_1984_p6_10_6_15
  (p q m j : ℕ)
  (hpq : p * q = 2 ^ m)
  (i : ℕ)
  (him : i ≤ m)
  (hp : p = 2 ^ i)
  (hj₀ : j = m - i) :
  q = 2 ^ j := by
  rw [hp] at hpq
  rw [hj₀, ← Nat.pow_div him (by norm_num)]
  refine Nat.eq_div_of_mul_eq_right ?_ hpq
  refine Nat.ne_of_gt ?_
  exact Nat.two_pow_pos i


lemma imo_1984_p6_10_6_16
  (a b p q m : ℕ)
  (hp₃ : 1 < p)
  (hp₅ : ∀ (i j : ℕ), 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a → i < 2 ∨ j < 2)
  (hp₆ : ∀ (i j : ℕ), i + j = m ∧ 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a → ¬j < 2)
  (i j : ℕ)
  (hp : p = 2 ^ i)
  (hq : q = 2 ^ j)
  (hpd : 2 ^ i ∣ b - a)
  (hqd : 2 ^ j ∣ b + a)
  (hij : i + j = m) :
  p = 2 := by
  have hj₃: ¬ j < 2 := by
    exact hp₆ i j {left:= hij , right:= { left := hpd , right:= hqd} }
  have hi₂: i < 2 := by
    have g₀: i < 2 ∨ j < 2 := by
      exact hp₅ i j { left := hpd , right:= hqd }
    omega
  have hi₃: 0 < i := by
    rw [hp] at hp₃
    refine Nat.zero_lt_of_ne_zero ?_
    exact (Nat.one_lt_two_pow_iff).mp hp₃
  have hi₄: i = 1 := by
    exact Nat.eq_of_le_of_lt_succ hi₃ hi₂
  rw [hi₄] at hp
  exact hp



lemma imo_1984_p6_10_6_17
  (a b m : ℕ)
  (hp₆ : ∀ (i j : ℕ), i + j = m ∧ 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a → ¬j < 2)
  (i j : ℕ)
  (hpd : 2 ^ i ∣ b - a)
  (hqd : 2 ^ j ∣ b + a)
  (hij : i + j = m) :
  ¬j < 2 := by
  exact hp₆ i j {left:= hij , right:= { left := hpd , right:= hqd} }



lemma imo_1984_p6_10_6_18
  (a b : ℕ)
  (hp₅ : ∀ (i j : ℕ), 2 ^ i ∣ b - a ∧ 2 ^ j ∣ b + a → i < 2 ∨ j < 2)
  (i j : ℕ)
  (hpd : 2 ^ i ∣ b - a)
  (hqd : 2 ^ j ∣ b + a)
  (hj : ¬j < 2) :
  i < 2 := by
  have g₀: i < 2 ∨ j < 2 := by
    exact hp₅ i j { left := hpd , right:= hqd }
  omega

lemma imo_1984_p6_10_6_19
  (p i : ℕ)
  (hp₃ : 1 < p)
  (hp : p = 2 ^ i) :
  0 < i := by
  rw [hp] at hp₃
  refine Nat.zero_lt_of_ne_zero ?_
  exact (Nat.one_lt_two_pow_iff).mp hp₃


lemma imo_1984_p6_10_6_20
  (p q i j m a b : ℕ)
  (hp : p = 2 ^ i)
  (hq : q = 2 ^ j)
  (hpd : 2 ^ i ∣ b - a)
  (hqd : 2 ^ j ∣ b + a)
  (hij : i + j = m)
  (hj₃ : ¬j < 2)
  (hi₂ : i < 2)
  (hi₃ : 0 < i) :
  p = 2 := by
  suffices hi: i = 1
  . rw [hi] at hp
    exact hp
  . exact Nat.eq_of_le_of_lt_succ hi₃ hi₂


lemma imo_1984_p6_10_7
  (m p q : ℕ)
  (hpq : p * q = 2 ^ m)
  (hm1 : 1 ≤ m)
  (hp : p = 2) :
  q = 2 ^ (m - 1) := by
  rw [hp, ← Nat.pow_sub_mul_pow 2 hm1, pow_one, mul_comm] at hpq
  exact Nat.mul_right_cancel (by norm_num) hpq


lemma imo_1984_p6_10_8
  (a b c m : ℕ)
  -- h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d
  -- h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d
  (h₂ : a < b ∧ b < c)
  (h₅ : b + c = 2 ^ m)
  -- hkm : m < k
  -- h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a)
  -- h₇ : 2 ^ m ∣ (b - a) * (b + a)
  -- h₇₁ : ∃ y z, y ∣ b - a ∧ z ∣ b + a ∧ y * z = 2 ^ m
  (q : ℕ)
  -- (hpd : p ∣ b - a)
  (hqd : q ∣ b + a)
  -- (hpq : p * q = 2 ^ m)
  (hm1 : 1 ≤ m)
  (h₈₀ : b - a < 2 ^ (m - 1))
  -- (hp : p = 2)
  (hq : q = 2 ^ (m - 1)) :
  b + a = 2 ^ (m - 1) := by
  rw [hq] at hqd
  have h₈₂: ∃ c, (b + a) = c * 2 ^ (m - 1) := by
    exact exists_eq_mul_left_of_dvd hqd
  obtain ⟨f, hf⟩ := h₈₂
  have hfeq1: f = 1 := by
    have hf₀: f * 2 ^ (m - 1) < 2 * 2 ^ (m - 1) := by
      rw [← hf, ← Nat.pow_succ', ← Nat.succ_sub hm1]
      rw [Nat.succ_sub_one, ← h₅]
      refine Nat.add_lt_add_left ?_ b
      exact lt_trans h₂.1 h₂.2
    have hf₁: f < 2 := by
      exact Nat.lt_of_mul_lt_mul_right hf₀
    interval_cases f
    . simp at hf
      exfalso
      linarith [hf]
    . linarith
  rw [hfeq1, one_mul] at hf
  exact hf


lemma imo_1984_p6_10_8_1
  (a b m q: ℕ)
  (hqd : q ∣ b + a)
  (hq : q = 2 ^ (m - 1)) :
  ∃ c, b + a = c * 2 ^ (m - 1) := by
  refine exists_eq_mul_left_of_dvd ?_
  rw [hq] at hqd
  exact hqd


lemma imo_1984_p6_10_8_2
  (a b c m : ℕ)
  (h₂ : a < b ∧ b < c)
  (h₅ : b + c = 2 ^ m)
  (hm1 : 1 ≤ m)
  (f : ℕ)
  (hf : b + a = f * 2 ^ (m - 1)) :
  f = 1 := by
  have hf₀: f * 2 ^ (m - 1) < 2 * 2 ^ (m - 1) := by
    rw [← hf, ← Nat.pow_succ', ← Nat.succ_sub hm1]
    rw [Nat.succ_sub_one, ← h₅]
    refine Nat.add_lt_add_left ?_ b
    exact lt_trans h₂.1 h₂.2
  have hf₁: f < 2 := by
    exact Nat.lt_of_mul_lt_mul_right hf₀
  interval_cases f
  . simp at hf
    exfalso
    linarith [hf]
  . linarith


lemma imo_1984_p6_10_8_3
  (a b c m : ℕ)
  (h₂ : a < b ∧ b < c)
  (h₅ : b + c = 2 ^ m)
  (hm1 : 1 ≤ m)
  (f : ℕ)
  (hf : b + a = f * 2 ^ (m - 1)) :
  f < 2 := by
  have hf₀: f * 2 ^ (m - 1) < 2 * 2 ^ (m - 1) := by
    rw [← hf, ← Nat.pow_succ', ← Nat.succ_sub hm1]
    rw [Nat.succ_sub_one, ← h₅]
    refine Nat.add_lt_add_left ?_ b
    exact lt_trans h₂.1 h₂.2
  exact Nat.lt_of_mul_lt_mul_right hf₀


lemma imo_1984_p6_10_8_4
  (a b c m : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (h₂ : a < b ∧ b < c)
  (f : ℕ)
  (hf : b + a = f * 2 ^ (m - 1))
  -- (hf₀ : f * 2 ^ (m - 1) < 2 * 2 ^ (m - 1))
  (hf₁ : f < 2) :
  f = 1 := by
  interval_cases f
  . simp at hf
    exfalso
    linarith [hf]
  . linarith


lemma imo_1984_p6_11
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h₂ : a < b ∧ b < c ∧ c < d)
  (h₃ : a * d = b * c)
  -- (h₄ : a + d = 2 ^ k)
  (h₅ : b + c = 2 ^ m)
  -- (hkm : m < k)
  (h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a))
  (h₇ : 2 ^ m ∣ (b - a) * (b + a))
  (h₈ : b + a = 2 ^ (m - 1)) :
  a = 2 ^ (2 * m - 2) / 2 ^ k := by
  have ga: 1 ≤ a := by exact Nat.succ_le_of_lt h₀.1
  have gb: 3 ≤ b := by
    by_contra! hc
    interval_cases b
    . linarith
    . linarith [ga, h₂.1]
    . have hc₁: Odd 2 := by exact h₁.2.1
      have hc₂: Even 2 := by exact even_iff.mpr rfl
      have hc₃: ¬ Even 2 := by exact not_even_iff_odd.mpr hc₁
      exact hc₃ hc₂
  have gm: 3 ≤ m := by
    have gm₀: 2 ^ 2 ≤ 2 ^ (m - 1) := by
      norm_num
      rw [← h₈]
      linarith
    have gm₁: 2 ≤ m - 1 := by
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp gm₀
    omega
  have g₀: a < 2 ^ (m - 2) := by
    have g₀₀: a + a < b + a := by simp [h₂.1]
    rw [h₈, ← mul_two a] at g₀₀
    have g₀₁: m - 1 = Nat.succ (m - 2) := by
      rw [← Nat.succ_sub ?_]
      . rw [succ_eq_add_one]
        omega
      . linarith
    rw [g₀₁, Nat.pow_succ 2 _] at g₀₀
    exact Nat.lt_of_mul_lt_mul_right g₀₀
  have h₉₀: b = 2 ^ (m - 1) - a := by
    symm
    exact Nat.sub_eq_of_eq_add h₈.symm
  rw [h₈, h₉₀] at h₆
  repeat rw [Nat.mul_sub_right_distrib] at h₆
  repeat rw [← Nat.pow_add] at h₆
  have hm1: 1 ≤ m := by
    linarith
  repeat rw [← Nat.sub_add_comm hm1] at h₆
  repeat rw [← Nat.add_sub_assoc hm1] at h₆
  ring_nf at h₆
  rw [← Nat.sub_add_eq _ 1 1] at h₆
  norm_num at h₆
  rw [← Nat.sub_add_eq _ (a * 2 ^ (m - 1)) (a * 2 ^ (m - 1))] at h₆
  rw [← two_mul (a * 2 ^ (m - 1))] at h₆
  rw [mul_comm 2 _] at h₆
  rw [mul_assoc a (2 ^ (m - 1)) 2] at h₆
  rw [← Nat.pow_succ, succ_eq_add_one] at h₆
  rw [Nat.sub_add_cancel hm1] at h₆
  rw [← Nat.sub_add_eq ] at h₆
  have h₉₁: 2 ^ (m * 2 - 1) = 2 ^ (m * 2 - 2) - a * 2 ^ m + (a * 2 ^ m + a * 2 ^ k) := by
    refine Nat.eq_add_of_sub_eq ?_ h₆
    by_contra! hc
    have g₁: 2 ^ (m * 2 - 1) - (a * 2 ^ m + a * 2 ^ k) = 0 := by
      exact Nat.sub_eq_zero_of_le (le_of_lt hc)
    rw [g₁] at h₆
    have g₂: 2 ^ (m * 2 - 2) ≤ a * 2 ^ m := by exact Nat.le_of_sub_eq_zero h₆.symm
    have g₃: 2 ^ (m - 2) ≤ a := by
      rw [mul_two, Nat.add_sub_assoc (by linarith) m] at g₂
      rw [Nat.pow_add, mul_comm] at g₂
      refine Nat.le_of_mul_le_mul_right g₂ ?_
      exact Nat.two_pow_pos m
    linarith [g₀, g₃]
  rw [← Nat.add_assoc] at h₉₁
  have h₉₂: a * 2 ^ k = 2 * 2 ^ (2 * m - 2) - 2 ^ (2 * m - 2) := by
    rw [Nat.sub_add_cancel ?_] at h₉₁
    . rw [add_comm] at h₉₁
      symm
      rw [← Nat.pow_succ', succ_eq_add_one]
      rw [← Nat.sub_add_comm ?_]
      . simp
        rw [mul_comm 2 m]
        exact Nat.sub_eq_of_eq_add h₉₁
      . linarith [hm1]
    . refine le_of_lt ?_
      rw [mul_two, Nat.add_sub_assoc, Nat.pow_add, mul_comm (2 ^ m) _]
      refine (Nat.mul_lt_mul_right (by linarith)).mpr g₀
      linarith
  nth_rewrite 2 [← Nat.one_mul (2 ^ (2 * m - 2))] at h₉₂
  rw [← Nat.mul_sub_right_distrib 2 1 (2 ^ (2 * m - 2))] at h₉₂
  norm_num at h₉₂
  refine Nat.eq_div_of_mul_eq_left ?_ h₉₂
  exact Ne.symm (NeZero.ne' (2 ^ k))


lemma imo_1984_p6_11_1
  (a b c d: ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h₂ : a < b ∧ b < c ∧ c < d) :
  -- (h₃ : a * d = b * c)
  -- (h₅ : b + c = 2 ^ m)
  -- (h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a))
  -- (h₇ : 2 ^ m ∣ (b - a) * (b + a))
  -- (h₈ : b + a = 2 ^ (m - 1))
  3 ≤ b := by
  by_contra! hc
  interval_cases b
  . linarith
  . linarith [h₀.1, h₂.1]
  . have hc₀: Odd 2 := by exact h₁.2.1
    have hc₁: ¬ Odd 2 := by decide
    exact hc₁ hc₀


lemma imo_1984_p6_11_2
  (a b m : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  -- h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d
  -- h₂ : a < b ∧ b < c ∧ c < d
  -- h₃ : a * d = b * c
  -- h₅ : b + c = 2 ^ m
  -- h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a)
  -- h₇ : 2 ^ m ∣ (b - a) * (b + a)
  (h₈ : b + a = 2 ^ (m - 1))
  (ga : 1 ≤ a)
  (gb : 3 ≤ b) :
  3 ≤ m := by
  have gm₀: 2 ^ 2 ≤ 2 ^ (m - 1) := by
    norm_num
    rw [← h₈]
    linarith
  have gm₁: 2 ≤ m - 1 := by
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp gm₀
  omega


lemma imo_1984_p6_11_3
  (a b m : ℕ)
  (h₂ : a < b)
  (h₈ : b + a = 2 ^ (m - 1))
  (gm : 3 ≤ m) :
  a < 2 ^ (m - 2) := by
  have g₀₀: a + a < b + a := by simp [h₂]
  rw [h₈, ← mul_two a] at g₀₀
  have g₀₁: m - 1 = Nat.succ (m - 2) := by
    rw [← Nat.succ_sub ?_]
    . rw [succ_eq_add_one]
      omega
    . linarith
  rw [g₀₁, Nat.pow_succ 2 _] at g₀₀
  exact Nat.lt_of_mul_lt_mul_right g₀₀


lemma imo_1984_p6_11_4
  (a b k m : ℕ)
  (h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a))
  (h₈ : b + a = 2 ^ (m - 1))
  (h₉ : b = 2 ^ (m - 1) - a)
  (hm1 : 1 ≤ m) :
  2 ^ (m * 2 - 1) - (a * 2 ^ m + a * 2 ^ k) = 2 ^ (m * 2 - 2) - a * 2 ^ m := by
  rw [h₈, h₉] at h₆
  repeat rw [Nat.mul_sub_right_distrib] at h₆
  repeat rw [← Nat.pow_add] at h₆
  repeat rw [← Nat.sub_add_comm hm1] at h₆
  repeat rw [← Nat.add_sub_assoc hm1] at h₆
  ring_nf at h₆
  rw [← Nat.sub_add_eq _ 1 1] at h₆
  norm_num at h₆
  rw [← Nat.sub_add_eq _ (a * 2 ^ (m - 1)) (a * 2 ^ (m - 1))] at h₆
  rw [← two_mul (a * 2 ^ (m - 1))] at h₆
  rw [mul_comm 2 _] at h₆
  rw [mul_assoc a (2 ^ (m - 1)) 2] at h₆
  rw [← Nat.pow_succ, succ_eq_add_one] at h₆
  rw [Nat.sub_add_cancel hm1] at h₆
  rw [← Nat.sub_add_eq ] at h₆
  exact h₆


lemma imo_1984_p6_11_5
  (a k m : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  -- (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  -- (h₂ : a < b ∧ b < c ∧ c < d)
  -- (h₃ : a * d = b * c)
  -- (h₅ : b + c = 2 ^ m)
  -- (h₇ : 2 ^ m ∣ (b - a) * (b + a))
  -- (h₈ : b + a = 2 ^ (m - 1))
  -- (ga : 1 ≤ a)
  -- (gb : 3 ≤ b)
  (gm : 3 ≤ m)
  (g₀ : a < 2 ^ (m - 2))
  -- (h₉ : b = 2 ^ (m - 1) - a)
  -- (hm1 : 1 ≤ m)
  (h₆ : 2 ^ (m * 2 - 1) - (a * 2 ^ m + a * 2 ^ k) = 2 ^ (m * 2 - 2) - a * 2 ^ m) :
  2 ^ (m * 2 - 1) = 2 ^ (m * 2 - 2) - a * 2 ^ m + (a * 2 ^ m + a * 2 ^ k) := by
  refine Nat.eq_add_of_sub_eq ?_ h₆
  by_contra! hc
  have g₁: 2 ^ (m * 2 - 1) - (a * 2 ^ m + a * 2 ^ k) = 0 := by
    exact Nat.sub_eq_zero_of_le (le_of_lt hc)
  rw [g₁] at h₆
  have g₂: 2 ^ (m * 2 - 2) ≤ a * 2 ^ m := by exact Nat.le_of_sub_eq_zero h₆.symm
  have g₃: 2 ^ (m - 2) ≤ a := by
    rw [mul_two, Nat.add_sub_assoc (by linarith) m] at g₂
    rw [Nat.pow_add, mul_comm] at g₂
    refine Nat.le_of_mul_le_mul_right g₂ ?_
    exact Nat.two_pow_pos m
  linarith [g₀, g₃]


lemma imo_1984_p6_11_6
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  -- h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d
  -- h₂ : a < b ∧ b < c ∧ c < d
  -- h₃ : a * d = b * c
  (h₅ : b + c = 2 ^ m)
  -- (h₇ : 2 ^ m ∣ (b - a) * (b + a))
  -- h₈ : b + a = 2 ^ (m - 1)
  -- ga : 1 ≤ a
  -- gb : 3 ≤ b
  (gm : 3 ≤ m)
  (g₀ : a < 2 ^ (m - 2))
  -- h₉₀ : b = 2 ^ (m - 1) - a
  (hm1 : 1 ≤ m)
  -- h₆ : 2 ^ (m * 2 - 1) - (a * 2 ^ m + a * 2 ^ k) = 2 ^ (m * 2 - 2) - a * 2 ^ m
  (h₉₁ : 2 ^ (m * 2 - 1) = 2 ^ (m * 2 - 2) - a * 2 ^ m + a * 2 ^ m + a * 2 ^ k) :
  a * 2 ^ k = 2 * 2 ^ (2 * m - 2) - 2 ^ (2 * m - 2) := by
  rw [Nat.sub_add_cancel ?_] at h₉₁
  . rw [add_comm] at h₉₁
    symm
    rw [← Nat.pow_succ', succ_eq_add_one]
    rw [← Nat.sub_add_comm ?_]
    . simp
      rw [mul_comm 2 m]
      exact Nat.sub_eq_of_eq_add h₉₁
    . linarith [hm1]
  . refine le_of_lt ?_
    rw [mul_two, Nat.add_sub_assoc, Nat.pow_add, mul_comm (2 ^ m) _]
    . refine (Nat.mul_lt_mul_right ?_).mpr g₀
      linarith
    . linarith

lemma imo_1984_p6_11_7
  (a k m : ℕ)
  (h₉₂ : a * 2 ^ k = 2 * 2 ^ (2 * m - 2) - 2 ^ (2 * m - 2)) :
  a = 2 ^ (2 * m - 2) / 2 ^ k := by
  nth_rewrite 2 [← Nat.one_mul (2 ^ (2 * m - 2))] at h₉₂
  rw [← Nat.mul_sub_right_distrib 2 1 (2 ^ (2 * m - 2))] at h₉₂
  norm_num at h₉₂
  refine Nat.eq_div_of_mul_eq_left ?_ h₉₂
  exact Ne.symm (NeZero.ne' (2 ^ k))



lemma imo_1984_p6_12
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h₂ : a < b ∧ b < c ∧ c < d)
  (h₃ : a * d = b * c)
  (h₄ : a + d = 2 ^ k)
  -- (h₅ : b + c = 2 ^ m)
  -- (hkm : m < k)
  (h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a))
  (h₇ : 2 ^ m ∣ (b - a) * (b + a))
  (h₈ : b + a = 2 ^ (m - 1))
  (h₉ : a = 2 ^ (2 * m - 2) / 2 ^ k) :
  a = 1 := by
  by_cases h₁₀: k ≤ 2 * m - 2
  . rw [Nat.pow_div h₁₀ (by norm_num)] at h₉
    rw [Nat.sub_right_comm (2*m) 2 k] at h₉
    by_contra! hc
    cases' (lt_or_gt_of_ne hc) with hc₀ hc₁
    . interval_cases a
      linarith
    . have hc₂: ¬ Odd a := by
        refine (not_odd_iff_even).mpr ?_
        have hc₃: 1 ≤ 2 * m - k - 2 := by
          by_contra! hc₄
          interval_cases (2 * m - k - 2)
          simp at h₉
          rw [h₉] at hc₁
          contradiction
        have hc₄: 2 * m - k - 2 = succ (2 * m - k - 3) := by
          rw [succ_eq_add_one]
          exact Nat.eq_add_of_sub_eq hc₃ rfl
        rw [h₉, hc₄, Nat.pow_succ']
        exact even_two_mul (2 ^ (2 * m - k - 3))
      exact hc₂ h₁.1
  . push_neg at h₁₀
    exfalso
    have ha: a = 0 := by
      rw [h₉]
      refine (Nat.div_eq_zero_iff).mpr ?_
      right
      refine Nat.pow_lt_pow_right ?_ h₁₀
      exact Nat.one_lt_two
    linarith [ha, h₀.1]



lemma imo_1984_p6_13
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h₂ : a < b ∧ b < c ∧ c < d)
  (h₃ : a * d = b * c)
  (h₄ : a + d = 2 ^ k)
  -- (h₅ : b + c = 2 ^ m)
  -- (hkm : m < k)
  (h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a))
  (h₇ : 2 ^ m ∣ (b - a) * (b + a))
  (h₈ : b + a = 2 ^ (m - 1))
  (h₉ : a = 2 ^ (2 * m - 2) / 2 ^ k)
  (h₁₀: k ≤ 2 * m - 2) :
  a = 1 := by
  rw [Nat.pow_div h₁₀ (by norm_num)] at h₉
  rw [Nat.sub_right_comm (2*m) 2 k] at h₉
  by_contra! hc
  cases' (lt_or_gt_of_ne hc) with hc₀ hc₁
  . interval_cases a
    linarith
  . have hc₂: ¬ Odd a := by
      refine (not_odd_iff_even).mpr ?_
      have hc₃: 1 ≤ 2 * m - k - 2 := by
        by_contra! hc₄
        interval_cases (2 * m - k - 2)
        simp at h₉
        rw [h₉] at hc₁
        contradiction
      have hc₄: 2 * m - k - 2 = succ (2 * m - k - 3) := by
        rw [succ_eq_add_one]
        exact Nat.eq_add_of_sub_eq hc₃ rfl
      rw [h₉, hc₄, Nat.pow_succ']
      exact even_two_mul (2 ^ (2 * m - k - 3))
    exact hc₂ h₁.1


lemma imo_1984_p6_13_1
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h₂ : a < b ∧ b < c ∧ c < d)
  (h₃ : a * d = b * c)
  (h₄ : a + d = 2 ^ k)
  (h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a))
  (h₇ : 2 ^ m ∣ (b - a) * (b + a))
  (h₈ : b + a = 2 ^ (m - 1))
  (h₉ : a = 2 ^ (2 * m - k - 2))
  -- (h₁₀ : k ≤ 2 * m - 2)
  (hc : a < 1) :
  False := by
  interval_cases a
  linarith


lemma imo_1984_p6_13_2
  (a b c d k m : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  -- (h₂ : a < b ∧ b < c ∧ c < d)
  -- (h₃ : a * d = b * c)
  -- (h₄ : a + d = 2 ^ k)
  -- (h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a))
  -- (h₇ : 2 ^ m ∣ (b - a) * (b + a))
  -- (h₈ : b + a = 2 ^ (m - 1))
  (h₉ : a = 2 ^ (2 * m - k - 2))
  -- (h₁₀ : k ≤ 2 * m - 2)
  (hc : 1 < a) :
  False := by
  have hc₂: ¬ Odd a := by
    refine (not_odd_iff_even).mpr ?_
    have hc₃: 1 ≤ 2 * m - k - 2 := by
      by_contra! hc₄
      interval_cases (2 * m - k - 2)
      simp at h₉
      rw [h₉] at hc
      contradiction
    have hc₄: 2 * m - k - 2 = succ (2 * m - k - 3) := by
      rw [succ_eq_add_one]
      exact Nat.eq_add_of_sub_eq hc₃ rfl
    rw [h₉, hc₄, Nat.pow_succ']
    exact even_two_mul (2 ^ (2 * m - k - 3))
  exact hc₂ h₁.1


lemma imo_1984_p6_13_3
  (a k m : ℕ)
  (h₉ : a = 2 ^ (2 * m - k - 2))
  (hc : 1 < a) :
  1 ≤ 2 * m - k - 2 := by
  by_contra! hc₄
  interval_cases (2 * m - k - 2)
  simp at h₉
  rw [h₉] at hc
  contradiction


lemma imo_1984_p6_13_4
  (a k m : ℕ)
  (h₉ : a = 2 ^ (2 * m - k - 2))
  (hc : 1 < a) :
  Even a := by
  have hc₃: 1 ≤ 2 * m - k - 2 := by
    by_contra! hc₄
    interval_cases (2 * m - k - 2)
    simp at h₉
    rw [h₉] at hc
    contradiction
  have hc₄: 2 * m - k - 2 = succ (2 * m - k - 3) := by
    rw [succ_eq_add_one]
    exact Nat.eq_add_of_sub_eq hc₃ rfl
  rw [h₉, hc₄, Nat.pow_succ']
  exact even_two_mul (2 ^ (2 * m - k - 3))


lemma imo_1984_p6_14
  (a k m : ℕ)
  (h₀ : 0 < a)
  -- (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  -- (h₂ : a < b ∧ b < c ∧ c < d)
  -- (h₃ : a * d = b * c)
  -- (h₄ : a + d = 2 ^ k)
  -- (h₅ : b + c = 2 ^ m)
  -- (hkm : m < k)
  -- (h₆ : b * 2 ^ m - a * 2 ^ k = (b - a) * (b + a))
  -- (h₇ : 2 ^ m ∣ (b - a) * (b + a))
  -- (h₈ : b + a = 2 ^ (m - 1))
  (h₉ : a = 2 ^ (2 * m - 2) / 2 ^ k)
  (hk2m : 2 * m - 2 < k) :
  False := by
  have ha: a = 0 := by
    rw [h₉]
    refine (Nat.div_eq_zero_iff).mpr ?_
    right
    exact Nat.pow_lt_pow_right (by norm_num) hk2m
  linarith [ha, h₀]


lemma imo_1984_p6_15
  (a k m : ℕ)
  (h₉ : a = 2 ^ (2 * m - 2) / 2 ^ k)
  (hk2m : 2 * m - 2 < k) :
  a = 0 := by
  rw [h₉]
  refine (Nat.div_eq_zero_iff).mpr ?_
  right
  exact Nat.pow_lt_pow_right (by norm_num) hk2m
