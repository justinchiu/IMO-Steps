import Mathlib
set_option linter.unusedVariables.analyzeTactics true

open Nat


lemma imo_2022_p5_1
  (b p: ℕ)
  (h₀: 0 < b)
  -- (hp: Nat.prime p)
  (hbp: b < p) :
  (1 + (b * p + b ^ p) ≤ (1 + b) ^ p) := by
  refine Nat.le_induction ?_ ?_ p hbp
  . rw [add_pow 1 b b.succ]
    rw [Finset.sum_range_succ _ b.succ]
    simp
    rw [add_comm (∑ x ∈ Finset.range (b + 1), b ^ (b + 1 - x) * (b + 1).choose x) 1]
    simp
    rw [Finset.sum_range_succ _ b]
    simp
    rw [add_comm _ (b * (b + 1))]
    simp
    have gb: b = b - 1 + 1 := by exact (Nat.sub_eq_iff_eq_add h₀).mp rfl
    nth_rewrite 3 [gb]
    rw [Finset.sum_range_succ' _ (b-1)]
    simp
  . intros n _ h₂
    nth_rewrite 2 [pow_add]
    rw [pow_one]
    have h₃: (1 + (b * n + b ^ n)) * (1 + b) ≤ ((1 + b) ^ n) * (1 + b) := by
      exact mul_le_mul_right' h₂ (1 + b)
    have h₄: 1 + (b * (n + 1) + b ^ (n + 1)) ≤ (1 + (b * n + b ^ n)) * (1 + b) := by
      ring_nf
      rw [Nat.add_assoc _ (b ^ 2 * n) (b ^ n)]
      exact Nat.le_add_right (1 + b + b * b ^ n + b * n) (b ^ 2 * n + b ^ n)
    exact le_trans h₄ h₃


lemma imo_2022_p5_1_1
  (b : ℕ)
  -- (p : ℕ)
  (h₀ : 0 < b) :
  -- (hbp : b < p) :
  1 + (b * succ b + b ^ succ b) ≤ (1 + b) ^ succ b := by
  rw [add_pow 1 b b.succ]
  rw [Finset.sum_range_succ _ b.succ]
  simp
  rw [add_comm (∑ x ∈ Finset.range (b + 1), b ^ (b + 1 - x) * (b + 1).choose x) 1]
  simp
  rw [Finset.sum_range_succ _ b]
  simp
  rw [add_comm _ (b * (b + 1))]
  simp
  have gb: b = b - 1 + 1 := by exact (Nat.sub_eq_iff_eq_add h₀).mp rfl
  nth_rewrite 3 [gb]
  rw [Finset.sum_range_succ' _ (b-1)]
  simp


lemma imo_2022_p5_1_2
  (b : ℕ)
  -- (p : ℕ)
  (h₀ : 0 < b) :
  -- (hbp : b < p) :
  1 + (b * succ b + b ^ succ b) ≤
    (Finset.sum (Finset.range (succ b)) fun x => 1 ^ x * b ^ (succ b - x) * ↑(choose (succ b) x)) +
      1 ^ succ b * b ^ (succ b - succ b) * ↑(choose (succ b) (succ b)) := by
  simp
  rw [add_comm (∑ x ∈ Finset.range (b + 1), b ^ (b + 1 - x) * (b + 1).choose x) 1]
  simp
  rw [Finset.sum_range_succ _ b]
  simp
  rw [add_comm _ (b * (b + 1))]
  simp
  have gb: b = b - 1 + 1 := by exact (Nat.sub_eq_iff_eq_add h₀).mp rfl
  nth_rewrite 3 [gb]
  rw [Finset.sum_range_succ' _ (b-1)]
  simp


lemma imo_2022_p5_1_3
  (b : ℕ)
  -- (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hbp : b < p)
  (h₁ : 1 + (b * succ b + b ^ succ b) ≤
    (Finset.sum (Finset.range (succ b)) fun x => 1 ^ x * b ^ (succ b - x) * ↑(choose (succ b) x)) +
      1 ^ succ b * b ^ (succ b - succ b) * ↑(choose (succ b) (succ b))) :
  1 + (b * succ b + b ^ succ b) ≤ (1 + b) ^ succ b := by
  rw [add_pow 1 b b.succ]
  rw [Finset.sum_range_succ _ b.succ]
  exact h₁


lemma imo_2022_p5_1_4
  (b : ℕ)
  -- (p : ℕ)
  (h₀ : 0 < b) :
  -- (hbp : b < p) :
  b * succ b + b ^ succ b ≤
    Finset.sum (Finset.range (succ b)) fun x => b ^ (succ b - x) * choose (succ b) x := by
  rw [Finset.sum_range_succ _ b]
  rw [succ_eq_add_one]
  simp
  rw [add_comm _ (b * (b + 1))]
  simp
  have gb: b = b - 1 + 1 := by exact (Nat.sub_eq_iff_eq_add h₀).mp rfl
  nth_rewrite 3 [gb]
  rw [Finset.sum_range_succ' _ (b-1)]
  simp


lemma imo_2022_p5_1_5
  (b : ℕ)
  -- (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hbp : b < p)
  (h₁ : b * (b + 1) + b ^ (b + 1) ≤
  (Finset.sum (Finset.range b) fun x => b ^ (b + 1 - x) * choose (b + 1) x) + b ^ (b + 1 - b) * choose (b + 1) b) :
  1 + (b * succ b + b ^ succ b) ≤ (1 + b) ^ succ b := by
  rw [add_pow 1 b b.succ]
  rw [Finset.sum_range_succ _ b.succ]
  simp
  rw [add_comm (∑ x ∈ Finset.range (b + 1), b ^ (b + 1 - x) * (b + 1).choose x) 1]
  simp
  rw [Finset.sum_range_succ _ b]
  exact h₁


lemma imo_2022_p5_1_6
  (b : ℕ)
  -- (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hbp : b < p)
  (h₁ : b * succ b + b ^ succ b ≤
    Finset.sum (Finset.range (succ b)) fun x => b ^ (succ b - x) * choose (succ b) x) :
  1 + (b * succ b + b ^ succ b) ≤
    (Finset.sum (Finset.range (succ b)) fun x => 1 ^ x * b ^ (succ b - x) * ↑(choose (succ b) x)) +
      1 ^ succ b * b ^ (succ b - succ b) * ↑(choose (succ b) (succ b)) := by
  simp
  rw [add_comm (∑ x ∈ Finset.range (b + 1), b ^ (b + 1 - x) * (b + 1).choose x) 1]
  simp
  exact h₁


lemma imo_2022_p5_1_7
  (b : ℕ)
  -- (p : ℕ)
  (h₀ : 0 < b) :
  -- (hbp : b < p) :
  b * succ b + b ^ succ b ≤
    (Finset.sum (Finset.range b) fun x => b ^ (succ b - x)
      * choose (succ b) x) + b ^ (succ b - b) * choose (succ b) b := by
  rw [succ_eq_add_one]
  simp
  rw [add_comm _ (b * (b + 1))]
  simp
  have gb: b = b - 1 + 1 := by exact (Nat.sub_eq_iff_eq_add h₀).mp rfl
  nth_rewrite 3 [gb]
  rw [Finset.sum_range_succ' _ (b-1)]
  simp


lemma imo_2022_p5_1_8
  (b : ℕ)
  -- (p : ℕ)
  (h₀ : 0 < b) :
  -- (hbp : b < p) :
  b * (b + 1) + b ^ (b + 1) ≤
    (Finset.sum (Finset.range b) fun x => b ^ (b + 1 - x) * choose (b + 1) x) + b * (b + 1) := by
  rw [add_comm _ (b * (b + 1))]
  simp
  have gb: b = b - 1 + 1 := by exact (Nat.sub_eq_iff_eq_add h₀).mp rfl
  nth_rewrite 3 [gb]
  rw [Finset.sum_range_succ' _ (b-1)]
  simp


lemma imo_2022_p5_1_9
  (b : ℕ)
  -- (p : ℕ)
  (h₀ : 0 < b) :
  -- (hbp : b < p) :
  b ^ (b + 1) ≤ Finset.sum (Finset.range b) fun x => b ^ (b + 1 - x) * choose (b + 1) x := by
  have gb: b = b - 1 + 1 := by exact (Nat.sub_eq_iff_eq_add h₀).mp rfl
  nth_rewrite 3 [gb]
  rw [Finset.sum_range_succ' _ (b-1)]
  simp


lemma imo_2022_p5_1_10
  (b : ℕ)
  -- (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hbp : b < p)
  (gb : b = b - 1 + 1) :
  b ^ (b + 1) ≤ Finset.sum (Finset.range b) fun x => b ^ (b + 1 - x) * choose (b + 1) x := by
  nth_rewrite 3 [gb]
  rw [Finset.sum_range_succ' _ (b-1)]
  simp


lemma imo_2022_p5_1_11
  (b : ℕ) :
  -- (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hbp : b < p)
  -- (gb : b = b - 1 + 1) :
  b ^ (b + 1) ≤ Finset.sum (Finset.range (b - 1 + 1)) fun x => b ^ (b + 1 - x) * choose (b + 1) x := by
  rw [Finset.sum_range_succ' _ (b-1)]
  simp

lemma imo_2022_p5_1_12
  (b : ℕ) :
  -- (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hbp : b < p) :
  ∀ (n : ℕ), succ b ≤ n → 1 + (b * n + b ^ n) ≤
    (1 + b) ^ n → 1 + (b * (n + 1) + b ^ (n + 1)) ≤ (1 + b) ^ (n + 1) := by
  intros n _ h₂
  nth_rewrite 2 [pow_add]
  rw [pow_one]
  have h₃: (1 + (b * n + b ^ n)) * (1 + b) ≤ ((1 + b) ^ n) * (1 + b) := by
    exact mul_le_mul_right' h₂ (1 + b)
  have h₄: 1 + (b * (n + 1) + b ^ (n + 1)) ≤ (1 + (b * n + b ^ n)) * (1 + b) := by
    ring_nf
    rw [Nat.add_assoc _ (b ^ 2 * n) (b ^ n)]
    exact Nat.le_add_right (1 + b + b * b ^ n + b * n) (b ^ 2 * n + b ^ n)
  exact le_trans h₄ h₃


lemma imo_2022_p5_1_13
  (b : ℕ)
  -- (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hbp : b < p)
  (n : ℕ)
  -- (hmn : succ b ≤ n)
  (h₂ : 1 + (b * n + b ^ n) ≤ (1 + b) ^ n) :
  1 + (b * (n + 1) + b ^ (n + 1)) ≤ (1 + b) ^ n * (1 + b) := by
  have h₃: (1 + (b * n + b ^ n)) * (1 + b) ≤ ((1 + b) ^ n) * (1 + b) := by
    exact mul_le_mul_right' h₂ (1 + b)
  have h₄: 1 + (b * (n + 1) + b ^ (n + 1)) ≤ (1 + (b * n + b ^ n)) * (1 + b) := by
    ring_nf
    rw [Nat.add_assoc _ (b ^ 2 * n) (b ^ n)]
    exact Nat.le_add_right (1 + b + b * b ^ n + b * n) (b ^ 2 * n + b ^ n)
  exact le_trans h₄ h₃


lemma imo_2022_p5_1_14
  (b : ℕ)
  -- (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hbp : b < p)
  (n : ℕ) :
  -- (h₂ : 1 + (b * n + b ^ n) ≤ (1 + b) ^ n)
  -- (h₃ : (1 + (b * n + b ^ n)) * (1 + b) ≤ ((1 + b) ^ n) * (1 + b)) :
  1 + (b * (n + 1) + b ^ (n + 1)) ≤ (1 + (b * n + b ^ n)) * (1 + b) := by
  have h₄: 1 + (b * (n + 1) + b ^ (n + 1)) ≤ (1 + (b * n + b ^ n)) * (1 + b) := by
    ring_nf
    rw [Nat.add_assoc _ (b ^ 2 * n) (b ^ n)]
    exact Nat.le_add_right (1 + b + b * b ^ n + b * n) (b ^ 2 * n + b ^ n)
  refine le_trans h₄ ?_
  linarith


lemma imo_2022_p5_1_15
  (b : ℕ)
  -- (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hbp : b < p)
  (n : ℕ) :
  -- (hmn : succ b ≤ n)
  -- (h₂ : 1 + (b * n + b ^ n) ≤ (1 + b) ^ n)
  -- (h₃ : (1 + (b * n + b ^ n)) * (1 + b) ≤ (1 + b) ^ n * (1 + b)) :
  1 + b + b * b ^ n + b * n ≤ 1 + b + b * b ^ n + b * n + b ^ 2 * n + b ^ n := by
  ring_nf
  rw [Nat.add_assoc _ (b ^ 2 * n) (b ^ n)]
  exact Nat.le_add_right (1 + b + b * b ^ n + b * n) (b ^ 2 * n + b ^ n)






lemma imo_2022_p5_2
  (n : ℕ)
  (hi : n ! ≤ n ^ n) :
  (succ n)! ≤ succ n ^ succ n := by
  by_cases hnp: 0 < n
  . rw [ factorial_succ, succ_eq_add_one, pow_add, pow_one, mul_comm ]
    refine mul_le_mul_right (n + 1) ?_
    -- have h₁: n.factorial ≤ n ^ n,
    -- { exact hi hnp },
    have h₂: n^ n ≤ (n + 1)^n := by
      refine (Nat.pow_le_pow_iff_left ?_).mpr ?_
      . linarith
      . linarith
    exact le_trans hi h₂
  . push_neg at hnp
    interval_cases n
    simp


lemma imo_2022_p5_2_1
  (n : ℕ)
  (hi : n ! ≤ n ^ n)
  (hnp : 0 < n) :
  (succ n)! ≤ succ n ^ succ n := by
  rw [ factorial_succ, succ_eq_add_one, pow_add, pow_one, mul_comm ]
  refine mul_le_mul_right (n + 1) ?_
  have h₂: n^ n ≤ (n + 1)^n := by
    refine (Nat.pow_le_pow_iff_left ?_).mpr ?_
    . linarith
    . linarith
  exact le_trans hi h₂


lemma imo_2022_p5_2_2
  (n : ℕ)
  (hi : n ! ≤ n ^ n)
  (hnp : ¬0 < n) :
  (succ n)! ≤ succ n ^ succ n := by
  push_neg at hnp
  interval_cases n
  simp


lemma imo_2022_p5_2_3
  (n : ℕ)
  (hi : n ! ≤ n ^ n)
  (hnp : 0 < n) :
  -- (h₁: (succ n)! ≤ succ n ^ succ n) :
  n ! * (n + 1) ≤ (n + 1) ^ n * (n + 1) := by
  refine mul_le_mul_right (n + 1) ?_
  have h₂: n^ n ≤ (n + 1)^n := by
    refine (Nat.pow_le_pow_iff_left ?_).mpr ?_
    . linarith
    . linarith
  exact le_trans hi h₂


lemma imo_2022_p5_2_4
  (n : ℕ)
  (hi : n ! ≤ n ^ n)
  (hnp : 0 < n) :
  n ! ≤ (n + 1) ^ n := by
  have h₂: n^ n ≤ (n + 1)^n := by
    refine (Nat.pow_le_pow_iff_left ?_).mpr ?_
    . linarith
    . linarith
  exact le_trans hi h₂


lemma imo_2022_p5_2_5
  (n : ℕ)
  -- (hi : n ! ≤ n ^ n)
  (hnp : 0 < n) :
  n ^ n ≤ (n + 1) ^ n := by
  refine (Nat.pow_le_pow_iff_left ?_).mpr ?_
  . linarith
  . linarith




lemma imo_2022_p5_3
  (a b p: ℕ)
  -- (h₀: 0 < a ∧ 0 < b)
  (hp: Nat.Prime p)
  (h₁: a ^ p = b.factorial + p)
  (hbp: p ≤ b) :
  (p ∣ a) := by
  have h₂: p ∣ b.factorial := by exact Nat.dvd_factorial (Nat.Prime.pos hp) hbp
  have h₃: p ∣ b.factorial + p := by exact Nat.dvd_add_self_right.mpr h₂
  have h₄: p ∣ a^p := by
    rw [h₁]
    exact h₃
  exact Nat.Prime.dvd_of_dvd_pow hp h₄


lemma imo_2022_p5_3_1
  (a b p : ℕ)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  (h₂ : p ∣ b !) :
  p ∣ a := by
  have h₃: p ∣ b.factorial + p := by exact Nat.dvd_add_self_right.mpr h₂
  have h₄: p ∣ a^p := by
    rw [h₁]
    exact h₃
  exact Nat.Prime.dvd_of_dvd_pow hp h₄


lemma imo_2022_p5_3_2
  (a b p : ℕ)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (h₂ : p ∣ b !)
  (h₃ : p ∣ b ! + p) :
  p ∣ a := by
  have h₄: p ∣ a^p := by
    rw [h₁]
    exact h₃
  exact Nat.Prime.dvd_of_dvd_pow hp h₄





lemma imo_2022_p5_4
  (a b : ℕ)
  (h₀: 2 ≤ a)
  (h₁: a < b) :
  (a + b < a * b ) := by
  have h₂: a + b < b + b := by exact add_lt_add_right h₁ b
  have h₃: b + b ≤ a * b := by
    rw [← two_mul]
    exact mul_le_mul_right' h₀ b
  exact gt_of_ge_of_gt h₃ h₂


lemma imo_2022_p5_4_1
  (a b : ℕ)
  (h₀ : 2 ≤ a)
  -- (h₁ : a < b)
  (h₂ : a + b < b + b) :
  a + b < a * b := by
  have h₃: b + b ≤ a * b := by
    rw [← two_mul]
    exact mul_le_mul_right' h₀ b
  exact gt_of_ge_of_gt h₃ h₂


lemma imo_2022_p5_4_2
  (a b : ℕ)
  (h₀ : 2 ≤ a) :
  -- (h₁ : a < b)
  -- (h₂ : a + b < b + b) :
  b + b ≤ a * b := by
  rw [← two_mul]
  exact mul_le_mul_right' h₀ b


lemma imo_2022_p5_5
  (p: ℕ) :
  (Finset.Ico p (2 * p - 1)).prod (fun x => x + 1)
    = (Finset.range (p - 1)).prod (fun x => p + (x + 1)) := by
  rw [Finset.prod_Ico_eq_prod_range _ (p) (2 * p - 1)]
  have h₀: 2 * p - 1 - p = p - 1 := by omega
  rw [h₀]
  exact rfl


lemma imo_2022_p5_5_1
  (p : ℕ) :
  (Finset.prod (Finset.range (2 * p - 1 - p)) fun k => p + k + 1) =
    Finset.prod (Finset.range (p - 1)) fun x => p + (x + 1) := by
  have h₀: 2 * p - 1 - p = p - 1 := by omega
  rw [h₀]
  exact rfl


lemma imo_2022_p5_5_2
  (p : ℕ)
  (h₀ : 2 * p - 1 - p = p - 1) :
  (Finset.prod (Finset.range (2 * p - 1 - p)) fun k => p + k + 1) =
    Finset.prod (Finset.range (p - 1)) fun x => p + (x + 1) := by
  rw [h₀]
  exact rfl



lemma imo_2022_p5_6
  (p: ℕ)
  (hp: 2 ≤ p) :
  (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1)
      = (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x + 1)) := by
  refine Nat.le_induction ?_ ?_ p hp
  . norm_num
  . intros n hn2 h₀
    simp at *
    have hn: 0 < n := by exact lt_of_succ_lt hn2
    rw [← Nat.mul_factorial_pred hn, h₀]
    let f: (ℕ → ℕ) := fun (x : ℕ) => n - x
    have h₁: (Finset.range n).prod f =
        (Finset.range 1).prod f * (Finset.Ico 1 n).prod f := by
      exact (Finset.prod_range_mul_prod_Ico (fun k => n - k) hn).symm
    rw [h₁]
    have h₂: (Finset.range 1).prod f = n := by
      exact Finset.prod_range_one fun k => n - k
    rw [h₂]
    simp
    left
    rw [Finset.prod_Ico_eq_prod_range f 1 n]
    ring_nf
    exact rfl


lemma imo_2022_p5_6_1 :
  -- (p : ℕ)
  -- (hp : 2 ≤ p) :
  ∀ (n : ℕ),
    2 ≤ n →
      ((Finset.prod (Finset.range (n - 1)) fun x => x + 1) = Finset.prod (Finset.range (n - 1)) fun x => n - (x + 1)) →
        (Finset.prod (Finset.range (n + 1 - 1)) fun x => x + 1) =
          Finset.prod (Finset.range (n + 1 - 1)) fun x => n + 1 - (x + 1) := by
  intros n hn2 h₀
  simp at *
  have hn: 0 < n := by exact lt_of_succ_lt hn2
  rw [← Nat.mul_factorial_pred hn, h₀]
  let f: (ℕ → ℕ) := fun (x : ℕ) => n - x
  have h₁: (Finset.range n).prod f =
      (Finset.range 1).prod f * (Finset.Ico 1 n).prod f := by
    exact (Finset.prod_range_mul_prod_Ico (fun k => n - k) hn).symm
  rw [h₁]
  have h₂: (Finset.range 1).prod f = n := by
    exact Finset.prod_range_one fun k => n - k
  rw [h₂]
  simp
  left
  rw [Finset.prod_Ico_eq_prod_range f 1 n]
  ring_nf
  exact rfl


lemma imo_2022_p5_6_2
  -- (p : ℕ)
  -- (hp : 2 ≤ p)
  (n : ℕ)
  (hn2 : 2 ≤ n)
  (h₀ : (n - 1)! = Finset.prod (Finset.range (n - 1)) fun x => n - (x + 1)) :
  n ! = Finset.prod (Finset.range n) fun x => n - x := by
  have hn: 0 < n := by exact lt_of_succ_lt hn2
  rw [← Nat.mul_factorial_pred hn, h₀]
  let f: (ℕ → ℕ) := fun (x : ℕ) => n - x
  have h₁: (Finset.range n).prod f =
      (Finset.range 1).prod f * (Finset.Ico 1 n).prod f := by
    exact (Finset.prod_range_mul_prod_Ico (fun k => n - k) hn).symm
  rw [h₁]
  have h₂: (Finset.range 1).prod f = n := by
    exact Finset.prod_range_one fun k => n - k
  rw [h₂]
  simp
  left
  rw [Finset.prod_Ico_eq_prod_range f 1 n]
  ring_nf
  exact rfl


lemma imo_2022_p5_6_3
  -- (p : ℕ)
  -- (hp : 2 ≤ p)
  (n : ℕ)
  -- (hn2 : 2 ≤ n)
  -- (h₀ : (n - 1)! = Finset.prod (Finset.range (n - 1)) fun x => n - (x + 1))
  (hn : 0 < n) :
  n * (Finset.prod (Finset.range (n - 1)) fun x => n - (x + 1))
    = Finset.prod (Finset.range n) fun x => n - x := by
  let f: (ℕ → ℕ) := fun (x : ℕ) => n - x
  have h₁: (Finset.range n).prod f =
      (Finset.range 1).prod f * (Finset.Ico 1 n).prod f := by
    exact (Finset.prod_range_mul_prod_Ico (fun k => n - k) hn).symm
  rw [h₁]
  have h₂: (Finset.range 1).prod f = n := by
    exact Finset.prod_range_one fun k => n - k
  rw [h₂]
  simp
  left
  rw [Finset.prod_Ico_eq_prod_range f 1 n]
  ring_nf
  exact rfl


lemma imo_2022_p5_6_4
  -- (p : ℕ)
  -- (hp : 2 ≤ p)
  (n : ℕ)
  -- (hn2 : 2 ≤ n)
  -- (h₀ : (n - 1)! = Finset.prod (Finset.range (n - 1)) fun x => n - (x + 1))
  (hn : 0 < n) :
  -- (f : ℕ → ℕ) :
  -- (hf: f = fun x => n - x) :
  n * (Finset.prod (Finset.range (n - 1)) fun x => n - (x + 1))
    = Finset.prod (Finset.range n) fun x => n - x := by
  have h₁: (Finset.range n).prod (fun x => n - x) =
      (Finset.range 1).prod (fun x => n - x) * (Finset.Ico 1 n).prod (fun x => n - x) := by
    exact (Finset.prod_range_mul_prod_Ico (fun k => n - k) hn).symm
  rw [h₁]
  have h₂: (Finset.range 1).prod (fun x => n - x) = n := by
    -- rw [hf]
    exact Finset.prod_range_one fun k => n - k
  rw [h₂]
  simp
  left
  rw [Finset.prod_Ico_eq_prod_range (fun x => n - x) 1 n]
  ring_nf


lemma imo_2022_p5_6_5
  -- (p : ℕ)
  -- (hp : 2 ≤ p)
  (n : ℕ)
  -- (hn2 : 2 ≤ n)
  -- (h₀ : (n - 1)! = Finset.prod (Finset.range (n - 1)) fun x => n - (x + 1))
  -- (hn : 0 < n)
  (f : ℕ → ℕ)
  (hf: f = fun x => n - x)
  (h₁ : Finset.prod (Finset.range n) f = Finset.prod (Finset.range 1) f * Finset.prod (Finset.Ico 1 n) f) :
  n * (Finset.prod (Finset.range (n - 1)) fun x => n - (x + 1))
    = Finset.prod (Finset.range n) fun x => n - x := by
  rw [← hf, h₁]
  have h₂: (Finset.range 1).prod f = n := by
    rw [hf]
    exact Finset.prod_range_one fun k => n - k
  rw [h₂]
  simp
  left
  rw [Finset.prod_Ico_eq_prod_range f 1 n]
  ring_nf
  rw [hf]


lemma imo_2022_p5_6_6
  -- (p : ℕ)
  -- (hp : 2 ≤ p)
  (n : ℕ)
  -- (hn2 : 2 ≤ n)
  -- (h₀ : (n - 1)! = Finset.prod (Finset.range (n - 1)) fun x => n - (x + 1))
  -- (hn : 0 < n)
  (f : ℕ → ℕ)
  (hf: f = fun x => n - x)
  -- (h₁ : Finset.prod (Finset.range n) f = Finset.prod (Finset.range 1) f * Finset.prod (Finset.Ico 1 n) f)
  (h₂ : Finset.prod (Finset.range 1) f = n) :
  n * (Finset.prod (Finset.range (n - 1)) fun x => n - (x + 1)) =
    Finset.prod (Finset.range 1) f * Finset.prod (Finset.Ico 1 n) f := by
  rw [h₂]
  simp
  left
  rw [Finset.prod_Ico_eq_prod_range f 1 n]
  ring_nf
  rw [hf]


lemma imo_2022_p5_6_7
  -- (p : ℕ)
  -- (hp : 2 ≤ p)
  (n : ℕ)
  -- (hn2 : 2 ≤ n)
  -- (h₀ : (n - 1)! = Finset.prod (Finset.range (n - 1)) fun x => n - (x + 1))
  -- (hn : 0 < n)
  (f : ℕ → ℕ)
  (hf: f = fun x => n - x) :
  -- (h₁ : Finset.prod (Finset.range n) f = Finset.prod (Finset.range 1) f * Finset.prod (Finset.Ico 1 n) f)
  -- (h₂ : Finset.prod (Finset.range 1) f = n) :
  (Finset.prod (Finset.range (n - 1)) fun x => n - (x + 1)) =
    Finset.prod (Finset.Ico 1 n) f ∨ n = 0 := by
  left
  rw [Finset.prod_Ico_eq_prod_range f 1 n]
  ring_nf
  rw [hf]


lemma imo_2022_p5_7
  (b p: ℕ)
  -- (h₀: 0 < b)
  (hp: Nat.Prime p)
  (hb2p: b < 2 * p) :
  b.factorial + p < p ^ (2 * p) := by
  have h₁: b.factorial ≤ (2*p - 1).factorial := by
    refine factorial_le ?_
    exact le_pred_of_lt hb2p
  have gp: 2 ≤ p := by exact Prime.two_le hp
  have gp1: (p - 1) + 1 = p := by
    refine Nat.sub_add_cancel ?_
    exact one_le_of_lt gp
  let f: (ℕ → ℕ) := (fun (x : ℕ) => x + 1)
  have h₂: (Finset.range (2 * p - 1)).prod f =
      (Finset.range (p - 1)).prod (fun (x : ℕ) => p^2 - (x+1)^2) * p := by
    -- break the prod into three segments rang(p-1) + p + (p+1) until 2p-1
    have g₀: (Finset.range (2 * p - 1)).prod f = (Finset.range ((p - 1) + 1)).prod f
           * (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod f := by
      symm
      refine Finset.prod_range_mul_prod_Ico f ?_
      rw [gp1]
      have gg₀: p + 2 - 1 ≤ 2 * p - 1 := by
        refine Nat.sub_le_sub_right ?_ 1
        rw [add_comm]
        exact add_le_mul (by norm_num) gp
      exact le_of_lt gg₀
    have g₁: (Finset.range ((p - 1) + 1)).prod (fun (x : ℕ) => x + 1) =
       (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1) * ((p - 1) + 1) := by
      exact Finset.prod_range_succ _ (p - 1)
    rw [g₁] at g₀
    nth_rewrite 2 [mul_comm] at g₀
    rw [← mul_assoc] at g₀
    rw [gp1] at g₀ g₁
    have g₂: (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod (fun (x : ℕ) => x + 1)
              = (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1)) := by
      rw [gp1]
      exact imo_2022_p5_5 p
    have g₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1)
              = (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1)) := by
      exact imo_2022_p5_6 p gp
    rw [gp1] at g₂
    rw [g₂,g₃] at g₀
    have g₄: (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1))
      * (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1))
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
      symm
      refine Finset.prod_mul_distrib
    have g₅: (fun (x : ℕ) => p ^ 2 - (x+1) ^ 2) = (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
      ext1 x
      exact Nat.sq_sub_sq p (x + 1)
    rw [g₄,← g₅] at g₀
    exact g₀
  have h₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => p^2 - (x+1)^2) * p
      ≤ (p^2)^(Finset.range (p - 1)).card * p := by
    refine Nat.mul_le_mul_right ?_ ?_
    refine Finset.prod_le_pow_card (Finset.range (p - 1)) ?_ (p^2) ?_
    intros x _
    exact (p ^ 2).sub_le ((x + 1) ^ 2)
  simp at *
  have h₄: b.factorial + p ≤ (p ^ 2) ^ (p - 1) * p + p := by
    refine add_le_add_right ?_ p
    refine le_trans ?_ h₃
    rw [← h₂]
    rw [Finset.prod_range_add_one_eq_factorial]
    exact h₁
  have h₅: b.factorial + p < (p ^ 2) ^ (p - 1) * p * p := by
    refine lt_of_le_of_lt h₄ ?_
    rw [add_comm]
    nth_rewrite 2 [mul_comm]
    refine imo_2022_p5_4 p ((p ^ 2) ^ (p - 1) * p) gp ?_
    refine lt_mul_left (by linarith) ?_
    rw [← pow_mul]
    refine Nat.one_lt_pow ?_ (Nat.lt_of_succ_le gp)
    refine Nat.mul_ne_zero (by norm_num) ?_
    exact Nat.sub_ne_zero_iff_lt.mpr gp
  rw [mul_assoc _ p p, ← pow_two p] at h₅
  rw [← Nat.pow_succ, succ_eq_add_one, gp1] at h₅
  rw [Nat.pow_mul]
  exact h₅


lemma imo_2022_p5_7_1
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  (hb2p : b < 2 * p) :
  b ! ≤ (2 * p - 1)! := by
  refine factorial_le ?_
  exact le_pred_of_lt hb2p


lemma imo_2022_p5_7_2
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p) :
  b ! + p < p ^ (2 * p) := by
  have gp1: (p - 1) + 1 = p := by
    refine Nat.sub_add_cancel ?_
    exact one_le_of_lt gp
  let f: (ℕ → ℕ) := (fun (x : ℕ) => x + 1)
  have h₂: (Finset.range (2 * p - 1)).prod f =
      (Finset.range (p - 1)).prod (fun (x : ℕ) => p^2 - (x+1)^2) * p := by
    -- break the prod into three segments rang(p-1) + p + (p+1) until 2p-1
    have g₀: (Finset.range (2 * p - 1)).prod f = (Finset.range ((p - 1) + 1)).prod f
           * (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod f := by
      symm
      refine Finset.prod_range_mul_prod_Ico f ?_
      rw [gp1]
      have gg₀: p + 2 - 1 ≤ 2 * p - 1 := by
        refine Nat.sub_le_sub_right ?_ 1
        rw [add_comm]
        exact add_le_mul (by norm_num) gp
      exact le_of_lt gg₀
    have g₁: (Finset.range ((p - 1) + 1)).prod (fun (x : ℕ) => x + 1) =
       (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1) * ((p - 1) + 1) := by
      exact Finset.prod_range_succ _ (p - 1)
    rw [g₁] at g₀
    nth_rewrite 2 [mul_comm] at g₀
    rw [← mul_assoc] at g₀
    rw [gp1] at g₀ g₁
    have g₂: (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod (fun (x : ℕ) => x + 1)
              = (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1)) := by
      rw [gp1]
      exact imo_2022_p5_5 p
    have g₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1)
              = (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1)) := by
      exact imo_2022_p5_6 p gp
    rw [gp1] at g₂
    rw [g₂,g₃] at g₀
    have g₄: (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1))
      * (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1))
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
      symm
      refine Finset.prod_mul_distrib
    have g₅: (fun (x : ℕ) => p ^ 2 - (x+1) ^ 2) = (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
      ext1 x
      exact Nat.sq_sub_sq p (x + 1)
    rw [g₄,← g₅] at g₀
    exact g₀
  have h₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => p^2 - (x+1)^2) * p
      ≤ (p^2)^(Finset.range (p - 1)).card * p := by
    refine Nat.mul_le_mul_right ?_ ?_
    refine Finset.prod_le_pow_card (Finset.range (p - 1)) ?_ (p^2) ?_
    intros x _
    exact (p ^ 2).sub_le ((x + 1) ^ 2)
  simp at *
  have h₄: b.factorial + p ≤ (p ^ 2) ^ (p - 1) * p + p := by
    refine add_le_add_right ?_ p
    refine le_trans ?_ h₃
    rw [← h₂]
    rw [Finset.prod_range_add_one_eq_factorial]
    exact h₁
  have h₅: b.factorial + p < (p ^ 2) ^ (p - 1) * p * p := by
    refine lt_of_le_of_lt h₄ ?_
    rw [add_comm]
    nth_rewrite 2 [mul_comm]
    refine imo_2022_p5_4 p ((p ^ 2) ^ (p - 1) * p) gp ?_
    refine lt_mul_left (by linarith) ?_
    rw [← pow_mul]
    refine Nat.one_lt_pow ?_ (Nat.lt_of_succ_le gp)
    refine Nat.mul_ne_zero (by norm_num) ?_
    exact Nat.sub_ne_zero_iff_lt.mpr gp
  rw [mul_assoc _ p p, ← pow_two p] at h₅
  rw [← Nat.pow_succ, succ_eq_add_one, gp1] at h₅
  rw [Nat.pow_mul]
  exact h₅


lemma imo_2022_p5_7_3
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  (hf : f = fun x => x + 1) :
  b ! + p < p ^ (2 * p) := by
  have h₂: (Finset.range (2 * p - 1)).prod f =
      (Finset.range (p - 1)).prod (fun (x : ℕ) => p^2 - (x+1)^2) * p := by
    -- important
    -- break the prod into three segments rang(p-1) + p + (p+1) until 2p-1
    have g₀: (Finset.range (2 * p - 1)).prod f = (Finset.range ((p - 1) + 1)).prod f
           * (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod f := by
      symm
      refine Finset.prod_range_mul_prod_Ico f ?_
      rw [gp1]
      have gg₀: p + 2 - 1 ≤ 2 * p - 1 := by
        refine Nat.sub_le_sub_right ?_ 1
        rw [add_comm]
        exact add_le_mul (by norm_num) gp
      exact le_of_lt gg₀
    have g₁: (Finset.range ((p - 1) + 1)).prod (fun (x : ℕ) => x + 1) =
       (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1) * ((p - 1) + 1) := by
      exact Finset.prod_range_succ _ (p - 1)
    rw [hf, g₁] at g₀
    nth_rewrite 2 [mul_comm] at g₀
    rw [← mul_assoc] at g₀
    rw [gp1] at g₀ g₁
    have g₂: (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod (fun (x : ℕ) => x + 1)
              = (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1)) := by
      rw [gp1]
      exact imo_2022_p5_5 p
    have g₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1)
              = (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1)) := by
      exact imo_2022_p5_6 p gp
    rw [gp1] at g₂
    rw [g₂,g₃] at g₀
    have g₄: (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1))
      * (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1))
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
      symm
      refine Finset.prod_mul_distrib
    have g₅: (fun (x : ℕ) => p ^ 2 - (x+1) ^ 2) = (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
      ext1 x
      exact Nat.sq_sub_sq p (x + 1)
    rw [g₄,← g₅, ← hf] at g₀
    exact g₀
  have h₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => p^2 - (x+1)^2) * p
      ≤ (p^2)^(Finset.range (p - 1)).card * p := by
    refine Nat.mul_le_mul_right ?_ ?_
    refine Finset.prod_le_pow_card (Finset.range (p - 1)) ?_ (p^2) ?_
    intros x _
    exact (p ^ 2).sub_le ((x + 1) ^ 2)
  simp at *
  have h₄: b.factorial + p ≤ (p ^ 2) ^ (p - 1) * p + p := by
    refine add_le_add_right ?_ p
    refine le_trans ?_ h₃
    rw [← h₂, hf]
    rw [Finset.prod_range_add_one_eq_factorial]
    exact h₁
  have h₅: b.factorial + p < (p ^ 2) ^ (p - 1) * p * p := by
    refine lt_of_le_of_lt h₄ ?_
    rw [add_comm]
    nth_rewrite 2 [mul_comm]
    refine imo_2022_p5_4 p ((p ^ 2) ^ (p - 1) * p) gp ?_
    refine lt_mul_left (by linarith) ?_
    rw [← pow_mul]
    refine Nat.one_lt_pow ?_ (Nat.lt_of_succ_le gp)
    refine Nat.mul_ne_zero (by norm_num) ?_
    exact Nat.sub_ne_zero_iff_lt.mpr gp
  rw [mul_assoc _ p p, ← pow_two p] at h₅
  rw [← Nat.pow_succ, succ_eq_add_one, gp1] at h₅
  rw [Nat.pow_mul]
  exact h₅


lemma imo_2022_p5_7_4
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  (hf : f = fun x => x + 1) :
  Finset.prod (Finset.range (2 * p - 1)) f =
    (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p := by
  have g₀: (Finset.range (2 * p - 1)).prod f = (Finset.range ((p - 1) + 1)).prod f
          * (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod f := by
    symm
    refine Finset.prod_range_mul_prod_Ico f ?_
    rw [gp1]
    have gg₀: p + 2 - 1 ≤ 2 * p - 1 := by
      refine Nat.sub_le_sub_right ?_ 1
      rw [add_comm]
      exact add_le_mul (by norm_num) gp
    exact le_of_lt gg₀
  have g₁: (Finset.range ((p - 1) + 1)).prod (fun (x : ℕ) => x + 1) =
      (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1) * ((p - 1) + 1) := by
    exact Finset.prod_range_succ _ (p - 1)
  rw [hf, g₁] at g₀
  nth_rewrite 2 [mul_comm] at g₀
  rw [← mul_assoc] at g₀
  rw [gp1] at g₀ g₁
  have g₂: (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod (fun (x : ℕ) => x + 1)
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1)) := by
    rw [gp1]
    exact imo_2022_p5_5 p
  have g₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1)
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1)) := by
    exact imo_2022_p5_6 p gp
  rw [gp1] at g₂
  rw [g₂,g₃] at g₀
  have g₄: (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1))
    * (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1))
          = (Finset.range (p - 1)).prod (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
    symm
    refine Finset.prod_mul_distrib
  have g₅: (fun (x : ℕ) => p ^ 2 - (x+1) ^ 2) = (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
    ext1 x
    exact Nat.sq_sub_sq p (x + 1)
  rw [g₄,← g₅, ← hf] at g₀
  exact g₀


lemma imo_2022_p5_7_5
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ) :
  -- (hf : f = fun x => x + 1) :
  Finset.prod (Finset.range (2 * p - 1)) f =
    Finset.prod (Finset.range (p - 1 + 1)) f * Finset.prod (Finset.Ico (p - 1 + 1) (2 * p - 1)) f := by
  symm
  refine Finset.prod_range_mul_prod_Ico f ?_
  rw [gp1]
  have gg₀: p + 2 - 1 ≤ 2 * p - 1 := by
    refine Nat.sub_le_sub_right ?_ 1
    rw [add_comm]
    exact add_le_mul (by norm_num) gp
  exact le_of_lt gg₀


lemma imo_2022_p5_7_6
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p) :
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1) :
  p - 1 + 1 ≤ 2 * p - 1 := by
  have h₂: p - 1 + 1 < p + 2 - 1 := by
    omega
  refine le_trans (le_of_lt h₂) ?_
  refine Nat.sub_le_sub_right ?_ 1
  rw [add_comm]
  exact add_le_mul (by norm_num) gp


lemma imo_2022_p5_7_7
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p) :
  -- (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1) :
  p + 2 - 1 ≤ 2 * p - 1 := by
  refine Nat.sub_le_sub_right ?_ 1
  rw [add_comm]
  exact add_le_mul (by norm_num) gp


lemma imo_2022_p5_7_8
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p) :
  -- (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1) :
  p + 2 ≤ 2 * p := by
  rw [add_comm]
  exact add_le_mul (by norm_num) gp


lemma imo_2022_p5_7_9
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  (hf : f = fun x => x + 1)
  (g₀ : Finset.prod (Finset.range (2 * p - 1)) f =
    Finset.prod (Finset.range (p - 1 + 1)) f * Finset.prod (Finset.Ico (p - 1 + 1) (2 * p - 1)) f) :
  Finset.prod (Finset.range (2 * p - 1)) f =
    (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p := by
  have g₁: (Finset.range ((p - 1) + 1)).prod (fun (x : ℕ) => x + 1) =
      (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1) * ((p - 1) + 1) := by
    exact Finset.prod_range_succ _ (p - 1)
  rw [hf, g₁] at g₀
  nth_rewrite 2 [mul_comm] at g₀
  rw [← mul_assoc] at g₀
  rw [gp1] at g₀ g₁
  have g₂: (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod (fun (x : ℕ) => x + 1)
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1)) := by
    rw [gp1]
    exact imo_2022_p5_5 p
  have g₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1)
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1)) := by
    exact imo_2022_p5_6 p gp
  rw [gp1] at g₂
  rw [g₂,g₃] at g₀
  have g₄: (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1))
    * (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1))
          = (Finset.range (p - 1)).prod (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
    symm
    refine Finset.prod_mul_distrib
  have g₅: (fun (x : ℕ) => p ^ 2 - (x+1) ^ 2) = (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
    ext1 x
    exact Nat.sq_sub_sq p (x + 1)
  rw [g₄,← g₅, ← hf] at g₀
  exact g₀


lemma imo_2022_p5_7_10
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  (hf : f = fun x => x + 1)
  (g₀ : Finset.prod (Finset.range (2 * p - 1)) f =
    Finset.prod (Finset.range (p - 1 + 1)) f * Finset.prod (Finset.Ico (p - 1 + 1) (2 * p - 1)) f)
  (g₁ : (Finset.prod (Finset.range (p - 1 + 1)) fun x => x + 1) =
    (Finset.prod (Finset.range (p - 1)) fun x => x + 1) * (p - 1 + 1)) :
  Finset.prod (Finset.range (2 * p - 1)) f =
    (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p := by
  rw [hf, g₁] at g₀
  nth_rewrite 2 [mul_comm] at g₀
  rw [← mul_assoc] at g₀
  rw [gp1] at g₀ g₁
  have g₂: (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod (fun (x : ℕ) => x + 1)
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1)) := by
    rw [gp1]
    exact imo_2022_p5_5 p
  have g₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1)
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1)) := by
    exact imo_2022_p5_6 p gp
  rw [gp1] at g₂
  rw [g₂,g₃] at g₀
  have g₄: (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1))
    * (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1))
          = (Finset.range (p - 1)).prod (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
    symm
    refine Finset.prod_mul_distrib
  have g₅: (fun (x : ℕ) => p ^ 2 - (x+1) ^ 2) = (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
    ext1 x
    exact Nat.sq_sub_sq p (x + 1)
  rw [g₄,← g₅, ← hf] at g₀
  exact g₀


lemma imo_2022_p5_7_11
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  (hf : f = fun x => x + 1)
  (g₀ : Finset.prod (Finset.range (2 * p - 1)) f =
    (Finset.prod (Finset.Ico p (2 * p - 1)) f * Finset.prod (Finset.range (p - 1)) fun x => x + 1) * p)
  (g₁ : (Finset.prod (Finset.range p) fun x => x + 1) =
    (Finset.prod (Finset.range (p - 1)) fun x => x + 1) * p) :
  Finset.prod (Finset.range (2 * p - 1)) f =
    (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p := by
  have g₂: (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod (fun (x : ℕ) => x + 1)
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1)) := by
    rw [gp1]
    exact imo_2022_p5_5 p
  have g₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1)
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1)) := by
    exact imo_2022_p5_6 p gp
  rw [gp1] at g₂
  rw [hf, g₂, g₃] at g₀
  have g₄: (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1))
    * (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1))
          = (Finset.range (p - 1)).prod (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
    symm
    refine Finset.prod_mul_distrib
  have g₅: (fun (x : ℕ) => p ^ 2 - (x+1) ^ 2) = (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
    ext1 x
    exact Nat.sq_sub_sq p (x + 1)
  rw [g₄,← g₅, ← hf] at g₀
  exact g₀


lemma imo_2022_p5_7_12
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  (hf : f = fun x => x + 1)
  (g₀ : Finset.prod (Finset.range (2 * p - 1)) f =
    Finset.prod (Finset.range (p - 1 + 1)) f * Finset.prod (Finset.Ico (p - 1 + 1) (2 * p - 1)) f)
  (g₁ : (Finset.prod (Finset.range (p - 1 + 1)) fun x => x + 1) =
    (Finset.prod (Finset.range (p - 1)) fun x => x + 1) * (p - 1 + 1)) :
  Finset.prod (Finset.range (2 * p - 1)) f =
    (Finset.prod (Finset.Ico p (2 * p - 1)) f *
      Finset.prod (Finset.range (p - 1)) fun x => x + 1) * p := by
  rw [hf, g₁] at g₀
  nth_rewrite 2 [mul_comm] at g₀
  rw [← mul_assoc] at g₀
  rw [gp1] at g₀ g₁
  rw [hf, g₀]


lemma imo_2022_p5_7_13
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  (hf : f = fun x => x + 1)
  (g₀ : Finset.prod (Finset.range (2 * p - 1)) f =
    (Finset.prod (Finset.Ico p (2 * p - 1)) f * Finset.prod (Finset.range (p - 1)) fun x => x + 1) * p)
  (g₁ : (Finset.prod (Finset.range p) fun x => x + 1) = (Finset.prod (Finset.range (p - 1)) fun x => x + 1) * p)
  (g₂ : (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod (fun (x : ℕ) => x + 1)
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1)))
  (g₃ : (Finset.prod (Finset.range (p - 1)) fun x => x + 1) = Finset.prod (Finset.range (p - 1)) fun x => p - (x + 1)) :
  Finset.prod (Finset.range (2 * p - 1)) f =
    (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p := by
  rw [gp1] at g₂
  rw [hf, g₂, g₃] at g₀
  have g₄: (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1))
    * (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1))
          = (Finset.range (p - 1)).prod (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
    symm
    refine Finset.prod_mul_distrib
  have g₅: (fun (x : ℕ) => p ^ 2 - (x+1) ^ 2) = (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
    ext1 x
    exact Nat.sq_sub_sq p (x + 1)
  rw [g₄,← g₅, ← hf] at g₀
  exact g₀


lemma imo_2022_p5_7_14
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  -- (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  (g₀ : Finset.prod (Finset.range (2 * p - 1)) f =
    ((Finset.prod (Finset.range (p - 1)) fun x => p + (x + 1)) *
        Finset.prod (Finset.range (p - 1)) fun x => p - (x + 1)) * p)
  (g₁ : (Finset.prod (Finset.range p) fun x => x + 1) = (Finset.prod (Finset.range (p - 1)) fun x => x + 1) * p)
  (g₂ : (Finset.prod (Finset.Ico p (2 * p - 1)) fun x => x + 1) = Finset.prod (Finset.range (p - 1)) fun x => p + (x + 1))
  (g₃ : (Finset.prod (Finset.range (p - 1)) fun x => x + 1) = Finset.prod (Finset.range (p - 1)) fun x => p - (x + 1))
  (g₄ : ((Finset.prod (Finset.range (p - 1)) fun x => p + (x + 1)) * Finset.prod (Finset.range (p - 1)) fun x => p - (x + 1)) =
    Finset.prod (Finset.range (p - 1)) fun x => (p + (x + 1)) * (p - (x + 1))) :
  Finset.prod (Finset.range (2 * p - 1)) f =
    (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p := by
  have g₅: (fun (x : ℕ) => p ^ 2 - (x+1) ^ 2) = (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
    ext1 x
    exact Nat.sq_sub_sq p (x + 1)
  rw [g₄,← g₅] at g₀
  exact g₀


lemma imo_2022_p5_7_15
  -- (b : ℕ)
  (p : ℕ) :
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  -- (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (g₀ : Finset.prod (Finset.range (2 * p - 1)) f =
  --   ((Finset.prod (Finset.range (p - 1)) fun x => p + (x + 1)) *
  --       Finset.prod (Finset.range (p - 1)) fun x => p - (x + 1)) * p)
  -- (g₁ : (Finset.prod (Finset.range p) fun x => x + 1) = (Finset.prod (Finset.range (p - 1)) fun x => x + 1) * p)
  -- (g₂ : (Finset.prod (Finset.Ico p (2 * p - 1)) fun x => x + 1) = Finset.prod (Finset.range (p - 1)) fun x => p + (x + 1))
  -- (g₃ : (Finset.prod (Finset.range (p - 1)) fun x => x + 1) = Finset.prod (Finset.range (p - 1)) fun x => p - (x + 1))
  -- (g₄ : ((Finset.prod (Finset.range (p - 1)) fun x => p + (x + 1)) * Finset.prod (Finset.range (p - 1)) fun x => p - (x + 1)) =
  --   Finset.prod (Finset.range (p - 1)) fun x => (p + (x + 1)) * (p - (x + 1))) :
  (fun x => p ^ 2 - (x + 1) ^ 2) = fun x => (p + (x + 1)) * (p - (x + 1)) := by
  ext1 x
  exact Nat.sq_sub_sq p (x + 1)


lemma imo_2022_p5_7_16
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  -- (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  (g₀ : Finset.prod (Finset.range (2 * p - 1)) f =
    ((Finset.prod (Finset.range (p - 1)) fun x => p + (x + 1)) *
        Finset.prod (Finset.range (p - 1)) fun x => p - (x + 1)) * p)
  (g₁ : (Finset.prod (Finset.range p) fun x => x + 1) = (Finset.prod (Finset.range (p - 1)) fun x => x + 1) * p)
  (g₂ : (Finset.prod (Finset.Ico p (2 * p - 1)) fun x => x + 1) = Finset.prod (Finset.range (p - 1)) fun x => p + (x + 1))
  (g₃ : (Finset.prod (Finset.range (p - 1)) fun x => x + 1) = Finset.prod (Finset.range (p - 1)) fun x => p - (x + 1))
  (g₄ : ((Finset.prod (Finset.range (p - 1)) fun x => p + (x + 1)) * Finset.prod (Finset.range (p - 1)) fun x => p - (x + 1)) =
    Finset.prod (Finset.range (p - 1)) fun x => (p + (x + 1)) * (p - (x + 1)))
  (g₅ : (fun x => p ^ 2 - (x + 1) ^ 2) = fun x => (p + (x + 1)) * (p - (x + 1))) :
  Finset.prod (Finset.range (2 * p - 1)) f =
    (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p := by
  rw [g₄,← g₅] at g₀
  exact g₀


lemma imo_2022_p5_7_17
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  (hf : f = fun x => x + 1)
  (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p) :
  b ! + p < p ^ (2 * p) := by
  have h₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => p^2 - (x+1)^2) * p
      ≤ (p^2)^(Finset.range (p - 1)).card * p := by
    refine Nat.mul_le_mul_right ?_ ?_
    refine Finset.prod_le_pow_card (Finset.range (p - 1)) ?_ (p^2) ?_
    intros x _
    exact (p ^ 2).sub_le ((x + 1) ^ 2)
  simp at *
  have h₄: b.factorial + p ≤ (p ^ 2) ^ (p - 1) * p + p := by
    refine add_le_add_right ?_ p
    refine le_trans ?_ h₃
    rw [← h₂, hf]
    rw [Finset.prod_range_add_one_eq_factorial]
    exact h₁
  have h₅: b.factorial + p < (p ^ 2) ^ (p - 1) * p * p := by
    refine lt_of_le_of_lt h₄ ?_
    rw [add_comm]
    nth_rewrite 2 [mul_comm]
    refine imo_2022_p5_4 p ((p ^ 2) ^ (p - 1) * p) gp ?_
    refine lt_mul_left (by linarith) ?_
    rw [← pow_mul]
    refine Nat.one_lt_pow ?_ (Nat.lt_of_succ_le gp)
    refine Nat.mul_ne_zero (by norm_num) ?_
    exact Nat.sub_ne_zero_iff_lt.mpr gp
  rw [mul_assoc _ p p, ← pow_two p] at h₅
  rw [← Nat.pow_succ, succ_eq_add_one, gp1] at h₅
  rw [Nat.pow_mul]
  exact h₅


lemma imo_2022_p5_7_18
  -- (b : ℕ)
  (p : ℕ) :
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  -- (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p) :
  (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p
    ≤ (p ^ 2) ^ (Finset.range (p - 1)).card * p := by
  refine Nat.mul_le_mul_right ?_ ?_
  refine Finset.prod_le_pow_card (Finset.range (p - 1)) ?_ (p^2) ?_
  intros x _
  exact (p ^ 2).sub_le ((x + 1) ^ 2)


lemma imo_2022_p5_7_19
  -- (b : ℕ)
  (p : ℕ) :
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  -- (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p) :
  (Finset.prod (Finset.range (p - 1)) fun x => (p ^ 2 - (x + 1) ^ 2)) ≤
    (p ^ 2) ^ (Finset.range (p - 1)).card := by
  refine Finset.prod_le_pow_card (Finset.range (p - 1)) ?_ (p^2) ?_
  intros x _
  exact (p ^ 2).sub_le ((x + 1) ^ 2)


lemma imo_2022_p5_7_20
  -- (b : ℕ)
  (p : ℕ) :
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  -- (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p) :
  ∀ x ∈ Finset.range (p - 1), p ^ 2 - (x + 1) ^ 2 ≤ p ^ 2 := by
  intros x _
  exact (p ^ 2).sub_le ((x + 1) ^ 2)


lemma imo_2022_p5_7_21
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  (hf : f = fun x => x + 1)
  (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (Finset.range (p - 1)).card * p) :
  b ! + p < p ^ (2 * p) := by
  simp at *
  have h₄: b.factorial + p ≤ (p ^ 2) ^ (p - 1) * p + p := by
    refine add_le_add_right ?_ p
    refine le_trans ?_ h₃
    rw [← h₂, hf]
    rw [Finset.prod_range_add_one_eq_factorial]
    exact h₁
  have h₅: b.factorial + p < (p ^ 2) ^ (p - 1) * p * p := by
    refine lt_of_le_of_lt h₄ ?_
    rw [add_comm]
    nth_rewrite 2 [mul_comm]
    refine imo_2022_p5_4 p ((p ^ 2) ^ (p - 1) * p) gp ?_
    refine lt_mul_left (by linarith) ?_
    rw [← pow_mul]
    refine Nat.one_lt_pow ?_ (Nat.lt_of_succ_le gp)
    refine Nat.mul_ne_zero (by norm_num) ?_
    exact Nat.sub_ne_zero_iff_lt.mpr gp
  rw [mul_assoc _ p p, ← pow_two p] at h₅
  rw [← Nat.pow_succ, succ_eq_add_one, gp1] at h₅
  rw [Nat.pow_mul]
  exact h₅


lemma imo_2022_p5_7_22
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  -- (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  (hf : f = fun x => x + 1)
  (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (p - 1) * p) :
  b ! + p ≤ (p ^ 2) ^ (p - 1) * p + p := by
  refine add_le_add_right ?_ p
  refine le_trans ?_ h₃
  rw [← h₂, hf]
  rw [Finset.prod_range_add_one_eq_factorial]
  exact h₁


lemma imo_2022_p5_7_23
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  -- (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  (hf : f = fun x => x + 1)
  (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (p - 1) * p) :
  b ! ≤ (p ^ 2) ^ (p - 1) * p := by
  refine le_trans ?_ h₃
  rw [← h₂, hf]
  rw [Finset.prod_range_add_one_eq_factorial]
  exact h₁


lemma imo_2022_p5_7_24
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  -- (gp1 : p - 1 + 1 = p)
  (f : ℕ → ℕ)
  (hf : f = fun x => x + 1) :
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  -- (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (p - 1) * p) :
  b ! ≤ Finset.prod (Finset.range (2 * p - 1)) f := by
  rw [hf]
  rw [Finset.prod_range_add_one_eq_factorial]
  exact h₁


lemma imo_2022_p5_7_25
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  -- (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (p - 1) * p)
  (h₄ : b ! + p ≤ (p ^ 2) ^ (p - 1) * p + p) :
  b ! + p < p ^ (2 * p) := by
  have h₅: b.factorial + p < (p ^ 2) ^ (p - 1) * p * p := by
    refine lt_of_le_of_lt h₄ ?_
    rw [add_comm]
    nth_rewrite 2 [mul_comm]
    refine imo_2022_p5_4 p ((p ^ 2) ^ (p - 1) * p) gp ?_
    refine lt_mul_left (by linarith) ?_
    rw [← pow_mul]
    refine Nat.one_lt_pow ?_ (Nat.lt_of_succ_le gp)
    refine Nat.mul_ne_zero (by norm_num) ?_
    exact Nat.sub_ne_zero_iff_lt.mpr gp
  rw [mul_assoc _ p p, ← pow_two p] at h₅
  rw [← Nat.pow_succ, succ_eq_add_one, gp1] at h₅
  rw [Nat.pow_mul]
  exact h₅


lemma imo_2022_p5_7_26
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p)
  -- (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  -- (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (p - 1) * p)
  (h₄ : b ! + p ≤ (p ^ 2) ^ (p - 1) * p + p) :
  b ! + p < (p ^ 2) ^ (p - 1) * p * p := by
  refine lt_of_le_of_lt h₄ ?_
  rw [add_comm]
  nth_rewrite 2 [mul_comm]
  refine imo_2022_p5_4 p ((p ^ 2) ^ (p - 1) * p) gp ?_
  refine lt_mul_left (by linarith) ?_
  rw [← pow_mul]
  refine Nat.one_lt_pow ?_ (Nat.lt_of_succ_le gp)
  refine Nat.mul_ne_zero (by norm_num) ?_
  exact Nat.sub_ne_zero_iff_lt.mpr gp


lemma imo_2022_p5_7_27
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p) :
  -- (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  -- (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (p - 1) * p)
  -- (h₄ : b ! + p ≤ (p ^ 2) ^ (p - 1) * p + p) :
  (p ^ 2) ^ (p - 1) * p + p < (p ^ 2) ^ (p - 1) * p * p := by
  rw [add_comm]
  nth_rewrite 2 [mul_comm]
  refine imo_2022_p5_4 p ((p ^ 2) ^ (p - 1) * p) gp ?_
  refine lt_mul_left (by linarith) ?_
  rw [← pow_mul]
  refine Nat.one_lt_pow ?_ (Nat.lt_of_succ_le gp)
  refine Nat.mul_ne_zero (by norm_num) ?_
  exact Nat.sub_ne_zero_iff_lt.mpr gp


lemma imo_2022_p5_7_28
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p) :
  -- (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  -- (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (p - 1) * p)
  -- (h₄ : b ! + p ≤ (p ^ 2) ^ (p - 1) * p + p) :
  p < (p ^ 2) ^ (p - 1) * p := by
  refine lt_mul_left (by linarith) ?_
  rw [← pow_mul]
  refine Nat.one_lt_pow ?_ (Nat.lt_of_succ_le gp)
  refine Nat.mul_ne_zero (by norm_num) ?_
  exact Nat.sub_ne_zero_iff_lt.mpr gp


lemma imo_2022_p5_7_29
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p) :
  -- (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  -- (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (p - 1) * p)
  -- (h₄ : b ! + p ≤ (p ^ 2) ^ (p - 1) * p + p) :
  1 < p ^ (2 * (p - 1)) := by
  refine Nat.one_lt_pow ?_ (Nat.lt_of_succ_le gp)
  refine Nat.mul_ne_zero (by norm_num) ?_
  exact Nat.sub_ne_zero_iff_lt.mpr gp


lemma imo_2022_p5_7_30
  -- (b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  (gp : 2 ≤ p) :
  -- (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  -- (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (p - 1) * p)
  -- (h₄ : b ! + p ≤ (p ^ 2) ^ (p - 1) * p + p) :
  2 * (p - 1) ≠ 0 := by
  refine Nat.mul_ne_zero (by norm_num) ?_
  exact Nat.sub_ne_zero_iff_lt.mpr gp


lemma imo_2022_p5_7_31
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  -- (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (p - 1) * p)
  -- (h₄ : b ! + p ≤ (p ^ 2) ^ (p - 1) * p + p)
  (h₅ : b ! + p < (p ^ 2) ^ (p - 1) * p * p) :
  b ! + p < p ^ (2 * p) := by
  rw [mul_assoc _ p p, ← pow_two p] at h₅
  rw [← Nat.pow_succ, succ_eq_add_one, gp1] at h₅
  rw [Nat.pow_mul]
  exact h₅


lemma imo_2022_p5_7_32
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  -- (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  -- (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (p - 1) * p)
  -- (h₄ : b ! + p ≤ (p ^ 2) ^ (p - 1) * p + p)
  (h₅ : b ! + p < (p ^ 2) ^ p) :
  b ! + p < p ^ (2 * p) := by
  rw [Nat.pow_mul]
  exact h₅


lemma imo_2022_p5_7_33
  (b p : ℕ)
  -- (h₀ : 0 < b)
  -- (hp : Nat.Prime p)
  -- (hb2p : b < 2 * p)
  -- (h₁ : b ! ≤ (2 * p - 1)!)
  -- (gp : 2 ≤ p)
  (gp1 : p - 1 + 1 = p)
  -- (f : ℕ → ℕ)
  -- (hf : f = fun x => x + 1)
  -- (h₂ : Finset.prod (Finset.range (2 * p - 1)) f = (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p)
  -- (h₃ : (Finset.prod (Finset.range (p - 1)) fun x => p ^ 2 - (x + 1) ^ 2) * p ≤ (p ^ 2) ^ (p - 1) * p)
  -- (h₄ : b ! + p ≤ (p ^ 2) ^ (p - 1) * p + p)
  (h₅ : b ! + p < (p ^ 2) ^ (p - 1) * p * p) :
  b ! + p < (p ^ 2) ^ p := by
  rw [mul_assoc _ p p, ← pow_two p] at h₅
  rw [← Nat.pow_succ, succ_eq_add_one, gp1] at h₅
  exact h₅


lemma imo_2022_p5_8
  (a b p: ℕ)
  (h₀: 0 < a ∧ 0 < b)
  (hp: Nat.Prime p)
  (h₁: a ^ p = b.factorial + p)
  (hbp: p ≤ b)
  (h₂: p ∣ a)
  (hb2p: b < 2 * p) :
  (a = p) := by
  have gp: p ≤ a := by exact Nat.le_of_dvd h₀.1 h₂
  cases' lt_or_eq_of_le gp with h₃ h₃
  . exfalso
    cases' h₂ with c h₂
    have gc: 0 < c := by
      by_contra hc0
      push_neg at hc0
      interval_cases c
      simp at *
      linarith
    by_cases hc: c < p
    . have g₁: c ∣ c^p := by exact dvd_pow_self c (by linarith)
      have h₄: c ∣ a^p := by
        rw [h₂, mul_pow]
        exact dvd_mul_of_dvd_right g₁ (p ^ p)
      have h₅: c ∣ b.factorial := by exact Nat.dvd_factorial gc (by linarith)
      have g₂: p = a ^ p - b.factorial := by
        symm
        rw [add_comm] at h₁
        refine (Nat.sub_eq_iff_eq_add ?_).mpr h₁
        rw [add_comm] at h₁
        exact le.intro (h₁.symm)
      have h₆: c ∣ p := by
        rw [g₂]
        exact dvd_sub' h₄ h₅
      have h₇: c = 1 ∨ c = p := by exact (dvd_prime hp).mp h₆
      cases' h₇ with h₇₀ h₇₁
      . rw [h₇₀, mul_one] at h₂
        rw [h₂] at h₃
        linarith [h₃]
      . rw [h₇₁] at hc
        simp at hc
    . push_neg at hc
      have g₃: p^2 ≤ a := by
        rw [h₂, pow_two]
        exact mul_le_mul_left' hc p
      have h₃: p^(2*p) ≤ a^p := by
        rw [pow_mul]
        exact pow_left_mono p g₃
      have h₇: b.factorial + p < p^(2*p) := by exact imo_2022_p5_7 b p hp hb2p
      rw [←h₁] at h₇
      linarith
  exact h₃.symm


lemma imo_2022_p5_8_1
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  (h₂ : p ∣ a)
  (hb2p : b < 2 * p)
  (gp : p ≤ a) :
  a = p := by
  cases' lt_or_eq_of_le gp with h₃ h₃
  . exfalso
    cases' h₂ with c h₂
    have gc: 0 < c := by
      by_contra hc0
      push_neg at hc0
      interval_cases c
      simp at *
      linarith
    by_cases hc: c < p
    . have g₁: c ∣ c^p := by exact dvd_pow_self c (by linarith)
      have h₄: c ∣ a^p := by
        rw [h₂, mul_pow]
        exact dvd_mul_of_dvd_right g₁ (p ^ p)
      have h₅: c ∣ b.factorial := by exact Nat.dvd_factorial gc (by linarith)
      have g₂: p = a ^ p - b.factorial := by
        symm
        rw [add_comm] at h₁
        refine (Nat.sub_eq_iff_eq_add ?_).mpr h₁
        rw [add_comm] at h₁
        exact le.intro (h₁.symm)
      have h₆: c ∣ p := by
        rw [g₂]
        exact dvd_sub' h₄ h₅
      have h₇: c = 1 ∨ c = p := by exact (dvd_prime hp).mp h₆
      cases' h₇ with h₇₀ h₇₁
      . rw [h₇₀, mul_one] at h₂
        rw [h₂] at h₃
        linarith [h₃]
      . rw [h₇₁] at hc
        simp at hc
    . push_neg at hc
      have g₃: p^2 ≤ a := by
        rw [h₂, pow_two]
        exact mul_le_mul_left' hc p
      have h₃: p^(2*p) ≤ a^p := by
        rw [pow_mul]
        exact pow_left_mono p g₃
      have h₇: b.factorial + p < p^(2*p) := by exact imo_2022_p5_7 b p hp hb2p
      rw [←h₁] at h₇
      linarith
  . exact h₃.symm


lemma imo_2022_p5_8_2
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  (h₂ : p ∣ a)
  (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a) :
  a = p := by
  exfalso
  cases' h₂ with c h₂
  have gc: 0 < c := by
    by_contra hc0
    push_neg at hc0
    interval_cases c
    simp at *
    linarith
  by_cases hc: c < p
  . have g₁: c ∣ c^p := by exact dvd_pow_self c (by linarith)
    have h₄: c ∣ a^p := by
      rw [h₂, mul_pow]
      exact dvd_mul_of_dvd_right g₁ (p ^ p)
    have h₅: c ∣ b.factorial := by exact Nat.dvd_factorial gc (by linarith)
    have g₂: p = a ^ p - b.factorial := by
      symm
      rw [add_comm] at h₁
      refine (Nat.sub_eq_iff_eq_add ?_).mpr h₁
      rw [add_comm] at h₁
      exact le.intro (h₁.symm)
    have h₆: c ∣ p := by
      rw [g₂]
      exact dvd_sub' h₄ h₅
    have h₇: c = 1 ∨ c = p := by exact (dvd_prime hp).mp h₆
    cases' h₇ with h₇₀ h₇₁
    . rw [h₇₀, mul_one] at h₂
      rw [h₂] at h₃
      linarith [h₃]
    . rw [h₇₁] at hc
      simp at hc
  . push_neg at hc
    have g₃: p^2 ≤ a := by
      rw [h₂, pow_two]
      exact mul_le_mul_left' hc p
    have h₃: p^(2*p) ≤ a^p := by
      rw [pow_mul]
      exact pow_left_mono p g₃
    have h₇: b.factorial + p < p^(2*p) := by exact imo_2022_p5_7 b p hp hb2p
    rw [←h₁] at h₇
    linarith


lemma imo_2022_p5_8_3
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c) :
  False := by
  have gc: 0 < c := by
    by_contra hc0
    push_neg at hc0
    interval_cases c
    simp at *
    linarith
  by_cases hc: c < p
  . have g₁: c ∣ c^p := by exact dvd_pow_self c (by linarith)
    have h₄: c ∣ a^p := by
      rw [h₂, mul_pow]
      exact dvd_mul_of_dvd_right g₁ (p ^ p)
    have h₅: c ∣ b.factorial := by exact Nat.dvd_factorial gc (by linarith)
    have g₂: p = a ^ p - b.factorial := by
      symm
      rw [add_comm] at h₁
      refine (Nat.sub_eq_iff_eq_add ?_).mpr h₁
      rw [add_comm] at h₁
      exact le.intro (h₁.symm)
    have h₆: c ∣ p := by
      rw [g₂]
      exact dvd_sub' h₄ h₅
    have h₇: c = 1 ∨ c = p := by exact (dvd_prime hp).mp h₆
    cases' h₇ with h₇₀ h₇₁
    . rw [h₇₀, mul_one] at h₂
      rw [h₂] at h₃
      linarith [h₃]
    . rw [h₇₁] at hc
      simp at hc
  . push_neg at hc
    have g₃: p^2 ≤ a := by
      rw [h₂, pow_two]
      exact mul_le_mul_left' hc p
    have h₃: p^(2*p) ≤ a^p := by
      rw [pow_mul]
      exact pow_left_mono p g₃
    have h₇: b.factorial + p < p^(2*p) := by exact imo_2022_p5_7 b p hp hb2p
    rw [←h₁] at h₇
    linarith


lemma imo_2022_p5_8_4
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c) :
  0 < c := by
  by_contra hc0
  push_neg at hc0
  interval_cases c
  simp at *
  linarith


lemma imo_2022_p5_8_5
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (hc0 : c ≤ 0) :
  False := by
  interval_cases c
  simp at *
  linarith


lemma imo_2022_p5_8_6
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  -- (c : ℕ)
  (h₂ : a = p * 0)
  (hc0 : 0 ≤ 0) :
  False := by
  simp at *
  linarith


lemma imo_2022_p5_8_7
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (gc : 0 < c) :
  False := by
  by_cases hc: c < p
  . have g₁: c ∣ c^p := by exact dvd_pow_self c (by linarith)
    have h₄: c ∣ a^p := by
      rw [h₂, mul_pow]
      exact dvd_mul_of_dvd_right g₁ (p ^ p)
    have h₅: c ∣ b.factorial := by exact Nat.dvd_factorial gc (by linarith)
    have g₂: p = a ^ p - b.factorial := by
      symm
      rw [add_comm] at h₁
      refine (Nat.sub_eq_iff_eq_add ?_).mpr h₁
      rw [add_comm] at h₁
      exact le.intro (h₁.symm)
    have h₆: c ∣ p := by
      rw [g₂]
      exact dvd_sub' h₄ h₅
    have h₇: c = 1 ∨ c = p := by exact (dvd_prime hp).mp h₆
    cases' h₇ with h₇₀ h₇₁
    . rw [h₇₀, mul_one] at h₂
      rw [h₂] at h₃
      linarith [h₃]
    . rw [h₇₁] at hc
      simp at hc
  . push_neg at hc
    have g₃: p^2 ≤ a := by
      rw [h₂, pow_two]
      exact mul_le_mul_left' hc p
    have h₃: p^(2*p) ≤ a^p := by
      rw [pow_mul]
      exact pow_left_mono p g₃
    have h₇: b.factorial + p < p^(2*p) := by exact imo_2022_p5_7 b p hp hb2p
    rw [←h₁] at h₇
    linarith


lemma imo_2022_p5_8_8
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (gc : 0 < c)
  (hc : c < p) :
  False := by
  have g₁: c ∣ c^p := by exact dvd_pow_self c (by linarith)
  have h₄: c ∣ a^p := by
    rw [h₂, mul_pow]
    exact dvd_mul_of_dvd_right g₁ (p ^ p)
  have h₅: c ∣ b.factorial := by exact Nat.dvd_factorial gc (by linarith)
  have g₂: p = a ^ p - b.factorial := by
    symm
    rw [add_comm] at h₁
    refine (Nat.sub_eq_iff_eq_add ?_).mpr h₁
    rw [add_comm] at h₁
    exact le.intro (h₁.symm)
  have h₆: c ∣ p := by
    rw [g₂]
    exact dvd_sub' h₄ h₅
  have h₇: c = 1 ∨ c = p := by exact (dvd_prime hp).mp h₆
  cases' h₇ with h₇₀ h₇₁
  . rw [h₇₀, mul_one] at h₂
    rw [h₂] at h₃
    linarith [h₃]
  . rw [h₇₁] at hc
    simp at hc


lemma imo_2022_p5_8_9
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (gc : 0 < c)
  (hc : c < p)
  (g₁ : c ∣ c ^ p) :
  False := by
  have h₄: c ∣ a^p := by
    rw [h₂, mul_pow]
    exact dvd_mul_of_dvd_right g₁ (p ^ p)
  have h₅: c ∣ b.factorial := by exact Nat.dvd_factorial gc (by linarith)
  have g₂: p = a ^ p - b.factorial := by
    symm
    rw [add_comm] at h₁
    refine (Nat.sub_eq_iff_eq_add ?_).mpr h₁
    rw [add_comm] at h₁
    exact le.intro (h₁.symm)
  have h₆: c ∣ p := by
    rw [g₂]
    exact dvd_sub' h₄ h₅
  have h₇: c = 1 ∨ c = p := by exact (dvd_prime hp).mp h₆
  cases' h₇ with h₇₀ h₇₁
  . rw [h₇₀, mul_one] at h₂
    rw [h₂] at h₃
    linarith [h₃]
  . rw [h₇₁] at hc
    simp at hc


lemma imo_2022_p5_8_10
  (a p : ℕ)
  -- (b : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  -- (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  -- (gc : 0 < c)
  -- (hc : c < p)
  (g₁ : c ∣ c ^ p) :
  c ∣ a ^ p := by
  rw [h₂, mul_pow]
  exact dvd_mul_of_dvd_right g₁ (p ^ p)


lemma imo_2022_p5_8_11
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (gc : 0 < c)
  (hc : c < p)
  (g₁ : c ∣ c ^ p)
  (h₄ : c ∣ a ^ p) :
  False := by
  have h₅: c ∣ b.factorial := by exact Nat.dvd_factorial gc (by linarith)
  have g₂: p = a ^ p - b.factorial := by
    symm
    rw [add_comm] at h₁
    refine (Nat.sub_eq_iff_eq_add ?_).mpr h₁
    rw [add_comm] at h₁
    exact le.intro (h₁.symm)
  have h₆: c ∣ p := by
    rw [g₂]
    exact dvd_sub' h₄ h₅
  have h₇: c = 1 ∨ c = p := by exact (dvd_prime hp).mp h₆
  cases' h₇ with h₇₀ h₇₁
  . rw [h₇₀, mul_one] at h₂
    rw [h₂] at h₃
    linarith [h₃]
  . rw [h₇₁] at hc
    simp at hc


lemma imo_2022_p5_8_12
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (gc : 0 < c)
  (hc : c < p)
  (g₁ : c ∣ c ^ p)
  (h₄ : c ∣ a ^ p)
  (h₅ : c ∣ b !) :
  False := by
  have g₂: p = a ^ p - b.factorial := by
    symm
    rw [add_comm] at h₁
    refine (Nat.sub_eq_iff_eq_add ?_).mpr h₁
    rw [add_comm] at h₁
    exact le.intro (h₁.symm)
  have h₆: c ∣ p := by
    rw [g₂]
    exact dvd_sub' h₄ h₅
  have h₇: c = 1 ∨ c = p := by exact (dvd_prime hp).mp h₆
  cases' h₇ with h₇₀ h₇₁
  . rw [h₇₀, mul_one] at h₂
    rw [h₂] at h₃
    linarith [h₃]
  . rw [h₇₁] at hc
    simp at hc


lemma imo_2022_p5_8_13
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  (hb2p : b < 2 * p)
  (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (gc : 0 < c)
  (hc : c < p)
  (g₁ : c ∣ c ^ p)
  (h₄ : c ∣ a ^ p)
  (h₅ : c ∣ b !) :
  p = a ^ p - b ! := by
  symm
  rw [add_comm] at h₁
  refine (Nat.sub_eq_iff_eq_add ?_).mpr h₁
  rw [add_comm] at h₁
  exact le.intro (h₁.symm)


lemma imo_2022_p5_8_14
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (h₁ : a ^ p = p + b !)
  (hbp : p ≤ b)
  (hb2p : b < 2 * p)
  (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (gc : 0 < c)
  (hc : c < p)
  (g₁ : c ∣ c ^ p)
  (h₄ : c ∣ a ^ p)
  (h₅ : c ∣ b !) :
  a ^ p - b ! = p := by
  refine (Nat.sub_eq_iff_eq_add ?_).mpr h₁
  rw [add_comm] at h₁
  exact le.intro (h₁.symm)


lemma imo_2022_p5_8_15
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (h₁ : a ^ p = p + b !)
  (hbp : p ≤ b)
  (hb2p : b < 2 * p)
  (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (gc : 0 < c)
  (hc : c < p)
  (g₁ : c ∣ c ^ p)
  (h₄ : c ∣ a ^ p)
  (h₅ : c ∣ b !) :
  b ! ≤ a ^ p := by
  rw [add_comm] at h₁
  exact le.intro (h₁.symm)


lemma imo_2022_p5_8_16
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (gc : 0 < c)
  (hc : c < p)
  (g₁ : c ∣ c ^ p)
  (h₄ : c ∣ a ^ p)
  (h₅ : c ∣ b !)
  (g₂ : p = a ^ p - b !) :
  False := by
  have h₆: c ∣ p := by
    rw [g₂]
    exact dvd_sub' h₄ h₅
  have h₇: c = 1 ∨ c = p := by exact (dvd_prime hp).mp h₆
  cases' h₇ with h₇₀ h₇₁
  . rw [h₇₀, mul_one] at h₂
    rw [h₂] at h₃
    linarith [h₃]
  . rw [h₇₁] at hc
    simp at hc


lemma imo_2022_p5_8_17
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  -- (h₃ : p < a)
  (c : ℕ)
  -- (h₂ : a = p * c)
  -- (gc : 0 < c)
  -- (hc : c < p)
  -- (g₁ : c ∣ c ^ p)
  (h₄ : c ∣ a ^ p)
  (h₅ : c ∣ b !)
  (g₂ : p = a ^ p - b !) :
  c ∣ p := by
  rw [g₂]
  exact dvd_sub' h₄ h₅


lemma imo_2022_p5_8_18
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (gc : 0 < c)
  (hc : c < p)
  (g₁ : c ∣ c ^ p)
  (h₄ : c ∣ a ^ p)
  (h₅ : c ∣ b !)
  (g₂ : p = a ^ p - b !)
  (h₆ : c ∣ p) :
  False := by
  have h₇: c = 1 ∨ c = p := by exact (dvd_prime hp).mp h₆
  cases' h₇ with h₇₀ h₇₁
  . rw [h₇₀, mul_one] at h₂
    rw [h₂] at h₃
    linarith [h₃]
  . rw [h₇₁] at hc
    simp at hc


lemma imo_2022_p5_8_19
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (gc : 0 < c)
  (hc : c < p)
  (g₁ : c ∣ c ^ p)
  (h₄ : c ∣ a ^ p)
  (h₅ : c ∣ b !)
  (g₂ : p = a ^ p - b !)
  (h₆ : c ∣ p)
  (h₇ : c = 1 ∨ c = p) :
  False := by
  cases' h₇ with h₇₀ h₇₁
  . rw [h₇₀, mul_one] at h₂
    rw [h₂] at h₃
    linarith [h₃]
  . rw [h₇₁] at hc
    simp at hc


lemma imo_2022_p5_8_20
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  (gc : 0 < c)
  (hc : c < p)
  (g₁ : c ∣ c ^ p)
  (h₄ : c ∣ a ^ p)
  (h₅ : c ∣ b !)
  (g₂ : p = a ^ p - b !)
  (h₆ : c ∣ p)
  (h₇₀ : c = 1) :
  False := by
  rw [h₇₀, mul_one] at h₂
  rw [h₂] at h₃
  linarith [h₃]


lemma imo_2022_p5_8_21
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  -- (h₃ : p < a)
  (c : ℕ)
  -- (h₂ : a = p * c)
  -- (gc : 0 < c)
  (hc : c < p)
  (g₁ : c ∣ c ^ p)
  (h₄ : c ∣ a ^ p)
  (h₅ : c ∣ b !)
  (g₂ : p = a ^ p - b !)
  (h₆ : c ∣ p)
  (h₇₁ : c = p) :
  False := by
  rw [h₇₁] at hc
  simp at hc


lemma imo_2022_p5_8_22
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  -- (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  -- (gc : 0 < c)
  (hc : p ≤ c) :
  False := by
  have g₃: p^2 ≤ a := by
    rw [h₂, pow_two]
    exact mul_le_mul_left' hc p
  have h₃: p^(2*p) ≤ a^p := by
    rw [pow_mul]
    exact pow_left_mono p g₃
  have h₇: b.factorial + p < p^(2*p) := by exact imo_2022_p5_7 b p hp hb2p
  rw [←h₁] at h₇
  linarith


lemma imo_2022_p5_8_23
  (a p : ℕ)
  -- (b : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  -- (h₃ : p < a)
  (c : ℕ)
  (h₂ : a = p * c)
  -- (gc : 0 < c)
  (hc : p ≤ c) :
  p ^ 2 ≤ a := by
  rw [h₂, pow_two]
  exact mul_le_mul_left' hc p


lemma imo_2022_p5_8_24
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  -- (h₃ : p < a)
  -- (c : ℕ)
  -- (h₂ : a = p * c)
  -- (gc : 0 < c)
  -- (hc : p ≤ c)
  (g₃ : p ^ 2 ≤ a) :
  False := by
  have h₃: p^(2*p) ≤ a^p := by
    rw [pow_mul]
    exact pow_left_mono p g₃
  have h₇: b.factorial + p < p^(2*p) := by exact imo_2022_p5_7 b p hp hb2p
  rw [←h₁] at h₇
  linarith


lemma imo_2022_p5_8_25
  (a p : ℕ)
  -- (b : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  -- (h₃ : p < a)
  -- (c : ℕ)
  -- (h₂ : a = p * c)
  -- (gc : 0 < c)
  -- (hc : p ≤ c)
  (g₃ : p ^ 2 ≤ a) :
  p ^ (2 * p) ≤ a ^ p := by
  rw [pow_mul]
  exact pow_left_mono p g₃


lemma imo_2022_p5_8_26
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  -- (h31 : p < a)
  -- (c : ℕ)
  -- (h₂ : a = p * c)
  -- (gc : 0 < c)
  -- (hc : p ≤ c)
  -- (g₃ : p ^ 2 ≤ a)
  (h₃ : p ^ (2 * p) ≤ a ^ p) :
  False := by
  have h₇: b.factorial + p < p^(2*p) := by exact imo_2022_p5_7 b p hp hb2p
  rw [←h₁] at h₇
  linarith


lemma imo_2022_p5_8_27
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (hb2p : b < 2 * p)
  -- (gp : p ≤ a)
  -- (h31 : p < a)
  -- (c : ℕ)
  -- (h₂ : a = p * c)
  -- (gc : 0 < c)
  -- (hc : p ≤ c)
  -- (g₃ : p ^ 2 ≤ a)
  (h₃ : p ^ (2 * p) ≤ a ^ p)
  (h₇ : b ! + p < p ^ (2 * p)) :
  False := by
  rw [←h₁] at h₇
  linarith


lemma imo_2022_p5_9
  (p: ℕ)
  -- (hp: Nat.Prime p)
  (hp5: 5 ≤ p) :
  ((↑p:ℤ) ^ p ≡ ↑p * (↑p + 1) * (-1) ^ (p - 1) + (-1) ^ p [ZMOD (↑p + 1) ^ 2]) := by
  -- have h₁: ↑p ^ p = Finset.range -- binomial expansion
  -- take the first two elements out
  -- show that all the other elements are individually divisible by (p+1)^2
  -- conclude that their sum is divisible by (p+1)^2
  -- summation ≡ 0 [ZMOD (↑p + 1) ^ 2]
  -- now show that Nat.modeq.add
  have h₀: (↑p:ℤ) = (↑p + 1) - 1 := by simp
  have h₁: ↑p ^ p ≡ ((↑p + 1) - 1) ^ p [ZMOD (↑p + 1) ^ 2] := by rw [← h₀]
  have h₂: (((↑p:ℤ) + 1) - 1) ^ p = (↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p)
           + (Finset.Ico 2 (p + 1)).sum (fun (k : ℕ) =>
           (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(p.choose k)) := by
    rw [sub_eq_add_neg]
    rw [add_pow ((↑p:ℤ) + 1) (-1:ℤ)]
    have g₀: 2 ≤ p + 1 := by
      have gg₀: 5 + 1 ≤ p + 1 := by exact add_le_add_right hp5 1
      refine le_trans ?_ gg₀
      norm_num
    have g₁: 1 ≤ 2 := by norm_num
    rw [← Finset.sum_range_add_sum_Ico _ g₀]
    rw [← Finset.sum_range_add_sum_Ico _ g₁]
    simp
    rw [add_comm]
    simp
    rw [mul_comm]
    rw [mul_assoc]
  have h₃: 0 ≡ (Finset.Ico 2 (p + 1)).sum (fun (k : ℕ) => (↑p + 1) ^ k * (-1) ^ (p - k) * ↑(p.choose k))
                [ZMOD (↑p + 1) ^ 2] := by
    refine Int.modEq_of_dvd ?_
    simp
    refine Finset.dvd_sum ?_
    intros x g₀
    have gx: 2 ≤ x := by exact (Finset.mem_Ico.mp g₀).left
    rw [mul_assoc]
    refine dvd_mul_of_dvd_left ?_ ((-1:ℤ) ^ (p - x) * ↑(p.choose x))
    refine pow_dvd_pow ((↑p:ℤ) + 1) gx
  rw [h₂] at h₁
  rw [← add_zero ((↑p:ℤ) ^ p)] at h₁
  exact Int.ModEq.add_right_cancel h₃ h₁


lemma imo_2022_p5_9_1
  (p : ℕ)
  (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2]) :
  ↑p ^ p ≡ ↑p * (↑p + 1) * (-1) ^ (p - 1) + (-1) ^ p [ZMOD (↑p + 1) ^ 2] := by
  have h₂: (((↑p:ℤ) + 1) - 1) ^ p = (↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p)
           + (Finset.Ico 2 (p + 1)).sum (fun (k : ℕ) =>
           (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(p.choose k)) := by
    rw [sub_eq_add_neg]
    rw [add_pow ((↑p:ℤ) + 1) (-1:ℤ)]
    have g₀: 2 ≤ p + 1 := by
      have gg₀: 5 + 1 ≤ p + 1 := by exact add_le_add_right hp5 1
      refine le_trans ?_ gg₀
      norm_num
    have g₁: 1 ≤ 2 := by norm_num
    rw [← Finset.sum_range_add_sum_Ico _ g₀]
    rw [← Finset.sum_range_add_sum_Ico _ g₁]
    simp
    rw [add_comm]
    simp
    rw [mul_comm]
    rw [mul_assoc]
  have h₃: 0 ≡ (Finset.Ico 2 (p + 1)).sum (fun (k : ℕ) => (↑p + 1) ^ k * (-1) ^ (p - k) * ↑(p.choose k))
                [ZMOD (↑p + 1) ^ 2] := by
    refine Int.modEq_of_dvd ?_
    simp
    refine Finset.dvd_sum ?_
    intros x g₀
    have gx: 2 ≤ x := by exact (Finset.mem_Ico.mp g₀).left
    rw [mul_assoc]
    refine dvd_mul_of_dvd_left ?_ ((-1:ℤ) ^ (p - x) * ↑(p.choose x))
    refine pow_dvd_pow ((↑p:ℤ) + 1) gx
  rw [h₂] at h₁
  rw [← add_zero ((↑p:ℤ) ^ p)] at h₁
  exact Int.ModEq.add_right_cancel h₃ h₁


lemma imo_2022_p5_9_2
  (p : ℕ)
  (hp5 : 5 ≤ p) :
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2]) :
  (↑p + 1 - 1) ^ p =
    ↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p +
      Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k) := by
  rw [sub_eq_add_neg]
  rw [add_pow ((↑p:ℤ) + 1) (-1:ℤ)]
  have g₀: 2 ≤ p + 1 := by
    have gg₀: 5 + 1 ≤ p + 1 := by exact add_le_add_right hp5 1
    refine le_trans ?_ gg₀
    norm_num
  have g₁: 1 ≤ 2 := by norm_num
  rw [← Finset.sum_range_add_sum_Ico _ g₀]
  rw [← Finset.sum_range_add_sum_Ico _ g₁]
  simp
  rw [add_comm]
  simp
  rw [mul_comm]
  rw [mul_assoc]


lemma imo_2022_p5_9_3
  (p : ℕ)
  (hp5 : 5 ≤ p) :
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  (Finset.sum (Finset.range (p + 1)) fun m => ((↑p:ℤ) + 1) ^ m * (-1:ℤ) ^ (p - m) * ↑(choose p m)) =
    (↑p:ℤ) * ((↑p:ℤ) + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p +
      Finset.sum (Finset.Ico 2 (p + 1)) fun k => ((↑p:ℤ) + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k) := by
  have g₀: 2 ≤ p + 1 := by
    have gg₀: 5 + 1 ≤ p + 1 := by exact add_le_add_right hp5 1
    refine le_trans ?_ gg₀
    norm_num
  have g₁: 1 ≤ 2 := by norm_num
  rw [← Finset.sum_range_add_sum_Ico _ g₀]
  rw [← Finset.sum_range_add_sum_Ico _ g₁]
  simp
  rw [add_comm]
  simp
  rw [mul_comm]
  rw [mul_assoc]


lemma imo_2022_p5_9_4
  (p : ℕ)
  (hp5 : 5 ≤ p) :
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2]) :
  (Finset.sum (Finset.range (p + 1)) fun m => ((↑p + 1) ^ m * (-1:ℤ) ^ (p - m) * ↑(choose p m))) =
    ↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1:ℤ) ^ p +
      Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k) := by
  have g₀: 2 ≤ p + 1 := by
    have gg₀: 5 + 1 ≤ p + 1 := by exact add_le_add_right hp5 1
    refine le_trans ?_ gg₀
    norm_num
  have g₁: 1 ≤ 2 := by norm_num
  rw [← Finset.sum_range_add_sum_Ico _ g₀]
  rw [← Finset.sum_range_add_sum_Ico _ g₁]
  simp
  rw [add_comm]
  simp
  rw [mul_comm]
  rw [mul_assoc]


lemma imo_2022_p5_9_5
  (p : ℕ)
  (hp5 : 5 ≤ p) :
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2]) :
  2 ≤ p + 1 := by
  have gg₀: 5 + 1 ≤ p + 1 := by exact add_le_add_right hp5 1
  refine le_trans ?_ gg₀
  norm_num


lemma imo_2022_p5_9_6
  (p : ℕ)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  (g₀ : 2 ≤ p + 1) :
  (Finset.sum (Finset.range (p + 1)) fun m => (↑p + 1) ^ m * (-1:ℤ) ^ (p - m) * ↑(choose p m)) =
    ↑p * (↑p + 1) * (-1) ^ (p - 1) + (-1) ^ p +
      Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k) := by
  have g₁: 1 ≤ 2 := by norm_num
  rw [← Finset.sum_range_add_sum_Ico _ g₀]
  rw [← Finset.sum_range_add_sum_Ico _ g₁]
  simp
  rw [add_comm]
  simp
  rw [mul_comm]
  rw [mul_assoc]


lemma imo_2022_p5_9_7
  (p : ℕ) :
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  -- (g₀ : 2 ≤ p + 1)
  -- (g₁ : 1 ≤ 2) :
  (((Finset.sum (Finset.range 1) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k)) +
        Finset.sum (Finset.Ico 1 2) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k)) +
      Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k)) =
    ↑p * (↑p + 1) * (-1) ^ (p - 1) + (-1) ^ p +
      Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k) := by
  simp
  rw [add_comm]
  simp
  rw [mul_comm]
  rw [mul_assoc]


lemma imo_2022_p5_9_8
  (p : ℕ) :
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  -- (g₀ : 2 ≤ p + 1)
  -- (g₁ : 1 ≤ 2) :
  (-1:ℤ) ^ p + (↑p + 1) * (-1) ^ (p - 1) * ↑p = ↑p * (↑p + 1) * (-1) ^ (p - 1) + (-1) ^ p := by
  rw [add_comm]
  simp
  rw [mul_comm]
  rw [mul_assoc]


lemma imo_2022_p5_9_9
  (p : ℕ) :
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  -- (g₀ : 2 ≤ p + 1)
  -- (g₁ : 1 ≤ 2) :
  (↑p + 1) * (-1:ℤ) ^ (p - 1) * ↑p = ↑p * (↑p + 1) * (-1) ^ (p - 1) := by
  rw [mul_comm]
  rw [mul_assoc]


lemma imo_2022_p5_9_10
  (p : ℕ)
  (h₀: (↑p + 1) * (-1:ℤ) ^ (p - 1) * ↑p + (-1) ^ p = ↑p * (↑p + 1) * (-1) ^ (p - 1) + (-1) ^ p)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  (g₀ : 2 ≤ p + 1) :
  (Finset.sum (Finset.range (p + 1)) fun m => (↑p + 1) ^ m * (-1:ℤ) ^ (p - m) * ↑(choose p m)) =
    ↑p * (↑p + 1) * (-1) ^ (p - 1) + (-1) ^ p +
      Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k) := by
  have g₁: 1 ≤ 2 := by norm_num
  rw [← Finset.sum_range_add_sum_Ico _ g₀]
  rw [← Finset.sum_range_add_sum_Ico _ g₁]
  simp
  rw [add_comm]
  exact h₀


lemma imo_2022_p5_9_11
  (p : ℕ)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  (h₂ : (↑p + 1 - 1) ^ p =
    ↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p +
      Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k)) :
  ↑p ^ p ≡ ↑p * (↑p + 1) * (-1) ^ (p - 1) + (-1) ^ p [ZMOD (↑p + 1) ^ 2] := by
  have h₃: 0 ≡ (Finset.Ico 2 (p + 1)).sum (fun (k : ℕ) => (↑p + 1) ^ k * (-1) ^ (p - k) * ↑(p.choose k))
                [ZMOD (↑p + 1) ^ 2] := by
    refine Int.modEq_of_dvd ?_
    simp
    refine Finset.dvd_sum ?_
    intros x g₀
    have gx: 2 ≤ x := by exact (Finset.mem_Ico.mp g₀).left
    rw [mul_assoc]
    refine dvd_mul_of_dvd_left ?_ ((-1:ℤ) ^ (p - x) * ↑(p.choose x))
    refine pow_dvd_pow ((↑p:ℤ) + 1) gx
  rw [h₂] at h₁
  rw [← add_zero ((↑p:ℤ) ^ p)] at h₁
  exact Int.ModEq.add_right_cancel h₃ h₁


lemma imo_2022_p5_9_12
  (p : ℕ) :
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : (↑p + 1 - 1) ^ p =
  --   ↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p +
  --     Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k)) :
  0 ≡ Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1) ^ (p - k)
    * ↑(choose p k) [ZMOD (↑p + 1) ^ 2] := by
  refine Int.modEq_of_dvd ?_
  simp
  refine Finset.dvd_sum ?_
  intros x g₀
  have gx: 2 ≤ x := by exact (Finset.mem_Ico.mp g₀).left
  rw [mul_assoc]
  refine dvd_mul_of_dvd_left ?_ ((-1:ℤ) ^ (p - x) * ↑(p.choose x))
  refine pow_dvd_pow ((↑p:ℤ) + 1) gx


lemma imo_2022_p5_9_13
  (p : ℕ) :
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : (↑p + 1 - 1) ^ p =
  --   ↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p +
  --     Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k))
  -- (h₃: 0 ≡ Finset.sum (Finset.Ico 2 (p + 1))
  --   fun (k:ℕ) => (↑p + 1) ^ k * (-1) ^ (p - k) * ↑(choose p k) [ZMOD (↑p + 1) ^ 2]) :
  ((↑p:ℤ) + 1) ^ 2 ∣ Finset.sum (Finset.Ico 2 (p + 1)) fun (k:ℕ) => ((↑p:ℤ) + 1) ^ k
    * (-1:ℤ) ^ (p - k) * ↑(choose p k) := by
  refine Finset.dvd_sum ?_
  intros x g₀
  have gx: 2 ≤ x := by exact (Finset.mem_Ico.mp g₀).left
  rw [mul_assoc]
  refine dvd_mul_of_dvd_left ?_ ((-1:ℤ) ^ (p - x) * ↑(p.choose x))
  exact pow_dvd_pow ((↑p:ℤ) + 1) gx


lemma imo_2022_p5_9_14
  (p : ℕ)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : (↑p + 1 - 1) ^ p =
  --   ↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p +
  --     Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k))
  (h₃ : ∀ i ∈ Finset.Ico 2 (p + 1), ((↑p:ℤ) + 1) ^ 2 ∣ (↑p + 1) ^ i * (-1:ℤ) ^ (p - i) * ↑(choose p i)) :
  0 ≡ Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1) ^ (p - k)
    * ↑(choose p k) [ZMOD (↑p + 1) ^ 2] := by
  refine Int.modEq_of_dvd ?_
  simp
  exact Finset.dvd_sum h₃


lemma imo_2022_p5_9_15
  (p : ℕ)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  (h₂ : ∀ x ∈ Finset.Ico 2 (p + 1), ((↑p:ℤ) + 1) ^ 2 ∣ ((↑p:ℤ) + 1) ^ x) :
  ((↑p:ℤ) + 1) ^ 2 ∣ Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k
    * (-1:ℤ) ^ (p - k) * ↑(choose p k) := by
  refine Finset.dvd_sum ?_
  intros x g₀
  rw [mul_assoc]
  refine dvd_mul_of_dvd_left ?_ ((-1:ℤ) ^ (p - x) * ↑(p.choose x))
  exact h₂ x g₀


lemma imo_2022_p5_9_16
  (p : ℕ) :
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : (↑p + 1 - 1) ^ p =
  --   ↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p +
  --     Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k)) :
  ∀ i ∈ Finset.Ico 2 (p + 1), ((↑p:ℤ) + 1) ^ 2 ∣ (↑p + 1) ^ i * (-1:ℤ) ^ (p - i) * ↑(choose p i) := by
  intros x g₀
  have gx: 2 ≤ x := by exact (Finset.mem_Ico.mp g₀).left
  rw [mul_assoc]
  refine dvd_mul_of_dvd_left ?_ ((-1:ℤ) ^ (p - x) * ↑(p.choose x))
  refine pow_dvd_pow ((↑p:ℤ) + 1) gx


lemma imo_2022_p5_9_17
  (p : ℕ)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : (↑p + 1 - 1) ^ p =
  --   ↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p +
  --     Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k))
  (x : ℕ)
  -- (g₀ : x ∈ Finset.Ico 2 (p + 1))
  (gx : 2 ≤ x) :
  ((↑p:ℤ) + 1) ^ 2 ∣ (↑p + 1) ^ x * (-1:ℤ) ^ (p - x) * ↑(choose p x) := by
  rw [mul_assoc]
  refine dvd_mul_of_dvd_left ?_ ((-1:ℤ) ^ (p - x) * ↑(p.choose x))
  refine pow_dvd_pow ((↑p:ℤ) + 1) gx


lemma imo_2022_p5_9_18
  (p : ℕ)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  -- (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : (↑p + 1 - 1) ^ p =
  --   ↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p +
  --     Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k))
  (x : ℕ)
  (g₀ : x ∈ Finset.Ico 2 (p + 1)) :
  ((↑p:ℤ) + 1) ^ 2 ∣ ((↑p:ℤ) + 1) ^ x := by
  refine pow_dvd_pow ((↑p:ℤ) + 1) ?_
  exact (Finset.mem_Ico.mp g₀).left


lemma imo_2022_p5_9_19
  (p : ℕ)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : ↑p = ↑p + 1 - 1)
  (h₁ : ↑p ^ p ≡ (↑p + 1 - 1) ^ p [ZMOD (↑p + 1) ^ 2])
  (h₂ : (↑p + 1 - 1) ^ p =
    ↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p +
      Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(choose p k))
  (h₃ : 0 ≡ Finset.sum (Finset.Ico 2 (p + 1)) fun k => (↑p + 1) ^ k * (-1) ^ (p - k) * ↑(choose p k) [ZMOD (↑p + 1) ^ 2]) :
  ↑p ^ p ≡ ↑p * (↑p + 1) * (-1) ^ (p - 1) + (-1) ^ p [ZMOD (↑p + 1) ^ 2] := by
  rw [h₂] at h₁
  rw [← add_zero ((↑p:ℤ) ^ p)] at h₁
  exact Int.ModEq.add_right_cancel h₃ h₁






lemma imo_2022_p5_10
  (p: ℕ)
  (hp: Nat.Prime p)
  (hp5: 5 ≤ p)
  -- (hp7: 7 ≤ p)
  (h₀: (p + 1) ^ 2 ∣ p ^ p - p) :
  False := by
  have h₁: ((↑p^p - ↑p):ℤ) ≡ (↑(p.choose 1) * ↑(p + 1) * (-1:ℤ)^(p-1) + (-1:ℤ)^p) - ↑p
      [ZMOD ↑(p+1)^2] := by
    refine Int.ModEq.sub_right (↑p) ?_
    simp
    exact imo_2022_p5_9 p hp5
  have gpo: Odd p := by
    refine Nat.Prime.odd_of_ne_two hp ?_
    linarith [hp5]
  have gpe: Even (p - 1) := by
    refine hp.even_sub_one ?_
    linarith [hp5]
  have g₁: (-1:ℤ) ^ (p - 1) = 1 := by exact Even.neg_one_pow gpe
  have g₂: (-1:ℤ) ^ (p) = -1 := by exact Odd.neg_one_pow gpo
  rw [g₁,g₂] at h₁
  simp at h₁
  -- norm_cast at h₁
  have h₂: (p ^ p - p) ≡ (p * (p + 1)) - 1 - p [MOD ((p + 1) ^ 2)] := by
    refine Int.natCast_modEq_iff.mp ?_
    have g₃: p ≤ p^p := by
      refine Nat.le_self_pow (by linarith) _
    rw [Nat.cast_sub g₃]
    have g₄: p ≤ p * (p + 1) - 1 := by
      rw [mul_add]
      simp
      rw [add_comm, Nat.add_sub_assoc]
      simp
      rw [← pow_two]
      refine Nat.one_le_pow 2 p (by linarith)
    rw [Nat.cast_sub g₄]
    have g₅: 1 ≤ p * (p + 1) := by
      rw [← mul_one (p * (p + 1))]
      refine Nat.le_mul_of_pos_left ?_ ?_
      refine Nat.mul_pos (by linarith) (by linarith)
    rw [Nat.cast_sub g₅]
    rw [← sub_eq_add_neg] at h₁
    norm_cast
    norm_cast at h₁
  have h₃: p * (p + 1) - 1 - p = p^2 - 1 := by
    rw [Nat.sub_sub, mul_add]
    simp
    rw [← pow_two]
    exact Nat.add_sub_add_right (p^2) p 1
  rw [h₃] at h₂
  clear h₃ gpo gpe g₁ g₂
  -- now derive a line of contradictions from h₀
  have hc₁: (p ^ p - p) ≡ 0 [MOD (p+1)^2] := by exact modEq_zero_iff_dvd.mpr h₀
  -- mix the contradiction with what we had in h₂
  have h₄: p ^ 2 - 1 ≡ 0 [MOD (p+1)^2] := by
    apply Nat.ModEq.symm at h₂
    exact Nat.ModEq.trans h₂ hc₁
  have h₅: p - 1 ≡ 0 [MOD (p+1)] := by
    rw [pow_two] at h₄
    have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
      rw [mul_comm]
      exact Nat.sq_sub_sq p 1
    simp at g₀
    rw [g₀] at h₄
    have g₁: p + 1 ≠ 0 := by linarith
    refine Nat.ModEq.mul_right_cancel' g₁ ?_
    rw [zero_mul]
    exact h₄
  have h₆: p - 1 ≤ 0 := by
    refine Nat.ModEq.le_of_lt_add h₅ ?_
    simp
    rw [← succ_eq_add_one]
    refine Nat.sub_lt_succ p 1
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]



lemma imo_2022_p5_10_1
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p) :
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p) :
  ↑p ^ p - ↑p ≡ ↑(choose p 1) * ↑(p + 1) * (-1) ^ (p - 1) + (-1) ^ p - ↑p [ZMOD ↑(p + 1) ^ 2] := by
  refine Int.ModEq.sub_right (↑p) ?_
  simp
  exact imo_2022_p5_9 p hp5


lemma imo_2022_p5_10_2
  (p : ℕ)
  (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  (h₁ : ↑p ^ p - ↑p ≡ ↑(choose p 1) * ↑(p + 1) * (-1) ^ (p - 1) + (-1) ^ p - ↑p [ZMOD ↑(p + 1) ^ 2]) :
  False := by
  have gpo: Odd p := by
    refine Nat.Prime.odd_of_ne_two hp ?_
    linarith [hp5]
  have gpe: Even (p - 1) := by
    refine hp.even_sub_one ?_
    linarith [hp5]
  have g₁: (-1:ℤ) ^ (p - 1) = 1 := by exact Even.neg_one_pow gpe
  have g₂: (-1:ℤ) ^ (p) = -1 := by exact Odd.neg_one_pow gpo
  rw [g₁,g₂] at h₁
  simp at h₁
  -- norm_cast at h₁
  have h₂: (p ^ p - p) ≡ (p * (p + 1)) - 1 - p [MOD ((p + 1) ^ 2)] := by
    refine Int.natCast_modEq_iff.mp ?_
    have g₃: p ≤ p^p := by
      refine Nat.le_self_pow (by linarith) _
    rw [Nat.cast_sub g₃]
    have g₄: p ≤ p * (p + 1) - 1 := by
      rw [mul_add]
      simp
      rw [add_comm, Nat.add_sub_assoc]
      simp
      rw [← pow_two]
      refine Nat.one_le_pow 2 p (by linarith)
    rw [Nat.cast_sub g₄]
    have g₅: 1 ≤ p * (p + 1) := by
      rw [← mul_one (p * (p + 1))]
      refine Nat.le_mul_of_pos_left ?_ ?_
      refine Nat.mul_pos (by linarith) (by linarith)
    rw [Nat.cast_sub g₅]
    rw [← sub_eq_add_neg] at h₁
    norm_cast
    norm_cast at h₁
  have h₃: p * (p + 1) - 1 - p = p^2 - 1 := by
    rw [Nat.sub_sub, mul_add]
    simp
    rw [← pow_two]
    exact Nat.add_sub_add_right (p^2) p 1
  rw [h₃] at h₂
  clear h₃ gpo gpe g₁ g₂
  -- now derive a line of contradictions from h₀
  have hc₁: (p ^ p - p) ≡ 0 [MOD (p+1)^2] := by exact modEq_zero_iff_dvd.mpr h₀
  -- mix the contradiction with what we had in h₂
  have h₄: p ^ 2 - 1 ≡ 0 [MOD (p+1)^2] := by
    apply Nat.ModEq.symm at h₂
    exact Nat.ModEq.trans h₂ hc₁
  have h₅: p - 1 ≡ 0 [MOD (p+1)] := by
    rw [pow_two] at h₄
    have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
      rw [mul_comm]
      exact Nat.sq_sub_sq p 1
    simp at g₀
    rw [g₀] at h₄
    have g₁: p + 1 ≠ 0 := by linarith
    refine Nat.ModEq.mul_right_cancel' g₁ ?_
    rw [zero_mul]
    exact h₄
  have h₆: p - 1 ≤ 0 := by
    refine Nat.ModEq.le_of_lt_add h₅ ?_
    simp
    rw [← succ_eq_add_one]
    refine Nat.sub_lt_succ p 1
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]


lemma imo_2022_p5_10_3
  (p : ℕ)
  (hp : Nat.Prime p)
  (hp5 : 5 ≤ p) :
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑(choose p 1) * ↑(p + 1) * (-1) ^ (p - 1) + (-1) ^ p - ↑p [ZMOD ↑(p + 1) ^ 2]) :
  Odd p := by
  refine Nat.Prime.odd_of_ne_two hp ?_
  linarith [hp5]


lemma imo_2022_p5_10_4
  (p : ℕ)
  (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  (h₁ : ↑p ^ p - ↑p ≡ ↑(choose p 1) * ↑(p + 1) * (-1) ^ (p - 1) + (-1) ^ p - ↑p [ZMOD ↑(p + 1) ^ 2])
  (gpo : Odd p) :
  False := by
  have gpe: Even (p - 1) := by
    refine hp.even_sub_one ?_
    linarith [hp5]
  have g₁: (-1:ℤ) ^ (p - 1) = 1 := by exact Even.neg_one_pow gpe
  have g₂: (-1:ℤ) ^ (p) = -1 := by exact Odd.neg_one_pow gpo
  rw [g₁,g₂] at h₁
  simp at h₁
  -- norm_cast at h₁
  have h₂: (p ^ p - p) ≡ (p * (p + 1)) - 1 - p [MOD ((p + 1) ^ 2)] := by
    refine Int.natCast_modEq_iff.mp ?_
    have g₃: p ≤ p^p := by
      refine Nat.le_self_pow (by linarith) _
    rw [Nat.cast_sub g₃]
    have g₄: p ≤ p * (p + 1) - 1 := by
      rw [mul_add]
      simp
      rw [add_comm, Nat.add_sub_assoc]
      simp
      rw [← pow_two]
      refine Nat.one_le_pow 2 p (by linarith)
    rw [Nat.cast_sub g₄]
    have g₅: 1 ≤ p * (p + 1) := by
      rw [← mul_one (p * (p + 1))]
      refine Nat.le_mul_of_pos_left ?_ ?_
      refine Nat.mul_pos (by linarith) (by linarith)
    rw [Nat.cast_sub g₅]
    rw [← sub_eq_add_neg] at h₁
    norm_cast
    norm_cast at h₁
  have h₃: p * (p + 1) - 1 - p = p^2 - 1 := by
    rw [Nat.sub_sub, mul_add]
    simp
    rw [← pow_two]
    exact Nat.add_sub_add_right (p^2) p 1
  rw [h₃] at h₂
  clear h₃ gpo gpe g₁ g₂
  -- now derive a line of contradictions from h₀
  have hc₁: (p ^ p - p) ≡ 0 [MOD (p+1)^2] := by exact modEq_zero_iff_dvd.mpr h₀
  -- mix the contradiction with what we had in h₂
  have h₄: p ^ 2 - 1 ≡ 0 [MOD (p+1)^2] := by
    apply Nat.ModEq.symm at h₂
    exact Nat.ModEq.trans h₂ hc₁
  have h₅: p - 1 ≡ 0 [MOD (p+1)] := by
    rw [pow_two] at h₄
    have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
      rw [mul_comm]
      exact Nat.sq_sub_sq p 1
    simp at g₀
    rw [g₀] at h₄
    have g₁: p + 1 ≠ 0 := by linarith
    refine Nat.ModEq.mul_right_cancel' g₁ ?_
    rw [zero_mul]
    exact h₄
  have h₆: p - 1 ≤ 0 := by
    refine Nat.ModEq.le_of_lt_add h₅ ?_
    simp
    rw [← succ_eq_add_one]
    refine Nat.sub_lt_succ p 1
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]


lemma imo_2022_p5_10_5
  (p : ℕ)
  (hp : Nat.Prime p)
  (hp5 : 5 ≤ p) :
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑(choose p 1) * ↑(p + 1) * (-1) ^ (p - 1) + (-1) ^ p - ↑p [ZMOD ↑(p + 1) ^ 2])
  -- (gpo : Odd p) :
  Even (p - 1) := by
  refine hp.even_sub_one ?_
  linarith [hp5]


lemma imo_2022_p5_10_6
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  (h₁ : ↑p ^ p - ↑p ≡ ↑(choose p 1) * ↑(p + 1) * (-1) ^ (p - 1) + (-1) ^ p - ↑p [ZMOD ↑(p + 1) ^ 2])
  (gpo : Odd p)
  (gpe : Even (p - 1)) :
  False := by
  have g₁: (-1:ℤ) ^ (p - 1) = 1 := by exact Even.neg_one_pow gpe
  have g₂: (-1:ℤ) ^ (p) = -1 := by exact Odd.neg_one_pow gpo
  rw [g₁,g₂] at h₁
  simp at h₁
  have h₂: (p ^ p - p) ≡ (p * (p + 1)) - 1 - p [MOD ((p + 1) ^ 2)] := by
    refine Int.natCast_modEq_iff.mp ?_
    have g₃: p ≤ p^p := by
      refine Nat.le_self_pow (by linarith) _
    rw [Nat.cast_sub g₃]
    have g₄: p ≤ p * (p + 1) - 1 := by
      rw [mul_add]
      simp
      rw [add_comm, Nat.add_sub_assoc]
      simp
      rw [← pow_two]
      refine Nat.one_le_pow 2 p (by linarith)
    rw [Nat.cast_sub g₄]
    have g₅: 1 ≤ p * (p + 1) := by
      rw [← mul_one (p * (p + 1))]
      refine Nat.le_mul_of_pos_left ?_ ?_
      refine Nat.mul_pos (by linarith) (by linarith)
    rw [Nat.cast_sub g₅]
    rw [← sub_eq_add_neg] at h₁
    norm_cast
    norm_cast at h₁
  have h₃: p * (p + 1) - 1 - p = p^2 - 1 := by
    rw [Nat.sub_sub, mul_add]
    simp
    rw [← pow_two]
    exact Nat.add_sub_add_right (p^2) p 1
  rw [h₃] at h₂
  clear h₃ gpo gpe g₁ g₂
  -- now derive a line of contradictions from h₀
  have hc₁: (p ^ p - p) ≡ 0 [MOD (p+1)^2] := by exact modEq_zero_iff_dvd.mpr h₀
  -- mix the contradiction with what we had in h₂
  have h₄: p ^ 2 - 1 ≡ 0 [MOD (p+1)^2] := by
    apply Nat.ModEq.symm at h₂
    exact Nat.ModEq.trans h₂ hc₁
  have h₅: p - 1 ≡ 0 [MOD (p+1)] := by
    rw [pow_two] at h₄
    have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
      rw [mul_comm]
      exact Nat.sq_sub_sq p 1
    simp at g₀
    rw [g₀] at h₄
    have g₁: p + 1 ≠ 0 := by linarith
    refine Nat.ModEq.mul_right_cancel' g₁ ?_
    rw [zero_mul]
    exact h₄
  have h₆: p - 1 ≤ 0 := by
    refine Nat.ModEq.le_of_lt_add h₅ ?_
    simp
    rw [← succ_eq_add_one]
    refine Nat.sub_lt_succ p 1
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]


lemma imo_2022_p5_10_7
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  (h₁ : ↑p ^ p - ↑p ≡ ↑(choose p 1) * ↑(p + 1) * (-1) ^ (p - 1) + (-1) ^ p - ↑p [ZMOD ↑(p + 1) ^ 2])
  (gpo : Odd p)
  (gpe : Even (p - 1))
  (g₁ : (-1) ^ (p - 1) = 1)
  (g₂ : (-1) ^ p = -1) :
  False := by
  rw [g₁,g₂] at h₁
  simp at h₁
  have h₂: (p ^ p - p) ≡ (p * (p + 1)) - 1 - p [MOD ((p + 1) ^ 2)] := by
    refine Int.natCast_modEq_iff.mp ?_
    have g₃: p ≤ p^p := by
      refine Nat.le_self_pow (by linarith) _
    rw [Nat.cast_sub g₃]
    have g₄: p ≤ p * (p + 1) - 1 := by
      rw [mul_add]
      simp
      rw [add_comm, Nat.add_sub_assoc]
      simp
      rw [← pow_two]
      refine Nat.one_le_pow 2 p (by linarith)
    rw [Nat.cast_sub g₄]
    have g₅: 1 ≤ p * (p + 1) := by
      rw [← mul_one (p * (p + 1))]
      refine Nat.le_mul_of_pos_left ?_ ?_
      refine Nat.mul_pos (by linarith) (by linarith)
    rw [Nat.cast_sub g₅]
    rw [← sub_eq_add_neg] at h₁
    norm_cast
    norm_cast at h₁
  have h₃: p * (p + 1) - 1 - p = p^2 - 1 := by
    rw [Nat.sub_sub, mul_add]
    simp
    rw [← pow_two]
    exact Nat.add_sub_add_right (p^2) p 1
  rw [h₃] at h₂
  clear h₃ gpo gpe g₁ g₂
  -- now derive a line of contradictions from h₀
  have hc₁: (p ^ p - p) ≡ 0 [MOD (p+1)^2] := by exact modEq_zero_iff_dvd.mpr h₀
  -- mix the contradiction with what we had in h₂
  have h₄: p ^ 2 - 1 ≡ 0 [MOD (p+1)^2] := by
    apply Nat.ModEq.symm at h₂
    exact Nat.ModEq.trans h₂ hc₁
  have h₅: p - 1 ≡ 0 [MOD (p+1)] := by
    rw [pow_two] at h₄
    have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
      rw [mul_comm]
      exact Nat.sq_sub_sq p 1
    simp at g₀
    rw [g₀] at h₄
    have g₁: p + 1 ≠ 0 := by linarith
    refine Nat.ModEq.mul_right_cancel' g₁ ?_
    rw [zero_mul]
    exact h₄
  have h₆: p - 1 ≤ 0 := by
    refine Nat.ModEq.le_of_lt_add h₅ ?_
    simp
    rw [← succ_eq_add_one]
    refine Nat.sub_lt_succ p 1
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]


lemma imo_2022_p5_10_8
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p) :
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑(choose p 1) * ↑(p + 1) * (-1) ^ (p - 1) + (-1:ℤ) ^ p - ↑p [ZMOD ↑(p + 1) ^ 2])
  -- (gpo : Odd p)
  -- (gpe : Even (p - 1))
  -- (g₁ : (-1) ^ (p - 1) = 1)
  -- (g₂ : (-1) ^ p = -1) :
  ((↑p^p - ↑p):ℤ) ≡ (↑(p.choose 1) * ↑(p + 1) * (-1:ℤ)^(p-1) + (-1:ℤ)^p) - ↑p [ZMOD ↑(p+1)^2] := by
  refine Int.ModEq.sub_right (↑p) ?_
  simp
  exact imo_2022_p5_9 p hp5


lemma imo_2022_p5_10_9
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  (gpo : Odd p)
  (gpe : Even (p - 1))
  (g₁ : (-1) ^ (p - 1) = 1)
  (g₂ : (-1) ^ p = -1)
  (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2]) :
  False := by
  have h₂: (p ^ p - p) ≡ (p * (p + 1)) - 1 - p [MOD ((p + 1) ^ 2)] := by
    refine Int.natCast_modEq_iff.mp ?_
    have g₃: p ≤ p^p := by
      refine Nat.le_self_pow (by linarith) _
    rw [Nat.cast_sub g₃]
    have g₄: p ≤ p * (p + 1) - 1 := by
      rw [mul_add]
      simp
      rw [add_comm, Nat.add_sub_assoc]
      simp
      rw [← pow_two]
      refine Nat.one_le_pow 2 p (by linarith)
    rw [Nat.cast_sub g₄]
    have g₅: 1 ≤ p * (p + 1) := by
      rw [← mul_one (p * (p + 1))]
      refine Nat.le_mul_of_pos_left ?_ ?_
      refine Nat.mul_pos (by linarith) (by linarith)
    rw [Nat.cast_sub g₅]
    rw [← sub_eq_add_neg] at h₁
    norm_cast
    norm_cast at h₁
  have h₃: p * (p + 1) - 1 - p = p^2 - 1 := by
    rw [Nat.sub_sub, mul_add]
    simp
    rw [← pow_two]
    exact Nat.add_sub_add_right (p^2) p 1
  rw [h₃] at h₂
  clear h₃ gpo gpe g₁ g₂
  -- now derive a line of contradictions from h₀
  have hc₁: (p ^ p - p) ≡ 0 [MOD (p+1)^2] := by exact modEq_zero_iff_dvd.mpr h₀
  -- mix the contradiction with what we had in h₂
  have h₄: p ^ 2 - 1 ≡ 0 [MOD (p+1)^2] := by
    apply Nat.ModEq.symm at h₂
    exact Nat.ModEq.trans h₂ hc₁
  have h₅: p - 1 ≡ 0 [MOD (p+1)] := by
    rw [pow_two] at h₄
    have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
      rw [mul_comm]
      exact Nat.sq_sub_sq p 1
    simp at g₀
    rw [g₀] at h₄
    have g₁: p + 1 ≠ 0 := by linarith
    refine Nat.ModEq.mul_right_cancel' g₁ ?_
    rw [zero_mul]
    exact h₄
  have h₆: p - 1 ≤ 0 := by
    refine Nat.ModEq.le_of_lt_add h₅ ?_
    simp
    rw [← succ_eq_add_one]
    refine Nat.sub_lt_succ p 1
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]


lemma imo_2022_p5_10_10
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (gpo : Odd p)
  -- (gpe : Even (p - 1))
  -- (g₁ : (-1) ^ (p - 1) = 1)
  -- (g₂ : (-1) ^ p = -1)
  (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2]) :
  p ^ p - p ≡ p * (p + 1) - 1 - p [MOD (p + 1) ^ 2] := by
  refine Int.natCast_modEq_iff.mp ?_
  have g₃: p ≤ p^p := by
    refine Nat.le_self_pow (by linarith) _
  rw [Nat.cast_sub g₃]
  have g₄: p ≤ p * (p + 1) - 1 := by
    rw [mul_add]
    simp
    rw [add_comm, Nat.add_sub_assoc]
    simp
    rw [← pow_two]
    refine Nat.one_le_pow 2 p (by linarith)
  rw [Nat.cast_sub g₄]
  have g₅: 1 ≤ p * (p + 1) := by
    rw [← mul_one (p * (p + 1))]
    refine Nat.le_mul_of_pos_left ?_ ?_
    refine Nat.mul_pos (by linarith) (by linarith)
  rw [Nat.cast_sub g₅]
  rw [← sub_eq_add_neg] at h₁
  norm_cast
  norm_cast at h₁


lemma imo_2022_p5_10_11
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (gpo : Odd p)
  -- (gpe : Even (p - 1))
  -- (g₁ : (-1) ^ (p - 1) = 1)
  -- (g₂ : (-1) ^ p = -1)
  (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2]) :
  ↑(p ^ p - p) ≡ ↑(p * (p + 1) - 1 - p) [ZMOD ↑(((↑p:ℤ) + 1) ^ 2)] := by
  have g₃: p ≤ p^p := by
    refine Nat.le_self_pow (by linarith) _
  rw [Nat.cast_sub g₃]
  have g₄: p ≤ p * (p + 1) - 1 := by
    rw [mul_add]
    simp
    rw [add_comm, Nat.add_sub_assoc]
    simp
    rw [← pow_two]
    refine Nat.one_le_pow 2 p (by linarith)
  rw [Nat.cast_sub g₄]
  have g₅: 1 ≤ p * (p + 1) := by
    rw [← mul_one (p * (p + 1))]
    refine Nat.le_mul_of_pos_left ?_ ?_
    refine Nat.mul_pos (by linarith) (by linarith)
  rw [Nat.cast_sub g₅]
  rw [← sub_eq_add_neg] at h₁
  norm_cast
  norm_cast at h₁


lemma imo_2022_p5_10_12
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (gpo : Odd p)
  -- (gpe : Even (p - 1))
  -- (g₁ : (-1) ^ (p - 1) = 1)
  -- (g₂ : (-1) ^ p = -1)
  (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  (g₃ : p ≤ p ^ p) :
  ↑(p ^ p - p) ≡ ↑(p * (p + 1) - 1 - p) [ZMOD ↑(((↑p:ℤ) + 1) ^ 2)] := by
  have g₄: p ≤ p * (p + 1) - 1 := by
    rw [mul_add]
    simp
    rw [add_comm, Nat.add_sub_assoc]
    simp
    rw [← pow_two]
    refine Nat.one_le_pow 2 p (by linarith)
  rw [Nat.cast_sub g₄]
  have g₅: 1 ≤ p * (p + 1) := by
    rw [← mul_one (p * (p + 1))]
    refine Nat.le_mul_of_pos_left ?_ ?_
    refine Nat.mul_pos (by linarith) (by linarith)
  rw [Nat.cast_sub g₅]
  rw [← sub_eq_add_neg] at h₁
  norm_cast
  norm_cast at h₁


lemma imo_2022_p5_10_13
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (gpo : Odd p)
  -- (gpe : Even (p - 1))
  -- (g₁ : (-1) ^ (p - 1) = 1)
  -- (g₂ : (-1) ^ p = -1)
  (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  (g₃ : p ≤ p ^ p)
  (g₄ : p ≤ p * (p + 1) - 1) :
  p ^ p - p ≡ p * (p + 1) - 1 - p [MOD (p + 1) ^ 2] := by
  refine Int.natCast_modEq_iff.mp ?_
  rw [Nat.cast_sub g₃]
  rw [Nat.cast_sub g₄]
  have g₅: 1 ≤ p * (p + 1) := by
    rw [← mul_one (p * (p + 1))]
    refine Nat.le_mul_of_pos_left ?_ ?_
    refine Nat.mul_pos (by linarith) (by linarith)
  rw [Nat.cast_sub g₅]
  rw [← sub_eq_add_neg] at h₁
  norm_cast
  norm_cast at h₁


lemma imo_2022_p5_10_14
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (gpo : Odd p)
  -- (gpe : Even (p - 1))
  -- (g₁ : (-1) ^ (p - 1) = 1)
  -- (g₂ : (-1) ^ p = -1)
  (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  (g₃ : p ≤ p ^ p) :
  ↑(p ^ p) - ↑p ≡ ↑(p * (p + 1) - 1 - p) [ZMOD ↑(((↑p:ℤ) + 1) ^ 2)] := by
  have g₄: p ≤ p * (p + 1) - 1 := by
    rw [mul_add]
    simp
    rw [add_comm, Nat.add_sub_assoc]
    simp
    rw [← pow_two]
    refine Nat.one_le_pow 2 p (by linarith)
  rw [Nat.cast_sub g₄]
  have g₅: 1 ≤ p * (p + 1) := by
    rw [← mul_one (p * (p + 1))]
    refine Nat.le_mul_of_pos_left ?_ ?_
    refine Nat.mul_pos (by linarith) (by linarith)
  rw [Nat.cast_sub g₅]
  rw [← sub_eq_add_neg] at h₁
  norm_cast
  norm_cast at h₁


lemma imo_2022_p5_10_15
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p) :
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (gpo : Odd p)
  -- (gpe : Even (p - 1))
  -- (g₁ : (-1) ^ (p - 1) = 1)
  -- (g₂ : (-1) ^ p = -1)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (g₃ : p ≤ p ^ p) :
  p ≤ p * (p + 1) - 1 := by
  rw [mul_add]
  simp
  rw [add_comm, Nat.add_sub_assoc]
  simp
  rw [← pow_two]
  refine Nat.one_le_pow 2 p (by linarith)


lemma imo_2022_p5_10_16
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (gpo : Odd p)
  -- (gpe : Even (p - 1))
  -- (g₁ : (-1) ^ (p - 1) = 1)
  -- (g₂ : (-1) ^ p = -1)
  (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  (g₃ : p ≤ p ^ p)
  (g₄ : p ≤ p * (p + 1) - 1) :
  ↑(p ^ p) - ↑p ≡ ↑(p * (p + 1) - 1 - p) [ZMOD ↑(((↑p:ℤ) + 1) ^ 2)] := by
  rw [Nat.cast_sub g₄]
  have g₅: 1 ≤ p * (p + 1) := by
    rw [← mul_one (p * (p + 1))]
    refine Nat.le_mul_of_pos_left ?_ ?_
    refine Nat.mul_pos (by linarith) (by linarith)
  rw [Nat.cast_sub g₅]
  rw [← sub_eq_add_neg] at h₁
  norm_cast
  norm_cast at h₁


lemma imo_2022_p5_10_17
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p) :
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (gpo : Odd p)
  -- (gpe : Even (p - 1))
  -- (g₁ : (-1) ^ (p - 1) = 1)
  -- (g₂ : (-1) ^ p = -1)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (g₃ : p ≤ p ^ p)
  -- (g₄ : p ≤ p * (p + 1) - 1) :
  1 ≤ p * (p + 1) := by
  rw [← mul_one (p * (p + 1))]
  refine Nat.le_mul_of_pos_left ?_ ?_
  refine Nat.mul_pos (by linarith) (by linarith)


lemma imo_2022_p5_10_18
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p) :
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (gpo : Odd p)
  -- (gpe : Even (p - 1))
  -- (g₁ : (-1) ^ (p - 1) = 1)
  -- (g₂ : (-1) ^ p = -1)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (g₃ : p ≤ p ^ p)
  -- (g₄ : p ≤ p * (p + 1) - 1) :
  1 ≤ p * (p + 1) - 27 := by
  have h₂: 6 ≤ (p + 1) := by
    linarith
  have h₃: 5 * 6 ≤ p * (p + 1) := by
    exact Nat.mul_le_mul hp5 h₂
  norm_num at h₃
  have h₄: 30 - 27 ≤ p * (p + 1) - 27 := by
    exact Nat.sub_le_sub_right h₃ 27
  norm_num at h₄
  exact le_trans (by linarith) h₄


lemma imo_2022_p5_10_19
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (gpo : Odd p)
  -- (gpe : Even (p - 1))
  -- (g₁ : (-1) ^ (p - 1) = 1)
  -- (g₂ : (-1) ^ p = -1)
  (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  (g₃ : p ≤ p ^ p)
  (g₄ : p ≤ p * (p + 1) - 1)
  (g₅ : 1 ≤ p * (p + 1)) :
  ↑(p ^ p) - ↑p ≡ ↑(p * (p + 1) - 1) - ↑p [ZMOD ↑(((↑p:ℤ) + 1) ^ 2)] := by
  rw [Nat.cast_sub g₅]
  rw [← sub_eq_add_neg] at h₁
  norm_cast
  norm_cast at h₁


lemma imo_2022_p5_10_20
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  (gpo : Odd p)
  (gpe : Even (p - 1))
  (g₁ : (-1) ^ (p - 1) = 1)
  (g₂ : (-1) ^ p = -1)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  (h₂ : p ^ p - p ≡ p * (p + 1) - 1 - p [MOD (p + 1) ^ 2]) :
  False := by
  have h₃: p * (p + 1) - 1 - p = p^2 - 1 := by
    rw [Nat.sub_sub, mul_add]
    simp
    rw [← pow_two]
    exact Nat.add_sub_add_right (p^2) p 1
  rw [h₃] at h₂
  clear h₃ gpo gpe g₁ g₂
  -- now derive a line of contradictions from h₀
  have hc₁: (p ^ p - p) ≡ 0 [MOD (p+1)^2] := by exact modEq_zero_iff_dvd.mpr h₀
  -- mix the contradiction with what we had in h₂
  have h₄: p ^ 2 - 1 ≡ 0 [MOD (p+1)^2] := by
    apply Nat.ModEq.symm at h₂
    exact Nat.ModEq.trans h₂ hc₁
  have h₅: p - 1 ≡ 0 [MOD (p+1)] := by
    rw [pow_two] at h₄
    have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
      rw [mul_comm]
      exact Nat.sq_sub_sq p 1
    simp at g₀
    rw [g₀] at h₄
    have g₁: p + 1 ≠ 0 := by linarith
    refine Nat.ModEq.mul_right_cancel' g₁ ?_
    rw [zero_mul]
    exact h₄
  have h₆: p - 1 ≤ 0 := by
    refine Nat.ModEq.le_of_lt_add h₅ ?_
    simp
    rw [← succ_eq_add_one]
    refine Nat.sub_lt_succ p 1
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]


lemma imo_2022_p5_10_21
  (p : ℕ) :
  -- (hp : Nat.Prime p)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (gpo : Odd p)
  -- (gpe : Even (p - 1))
  -- (g₁ : (-1) ^ (p - 1) = 1)
  -- (g₂ : (-1) ^ p = -1)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : p ^ p - p ≡ p * (p + 1) - 1 - p [MOD (p + 1) ^ 2]) :
  p * (p + 1) - 1 - p = p ^ 2 - 1 := by
  rw [Nat.sub_sub, mul_add]
  simp
  rw [← pow_two]
  exact Nat.add_sub_add_right (p^2) p 1


lemma imo_2022_p5_10_22
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  (gpo : Odd p)
  (gpe : Even (p - 1))
  (g₁ : (-1) ^ (p - 1) = 1)
  (g₂ : (-1) ^ p = -1)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  (h₂ : p ^ p - p ≡ p * (p + 1) - 1 - p [MOD (p + 1) ^ 2])
  (h₃ : p * (p + 1) - 1 - p = p ^ 2 - 1) :
  False := by
  rw [h₃] at h₂
  clear h₃ gpo gpe g₁ g₂
  -- now derive a line of contradictions from h₀
  have hc₁: (p ^ p - p) ≡ 0 [MOD (p+1)^2] := by exact modEq_zero_iff_dvd.mpr h₀
  -- mix the contradiction with what we had in h₂
  have h₄: p ^ 2 - 1 ≡ 0 [MOD (p+1)^2] := by
    apply Nat.ModEq.symm at h₂
    exact Nat.ModEq.trans h₂ hc₁
  have h₅: p - 1 ≡ 0 [MOD (p+1)] := by
    rw [pow_two] at h₄
    have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
      rw [mul_comm]
      exact Nat.sq_sub_sq p 1
    simp at g₀
    rw [g₀] at h₄
    have g₁: p + 1 ≠ 0 := by linarith
    refine Nat.ModEq.mul_right_cancel' g₁ ?_
    rw [zero_mul]
    exact h₄
  have h₆: p - 1 ≤ 0 := by
    refine Nat.ModEq.le_of_lt_add h₅ ?_
    simp
    rw [← succ_eq_add_one]
    refine Nat.sub_lt_succ p 1
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]


lemma imo_2022_p5_10_23
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  (h₂ : p ^ p - p ≡ p ^ 2 - 1 [MOD (p + 1) ^ 2])
  (hc₁ : p ^ p - p ≡ 0 [MOD (p + 1) ^ 2]) :
  False := by
  -- mix the contradiction with what we had in h₂
  have h₄: p ^ 2 - 1 ≡ 0 [MOD (p+1)^2] := by
    apply Nat.ModEq.symm at h₂
    exact Nat.ModEq.trans h₂ hc₁
  have h₅: p - 1 ≡ 0 [MOD (p+1)] := by
    rw [pow_two] at h₄
    have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
      rw [mul_comm]
      exact Nat.sq_sub_sq p 1
    simp at g₀
    rw [g₀] at h₄
    have g₁: p + 1 ≠ 0 := by linarith
    refine Nat.ModEq.mul_right_cancel' g₁ ?_
    rw [zero_mul]
    exact h₄
  have h₆: p - 1 ≤ 0 := by
    refine Nat.ModEq.le_of_lt_add h₅ ?_
    simp
    rw [← succ_eq_add_one]
    refine Nat.sub_lt_succ p 1
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]


lemma imo_2022_p5_10_24
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  (h₂ : p ^ p - p ≡ p ^ 2 - 1 [MOD (p + 1) ^ 2])
  (hc₁ : p ^ p - p ≡ 0 [MOD (p + 1) ^ 2]) :
  p ^ 2 - 1 ≡ 0 [MOD (p + 1) ^ 2] := by
  apply Nat.ModEq.symm at h₂
  exact Nat.ModEq.trans h₂ hc₁


lemma imo_2022_p5_10_25
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : p ^ p - p ≡ p ^ 2 - 1 [MOD (p + 1) ^ 2])
  -- (hc₁ : p ^ p - p ≡ 0 [MOD (p + 1) ^ 2])
  (h₄ : p ^ 2 - 1 ≡ 0 [MOD (p + 1) ^ 2]) :
  False := by
  have h₅: p - 1 ≡ 0 [MOD (p+1)] := by
    rw [pow_two] at h₄
    have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
      rw [mul_comm]
      exact Nat.sq_sub_sq p 1
    simp at g₀
    rw [g₀] at h₄
    have g₁: p + 1 ≠ 0 := by linarith
    refine Nat.ModEq.mul_right_cancel' g₁ ?_
    rw [zero_mul]
    exact h₄
  have h₆: p - 1 ≤ 0 := by
    refine Nat.ModEq.le_of_lt_add h₅ ?_
    simp
    rw [← succ_eq_add_one]
    refine Nat.sub_lt_succ p 1
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]


lemma imo_2022_p5_10_26
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : p ^ p - p ≡ p ^ 2 - 1 [MOD (p + 1) ^ 2])
  -- (hc₁ : p ^ p - p ≡ 0 [MOD (p + 1) ^ 2])
  (h₄ : p ^ 2 - 1 ≡ 0 [MOD (p + 1) ^ 2]) :
  p - 1 ≡ 0 [MOD p + 1] := by
  rw [pow_two] at h₄
  have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
    rw [mul_comm]
    exact Nat.sq_sub_sq p 1
  simp at g₀
  rw [g₀] at h₄
  have g₁: p + 1 ≠ 0 := by linarith
  refine Nat.ModEq.mul_right_cancel' g₁ ?_
  rw [zero_mul]
  exact h₄


lemma imo_2022_p5_10_27
  (p : ℕ) :
  -- (hp : Nat.Prime p)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : p ^ p - p ≡ p ^ 2 - 1 [MOD (p + 1) ^ 2])
  -- (hc₁ : p ^ p - p ≡ 0 [MOD (p + 1) ^ 2])
  -- (h₄ : p ^ 2 - 1 ≡ 0 [MOD (p + 1) * (p + 1)]) :
  p ^ 2 - 1 ^ 2 = (p - 1) * (p + 1) := by
  rw [mul_comm]
  exact Nat.sq_sub_sq p 1


lemma imo_2022_p5_10_28
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : p ^ p - p ≡ p ^ 2 - 1 [MOD (p + 1) ^ 2])
  -- (hc₁ : p ^ p - p ≡ 0 [MOD (p + 1) ^ 2])
  (h₄ : p ^ 2 - 1 ≡ 0 [MOD (p + 1) * (p + 1)])
  (g₀ : p ^ 2 - 1 ^ 2 = (p - 1) * (p + 1)) :
  p - 1 ≡ 0 [MOD p + 1] := by
  simp at g₀
  rw [g₀] at h₄
  have g₁: p + 1 ≠ 0 := by linarith
  refine Nat.ModEq.mul_right_cancel' g₁ ?_
  rw [zero_mul]
  exact h₄


lemma imo_2022_p5_10_29
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : p ^ p - p ≡ p ^ 2 - 1 [MOD (p + 1) ^ 2])
  -- (hc₁ : p ^ p - p ≡ 0 [MOD (p + 1) ^ 2])
  (h₄ : p ^ 2 - 1 ≡ 0 [MOD (p + 1) ^ 2]) :
  (p - 1) * (p + 1) ≡ 0 [MOD (p + 1) * (p + 1)] := by
  rw [pow_two] at h₄
  have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
    rw [mul_comm]
    exact Nat.sq_sub_sq p 1
  simp at g₀
  rw [g₀] at h₄
  exact h₄


lemma imo_2022_p5_10_30
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : p ^ p - p ≡ p ^ 2 - 1 [MOD (p + 1) ^ 2])
  -- (hc₁ : p ^ p - p ≡ 0 [MOD (p + 1) ^ 2])
  (h₄ : (p - 1) * (p + 1) ≡ 0 [MOD (p + 1) * (p + 1)])
  -- (g₀ : p ^ 2 - 1 = (p - 1) * (p + 1))
  (g₁ : p + 1 ≠ 0) :
  p - 1 ≡ 0 [MOD p + 1] := by
  refine Nat.ModEq.mul_right_cancel' g₁ ?_
  rw [zero_mul]
  exact h₄


lemma imo_2022_p5_10_31
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : p ^ p - p ≡ p ^ 2 - 1 [MOD (p + 1) ^ 2])
  -- (hc₁ : p ^ p - p ≡ 0 [MOD (p + 1) ^ 2])
  -- (h₄ : p ^ 2 - 1 ≡ 0 [MOD (p + 1) ^ 2])
  (h₅ : p - 1 ≡ 0 [MOD p + 1]) :
  False := by
  have h₆: p - 1 ≤ 0 := by
    refine Nat.ModEq.le_of_lt_add h₅ ?_
    simp
    rw [← succ_eq_add_one]
    refine Nat.sub_lt_succ p 1
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]


lemma imo_2022_p5_10_32
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : p ^ p - p ≡ p ^ 2 - 1 [MOD (p + 1) ^ 2])
  -- (hc₁ : p ^ p - p ≡ 0 [MOD (p + 1) ^ 2])
  -- (h₄ : p ^ 2 - 1 ≡ 0 [MOD (p + 1) ^ 2])
  (h₅ : p - 1 ≡ 0 [MOD p + 1]) :
  p - 1 ≤ 0 := by
  refine Nat.ModEq.le_of_lt_add h₅ ?_
  simp
  rw [← succ_eq_add_one]
  refine Nat.sub_lt_succ p 1


lemma imo_2022_p5_10_33
  (p : ℕ) :
  -- (hp : Nat.Prime p)
  -- (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : p ^ p - p ≡ p ^ 2 - 1 [MOD (p + 1) ^ 2])
  -- (hc₁ : p ^ p - p ≡ 0 [MOD (p + 1) ^ 2])
  -- (h₄ : p ^ 2 - 1 ≡ 0 [MOD (p + 1) ^ 2])
  -- (h₅ : p - 1 ≡ 0 [MOD p + 1]) :
  p - 1 < 0 + (p + 1) := by
  simp
  rw [← succ_eq_add_one]
  refine Nat.sub_lt_succ p 1


lemma imo_2022_p5_10_34
  (p : ℕ)
  -- (hp : Nat.Prime p)
  (hp5 : 5 ≤ p)
  -- (h₀ : (p + 1) ^ 2 ∣ p ^ p - p)
  -- (h₁ : ↑p ^ p - ↑p ≡ ↑p * (↑p + 1) + -1 - ↑p [ZMOD (↑p + 1) ^ 2])
  -- (h₂ : p ^ p - p ≡ p ^ 2 - 1 [MOD (p + 1) ^ 2])
  -- (hc₁ : p ^ p - p ≡ 0 [MOD (p + 1) ^ 2])
  -- (h₄ : p ^ 2 - 1 ≡ 0 [MOD (p + 1) ^ 2])
  -- (h₅ : p - 1 ≡ 0 [MOD p + 1])
  (h₆ : p - 1 ≤ 0) :
  False := by
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]






lemma imo_2022_p5_11
  (p: ℕ)
  -- (hp: Nat.Prime p)
  (hpl: 5 ≤ p) :
  (p + p.factorial < p ^ p) := by
  -- induction p using Nat.case_strong_induction_on with n ih,
  refine Nat.le_induction ?_ ?_ p (hpl)
  . exact Nat.lt_of_sub_eq_succ rfl
  . intros n hn h₁
    have h₂: n + 1 + (n + 1).factorial = (n.factorial + 1) * (n + 1) := by
      rw[add_mul, one_mul, Nat.factorial_succ]
      rw [add_comm (n + 1)]
      rw [mul_comm (n + 1)]
    rw [h₂, pow_add, pow_one ]
    refine Nat.mul_lt_mul_of_pos_right ?_ (by linarith)
    have h₅: n ^ n < (n + 1) ^ n := by
      refine Nat.pow_lt_pow_left ?_ ?_
      . exact lt_add_one n
      . refine Nat.ne_of_gt ?_
        linarith
    linarith



lemma imo_2022_p5_11_1 :
  -- (p : ℕ)
  -- (hpl : 5 ≤ p) :
  ∀ (n : ℕ), 5 ≤ n → n + n ! < n ^ n → n + 1 + (n + 1)! < (n + 1) ^ (n + 1) := by
  intros n hn h₁
  have h₂: n + 1 + (n + 1).factorial = (n.factorial + 1) * (n + 1) := by
    rw[add_mul, one_mul, Nat.factorial_succ]
    rw [add_comm (n + 1)]
    rw [mul_comm (n + 1)]
  rw [h₂, pow_add, pow_one ]
  refine Nat.mul_lt_mul_of_pos_right ?_ (by linarith)
  have h₅: n ^ n < (n + 1) ^ n := by
    refine Nat.pow_lt_pow_left ?_ ?_
    . exact lt_add_one n
    . refine Nat.ne_of_gt ?_
      linarith
  linarith


lemma imo_2022_p5_11_2
  -- (p : ℕ)
  -- (hpl : 5 ≤ p)
  (n : ℕ)
  (hn : 5 ≤ n)
  (h₁ : n + n ! < n ^ n) :
  n + 1 + (n + 1)! < (n + 1) ^ (n + 1) := by
  have h₂: n + 1 + (n + 1).factorial = (n.factorial + 1) * (n + 1) := by
    rw[add_mul, one_mul, Nat.factorial_succ]
    rw [add_comm (n + 1)]
    rw [mul_comm (n + 1)]
  rw [h₂, pow_add, pow_one ]
  refine Nat.mul_lt_mul_of_pos_right ?_ (by linarith)
  have h₅: n ^ n < (n + 1) ^ n := by
    refine Nat.pow_lt_pow_left ?_ ?_
    . exact lt_add_one n
    . refine Nat.ne_of_gt ?_
      linarith
  linarith


lemma imo_2022_p5_11_3
  -- (p : ℕ)
  -- (hpl : 5 ≤ p)
  (n : ℕ) :
  -- (hn : 5 ≤ n)
  -- (h₁ : n + n ! < n ^ n) :
  n + 1 + (n + 1)! = (n ! + 1) * (n + 1) := by
  rw[add_mul, one_mul, Nat.factorial_succ]
  rw [add_comm (n + 1)]
  rw [mul_comm (n + 1)]


lemma imo_2022_p5_11_4
  -- (p : ℕ)
  -- (hpl : 5 ≤ p)
  (n : ℕ)
  (hn : 5 ≤ n)
  (h₁ : n + n ! < n ^ n)
  (h₂ : n + 1 + (n + 1)! = (n ! + 1) * (n + 1)) :
  n + 1 + (n + 1)! < (n + 1) ^ (n + 1) := by
  rw [h₂, pow_add, pow_one ]
  refine Nat.mul_lt_mul_of_pos_right ?_ (by linarith)
  have h₅: n ^ n < (n + 1) ^ n := by
    refine Nat.pow_lt_pow_left ?_ ?_
    . exact lt_add_one n
    . refine Nat.ne_of_gt ?_
      linarith
  linarith


lemma imo_2022_p5_11_5
  -- (p : ℕ)
  -- (hpl : 5 ≤ p)
  (n : ℕ)
  (hn : 5 ≤ n)
  (h₁ : n + n ! < n ^ n) :
  -- (h₂ : n + 1 + (n + 1)! = (n ! + 1) * (n + 1)) :
  n ! + 1 < (n + 1) ^ n := by
  have h₅: n ^ n < (n + 1) ^ n := by
    refine Nat.pow_lt_pow_left ?_ ?_
    . exact lt_add_one n
    . refine Nat.ne_of_gt ?_
      linarith
  linarith


lemma imo_2022_p5_11_6
  -- (p : ℕ)
  -- (hpl : 5 ≤ p)
  (n : ℕ)
  (hn : 5 ≤ n)
  -- (h₁ : n + n ! < n ^ n)
  -- (h₂ : n + 1 + (n + 1)! = (n ! + 1) * (n + 1))
  (h₄ : n + n ! < n ^ n) :
  n ! + 1 < (n + 1) ^ n := by
  have h₅: n ^ n < (n + 1) ^ n := by
    refine Nat.pow_lt_pow_left ?_ ?_
    . exact lt_add_one n
    . refine Nat.ne_of_gt ?_
      linarith
  linarith


lemma imo_2022_p5_11_7
  -- (p : ℕ)
  -- (hpl : 5 ≤ p)
  (n : ℕ)
  (hn : 5 ≤ n) :
  -- (h₁ : n + n ! < n ^ n)
  -- (h₂ : n + 1 + (n + 1)! = (n ! + 1) * (n + 1))
  -- (h₄ : n + n ! < n ^ n) :
  n ^ n < (n + 1) ^ n := by
  refine Nat.pow_lt_pow_left ?_ ?_
  . exact lt_add_one n
  . refine Nat.ne_of_gt ?_
    linarith




lemma imo_2022_p5_12
  (b p: ℕ)
  (hp: Nat.Prime p)
  (hbp: p ≤ b)
  (h₁: p ^ p = b.factorial + p)
  (hp5: 5 ≤ p) :
  (False) := by
  -- first prove that b = p cannot be
  by_cases h₄: b = p
  . exfalso
    rw [h₄] at h₁
    have h₅: p + p.factorial < p^p := by exact imo_2022_p5_11 p hp5
    linarith
  . have hpb: p < b := by exact lt_of_le_of_ne' hbp h₄
    clear hbp h₄
    have h₂: (p + 1) ^ 2 ∣ b.factorial := by
      have g₁: p + 1 ≤ b := by exact succ_le_iff.mpr hpb
      have g₂: 2 ∣ (p + 1) := by
        have gg₁: Odd p := by
          refine hp.odd_of_ne_two ?_
          linarith
        have gg₂: Even (p + 1) := by
          refine gg₁.add_odd ?_
          norm_num
        exact even_iff_two_dvd.mp gg₂
      have g₃: 2 * ((p+1)/2) * (p + 1) ∣ b.factorial := by
        have gg₁: (p + 1).factorial ∣ b.factorial := by exact Nat.factorial_dvd_factorial g₁
        have gg₂: (p + 1).factorial = (p + 1) * p.factorial := by exact factorial_succ p
        rw [mul_comm] at gg₂
        have gg₃: 6/2 ≤ (p + 1)/2 := by
          refine Nat.div_le_div_right ?_
          linarith
        norm_num at gg₃
        have gg₄: 2 + (p+1)/2 ≤ p := by
          -- strong induction
          refine Nat.le_induction ?_ ?_ p (hp5)
          . norm_num
          . intros n _ h₂
            ring_nf
            have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
              rw [← succ_eq_add_one]
              refine Nat.succ_le_succ ?_
              refine Nat.div_le_div_right ?_
              linarith
            simp
            nth_rewrite 1 [← mul_one 2]
            rw [Nat.two_mul 1, add_assoc]
            refine Nat.add_le_add_left ?_ 1
            refine le_trans ?_ h₂
            rw [add_comm 2 _]
            nth_rewrite 3 [← mul_one 2]
            rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
            exact Nat.add_le_add_right ggg₁ 1
        have gg₅: (2+(p+1)/2).factorial ∣ p.factorial := by
          exact factorial_dvd_factorial gg₄
        have gg₆: (2:ℕ).factorial * ((p+1)/2).factorial ∣ p.factorial := by
          refine dvd_trans ?_ gg₅
          exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)
        have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
          refine dvd_trans ?_ gg₆
          simp
          refine mul_dvd_mul_left 2 ?_
          refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
        have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
          refine mul_dvd_mul_right ?_ (p + 1)
          exact gg₇
        rw [gg₂] at gg₁
        exact dvd_trans gg₈ gg₁
      have g₄: 2 * ((p+1)/2) = (p + 1) := by
        exact Nat.mul_div_cancel' g₂
      rw [g₄] at g₃
      ring_nf at *
      exact g₃
    have h₃: b.factorial = p ^ p - p := by exact eq_tsub_of_add_eq (h₁.symm)
    rw [h₃] at h₂
    exact imo_2022_p5_10 p hp hp5 h₂


lemma imo_2022_p5_12_1
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (hbp : p ≤ b)
  (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p)
  (h₄ : b = p) :
  False := by
  rw [h₄] at h₁
  have h₅: p + p.factorial < p ^ p := by exact imo_2022_p5_11 p hp5
  linarith


lemma imo_2022_p5_12_2
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (hbp : p ≤ b)
  (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p)
  (h₄ : b = p)
  (h₅ : p + p ! < p ^ p) :
  False := by
  rw [h₄] at h₁
  linarith


lemma imo_2022_p5_12_3
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (hbp : p ≤ b)
  (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  (h₄ : b = p)
  (h₅ : p + p ! < p ^ p) :
  False := by
  rw [h₁, add_comm, h₄] at h₅
  apply Nat.add_lt_add_iff_right.mp at h₅
  linarith


lemma imo_2022_p5_12_4
  (b p : ℕ)
  (hp : Nat.Prime p)
  (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p)
  (hpb : p < b) :
  False := by
  have h₂: (p + 1) ^ 2 ∣ b.factorial := by
    have g₁: p + 1 ≤ b := by exact succ_le_iff.mpr hpb
    have g₂: 2 ∣ (p + 1) := by
      have gg₁: Odd p := by
        refine hp.odd_of_ne_two ?_
        linarith
      have gg₂: Even (p + 1) := by
        refine gg₁.add_odd ?_
        norm_num
      exact even_iff_two_dvd.mp gg₂
    have g₃: 2 * ((p+1)/2) * (p + 1) ∣ b.factorial := by
      have gg₁: (p + 1).factorial ∣ b.factorial := by exact Nat.factorial_dvd_factorial g₁
      have gg₂: (p + 1).factorial = (p + 1) * p.factorial := by exact factorial_succ p
      rw [mul_comm] at gg₂
      have gg₃: 6/2 ≤ (p + 1)/2 := by
        refine Nat.div_le_div_right ?_
        linarith
      norm_num at gg₃
      have gg₄: 2 + (p+1)/2 ≤ p := by
        -- strong induction
        refine Nat.le_induction ?_ ?_ p (hp5)
        . norm_num
        . intros n _ h₂
          ring_nf
          have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
            rw [← succ_eq_add_one]
            refine Nat.succ_le_succ ?_
            refine Nat.div_le_div_right ?_
            linarith
          simp
          nth_rewrite 1 [← mul_one 2]
          rw [Nat.two_mul 1, add_assoc]
          refine Nat.add_le_add_left ?_ 1
          refine le_trans ?_ h₂
          rw [add_comm 2 _]
          nth_rewrite 3 [← mul_one 2]
          rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
          exact Nat.add_le_add_right ggg₁ 1
      have gg₅: (2+(p+1)/2).factorial ∣ p.factorial := by
        exact factorial_dvd_factorial gg₄
      have gg₆: (2:ℕ).factorial * ((p+1)/2).factorial ∣ p.factorial := by
        refine dvd_trans ?_ gg₅
        exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)
      have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
        refine dvd_trans ?_ gg₆
        simp
        refine mul_dvd_mul_left 2 ?_
        refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
      have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
        refine mul_dvd_mul_right ?_ (p + 1)
        exact gg₇
      rw [gg₂] at gg₁
      exact dvd_trans gg₈ gg₁
    have g₄: 2 * ((p+1)/2) = (p + 1) := by
      exact Nat.mul_div_cancel' g₂
    rw [g₄] at g₃
    ring_nf at *
    exact g₃
  have h₃: b.factorial = p ^ p - p := by exact eq_tsub_of_add_eq (h₁.symm)
  rw [h₃] at h₂
  exact imo_2022_p5_10 p hp hp5 h₂


lemma imo_2022_p5_12_5
  (b p : ℕ)
  (hp : Nat.Prime p)
  (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p)
  (hpb : p < b) :
  (p + 1) ^ 2 ∣ b ! := by
  have g₁: p + 1 ≤ b := by exact succ_le_iff.mpr hpb
  have g₂: 2 ∣ (p + 1) := by
    have gg₁: Odd p := by
      refine hp.odd_of_ne_two ?_
      linarith
    have gg₂: Even (p + 1) := by
      refine gg₁.add_odd ?_
      norm_num
    exact even_iff_two_dvd.mp gg₂
  have g₃: 2 * ((p+1)/2) * (p + 1) ∣ b.factorial := by
    have gg₁: (p + 1).factorial ∣ b.factorial := by exact Nat.factorial_dvd_factorial g₁
    have gg₂: (p + 1).factorial = (p + 1) * p.factorial := by exact factorial_succ p
    rw [mul_comm] at gg₂
    have gg₃: 6/2 ≤ (p + 1)/2 := by
      refine Nat.div_le_div_right ?_
      linarith
    norm_num at gg₃
    have gg₄: 2 + (p+1)/2 ≤ p := by
      -- strong induction
      refine Nat.le_induction ?_ ?_ p (hp5)
      . norm_num
      . intros n _ h₂
        ring_nf
        have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
          rw [← succ_eq_add_one]
          refine Nat.succ_le_succ ?_
          refine Nat.div_le_div_right ?_
          linarith
        simp
        nth_rewrite 1 [← mul_one 2]
        rw [Nat.two_mul 1, add_assoc]
        refine Nat.add_le_add_left ?_ 1
        refine le_trans ?_ h₂
        rw [add_comm 2 _]
        nth_rewrite 3 [← mul_one 2]
        rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
        exact Nat.add_le_add_right ggg₁ 1
    have gg₅: (2+(p+1)/2).factorial ∣ p.factorial := by
      exact factorial_dvd_factorial gg₄
    have gg₆: (2:ℕ).factorial * ((p+1)/2).factorial ∣ p.factorial := by
      refine dvd_trans ?_ gg₅
      exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)
    have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
      refine dvd_trans ?_ gg₆
      simp
      refine mul_dvd_mul_left 2 ?_
      refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
    have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
      refine mul_dvd_mul_right ?_ (p + 1)
      exact gg₇
    rw [gg₂] at gg₁
    exact dvd_trans gg₈ gg₁
  have g₄: 2 * ((p+1)/2) = (p + 1) := by
    exact Nat.mul_div_cancel' g₂
  rw [g₄] at g₃
  ring_nf at *
  exact g₃


lemma imo_2022_p5_12_6
  (b p : ℕ)
  (hp : Nat.Prime p)
  (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  (g₁ : p + 1 ≤ b) :
  (p + 1) ^ 2 ∣ b ! := by
  have g₂: 2 ∣ (p + 1) := by
    have gg₁: Odd p := by
      refine hp.odd_of_ne_two ?_
      linarith
    have gg₂: Even (p + 1) := by
      refine gg₁.add_odd ?_
      norm_num
    exact even_iff_two_dvd.mp gg₂
  have g₃: 2 * ((p+1)/2) * (p + 1) ∣ b.factorial := by
    have gg₁: (p + 1).factorial ∣ b.factorial := by exact Nat.factorial_dvd_factorial g₁
    have gg₂: (p + 1).factorial = (p + 1) * p.factorial := by exact factorial_succ p
    rw [mul_comm] at gg₂
    have gg₃: 6/2 ≤ (p + 1)/2 := by
      refine Nat.div_le_div_right ?_
      linarith
    norm_num at gg₃
    have gg₄: 2 + (p+1)/2 ≤ p := by
      -- strong induction
      refine Nat.le_induction ?_ ?_ p (hp5)
      . norm_num
      . intros n _ h₂
        ring_nf
        have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
          rw [← succ_eq_add_one]
          refine Nat.succ_le_succ ?_
          refine Nat.div_le_div_right ?_
          linarith
        simp
        nth_rewrite 1 [← mul_one 2]
        rw [Nat.two_mul 1, add_assoc]
        refine Nat.add_le_add_left ?_ 1
        refine le_trans ?_ h₂
        rw [add_comm 2 _]
        nth_rewrite 3 [← mul_one 2]
        rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
        exact Nat.add_le_add_right ggg₁ 1
    have gg₅: (2+(p+1)/2).factorial ∣ p.factorial := by
      exact factorial_dvd_factorial gg₄
    have gg₆: (2:ℕ).factorial * ((p+1)/2).factorial ∣ p.factorial := by
      refine dvd_trans ?_ gg₅
      exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)
    have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
      refine dvd_trans ?_ gg₆
      simp
      refine mul_dvd_mul_left 2 ?_
      refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
    have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
      refine mul_dvd_mul_right ?_ (p + 1)
      exact gg₇
    rw [gg₂] at gg₁
    exact dvd_trans gg₈ gg₁
  have g₄: 2 * ((p+1)/2) = (p + 1) := by
    exact Nat.mul_div_cancel' g₂
  rw [g₄] at g₃
  ring_nf at *
  exact g₃


lemma imo_2022_p5_12_7
  -- (b : ℕ)
  (p : ℕ)
  (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p) :
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b) :
  2 ∣ p + 1 := by
  have gg₁: Odd p := by
    refine hp.odd_of_ne_two ?_
    linarith
  have gg₂: Even (p + 1) := by
    refine gg₁.add_odd ?_
    norm_num
  exact even_iff_two_dvd.mp gg₂


lemma imo_2022_p5_12_8
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  (g₁ : p + 1 ≤ b)
  (g₂ : 2 ∣ p + 1) :
  (p + 1) ^ 2 ∣ b ! := by
  have g₃: 2 * ((p+1)/2) * (p + 1) ∣ b.factorial := by
    have gg₁: (p + 1).factorial ∣ b.factorial := by exact Nat.factorial_dvd_factorial g₁
    have gg₂: (p + 1).factorial = (p + 1) * p.factorial := by exact factorial_succ p
    rw [mul_comm] at gg₂
    have gg₃: 6/2 ≤ (p + 1)/2 := by
      refine Nat.div_le_div_right ?_
      linarith
    norm_num at gg₃
    have gg₄: 2 + (p+1)/2 ≤ p := by
      -- strong induction
      refine Nat.le_induction ?_ ?_ p (hp5)
      . norm_num
      . intros n _ h₂
        ring_nf
        have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
          rw [← succ_eq_add_one]
          refine Nat.succ_le_succ ?_
          refine Nat.div_le_div_right ?_
          linarith
        simp
        nth_rewrite 1 [← mul_one 2]
        rw [Nat.two_mul 1, add_assoc]
        refine Nat.add_le_add_left ?_ 1
        refine le_trans ?_ h₂
        rw [add_comm 2 _]
        nth_rewrite 3 [← mul_one 2]
        rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
        exact Nat.add_le_add_right ggg₁ 1
    have gg₅: (2+(p+1)/2).factorial ∣ p.factorial := by
      exact factorial_dvd_factorial gg₄
    have gg₆: (2:ℕ).factorial * ((p+1)/2).factorial ∣ p.factorial := by
      refine dvd_trans ?_ gg₅
      exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)
    have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
      refine dvd_trans ?_ gg₆
      simp
      refine mul_dvd_mul_left 2 ?_
      refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
    have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
      refine mul_dvd_mul_right ?_ (p + 1)
      exact gg₇
    rw [gg₂] at gg₁
    exact dvd_trans gg₈ gg₁
  have g₄: 2 * ((p+1)/2) = (p + 1) := by
    exact Nat.mul_div_cancel' g₂
  rw [g₄] at g₃
  ring_nf at *
  exact g₃


lemma imo_2022_p5_12_9
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  (g₁ : p + 1 ≤ b) :
  -- (g₂ : 2 ∣ p + 1) :
  2 * ((p + 1) / 2) * (p + 1) ∣ b ! := by
  have gg₁: (p + 1).factorial ∣ b.factorial := by exact Nat.factorial_dvd_factorial g₁
  have gg₂: (p + 1).factorial = (p + 1) * p.factorial := by exact factorial_succ p
  rw [mul_comm] at gg₂
  have gg₃: 6/2 ≤ (p + 1)/2 := by
    refine Nat.div_le_div_right ?_
    linarith
  norm_num at gg₃
  have gg₄: 2 + (p+1)/2 ≤ p := by
    -- strong induction
    refine Nat.le_induction ?_ ?_ p (hp5)
    . norm_num
    . intros n _ h₂
      ring_nf
      have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
        rw [← succ_eq_add_one]
        refine Nat.succ_le_succ ?_
        refine Nat.div_le_div_right ?_
        linarith
      simp
      nth_rewrite 1 [← mul_one 2]
      rw [Nat.two_mul 1, add_assoc]
      refine Nat.add_le_add_left ?_ 1
      refine le_trans ?_ h₂
      rw [add_comm 2 _]
      nth_rewrite 3 [← mul_one 2]
      rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
      exact Nat.add_le_add_right ggg₁ 1
  have gg₅: (2+(p+1)/2).factorial ∣ p.factorial := by
    exact factorial_dvd_factorial gg₄
  have gg₆: (2:ℕ).factorial * ((p+1)/2).factorial ∣ p.factorial := by
    refine dvd_trans ?_ gg₅
    exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)
  have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
    refine dvd_trans ?_ gg₆
    simp
    refine mul_dvd_mul_left 2 ?_
    refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
  have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
    refine mul_dvd_mul_right ?_ (p + 1)
    exact gg₇
  rw [gg₂] at gg₁
  exact dvd_trans gg₈ gg₁


lemma imo_2022_p5_12_10
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  (gg₁ : (p + 1)! ∣ b !) :
  2 * ((p + 1) / 2) * (p + 1) ∣ b ! := by
  have gg₂: (p + 1).factorial = (p + 1) * p.factorial := by exact factorial_succ p
  rw [mul_comm] at gg₂
  have gg₃: 6/2 ≤ (p + 1)/2 := by
    refine Nat.div_le_div_right ?_
    linarith
  norm_num at gg₃
  have gg₄: 2 + (p+1)/2 ≤ p := by
    -- strong induction
    refine Nat.le_induction ?_ ?_ p (hp5)
    . norm_num
    . intros n _ h₂
      ring_nf
      have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
        rw [← succ_eq_add_one]
        refine Nat.succ_le_succ ?_
        refine Nat.div_le_div_right ?_
        linarith
      simp
      nth_rewrite 1 [← mul_one 2]
      rw [Nat.two_mul 1, add_assoc]
      refine Nat.add_le_add_left ?_ 1
      refine le_trans ?_ h₂
      rw [add_comm 2 _]
      nth_rewrite 3 [← mul_one 2]
      rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
      exact Nat.add_le_add_right ggg₁ 1
  have gg₅: (2+(p+1)/2).factorial ∣ p.factorial := by
    exact factorial_dvd_factorial gg₄
  have gg₆: (2:ℕ).factorial * ((p+1)/2).factorial ∣ p.factorial := by
    refine dvd_trans ?_ gg₅
    exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)
  have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
    refine dvd_trans ?_ gg₆
    simp
    refine mul_dvd_mul_left 2 ?_
    refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
  have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
    refine mul_dvd_mul_right ?_ (p + 1)
    exact gg₇
  rw [gg₂] at gg₁
  exact dvd_trans gg₈ gg₁


lemma imo_2022_p5_12_11
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  (gg₁ : (p + 1)! ∣ b !)
  (gg₂ : (p + 1)! = (p + 1) * p !) :
  2 * ((p + 1) / 2) * (p + 1) ∣ b ! := by
  rw [mul_comm] at gg₂
  have gg₃: 6/2 ≤ (p + 1)/2 := by
    refine Nat.div_le_div_right ?_
    linarith
  norm_num at gg₃
  have gg₄: 2 + (p+1)/2 ≤ p := by
    -- strong induction
    refine Nat.le_induction ?_ ?_ p (hp5)
    . norm_num
    . intros n _ h₂
      ring_nf
      have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
        rw [← succ_eq_add_one]
        refine Nat.succ_le_succ ?_
        refine Nat.div_le_div_right ?_
        linarith
      simp
      nth_rewrite 1 [← mul_one 2]
      rw [Nat.two_mul 1, add_assoc]
      refine Nat.add_le_add_left ?_ 1
      refine le_trans ?_ h₂
      rw [add_comm 2 _]
      nth_rewrite 3 [← mul_one 2]
      rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
      exact Nat.add_le_add_right ggg₁ 1
  have gg₅: (2+(p+1)/2).factorial ∣ p.factorial := by
    exact factorial_dvd_factorial gg₄
  have gg₆: (2:ℕ).factorial * ((p+1)/2).factorial ∣ p.factorial := by
    refine dvd_trans ?_ gg₅
    exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)
  have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
    refine dvd_trans ?_ gg₆
    simp
    refine mul_dvd_mul_left 2 ?_
    refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
  have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
    refine mul_dvd_mul_right ?_ (p + 1)
    exact gg₇
  rw [gg₂] at gg₁
  exact dvd_trans gg₈ gg₁


lemma imo_2022_p5_12_12
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  (gg₁ : (p + 1)! ∣ b !)
  (gg₂ : (p + 1)! = p ! * (p + 1))
  (gg₃ : 3 ≤ (p + 1) / 2) :
  2 * ((p + 1) / 2) * (p + 1) ∣ b ! := by
  have gg₄: 2 + (p+1)/2 ≤ p := by
    -- strong induction
    refine Nat.le_induction ?_ ?_ p (hp5)
    . norm_num
    . intros n _ h₂
      ring_nf
      have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
        rw [← succ_eq_add_one]
        refine Nat.succ_le_succ ?_
        refine Nat.div_le_div_right ?_
        linarith
      simp
      nth_rewrite 1 [← mul_one 2]
      rw [Nat.two_mul 1, add_assoc]
      refine Nat.add_le_add_left ?_ 1
      refine le_trans ?_ h₂
      rw [add_comm 2 _]
      nth_rewrite 3 [← mul_one 2]
      rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
      exact Nat.add_le_add_right ggg₁ 1
  have gg₅: (2+(p+1)/2).factorial ∣ p.factorial := by
    exact factorial_dvd_factorial gg₄
  have gg₆: (2:ℕ).factorial * ((p+1)/2).factorial ∣ p.factorial := by
    refine dvd_trans ?_ gg₅
    exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)
  have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
    refine dvd_trans ?_ gg₆
    simp
    refine mul_dvd_mul_left 2 ?_
    refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
  have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
    refine mul_dvd_mul_right ?_ (p + 1)
    exact gg₇
  rw [gg₂] at gg₁
  exact dvd_trans gg₈ gg₁


lemma imo_2022_p5_12_13
  -- (b : ℕ)
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p) :
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  -- (gg₁ : (p + 1)! ∣ b !)
  -- (gg₂ : (p + 1)! = p ! * (p + 1))
  -- (gg₃ : 3 ≤ (p + 1) / 2) :
  2 + (p + 1) / 2 ≤ p := by
  refine Nat.le_induction ?_ ?_ p (hp5)
  . norm_num
  . intros n _ h₂
    ring_nf
    have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
      rw [← succ_eq_add_one]
      refine Nat.succ_le_succ ?_
      refine Nat.div_le_div_right ?_
      linarith
    simp
    nth_rewrite 1 [← mul_one 2]
    rw [Nat.two_mul 1, add_assoc]
    refine Nat.add_le_add_left ?_ 1
    refine le_trans ?_ h₂
    rw [add_comm 2 _]
    nth_rewrite 3 [← mul_one 2]
    rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
    exact Nat.add_le_add_right ggg₁ 1


lemma imo_2022_p5_12_14 :
  -- (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  -- (gg₁ : (p + 1)! ∣ b !)
  -- (gg₂ : (p + 1)! = p ! * (p + 1))
  -- (gg₃ : 3 ≤ (p + 1) / 2) :
  ∀ (n : ℕ), 5 ≤ n → 2 + (n + 1) / 2 ≤ n → 2 + (n + 1 + 1) / 2 ≤ n + 1 := by
  intros n _ h₂
  ring_nf
  have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
    rw [← succ_eq_add_one]
    refine Nat.succ_le_succ ?_
    refine Nat.div_le_div_right ?_
    linarith
  simp
  nth_rewrite 1 [← mul_one 2]
  rw [Nat.two_mul 1, add_assoc]
  refine Nat.add_le_add_left ?_ 1
  refine le_trans ?_ h₂
  rw [add_comm 2 _]
  nth_rewrite 3 [← mul_one 2]
  rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
  exact Nat.add_le_add_right ggg₁ 1


lemma imo_2022_p5_12_15
  -- (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  -- (gg₁ : (p + 1)! ∣ b !)
  -- (gg₂ : (p + 1)! = p ! * (p + 1))
  -- (gg₃ : 3 ≤ (p + 1) / 2)
  (n : ℕ)
  -- (hmn : 5 ≤ n)
  (h₂ : 2 + (n + 1) / 2 ≤ n) :
  2 + (2 + n) / 2 ≤ 1 + n := by
  ring_nf
  have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
    rw [← succ_eq_add_one]
    refine Nat.succ_le_succ ?_
    refine Nat.div_le_div_right ?_
    linarith
  simp
  nth_rewrite 1 [← mul_one 2]
  rw [Nat.two_mul 1, add_assoc]
  refine Nat.add_le_add_left ?_ 1
  refine le_trans ?_ h₂
  rw [add_comm 2 _]
  nth_rewrite 3 [← mul_one 2]
  rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
  exact Nat.add_le_add_right ggg₁ 1


lemma imo_2022_p5_12_16
  -- (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  -- (gg₁ : (p + 1)! ∣ b !)
  -- (gg₂ : (p + 1)! = p ! * (p + 1))
  -- (gg₃ : 3 ≤ (p + 1) / 2)
  (n : ℕ) :
  -- (hmn : 5 ≤ n)
  -- (h₂ : 2 + (n + 1) / 2 ≤ n) :
  succ (n / 2) ≤ (n + 1) / 2 + 1 := by
  rw [← succ_eq_add_one]
  refine Nat.succ_le_succ ?_
  refine Nat.div_le_div_right ?_
  linarith


lemma imo_2022_p5_12_17
  -- (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  -- (gg₁ : (p + 1)! ∣ b !)
  -- (gg₂ : (p + 1)! = p ! * (p + 1))
  -- (gg₃ : 3 ≤ (p + 1) / 2)
  (n : ℕ)
  -- (hmn : 5 ≤ n)
  (h₂ : 2 + (n + 1) / 2 ≤ n)
  (ggg₁ : succ (n / 2) ≤ (n + 1) / 2 + 1) :
  2 + succ (n / 2) ≤ 1 + n := by
  nth_rewrite 1 [← mul_one 2]
  rw [Nat.two_mul 1, add_assoc]
  refine Nat.add_le_add_left ?_ 1
  refine le_trans ?_ h₂
  rw [add_comm 2 _]
  nth_rewrite 3 [← mul_one 2]
  rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
  exact Nat.add_le_add_right ggg₁ 1


lemma imo_2022_p5_12_18
  -- (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  -- (gg₁ : (p + 1)! ∣ b !)
  -- (gg₂ : (p + 1)! = p ! * (p + 1))
  -- (gg₃ : 3 ≤ (p + 1) / 2)
  (n : ℕ)
  -- (hmn : 5 ≤ n)
  (h₂ : 2 + (n + 1) / 2 ≤ n)
  (ggg₁ : succ (n / 2) ≤ (n + 1) / 2 + 1) :
  1 + succ (n / 2) ≤ n := by
  refine le_trans ?_ h₂
  rw [add_comm 2 _]
  nth_rewrite 3 [← mul_one 2]
  rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
  exact Nat.add_le_add_right ggg₁ 1


lemma imo_2022_p5_12_19
  -- (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  -- (gg₁ : (p + 1)! ∣ b !)
  -- (gg₂ : (p + 1)! = p ! * (p + 1))
  -- (gg₃ : 3 ≤ (p + 1) / 2)
  (n : ℕ)
  -- (hmn : 5 ≤ n)
  (h₂ : 2 + (n + 1) / 2 ≤ n)
  -- (ggg₁ : succ (n / 2) ≤ (n + 1) / 2 + 1)
  (g₃ : 1 + succ (n / 2) ≤ (n + 1) / 2 + 2 * 1) :
  1 + succ (n / 2) ≤ n := by
  refine le_trans ?_ h₂
  rw [add_comm 2 _]
  nth_rewrite 3 [← mul_one 2]
  rw [Nat.two_mul 1, ← add_assoc]
  exact g₃


lemma imo_2022_p5_12_20
  -- (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  -- (gg₁ : (p + 1)! ∣ b !)
  -- (gg₂ : (p + 1)! = p ! * (p + 1))
  -- (gg₃ : 3 ≤ (p + 1) / 2)
  (n : ℕ)
  -- (hmn : 5 ≤ n)
  -- (h₂ : 2 + (n + 1) / 2 ≤ n)
  (ggg₁ : succ (n / 2) ≤ (n + 1) / 2 + 1) :
  1 + succ (n / 2) ≤ (n + 1) / 2 + 2 := by
  nth_rewrite 3 [← mul_one 2]
  rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
  exact Nat.add_le_add_right ggg₁ 1


lemma imo_2022_p5_12_21
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  (gg₁ : (p + 1)! ∣ b !)
  (gg₂ : (p + 1)! = p ! * (p + 1))
  (gg₃ : 3 ≤ (p + 1) / 2)
  (gg₄ : 2 + (p + 1) / 2 ≤ p) :
  2 * ((p + 1) / 2) * (p + 1) ∣ b ! := by
  have gg₅: (2+(p+1)/2).factorial ∣ p.factorial := by
    exact factorial_dvd_factorial gg₄
  have gg₆: (2:ℕ).factorial * ((p+1)/2).factorial ∣ p.factorial := by
    refine dvd_trans ?_ gg₅
    exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)
  have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
    refine dvd_trans ?_ gg₆
    simp
    refine mul_dvd_mul_left 2 ?_
    refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
  have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
    refine mul_dvd_mul_right ?_ (p + 1)
    exact gg₇
  rw [gg₂] at gg₁
  exact dvd_trans gg₈ gg₁


lemma imo_2022_p5_12_22
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  (gg₁ : (p + 1)! ∣ b !)
  (gg₂ : (p + 1)! = p ! * (p + 1))
  (gg₃ : 3 ≤ (p + 1) / 2)
  (gg₄ : 2 + (p + 1) / 2 ≤ p)
  (gg₅ : (2 + (p + 1) / 2)! ∣ p !) :
  2 * ((p + 1) / 2) * (p + 1) ∣ b ! := by
  have gg₆: (2:ℕ).factorial * ((p+1)/2).factorial ∣ p.factorial := by
    refine dvd_trans ?_ gg₅
    exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)
  have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
    refine dvd_trans ?_ gg₆
    simp
    refine mul_dvd_mul_left 2 ?_
    refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
  have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
    refine mul_dvd_mul_right ?_ (p + 1)
    exact gg₇
  rw [gg₂] at gg₁
  exact dvd_trans gg₈ gg₁


lemma imo_2022_p5_12_23
  -- (b : ℕ)
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  -- (gg₁ : (p + 1)! ∣ b !)
  -- (gg₂ : (p + 1)! = p ! * (p + 1))
  -- (gg₃ : 3 ≤ (p + 1) / 2)
  -- (gg₄ : 2 + (p + 1) / 2 ≤ p)
  (gg₅ : (2 + (p + 1) / 2)! ∣ p !) :
  2! * ((p + 1) / 2)! ∣ p ! := by
  refine dvd_trans ?_ gg₅
  exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)


lemma imo_2022_p5_12_24
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  (gg₁ : (p + 1)! ∣ b !)
  (gg₂ : (p + 1)! = p ! * (p + 1))
  (gg₃ : 3 ≤ (p + 1) / 2)
  (gg₄ : 2 + (p + 1) / 2 ≤ p)
  (gg₅ : (2 + (p + 1) / 2)! ∣ p !)
  (gg₆ : 2! * ((p + 1) / 2)! ∣ p !) :
  2 * ((p + 1) / 2) * (p + 1) ∣ b ! := by
  have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
    refine dvd_trans ?_ gg₆
    simp
    refine mul_dvd_mul_left 2 ?_
    refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
  have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
    refine mul_dvd_mul_right ?_ (p + 1)
    exact gg₇
  rw [gg₂] at gg₁
  exact dvd_trans gg₈ gg₁


lemma imo_2022_p5_12_25
  -- (b : ℕ)
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  -- (gg₁ : (p + 1)! ∣ b !)
  -- (gg₂ : (p + 1)! = p ! * (p + 1))
  (gg₃ : 3 ≤ (p + 1) / 2)
  -- (gg₄ : 2 + (p + 1) / 2 ≤ p)
  -- (gg₅ : (2 + (p + 1) / 2)! ∣ p !)
  (gg₆ : 2! * ((p + 1) / 2)! ∣ p !) :
  2 * ((p + 1) / 2) ∣ p ! := by
  refine dvd_trans ?_ gg₆
  simp
  refine mul_dvd_mul_left 2 ?_
  refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)


lemma imo_2022_p5_12_26
  -- (b : ℕ)
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  -- (gg₁ : (p + 1)! ∣ b !)
  -- (gg₂ : (p + 1)! = p ! * (p + 1))
  (gg₃ : 3 ≤ (p + 1) / 2) :
  -- (gg₄ : 2 + (p + 1) / 2 ≤ p)
  -- (gg₅ : (2 + (p + 1) / 2)! ∣ p !)
  -- (gg₆ : 2! * ((p + 1) / 2)! ∣ p !) :
  2 * ((p + 1) / 2) ∣ 2 * ((p + 1) / 2)! := by
  refine mul_dvd_mul_left 2 ?_
  refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)


lemma imo_2022_p5_12_27
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  (gg₁ : (p + 1)! ∣ b !)
  (gg₂ : (p + 1)! = p ! * (p + 1))
  (gg₃ : 3 ≤ (p + 1) / 2)
  (gg₄ : 2 + (p + 1) / 2 ≤ p)
  (gg₅ : (2 + (p + 1) / 2)! ∣ p !)
  (gg₆ : 2! * ((p + 1) / 2)! ∣ p !)
  (gg₇ : 2 * ((p + 1) / 2) ∣ p !) :
  2 * ((p + 1) / 2) * (p + 1) ∣ b ! := by
  have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
    refine mul_dvd_mul_right ?_ (p + 1)
    exact gg₇
  rw [gg₂] at gg₁
  exact dvd_trans gg₈ gg₁


lemma imo_2022_p5_12_28
  -- (b : ℕ)
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  -- (gg₁ : (p + 1)! ∣ b !)
  -- (gg₂ : (p + 1)! = p ! * (p + 1))
  -- (gg₃ : 3 ≤ (p + 1) / 2)
  -- (gg₄ : 2 + (p + 1) / 2 ≤ p)
  -- (gg₅ : (2 + (p + 1) / 2)! ∣ p !)
  -- (gg₆ : 2! * ((p + 1) / 2)! ∣ p !)
  (gg₇ : 2 * ((p + 1) / 2) ∣ p !) :
  2 * ((p + 1) / 2) * (p + 1) ∣ p ! * (p + 1) := by
  refine mul_dvd_mul_right ?_ (p + 1)
  exact gg₇


lemma imo_2022_p5_12_29
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  -- (g₁ : p + 1 ≤ b)
  -- (g₂ : 2 ∣ p + 1)
  (gg₁ : (p + 1)! ∣ b !)
  (gg₂ : (p + 1)! = p ! * (p + 1))
  (gg₃ : 3 ≤ (p + 1) / 2)
  (gg₄ : 2 + (p + 1) / 2 ≤ p)
  (gg₅ : (2 + (p + 1) / 2)! ∣ p !)
  (gg₆ : 2! * ((p + 1) / 2)! ∣ p !)
  (gg₇ : 2 * ((p + 1) / 2) ∣ p !)
  (gg₈ : 2 * ((p + 1) / 2) * (p + 1) ∣ p ! * (p + 1)) :
  2 * ((p + 1) / 2) * (p + 1) ∣ b ! := by
  rw [gg₂] at gg₁
  exact dvd_trans gg₈ gg₁


lemma imo_2022_p5_12_30
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  (g₁ : p + 1 ≤ b)
  (g₂ : 2 ∣ p + 1)
  (g₃ : 2 * ((p + 1) / 2) * (p + 1) ∣ b !) :
  (p + 1) ^ 2 ∣ b ! := by
  have g₄: 2 * ((p+1)/2) = (p + 1) := by
    exact Nat.mul_div_cancel' g₂
  rw [g₄] at g₃
  ring_nf at *
  exact g₃


lemma imo_2022_p5_12_31
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  (h₁ : p ^ p = b ! + p)
  -- (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  (g₁ : p + 1 ≤ b)
  (g₂ : 2 ∣ p + 1)
  (g₃ : 2 * ((p + 1) / 2) * (p + 1) ∣ b !)
  (g₄ : 2 * ((p + 1) / 2) = p + 1) :
  (p + 1) ^ 2 ∣ b ! := by
  rw [g₄] at g₃
  ring_nf at *
  exact g₃


lemma imo_2022_p5_12_32
  (b p : ℕ)
  (hp : Nat.Prime p)
  (h₁ : p ^ p = b ! + p)
  (hp5 : 5 ≤ p)
  -- (hpb : p < b)
  (h₂ : (p + 1) ^ 2 ∣ b !) :
  False := by
  have h₃: b.factorial = p ^ p - p := by exact eq_tsub_of_add_eq (h₁.symm)
  rw [h₃] at h₂
  exact imo_2022_p5_10 p hp hp5 h₂


lemma imo_2022_p5_13
  (a b p: ℕ)
  (hp: Nat.Prime p)
  (h₂: p ∣ a)
  (hb2p: 2 * p ≤ b) :
  (p ^ 2 ∣ a ^ p - b.factorial) := by
  have g₁: p^p ∣ a^p := by exact pow_dvd_pow_of_dvd h₂ p
  have g₂: 2 ≤ p := by exact Prime.two_le hp
  have h₃: p^2 ∣ a^p := by exact pow_dvd_of_le_of_pow_dvd g₂ g₁
  have g₃: (2*p).factorial ∣ b.factorial := by exact factorial_dvd_factorial hb2p
  have g₄: p.factorial * p.factorial ∣ (p+p).factorial := by
    exact factorial_mul_factorial_dvd_factorial_add p p
  rw [← pow_two, ← two_mul] at g₄
  have g₅: p ∣ p.factorial := by exact Nat.dvd_factorial (by linarith) (by linarith)
  have h₄: p ^ 2 ∣ p.factorial ^ 2 := by exact pow_dvd_pow_of_dvd g₅ 2
  have g₆: p ^ 2 ∣ (2 * p).factorial := by exact dvd_trans h₄ g₄
  have h₅: p^2 ∣ b.factorial := by exact dvd_trans g₆ g₃
  exact dvd_sub' h₃ h₅


lemma imo_2022_p5_13_1
  (a b p : ℕ)
  (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  (hb2p : 2 * p ≤ b)
  (g₁ : p ^ p ∣ a ^ p) :
  p ^ 2 ∣ a ^ p - b ! := by
  have g₂: 2 ≤ p := by exact Prime.two_le hp
  have h₃: p^2 ∣ a^p := by exact pow_dvd_of_le_of_pow_dvd g₂ g₁
  have g₃: (2*p).factorial ∣ b.factorial := by exact factorial_dvd_factorial hb2p
  have g₄: p.factorial * p.factorial ∣ (p+p).factorial := by
    exact factorial_mul_factorial_dvd_factorial_add p p
  rw [← pow_two, ← two_mul] at g₄
  have g₅: p ∣ p.factorial := by exact Nat.dvd_factorial (by linarith) (by linarith)
  have h₄: p ^ 2 ∣ p.factorial ^ 2 := by exact pow_dvd_pow_of_dvd g₅ 2
  have g₆: p ^ 2 ∣ (2 * p).factorial := by exact dvd_trans h₄ g₄
  have h₅: p^2 ∣ b.factorial := by exact dvd_trans g₆ g₃
  exact dvd_sub' h₃ h₅


lemma imo_2022_p5_13_2
  (a b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  (hb2p : 2 * p ≤ b)
  (g₁ : p ^ p ∣ a ^ p)
  (g₂ : 2 ≤ p) :
  p ^ 2 ∣ a ^ p - b ! := by
  have h₃: p^2 ∣ a^p := by exact pow_dvd_of_le_of_pow_dvd g₂ g₁
  have g₃: (2*p).factorial ∣ b.factorial := by exact factorial_dvd_factorial hb2p
  have g₄: p.factorial * p.factorial ∣ (p+p).factorial := by
    exact factorial_mul_factorial_dvd_factorial_add p p
  rw [← pow_two, ← two_mul] at g₄
  have g₅: p ∣ p.factorial := by exact Nat.dvd_factorial (by linarith) (by linarith)
  have h₄: p ^ 2 ∣ p.factorial ^ 2 := by exact pow_dvd_pow_of_dvd g₅ 2
  have g₆: p ^ 2 ∣ (2 * p).factorial := by exact dvd_trans h₄ g₄
  have h₅: p^2 ∣ b.factorial := by exact dvd_trans g₆ g₃
  exact dvd_sub' h₃ h₅


lemma imo_2022_p5_13_3
  (a b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  (hb2p : 2 * p ≤ b)
  -- (g₁ : p ^ p ∣ a ^ p)
  (g₂ : 2 ≤ p)
  (h₃ : p ^ 2 ∣ a ^ p) :
  p ^ 2 ∣ a ^ p - b ! := by
  have g₃: (2*p).factorial ∣ b.factorial := by exact factorial_dvd_factorial hb2p
  have g₄: p.factorial * p.factorial ∣ (p+p).factorial := by
    exact factorial_mul_factorial_dvd_factorial_add p p
  rw [← pow_two, ← two_mul] at g₄
  have g₅: p ∣ p.factorial := by exact Nat.dvd_factorial (by linarith) (by linarith)
  have h₄: p ^ 2 ∣ p.factorial ^ 2 := by exact pow_dvd_pow_of_dvd g₅ 2
  have g₆: p ^ 2 ∣ (2 * p).factorial := by exact dvd_trans h₄ g₄
  have h₅: p^2 ∣ b.factorial := by exact dvd_trans g₆ g₃
  exact dvd_sub' h₃ h₅


lemma imo_2022_p5_13_4
  (a p : ℕ)
  -- (b : ℕ)
  (hp : Nat.Prime p)
  (h₂ : p ∣ a) :
  -- (hb2p : 2 * p ≤ b) :
  p ^ 2 ∣ a ^ p := by
  have g₁: p^p ∣ a^p := by exact pow_dvd_pow_of_dvd h₂ p
  have g₂: 2 ≤ p := by exact Prime.two_le hp
  exact pow_dvd_of_le_of_pow_dvd g₂ g₁


lemma imo_2022_p5_13_5
  (a b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  -- (g₁ : p ^ p ∣ a ^ p)
  (g₂ : 2 ≤ p)
  (h₃ : p ^ 2 ∣ a ^ p)
  (g₃ : (2 * p)! ∣ b !) :
  p ^ 2 ∣ a ^ p - b ! := by
  have g₄: p.factorial * p.factorial ∣ (p+p).factorial := by
    exact factorial_mul_factorial_dvd_factorial_add p p
  rw [← pow_two, ← two_mul] at g₄
  have g₅: p ∣ p.factorial := by exact Nat.dvd_factorial (by linarith) (by linarith)
  have h₄: p ^ 2 ∣ p.factorial ^ 2 := by exact pow_dvd_pow_of_dvd g₅ 2
  have g₆: p ^ 2 ∣ (2 * p).factorial := by exact dvd_trans h₄ g₄
  have h₅: p^2 ∣ b.factorial := by exact dvd_trans g₆ g₃
  exact dvd_sub' h₃ h₅


lemma imo_2022_p5_13_6
  (a b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  -- (g₁ : p ^ p ∣ a ^ p)
  (g₂ : 2 ≤ p)
  (h₃ : p ^ 2 ∣ a ^ p)
  (g₃ : (2 * p)! ∣ b !)
  (g₄ : p ! * p ! ∣ (p + p)!) :
  p ^ 2 ∣ a ^ p - b ! := by
  rw [← pow_two, ← two_mul] at g₄
  have g₅: p ∣ p.factorial := by exact Nat.dvd_factorial (by linarith) (by linarith)
  have h₄: p ^ 2 ∣ p.factorial ^ 2 := by exact pow_dvd_pow_of_dvd g₅ 2
  have g₆: p ^ 2 ∣ (2 * p).factorial := by exact dvd_trans h₄ g₄
  have h₅: p^2 ∣ b.factorial := by exact dvd_trans g₆ g₃
  exact dvd_sub' h₃ h₅


lemma imo_2022_p5_13_7
  (a b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  -- (g₁ : p ^ p ∣ a ^ p)
  -- (g₂ : 2 ≤ p)
  (h₃ : p ^ 2 ∣ a ^ p)
  (g₃ : (2 * p)! ∣ b !)
  (g₄ : p ! ^ 2 ∣ (2 * p)!)
  (g₅ : p ∣ p !) :
  p ^ 2 ∣ a ^ p - b ! := by
  have h₄: p ^ 2 ∣ p.factorial ^ 2 := by exact pow_dvd_pow_of_dvd g₅ 2
  have g₆: p ^ 2 ∣ (2 * p).factorial := by exact dvd_trans h₄ g₄
  have h₅: p^2 ∣ b.factorial := by exact dvd_trans g₆ g₃
  exact dvd_sub' h₃ h₅


lemma imo_2022_p5_13_8
  -- (a b : ℕ)
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  -- (g₁ : p ^ p ∣ a ^ p)
  (g₂ : 2 ≤ p) :
  -- (h₃ : p ^ 2 ∣ a ^ p)
  -- (g₃ : (2 * p)! ∣ b !)
  -- (g₄ : p ! ^ 2 ∣ (2 * p)!) :
  p ^ 2 ∣ p ! ^ 2 := by
  have g₅: p ∣ p.factorial := by exact Nat.dvd_factorial (by linarith) (by linarith)
  exact pow_dvd_pow_of_dvd g₅ 2


lemma imo_2022_p5_13_9
  -- (a b : ℕ)
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  -- (g₁ : p ^ p ∣ a ^ p)
  (g₂ : 2 ≤ p) :
  -- (h₃ : p ^ 2 ∣ a ^ p) :
  -- (g₃ : (2 * p)! ∣ b !)
  -- (g₄ : p ! ^ 2 ∣ (2 * p)!)
  p ^ 2 ∣ p ! ^ 2 := by
  refine pow_dvd_pow_of_dvd ?_ 2
  exact Nat.dvd_factorial (by linarith) (by linarith)


lemma imo_2022_p5_13_10
  (a b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  -- (g₁ : p ^ p ∣ a ^ p)
  -- (g₂ : 2 ≤ p)
  (h₃ : p ^ 2 ∣ a ^ p)
  (g₃ : (2 * p)! ∣ b !)
  (g₄ : p ! ^ 2 ∣ (2 * p)!)
  -- (g₅ : p ∣ p !)
  (h₄ : p ^ 2 ∣ p ! ^ 2) :
  p ^ 2 ∣ a ^ p - b ! := by
  have g₆: p ^ 2 ∣ (2 * p).factorial := by exact dvd_trans h₄ g₄
  have h₅: p^2 ∣ b.factorial := by exact dvd_trans g₆ g₃
  exact dvd_sub' h₃ h₅


lemma imo_2022_p5_13_11
  -- (a b : ℕ)
  (p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  -- (g₁ : p ^ p ∣ a ^ p)
  -- (g₂ : 2 ≤ p)
  -- (h₃ : p ^ 2 ∣ a ^ p)
  -- (g₃ : (2 * p)! ∣ b !)
  (g₅ : p ∣ p !) :
  p ^ 2 ∣ (2 * p)! := by
  have h₄: p ^ 2 ∣ p.factorial ^ 2 := by exact pow_dvd_pow_of_dvd g₅ 2
  refine dvd_trans h₄ ?_
  have g₄: p.factorial * p.factorial ∣ (p+p).factorial := by
    exact factorial_mul_factorial_dvd_factorial_add p p
  rw [← pow_two, ← two_mul] at g₄
  exact g₄


lemma imo_2022_p5_13_12
  (a b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  -- (g₁ : p ^ p ∣ a ^ p)
  -- (g₂ : 2 ≤ p)
  (h₃ : p ^ 2 ∣ a ^ p)
  (g₃ : (2 * p)! ∣ b !)
  -- (g₄ : p ! ^ 2 ∣ (2 * p)!)
  -- (g₅ : p ∣ p !)
  -- (h₄ : p ^ 2 ∣ p ! ^ 2)
  (g₆ : p ^ 2 ∣ (2 * p)!) :
  p ^ 2 ∣ a ^ p - b ! := by
  have h₅: p^2 ∣ b.factorial := by exact dvd_trans g₆ g₃
  exact dvd_sub' h₃ h₅


lemma imo_2022_p5_13_13
  -- (a : ℕ)
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  -- (g₁ : p ^ p ∣ a ^ p)
  -- (g₂ : 2 ≤ p)
  -- (h₃ : p ^ 2 ∣ a ^ p)
  (g₃ : (2 * p)! ∣ b !)
  (g₄ : p ! ^ 2 ∣ (2 * p)!)
  -- (g₅ : p ∣ p !)
  (h₄ : p ^ 2 ∣ p ! ^ 2) :
  p ^ 2 ∣ b ! := by
  refine dvd_trans ?_ g₃
  exact dvd_trans h₄ g₄


lemma imo_2022_p5_13_14
  -- (a : ℕ)
  (b p : ℕ)
  -- (hp : Nat.Prime p)
  -- (h₂ : p ∣ a)
  (hb2p : 2 * p ≤ b)
  -- (g₁ : p ^ p ∣ a ^ p)
  -- (g₂ : 2 ≤ p)
  -- (h₃ : p ^ 2 ∣ a ^ p)
  (g₄ : p ! ^ 2 ∣ (2 * p)!)
  -- (g₅ : p ∣ p !)
  (h₄ : p ^ 2 ∣ p ! ^ 2) :
  p ^ 2 ∣ b ! := by
  have g₃: (2*p).factorial ∣ b.factorial := by exact factorial_dvd_factorial hb2p
  refine dvd_trans ?_ g₃
  exact dvd_trans h₄ g₄





lemma imo_2022_p5_14
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : b < p) :
  (a, b, p) = (2, 2, 2) ∨ (a, b, p) = (3, 4, 3) := by
  exfalso
  by_cases hab: a ≤ b
  . have h₂: a ∣ b.factorial := by exact Nat.dvd_factorial h₀.1 hab
    have g₃: a ∣ b.factorial + p := by
      rw [← h₁]
      refine dvd_pow_self a ?_
      exact Nat.Prime.ne_zero hp
    have h₃: a ∣ p := by exact (Nat.dvd_add_right h₂).mp g₃
    have h₄: a = 1 := by
      have g₄: a = 1 ∨ a = p := by
        exact (Nat.dvd_prime hp).mp h₃
      cases' g₄ with g₄₀ g₄₁
      . exact g₄₀
      . exfalso
        rw [← g₄₁] at hbp
        linarith[hbp,hab]
    rw [h₄] at h₁
    simp at h₁
    have h₅: 2 ≤ p := by exact Nat.Prime.two_le hp
    have g₆: 0 < b.factorial := by exact Nat.factorial_pos b
    have h₇: 1+2 ≤ b.factorial + p := by exact Nat.add_le_add g₆ h₅
    rw [← h₁] at h₇
    linarith
  . push_neg at hab
    have h₂: (b+1)^p ≤ a^p := by
      refine (Nat.pow_le_pow_iff_left ?_).mpr hab
      exact Nat.Prime.ne_zero hp
    have h₃: b^p + p*b + 1 ≤ (b+1)^p := by
      ring_nf
      rw [add_assoc]
      exact imo_2022_p5_1 b p h₀.2 hbp
    have g₄: p * 1 ≤ p * b := by
      refine mul_le_mul ?_ ?_ ?_ ?_
      . exact rfl.ge
      . exact h₀.2
      . norm_num
      . exact Nat.zero_le p
    have g₄: b.factorial ≤ b^b := by exact Nat.factorial_le_pow b
    have g₅: b^b ≤ b^p := by
      refine Nat.pow_le_pow_of_le_right h₀.2 ?_
      exact le_of_lt hbp
    linarith


lemma imo_2022_p5_14_1
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  (hab : a ≤ b) :
  False := by
  have h₂: a ∣ b.factorial := by exact Nat.dvd_factorial h₀.1 hab
  have g₃: a ∣ b.factorial + p := by
    rw [← h₁]
    refine dvd_pow_self a ?_
    exact Nat.Prime.ne_zero hp
  have h₃: a ∣ p := by exact (Nat.dvd_add_right h₂).mp g₃
  have h₄: a = 1 := by
    have g₄: a = 1 ∨ a = p := by
      exact (Nat.dvd_prime hp).mp h₃
    cases' g₄ with g₄₀ g₄₁
    . exact g₄₀
    . exfalso
      rw [← g₄₁] at hbp
      linarith[hbp,hab]
  rw [h₄] at h₁
  simp at h₁
  have h₅: 2 ≤ p := by exact Nat.Prime.two_le hp
  have g₆: 0 < b.factorial := by exact Nat.factorial_pos b
  have h₇: 1+2 ≤ b.factorial + p := by exact Nat.add_le_add g₆ h₅
  rw [← h₁] at h₇
  linarith


lemma imo_2022_p5_14_2
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  (hab : a ≤ b)
  (h₂ : a ∣ b !) :
  False := by
  have g₃: a ∣ b.factorial + p := by
    rw [← h₁]
    refine dvd_pow_self a ?_
    exact Nat.Prime.ne_zero hp
  have h₃: a ∣ p := by exact (Nat.dvd_add_right h₂).mp g₃
  have h₄: a = 1 := by
    have g₄: a = 1 ∨ a = p := by
      exact (Nat.dvd_prime hp).mp h₃
    cases' g₄ with g₄₀ g₄₁
    . exact g₄₀
    . exfalso
      rw [← g₄₁] at hbp
      linarith[hbp,hab]
  rw [h₄] at h₁
  simp at h₁
  have h₅: 2 ≤ p := by exact Nat.Prime.two_le hp
  have g₆: 0 < b.factorial := by exact Nat.factorial_pos b
  have h₇: 1+2 ≤ b.factorial + p := by exact Nat.add_le_add g₆ h₅
  rw [← h₁] at h₇
  linarith


lemma imo_2022_p5_14_3
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p) :
  -- (hbp : b < p)
  -- (hab : a ≤ b)
  -- (h₂ : a ∣ b !) :
  a ∣ b ! + p := by
  rw [← h₁]
  refine dvd_pow_self a ?_
  exact Nat.Prime.ne_zero hp


lemma imo_2022_p5_14_4
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  (hab : a ≤ b)
  (h₂ : a ∣ b !)
  (g₃ : a ∣ b ! + p) :
  False := by
  have h₃: a ∣ p := by exact (Nat.dvd_add_right h₂).mp g₃
  have h₄: a = 1 := by
    have g₄: a = 1 ∨ a = p := by
      exact (Nat.dvd_prime hp).mp h₃
    cases' g₄ with g₄₀ g₄₁
    . exact g₄₀
    . exfalso
      rw [← g₄₁] at hbp
      linarith[hbp,hab]
  rw [h₄] at h₁
  simp at h₁
  have h₅: 2 ≤ p := by exact Nat.Prime.two_le hp
  have g₆: 0 < b.factorial := by exact Nat.factorial_pos b
  have h₇: 1 + 2 ≤ b.factorial + p := by exact Nat.add_le_add g₆ h₅
  rw [← h₁] at h₇
  linarith


lemma imo_2022_p5_14_5
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  (hab : a ≤ b)
  (h₂ : a ∣ b !)
  (g₃ : a ∣ b ! + p)
  (h₃ : a ∣ p) :
  False := by
  have h₄: a = 1 := by
    have g₄: a = 1 ∨ a = p := by
      exact (Nat.dvd_prime hp).mp h₃
    cases' g₄ with g₄₀ g₄₁
    . exact g₄₀
    . exfalso
      rw [← g₄₁] at hbp
      linarith[hbp,hab]
  rw [h₄] at h₁
  simp at h₁
  have h₅: 2 ≤ p := by exact Nat.Prime.two_le hp
  have g₆: 0 < b.factorial := by exact Nat.factorial_pos b
  have h₇: 1+2 ≤ b.factorial + p := by exact Nat.add_le_add g₆ h₅
  rw [← h₁] at h₇
  linarith


lemma imo_2022_p5_14_6
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  (hab : a ≤ b)
  (h₂ : a ∣ b !)
  (g₃ : a ∣ b ! + p)
  (h₃ : a ∣ p) :
  a = 1 := by
  have g₄: a = 1 ∨ a = p := by
    exact (Nat.dvd_prime hp).mp h₃
  cases' g₄ with g₄₀ g₄₁
  . exact g₄₀
  . exfalso
    rw [← g₄₁] at hbp
    linarith[hbp,hab]


lemma imo_2022_p5_14_7
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  (hab : a ≤ b)
  (h₂ : a ∣ b !)
  (g₃ : a ∣ b ! + p)
  (h₃ : a ∣ p)
  (g₄ : a = 1 ∨ a = p) :
  a = 1 := by
  cases' g₄ with g₄₀ g₄₁
  . exact g₄₀
  . exfalso
    rw [← g₄₁] at hbp
    linarith[hbp,hab]


lemma imo_2022_p5_14_8
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  (hab : a ≤ b)
  (h₂ : a ∣ b !)
  (g₃ : a ∣ b ! + p)
  (h₃ : a ∣ p)
  (g₄₁ : a = p) :
  a = 1 := by
  exfalso
  rw [← g₄₁] at hbp
  linarith[hbp,hab]


lemma imo_2022_p5_14_9
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  (hab : a ≤ b)
  (h₂ : a ∣ b !)
  (g₃ : a ∣ b ! + p)
  (h₃ : a ∣ p)
  (g₄₁ : a = p) :
  False := by
  rw [← g₄₁] at hbp
  linarith[hbp,hab]


lemma imo_2022_p5_14_10
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  (hab : a ≤ b)
  (h₂ : a ∣ b !)
  (g₃ : a ∣ b ! + p)
  (h₃ : a ∣ p)
  (h₄ : a = 1) :
  False := by
  rw [h₄] at h₁
  simp at h₁
  have h₅: 2 ≤ p := by exact Nat.Prime.two_le hp
  have g₆: 0 < b.factorial := by exact Nat.factorial_pos b
  have h₇: 1+2 ≤ b.factorial + p := by exact Nat.add_le_add g₆ h₅
  rw [← h₁] at h₇
  linarith


lemma imo_2022_p5_14_11
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (hbp : b < p)
  -- (hab : a ≤ b)
  -- (h₂ : a ∣ b !)
  -- (g₃ : a ∣ b ! + p)
  -- (h₃ : a ∣ p)
  -- (h₄ : a = 1)
  (h₁ : 1 = b ! + p) :
  False := by
  have h₅: 2 ≤ p := by exact Nat.Prime.two_le hp
  have g₆: 0 < b.factorial := by exact Nat.factorial_pos b
  have h₇: 1+2 ≤ b.factorial + p := by exact Nat.add_le_add g₆ h₅
  rw [← h₁] at h₇
  linarith


lemma imo_2022_p5_14_12
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (hbp : b < p)
  -- (hab : a ≤ b)
  -- (h₂ : a ∣ b !)
  -- (g₃ : a ∣ b ! + p)
  -- (h₃ : a ∣ p)
  -- (h₄ : a = 1)
  (h₁ : 1 = b ! + p)
  (h₅ : 2 ≤ p) :
  False := by
  have g₆: 0 < b.factorial := by exact Nat.factorial_pos b
  have h₇: 1+2 ≤ b.factorial + p := by exact Nat.add_le_add g₆ h₅
  rw [← h₁] at h₇
  linarith


lemma imo_2022_p5_14_13
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (hbp : b < p)
  -- (hab : a ≤ b)
  -- (h₂ : a ∣ b !)
  -- (g₃ : a ∣ b ! + p)
  -- (h₃ : a ∣ p)
  -- (h₄ : a = 1)
  (h₁ : 1 = b ! + p)
  (h₅ : 2 ≤ p)
  (g₆ : 0 < b !) :
  False := by
  have h₇: 1+2 ≤ b.factorial + p := by exact Nat.add_le_add g₆ h₅
  rw [← h₁] at h₇
  linarith


lemma imo_2022_p5_14_14
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (hbp : b < p)
  -- (hab : a ≤ b)
  -- (h₂ : a ∣ b !)
  -- (g₃ : a ∣ b ! + p)
  -- (h₃ : a ∣ p)
  -- (h₄ : a = 1)
  (h₁ : 1 = b ! + p) :
  -- (h₅ : 2 ≤ p) :
  1 ≤ b ! := by
  have g₆: 0 < b.factorial := by exact Nat.factorial_pos b
  linarith [g₆]


lemma imo_2022_p5_14_15
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (hbp : b < p)
  -- (hab : a ≤ b)
  -- (h₂ : a ∣ b !)
  -- (g₃ : a ∣ b ! + p)
  -- (h₃ : a ∣ p)
  -- (h₄ : a = 1)
  (h₁ : 1 = b ! + p)
  (h₅ : 2 ≤ p)
  (g₆ : 0 < b !) :
  -- (h₆ : 1 ≤ b !) :
  False := by
  have h₇: 1+2 ≤ b.factorial + p := by exact Nat.add_le_add g₆ h₅
  rw [← h₁] at h₇
  linarith


lemma imo_2022_p5_14_16
  -- (a : ℕ)
  (b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p) :
  -- (hbp : b < p)
  -- (hab : a ≤ b)
  -- (h₂ : a ∣ b !)
  -- (g₃ : a ∣ b ! + p)
  -- (h₃ : a ∣ p)
  -- (h₄ : a = 1)
  -- (h₁ : 1 = b ! + p)
  -- (h₆ : 1 ≤ b !) :
  1 + 2 ≤ b ! + p := by
  have h₅: 2 ≤ p := by exact Nat.Prime.two_le hp
  have g₆: 0 < b.factorial := by exact Nat.factorial_pos b
  exact Nat.add_le_add g₆ h₅


lemma imo_2022_p5_14_17
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (hbp : b < p)
  -- (hab : a ≤ b)
  -- (h₂ : a ∣ b !)
  -- (g₃ : a ∣ b ! + p)
  -- (h₃ : a ∣ p)
  -- (h₄ : a = 1)
  (h₁ : 1 = b ! + p)
  -- (h₅ : 2 ≤ p)
  -- (g₆ : 0 < b !)
  -- (h₆ : 1 ≤ b !)
  (h₇ : 1 + 2 ≤ b ! + p) :
  False := by
  rw [← h₁] at h₇
  linarith


lemma imo_2022_p5_14_18
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  (hab : b < a) :
  False := by
  have h₂: (b+1)^p ≤ a^p := by
    refine (Nat.pow_le_pow_iff_left ?_).mpr hab
    exact Nat.Prime.ne_zero hp
  have h₃: b^p + p*b + 1 ≤ (b+1)^p := by
    ring_nf
    rw [add_assoc]
    exact imo_2022_p5_1 b p h₀.2 hbp
  have g₄: p * 1 ≤ p * b := by
    refine mul_le_mul ?_ ?_ ?_ ?_
    . exact rfl.ge
    . exact h₀.2
    . norm_num
    . exact Nat.zero_le p
  have g₄: b.factorial ≤ b^b := by exact Nat.factorial_le_pow b
  have g₅: b^b ≤ b^p := by
    refine Nat.pow_le_pow_of_le_right h₀.2 ?_
    exact le_of_lt hbp
  linarith


lemma imo_2022_p5_14_19
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : b < p)
  (hab : b < a) :
  (b + 1) ^ p ≤ a ^ p := by
  refine (Nat.pow_le_pow_iff_left ?_).mpr hab
  exact Nat.Prime.ne_zero hp


lemma imo_2022_p5_14_20
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  -- (hab : b < a)
  (h₂ : (b + 1) ^ p ≤ a ^ p) :
  False := by
  have h₃: b^p + p*b + 1 ≤ (b+1)^p := by
    ring_nf
    rw [add_assoc]
    exact imo_2022_p5_1 b p h₀.2 hbp
  have g₄: p * 1 ≤ p * b := by
    refine mul_le_mul ?_ ?_ ?_ ?_
    . exact rfl.ge
    . exact h₀.2
    . norm_num
    . exact Nat.zero_le p
  have g₄: b.factorial ≤ b^b := by exact Nat.factorial_le_pow b
  have g₅: b^b ≤ b^p := by
    refine Nat.pow_le_pow_of_le_right h₀.2 ?_
    exact le_of_lt hbp
  linarith


lemma imo_2022_p5_14_21
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  (hbp : b < p) :
  -- (hab : b < a)
  -- (h₂ : (b + 1) ^ p ≤ a ^ p) :
  b ^ p + p * b + 1 ≤ (b + 1) ^ p := by
  ring_nf
  rw [add_assoc]
  exact imo_2022_p5_1 b p h₀.2 hbp


lemma imo_2022_p5_14_22
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  -- (hab : b < a)
  (h₂ : (b + 1) ^ p ≤ a ^ p)
  (h₃ : b ^ p + p * b + 1 ≤ (b + 1) ^ p) :
  False := by
  have g₄: p * 1 ≤ p * b := by
    refine mul_le_mul ?_ ?_ ?_ ?_
    . exact rfl.ge
    . exact h₀.2
    . norm_num
    . exact Nat.zero_le p
  have g₄: b.factorial ≤ b^b := by exact Nat.factorial_le_pow b
  have g₅: b^b ≤ b^p := by
    refine Nat.pow_le_pow_of_le_right h₀.2 ?_
    exact le_of_lt hbp
  linarith


lemma imo_2022_p5_14_23
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b) :
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : b < p)
  -- (hab : b < a)
  -- (h₂ : (b + 1) ^ p ≤ a ^ p)
  -- (h₃ : b ^ p + p * b + 1 ≤ (b + 1) ^ p) :
  p * 1 ≤ p * b := by
  refine mul_le_mul ?_ ?_ ?_ ?_
  . exact rfl.ge
  . exact h₀.2
  . norm_num
  . exact Nat.zero_le p


lemma imo_2022_p5_14_24
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  -- (hab : b < a)
  (h₂ : (b + 1) ^ p ≤ a ^ p)
  (h₃ : b ^ p + p * b + 1 ≤ (b + 1) ^ p)
  (g₄ : p * 1 ≤ p * b) :
  False := by
  have g₄: b.factorial ≤ b^b := by exact Nat.factorial_le_pow b
  have g₅: b^b ≤ b^p := by
    refine Nat.pow_le_pow_of_le_right h₀.2 ?_
    exact le_of_lt hbp
  linarith


lemma imo_2022_p5_14_25
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  -- (hab : b < a)
  (h₂ : (b + 1) ^ p ≤ a ^ p)
  (h₃ : b ^ p + p * b + 1 ≤ (b + 1) ^ p)
  -- (g₄ : p * 1 ≤ p * b)
  (h₄ : b ^ p + p < b ^ p + p * b + 1) :
  False := by
  have g₄: b.factorial ≤ b^b := by exact Nat.factorial_le_pow b
  have g₅: b^b ≤ b^p := by
    refine Nat.pow_le_pow_of_le_right h₀.2 ?_
    exact le_of_lt hbp
  linarith


lemma imo_2022_p5_14_26
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : b < p)
  -- (hab : b < a)
  (h₂ : (b + 1) ^ p ≤ a ^ p)
  (h₃ : b ^ p + p * b + 1 ≤ (b + 1) ^ p)
  -- (g4 : p * 1 ≤ p * b)
  (h₄ : b ^ p + p < b ^ p + p * b + 1)
  (g₄ : b ! ≤ b ^ b) :
  False := by
  have g₅: b^b ≤ b^p := by
    refine Nat.pow_le_pow_of_le_right h₀.2 ?_
    exact le_of_lt hbp
  linarith


lemma imo_2022_p5_14_27
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  (hbp : b < p) :
  -- (hab : b < a)
  -- (h₂ : (b + 1) ^ p ≤ a ^ p)
  -- (h₃ : b ^ p + p * b + 1 ≤ (b + 1) ^ p)
  -- (g4 : p * 1 ≤ p * b)
  -- (h₄ : b ^ p + p < b ^ p + p * b + 1)
  -- (g₄ : b ! ≤ b ^ b) :
  b ^ b ≤ b ^ p := by
  refine Nat.pow_le_pow_of_le_right h₀.2 ?_
  exact le_of_lt hbp


lemma imo_2022_p5_15
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b) :
  (a, b, p) = (2, 2, 2) ∨ (a, b, p) = (3, 4, 3) := by
  have h₂: p ∣ a := by exact imo_2022_p5_3 a b p hp h₁ hbp
  by_cases hb2p: b < 2*p
  . have h₃: a = p := by exact imo_2022_p5_8 a b p h₀ hp h₁ hbp h₂ hb2p
    rw [h₃] at h₁
    by_cases hp5: p < 5
    . have h₄: 2 ≤ p := by exact Prime.two_le hp
      interval_cases p
      . left
        norm_num at h₁
        have h₄: b.factorial = 2 := by linarith
        have g₅: (2:ℕ).factorial = 2 := by norm_num
        rw [← g₅] at h₄
        have h₅: b = 2 := by
          refine (Nat.factorial_inj ?_).mp h₄
          linarith
        rw [h₃,h₅]
      . right
        norm_num at h₁
        rw [h₃]
        have h₄: b.factorial = 24 := by linarith
        have g₅: (4:ℕ).factorial = 24 := by exact rfl
        rw [← g₅] at h₄
        have h₅: b = 4 := by
          refine (Nat.factorial_inj ?_).mp h₄
          linarith
        rw [h₅]
      . exfalso
        contradiction
    . push_neg at hp5
      exfalso
      -- lifting the exponent
      exact imo_2022_p5_12 b p hp hbp h₁ hp5
  . push_neg at hb2p
    exfalso
    have h₃: p^2 ∣ a^p - b.factorial := by exact imo_2022_p5_13 a b p hp h₂ hb2p
    have g₃: b.factorial ≤ a^p := by exact le.intro (h₁.symm)
    have g₄: a^p - b.factorial = p := by
      rw [add_comm] at h₁
      exact (Nat.sub_eq_iff_eq_add g₃).mpr h₁
    have h₄: p^2 ∣ p := by
      rw [g₄] at h₃
      exact h₃
    have gp: 0 < p := by exact Prime.pos hp
    have h₅: p^2 ≤ p := by exact Nat.le_of_dvd gp h₄
    have g₆: 1 < p := by exact Prime.one_lt hp
    have h₆: p^1 < p^2 := by exact Nat.pow_lt_pow_succ g₆
    linarith


lemma imo_2022_p5_15_1
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  (h₂ : p ∣ a) :
  (a, b, p) = (2, 2, 2) ∨ (a, b, p) = (3, 4, 3) := by
  by_cases hb2p: b < 2*p
  . have h₃: a = p := by exact imo_2022_p5_8 a b p h₀ hp h₁ hbp h₂ hb2p
    rw [h₃] at h₁
    by_cases hp5: p < 5
    . have h₄: 2 ≤ p := by exact Prime.two_le hp
      interval_cases p
      . left
        norm_num at h₁
        have h₄: b.factorial = 2 := by linarith
        have g₅: (2:ℕ).factorial = 2 := by norm_num
        rw [← g₅] at h₄
        have h₅: b = 2 := by
          refine (Nat.factorial_inj ?_).mp h₄
          linarith
        rw [h₃,h₅]
      . right
        norm_num at h₁
        rw [h₃]
        have h₄: b.factorial = 24 := by linarith
        have g₅: (4:ℕ).factorial = 24 := by exact rfl
        rw [← g₅] at h₄
        have h₅: b = 4 := by
          refine (Nat.factorial_inj ?_).mp h₄
          linarith
        rw [h₅]
      . exfalso
        contradiction
    . push_neg at hp5
      exfalso
      -- lifting the exponent
      exact imo_2022_p5_12 b p hp hbp h₁ hp5
  . push_neg at hb2p
    exfalso
    have h₃: p^2 ∣ a^p - b.factorial := by exact imo_2022_p5_13 a b p hp h₂ hb2p
    have g₃: b.factorial ≤ a^p := by exact le.intro (h₁.symm)
    have g₄: a^p - b.factorial = p := by
      rw [add_comm] at h₁
      exact (Nat.sub_eq_iff_eq_add g₃).mpr h₁
    have h₄: p^2 ∣ p := by
      rw [g₄] at h₃
      exact h₃
    have gp: 0 < p := by exact Prime.pos hp
    have h₅: p^2 ≤ p := by exact Nat.le_of_dvd gp h₄
    have g₆: 1 < p := by exact Prime.one_lt hp
    have h₆: p^1 < p^2 := by exact Nat.pow_lt_pow_succ g₆
    linarith


lemma imo_2022_p5_15_2
  (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  (h₂ : p ∣ a)
  (hb2p : b < 2 * p) :
  (a, b, p) = (2, 2, 2) ∨ (a, b, p) = (3, 4, 3) := by
  have h₃: a = p := by exact imo_2022_p5_8 a b p h₀ hp h₁ hbp h₂ hb2p
  rw [h₃] at h₁
  by_cases hp5: p < 5
  . have h₄: 2 ≤ p := by exact Prime.two_le hp
    interval_cases p
    . left
      norm_num at h₁
      have h₄: b.factorial = 2 := by linarith
      have g₅: (2:ℕ).factorial = 2 := by norm_num
      rw [← g₅] at h₄
      have h₅: b = 2 := by
        refine (Nat.factorial_inj ?_).mp h₄
        linarith
      rw [h₃,h₅]
    . right
      norm_num at h₁
      rw [h₃]
      have h₄: b.factorial = 24 := by linarith
      have g₅: (4:ℕ).factorial = 24 := by exact rfl
      rw [← g₅] at h₄
      have h₅: b = 4 := by
        refine (Nat.factorial_inj ?_).mp h₄
        linarith
      rw [h₅]
    . exfalso
      contradiction
  . push_neg at hp5
    exfalso
    -- lifting the exponent
    exact imo_2022_p5_12 b p hp hbp h₁ hp5


lemma imo_2022_p5_15_3
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  (h₂ : p ∣ a)
  (hb2p : b < 2 * p)
  (h₃ : a = p) :
  (a, b, p) = (2, 2, 2) ∨ (a, b, p) = (3, 4, 3) := by
  rw [h₃] at h₁
  by_cases hp5: p < 5
  . have h₄: 2 ≤ p := by exact Prime.two_le hp
    interval_cases p
    . left
      norm_num at h₁
      have h₄: b.factorial = 2 := by linarith
      have g₅: (2:ℕ).factorial = 2 := by norm_num
      rw [← g₅] at h₄
      have h₅: b = 2 := by
        refine (Nat.factorial_inj ?_).mp h₄
        linarith
      rw [h₃,h₅]
    . right
      norm_num at h₁
      rw [h₃]
      have h₄: b.factorial = 24 := by linarith
      have g₅: (4:ℕ).factorial = 24 := by exact rfl
      rw [← g₅] at h₄
      have h₅: b = 4 := by
        refine (Nat.factorial_inj ?_).mp h₄
        linarith
      rw [h₅]
    . exfalso
      contradiction
  . push_neg at hp5
    exfalso
    -- lifting the exponent
    exact imo_2022_p5_12 b p hp hbp h₁ hp5


lemma imo_2022_p5_15_4
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : p ^ p = b ! + p)
  (hbp : p ≤ b)
  (h₂ : p ∣ a)
  (hb2p : b < 2 * p)
  (h₃ : a = p)
  (hp5 : p < 5) :
  (a, b, p) = (2, 2, 2) ∨ (a, b, p) = (3, 4, 3) := by
  have h₄: 2 ≤ p := by exact Prime.two_le hp
  interval_cases p
  . left
    norm_num at h₁
    have h₄: b.factorial = 2 := by linarith
    have g₅: (2:ℕ).factorial = 2 := by norm_num
    rw [← g₅] at h₄
    have h₅: b = 2 := by
      refine (Nat.factorial_inj ?_).mp h₄
      linarith
    rw [h₃,h₅]
  . right
    norm_num at h₁
    rw [h₃]
    have h₄: b.factorial = 24 := by linarith
    have g₅: (4:ℕ).factorial = 24 := by exact rfl
    rw [← g₅] at h₄
    have h₅: b = 4 := by
      refine (Nat.factorial_inj ?_).mp h₄
      linarith
    rw [h₅]
  . exfalso
    contradiction


lemma imo_2022_p5_15_5
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : p ^ p = b ! + p)
  (hbp : p ≤ b)
  (h₂ : p ∣ a)
  (hb2p : b < 2 * p)
  (h₃ : a = p)
  (hp5 : p < 5)
  (h₄ : 2 ≤ p) :
  (a, b, p) = (2, 2, 2) ∨ (a, b, p) = (3, 4, 3) := by
  interval_cases p
  . left
    norm_num at h₁
    have h₄: b.factorial = 2 := by linarith
    have g₅: (2:ℕ).factorial = 2 := by norm_num
    rw [← g₅] at h₄
    have h₅: b = 2 := by
      refine (Nat.factorial_inj ?_).mp h₄
      linarith
    rw [h₃,h₅]
  . right
    norm_num at h₁
    rw [h₃]
    have h₄: b.factorial = 24 := by linarith
    have g₅: (4:ℕ).factorial = 24 := by exact rfl
    rw [← g₅] at h₄
    have h₅: b = 4 := by
      refine (Nat.factorial_inj ?_).mp h₄
      linarith
    rw [h₅]
  . exfalso
    contradiction


lemma imo_2022_p5_15_6
  (a b : ℕ)
  -- (p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime 2)
  (h₁ : 2 ^ 2 = b ! + 2)
  (hbp : 2 ≤ b)
  -- (h₂ : 2 ∣ a)
  -- (hb2p : b < 2 * 2)
  (h₃ : a = 2) :
  -- (hp5 : 2 < 5)
  -- (h₄ : 2 ≤ 2) :
  (a, b, 2) = (2, 2, 2) ∨ (a, b, 2) = (3, 4, 3) := by
  left
  norm_num at h₁
  have h₄: b.factorial = 2 := by linarith
  have g₅: (2:ℕ).factorial = 2 := by norm_num
  rw [← g₅] at h₄
  have h₅: b = 2 := by
    refine (Nat.factorial_inj ?_).mp h₄
    linarith
  rw [h₃,h₅]


lemma imo_2022_p5_15_7
  (a b : ℕ)
  -- (p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime 2)
  (hbp : 2 ≤ b)
  -- (h₂ : 2 ∣ a)
  -- (hb2p : b < 2 * 2)
  (h₃ : a = 2)
  -- (hp5 : 2 < 5)
  -- (h₄ : 2 ≤ 2)
  (h₁ : 2 = b !) :
  (a, b, 2) = (2, 2, 2) := by
  have h₄: b.factorial = 2 := by linarith
  have g₅: (2:ℕ).factorial = 2 := by norm_num
  rw [← g₅] at h₄
  have h₅: b = 2 := by
    refine (Nat.factorial_inj ?_).mp h₄
    linarith
  rw [h₃,h₅]


lemma imo_2022_p5_15_8
  -- (a p : ℕ)
  (b : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime 2)
  (hbp : 2 ≤ b)
  -- (h₂ : 2 ∣ a)
  -- (hb2p : b < 2 * 2)
  -- (h₃ : a = 2)
  -- (hp5 : 2 < 5)
  -- (h4 : 2 ≤ 2)
  -- (h₁ : 2 = b !)
  (h₄ : b ! = 2!) :
  -- (g₅ : 2! = 2) :
  b = 2 := by
  refine (Nat.factorial_inj ?_).mp h₄
  linarith


lemma imo_2022_p5_15_9
  (a b : ℕ)
  -- (p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime 3)
  (h₁ : 3 ^ 3 = b ! + 3)
  (hbp : 3 ≤ b)
  -- (h₂ : 3 ∣ a)
  -- (hb2p : b < 2 * 3)
  (h₃ : a = 3) :
  -- (hp5 : 3 < 5)
  -- (h₄ : 2 ≤ 3) :
  (a, b, 3) = (2, 2, 2) ∨ (a, b, 3) = (3, 4, 3) := by
  right
  norm_num at h₁
  rw [h₃]
  have h₄: b.factorial = 24 := by linarith
  have g₅: (4:ℕ).factorial = 24 := by exact rfl
  rw [← g₅] at h₄
  have h₅: b = 4 := by
    refine (Nat.factorial_inj ?_).mp h₄
    linarith
  rw [h₅]


lemma imo_2022_p5_15_10
  (a b : ℕ)
  -- (p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime 3)
  (hbp : 3 ≤ b)
  -- (h₂ : 3 ∣ a)
  -- (hb2p : b < 2 * 3)
  (h₃ : a = 3)
  -- (hp5 : 3 < 5)
  -- (h₄ : 2 ≤ 3)
  (h₁ : 24 = b !) :
  (a, b, 3) = (3, 4, 3) := by
  rw [h₃]
  have h₄: b.factorial = 24 := by linarith
  have g₅: (4:ℕ).factorial = 24 := by exact rfl
  rw [← g₅] at h₄
  have h₅: b = 4 := by
    refine (Nat.factorial_inj ?_).mp h₄
    linarith
  rw [h₅]


lemma imo_2022_p5_15_11
  (b : ℕ)
  -- (a p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime 3)
  (hbp : 3 ≤ b)
  -- (h₂ : 3 ∣ a)
  -- (hb2p : b < 2 * 3)
  -- (h₃ : a = 3)
  -- (hp5 : 3 < 5)
  -- (h4 : 2 ≤ 3)
  -- (h₁ : 24 = b !)
  (h₄ : b ! = 4!) :
  -- (g₅ : 4! = 24) :
  b = 4 := by
  refine (Nat.factorial_inj ?_).mp h₄
  linarith


lemma imo_2022_p5_15_12
  (a b : ℕ)
  -- (p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime 4) :
  -- (h₁ : 4 ^ 4 = b ! + 4)
  -- (hbp : 4 ≤ b)
  -- (h₂ : 4 ∣ a)
  -- (hb2p : b < 2 * 4)
  -- (h₃ : a = 4)
  -- (hp5 : 4 < 5)
  -- (h₄ : 2 ≤ 4) :
  (a, b, 4) = (2, 2, 2) ∨ (a, b, 4) = (3, 4, 3) := by
  exfalso
  contradiction


lemma imo_2022_p5_15_13
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : p ^ p = b ! + p)
  (hbp : p ≤ b)
  -- (h₂ : p ∣ a)
  -- (hb2p : b < 2 * p)
  -- (h₃ : a = p)
  (hp5 : 5 ≤ p) :
  (a, b, p) = (2, 2, 2) ∨ (a, b, p) = (3, 4, 3) := by
  exfalso
  -- lifting the exponent
  exact imo_2022_p5_12 b p hp hbp h₁ hp5


lemma imo_2022_p5_15_14
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  (h₂ : p ∣ a)
  (hb2p : 2 * p ≤ b) :
  (a, b, p) = (2, 2, 2) ∨ (a, b, p) = (3, 4, 3) := by
  exfalso
  have h₃: p^2 ∣ a^p - b.factorial := by exact imo_2022_p5_13 a b p hp h₂ hb2p
  have g₃: b.factorial ≤ a^p := by exact le.intro (h₁.symm)
  have g₄: a^p - b.factorial = p := by
    rw [add_comm] at h₁
    exact (Nat.sub_eq_iff_eq_add g₃).mpr h₁
  have h₄: p^2 ∣ p := by
    rw [g₄] at h₃
    exact h₃
  have gp: 0 < p := by exact Prime.pos hp
  have h₅: p^2 ≤ p := by exact Nat.le_of_dvd gp h₄
  have g₆: 1 < p := by exact Prime.one_lt hp
  have h₆: p^1 < p^2 := by exact Nat.pow_lt_pow_succ g₆
  linarith


lemma imo_2022_p5_15_15
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  (h₂ : p ∣ a)
  (hb2p : 2 * p ≤ b) :
  False := by
  have h₃: p^2 ∣ a^p - b.factorial := by exact imo_2022_p5_13 a b p hp h₂ hb2p
  have g₃: b.factorial ≤ a^p := by exact le.intro (h₁.symm)
  have g₄: a^p - b.factorial = p := by
    rw [add_comm] at h₁
    exact (Nat.sub_eq_iff_eq_add g₃).mpr h₁
  have h₄: p^2 ∣ p := by
    rw [g₄] at h₃
    exact h₃
  have gp: 0 < p := by exact Prime.pos hp
  have h₅: p^2 ≤ p := by exact Nat.le_of_dvd gp h₄
  have g₆: 1 < p := by exact Prime.one_lt hp
  have h₆: p^1 < p^2 := by exact Nat.pow_lt_pow_succ g₆
  linarith


lemma imo_2022_p5_15_16
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  (h₃ : p ^ 2 ∣ a ^ p - b !) :
  False := by
  have g₃: b.factorial ≤ a^p := by exact le.intro (h₁.symm)
  have g₄: a^p - b.factorial = p := by
    rw [add_comm] at h₁
    exact (Nat.sub_eq_iff_eq_add g₃).mpr h₁
  have h₄: p^2 ∣ p := by
    rw [g₄] at h₃
    exact h₃
  have gp: 0 < p := by exact Prime.pos hp
  have h₅: p^2 ≤ p := by exact Nat.le_of_dvd gp h₄
  have g₆: 1 < p := by exact Prime.one_lt hp
  have h₆: p^1 < p^2 := by exact Nat.pow_lt_pow_succ g₆
  linarith


lemma imo_2022_p5_15_17
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  (h₃ : p ^ 2 ∣ a ^ p - b !)
  (g₃ : b ! ≤ a ^ p) :
  False := by
  have g₄: a^p - b.factorial = p := by
    rw [add_comm] at h₁
    exact (Nat.sub_eq_iff_eq_add g₃).mpr h₁
  have h₄: p^2 ∣ p := by
    rw [g₄] at h₃
    exact h₃
  have gp: 0 < p := by exact Prime.pos hp
  have h₅: p^2 ≤ p := by exact Nat.le_of_dvd gp h₄
  have g₆: 1 < p := by exact Prime.one_lt hp
  have h₆: p^1 < p^2 := by exact Nat.pow_lt_pow_succ g₆
  linarith


lemma imo_2022_p5_15_18
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  (h₁ : a ^ p = b ! + p)
  (hbp : p ≤ b)
  (h₂ : p ∣ a)
  (hb2p : 2 * p ≤ b)
  (h₃ : p ^ 2 ∣ a ^ p - b !)
  (g₃ : b ! ≤ a ^ p) :
  a ^ p - b ! = p := by
  rw [add_comm] at h₁
  exact (Nat.sub_eq_iff_eq_add g₃).mpr h₁


lemma imo_2022_p5_15_19
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  (h₃ : p ^ 2 ∣ a ^ p - b !)
  -- (g₃ : b ! ≤ a ^ p)
  (g₄ : a ^ p - b ! = p) :
  False := by
  have h₄: p^2 ∣ p := by
    rw [g₄] at h₃
    exact h₃
  have gp: 0 < p := by exact Prime.pos hp
  have h₅: p^2 ≤ p := by exact Nat.le_of_dvd gp h₄
  have g₆: 1 < p := by exact Prime.one_lt hp
  have h₆: p^1 < p^2 := by exact Nat.pow_lt_pow_succ g₆
  linarith


lemma imo_2022_p5_15_20
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  -- (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  (h₃ : p ^ 2 ∣ a ^ p - b !)
  (g₃ : b ! ≤ a ^ p)
  (g₄ : a ^ p - b ! = p) :
  p ^ 2 ∣ p := by
  rw [g₄] at h₃
  exact h₃


lemma imo_2022_p5_15_21
  -- (a b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  -- (h₃ : p ^ 2 ∣ a ^ p - b !)
  -- (g₃ : b ! ≤ a ^ p)
  -- (g₄ : a ^ p - b ! = p)
  (h₄ : p ^ 2 ∣ p) :
  False := by
  have gp: 0 < p := by exact Prime.pos hp
  have h₅: p^2 ≤ p := by exact Nat.le_of_dvd gp h₄
  have g₆: 1 < p := by exact Prime.one_lt hp
  have h₆: p^1 < p^2 := by exact Nat.pow_lt_pow_succ g₆
  linarith


lemma imo_2022_p5_15_22
  (a b p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  (h₃ : p ^ 2 ∣ a ^ p - b !)
  -- (g₃ : b ! ≤ a ^ p)
  (g₄ : a ^ p - b ! = p) :
  p ^ 2 ≤ p := by
  have gp: 0 < p := by exact Prime.pos hp
  have h₄: p^2 ∣ p := by
    rw [g₄] at h₃
    exact h₃
  exact Nat.le_of_dvd gp h₄


lemma imo_2022_p5_15_23
  -- (a b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p)
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  -- (h₃ : p ^ 2 ∣ a ^ p - b !)
  -- (g₃ : b ! ≤ a ^ p)
  -- (g₄ : a ^ p - b ! = p)
  -- (h₄ : p ^ 2 ∣ p)
  -- (gp : 0 < p)
  (h₅ : p ^ 2 ≤ p) :
  False := by
  have g₆: 1 < p := by exact Prime.one_lt hp
  have h₆: p^1 < p^2 := by exact Nat.pow_lt_pow_succ g₆
  linarith


lemma imo_2022_p5_15_24
  -- (a b : ℕ)
  (p : ℕ)
  -- (h₀ : 0 < a ∧ 0 < b)
  (hp : Nat.Prime p) :
  -- (h₁ : a ^ p = b ! + p)
  -- (hbp : p ≤ b)
  -- (h₂ : p ∣ a)
  -- (hb2p : 2 * p ≤ b)
  -- (h₃ : p ^ 2 ∣ a ^ p - b !)
  -- (g₃ : b ! ≤ a ^ p)
  -- (g₄ : a ^ p - b ! = p)
  -- (h₄ : p ^ 2 ∣ p)
  -- (h₅ : p ^ 2 ≤ p) :
  p ^ 1 < p ^ 2 := by
  refine Nat.pow_lt_pow_succ ?_
  exact Prime.one_lt hp
