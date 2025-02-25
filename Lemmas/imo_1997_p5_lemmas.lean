import Mathlib
set_option linter.unusedVariables.analyzeTactics true

open Nat Real


lemma imo_1997_p5_1
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (g : x ^ y ^ 2 = (x ^ y) ^ y)
  (hxy : x ≤ y)
  (h₁ : (x ^ y) ^ y = y ^ x) :
  x ^ y ≤ y := by
  by_contra! hc
  have h₂: y^x ≤ y^y := by
    { exact Nat.pow_le_pow_of_le_right h₀.2 hxy }
  have h₃: y^y < (x^y)^y := by
    refine Nat.pow_lt_pow_left hc ?_
    refine Nat.pos_iff_ne_zero.mp h₀.2
  rw [h₁] at h₃
  linarith [h₂, h₃]


lemma imo_1997_p5_1_1
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (hxy : x ≤ y)
  (h₁ : (x ^ y) ^ y = y ^ x)
  (hc : y < x ^ y) :
  False := by
  have h₂: y^x ≤ y^y := by
    { exact Nat.pow_le_pow_of_le_right h₀.2 hxy }
  have h₃: y^y < (x^y)^y := by
    refine Nat.pow_lt_pow_left hc ?_
    refine Nat.pos_iff_ne_zero.mp h₀.2
  rw [h₁] at h₃
  linarith [h₂, h₃]


lemma imo_1997_p5_1_2
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (hxy : x ≤ y)
  (h₁ : (x ^ y) ^ y = y ^ x)
  (hc : y < x ^ y)
  (h₂ : y ^ x ≤ y ^ y) :
  False := by
  have h₃: y^y < (x^y)^y := by
    refine Nat.pow_lt_pow_left hc ?_
    refine Nat.pos_iff_ne_zero.mp h₀.2
  rw [h₁] at h₃
  linarith [h₂, h₃]


lemma imo_1997_p5_1_3
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (hxy : x ≤ y)
  -- (h₁ : (x ^ y) ^ y = y ^ x)
  (hc : y < x ^ y) :
  -- (h₂ : y ^ x ≤ y ^ y) :
  y ^ y < (x ^ y) ^ y := by
  refine Nat.pow_lt_pow_left hc ?_
  exact Nat.pos_iff_ne_zero.mp h₀.2


lemma imo_1997_p5_2
  (k : ℕ)
  (hk : 5 ≤ k) :
  4 * k < 2 ^ k := by
  -- Proceed by induction on k
  induction' k using Nat.case_strong_induction_on with n ih
  -- Base case: k = 0 is not possible since 5 ≤ k
  -- so we start directly with k = 5 as the base case
  . norm_num
  by_cases h₀ : n < 5
  . have hn: n = 4 := by linarith
    rw [hn]
    norm_num
  . push_neg at h₀
    have ih₁ : 4 * n < 2 ^ n := ih n (le_refl n) h₀
    rw [mul_add, pow_add, mul_one, pow_one, mul_two]
    refine Nat.add_lt_add ih₁ ?_
    refine lt_trans ?_ ih₁
    refine (Nat.lt_mul_iff_one_lt_right (by norm_num)).mpr ?_
    refine Nat.lt_of_lt_of_le ?_ h₀
    norm_num


lemma imo_1997_p5_2_1
  (n : ℕ)
  (ih : ∀ m ≤ n, 5 ≤ m → 4 * m < 2 ^ m)
  (hk : 5 ≤ succ n) :
  4 * succ n < 2 ^ succ n := by
  by_cases h₀ : n < 5
  . rw [succ_eq_add_one] at hk
    have hn: n = 4 := by linarith
    rw [hn]
    norm_num
  . push_neg at h₀
    have ih₁ : 4 * n < 2 ^ n := ih n (le_refl n) h₀
    rw [succ_eq_add_one, mul_add, pow_add, mul_one, pow_one, mul_two]
    refine Nat.add_lt_add ih₁ ?_
    refine lt_trans ?_ ih₁
    refine (Nat.lt_mul_iff_one_lt_right (by norm_num)).mpr ?_
    refine Nat.lt_of_lt_of_le ?_ h₀
    norm_num


lemma imo_1997_p5_2_2
  (n : ℕ)
  -- (ih : ∀ m ≤ n, 5 ≤ m → 4 * m < 2 ^ m)
  (hk : 5 ≤ succ n)
  (h₀ : n < 5) :
  4 * succ n < 2 ^ succ n := by
  rw [succ_eq_add_one] at hk
  have hn: n = 4 := by linarith
  rw [hn]
  norm_num


lemma imo_1997_p5_2_3
  (n : ℕ)
  (ih : ∀ m ≤ n, 5 ≤ m → 4 * m < 2 ^ m)
  -- (hk : 5 ≤ succ n)
  (h₀ : 5 ≤ n) :
  4 * succ n < 2 ^ succ n := by
  have ih₁ : 4 * n < 2 ^ n := ih n (le_refl n) h₀
  rw [succ_eq_add_one, mul_add, pow_add, mul_one, pow_one, mul_two]
  refine Nat.add_lt_add ih₁ ?_
  refine lt_trans ?_ ih₁
  refine (Nat.lt_mul_iff_one_lt_right (by norm_num)).mpr ?_
  refine Nat.lt_of_lt_of_le ?_ h₀
  norm_num


lemma imo_1997_p5_2_4
  (n : ℕ)
  -- (ih : ∀ m ≤ n, 5 ≤ m → 4 * m < 2 ^ m)
  -- (hk : 5 ≤ succ n)
  (h₀ : 5 ≤ n)
  (ih₁ : 4 * n < 2 ^ n) :
  4 * succ n < 2 ^ succ n := by
  rw [succ_eq_add_one, mul_add, pow_add, mul_one, pow_one, mul_two]
  refine Nat.add_lt_add ih₁ ?_
  refine lt_trans ?_ ih₁
  refine (Nat.lt_mul_iff_one_lt_right (by norm_num)).mpr ?_
  refine Nat.lt_of_lt_of_le ?_ h₀
  norm_num


lemma imo_1997_p5_2_5
  (n : ℕ)
  -- (ih : ∀ m ≤ n, 5 ≤ m → 4 * m < 2 ^ m)
  -- (hk : 5 ≤ succ n)
  (h₀ : 5 ≤ n)
  (ih₁ : 4 * n < 2 ^ n) :
  4 * n + 4 < 2 ^ n + 2 ^ n := by
  refine Nat.add_lt_add ih₁ ?_
  refine lt_trans ?_ ih₁
  refine (Nat.lt_mul_iff_one_lt_right (by norm_num)).mpr ?_
  refine Nat.lt_of_lt_of_le ?_ h₀
  norm_num


lemma imo_1997_p5_2_6
  (n : ℕ)
  -- (ih : ∀ m ≤ n, 5 ≤ m → 4 * m < 2 ^ m)
  -- (hk : 5 ≤ succ n)
  (h₀ : 5 ≤ n)
  (ih₁ : 4 * n < 2 ^ n) :
  4 < 2 ^ n := by
  refine lt_trans ?_ ih₁
  refine (Nat.lt_mul_iff_one_lt_right (by norm_num)).mpr ?_
  refine Nat.lt_of_lt_of_le ?_ h₀
  norm_num


lemma imo_1997_p5_2_7
  (n : ℕ)
  -- (ih : ∀ m ≤ n, 5 ≤ m → 4 * m < 2 ^ m)
  -- (hk : 5 ≤ succ n)
  (h₀ : 5 ≤ n) :
  -- (ih₁ : 4 * n < 2 ^ n) :
  4 < 4 * n := by
  refine (Nat.lt_mul_iff_one_lt_right (by norm_num)).mpr ?_
  refine Nat.lt_of_lt_of_le ?_ h₀
  norm_num


lemma imo_1997_p5_3
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x^(y^2) = y^x)
  (g₁ : x^(y^2) = (x^y)^y)
  (hxy : x ≤ y) :
  (x, y) = (1, 1) ∨ (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by
  rw [g₁] at h₁
  have g2: x^y ≤ y := by
    exact imo_1997_p5_1 x y h₀ hxy h₁
  have g3: x = 1 := by
    by_contra! hc
    have g3: 2 ≤ x := by
      by_contra! gc
      interval_cases x
      . linarith
      . omega
    have g4: 2 ^ y ≤ x ^ y := by { exact Nat.pow_le_pow_of_le_left g3 y }
    have g5: y < 2 ^ y := by exact Nat.lt_two_pow_self
    linarith
  rw [g3] at h₁
  simp at h₁
  left
  norm_num
  exact { left := g3, right := id h₁.symm }


lemma imo_1997_p5_3_1
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : (x ^ y) ^ y = y ^ x)
  (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  (hxy : x ≤ y)
  (g₂ : x ^ y ≤ y) :
  (x, y) = (1, 1) := by
  have g₃: x = 1 := by
    by_contra! hc
    have g3: 2 ≤ x := by
      by_contra! gc
      interval_cases x
      . linarith
      . omega
    have g4: 2^y ≤ x^y := by { exact Nat.pow_le_pow_of_le_left g3 y }
    have g5: y < 2^y := by exact Nat.lt_two_pow_self
    linarith
  rw [g₃] at h₁
  simp at h₁
  norm_num
  exact { left := g₃, right := id h₁.symm }


lemma imo_1997_p5_3_2
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : (x ^ y) ^ y = y ^ x)
  (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  (hxy : x ≤ y)
  (g2 : x ^ y ≤ y) :
  x = 1 := by
  by_contra! hc
  have g₃: 2 ≤ x := by
    by_contra! gc
    interval_cases x
    . linarith
    . omega
  have g₄: 2^y ≤ x ^ y := by { exact Nat.pow_le_pow_of_le_left g₃ y }
  have g₅: y < 2 ^ y := by exact Nat.lt_two_pow_self
  linarith


lemma imo_1997_p5_3_3
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : (x ^ y) ^ y = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : x ≤ y)
  (g₂ : x ^ y ≤ y)
  -- (hc : ¬x = 1)
  (g₃ : 2 ≤ x) :
  False := by
  have g₄: 2^y ≤ x ^ y := by { exact Nat.pow_le_pow_of_le_left g₃ y }
  have g₅: y < 2 ^ y := by exact Nat.lt_two_pow_self
  linarith


lemma imo_1997_p5_3_4
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : (x ^ y) ^ y = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : x ≤ y)
  (g2 : x ^ y ≤ y)
  -- (hc : ¬x = 1)
  -- (g₃ : 2 ≤ x)
  (g₄ : 2 ^ y ≤ x ^ y) :
  False := by
  have g₅: y < 2 ^ y := by exact Nat.lt_two_pow_self
  linarith


lemma imo_1997_p5_3_5
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : (x ^ y) ^ y = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : x ≤ y)
  -- (g2 : x ^ y ≤ y)
  -- (hc : ¬x = 1)
  (g₃ : 2 ≤ x) :
  -- (g4 : 2 ^ y ≤ x ^ y) :
  y + 2 < 2 ^ y + x := by
  refine lt_add_of_lt_add_left ?_ g₃
  refine add_lt_add_right ?_ 2
  exact Nat.lt_two_pow_self


lemma imo_1997_p5_3_6
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  (h₁ : (x ^ y) ^ y = y ^ x)
  (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  (hxy : x ≤ y)
  (g₂ : x ^ y ≤ y)
  (g₃ : x = 1) :
  y = 1 := by
  rw [g₃] at h₁
  simp at h₁
  exact id h₁.symm


lemma imo_1997_p5_4
  (x: ℕ)
  (h₀: 0 < x):
  (↑x = Real.exp (Real.log ↑x)):= by
  have hx_pos : 0 < (↑x : ℝ) := by exact Nat.cast_pos.mpr h₀
  symm
  exact Real.exp_log hx_pos


lemma imo_1997_p5_5
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x) :
  y ^ 2 < x := by
  by_cases hy: 1 < y
  . have hx: 2 ≤ x := by linarith
    have h₂: y ^ x < x ^ x := by
      refine Nat.pow_lt_pow_left hxy ?_
      exact Nat.ne_of_lt' h₀.1
    rw [← h₁] at h₂
    exact (Nat.pow_lt_pow_iff_right hx).mp h₂
  . push_neg at hy
    interval_cases y
    . simp
      exact h₀.1
    . simp at *
      assumption


lemma imo_1997_p5_5_1
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x)
  (hy : 1 < y) :
  y ^ 2 < x := by
  have hx: 2 ≤ x := by linarith
  have h₂: y ^ x < x ^ x := by
    refine Nat.pow_lt_pow_left hxy ?_
    exact Nat.ne_of_lt' h₀.1
  rw [← h₁] at h₂
  exact (Nat.pow_lt_pow_iff_right hx).mp h₂


lemma imo_1997_p5_5_2
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x) :
  -- (hy : 1 < y)
  -- (hx : 2 ≤ x) :
  y ^ x < x ^ x := by
  refine Nat.pow_lt_pow_left hxy ?_
  exact Nat.ne_of_lt' h₀.1


lemma imo_1997_p5_5_3
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (hy : 1 < y)
  (hx : 2 ≤ x)
  (h₂ : y ^ x < x ^ x) :
  y ^ 2 < x := by
  rw [← h₁] at h₂
  exact (Nat.pow_lt_pow_iff_right hx).mp h₂


lemma imo_1997_p5_5_4
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x)
  (hy : ¬1 < y) :
  y ^ 2 < x := by
  push_neg at hy
  interval_cases y
  . simp
    exact h₀.1
  . simp at *
    assumption


lemma imo_1997_p5_6
  (x y: ℕ)
  (h₀: 0 < x ∧ 0 < y)
  (h₁: x ^ y ^ 2 = y ^ x) :
  (↑x / ↑y^2) ^ y ^ 2 = (↑y:ℝ)^ ((↑x:ℝ) - 2 * ↑y ^ 2) := by
  have g₁: (↑x:ℝ) ^ (↑y:ℝ) ^ 2 = (↑y:ℝ) ^ (↑x:ℝ) := by
    norm_cast
  have g₂: 0 < ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)) := by
    norm_cast
    exact pow_pos h₀.2 _
  have g₃: ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
        = ((↑y:ℝ) ^ (↑x:ℝ)) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)) := by
    refine (div_left_inj' ?_).mpr g₁
    norm_cast
    refine pow_ne_zero _ ?_
    linarith [h₀.2]
  have gy: 0 < (↑y:ℝ) := by
    norm_cast
    exact h₀.2
  rw [← Real.rpow_sub gy (↑x) (2 * ↑y ^ 2)] at g₃
  have g₄: ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
        = (↑x / ↑y^2) ^ y ^ 2 := by
    have g₅: (↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2) = ((↑y:ℝ) ^ 2) ^ ((↑y:ℝ) ^ 2) := by
      norm_cast
      refine pow_mul y 2 (y^2)
    rw [g₅]
    symm
    norm_cast
    -- repeat {rw [Nat.cast_pow]}
    have g₆: ((↑x:ℝ) / ↑y ^ 2) ^ y ^ 2 = ↑x ^ y ^ 2 / (↑y ^ 2) ^ y ^ 2 := by
      refine div_pow (↑x:ℝ) ((↑y:ℝ) ^ 2) (y^2)
    norm_cast at *
  rw [g₄] at g₃
  norm_cast at *


lemma imo_1997_p5_6_1
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y) :
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : ↑x ^ ↑y ^ 2 = ↑y ^ ↑x) :
  0 < ↑y ^ (2 * ↑y ^ 2) := by
  -- norm_cast
  exact pow_pos h₀.2 _


lemma imo_1997_p5_6_2
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  (g₁ : (↑x:ℝ) ^ (↑y:ℝ) ^ 2 = (↑y:ℝ) ^ (↑x:ℝ)) :
  -- (g₂ : 0 < ↑y ^ (2 * ↑y ^ 2)) :
  (↑x / ↑y ^ 2) ^ y ^ 2 = (↑y:ℝ) ^ ((↑x:ℝ) - 2 * ↑y ^ 2) := by
  have g₃: ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
        = ((↑y:ℝ) ^ (↑x:ℝ)) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)) := by
    refine (div_left_inj' ?_).mpr g₁
    norm_cast
    refine pow_ne_zero _ ?_
    linarith [h₀.2]
  have gy: 0 < (↑y:ℝ) := by
    norm_cast
    exact h₀.2
  rw [← Real.rpow_sub gy (↑x) (2 * ↑y ^ 2)] at g₃
  have g₄: ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
        = (↑x / ↑y^2) ^ y ^ 2 := by
    have g₅: (↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2) = ((↑y:ℝ) ^ 2) ^ ((↑y:ℝ) ^ 2) := by
      norm_cast
      refine pow_mul y 2 (y^2)
    rw [g₅]
    symm
    norm_cast
    -- repeat {rw [Nat.cast_pow]}
    have g₆: ((↑x:ℝ) / ↑y ^ 2) ^ y ^ 2 = ↑x ^ y ^ 2 / (↑y ^ 2) ^ y ^ 2 := by
      refine div_pow (↑x:ℝ) ((↑y:ℝ) ^ 2) (y^2)
    norm_cast at *
  rw [g₄] at g₃
  norm_cast at *


lemma imo_1997_p5_6_3
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y) :
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : ↑x ^ ↑y ^ 2 = ↑y ^ ↑x)
  -- (g₂ : 0 < ↑y ^ (2 * ↑y ^ 2)) :
  ↑y ^ (2 * ↑y ^ 2) ≠ 0 := by
  norm_cast
  refine pow_ne_zero _ ?_
  linarith [h₀.2]


lemma imo_1997_p5_6_4
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  (g₁ : (↑x:ℝ) ^ (↑y:ℝ) ^ 2 = (↑y:ℝ) ^ (↑x:ℝ)) :
  -- (g₂ : 0 < ↑y ^ (2 * ↑y ^ 2))
  -- (g₃ : ↑x ^ ↑y ^ 2 / ↑y ^ (2 * ↑y ^ 2) = ↑y ^ ↑x / ↑y ^ (2 * ↑y ^ 2))
  -- (gy : 0 < ↑y) :
  ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
        = ((↑y:ℝ) ^ (↑x:ℝ)) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)) := by
  refine (div_left_inj' ?_).mpr g₁
  norm_cast
  refine pow_ne_zero _ ?_
  linarith [h₀.2]


lemma imo_1997_p5_6_5
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : ↑x ^ ↑y ^ 2 = ↑y ^ ↑x)
  -- (g₂ : 0 < ↑y ^ (2 * ↑y ^ 2))
  (g₃ : ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
        = ((↑y:ℝ) ^ (↑x:ℝ)) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)))
  (gy : 0 < (↑y:ℝ)) :
  (↑x / ↑y ^ 2) ^ y ^ 2 = (↑y:ℝ) ^ ((↑x:ℝ) - 2 * ↑y ^ 2) := by
  rw [← Real.rpow_sub gy (↑x) (2 * ↑y ^ 2)] at g₃
  have g₄: ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
        = (↑x / ↑y^2) ^ y ^ 2 := by
    have g₅: (↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2) = ((↑y:ℝ) ^ 2) ^ ((↑y:ℝ) ^ 2) := by
      norm_cast
      refine pow_mul y 2 (y^2)
    rw [g₅]
    symm
    norm_cast
    -- repeat {rw [Nat.cast_pow]}
    have g₆: ((↑x:ℝ) / ↑y ^ 2) ^ y ^ 2 = ↑x ^ y ^ 2 / (↑y ^ 2) ^ y ^ 2 := by
      refine div_pow (↑x:ℝ) ((↑y:ℝ) ^ 2) (y^2)
    norm_cast at *
  rw [g₄] at g₃
  norm_cast at *


lemma imo_1997_p5_6_6
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : ↑x ^ ↑y ^ 2 = ↑y ^ ↑x)
  -- (g₂ : 0 < ↑y ^ (2 * ↑y ^ 2))
  (g₃ : ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
        = ((↑y:ℝ) ^ (↑x:ℝ)) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)))
  (gy : 0 < (↑y:ℝ)) :
  ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)) = (↑x / ↑y^2) ^ y ^ 2 := by
  have g₅: (↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2) = ((↑y:ℝ) ^ 2) ^ ((↑y:ℝ) ^ 2) := by
    norm_cast
    refine pow_mul y 2 (y^2)
  rw [g₅]
  symm
  norm_cast
  -- repeat {rw [Nat.cast_pow]}
  have g₆: ((↑x:ℝ) / ↑y ^ 2) ^ y ^ 2 = ↑x ^ y ^ 2 / (↑y ^ 2) ^ y ^ 2 := by
    refine div_pow (↑x:ℝ) ((↑y:ℝ) ^ 2) (y^2)
  norm_cast at *


lemma imo_1997_p5_6_7
  -- (x : ℕ)
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : ↑x ^ ↑y ^ 2 = ↑y ^ ↑x)
  -- (g₂ : 0 < ↑y ^ (2 * ↑y ^ 2))
  -- (g₃ : ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
  --       = ((↑y:ℝ) ^ (↑x:ℝ)) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)))
  (hy : 0 < y)
  (hxy : y < x) :
  (↑y:ℝ) ^ (2 * (y ^ 2)) < ((↑x:ℝ) ^ 2) ^ (y ^ 2) := by
  rw [pow_mul (↑y:ℝ) 2 (y ^ 2)]
  refine pow_lt_pow_left₀ ?_ ?_ ?_
  . norm_cast
    exact Nat.pow_lt_pow_left hxy (by decide)
  . exact sq_nonneg (↑y:ℝ)
  . symm
    refine Nat.ne_of_lt ?_
    exact pos_pow_of_pos 2 hy


lemma imo_1997_p5_6_8
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : ↑x ^ ↑y ^ 2 = ↑y ^ ↑x)
  -- (g₂ : 0 < ↑y ^ (2 * ↑y ^ 2))
  (g₃ : ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
        = ((↑y:ℝ) ^ (↑x:ℝ)) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)))
  (gy : 0 < (↑y:ℝ))
  (g₅ : (↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2) = ((↑y:ℝ) ^ 2) ^ ((↑y:ℝ) ^ 2)) :
  ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)) = (↑x / ↑y^2) ^ y ^ 2 := by
  rw [g₅]
  symm
  norm_cast
  have g₆: ((↑x:ℝ) / ↑y ^ 2) ^ y ^ 2 = ↑x ^ y ^ 2 / (↑y ^ 2) ^ y ^ 2 := by
    refine div_pow (↑x:ℝ) ((↑y:ℝ) ^ 2) (y^2)
  norm_cast at *


lemma imo_1997_p5_6_9
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : ↑x ^ ↑y ^ 2 = ↑y ^ ↑x)
  -- (g₂ : 0 < ↑y ^ (2 * ↑y ^ 2))
  (g₃ : ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2))
        = ((↑y:ℝ) ^ (↑x:ℝ)) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)))
  (gy : 0 < (↑y:ℝ))
  (g₅ : (↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2) = ((↑y:ℝ) ^ 2) ^ ((↑y:ℝ) ^ 2)) :
  ((↑x:ℝ) ^ (↑y:ℝ) ^ 2) / ((↑y:ℝ) ^ (2 * (↑y:ℝ) ^ 2)) = (↑x / ↑y^2) ^ y ^ 2 := by
  rw [g₅]
  symm
  norm_cast
  have g₆: ((↑x:ℝ) / ↑y ^ 2) ^ y ^ 2 = ↑x ^ y ^ 2 / (↑y ^ 2) ^ y ^ 2 := by
    refine div_pow (↑x:ℝ) ((↑y:ℝ) ^ 2) (y^2)
  norm_cast at *


lemma imo_1997_p5_6_10
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : ↑x ^ ↑y ^ 2 = ↑y ^ ↑x)
  -- (g₂ : 0 < ↑y ^ (2 * ↑y ^ 2))
  (g₃ : ↑x ^ ↑y ^ 2 / ↑y ^ (2 * ↑y ^ 2) = ↑y ^ (↑x - 2 * ↑y ^ 2))
  (gy : 0 < ↑y)
  (g₄ : ↑x ^ ↑y ^ 2 / ↑y ^ (2 * ↑y ^ 2) = (↑x / ↑y ^ 2) ^ y ^ 2) :
  (↑x / ↑y ^ 2) ^ y ^ 2 = ↑y ^ (↑x - 2 * ↑y ^ 2) := by
  rw [g₄] at g₃
  norm_cast at *


lemma imo_1997_p5_7
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x) :
  2 * y ^ 2 < x := by
  by_cases hy1: y = 1
  . rw [hy1]
    norm_num
    by_contra! hc
    interval_cases x
    . linarith
    . linarith
    . rw [hy1] at h₁
      simp at h₁
  . have hy: 1 < y := by
      contrapose! hy1
      linarith
    clear hy1
    have h₂: (↑y:ℝ) ^ 2 < ↑x := by
      norm_cast
      exact imo_1997_p5_5 x y h₀ h₁ hxy
    have h₃: 1 < ↑x / (↑y:ℝ) ^ 2 := by
      refine (one_lt_div ?_).mpr h₂
      norm_cast
      exact pow_pos h₀.2 2  -- rw ← one_mul ((↑y:ℝ)^2) at h₂, refine lt_div_iff_mul_lt.mpr h₂, },
    have h₄: 1 < (↑x / (↑y:ℝ)^2)^(y^2) := by
      refine one_lt_pow₀ h₃ ?_
      refine Nat.ne_of_gt ?_
      refine sq_pos_of_pos ?_
      exact lt_of_succ_lt hy
    have h₅: (↑x/ (↑y:ℝ)^2)^(y^2) = (↑y:ℝ)^((↑x:ℝ) - 2*(↑y:ℝ)^2) := by
      exact imo_1997_p5_6 x y h₀ h₁
    rw [h₅] at h₄
    have h₆: 0 < (↑x:ℝ) - 2 * (↑y:ℝ) ^ 2 := by
      by_contra! hc
      cases' lt_or_eq_of_le hc with hlt heq
      . have gy: 1 < (↑y:ℝ) := by
          norm_cast
        have glt: (↑x:ℝ) - 2*(↑y:ℝ)^2 < (↑0:ℝ) := by
          norm_cast at *
        have g₁: (↑y:ℝ) ^ ((↑x:ℝ) - 2*(↑y:ℝ)^2) < (↑y:ℝ) ^ (↑0:ℝ) := by
          exact Real.rpow_lt_rpow_of_exponent_lt gy glt
        simp at g₁
        linarith[ h₄,g₁]
      . rw [heq] at h₄
        simp at h₄
    simp at h₆
    norm_cast at h₆


lemma imo_1997_p5_7_1
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x)
  (hy1 : y = 1) :
  2 * y ^ 2 < x := by
  rw [hy1]
  norm_num
  by_contra! hc
  interval_cases x
  . linarith
  . linarith
  . rw [hy1] at h₁
    simp at h₁


lemma imo_1997_p5_7_2
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x)
  (hy1 : y = 1) :
  2 < x := by
  by_contra! hc
  interval_cases x
  . linarith
  . linarith
  . rw [hy1] at h₁
    simp at h₁


lemma imo_1997_p5_7_3
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x)
  (hy1 : y = 1)
  (hc : x ≤ 2) :
  False := by
  interval_cases x
  . linarith
  . linarith
  . rw [hy1] at h₁
    simp at h₁


lemma imo_1997_p5_7_4
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x)
  (hy : 1 < y) :
  2 * y ^ 2 < x := by
  have h₂: (↑y:ℝ) ^ 2 < ↑x := by
    norm_cast
    exact imo_1997_p5_5 x y h₀ h₁ hxy
  have h₃: 1 < ↑x / (↑y:ℝ) ^ 2 := by
    refine (one_lt_div ?_).mpr h₂
    norm_cast
    exact pow_pos h₀.2 2
  have h₄: 1 < (↑x / (↑y:ℝ)^2)^(y^2) := by
    refine one_lt_pow₀ h₃ ?_
    refine Nat.ne_of_gt ?_
    refine sq_pos_of_pos ?_
    exact lt_of_succ_lt hy
  have h₅: (↑x/ (↑y:ℝ)^2)^(y^2) = (↑y:ℝ)^((↑x:ℝ) - 2*(↑y:ℝ)^2) := by
    exact imo_1997_p5_6 x y h₀ h₁
  rw [h₅] at h₄
  have h₆: 0 < (↑x:ℝ) - 2 * (↑y:ℝ) ^ 2 := by
    by_contra! hc
    cases' lt_or_eq_of_le hc with hlt heq
    . have gy: 1 < (↑y:ℝ) := by
        norm_cast
      have glt: (↑x:ℝ) - 2*(↑y:ℝ)^2 < (↑0:ℝ) := by
        norm_cast at *
      have g₁: (↑y:ℝ) ^ ((↑x:ℝ) - 2*(↑y:ℝ)^2) < (↑y:ℝ) ^ (↑0:ℝ) := by
        exact Real.rpow_lt_rpow_of_exponent_lt gy glt
      simp at g₁
      linarith[ h₄,g₁]
    . rw [heq] at h₄
      simp at h₄
  simp at h₆
  norm_cast at h₆


lemma imo_1997_p5_7_5
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  (hy : 1 < y)
  (h₂ : (↑y:ℝ) ^ 2 < ↑x) :
  2 * y ^ 2 < x := by
  have h₃: 1 < ↑x / (↑y:ℝ) ^ 2 := by
    refine (one_lt_div ?_).mpr h₂
    norm_cast
    exact pow_pos h₀.2 2  -- rw ← one_mul ((↑y:ℝ)^2) at h₂, refine lt_div_iff_mul_lt.mpr h₂, },
  have h₄: 1 < (↑x / (↑y:ℝ)^2)^(y^2) := by
    refine one_lt_pow₀ h₃ ?_
    refine Nat.ne_of_gt ?_
    refine sq_pos_of_pos ?_
    exact lt_of_succ_lt hy
  have h₅: (↑x/ (↑y:ℝ)^2)^(y^2) = (↑y:ℝ)^((↑x:ℝ) - 2*(↑y:ℝ)^2) := by
    exact imo_1997_p5_6 x y h₀ h₁
  rw [h₅] at h₄
  have h₆: 0 < (↑x:ℝ) - 2 * (↑y:ℝ) ^ 2 := by
    by_contra! hc
    cases' lt_or_eq_of_le hc with hlt heq
    . have gy: 1 < (↑y:ℝ) := by
        norm_cast
      have glt: (↑x:ℝ) - 2*(↑y:ℝ)^2 < (↑0:ℝ) := by
        norm_cast at *
      have g₁: (↑y:ℝ) ^ ((↑x:ℝ) - 2*(↑y:ℝ)^2) < (↑y:ℝ) ^ (↑0:ℝ) := by
        exact Real.rpow_lt_rpow_of_exponent_lt gy glt
      simp at g₁
      linarith[ h₄,g₁]
    . rw [heq] at h₄
      simp at h₄
  simp at h₆
  norm_cast at h₆


lemma imo_1997_p5_7_6
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (hy : 1 < y)
  (h₂ : (↑y:ℝ) ^ 2 < ↑x) :
  1 < ↑x / (↑y:ℝ) ^ 2 := by
  refine (one_lt_div ?_).mpr h₂
  norm_cast
  exact pow_pos h₀.2 2


lemma imo_1997_p5_7_7
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  (hy : 1 < y)
  -- (h₂ : ↑y ^ 2 < ↑x)
  (h₃ : 1 < ↑x / (↑y:ℝ) ^ 2) :
  2 * y ^ 2 < x := by
  have h₄: 1 < (↑x / (↑y:ℝ)^2)^(y^2) := by
    refine one_lt_pow₀ h₃ ?_
    refine Nat.ne_of_gt ?_
    refine sq_pos_of_pos ?_
    exact lt_of_succ_lt hy
  have h₅: (↑x/ (↑y:ℝ)^2)^(y^2) = (↑y:ℝ)^((↑x:ℝ) - 2*(↑y:ℝ)^2) := by
    exact imo_1997_p5_6 x y h₀ h₁
  rw [h₅] at h₄
  have h₆: 0 < (↑x:ℝ) - 2 * (↑y:ℝ) ^ 2 := by
    by_contra! hc
    cases' lt_or_eq_of_le hc with hlt heq
    . have gy: 1 < (↑y:ℝ) := by
        norm_cast
      have glt: (↑x:ℝ) - 2*(↑y:ℝ)^2 < (↑0:ℝ) := by
        norm_cast at *
      have g₁: (↑y:ℝ) ^ ((↑x:ℝ) - 2*(↑y:ℝ)^2) < (↑y:ℝ) ^ (↑0:ℝ) := by
        exact Real.rpow_lt_rpow_of_exponent_lt gy glt
      simp at g₁
      linarith[ h₄,g₁]
    . rw [heq] at h₄
      simp at h₄
  simp at h₆
  norm_cast at h₆


lemma imo_1997_p5_7_8
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  (hy : 1 < y)
  -- (h₂ : ↑y ^ 2 < ↑x)
  (h₃ : 1 < ↑x / ↑y ^ 2) :
  1 < (↑x / ↑y ^ 2) ^ y ^ 2 := by
  refine one_lt_pow₀ h₃ ?_
  refine Nat.ne_of_gt ?_
  refine sq_pos_of_pos ?_
  exact lt_of_succ_lt hy


lemma imo_1997_p5_7_9
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  (hy : 1 < y)
  -- (h₂ : ↑y ^ 2 < ↑x)
  -- (h₃ : 1 < ↑x / ↑y ^ 2)
  (h₄ : 1 < (↑x / (↑y:ℝ)^2)^(y^2))
  (h₅ : (↑x/ (↑y:ℝ)^2)^(y^2) = (↑y:ℝ)^((↑x:ℝ) - 2*(↑y:ℝ)^2)) :
  2 * y ^ 2 < x := by
  rw [h₅] at h₄
  have h₆: 0 < (↑x:ℝ) - 2 * (↑y:ℝ) ^ 2 := by
    by_contra! hc
    cases' lt_or_eq_of_le hc with hlt heq
    . have gy: 1 < (↑y:ℝ) := by
        norm_cast
      have glt: (↑x:ℝ) - 2*(↑y:ℝ)^2 < (↑0:ℝ) := by
        norm_cast at *
      have g₁: (↑y:ℝ) ^ ((↑x:ℝ) - 2*(↑y:ℝ)^2) < (↑y:ℝ) ^ (↑0:ℝ) := by
        exact Real.rpow_lt_rpow_of_exponent_lt gy glt
      simp at g₁
      linarith[ h₄,g₁]
    . rw [heq] at h₄
      simp at h₄
  simp at h₆
  norm_cast at h₆


lemma imo_1997_p5_7_10
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (hy : 1 < y)
  -- (h₂ : ↑y ^ 2 < ↑x)
  -- (h₃ : 1 < ↑x / ↑y ^ 2)
  (h₄ : 1 < ↑y ^ (↑x - 2 * ↑y ^ 2))
  (h₅ : (↑x / ↑y ^ 2) ^ y ^ 2 = ↑y ^ (↑x - 2 * ↑y ^ 2)) :
  0 < ↑x - 2 * ↑y ^ 2 := by
  by_contra! hc
  cases' lt_or_eq_of_le hc with hlt heq
  . have gy: 1 < (↑y:ℝ) := by
      norm_cast
    have glt: (↑x:ℝ) - 2*(↑y:ℝ)^2 < (↑0:ℝ) := by
      norm_cast at *
    have g₁: (↑y:ℝ) ^ ((↑x:ℝ) - 2*(↑y:ℝ)^2) < (↑y:ℝ) ^ (↑0:ℝ) := by
      exact Real.rpow_lt_rpow_of_exponent_lt gy glt
    simp at g₁
    linarith[ h₄,g₁]
  . rw [heq] at h₄
    simp at h₄


lemma imo_1997_p5_7_11
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (hy : 1 < y)
  -- (h₂ : ↑y ^ 2 < ↑x)
  -- (h₃ : 1 < ↑x / ↑y ^ 2)
  (h₄ : 1 < ↑y ^ (↑x - 2 * ↑y ^ 2))
  (h₅ : (↑x / ↑y ^ 2) ^ y ^ 2 = ↑y ^ (↑x - 2 * ↑y ^ 2))
  (hc : ↑x - 2 * ↑y ^ 2 ≤ 0) :
  False := by
  cases' lt_or_eq_of_le hc with hlt heq
  . have gy: 1 < (↑y:ℝ) := by
      norm_cast
    have glt: (↑x:ℝ) - 2*(↑y:ℝ)^2 < (↑0:ℝ) := by
      norm_cast at *
    have g₁: (↑y:ℝ) ^ ((↑x:ℝ) - 2*(↑y:ℝ)^2) < (↑y:ℝ) ^ (↑0:ℝ) := by
      exact Real.rpow_lt_rpow_of_exponent_lt gy glt
    simp at g₁
    linarith[ h₄,g₁]
  . rw [heq] at h₄
    simp at h₄


lemma imo_1997_p5_7_12
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (hy : 1 < y)
  -- (h₂ : ↑y ^ 2 < ↑x)
  -- (h₃ : 1 < ↑x / ↑y ^ 2)
  (h₄ : 1 < ↑y ^ (↑x - 2 * ↑y ^ 2))
  -- (h₅ : (↑x / ↑y ^ 2) ^ y ^ 2 = ↑y ^ (↑x - 2 * ↑y ^ 2))
  -- (hc : ↑x - 2 * ↑y ^ 2 ≤ 0)
  (hlt : ↑x - 2 * ↑y ^ 2 < 0) :
  False := by
  have gy: 1 < (↑y:ℝ) := by
      norm_cast
  have glt: (↑x:ℝ) - 2*(↑y:ℝ)^2 < (↑0:ℝ) := by
    norm_cast at *
  have g₁: (↑y:ℝ) ^ ((↑x:ℝ) - 2*(↑y:ℝ)^2) < (↑y:ℝ) ^ (↑0:ℝ) := by
    exact Real.rpow_lt_rpow_of_exponent_lt gy glt
  simp at g₁
  linarith[ h₄,g₁]


lemma imo_1997_p5_7_13
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (hy : 1 < y)
  -- (h₂ : ↑y ^ 2 < ↑x)
  -- (h₃ : 1 < ↑x / ↑y ^ 2)
  (h₄ : 1 < ↑y ^ (↑x - 2 * ↑y ^ 2))
  -- (h₅ : (↑x / ↑y ^ 2) ^ y ^ 2 = ↑y ^ (↑x - 2 * ↑y ^ 2))
  -- (hc : ↑x - 2 * ↑y ^ 2 ≤ 0)
  -- (hlt : ↑x - 2 * ↑y ^ 2 < 0)
  (gy : 1 < ↑y)
  -- (glt : ↑x - 2 * ↑y ^ 2 < 0)
  (g₁ : ↑y ^ (↑x - 2 * ↑y ^ 2) < ↑y ^ 0) :
  False := by
  simp at g₁
  linarith[ h₄,g₁]


lemma imo_1997_p5_7_14
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (hy : 1 < y)
  -- (h₂ : ↑y ^ 2 < ↑x)
  -- (h₃ : 1 < ↑x / ↑y ^ 2)
  (h₄ : 1 < ↑y ^ (↑x - 2 * ↑y ^ 2))
  (h₅ : (↑x / ↑y ^ 2) ^ y ^ 2 = ↑y ^ (↑x - 2 * ↑y ^ 2))
  (hc : ↑x - 2 * ↑y ^ 2 ≤ 0)
  (heq : ↑x - 2 * ↑y ^ 2 = 0) :
  False := by
  rw [heq] at h₄
  simp at h₄


lemma imo_1997_p5_7_15
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (hy : 1 < y)
  -- (h₂ : ↑y ^ 2 < ↑x)
  -- (h₃ : 1 < ↑x / ↑y ^ 2)
  -- (h₄ : 1 < ↑y ^ (↑x - 2 * ↑y ^ 2))
  -- (h₅ : (↑x / ↑y ^ 2) ^ y ^ 2 = ↑y ^ (↑x - 2 * ↑y ^ 2))
  (h₆ : 0 < ↑x - 2 * ↑y ^ 2) :
  2 * y ^ 2 < x := by
  simp at h₆
  norm_cast at h₆


lemma imo_1997_p5_8
  (x y: ℕ)
  (h₀: 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hyx: y < x) :
  (y^2 ∣ x) := by
  have h₂: (x ^ y ^ 2).factorization = (y^x).factorization := by
    exact congr_arg Nat.factorization h₁
  simp at h₂
  symm at h₂
  have hxy1: 2 * y^2 ≤ x := by exact le_of_lt (imo_1997_p5_7 x y h₀ h₁ hyx)
  have hxy: 2 • y^2 ≤ x := by exact hxy1
  have h₃: 2 • y^2 • x.factorization ≤ x • x.factorization := by
    rw [← smul_assoc]
    refine nsmul_le_nsmul_left ?_ hxy
    norm_num
  rw [← h₂] at h₃
  have h₄: 2 • x • y.factorization = x • (2 • y.factorization) := by
    rw [← smul_assoc, ← smul_assoc]
    have g₄: 2 • x = x • 2 := by
      simp
      exact mul_comm 2 x
    rw [g₄]
  rw [h₄] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  have h₅: (y ^ 2) ^ x ∣ x^x := by
    have g₁: (y ^ 2) ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      refine pow_ne_zero 2 ?_
      linarith
    have g₂: x ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      linarith
    exact (Nat.factorization_le_iff_dvd g₁ g₂).mp h₃
  refine (Nat.pow_dvd_pow_iff ?_).mp h₅
  exact Nat.ne_of_gt h₀.1


lemma imo_1997_p5_8_1
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hyx : y < x)
  (h₂ : Nat.factorization (x ^ y ^ 2) = Nat.factorization (y ^ x)) :
  y ^ 2 ∣ x := by
  simp at h₂
  symm at h₂
  have hxy1: 2 * y^2 ≤ x := by exact le_of_lt (imo_1997_p5_7 x y h₀ h₁ hyx)
  have hxy: 2 • y^2 ≤ x := by exact hxy1
  have h₃: 2 • y^2 • x.factorization ≤ x • x.factorization := by
    rw [← smul_assoc]
    refine nsmul_le_nsmul_left ?_ hxy
    norm_num
  rw [← h₂] at h₃
  have h₄: 2 • x • y.factorization = x • (2 • y.factorization) := by
    rw [← smul_assoc, ← smul_assoc]
    have g₄: 2 • x = x • 2 := by
      simp
      exact mul_comm 2 x
    rw [g₄]
  rw [h₄] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  have h₅: (y ^ 2) ^ x ∣ x^x := by
    have g₁: (y ^ 2) ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      refine pow_ne_zero 2 ?_
      linarith
    have g₂: x ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      linarith
    exact (Nat.factorization_le_iff_dvd g₁ g₂).mp h₃
  refine (Nat.pow_dvd_pow_iff ?_).mp h₅
  exact Nat.ne_of_gt h₀.1


lemma imo_1997_p5_8_2
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hyx : y < x)
  (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x) :
  y ^ 2 ∣ x := by
  have hxy1: 2 * y^2 ≤ x := by exact le_of_lt (imo_1997_p5_7 x y h₀ h₁ hyx)
  have hxy: 2 • y^2 ≤ x := by exact hxy1
  have h₃: 2 • y^2 • x.factorization ≤ x • x.factorization := by
    rw [← smul_assoc]
    refine nsmul_le_nsmul_left ?_ hxy
    norm_num
  rw [← h₂] at h₃
  have h₄: 2 • x • y.factorization = x • (2 • y.factorization) := by
    rw [← smul_assoc, ← smul_assoc]
    have g₄: 2 • x = x • 2 := by
      simp
      exact mul_comm 2 x
    rw [g₄]
  rw [h₄] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  have h₅: (y ^ 2) ^ x ∣ x^x := by
    have g₁: (y ^ 2) ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      refine pow_ne_zero 2 ?_
      linarith
    have g₂: x ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      linarith
    exact (Nat.factorization_le_iff_dvd g₁ g₂).mp h₃
  refine (Nat.pow_dvd_pow_iff ?_).mp h₅
  exact Nat.ne_of_gt h₀.1


lemma imo_1997_p5_8_3
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  (hyx : y < x)
  (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  (hxy : 2 • y ^ 2 ≤ x) :
  y ^ 2 ∣ x := by
  have h₃: 2 • y^2 • x.factorization ≤ x • x.factorization := by
    rw [← smul_assoc]
    refine nsmul_le_nsmul_left ?_ hxy
    norm_num
  rw [← h₂] at h₃
  have h₄: 2 • x • y.factorization = x • (2 • y.factorization) := by
    rw [← smul_assoc, ← smul_assoc]
    have g₄: 2 • x = x • 2 := by
      simp
      exact mul_comm 2 x
    rw [g₄]
  rw [h₄] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  have h₅: (y ^ 2) ^ x ∣ x^x := by
    have g₁: (y ^ 2) ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      refine pow_ne_zero 2 ?_
      linarith
    have g₂: x ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      linarith
    exact (Nat.factorization_le_iff_dvd g₁ g₂).mp h₃
  refine (Nat.pow_dvd_pow_iff ?_).mp h₅
  exact Nat.ne_of_gt h₀.1


lemma imo_1997_p5_8_4
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hyx : y < x)
  -- (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  (hxy : 2 • y ^ 2 ≤ x) :
  2 • y ^ 2 • Nat.factorization x ≤ x • Nat.factorization x := by
  rw [← smul_assoc]
  refine nsmul_le_nsmul_left ?_ hxy
  norm_num


lemma imo_1997_p5_8_5
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hyx : y < x)
  -- (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  (hxy : 2 • y ^ 2 ≤ x) :
  (2 • y ^ 2) • Nat.factorization x ≤ x • Nat.factorization x := by
  refine nsmul_le_nsmul_left ?_ hxy
  norm_num


lemma imo_1997_p5_8_6
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hyx : y < x)
  (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  (hxy1 : 2 * y ^ 2 ≤ x)
  (hxy : 2 • y ^ 2 ≤ x) :
  0 ≤ Nat.factorization x := by
  exact _root_.zero_le x.factorization

lemma imo_1997_p5_8_7
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  (hyx : y < x)
  (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  -- (hxy : 2 • y ^ 2 ≤ x)
  (h₃ : 2 • y ^ 2 • Nat.factorization x ≤ x • Nat.factorization x) :
  y ^ 2 ∣ x := by
  rw [← h₂] at h₃
  have h₄: 2 • x • y.factorization = x • (2 • y.factorization) := by
    rw [← smul_assoc, ← smul_assoc]
    have g₄: 2 • x = x • 2 := by
      simp
      exact mul_comm 2 x
    rw [g₄]
  rw [h₄] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  have h₅: (y ^ 2) ^ x ∣ x^x := by
    have g₁: (y ^ 2) ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      refine pow_ne_zero 2 ?_
      linarith
    have g₂: x ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      linarith
    exact (Nat.factorization_le_iff_dvd g₁ g₂).mp h₃
  refine (Nat.pow_dvd_pow_iff ?_).mp h₅
  exact Nat.ne_of_gt h₀.1


lemma imo_1997_p5_8_8
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  (hyx : y < x)
  -- (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  -- (hxy : 2 • y ^ 2 ≤ x)
  (h₃ : 2 • x • Nat.factorization y ≤ x • Nat.factorization x) :
  y ^ 2 ∣ x := by
  have h₄: 2 • x • y.factorization = x • (2 • y.factorization) := by
    rw [← smul_assoc, ← smul_assoc]
    have g₄: 2 • x = x • 2 := by
      simp
      exact mul_comm 2 x
    rw [g₄]
  rw [h₄] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  have h₅: (y ^ 2) ^ x ∣ x^x := by
    have g₁: (y ^ 2) ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      refine pow_ne_zero 2 ?_
      linarith
    have g₂: x ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      linarith
    exact (Nat.factorization_le_iff_dvd g₁ g₂).mp h₃
  refine (Nat.pow_dvd_pow_iff ?_).mp h₅
  exact Nat.ne_of_gt h₀.1



lemma imo_1997_p5_8_9
  (x y : ℕ) :
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hyx : y < x)
  -- (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  -- (hxy : 2 • y ^ 2 ≤ x)
  -- (h₃ : 2 • x • Nat.factorization y ≤ x • Nat.factorization x) :
  2 • x • Nat.factorization y = x • 2 • Nat.factorization y := by
  rw [← smul_assoc, ← smul_assoc]
  have g₄: 2 • x = x • 2 := by
    simp
    exact mul_comm 2 x
  rw [g₄]
  -- exact nsmul_left_comm (Nat.factorization y) x 2


lemma imo_1997_p5_8_10
  (x y : ℕ) :
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hyx : y < x)
  -- (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  -- (hxy : 2 • y ^ 2 ≤ x)
  -- (h₃ : 2 • x • Nat.factorization y ≤ x • Nat.factorization x) :
  (2 • x) • Nat.factorization y = (x • 2) • Nat.factorization y := by
  have g₄: 2 • x = x • 2 := by
    simp
    exact mul_comm 2 x
  rw [g₄]


lemma imo_1997_p5_8_11
  (x : ℕ) :
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hyx : y < x)
  -- (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  -- (hxy : 2 • y ^ 2 ≤ x)
  -- (h₃ : 2 • x • Nat.factorization y ≤ x • Nat.factorization x) :
  2 • x = x • 2 := by
  rw [smul_eq_mul, smul_eq_mul]
  exact Nat.mul_comm 2 x


lemma imo_1997_p5_8_12
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  (hyx : y < x)
  -- (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  -- (hxy : 2 • y ^ 2 ≤ x)
  (h₃ : 2 • x • Nat.factorization y ≤ x • Nat.factorization x)
  (h₄ : 2 • x • Nat.factorization y = x • 2 • Nat.factorization y) :
  y ^ 2 ∣ x := by
  rw [h₄] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  rw [← Nat.factorization_pow] at h₃
  have h₅: (y ^ 2) ^ x ∣ x^x := by
    have g₁: (y ^ 2) ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      refine pow_ne_zero 2 ?_
      linarith
    have g₂: x ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      linarith
    exact (Nat.factorization_le_iff_dvd g₁ g₂).mp h₃
  refine (Nat.pow_dvd_pow_iff ?_).mp h₅
  exact Nat.ne_of_gt h₀.1


lemma imo_1997_p5_8_13
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  (hyx : y < x)
  -- (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  -- (hxy : 2 • y ^ 2 ≤ x)
  (h₃ : Nat.factorization ((y ^ 2) ^ x) ≤ Nat.factorization (x ^ x)) :
  -- (h₄ : 2 • x • Nat.factorization y = x • 2 • Nat.factorization y) :
  y ^ 2 ∣ x := by
  have h₅: (y ^ 2) ^ x ∣ x^x := by
    have g₁: (y ^ 2) ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      refine pow_ne_zero 2 ?_
      linarith
    have g₂: x ^ x ≠ 0 := by
      refine pow_ne_zero x ?_
      linarith
    exact (Nat.factorization_le_iff_dvd g₁ g₂).mp h₃
  refine (Nat.pow_dvd_pow_iff ?_).mp h₅
  exact Nat.ne_of_gt h₀.1


lemma imo_1997_p5_8_14
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  (hyx : y < x)
  -- (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  -- (hxy : 2 • y ^ 2 ≤ x)
  (h₃ : Nat.factorization ((y ^ 2) ^ x) ≤ Nat.factorization (x ^ x)) :
  -- (h₄ : 2 • x • Nat.factorization y = x • 2 • Nat.factorization y) :
  (y ^ 2) ^ x ∣ x ^ x := by
  have g₁: (y ^ 2) ^ x ≠ 0 := by
    refine pow_ne_zero x ?_
    refine pow_ne_zero 2 ?_
    linarith
  have g₂: x ^ x ≠ 0 := by
    refine pow_ne_zero x ?_
    linarith
  exact (Nat.factorization_le_iff_dvd g₁ g₂).mp h₃


lemma imo_1997_p5_8_15
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  (hyx : y < x)
  -- (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  -- (hxy : 2 • y ^ 2 ≤ x)
  (h₃ : Nat.factorization ((y ^ 2) ^ x) ≤ Nat.factorization (x ^ x))
  -- (h₄ : 2 • x • Nat.factorization y = x • 2 • Nat.factorization y)
  (g₁ : (y ^ 2) ^ x ≠ 0) :
  (y ^ 2) ^ x ∣ x ^ x := by
  have g₂: x ^ x ≠ 0 := by
    refine pow_ne_zero x ?_
    linarith
  exact (Nat.factorization_le_iff_dvd g₁ g₂).mp h₃


lemma imo_1997_p5_8_16
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hyx : y < x)
  -- (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  -- (hxy : 2 • y ^ 2 ≤ x)
  (h₃ : Nat.factorization ((y ^ 2) ^ x) ≤ Nat.factorization (x ^ x))
  -- (h₄ : 2 • x • Nat.factorization y = x • 2 • Nat.factorization y)
  (g₁ : y = 0 → x = 0) :
  (y ^ 2) ^ x ∣ x ^ x := by
  refine (Nat.factorization_le_iff_dvd ?_ ?_).mp h₃
  . simp_all only [Nat.factorization_pow, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, not_false_eq_true,]
    omega
  . simp_all only [ne_eq, pow_eq_zero_iff', and_not_self, not_false_eq_true]



lemma imo_1997_p5_8_17
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hyx : y < x)
  -- (h₂ : x • Nat.factorization y = y ^ 2 • Nat.factorization x)
  -- (hxy1 : 2 * y ^ 2 ≤ x)
  -- (hxy : 2 • y ^ 2 ≤ x)
  -- (h₃ : Nat.factorization ((y ^ 2) ^ x) ≤ Nat.factorization (x ^ x))
  -- (h₄ : 2 • x • Nat.factorization y = x • 2 • Nat.factorization y)
  (h₅ : (y ^ 2) ^ x ∣ x ^ x) :
  y ^ 2 ∣ x := by
  refine (Nat.pow_dvd_pow_iff ?_).mp h₅
  exact Nat.ne_of_gt h₀.1



lemma imo_1997_p5_9
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (h₂ : Real.log (↑x:ℝ)  = Real.log ↑y * ↑x / (↑(y ^ 2:ℕ ):ℝ) )
  (hxy : y < x) :
  x = y ^ (x / y ^ 2) := by
  have h_exp : Real.exp (Real.log ↑x)
            = Real.exp (Real.log ↑y * (↑x:ℝ)  / ((↑y:ℝ)) ^ 2) := by
    rw [h₂]
    norm_cast
  rw [← imo_1997_p5_4 x h₀.1] at h_exp
  rw [← mul_div] at h_exp
  rw [Real.exp_mul] at h_exp
  rw [← imo_1997_p5_4 y h₀.2] at h_exp
  have h₃: (↑x:ℝ) / ((↑y:ℝ)^2) = (↑(x / y^2:ℕ):ℝ) := by
    norm_cast
    symm
    have g₂: y^2 ∣ x := by
      exact imo_1997_p5_8 x y h₀ h₁ hxy
    have h₃: (↑(y^(2:ℕ)):ℝ) ≠ 0 := by
      norm_cast
      exact pow_ne_zero 2 ( by linarith)
    exact Nat.cast_div g₂ h₃
  have h₄ : (↑(y ^ (x / y ^ (2:ℕ))):ℝ) = (↑y:ℝ)^((↑x:ℝ) / ((↑y:ℝ)^2)) := by
    rw [Nat.cast_pow, h₃]
    norm_cast
  rw [←h₄] at h_exp
  exact Nat.cast_inj.mp h_exp


lemma imo_1997_p5_9_1
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  -- (h₂ : Real.log ↑x = Real.log ↑y * ↑x / ↑(y ^ 2:ℕ))
  (hxy : y < x)
  (h_exp : rexp (Real.log ↑x) = rexp (Real.log ↑y * ↑x / ↑y ^ 2)) :
  x = y ^ (x / y ^ 2) := by
  rw [← imo_1997_p5_4 x h₀.1] at h_exp
  rw [← mul_div] at h_exp
  rw [Real.exp_mul] at h_exp
  rw [← imo_1997_p5_4 y h₀.2] at h_exp
  have h₃: (↑x:ℝ) / ((↑y:ℝ)^2) = (↑(x / y^2:ℕ):ℝ) := by
    norm_cast
    symm
    have g₂: y^2 ∣ x := by
      exact imo_1997_p5_8 x y h₀ h₁ hxy
    have h₃: (↑(y^(2:ℕ)):ℝ) ≠ 0 := by
      norm_cast
      exact pow_ne_zero 2 ( by linarith)
    exact Nat.cast_div g₂ h₃
  have h₄ : (↑(y ^ (x / y ^ (2:ℕ))):ℝ) = (↑y:ℝ)^((↑x:ℝ) / ((↑y:ℝ)^2)) := by
    rw [Nat.cast_pow, h₃]
    norm_cast
  rw [←h₄] at h_exp
  exact Nat.cast_inj.mp h_exp


lemma imo_1997_p5_9_2
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  -- (h₂ : Real.log ↑x = Real.log ↑y * ↑x / ↑(y ^ 2:ℕ))
  (hxy : y < x)
  (h_exp : ↑x = rexp (Real.log ↑y * (↑x / ↑y ^ 2))) :
  x = y ^ (x / y ^ 2) := by
  rw [Real.exp_mul] at h_exp
  rw [← imo_1997_p5_4 y h₀.2] at h_exp
  have h₃: (↑x:ℝ) / ((↑y:ℝ)^2) = (↑(x / y^2:ℕ):ℝ) := by
    norm_cast
    symm
    have g₂: y^2 ∣ x := by
      exact imo_1997_p5_8 x y h₀ h₁ hxy
    have h₃: (↑(y^(2:ℕ)):ℝ) ≠ 0 := by
      norm_cast
      exact pow_ne_zero 2 ( by linarith)
    exact Nat.cast_div g₂ h₃
  have h₄ : (↑(y ^ (x / y ^ (2:ℕ))):ℝ) = (↑y:ℝ)^((↑x:ℝ) / ((↑y:ℝ)^2)) := by
    rw [Nat.cast_pow, h₃]
    norm_cast
  rw [←h₄] at h_exp
  exact Nat.cast_inj.mp h_exp


lemma imo_1997_p5_9_3
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  -- (h₂ : Real.log ↑x = Real.log ↑y * ↑x / ↑(y ^ 2:ℕ))
  (hxy : y < x)
  (h_exp : ↑x = rexp (Real.log ↑y) ^ (↑x  / (↑y:ℝ) ^ 2)) :
  x = y ^ (x / y ^ 2) := by
  rw [← imo_1997_p5_4 y h₀.2] at h_exp
  have h₃: (↑x:ℝ) / ((↑y:ℝ)^2) = (↑(x / y^2:ℕ):ℝ) := by
    norm_cast
    symm
    have g₂: y^2 ∣ x := by
      exact imo_1997_p5_8 x y h₀ h₁ hxy
    have h₃: (↑(y^(2:ℕ)):ℝ) ≠ 0 := by
      norm_cast
      exact pow_ne_zero 2 ( by linarith)
    exact Nat.cast_div g₂ h₃
  have h₄ : (↑(y ^ (x / y ^ (2:ℕ))):ℝ) = (↑y:ℝ)^((↑x:ℝ) / ((↑y:ℝ)^2)) := by
    rw [Nat.cast_pow, h₃]
    norm_cast
  rw [←h₄] at h_exp
  exact Nat.cast_inj.mp h_exp


lemma imo_1997_p5_9_4
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  -- (h₂ : Real.log ↑x = Real.log ↑y * ↑x / ↑(y ^ 2:ℕ))
  (hxy : y < x)
  (h_exp : (↑x:ℝ) = (↑y:ℝ) ^ ((↑x:ℝ) / (↑y:ℝ) ^ 2)) :
  -- ↑x = rexp (Real.log ↑y) ^ (↑x  / (↑y:ℝ) ^ 2)
  x = y ^ (x / y ^ 2) := by
  have h₃: (↑x:ℝ) / ((↑y:ℝ)^2) = (↑(x / y^2:ℕ)) := by
    norm_cast
    symm
    have g₂: y^2 ∣ x := by
      exact imo_1997_p5_8 x y h₀ h₁ hxy
    have h₃: (↑(y^(2:ℕ)):ℝ) ≠ 0 := by
      norm_cast
      exact pow_ne_zero 2 ( by linarith)
    exact Nat.cast_div g₂ h₃
  have h₄ : (↑(y ^ (x / y ^ (2:ℕ))):ℝ) = (↑y:ℝ)^((↑x:ℝ) / ((↑y:ℝ)^2)) := by
    rw [Nat.cast_pow, h₃]
    norm_cast
  rw [←h₄] at h_exp
  exact Nat.cast_inj.mp h_exp


lemma imo_1997_p5_9_5
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  -- (h₂ : Real.log ↑x = Real.log ↑y * ↑x / ↑(y ^ 2:ℕ))
  (hxy : y < x) :
  -- (h_exp : ↑x = ↑y ^ (↑x / ↑y ^ 2:ℕ)) :
  (↑x:ℝ) / ((↑y:ℝ)^2) = (↑(x / y^2:ℕ):ℝ) := by
  norm_cast
  symm
  have g₂: y^2 ∣ x := by
    exact imo_1997_p5_8 x y h₀ h₁ hxy
  have h₃: (↑(y^(2:ℕ)):ℝ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero 2 ( by linarith)
  exact Nat.cast_div g₂ h₃


lemma imo_1997_p5_9_6
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (h₂ : Real.log ↑x = Real.log ↑y * ↑x / ↑(y ^ 2:ℕ))
  -- (hxy : y < x)
  -- (h_exp : ↑x = ↑y ^ (↑x / ↑y ^ 2))
  (g₂ : y ^ 2 ∣ x) :
  (↑(x / y^2:ℕ):ℝ) = (↑x:ℝ) / (↑(y^2:ℕ)) := by
  have h₃: (↑(y^(2:ℕ)):ℝ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero 2 ( by linarith)
  exact Nat.cast_div g₂ h₃


lemma imo_1997_p5_9_7
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  (h₂ : Real.log (↑x:ℝ)  = Real.log ↑y * ↑x / (↑(y ^ 2:ℕ ):ℝ) ) :
  (↑x:ℝ) = (↑y:ℝ) ^ ((↑x:ℝ) / (↑y:ℝ) ^ 2) := by
  have h_exp : Real.exp (Real.log ↑x)
            = Real.exp (Real.log ↑y * (↑x:ℝ)  / ((↑y:ℝ)) ^ 2) := by
    rw [h₂]
    norm_cast
  rw [← imo_1997_p5_4 x h₀.1] at h_exp
  rw [← mul_div] at h_exp
  rw [Real.exp_mul] at h_exp
  rw [← imo_1997_p5_4 y h₀.2] at h_exp
  exact h_exp


lemma imo_1997_p5_9_8
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  (h₂ : Real.log (↑x:ℝ)  = Real.log ↑y * ↑x / (↑(y ^ 2:ℕ ):ℝ) ) :
  ↑x = rexp (Real.log ↑y * (↑x / ↑y ^ 2)) := by
  have h_exp : Real.exp (Real.log ↑x)
            = Real.exp (Real.log ↑y * (↑x:ℝ)  / ((↑y:ℝ)) ^ 2) := by
    rw [h₂]
    norm_cast
  rw [← imo_1997_p5_4 x h₀.1] at h_exp
  rw [← mul_div] at h_exp
  exact h_exp


lemma imo_1997_p5_9_9
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (h₂ : Real.log ↑x = Real.log ↑y * ↑x / ↑(y ^ 2:ℕ))
  -- (hxy : y < x)
  (h_exp : (↑x:ℝ) = (↑y:ℝ) ^ ((↑x:ℝ) / (↑y:ℝ) ^ 2))
  (h₃ : (↑x:ℝ) / ((↑y:ℝ)^2) = (↑(x / y^2:ℕ))) :
  x = y ^ (x / y ^ 2) := by
  have h₄ : (↑(y ^ (x / y ^ (2:ℕ))):ℝ) = (↑y:ℝ)^((↑x:ℝ) / ((↑y:ℝ)^2)) := by
    rw [Nat.cast_pow, h₃]
    norm_cast
  rw [←h₄] at h_exp
  exact Nat.cast_inj.mp h_exp


lemma imo_1997_p5_9_10
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (h₂ : Real.log ↑x = Real.log ↑y * ↑x / ↑(y ^ 2:ℕ))
  -- (hxy : y < x)
  -- (h_exp : ↑x = ↑y ^ (↑x / ↑y ^ 2))
  (h₃ : (↑x:ℝ) / ((↑y:ℝ)^2) = ↑(x / y^2:ℕ)) :
  (↑(y ^ (x / y ^ (2:ℕ))):ℝ) = (↑y:ℝ) ^ ((↑x:ℝ) / ((↑y:ℝ)^2)) := by
  rw [Nat.cast_pow, h₃]
  norm_cast


lemma imo_1997_p5_9_11
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (h₂ : Real.log ↑x = Real.log ↑y * ↑x / ↑(y ^ 2:ℕ))
  -- (hxy : y < x)
  (h_exp : ↑x = ↑(y ^ (x / y ^ 2)))
  (h₃ : ↑x / ↑y ^ 2 = ↑(x / y ^ 2))
  (h₄ : ↑(y ^ (x / y ^ 2)) = ↑y ^ (↑x / ↑y ^ 2)) :
  x = y ^ (x / y ^ 2) := by
  rw [←h₄] at h_exp
  exact Nat.cast_inj.mp h_exp




  lemma imo_1997_p5_10
    (x y : ℕ)
    (h₀ : 0 < x ∧ 0 < y)
    (h₁ : x ^ y ^ 2 = y ^ x)
    (hxy : y < x) :
    x = y ^ (x / y ^ 2) := by
    -- sketch: y^2 * log x = x * log y
    have h₃: Real.log (x^(y^2)) = Real.log (y^x) := by
      norm_cast
      rw [h₁]
    have h₄: (↑(y ^ (2:ℕ)):ℝ)  * Real.log x = ↑x * Real.log y := by
      have h41: Real.log (y^x) = (↑x:ℝ) * Real.log (y) := by
        exact Real.log_pow y x
      have h42: Real.log (x^(y^2)) = (↑(y ^ (2:ℕ)):ℝ) * Real.log x := by
        exact Real.log_pow x (y^2)
      rw [h41,h42] at h₃
      exact h₃
    -- ring_nf at h₄
    have h₅: Real.log ↑x = Real.log ↑y * ↑x / (↑(y ^ (2:ℕ)):ℝ) := by
      by_contra! hc
      rw [mul_comm (Real.log ↑y) (↑x)] at hc
      rw [← h₄, mul_comm, ← mul_div] at hc
      rw [div_self, mul_one] at hc
      . apply hc
        norm_cast
      . norm_cast
        push_neg
        refine pow_ne_zero 2 ?_
        exact Nat.ne_of_gt h₀.2
    have h₆: x = y ^ (x / y ^ 2) := by
      exact imo_1997_p5_9 x y h₀ h₁ h₅ hxy
    exact h₆

lemma imo_1997_p5_10_1
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x)
  (h₃ : Real.log (↑x ^ y ^ 2) = Real.log (↑y ^ x)) :
  x = y ^ (x / y ^ 2) := by
  have h₄: (↑(y ^ (2:ℕ)):ℝ)  * Real.log x = ↑x * Real.log y := by
    have h41: Real.log (y^x) = (↑x:ℝ) * Real.log (y) := by
      exact Real.log_pow y x
    have h42: Real.log (x^(y^2)) = (↑(y ^ (2:ℕ)):ℝ) * Real.log x := by
      exact Real.log_pow x (y^2)
    rw [h41,h42] at h₃
    exact h₃
  -- ring_nf at h₄
  have h₅: Real.log ↑x = Real.log ↑y * ↑x / (↑(y ^ (2:ℕ)):ℝ) := by
    by_contra! hc
    rw [mul_comm (Real.log ↑y) (↑x)] at hc
    rw [← h₄, mul_comm, ← mul_div] at hc
    rw [div_self, mul_one] at hc
    . apply hc
      norm_cast
    . norm_cast
      push_neg
      refine pow_ne_zero 2 ?_
      exact Nat.ne_of_gt h₀.2
  have h₆: x = y ^ (x / y ^ 2) := by
    exact imo_1997_p5_9 x y h₀ h₁ h₅ hxy
  exact h₆


lemma imo_1997_p5_10_2
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  (h₃ : Real.log (↑x ^ y ^ 2) = Real.log (↑y ^ x)) :
  ↑(y ^ 2:ℕ) * Real.log ↑x = ↑x * Real.log ↑y := by
  have h41: Real.log (y^x) = (↑x:ℝ) * Real.log (y) := by
    exact Real.log_pow y x
  have h42: Real.log (x^(y^2)) = (↑(y ^ (2:ℕ)):ℝ) * Real.log x := by
    exact Real.log_pow x (y^2)
  rw [h41,h42] at h₃
  exact h₃


lemma imo_1997_p5_10_3
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  (h₃ : Real.log (↑x ^ y ^ 2) = Real.log (↑y ^ x))
  (h₄₁ : Real.log (↑y ^ x) = ↑x * Real.log ↑y) :
  ↑(y ^ 2:ℕ) * Real.log ↑x = ↑x * Real.log ↑y := by
  have h₄₂: Real.log (x^(y^2)) = (↑(y ^ (2:ℕ)):ℝ) * Real.log x := by
    exact Real.log_pow x (y^2)
  rw [h₄₁,h₄₂] at h₃
  exact h₃


lemma imo_1997_p5_10_4
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  (h₃ : Real.log (↑x ^ y ^ 2) = Real.log (↑y ^ x))
  (h₄₁ : Real.log (↑y ^ x) = ↑x * Real.log ↑y)
  (h₄₂ : Real.log (↑x ^ y ^ 2) = ↑(y ^ 2:ℕ) * Real.log ↑x) :
  ↑(y ^ 2:ℕ) * Real.log ↑x = ↑x * Real.log ↑y := by
  rw [h₄₁,h₄₂] at h₃
  exact h₃

lemma imo_1997_p5_10_5
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x)
  -- (h₃ : Real.log (↑x ^ y ^ 2) = Real.log (↑y ^ x))
  (h₄ : ↑(y ^ 2:ℕ) * Real.log ↑x = ↑x * Real.log ↑y) :
  x = y ^ (x / y ^ 2) := by
  have h₅: Real.log ↑x = Real.log ↑y * ↑x / (↑(y ^ (2:ℕ)):ℝ) := by
    by_contra! hc
    rw [mul_comm (Real.log ↑y) (↑x)] at hc
    rw [← h₄, mul_comm, ← mul_div] at hc
    rw [div_self, mul_one] at hc
    . apply hc
      norm_cast
    . norm_cast
      push_neg
      refine pow_ne_zero 2 ?_
      exact Nat.ne_of_gt h₀.2
  have h₆: x = y ^ (x / y ^ 2) := by
    exact imo_1997_p5_9 x y h₀ h₁ h₅ hxy
  exact h₆


lemma imo_1997_p5_10_6
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (h₃ : Real.log (↑x ^ y ^ 2) = Real.log (↑y ^ x))
  (h₄ : ↑(y ^ 2:ℕ) * Real.log ↑x = ↑x * Real.log ↑y) :
  Real.log ↑x = Real.log ↑y * ↑x / ↑(y ^ 2:ℕ) := by
  by_contra! hc
  rw [mul_comm (Real.log ↑y) (↑x)] at hc
  rw [← h₄, mul_comm, ← mul_div] at hc
  rw [div_self, mul_one] at hc
  . apply hc
    norm_cast
  . norm_cast
    push_neg
    refine pow_ne_zero 2 ?_
    exact Nat.ne_of_gt h₀.2


lemma imo_1997_p5_10_7
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (h₃ : Real.log (↑x ^ y ^ 2) = Real.log (↑y ^ x))
  (h₄ : ↑(y ^ 2:ℕ) * Real.log ↑x = ↑x * Real.log ↑y)
  (hc : ¬Real.log ↑x = Real.log ↑y * ↑x / ↑(y ^ 2:ℕ)) :
  False := by
  rw [mul_comm (Real.log ↑y) (↑x)] at hc
  rw [← h₄, mul_comm, ← mul_div] at hc
  rw [div_self, mul_one] at hc
  . apply hc
    norm_cast
  . norm_cast
    push_neg
    refine pow_ne_zero 2 ?_
    exact Nat.ne_of_gt h₀.2


lemma imo_1997_p5_10_8
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (h₃ : Real.log (↑x ^ y ^ 2) = Real.log (↑y ^ x))
  (h₄ : ↑(y ^ 2:ℕ) * Real.log ↑x = ↑x * Real.log ↑y)
  (hc : ¬Real.log ↑x = ↑x * Real.log ↑y / ↑(y ^ 2:ℕ)) :
  False := by
  rw [← h₄, mul_comm, ← mul_div] at hc
  rw [div_self, mul_one] at hc
  . apply hc
    norm_cast
  . norm_cast
    push_neg
    refine pow_ne_zero 2 ?_
    exact Nat.ne_of_gt h₀.2


lemma imo_1997_p5_10_9
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (h₃ : Real.log (↑x ^ y ^ 2) = Real.log (↑y ^ x))
  -- (h₄ : ↑(y ^ 2:ℕ) * Real.log ↑x = ↑x * Real.log ↑y)
  (hc : ¬Real.log ↑x = Real.log ↑x * (↑(y ^ 2:ℕ) / ↑(y ^ 2:ℕ))) :
  False := by
  rw [div_self, mul_one] at hc
  . apply hc
    norm_cast
  . norm_cast
    push_neg
    refine pow_ne_zero 2 ?_
    exact Nat.ne_of_gt h₀.2


lemma imo_1997_p5_10_10
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (hxy : y < x)
  -- (h₃ : Real.log (↑x ^ y ^ 2) = Real.log (↑y ^ x))
  -- (h₄ : ↑(y ^ 2:ℕ) * Real.log ↑x = ↑x * Real.log ↑y)
  (hc : ¬Real.log ↑x = Real.log ↑x * (↑(y ^ 2:ℕ) / ↑(y ^ 2:ℕ))) :
  ↑((y ^ 2):ℝ) ≠ 0 := by
  norm_cast
  push_neg
  refine pow_ne_zero 2 ?_
  exact Nat.ne_of_gt h₀.2


lemma imo_1997_p5_10_11
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (hxy : y < x)
  -- (h₃ : Real.log (↑x ^ y ^ 2) = Real.log (↑y ^ x))
  -- (h₄ : ↑(y ^ 2:ℕ) * Real.log ↑x = ↑x * Real.log ↑y)
  (h₅ : Real.log ↑x = Real.log ↑y * ↑x / ↑(y ^ 2:ℕ)) :
  x = y ^ (x / y ^ 2) := by
  have h₆: x = y ^ (x / y ^ 2) := by
    exact imo_1997_p5_9 x y h₀ h₁ h₅ hxy
  exact h₆




lemma imo_1997_p5_11_1
  (x y : ℕ) :
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x) :
  x ^ y ^ 2 = (x ^ y) ^ y := by
  rw [Nat.pow_two]
  exact Nat.pow_mul x y y


lemma imo_1997_p5_11_2
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  (hxy : y < x) :
  (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by
  have h₃: x = y ^ (x / y ^ 2) := by
    exact imo_1997_p5_10 x y h₀ h₁ hxy
  let k:ℕ  := x / y^2
  have hk_def: k = x / y^2 := by exact rfl
  by_cases hk: k < 2
  . rw [← hk_def] at h₃
    interval_cases k
    . exfalso
      simp at h₃
      linarith
    . exfalso
      simp at *
      linarith [hxy,h₃] --simp at h₃, rw h₃ at hxy, linarith[hxy], },
  . push_neg at hk
    rw [← hk_def] at h₃
    have h₅: k = y^(k-2) := by
      rw [h₃] at hk_def
      nth_rewrite 1 [hk_def]
      exact Nat.pow_div hk h₀.2
    by_cases hk5: k < 5
    . interval_cases k
      . exfalso
        simp at h₅
      . right
        norm_num
        simp at h₅
        symm at h₅
        rw [h₅] at h₃
        norm_num at h₃
        exact { left := h₃, right := h₅ }
      . simp at h₅
        symm at h₅
        have g₂: y^4 = y^2 * y^2 := by ring_nf
        rw [g₂, h₅] at h₃
        norm_num at h₃
        left
        norm_num
        constructor
        . exact h₃
        . have h₆ : y ^ 2 = 2 ^ 2 := by
            norm_num
            exact h₅
          have h₇: 0 ≤ y := by
            linarith
          exact (sq_eq_sq₀ h₇ (by linarith)).mp (h₆)
    push_neg at hk5
    by_cases hy: 2 ≤ y
    . have h₅₁: k < y^(k-2) := by
        have h₆: 2^(k-2) ≤ y^(k-2) := by
          have hk1: 3 ≤ k - 2 := by exact Nat.sub_le_sub_right hk5 2
          exact (Nat.pow_le_pow_iff_left (by linarith)).mpr hy
        have h₇: 4*k < 2^k := by
          exact imo_1997_p5_2 k hk5
        have h₇: k < 2^(k-2) := by
          have h₈ : k < 2 ^ k / 4 := by
            have h81: 4 ∣ 2^k := by
              have h82: 2^k = 4*2^(k-2) := by
                have h83: k = 2 + (k -2) := by
                  ring_nf
                  exact (add_sub_of_le hk).symm
                nth_rewrite 1 [h83]
                rw [pow_add]
                norm_num
              rw [h82]
              exact Nat.dvd_mul_right 4 (2^(k-2))
            exact (Nat.lt_div_iff_mul_lt' h81 k).mpr h₇
          have h₉: 2 ^ k / 4 = 2 ^ (k-2) := by
            have g2: k = k - 2 + 2 := by
              exact (Nat.sub_eq_iff_eq_add hk).mp rfl
            have h1: 2^k = 2^(k - 2 + 2) := by
              exact congrArg (HPow.hPow 2) g2
            have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
            rw [h1, h2]
            ring_nf
            simp
          linarith
        linarith
      exfalso
      linarith
    . push_neg at hy
      interval_cases y
      . linarith
      . simp at h₅
        simp at h₃
        linarith


lemma imo_1997_p5_11_3
  (x y k : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  (hxy : y < x)
  (h₃ : x = y ^ (x / y ^ 2))
  (hk_def : k = x / y ^ 2) :
  (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by
  by_cases hk: k < 2
  . rw [← hk_def] at h₃
    interval_cases k
    . exfalso
      simp at h₃
      linarith
    . exfalso
      simp at *
      linarith [hxy,h₃]
  . push_neg at hk
    rw [← hk_def] at h₃
    have h₅: k = y^(k-2) := by
      rw [h₃] at hk_def
      nth_rewrite 1 [hk_def]
      exact Nat.pow_div hk h₀.2
    by_cases hk5: k < 5
    . interval_cases k
      . exfalso
        simp at h₅
      . right
        norm_num
        simp at h₅
        symm at h₅
        rw [h₅] at h₃
        norm_num at h₃
        exact { left := h₃, right := h₅ }
      . simp at h₅
        symm at h₅
        have g₂: y^4 = y^2 * y^2 := by ring_nf
        rw [g₂, h₅] at h₃
        norm_num at h₃
        left
        norm_num
        constructor
        . exact h₃
        . have h₆ : y ^ 2 = 2 ^ 2 := by
            norm_num
            exact h₅
          have h₇: 0 ≤ y := by
            linarith
          exact (sq_eq_sq₀ h₇ (by linarith)).mp (h₆)
    push_neg at hk5
    by_cases hy: 2 ≤ y
    . have h₅₁: k < y^(k-2) := by
        have h₆: 2^(k-2) ≤ y^(k-2) := by
          have hk1: 3 ≤ k - 2 := by exact Nat.sub_le_sub_right hk5 2
          refine (Nat.pow_le_pow_iff_left ?_).mpr hy
          have h₆₀: 2 < k - 2 := by exact hk1
          exact Nat.not_eq_zero_of_lt h₆₀
        have h₇: 4*k < 2^k := by
          exact imo_1997_p5_2 k hk5
        have h₇: k < 2^(k-2) := by
          have h₈ : k < 2 ^ k / 4 := by
            have h81: 4 ∣ 2^k := by
              have h82: 2^k = 4*2^(k-2) := by
                have h83: k = 2 + (k -2) := by
                  ring_nf
                  exact (add_sub_of_le hk).symm
                nth_rewrite 1 [h83]
                rw [pow_add]
                norm_num
              rw [h82]
              exact Nat.dvd_mul_right 4 (2^(k-2))
            exact (Nat.lt_div_iff_mul_lt' h81 k).mpr h₇
          have h₉: 2 ^ k / 4 = 2 ^ (k-2) := by
            have g2: k = k - 2 + 2 := by
              exact (Nat.sub_eq_iff_eq_add hk).mp rfl
            have h1: 2^k = 2^(k - 2 + 2) := by
              exact congrArg (HPow.hPow 2) g2
            have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
            rw [h1, h2]
            ring_nf
            simp
          linarith
        linarith
      exfalso
      linarith
    . push_neg at hy
      interval_cases y
      . linarith
      . simp at h₅
        simp at h₃
        linarith


lemma imo_1997_p5_11_4
  (x y k : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  (hxy : y < x)
  (h₃ : x = y ^ (x / y ^ 2))
  (hk_def : k = x / y ^ 2)
  (hk : k < 2) :
  (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by
  rw [← hk_def] at h₃
  interval_cases k
  . exfalso
    simp at h₃
    linarith
  . exfalso
    simp at *
    linarith [hxy,h₃]


lemma imo_1997_p5_11_5
  (x y k : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  (hxy : y < x)
  (h₃ : x = y ^ (x / y ^ 2))
  (hk_def : k = x / y ^ 2)
  (hk : k < 2) :
  False := by
  rw [← hk_def] at h₃
  interval_cases k
  . simp at h₃
    linarith
  . simp at *
    linarith [hxy,h₃]


lemma imo_1997_p5_11_6
  (x y k : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  (hxy : y < x)
  (h₃ : x = y ^ (x / y ^ 2))
  (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k) :
  (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by
  rw [← hk_def] at h₃
  have h₅: k = y^(k-2) := by
    rw [h₃] at hk_def
    nth_rewrite 1 [hk_def]
    exact Nat.pow_div hk h₀.2
  by_cases hk5: k < 5
  . interval_cases k
    . exfalso
      simp at h₅
    . right
      norm_num
      simp at h₅
      symm at h₅
      rw [h₅] at h₃
      norm_num at h₃
      exact { left := h₃, right := h₅ }
    . simp at h₅
      symm at h₅
      have g₂: y^4 = y^2 * y^2 := by ring_nf
      rw [g₂, h₅] at h₃
      norm_num at h₃
      left
      norm_num
      constructor
      . exact h₃
      . have h₆ : y ^ 2 = 2 ^ 2 := by
          norm_num
          exact h₅
        have h₇: 0 ≤ y := by
          linarith
        exact (sq_eq_sq₀ h₇ (by linarith)).mp (h₆)
  push_neg at hk5
  by_cases hy: 2 ≤ y
  . have h₅₁: k < y^(k-2) := by
      have h₆: 2^(k-2) ≤ y^(k-2) := by
        have hk1: 3 ≤ k - 2 := by exact Nat.sub_le_sub_right hk5 2
        exact (Nat.pow_le_pow_iff_left (by linarith)).mpr hy
      have h₇: 4*k < 2^k := by
        exact imo_1997_p5_2 k hk5
      have h₇: k < 2^(k-2) := by
        have h₈ : k < 2 ^ k / 4 := by
          have h81: 4 ∣ 2^k := by
            have h82: 2^k = 4*2^(k-2) := by
              have h83: k = 2 + (k -2) := by
                ring_nf
                exact (add_sub_of_le hk).symm
              nth_rewrite 1 [h83]
              rw [pow_add]
              norm_num
            rw [h82]
            exact Nat.dvd_mul_right 4 (2^(k-2))
          exact (Nat.lt_div_iff_mul_lt' h81 k).mpr h₇
        have h₉: 2 ^ k / 4 = 2 ^ (k-2) := by
          have g2: k = k - 2 + 2 := by
            exact (Nat.sub_eq_iff_eq_add hk).mp rfl
          have h1: 2^k = 2^(k - 2 + 2) := by
            exact congrArg (HPow.hPow 2) g2
          have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
          rw [h1, h2]
          ring_nf
          simp
        linarith
      linarith
    exfalso
    linarith
  . push_neg at hy
    interval_cases y
    . linarith
    . simp at h₅
      simp at h₃
      linarith


lemma imo_1997_p5_11_7
  (x y k : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  (h₃ : x = y ^ k)
  (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k) :
  k = y ^ (k - 2) := by
  rw [h₃] at hk_def
  nth_rewrite 1 [hk_def]
  exact Nat.pow_div hk h₀.2


lemma imo_1997_p5_11_8
  (x y k : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  (h₃ : x = y ^ k)
  (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k)
  (h₅ : k = y ^ (k - 2))
  (hk5 : k < 5) :
  (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by
  interval_cases k
  . exfalso
    simp at h₅
  . right
    norm_num
    simp at h₅
    symm at h₅
    rw [h₅] at h₃
    norm_num at h₃
    exact { left := h₃, right := h₅ }
  . simp at h₅
    symm at h₅
    have g₂: y^4 = y^2 * y^2 := by ring_nf
    rw [g₂, h₅] at h₃
    norm_num at h₃
    left
    norm_num
    constructor
    . exact h₃
    . have h₆ : y ^ 2 = 2 ^ 2 := by
        norm_num
        exact h₅
      have h₇: 0 ≤ y := by
        linarith
      exact (sq_eq_sq₀ h₇ (by linarith)).mp (h₆)


lemma imo_1997_p5_11_9
  (x y : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  (h₃ : x = y ^ 3)
  (hk_def : 3 = x / y ^ 2)
  (hk : 2 ≤ 3)
  (h₅ : 3 = y ^ (3 - 2))
  (hk5 : 3 < 5) :
  (x, y) = (27, 3) := by
  norm_num
  simp at h₅
  symm at h₅
  rw [h₅] at h₃
  norm_num at h₃
  exact { left := h₃, right := h₅ }


lemma imo_1997_p5_11_10
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  (h₃ : x = y ^ 4)
  (hk_def : 4 = x / y ^ 2)
  (hk : 2 ≤ 4)
  (h₅ : 4 = y ^ (4 - 2))
  (hk5 : 4 < 5) :
  (x, y) = (16, 2) := by
  simp at h₅
  symm at h₅
  have g₂: y^4 = y^2 * y^2 := by ring_nf
  rw [g₂, h₅] at h₃
  norm_num at h₃
  norm_num
  constructor
  . exact h₃
  . have h₆ : y ^ 2 = 2 ^ 2 := by
      norm_num
      exact h₅
    have h₇: 0 ≤ y := by
      linarith
    exact (sq_eq_sq₀ h₇ (by linarith)).mp (h₆)


lemma imo_1997_p5_11_11
  (y: ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (hk_def : 4 = x / y ^ 2)
  -- (hk : 2 ≤ 4)
  -- (hk5 : 4 < 5)
  (h₅ : y ^ 2 = 4)
  (g₂ : y ^ 4 = y ^ 2 * y ^ 2) :
  -- (h₃ : x = 16) :
  y = 2 := by
  rw [pow_two] at h₅
  refine ((fun {m n} => Nat.mul_self_inj.mp) (?_)).symm
  exact h₅.symm


lemma imo_1997_p5_11_12
  (x y k : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  (hxy : y < x)
  (h₃ : x = y ^ k)
  (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k)
  (h₅ : k = y ^ (k - 2))
  (hk5 : 5 ≤ k) :
  (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by
  by_cases hy: 2 ≤ y
  . have h₅₁: k < y^(k-2) := by
      have h₆: 2^(k-2) ≤ y^(k-2) := by
        have hk1: 3 ≤ k - 2 := by exact Nat.sub_le_sub_right hk5 2
        exact (Nat.pow_le_pow_iff_left (by linarith)).mpr hy
      have h₇: 4*k < 2^k := by
        exact imo_1997_p5_2 k hk5
      have h₇: k < 2^(k-2) := by
        have h₈ : k < 2 ^ k / 4 := by
          have h81: 4 ∣ 2^k := by
            have h82: 2^k = 4*2^(k-2) := by
              have h83: k = 2 + (k -2) := by
                ring_nf
                exact (add_sub_of_le hk).symm
              nth_rewrite 1 [h83]
              rw [pow_add]
              norm_num
            rw [h82]
            exact Nat.dvd_mul_right 4 (2^(k-2))
          exact (Nat.lt_div_iff_mul_lt' h81 k).mpr h₇
        have h₉: 2 ^ k / 4 = 2 ^ (k-2) := by
          have g2: k = k - 2 + 2 := by
            exact (Nat.sub_eq_iff_eq_add hk).mp rfl
          have h1: 2^k = 2^(k - 2 + 2) := by
            exact congrArg (HPow.hPow 2) g2
          have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
          rw [h1, h2]
          ring_nf
          simp
        linarith
      linarith
    exfalso
    linarith
  . push_neg at hy
    interval_cases y
    . linarith
    . simp at h₅
      simp at h₃
      linarith


lemma imo_1997_p5_11_13
  (x y k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k)
  (h₅ : k = y ^ (k - 2))
  (hk5 : 5 ≤ k)
  (hy : 2 ≤ y) :
  (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by
  have h₅₁: k < y^(k-2) := by
    have h₆: 2^(k-2) ≤ y^(k-2) := by
      have hk1: 3 ≤ k - 2 := by exact Nat.sub_le_sub_right hk5 2
      exact (Nat.pow_le_pow_iff_left (by linarith)).mpr hy
    have h₇: 4*k < 2^k := by
      exact imo_1997_p5_2 k hk5
    have h₇: k < 2^(k-2) := by
      have h₈ : k < 2 ^ k / 4 := by
        have h81: 4 ∣ 2^k := by
          have h82: 2^k = 4*2^(k-2) := by
            have h83: k = 2 + (k -2) := by
              ring_nf
              exact (add_sub_of_le hk).symm
            nth_rewrite 1 [h83]
            rw [pow_add]
            norm_num
          rw [h82]
          exact Nat.dvd_mul_right 4 (2^(k-2))
        exact (Nat.lt_div_iff_mul_lt' h81 k).mpr h₇
      have h₉: 2 ^ k / 4 = 2 ^ (k-2) := by
        have g2: k = k - 2 + 2 := by
          exact (Nat.sub_eq_iff_eq_add hk).mp rfl
        have h1: 2^k = 2^(k - 2 + 2) := by
          exact congrArg (HPow.hPow 2) g2
        have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
        rw [h1, h2]
        ring_nf
        simp
      linarith
    linarith
  exfalso
  linarith


lemma imo_1997_p5_11_14
  (x y k : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x ^ y ^ 2 = y ^ x)
  (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  (hxy : y < x)
  (h₃ : x = y ^ k)
  (hk_def : k = x / y ^ 2)
  -- (hk : 2 ≤ k)
  (h₅ : k = y ^ (k - 2))
  (hk5 : 5 ≤ k)
  (hy : y < 2) :
  (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by
  interval_cases y
  . linarith
  . simp at h₅
    simp at h₃
    linarith


lemma imo_1997_p5_11_15
  (x y k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k)
  (h₅ : k = y ^ (k - 2))
  (hk5 : 5 ≤ k)
  (hy : 2 ≤ y) :
  (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by
  have h₅₁: k < y^(k-2) := by
    have h₆: 2^(k-2) ≤ y^(k-2) := by
      have hk1: 3 ≤ k - 2 := by exact Nat.sub_le_sub_right hk5 2
      exact (Nat.pow_le_pow_iff_left (by linarith)).mpr hy
    have h₇: 4*k < 2^k := by
      exact imo_1997_p5_2 k hk5
    have h₈: k < 2^(k-2) := by
      have h₈ : k < 2 ^ k / 4 := by
        have h81: 4 ∣ 2^k := by
          have h82: 2^k = 4*2^(k-2) := by
            have h83: k = 2 + (k -2) := by
              ring_nf
              exact (add_sub_of_le hk).symm
            nth_rewrite 1 [h83]
            rw [pow_add]
            norm_num
          rw [h82]
          exact Nat.dvd_mul_right 4 (2^(k-2))
        exact (Nat.lt_div_iff_mul_lt' h81 k).mpr h₇
      have h₉: 2 ^ k / 4 = 2 ^ (k-2) := by
        have g2: k = k - 2 + 2 := by
          exact (Nat.sub_eq_iff_eq_add hk).mp rfl
        have h1: 2^k = 2^(k - 2 + 2) := by
          exact congrArg (HPow.hPow 2) g2
        have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
        rw [h1, h2]
        ring_nf
        simp
      linarith
    linarith
  exfalso
  linarith


lemma imo_1997_p5_11_16
  (y k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k)
  (h₅ : k = y ^ (k - 2))
  (hk5 : 5 ≤ k)
  (hy : 2 ≤ y) :
  False := by
  have h₅₁: k < y^(k-2) := by
    have h₆: 2^(k-2) ≤ y^(k-2) := by
      have hk1: 3 ≤ k - 2 := by exact Nat.sub_le_sub_right hk5 2
      exact (Nat.pow_le_pow_iff_left (by linarith)).mpr hy
    have h₇: 4*k < 2^k := by
      exact imo_1997_p5_2 k hk5
    have h₈: k < 2^(k-2) := by
      have h₈ : k < 2 ^ k / 4 := by
        have h81: 4 ∣ 2^k := by
          have h82: 2^k = 4*2^(k-2) := by
            have h83: k = 2 + (k -2) := by
              ring_nf
              exact (add_sub_of_le hk).symm
            nth_rewrite 1 [h83]
            rw [pow_add]
            norm_num
          rw [h82]
          exact Nat.dvd_mul_right 4 (2^(k-2))
        exact (Nat.lt_div_iff_mul_lt' h81 k).mpr h₇
      have h₉: 2 ^ k / 4 = 2 ^ (k-2) := by
        have g2: k = k - 2 + 2 := by
          exact (Nat.sub_eq_iff_eq_add hk).mp rfl
        have h1: 2^k = 2^(k - 2 + 2) := by
          exact congrArg (HPow.hPow 2) g2
        have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
        rw [h1, h2]
        ring_nf
        simp
      linarith
    linarith
  nth_rw 1 [← h₅] at h₅₁
  apply Nat.ne_of_lt at h₅₁
  refine false_of_ne h₅₁


lemma imo_1997_p5_11_17
  (y k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k)
  (h₅ : k = y ^ (k - 2))
  (hk5 : 5 ≤ k)
  (hy : 2 ≤ y) :
  k < y ^ (k - 2) := by
  have h₆: 2^(k-2) ≤ y^(k-2) := by
    have hk1: 3 ≤ k - 2 := by exact Nat.sub_le_sub_right hk5 2
    exact (Nat.pow_le_pow_iff_left (by linarith)).mpr hy
  have h₇: 4*k < 2^k := by
    exact imo_1997_p5_2 k hk5
  have h₈: k < 2^(k-2) := by
    have h₈ : k < 2 ^ k / 4 := by
      have h81: 4 ∣ 2^k := by
        have h82: 2^k = 4*2^(k-2) := by
          have h83: k = 2 + (k -2) := by
            ring_nf
            exact (add_sub_of_le hk).symm
          nth_rewrite 1 [h83]
          rw [pow_add]
          norm_num
        rw [h82]
        exact Nat.dvd_mul_right 4 (2^(k-2))
      exact (Nat.lt_div_iff_mul_lt' h81 k).mpr h₇
    have h₉: 2 ^ k / 4 = 2 ^ (k-2) := by
      have g2: k = k - 2 + 2 := by
        exact (Nat.sub_eq_iff_eq_add hk).mp rfl
      have h1: 2^k = 2^(k - 2 + 2) := by
        exact congrArg (HPow.hPow 2) g2
      have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
      rw [h1, h2]
      ring_nf
      simp
    linarith
  linarith


lemma imo_1997_p5_11_18
  (y k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  -- (hk : 2 ≤ k)
  -- (h₅ : k = y ^ (k - 2))
  (hk5 : 5 ≤ k)
  (hy : 2 ≤ y) :
  2 ^ (k - 2) ≤ y ^ (k - 2) := by
  have hk1: 3 ≤ k - 2 := by exact Nat.sub_le_sub_right hk5 2
  exact (Nat.pow_le_pow_iff_left (by linarith)).mpr hy


lemma imo_1997_p5_11_19
  (y k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k)
  (h₅ : k = y ^ (k - 2))
  -- (hk5 : 5 ≤ k)
  -- (hy : 2 ≤ y)
  (h₆ : 2 ^ (k - 2) ≤ y ^ (k - 2))
  (h₇ : 4 * k < 2 ^ k) :
  k < y ^ (k - 2) := by
  have h₈: k < 2^(k-2) := by
    have h₈ : k < 2 ^ k / 4 := by
      have h81: 4 ∣ 2^k := by
        have h82: 2^k = 4*2^(k-2) := by
          have h83: k = 2 + (k -2) := by
            ring_nf
            exact (add_sub_of_le hk).symm
          nth_rewrite 1 [h83]
          rw [pow_add]
          norm_num
        rw [h82]
        exact Nat.dvd_mul_right 4 (2^(k-2))
      exact (Nat.lt_div_iff_mul_lt' h81 k).mpr h₇
    have h₉: 2 ^ k / 4 = 2 ^ (k-2) := by
      have g2: k = k - 2 + 2 := by
        exact (Nat.sub_eq_iff_eq_add hk).mp rfl
      have h1: 2^k = 2^(k - 2 + 2) := by
        exact congrArg (HPow.hPow 2) g2
      have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
      rw [h1, h2]
      ring_nf
      simp
    linarith
  linarith


lemma imo_1997_p5_11_20
  (y k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k)
  (h₅ : k = y ^ (k - 2))
  -- (hk5 : 5 ≤ k)
  -- (hy : 2 ≤ y)
  (h₆ : 2 ^ (k - 2) ≤ y ^ (k - 2))
  (h₇ : 4 * k < 2 ^ k) :
  k < 2 ^ (k - 2) := by
  have h₈ : k < 2 ^ k / 4 := by
    have h81: 4 ∣ 2^k := by
      have h82: 2^k = 4*2^(k-2) := by
        have h83: k = 2 + (k -2) := by
          ring_nf
          exact (add_sub_of_le hk).symm
        nth_rewrite 1 [h83]
        rw [pow_add]
        norm_num
      rw [h82]
      exact Nat.dvd_mul_right 4 (2^(k-2))
    exact (Nat.lt_div_iff_mul_lt' h81 k).mpr h₇
  have h₉: 2 ^ k / 4 = 2 ^ (k-2) := by
    have g2: k = k - 2 + 2 := by
      exact (Nat.sub_eq_iff_eq_add hk).mp rfl
    have h1: 2^k = 2^(k - 2 + 2) := by
      exact congrArg (HPow.hPow 2) g2
    have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
    rw [h1, h2]
    ring_nf
    simp
  linarith


lemma imo_1997_p5_11_21
  (k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k)
  -- (h₅ : k = y ^ (k - 2))
  -- (hk5 : 5 ≤ k)
  -- (hy : 2 ≤ y)
  -- (h₆ : 2 ^ (k - 2) ≤ y ^ (k - 2))
  (h₇ : 4 * k < 2 ^ k) :
  k < 2 ^ k / 4 := by
  have h81: 4 ∣ 2^k := by
    have h82: 2^k = 4*2^(k-2) := by
      have h83: k = 2 + (k -2) := by
        ring_nf
        exact (add_sub_of_le hk).symm
      nth_rewrite 1 [h83]
      rw [pow_add]
      norm_num
    rw [h82]
    exact Nat.dvd_mul_right 4 (2^(k-2))
  exact (Nat.lt_div_iff_mul_lt' h81 k).mpr h₇


lemma imo_1997_p5_11_22
  -- (x y : ℕ)
  (k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k) :
  -- (h₅ : k = y ^ (k - 2))
  -- (hk5 : 5 ≤ k)
  -- (hy : 2 ≤ y)
  -- (h₆ : 2 ^ (k - 2) ≤ y ^ (k - 2))
  -- (h₇ : 4 * k < 2 ^ k) :
  4 ∣ 2 ^ k := by
  have h82: 2^k = 4*2^(k-2) := by
    have h83: k = 2 + (k -2) := by
      ring_nf
      exact (add_sub_of_le hk).symm
    nth_rewrite 1 [h83]
    rw [pow_add]
    norm_num
  rw [h82]
  exact Nat.dvd_mul_right 4 (2^(k-2))



lemma imo_1997_p5_11_23
  -- (x y : ℕ)
  (k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k) :
  -- (h₅ : k = y ^ (k - 2))
  -- (hk5 : 5 ≤ k)
  -- (hy : 2 ≤ y)
  -- (h₆ : 2 ^ (k - 2) ≤ y ^ (k - 2))
  -- (h₇ : 4 * k < 2 ^ k) :
  2 ^ k = 4 * 2 ^ (k - 2) := by
  have h83: k = 2 + (k -2) := by
    ring_nf
    exact (add_sub_of_le hk).symm
  nth_rewrite 1 [h83]
  rw [pow_add]
  norm_num


lemma imo_1997_p5_11_24
  -- (x y : ℕ)
  (k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  -- (hk : 2 ≤ k)
  -- (h₅ : k = y ^ (k - 2))
  -- (hk5 : 5 ≤ k)
  -- (hy : 2 ≤ y)
  -- (h₆ : 2 ^ (k - 2) ≤ y ^ (k - 2))
  -- (h₇ : 4 * k < 2 ^ k)
  (h₈₃ : k = 2 + (k - 2)) :
  2 ^ k = 4 * 2 ^ (k - 2) := by
  nth_rewrite 1 [h₈₃]
  rw [pow_add]
  norm_num


lemma imo_1997_p5_11_25
  -- (x y : ℕ)
  (k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  -- (hk : 2 ≤ k)
  -- (h₅ : k = y ^ (k - 2))
  -- (hk5 : 5 ≤ k)
  -- (hy : 2 ≤ y)
  -- (h₆ : 2 ^ (k - 2) ≤ y ^ (k - 2))
  -- (h₇ : 4 * k < 2 ^ k)
  (h82 : 2 ^ k = 4 * 2 ^ (k - 2)) :
  4 ∣ 2 ^ k := by
  rw [h82]
  exact Nat.dvd_mul_right 4 (2^(k-2))


lemma imo_1997_p5_11_26
  -- (x : ℕ)
  (y k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k)
  (h₅ : k = y ^ (k - 2))
  -- (hk5 : 5 ≤ k)
  -- (hy : 2 ≤ y)
  (h₆ : 2 ^ (k - 2) ≤ y ^ (k - 2))
  -- (h₇ : 4 * k < 2 ^ k)
  (h₈ : k < 2 ^ k / 4) :
  k < 2 ^ (k - 2) := by
  have h₉: 2 ^ k / 4 = 2 ^ (k-2) := by
    have g2: k = k - 2 + 2 := by
      exact (Nat.sub_eq_iff_eq_add hk).mp rfl
    have h1: 2^k = 2^(k - 2 + 2) := by
      exact congrArg (HPow.hPow 2) g2
    have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
    rw [h1, h2]
    ring_nf
    simp
  linarith


lemma imo_1997_p5_11_27
  -- (x y : ℕ)
  (k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  (hk : 2 ≤ k) :
  -- (h₅ : k = y ^ (k - 2))
  -- (hk5 : 5 ≤ k)
  -- (hy : 2 ≤ y)
  -- (h₆ : 2 ^ (k - 2) ≤ y ^ (k - 2))
  -- (h₇ : 4 * k < 2 ^ k)
  -- (h₈ : k < 2 ^ k / 4) :
  2 ^ k / 4 = 2 ^ (k - 2) := by
  have g2: k = k - 2 + 2 := by
    exact (Nat.sub_eq_iff_eq_add hk).mp rfl
  have h1: 2^k = 2^(k - 2 + 2) := by
    exact congrArg (HPow.hPow 2) g2
  have h2: 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
  rw [h1, h2]
  ring_nf
  simp

lemma imo_1997_p5_11_28
  -- (x y : ℕ)
  (k : ℕ)
  -- (h₀ : 0 < x ∧ 0 < y)
  -- (h₁ : x ^ y ^ 2 = y ^ x)
  -- (g₁ : x ^ y ^ 2 = (x ^ y) ^ y)
  -- (hxy : y < x)
  -- (h₃ : x = y ^ k)
  -- (hk_def : k = x / y ^ 2)
  -- (hk : 2 ≤ k)
  -- (h₅ : k = y ^ (k - 2))
  -- (hk5 : 5 ≤ k)
  -- (hy : 2 ≤ y)
  -- (h₆ : 2 ^ (k - 2) ≤ y ^ (k - 2))
  -- (h₇ : 4 * k < 2 ^ k)
  -- (h₈ : k < 2 ^ k / 4)
  -- (g2 : k = k - 2 + 2)
  (h1 : 2 ^ k = 2 ^ (k - 2 + 2))
  (h2 : 2 ^ (k - 2 + 2) = 2 ^ (k - 2) * 2 ^ 2) :
  2 ^ k / 4 = 2 ^ (k - 2) := by
  rw [h1, h2]
  ring_nf
  simp
