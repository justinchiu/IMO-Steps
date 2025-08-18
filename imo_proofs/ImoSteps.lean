import Mathlib

open Nat BigOperators Finset Real

namespace ImoSteps

-- Prime divisor helpers
-- Used in: imo_1992_p1.lean
lemma prime_divisor_cases {p : ℕ} {x y : ℤ} (hp : Nat.Prime p) (h : x * y = ↑p) :
    x = -1 ∨ x = 1 ∨ x = -↑p ∨ x = ↑p := by
  have ha := Int.natAbs_eq x
  have : x.natAbs * y.natAbs = p := by
    rw [← Int.natAbs_mul, h]
    simp
  have hab := Nat.Prime.eq_one_or_self_of_dvd hp x.natAbs ⟨y.natAbs, this.symm⟩
  cases hab with
  | inl h1 => 
    rw [h1] at ha
    cases ha <;> simp [*]
  | inr hp' =>
    rw [hp'] at ha
    cases ha <;> simp [*]

-- Factorial helpers  
-- Used in: (none)
lemma factorial_bound_helper (n k : ℕ) (h : k ≤ n) :
    (k.factorial : ℚ) * (n - k).factorial ≤ n.factorial := by
  norm_cast
  have := Nat.factorial_mul_factorial_dvd_factorial h
  exact Nat.le_of_dvd (Nat.factorial_pos _) this

-- Recurrence relation helpers
-- Used in: (none - imo_1985_p6 has similar pattern but uses NNReal instead of ℝ)
lemma recurrence_positive (f : ℕ → ℝ → ℝ)
    (h₀ : ∀ x, f 1 x = x)
    (h₁ : ∀ n x, 0 < n → f (n + 1) x = f n x * (f n x + 1 / n))
    (n : ℕ) (x : ℝ) (hn : 0 < n) (hx : 0 < x) : 
    0 < f n x := by
  induction n, hn using Nat.le_induction with
  | base => rw [h₀]; exact hx
  | succ n hn ih =>
    rw [h₁ n x hn]
    apply mul_pos ih
    apply add_pos ih
    exact div_pos one_pos (Nat.cast_pos.mpr hn)

-- AM-GM inequality for 2 terms
-- Used in: imo_1984_p6.lean, imo_2007_p6.lean
lemma two_mul_le_add_sq (a b : ℝ) : 2 * a * b ≤ a^2 + b^2 := by
  have : 0 ≤ (a - b)^2 := sq_nonneg _
  linarith [this]

-- AM-GM inequality for 4 terms
-- Used in: imo_2023_p4.lean
lemma amgm_four (b1 b2 b3 b4 : ℝ)
    (hb1: 0 ≤ b1) (hb2: 0 ≤ b2) (hb3: 0 ≤ b3) (hb4: 0 ≤ b4) :
    4 * (b1 * b2 * b3 * b4) ^ (4:ℝ)⁻¹ ≤ b1 + b2 + b3 + b4 := by
  let w1 : ℝ := (4:ℝ)⁻¹
  let w2 : ℝ := w1
  let w3 : ℝ := w2
  let w4 : ℝ := w3
  rw [mul_comm]
  refine mul_le_of_le_div₀ ?_ (by norm_num) ?_
  · refine add_nonneg ?_ hb4
    refine add_nonneg ?_ hb3
    exact add_nonneg hb1 hb2
  have h₀: (b1^w1 * b2^w2 * b3^w3 * b4^w4) ≤ w1 * b1 + w2 * b2 + w3 * b3 + w4 * b4 := by
    refine geom_mean_le_arith_mean4_weighted (by norm_num) ?_ ?_ ?_ hb1 hb2 hb3 hb4 ?_
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  repeat rw [mul_rpow _]
  ring_nf at *
  linarith
  repeat { assumption }
  · exact mul_nonneg hb1 hb2
  · exact hb4
  · refine mul_nonneg ?_ hb3
    exact mul_nonneg hb1 hb2


-- Rearrangement inequality for 3 terms (standard form)
-- Used in: (none)
lemma rearrangement_three (a b c x y z : ℝ) (ha : a ≤ b) (hb : b ≤ c) 
    (hx : x ≤ y) (hy : y ≤ z) :
    a * z + b * y + c * x ≤ a * x + b * y + c * z := by
  have h1 : (c - a) * (z - x) ≥ 0 := mul_nonneg (by linarith) (by linarith)
  linarith

-- Rearrangement for products (variant 1)
-- Used in: imo_1983_p6.lean
lemma rearrangement_prod_1 (a b c x y z : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₂: c ≤ b ∧ b ≤ a)
    (h₃: z ≤ y ∧ y ≤ x) :
    a * z + c * y + b * x ≤ c * z + b * y + a * x := by
  suffices h₄: c * (y - z) + b * (x - y) ≤ a * (x - z) by linarith
  have h₅: c * (y - z) + b * (x - y) ≤ b * (y - z) + b * (x - y) := by
    simp
    refine mul_le_mul h₂.1 ?_ ?_ ?_
    · exact le_rfl
    · exact sub_nonneg_of_le h₃.1
    · exact le_of_lt h₀.2.1
  refine le_trans h₅ ?_
  rw [mul_sub, mul_sub, add_comm]
  rw [← add_sub_assoc, sub_add_cancel]
  rw [← mul_sub]
  refine mul_le_mul h₂.2 ?_ ?_ ?_
  · exact le_rfl
  · refine sub_nonneg_of_le ?_
    exact le_trans h₃.1 h₃.2
  · exact le_of_lt h₀.1

-- Rearrangement for products (variant 2)
-- Used in: imo_1983_p6.lean
lemma rearrangement_prod_2 (a b c x y z : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₂: c ≤ b ∧ b ≤ a)
    (h₃: z ≤ y ∧ y ≤ x) :
    b * z + a * y + c * x ≤ c * z + b * y + a * x := by
  suffices h₄: c * (x - z) + b * (z - y) ≤ a * (x - y) by linarith
  have h₅: c * (x - z) + b * (z - y) ≤ b * (x - z) + b * (z - y) := by
    simp
    refine mul_le_mul h₂.1 ?_ ?_ ?_
    · exact le_rfl
    · refine sub_nonneg_of_le ?_
      exact le_trans h₃.1 h₃.2
    · exact le_of_lt h₀.2.1
  refine le_trans h₅ ?_
  rw [mul_sub, mul_sub]
  rw [← add_sub_assoc, sub_add_cancel]
  rw [← mul_sub]
  refine mul_le_mul h₂.2 ?_ ?_ ?_
  · exact le_rfl
  · exact sub_nonneg_of_le h₃.2
  · exact le_of_lt h₀.1

-- Exponential growth bound
-- Used in: imo_1997_p5.lean
lemma exp_bound_small (k : ℕ) (hk : 5 ≤ k) : 4 * k < 2 ^ k := by
  induction' k, hk using Nat.le_induction with n hn ih
  · norm_num
  · calc 4 * (n + 1) = 4 * n + 4 := by ring
      _ < 2 ^ n + 4 := by linarith [ih]
      _ < 2 ^ n + 2 ^ n := by 
        have : 2 ^ n ≥ 2 ^ 5 := Nat.pow_le_pow_of_le_right (by omega) hn
        have : 2 ^ 5 = 32 := by norm_num
        omega
      _ = 2 ^ (n + 1) := by ring

-- Sum vs product inequality
-- Used in: imo_2022_p5.lean
lemma sum_lt_product (a b : ℕ) (ha : 2 ≤ a) (hab : a < b) : a + b < a * b := by
  calc a + b < b + b := add_lt_add_right hab b
    _ = 2 * b := by ring
    _ ≤ a * b := mul_le_mul_right' ha b

-- Divisibility in factorials
-- Used in: (none)
lemma prime_dvd_factorial (p n : ℕ) (hp : Nat.Prime p) (hn : p ≤ n) : p ∣ n.factorial := by
  exact dvd_factorial hp.pos hn

-- Factorial bounds
-- Used in: imo_2022_p5.lean
lemma factorial_le_pow (n : ℕ) : n.factorial ≤ n ^ n := by
  induction' n with k ih
  · simp
  · rw [factorial_succ, pow_succ]
    by_cases hk : 0 < k
    · calc (k + 1) * k.factorial ≤ (k + 1) * k ^ k := Nat.mul_le_mul_left _ ih
        _ ≤ (k + 1) * (k + 1) ^ k := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_left (Nat.le_succ _) _
        _ = (k + 1) ^ (k + 1) := by ring
    · simp at hk; subst hk; simp


-- Triangle inequality helper
-- Used in: imo_1964_p2.lean
lemma triangle_aux (x y z : ℝ) : (x + y - z) * (x + z - y) ≤ x^2 := by
  nlinarith [sq_nonneg (y - z)]

-- Ackermann-like recurrence pattern
-- Used in: imo_1981_p6.lean
lemma ackermann_pattern (f : ℕ → ℕ → ℕ)
    (h₀ : ∀ y, f 0 y = y + 1)
    (h₁ : ∀ x, f (x + 1) 0 = f x 1)
    (h₂ : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) :
    (∀ y, f 1 y = y + 2) ∧ (∀ y, f 2 y = 2*y + 3) := by
  have f1 : ∀ y, f 1 y = y + 2 := by
    intro y; induction y with
    | zero => simp [h₁, h₀]
    | succ n ih => rw [h₂, h₀, ih]
  constructor
  · exact f1
  · intro y; induction y with
    | zero => simp [h₁, f1]
    | succ n ih => rw [h₂, f1, ih]; ring

-- Sequence monotonicity
-- Used in: (none)
lemma seq_monotone_strict {α : Type*} [LinearOrder α] (a : ℕ → α)
    (h : ∀ n, a n < a (n + 1)) : StrictMono a := by
  intro m n hmn
  induction' n, hmn using Nat.le_induction with k hk ih
  · exact (h m)
  · exact ih.trans (h k)

-- Power of 2 divisibility
-- Used in: (none)
lemma pow2_dvd_iff (n k : ℕ) : 2^k ∣ n ↔ n % 2^k = 0 := by
  constructor
  · intro h; exact Nat.mod_eq_zero_of_dvd h
  · intro h; exact Nat.dvd_of_mod_eq_zero h

-- Interval arithmetic
-- Used in: (none)
lemma interval_bound (x : ℝ) (a b : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    |x| ≤ max |a| |b| := by
  cases' le_or_lt 0 x with hx hx
  · rw [abs_of_nonneg hx]
    apply le_max_of_le_right
    rw [abs_of_nonneg (le_trans hx hb)]
    exact hb
  · rw [abs_of_neg hx]
    apply le_max_of_le_left
    rw [abs_of_nonpos (le_trans ha hx.le)]
    linarith

-- Modular arithmetic patterns
-- Used in: (none)
lemma modEq_sum_const (n : ℕ) (c m : ℕ) : 
    ∑ _ ∈ Finset.range n, c ≡ n * c [MOD m] := by
  simp [Finset.sum_const, Finset.card_range]
  rfl

-- Used in: (none)
lemma modEq_pow_of_modEq (a b n m : ℕ) (h : a ≡ b [MOD m]) :
    a^n ≡ b^n [MOD m] := ModEq.pow n h

-- Subadditivity pattern for functional equations
-- Used in: imo_1982_p1.lean
lemma subadditive_of_delta {f : ℕ → ℤ} 
    (h : ∀ m n, 0 < m → 0 < n → f (m + n) - f m - f n ∈ ({0, 1} : Set ℤ)) :
    ∀ m n, 0 < m → 0 < n → f m + f n ≤ f (m + n) := by
  intros m n hm hn
  have := h m n hm hn
  simp at this
  cases this with
  | inl h1 => linarith
  | inr h2 => linarith

-- Multiplicative bound from subadditivity
-- Used in: imo_1982_p1.lean
lemma mult_bound_of_subadditive {f : ℕ → ℤ}
    (h_sub : ∀ m n, 0 < m → 0 < n → f m + f n ≤ f (m + n)) :
    ∀ m k, 0 < m → 0 < k → k * f m ≤ f (k * m) := by
  intros m k hm hk
  induction' k with k ih
  · contradiction
  · cases' k with k'
    · simp
    · calc (k'.succ + 1) * f m = k'.succ * f m + f m := by ring
        _ ≤ f (k'.succ * m) + f m := by linarith [ih (by omega)]
        _ ≤ f (k'.succ * m + m) := h_sub _ _ (by positivity) hm
        _ = f ((k'.succ + 1) * m) := by ring_nf

-- Trigonometric identities
-- Used in: imo_1963_p5.lean
lemma sin_mul_cos (x y : ℝ) :
    Real.sin x * Real.cos y = (sin (x + y) + sin (x - y)) / 2 := by
  rw [sin_add, sin_sub]
  simp

-- Square root algebraic identity
-- Used in: imo_1962_p2.lean
lemma sqrt_diff_sq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a + b - 2 * sqrt a * sqrt b = (sqrt a - sqrt b)^2 := by
  rw [sub_sq, sq_sqrt ha, sq_sqrt hb]
  ring

-- Trigonometric sum patterns
-- Used in: (none - imo_1969_p2 uses weighted version)
lemma cos_sum_angle_add (k : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    ∑ i ∈ Finset.range k, Real.cos (a i + x) = 
    (∑ i ∈ Finset.range k, Real.cos (a i)) * Real.cos x - 
    (∑ i ∈ Finset.range k, Real.sin (a i)) * Real.sin x := by
  simp only [Real.cos_add]
  rw [Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul]

-- Product telescoping pattern
-- Used in: (none)
lemma prod_telescope (f : ℕ → ℚ) (n : ℕ) (h : ∀ i < n, f i ≠ 0) (h0 : f 0 ≠ 0) :
    ∏ i ∈ Finset.range n, (f (i + 1) / f i) = f n / f 0 := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [Finset.prod_range_succ]
    by_cases hn : n = 0
    · simp [hn]
    · have : ∀ i < n, f i ≠ 0 := fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))
      rw [ih this]
      field_simp [h n (Nat.lt_succ_self n), h0]
      ring

-- Inequality chain for triangle sides
-- Used in: (none)
lemma triangle_ineq_chain (a b c : ℝ) (h_tri : c < a + b ∧ b < a + c ∧ a < b + c) :
    (a + b - c) * (a + c - b) * (b + c - a) > 0 := by
  have h1 : 0 < a + b - c := by linarith [h_tri.1]
  have h2 : 0 < a + c - b := by linarith [h_tri.2.1]
  have h3 : 0 < b + c - a := by linarith [h_tri.2.2]
  positivity

-- Contradiction from negative square
-- Used in: (none - imo_2022_p2 uses different approach)
lemma neg_sq_false {x y : ℝ} (hxy : x ≠ y) : ¬((x - y)^2 < 0) := by
  have : 0 < (x - y)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
  linarith


-- Additional helper for factorial products
-- Used in: (none)
lemma factorial_product_bound (n k : ℕ) (h : k ≤ n) :
    k.factorial * (n - k).factorial ≤ n.factorial := by
  have : k.factorial * (n - k).factorial ∣ n.factorial := 
    Nat.factorial_mul_factorial_dvd_factorial h
  exact Nat.le_of_dvd (Nat.factorial_pos n) this

-- Quadratic non-residues modulo 5
-- Used in: imo_1974_p3.lean
lemma not_square_mod_5_eq_2 (a : ℕ) : ¬ a^2 ≡ 2 [MOD 5] := by
  intro h
  let b := a % 5
  have hb : a ≡ b [MOD 5] := Nat.mod_modEq a 5 |>.symm
  have : a^2 ≡ b^2 [MOD 5] := ModEq.pow 2 hb
  have hb2 : b^2 ≡ 2 [MOD 5] := ModEq.trans this.symm h
  have : b < 5 := Nat.mod_lt a (by norm_num : 0 < 5)
  interval_cases b <;> (simp only [pow_two, ModEq] at hb2; norm_num at hb2)

lemma not_square_mod_5_eq_3 (a : ℕ) : ¬ a^2 ≡ 3 [MOD 5] := by
  intro h
  let b := a % 5
  have hb : a ≡ b [MOD 5] := Nat.mod_modEq a 5 |>.symm
  have : a^2 ≡ b^2 [MOD 5] := ModEq.pow 2 hb
  have hb2 : b^2 ≡ 3 [MOD 5] := ModEq.trans this.symm h
  have : b < 5 := Nat.mod_lt a (by norm_num : 0 < 5)
  interval_cases b <;> (simp only [pow_two, ModEq] at hb2; norm_num at hb2)

-- Sign patterns for products
-- Used in: (none - imo_1965_p2 uses Mathlib lemmas directly)
lemma sign_patterns {α : Type*} [LinearOrderedRing α] :
    (∀ a b : α, a < 0 → b < 0 → 0 < a * b) ∧ 
    (∀ a b : α, a < 0 → 0 < b → a * b < 0) ∧
    (∀ a b : α, 0 < a → b < 0 → a * b < 0) ∧
    (∀ a b : α, 0 < a → 0 < b → 0 < a * b) := by
  constructor
  · intros a b ha hb
    exact mul_pos_of_neg_of_neg ha hb
  constructor
  · intros a b ha hb
    exact mul_neg_of_neg_of_pos ha hb
  constructor
  · intros a b ha hb
    exact mul_neg_of_pos_of_neg ha hb
  · intros a b ha hb
    exact mul_pos ha hb

end ImoSteps