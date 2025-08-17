import Mathlib

open Nat BigOperators Finset

namespace ImoSteps

-- Prime divisor helpers
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
lemma factorial_bound_helper (n k : ℕ) (h : k ≤ n) :
    (k.factorial : ℚ) * (n - k).factorial ≤ n.factorial := by
  norm_cast
  have := Nat.factorial_mul_factorial_dvd_factorial h
  exact Nat.le_of_dvd (Nat.factorial_pos _) this

-- Recurrence relation helpers (for IMO 1985 P6)
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
lemma two_mul_le_add_sq (a b : ℝ) : 2 * a * b ≤ a^2 + b^2 := by
  have : 0 ≤ (a - b)^2 := sq_nonneg _
  linarith [this]

-- Rearrangement inequality for 3 terms
lemma rearrangement_three (a b c x y z : ℝ) (ha : a ≤ b) (hb : b ≤ c) 
    (hx : x ≤ y) (hy : y ≤ z) :
    a * z + b * y + c * x ≤ a * x + b * y + c * z := by
  have h1 : (c - a) * (z - x) ≥ 0 := mul_nonneg (by linarith) (by linarith)
  linarith

-- Exponential growth bound
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
lemma sum_lt_product (a b : ℕ) (ha : 2 ≤ a) (hab : a < b) : a + b < a * b := by
  calc a + b < b + b := add_lt_add_right hab b
    _ = 2 * b := by ring
    _ ≤ a * b := mul_le_mul_right' ha b

-- Divisibility in factorials
lemma prime_dvd_factorial (p n : ℕ) (hp : Nat.Prime p) (hn : p ≤ n) : p ∣ n.factorial := by
  exact dvd_factorial hp.pos hn

-- Factorial bounds
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
lemma triangle_aux (x y z : ℝ) : (x + y - z) * (x + z - y) ≤ x^2 := by
  nlinarith [sq_nonneg (y - z)]

-- Ackermann-like recurrence pattern
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
lemma seq_monotone_strict {α : Type*} [LinearOrder α] (a : ℕ → α)
    (h : ∀ n, a n < a (n + 1)) : StrictMono a := by
  intro m n hmn
  induction' n, hmn using Nat.le_induction with k hk ih
  · exact (h m)
  · exact ih.trans (h k)

-- Power of 2 divisibility
lemma pow2_dvd_iff (n k : ℕ) : 2^k ∣ n ↔ n % 2^k = 0 := by
  constructor
  · intro h; exact Nat.mod_eq_zero_of_dvd h
  · intro h; exact Nat.dvd_of_mod_eq_zero h

-- Interval arithmetic
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
lemma modEq_sum_const (n : ℕ) (c m : ℕ) : 
    ∑ k in Finset.range n, c ≡ n * c [MOD m] := by
  simp [Finset.sum_const, Finset.card_range]

lemma modEq_pow_of_modEq (a b n m : ℕ) (h : a ≡ b [MOD m]) :
    a^n ≡ b^n [MOD m] := ModEq.pow n h

-- Subadditivity pattern for functional equations
lemma subadditive_of_delta {f : ℕ → ℤ} 
    (h : ∀ m n, 0 < m → 0 < n → f (m + n) - f m - f n ∈ ({0, 1} : Set ℤ)) :
    ∀ m n, 0 < m → 0 < n → f m + f n ≤ f (m + n) := by
  intros m n hm hn
  have := h m n hm hn
  omega

-- Multiplicative bound from subadditivity
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

-- Trigonometric sum patterns
lemma cos_sum_angle_add (k : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    ∑ i in Finset.range k, cos (a i + x) = 
    (∑ i in Finset.range k, cos (a i)) * cos x - 
    (∑ i in Finset.range k, sin (a i)) * sin x := by
  simp only [cos_add]
  rw [Finset.sum_sub_distrib]
  congr 1 <;> [conv_rhs => rw [← Finset.sum_mul]; conv_rhs => rw [← Finset.sum_mul]]

-- Product telescoping pattern
lemma prod_telescope {α : Type*} [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∏ i in Finset.range n, (f (i + 1) / f i) = f n / f 0 := by
  sorry -- This requires careful handling of division

-- Inequality chain for triangle sides
lemma triangle_ineq_chain (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_tri : c < a + b ∧ b < a + c ∧ a < b + c) :
    (a + b - c) * (a + c - b) * (b + c - a) > 0 := by
  have h1 : 0 < a + b - c := by linarith [h_tri.1]
  have h2 : 0 < a + c - b := by linarith [h_tri.2.1]
  have h3 : 0 < b + c - a := by linarith [h_tri.2.2]
  positivity

-- Convergence pattern for recurrence relations
lemma recurrence_bounded {f : ℕ → ℝ → ℝ}
    (h_rec : ∀ n x, f (n + 1) x = f n x * (f n x + 1 / n))
    (h_small : ∀ n x, x < 1/n → f n x < x + x^2) :
    ∀ n x, x < 1/n → f (n + 1) x < f n x := by
  intros n x hx
  rw [h_rec]
  have bound := h_small n x hx
  have pos : 0 < f n x := by linarith [bound, hx]
  have : f n x + 1 / n < 1 := by linarith [bound, hx]
  calc f n x * (f n x + 1 / n) < f n x * 1 := mul_lt_mul_of_pos_left this pos
    _ = f n x := mul_one _

-- Counting argument for powers of 2
lemma power2_count {s : Finset ℕ} (h : ∀ x ∈ s, ∃ n, x = 2^n) :
    s.card ≤ (s.sup id).log 2 + 1 := by
  sorry -- This requires logarithm properties

-- Chinese remainder theorem application
lemma crt_unique_mod (a b p q : ℕ) (hp : Prime p) (hq : Prime q) (hpq : p ≠ q)
    (ha : a ≡ b [MOD p]) (hb : a ≡ b [MOD q]) :
    a ≡ b [MOD p * q] := by
  have cop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr (hp.ne_one ∘ hq.dvd_of_eq hpq.symm)
  exact ModEq.mul_mod_of_coprime cop ha hb

end ImoSteps