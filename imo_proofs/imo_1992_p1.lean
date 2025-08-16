import ImoSteps
set_option linter.unusedVariables.analyzeTactics true

open Int Rat

lemma mylemma_main_lt2 (p q r: ℤ) (hpl: 4 ≤ p) (hql: 5 ≤ q) (hrl: 6 ≤ r) :
  (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑2 := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)
    = (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) := by norm_cast; simp
  have hp: (↑p/↑(p-1):ℚ) ≤ ((4/3):ℚ) := by
    exact (div_le_iff₀ (by norm_cast; linarith [hpl])).mpr (by norm_cast; linarith)
  have hq: (↑q/↑(q-1)) ≤ ((5/4):ℚ) := by
    exact (div_le_iff₀ (by norm_cast; linarith[hql])).mpr (by norm_cast; linarith)
  have hr: (↑r/↑(r-1)) ≤ ((6/5):ℚ) := by
    exact (div_le_iff₀ (by norm_cast; linarith[hrl])).mpr (by norm_cast; linarith)
  rw [h₁]; norm_num
  calc (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1))
    ≤ (4/3:ℚ) * ((5/4):ℚ) * ((6/5):ℚ) := by
      apply mul_le_mul _ hr (by norm_cast; linarith) (by norm_num)
      apply mul_le_mul hp hq (by norm_cast; linarith) (by norm_num)
    _ = 2 := by norm_num

lemma mylemma_main_lt4 (p q r: ℤ) (hpl: 2 ≤ p) (hql: 3 ≤ q) (hrl: 4 ≤ r) :
  (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑4 := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)
      = (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) := by norm_cast; simp
  have hp: (↑p/↑(p-1):ℚ) ≤ ↑(2:ℚ) := by
    exact (div_le_iff₀ (by norm_cast; linarith[hpl])).mpr (by norm_cast; linarith)
  have hq: (↑q/↑(q-1)) ≤ ((3/2):ℚ) := by
    exact (div_le_iff₀ (by norm_cast; linarith[hql])).mpr (by norm_cast; linarith)
  have hr: (↑r/↑(r-1)) ≤ ((4/3):ℚ) := by
    exact (div_le_iff₀ (by norm_cast; linarith[hrl])).mpr (by norm_cast; linarith)
  rw [h₁]
  calc (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1))
    ≤ (2:ℚ) * ((3/2):ℚ) * ((4/3):ℚ) := by
      apply mul_le_mul _ hr (by norm_cast; linarith) (by norm_num)
      apply mul_le_mul hp hq (by norm_cast; linarith) (by norm_num)
    _ = 4 := by norm_num

-- Unified k bound lemma to reduce redundancy
lemma k_bound_general (p q r k: ℤ) (bound : ℚ) (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1)) (hbound: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ bound) :
  (k : ℚ) < bound := by
  have h₁: ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    have g₁: ↑(p * q * r - 1) = ↑k * (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by norm_cast; linarith
    symm; exact (div_eq_iff (by norm_cast; linarith[hden])).mpr g₁
  have h₂: ↑k < (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    rw [h₁]; exact div_lt_div_of_pos_right (by norm_cast; exact sub_one_lt _) (by norm_cast)
  exact lt_of_lt_of_le h₂ hbound

lemma mylemma_k_lt_2 (p q r k: ℤ) (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (hpl: 4 ≤ p) (hql: 5 ≤ q) (hrl: 6 ≤ r) (hden: 0 < (p - 1) * (q - 1) * (r - 1)) :
  (k < 2) := by
  have h := k_bound_general p q r k 2 hk hden (mylemma_main_lt2 p q r hpl hql hrl)
  norm_cast at h

lemma mylemma_k_lt_4 (p q r k: ℤ) (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (hpl: 2 ≤ p) (hql: 3 ≤ q) (hrl: 4 ≤ r) (hden: 0 < (p - 1) * (q - 1) * (r - 1)) :
  (k < 4) := by
  have h := k_bound_general p q r k 4 hk hden (mylemma_main_lt4 p q r hpl hql hrl)
  norm_cast at h

lemma mylemma_k_gt_1 (p q r k: ℤ) (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (hpl: 2 ≤ p) (hql: 3 ≤ q) (hrl: 4 ≤ r) (hden: 0 < (p - 1) * (q - 1) * (r - 1)) :
  (1 < k) := by
  have hk_pos : 0 < k := by
    have g₁: 24 ≤ p * q * r := mul_le_mul (mul_le_mul hpl hql (by norm_num) (by linarith[hpl])) hrl (by norm_num) (by linarith)
    have g₂: 0 < p * q * r - 1 := by linarith[g₁]
    have : k * ((p - 1) * (q - 1) * (r - 1)) = p * q * r - 1 := by linarith [hk]
    have : k > 0 := by
      by_contra h; push_neg at h
      have : k * ((p - 1) * (q - 1) * (r - 1)) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg h (le_of_lt hden)
      linarith [this, g₂]
    exact this
  by_contra hc; push_neg at hc
  interval_cases k
  · linarith [hk_pos]
  · simp at hk
    have : p * q + q * r + r * p = p + q + r := by linarith [hk]
    have h₁ : p < p * q := lt_mul_right (by linarith) (by linarith)
    have h₂ : q < q * r := lt_mul_right (by linarith) (by linarith)
    have h₃ : r < r * p := lt_mul_right (by linarith) (by linarith)
    linarith [this, h₁, h₂, h₃]

lemma mylemma_p_lt_4 (p q r k: ℤ) (h₀ : 1 < p ∧ p < q ∧ q < r) (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (hpl: 2 ≤ p) (hql: 3 ≤ q) (hrl: 4 ≤ r) (hden: 0 < (p - 1) * (q - 1) * (r - 1)) :
  (p < 4) := by
  by_contra hcp; push_neg at hcp
  have hcq: 5 ≤ q := by linarith [h₀.2.1, hcp]
  have hcr: 6 ≤ r := by linarith [h₀.2.2, hcq]
  have h₃: k < 2 := mylemma_k_lt_2 p q r k hk hcp hcq hcr hden
  have h₄: 1 < k := mylemma_k_gt_1 p q r k hk hpl hql hrl hden
  linarith

-- Prime divisor lemma: simplified version
lemma prime_divisor_cases (q r : ℤ) (p: ℕ) (h₀ : q * r = ↑p) (h₁: Nat.Prime p) :
  q = -1 ∨ q = 1 ∨ q = -p ∨ q = p := by
  have hdiv : Int.natAbs q ∣ p := by
    use Int.natAbs r; exact Int.natAbs_mul_natAbs_eq h₀
  cases' Nat.Prime.eq_one_or_self_of_dvd h₁ (Int.natAbs q) hdiv with h_one h_p
  · exact (Int.natAbs_eq_one_iff.mp h_one).symm
  · have : Int.natAbs q = p := h_p
    exact (Int.natAbs_eq_natAbs_iff.mp (by norm_cast)).symm

-- Specific prime factorization cases - simplified
lemma factor_prime (a b : ℤ) (p : ℕ) (hp : Nat.Prime p) (h : a * b = p) :
  a = -1 ∨ a = 1 ∨ a = -p ∨ a = p := prime_divisor_cases a b p h hp

lemma mylemma_case_k_2 (p q r: ℤ) (h₀: 1 < p ∧ p < q ∧ q < r) (hpl: 2 ≤ p) (hql: 3 ≤ q) (hrl: 4 ≤ r)
  (hpu: p < 4) (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * 2) :
  (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  interval_cases p
  · exfalso; norm_num at *; linarith [show 2*q + 2*r = 3 by linarith [hk], hql, hrl]
  · right; norm_num at *
    have h₁: (4-q)*(4-r) = 11 := by linarith [hk]
    cases' factor_prime (4-q) (4-r) 11 (by decide) h₁ with h_case h_cases
    · exact ⟨by linarith [h_case], by linarith [h_case, h₁]⟩
    · exfalso
      cases' h_cases with h_case h_cases
      · linarith [h_case, hql]
      · cases' h_cases with h_case h_case
        · linarith [h_case, h₀.2.2]
        · linarith [h_case, hql]

lemma mylemma_case_k_3 (p q r: ℤ) (h₀: 1 < p ∧ p < q ∧ q < r) (hpl: 2 ≤ p) (hql: 3 ≤ q) (hrl: 4 ≤ r)
  (hpu: p < 4) (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * 3) :
  (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  interval_cases p
  · norm_num at *
    have h₁: (q-3)*(r-3) = 5 := by linarith [hk]
    cases' factor_prime (q-3) (r-3) 5 (by decide) h₁ with h_case h_cases
    · exfalso; linarith [hql, h_case]
    · cases' h_cases with h_case h_cases
      · exact ⟨by linarith [h_case], by linarith [h_case, h₁]⟩ 
      · exfalso
        cases' h_cases with h_case h_case
        · linarith [hql, h_case]
        · linarith [h₀.2.2, show q = 8 ∧ r = 4 by constructor <;> linarith [h_case, h₁]]
  · exfalso; norm_num at *
    have h₁: (6 - 3*q) * (2 - r) = 5 := by linarith [hk]
    cases' factor_prime (6 - 3*q) (2 - r) 5 (by decide) h₁ with h_case h_cases <;> linarith [h_case, hql]

theorem imo_1992_p1 (p q r : ℤ) (h₀ : 1 < p ∧ p < q ∧ q < r)
  (h₁ : (p - 1) * (q - 1) * (r - 1)∣(p * q * r - 1)) :
  (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  obtain ⟨k, hk⟩ := h₁
  have hpl: 2 ≤ p := by linarith [h₀.1]
  have hql: 3 ≤ q := by linarith [h₀.2.1, hpl]
  have hrl: 4 ≤ r := by linarith [h₀.2.2, hql]
  have hden: 0 < (((p - 1) * (q - 1)) * (r - 1)) := by
    exact mul_pos (mul_pos (by linarith [h₀.1]) (by linarith [h₀.2.1])) (by linarith [h₀.2.2])
  have hk4: k < 4 := mylemma_k_lt_4 p q r k hk hpl hql hrl hden
  have hk1: 1 < k := mylemma_k_gt_1 p q r k hk hpl hql hrl hden
  have hpu: p < 4 := mylemma_p_lt_4 p q r k h₀ hk hpl hql hrl hden
  interval_cases k
  · exact mylemma_case_k_2 p q r h₀ hpl hql hrl hpu hk
  · exact mylemma_case_k_3 p q r h₀ hpl hql hrl hpu hk