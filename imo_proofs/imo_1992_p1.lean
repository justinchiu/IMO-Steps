import Mathlib
import ImoSteps
set_option linter.unusedVariables.analyzeTactics true

open Int Rat ImoSteps


lemma mylemma_main_lt2
  (p q r: ℤ)
  (hpl: 4 ≤ p)
  (hql: 5 ≤ q)
  (hrl: 6 ≤ r) :
  (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑2 := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)
    = (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) := by
    norm_cast
    simp
  have hp: (↑p/↑(p-1):ℚ) ≤ ((4/3):ℚ) := by
    have g₁: 0 < (↑(p - 1):ℚ) := by
      norm_cast
      linarith [hpl]
    have g₂: ↑p * ↑(3:ℚ) ≤ ↑(4:ℚ) * (↑(p - 1):ℚ) := by
      norm_cast
      linarith
    refine (div_le_iff₀ g₁).mpr ?_
    rw [div_mul_eq_mul_div]
    refine (le_div_iff₀ ?_).mpr g₂
    norm_num
  have hq: (↑q/↑(q-1)) ≤ ((5/4):ℚ) := by
    have g₁: 0 < (↑(q - 1):ℚ) := by
      norm_cast
      linarith[hql]
    have g₂: ↑q * ↑(4:ℚ) ≤ ↑(5:ℚ) * (↑(q - 1):ℚ) := by
      norm_cast
      linarith
    refine (div_le_iff₀ g₁).mpr ?_
    rw [div_mul_eq_mul_div]
    refine (le_div_iff₀ ?_).mpr g₂
    norm_num
  have hr: (↑r/↑(r-1)) ≤ ((6/5):ℚ) := by
    have g₁: 0 < (↑(r - 1):ℚ) := by
      norm_cast
      linarith[hql]
    have g₂: ↑r * ↑(5:ℚ) ≤ ↑(6:ℚ) * (↑(r - 1):ℚ) := by
      norm_cast
      linarith
    refine (div_le_iff₀ g₁).mpr ?_
    rw [div_mul_eq_mul_div]
    refine (le_div_iff₀ ?_).mpr g₂
    norm_num
  have hub: (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) ≤ (4/3:ℚ) * ((5/4):ℚ) * ((6/5):ℚ) := by
    have hq_nonneg: 0 ≤ (↑q:ℚ) := by
      norm_cast
      linarith
    have hq_1_nonneg: 0 ≤ (↑(q - 1):ℚ) := by
      norm_cast
      linarith
    have h₂: 0 ≤ (((q:ℚ) / ↑(q - 1)):ℚ) := by
      exact div_nonneg hq_nonneg hq_1_nonneg
    have hub1: (↑p/↑(p-1)) * (↑q/↑(q-1)) ≤ ((4/3):ℚ) * ((5/4):ℚ) := by
      exact mul_le_mul hp hq h₂ (by norm_num)
    have hr_nonneg: 0 ≤ (↑r:ℚ) := by
      norm_cast
      linarith
    have hr_1_nonneg: 0 ≤ (↑(r - 1):ℚ) := by
      norm_cast
      linarith
    have h₃: 0 ≤ (((r:ℚ) / ↑(r - 1)):ℚ) := by
      exact div_nonneg hr_nonneg hr_1_nonneg
    exact mul_le_mul hub1 hr h₃ (by norm_num)
  norm_num at hub
  rw [h₁]
  norm_num
  exact hub


lemma mylemma_k_lt_2
  (p q r k: ℤ)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (hpl: 4 ≤ p)
  (hql: 5 ≤ q)
  (hrl: 6 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1) ) :
  (k < 2) := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑2 := by
    exact mylemma_main_lt2 p q r hpl hql hrl
  have h₂: ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    have g₁: ↑(p * q * r - 1) = ↑k * (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
      norm_cast
      linarith
    symm
    have g₂: (↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≠ 0 := by
      norm_cast
      linarith[hden]
    exact (div_eq_iff g₂).mpr g₁
  have h₃: ↑k < (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    rw [h₂]
    have g₁: (↑(p * q * r - 1):ℚ) < (↑(p * q * r):ℚ) := by
      norm_cast
      exact sub_one_lt (p * q * r)
    have g₂: 0 < (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
      norm_cast
    exact div_lt_div_of_pos_right g₁ g₂
  have h₄: (↑k:ℚ) < ↑2 := by
    exact lt_of_lt_of_le h₃ h₁
  norm_cast at h₄


lemma mylemma_main_lt4
  (p q r: ℤ)
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r) :
  (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑4 := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)
      = (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) := by
    norm_cast
    simp
  have hp: (↑p/↑(p-1):ℚ) ≤ ↑(2:ℚ) := by
    have g₁: 0 < (↑(p - 1):ℚ) := by
      norm_cast
      linarith[hpl]
    have g₂: ↑p ≤ ↑(2:ℚ) * (↑(p - 1):ℚ) := by
      norm_cast
      linarith
    exact (div_le_iff₀ g₁).mpr g₂
  have hq: (↑q/↑(q-1)) ≤ ((3/2):ℚ) := by
    have g₁: 0 < (↑(q - 1):ℚ) := by
      norm_cast
      linarith[hql]
    have g₂: ↑q * ↑(2:ℚ) ≤ ↑(3:ℚ) * (↑(q - 1):ℚ) := by
      norm_cast
      linarith
    refine (div_le_iff₀ g₁).mpr ?_
    rw [div_mul_eq_mul_div]
    refine (le_div_iff₀ ?_).mpr g₂
    norm_num
  have hr: (↑r/↑(r-1)) ≤ ((4/3):ℚ) := by
    have g₁: 0 < (↑(r - 1):ℚ) := by
      norm_cast
      linarith[hql]
    have g₂: ↑r * ↑(3:ℚ) ≤ ↑(4:ℚ) * (↑(r - 1):ℚ) := by
      norm_cast
      linarith
    refine (div_le_iff₀ g₁).mpr ?_
    rw [div_mul_eq_mul_div]
    refine (le_div_iff₀ ?_).mpr g₂
    norm_num
  have hub: (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) ≤ (2:ℚ) * ((3/2):ℚ) * ((4/3):ℚ) := by
    have hq_nonneg: 0 ≤ (↑q:ℚ) := by
      norm_cast
      linarith
    have hq_1_nonneg: 0 ≤ (↑(q - 1):ℚ) := by
      norm_cast
      linarith
    have h₂: 0 ≤ (((q:ℚ) / ↑(q - 1)):ℚ) := by
      exact div_nonneg hq_nonneg hq_1_nonneg
    have hub1: (↑p/↑(p-1)) * (↑q/↑(q-1)) ≤ (2:ℚ) * ((3/2):ℚ) := by
      exact mul_le_mul hp hq h₂ (by norm_num)
    have hr_nonneg: 0 ≤ (↑r:ℚ) := by
      norm_cast
      linarith
    have hr_1_nonneg: 0 ≤ (↑(r - 1):ℚ) := by
      norm_cast
      linarith
    have h₃: 0 ≤ (((r:ℚ) / ↑(r - 1)):ℚ) := by
      exact div_nonneg hr_nonneg hr_1_nonneg
    exact mul_le_mul hub1 hr h₃ (by norm_num)
  norm_num at hub
  rw [h₁]
  norm_num
  exact hub



lemma mylemma_k_lt_4
  (p q r k: ℤ)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1) ) :
  (k < 4) := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑4 := by
    exact mylemma_main_lt4 p q r hpl hql hrl
  have h₂: ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    have g₁: ↑(p * q * r - 1) = ↑k * (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
      norm_cast
      linarith
    symm
    have g₂: (↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≠ 0 := by
      norm_cast
      linarith [hden]
    exact (div_eq_iff g₂).mpr g₁
  have h₃: ↑k < (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    rw [h₂]
    have g₁: (↑(p * q * r - 1):ℚ) < (↑(p * q * r):ℚ) := by
      norm_cast
      exact sub_one_lt (p * q * r)
    have g₂: 0 < (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
      norm_cast
    exact div_lt_div_of_pos_right g₁ g₂
  have h₄: (↑k:ℚ) < ↑4 := by
    exact lt_of_lt_of_le h₃ h₁
  norm_cast at h₄



lemma mylemma_k_gt_1
  (p q r k: ℤ)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (h₁: ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ))
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1) ) :
  (1 < k) := by
  have hk0: 0 < (↑k:ℚ) := by
    have g₁: 2*3*4 ≤ p * q * r := by
      have g₂: 2*3 ≤ p * q := by
        exact mul_le_mul hpl hql (by norm_num) (by linarith[hpl])
      exact mul_le_mul g₂ hrl (by norm_num) (by linarith[g₂])
    have g₂: 0 < (↑(p * q * r - 1):ℚ) := by
      norm_cast
      linarith[g₁]
    have g₃: 0 < (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
      norm_cast
    rw [h₁]
    exact div_pos g₂ g₃
  norm_cast at hk0
  by_contra hc
  push_neg at hc
  interval_cases k
  simp at hk
  exfalso
  have g₁: p*q + q*r + r*p = p+q+r := by linarith
  have g₂: p < p*q := by exact lt_mul_right (by linarith) (by linarith)
  have g₃: q < q*r := by exact lt_mul_right (by linarith) (by linarith)
  have g₄: r < r*p := by exact lt_mul_right (by linarith) (by linarith)
  have g₅: p+q+r < p*q + q*r + r*p := by linarith[g₂,g₃,g₄]
  linarith [g₁,g₅]



lemma mylemma_p_lt_4
  (p q r k: ℤ)
  (h₀ : 1 < p ∧ p < q ∧ q < r)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (h₁: ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ))
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1) ) :
  (p < 4) := by
  by_contra hcp
  push_neg at hcp
  have hcq: 5 ≤ q := by linarith
  have hcr: 6 ≤ r := by linarith
  have h₃: k < 2 := by exact mylemma_k_lt_2 p q r k hk hcp hcq hcr hden
  have h₄: 1 < k := by exact mylemma_k_gt_1 p q r k hk h₁ hpl hql hrl hden
  linarith




lemma mylemma_qr_11
  (q r: ℤ)
  (h₀: (4 - q) * (4 - r) = 11) :
  (4 - q = -1 ∨ 4 - q = 1 ∨ 4 - q = -11 ∨ 4 - q = 11) := by
  have h₁: Nat.Prime (11) := by decide
  exact prime_divisor_cases h₁ h₀


lemma mylemma_qr_5
  (q r: ℤ)
  (h₀: (q - 3) * (r - 3) = 5) :
  (q - 3 = -1 ∨ q - 3 = 1 ∨ q - 3 = -5 ∨ q - 3 = 5) := by
  have h₁: Nat.Prime (5) := by decide
  exact prime_divisor_cases h₁ h₀


lemma mylemma_63qr_5
  (q r: ℤ)
  (h₀: (6 - 3*q) * (2 - r) = 5) :
  (6 - 3*q = -1 ∨ 6 - 3*q = 1 ∨ 6 - 3*q = -5 ∨ 6 - 3*q = 5) := by
  have h₁: Nat.Prime (5) := by decide
  exact prime_divisor_cases h₁ h₀


lemma mylemma_case_k_2
  (p q r: ℤ)
  (h₀: 1 < p ∧ p < q ∧ q < r)
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r)
  (hpu: p < 4)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * 2) :
  (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  interval_cases p
  . exfalso
    norm_num at *
    have g₁: 2*q + 2*r = 3 := by linarith
    linarith [g₁,hql,hrl]
  . right
    norm_num at *
    -- have g₁: q*r - 4*q - 4*r + 5 = 0 := by linarith
    have g₂: (4-q)*(4-r) = 11 := by linarith
    have g₃: (4-q) = -1 ∨ (4-q) = 1 ∨ (4-q) = -11 ∨ (4-q) = 11 := by
      exact mylemma_qr_11 q r g₂
    cases' g₃ with g₃₁ g₃₂
    . have hq: q = 5 := by linarith
      constructor
      . exact hq
      . rw [hq] at g₂
        linarith[g₂]
    . exfalso
      cases' g₃₂ with g₃₂ g₃₃
      . have hq: q = 3 := by linarith[g₃₂]
        rw [hq] at g₂
        have hr: r = -7 := by linarith[g₂]
        linarith[hrl,hr]
      . cases' g₃₃ with g₃₃ g₃₄
        . have hq: q = 15 := by linarith[g₃₃]
          rw [hq] at g₂
          have hr: r = 5 := by linarith[g₂]
          linarith[hq,hr,h₀.2]
        . have hq: q = -7 := by linarith[g₃₄]
          linarith[hq,hql]


lemma mylemma_case_k_3
  (p q r: ℤ)
  (h₀: 1 < p ∧ p < q ∧ q < r)
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r)
  (hpu: p < 4)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * 3) :
  (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  interval_cases p
  -- p = 2
  . norm_num at *
    -- have g₁: q*r - 3*q - 3*r + 4 = 0 := by linarith
    have g₂: (q-3)*(r-3) = 5 := by linarith
    have g₃: (q-3) = -1 ∨ (q-3) = 1 ∨ (q-3) = -5 ∨ (q-3) = 5 := by
      exact mylemma_qr_5 q r g₂
    cases' g₃ with g₃₁ g₃₂
    . exfalso
      linarith [hql,g₃₁]
    . cases' g₃₂ with g₃₂ g₃₃
      . have hq: q = 4 := by linarith
        rw [hq] at g₂
        have hr: r = 8 := by linarith[g₂]
        exact { left := hq, right := hr }
      . exfalso
        cases' g₃₃ with g₃₃ g₃₄
        . linarith[hql,g₃₃]
        . have hq: q = 8 := by linarith
          rw [hq] at g₂
          norm_num at g₂
          have hr: r = 4 := by linarith
          linarith[hrl,hr]
  -- p = 3
  . right
    norm_num at *
    -- have g₁: 3 * q * r - 6 * q - 6 * r + 7 = 0 := by linarith
    have g₂: (6 - 3*q) * (2 - r) = 5 := by linarith
    have g₃: (6 - 3*q) = -1 ∨ (6 - 3*q) = 1 ∨ (6 - 3*q) = -5 ∨ (6 - 3*q) = 5 := by
      exact mylemma_63qr_5 q r g₂
    exfalso
    cases' g₃ with g₃₁ g₃₂
    . linarith[g₃₁,q]
    . cases' g₃₂ with g₃₂ g₃₃
      . linarith[g₃₂,q]
      . cases' g₃₃ with g₃₃ g₃₄
        . linarith[g₃₃,q]
        . linarith[g₃₄,q]



theorem imo_1992_p1
  (p q r : ℤ)
  (h₀ : 1 < p ∧ p < q ∧ q < r)
  (h₁ : (p - 1) * (q - 1) * (r - 1)∣(p * q * r - 1)) :
  (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  cases' h₁ with k hk
  have hpl: 2 ≤ p := by linarith
  have hql: 3 ≤ q := by linarith
  have hrl: 4 ≤ r := by linarith
  have hden: 0 < (((p - 1) * (q - 1)) * (r - 1)) := by
    have gp: 0 < (p - 1) := by linarith
    have gq: 0 < (q - 1) := by linarith
    have gr: 0 < (r - 1) := by linarith
    exact mul_pos (mul_pos gp gq) gr
  have h₁: ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    have g₁: ↑(p * q * r - 1) = ↑k * (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
      norm_cast
      linarith
    symm
    have g₂: (↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≠ 0 := by
      norm_cast
      linarith[hden]
    exact (div_eq_iff g₂).mpr g₁
  have hk4: k < 4 := by exact mylemma_k_lt_4 p q r k hk hpl hql hrl hden
  have hk1: 1 < k := by exact mylemma_k_gt_1 p q r k hk h₁ hpl hql hrl hden
  have hpu: p < 4 := by exact mylemma_p_lt_4 p q r k h₀ hk h₁ hpl hql hrl hden
  interval_cases k
  . exact mylemma_case_k_2 p q r h₀ hpl hql hrl hpu hk
  . exact mylemma_case_k_3 p q r h₀ hpl hql hrl hpu hk
