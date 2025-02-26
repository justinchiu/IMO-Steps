import Mathlib
set_option linter.unusedVariables.analyzeTactics true

open Int Rat


lemma imo_1992_p1_1
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


lemma imo_1992_p1_1_1
  (p : ℤ)
  (hpl : 4 ≤ p) :
  ↑p / ↑(p - 1) ≤ ((4/3):ℚ) := by
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


lemma imo_1992_p1_1_2
  (p : ℤ)
  -- (q r : ℤ)
  -- (hpl : 4 ≤ p)
  -- (hql : 5 ≤ q)
  -- (hrl : 6 ≤ r)
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  (g₁ : 0 < (↑(p - 1):ℚ))
  (g₂ : ↑p * ↑(3:ℚ) ≤ ↑(4:ℚ) * (↑(p - 1):ℚ)) :
  ↑p / ↑(p - 1) ≤ ((4/3):ℚ) := by
  refine (div_le_iff₀ g₁).mpr ?_
  rw [div_mul_eq_mul_div]
  refine (le_div_iff₀ ?_).mpr g₂
  norm_num


lemma imo_1992_p1_1_3
  -- (p r : ℤ)
  (q: ℤ)
  -- (hpl : 4 ≤ p)
  (hql : 5 ≤ q) :
  -- (hrl : 6 ≤ r)
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  -- (hp : ↑p / ↑(p - 1) ≤ 4 / 3) :
  ↑q / ↑(q - 1) ≤ ((5 / 4):ℚ) := by
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


lemma imo_1992_p1_1_4
  -- (p r : ℤ)
  (q: ℤ)
  -- (hpl : 4 ≤ p)
  -- (hql : 5 ≤ q)
  -- (hrl : 6 ≤ r)
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  -- (hp : ↑p / ↑(p - 1) ≤ 4 / 3)
  (g₁ : 0 < (↑(q - 1):ℚ))
  (g₂ : ↑q * ↑(4:ℚ) ≤ ↑(5:ℚ) * (↑(q - 1):ℚ)) :
  ↑q / ↑(q - 1) ≤ ((5 / 4):ℚ) := by
  refine (div_le_iff₀ g₁).mpr ?_
  rw [div_mul_eq_mul_div]
  refine (le_div_iff₀ ?_).mpr g₂
  norm_num


lemma imo_1992_p1_1_5
  (p q r : ℤ)
  -- (hpl : 4 ≤ p)
  (hql : 5 ≤ q)
  (hrl : 6 ≤ r)
  (h₁ : (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)
          = (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)))
  (hp : ↑p / ↑(p - 1) ≤ ((4 / 3):ℚ))
  (hq : ↑q / ↑(q - 1) ≤ ((5 / 4):ℚ)) :
  (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑2 := by
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


lemma imo_1992_p1_1_6
  -- (p : ℤ)
  (q r : ℤ)
  -- (hpl : 4 ≤ p)
  (hql : 5 ≤ q)
  (hrl : 6 ≤ r) :
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  -- (hp : ↑p / ↑(p - 1) ≤ 4 / 3)
  -- (hq : ↑q / ↑(q - 1) ≤ 5 / 4) :
  ↑r / ↑(r - 1) ≤ ((6/5):ℚ) := by
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


lemma imo_1992_p1_1_7
  -- (p q : ℤ)
  (r : ℤ)
  -- (hpl : 4 ≤ p)
  -- (hql : 5 ≤ q)
  -- (hrl : 6 ≤ r)
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  -- (hp : ↑p / ↑(p - 1) ≤ 4 / 3)
  -- (hq : ↑q / ↑(q - 1) ≤ 5 / 4)
  (g₁ : 0 < (↑(r - 1):ℚ))
  (g₂ : ↑r * ↑(5:ℚ) ≤ ↑(6:ℚ) * (↑(r - 1):ℚ)) :
  ↑r / ↑(r - 1) ≤ ((6/5):ℚ) := by
  refine (div_le_iff₀ g₁).mpr ?_
  rw [div_mul_eq_mul_div]
  refine (le_div_iff₀ ?_).mpr g₂
  norm_num


lemma imo_1992_p1_1_8
  (p q r : ℤ)
  -- (hpl : 4 ≤ p)
  (hql : 5 ≤ q)
  (hrl : 6 ≤ r)
  (h₁ : (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)
          = (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)))
  (hp : ↑p / ↑(p - 1) ≤ ((4/3):ℚ))
  (hq : ↑q / ↑(q - 1) ≤ ((5/4):ℚ))
  (hr : ↑r / ↑(r - 1) ≤ ((6/5):ℚ)) :
  (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑2 := by
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


lemma imo_1992_p1_1_9
  (p q r : ℤ)
  -- (hpl : 4 ≤ p)
  (hql : 5 ≤ q)
  (hrl : 6 ≤ r)
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  (hp : ↑p / ↑(p - 1) ≤ ((4 / 3):ℚ))
  (hq : ↑q / ↑(q - 1) ≤ ((5 / 4):ℚ))
  (hr : ↑r / ↑(r - 1) ≤ ((6 / 5):ℚ)) :
  (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) ≤ (4/3:ℚ) * ((5/4):ℚ) * ((6/5):ℚ) := by
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


lemma imo_1992_p1_1_10
  -- (p r : ℤ)
  (q : ℤ)
  -- (hpl : 4 ≤ p)
  (hql : 5 ≤ q) :
  -- (hrl : 6 ≤ r)
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  -- (hp : ↑p / ↑(p - 1) ≤ 4 / 3)
  -- (hq : ↑q / ↑(q - 1) ≤ 5 / 4)
  -- (hr : ↑r / ↑(r - 1) ≤ 6 / 5) :
  -- hq_nonneg : 0 ≤ ↑q
  -- hq_1_nonneg : 0 ≤ ↑(q - 1)
  0 ≤ (((q:ℚ) / ↑(q - 1)):ℚ) := by
  have hq_nonneg: 0 ≤ (↑q:ℚ) := by
    norm_cast
    linarith
  have hq_1_nonneg: 0 ≤ (↑(q - 1):ℚ) := by
    norm_cast
    linarith
  exact div_nonneg hq_nonneg hq_1_nonneg


lemma imo_1992_p1_1_11
  (p q r : ℤ)
  -- (hpl : 4 ≤ p)
  -- (hql : 5 ≤ q)
  -- (hrl : 6 ≤ r)
  (h₁ : (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)
          = (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)))
  -- (hp : ↑p / ↑(p - 1) ≤ 4 / 3)
  -- (hq : ↑q / ↑(q - 1) ≤ 5 / 4)
  -- (hr : ↑r / ↑(r - 1) ≤ 6 / 5)
  (hub : (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) ≤ (4/3:ℚ) * ((5/4):ℚ) * ((6/5):ℚ)) :
  (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑2 := by
  rw [h₁]
  norm_num
  norm_num at hub
  exact hub


lemma imo_1992_p1_1_12
  (p q r : ℤ)
  -- (hpl : 4 ≤ p)
  -- (hql : 5 ≤ q)
  -- (hrl : 6 ≤ r)
  -- -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  -- (hp : ↑p / ↑(p - 1) ≤ 4 / 3)
  -- (hq : ↑q / ↑(q - 1) ≤ 5 / 4)
  -- (hr : ↑r / ↑(r - 1) ≤ 6 / 5)
  (hub : (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) ≤ (4/3:ℚ) * ((5/4):ℚ) * ((6/5):ℚ)) :
  (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑2 := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)
    = (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) := by
    norm_cast
    simp
  rw [h₁]
  norm_num
  norm_num at hub
  exact hub


lemma imo_1992_p1_2
  (p q r k: ℤ)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (hpl: 4 ≤ p)
  (hql: 5 ≤ q)
  (hrl: 6 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1) ) :
  (k < 2) := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑2 := by
    exact imo_1992_p1_1 p q r hpl hql hrl
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


lemma imo_1992_p1_2_1
  (p q r k : ℤ)
  (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  -- (hpl : 4 ≤ p)
  -- (hql : 5 ≤ q)
  -- (hrl : 6 ≤ r)
  (hden : 0 < (p - 1) * (q - 1) * (r - 1))
  (h₁ : (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ 2) :
  k < 2 := by
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


lemma imo_1992_p1_2_2
  (p q r k : ℤ)
  (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  -- (hpl : 4 ≤ p)
  -- (hql : 5 ≤ q)
  -- (hrl : 6 ≤ r)
  (hden : 0 < (p - 1) * (q - 1) * (r - 1)) :
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) ≤ 2) :
  ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
  have g₁: ↑(p * q * r - 1) = ↑k * (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    norm_cast
    linarith
  symm
  have g₂: (↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≠ 0 := by
    norm_cast
    linarith[hden]
  exact (div_eq_iff g₂).mpr g₁


lemma imo_1992_p1_2_3
  (p q r k : ℤ)
  -- (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  -- (hpl : 4 ≤ p)
  -- (hql : 5 ≤ q)
  -- (hrl : 6 ≤ r)
  (hden : 0 < (p - 1) * (q - 1) * (r - 1))
  (h₁ : (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑2)
  (h₂ : ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ)) :
  k < 2 := by
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


lemma imo_1992_p1_2_4
  (p q r k : ℤ)
  -- (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  -- (hpl : 4 ≤ p)
  -- (hql : 5 ≤ q)
  -- (hrl : 6 ≤ r)
  (hden : 0 < (p - 1) * (q - 1) * (r - 1))
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) ≤ 2)
  (h₂ : ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ)) :
  ↑k < (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
  rw [h₂]
  have g₁: (↑(p * q * r - 1):ℚ) < (↑(p * q * r):ℚ) := by
    norm_cast
    exact sub_one_lt (p * q * r)
  have g₂: 0 < (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    norm_cast
  exact div_lt_div_of_pos_right g₁ g₂


lemma imo_1992_p1_2_5
  (p q r k : ℤ)
  -- (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  -- (hpl : 4 ≤ p)
  -- (hql : 5 ≤ q)
  -- (hrl : 6 ≤ r)
  -- (hden : 0 < (p - 1) * (q - 1) * (r - 1))
  (h₁ : (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑2)
  -- (h₂ : ↑k = ↑(p * q * r - 1) / ↑((p - 1) * (q - 1) * (r - 1)))
  (h₃ : ↑k < (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)) :
  k < 2 := by
  have h₄: (↑k:ℚ) < ↑2 := by
    exact lt_of_lt_of_le h₃ h₁
  norm_cast at h₄


lemma imo_1992_p1_3
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


lemma imo_1992_p1_3_1
  (p : ℤ)
  -- (q r : ℤ)
  (hpl : 2 ≤ p) :
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  -- (h₁ : (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)
  --     = (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1))) :
  (↑p/↑(p-1):ℚ) ≤ ↑(2:ℚ) := by
  have g₁: 0 < (↑(p - 1):ℚ) := by
    norm_cast
    linarith[hpl]
  have g₂: ↑p ≤ ↑(2:ℚ) * (↑(p - 1):ℚ) := by
    norm_cast
    linarith
  exact (div_le_iff₀ g₁).mpr g₂


lemma imo_1992_p1_3_2
  (p : ℤ)
  -- (q r : ℤ)
  (hpl : 2 ≤ p)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  (g₁ : 0 < (↑(p - 1):ℚ)) :
  (↑p/↑(p-1):ℚ) ≤ ↑(2:ℚ) := by
  have g₂: ↑p ≤ ↑(2:ℚ) * (↑(p - 1):ℚ) := by
    norm_cast
    linarith
  exact (div_le_iff₀ g₁).mpr g₂


lemma imo_1992_p1_3_3
  -- (p r : ℤ)
  (q : ℤ)
  -- (hpl : 2 ≤ p)
  (hql : 3 ≤ q) :
  -- (hrl : 4 ≤ r)
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  -- (hp : ↑p / ↑(p - 1) ≤ 2) :
  (↑q/↑(q-1)) ≤ ((3/2):ℚ) := by
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


lemma imo_1992_p1_3_4
  -- (p r : ℤ)
  (q : ℤ)
  -- (hpl : 2 ≤ p)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  -- (hp : ↑p / ↑(p - 1) ≤ 2)
  (g₁ : 0 < (↑(q - 1):ℚ))
  (g₂ : ↑q * ↑(2:ℚ) ≤ ↑(3:ℚ) * (↑(q - 1):ℚ)) :
  (↑q/↑(q-1)) ≤ ((3/2):ℚ) := by
  refine (div_le_iff₀ g₁).mpr ?_
  rw [div_mul_eq_mul_div]
  refine (le_div_iff₀ ?_).mpr g₂
  norm_num


lemma imo_1992_p1_3_5
  -- (p q : ℤ)
  (r : ℤ)
  -- (hpl : 2 ≤ p)
  -- (hql : 3 ≤ q)
  (hrl : 4 ≤ r) :
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  -- (hp : ↑p / ↑(p - 1) ≤ 2)
  -- (hq : ↑q / ↑(q - 1) ≤ 3 / 2) :
  ↑r / ↑(r - 1) ≤ ((4 / 3):ℚ) := by
  have g₁: 0 < (↑(r - 1):ℚ) := by
    norm_cast
    linarith
  have g₂: ↑r * ↑(3:ℚ) ≤ ↑(4:ℚ) * (↑(r - 1):ℚ) := by
    norm_cast
    linarith
  refine (div_le_iff₀ g₁).mpr ?_
  rw [div_mul_eq_mul_div]
  refine (le_div_iff₀ ?_).mpr g₂
  norm_num


lemma imo_1992_p1_3_6
  -- (p q : ℤ)
  (r : ℤ)
  -- (hpl : 2 ≤ p)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  -- (hp : ↑p / ↑(p - 1) ≤ 2)
  -- (hq : ↑q / ↑(q - 1) ≤ 3 / 2)
  (g₁ : 0 < (↑(r - 1):ℚ))
  (g₂ : ↑r * ↑(3:ℚ) ≤ ↑(4:ℚ) * (↑(r - 1):ℚ)) :
  ↑r / ↑(r - 1) ≤ ((4 / 3):ℚ) := by
  refine (div_le_iff₀ g₁).mpr ?_
  rw [div_mul_eq_mul_div]
  refine (le_div_iff₀ ?_).mpr g₂
  norm_num


lemma imo_1992_p1_3_7
  (p q r : ℤ)
  -- (hpl : 2 ≤ p)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  -- (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  (hp : (↑p/↑(p-1):ℚ) ≤ ↑(2:ℚ))
  (hq : ↑q / ↑(q - 1) ≤ ((3 / 2):ℚ))
  (hr : ↑r / ↑(r - 1) ≤ ((4 / 3):ℚ)) :
  (↑p/↑(p-1)) * (↑q/↑(q-1)) * (↑r/↑(r-1)) ≤ (2:ℚ) * ((3/2):ℚ) * ((4/3):ℚ) := by
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


lemma imo_1992_p1_3_8
  (p q r : ℤ)
  -- (hpl : 2 ≤ p)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  (h₁ : ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) = ↑p / ↑(p - 1) * (↑q / ↑(q - 1)) * (↑r / ↑(r - 1)))
  -- (hp : ↑p / ↑(p - 1) ≤ 2)
  -- (hq : ↑q / ↑(q - 1) ≤ 3 / 2)
  -- (hr : ↑r / ↑(r - 1) ≤ 4 / 3)
  (hub : ↑p / (↑p - 1) * (↑q / (↑q - 1)) * (↑r / (↑r - 1)) ≤ 4) :
  ↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)) ≤ 4 := by
  rw [h₁]
  exact hub


lemma imo_1992_p1_4
  (p q r k: ℤ)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1) ) :
  (k < 4) := by
  have h₁: (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑4 := by
    exact imo_1992_p1_3 p q r hpl hql hrl
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


lemma imo_1992_p1_4_1
  (p q r k : ℤ)
  -- (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  -- (hpl : 2 ≤ p)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  -- (hden : 0 < (p - 1) * (q - 1) * (r - 1))
  (h₁ : (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≤ ↑4)
  -- (h₂ : ↑k = ↑(p * q * r - 1) / ↑((p - 1) * (q - 1) * (r - 1)))
  (h₃ : ↑k < (↑(p * q * r) / ↑((p - 1) * (q - 1) * (r - 1)):ℚ)) :
  k < 4 := by
  have h₄: (↑k:ℚ) < ↑4 := by
    exact lt_of_lt_of_le h₃ h₁
  norm_cast at h₄


lemma imo_1992_p1_5
  (p q r k: ℤ)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (h₁: ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ))
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1)) :
  (1 < k) := by
  have hk0: 0 < (↑k:ℚ) := by
    have g₁: 2 * 3 * 4 ≤ p * q * r := by
      have g₂: 2 * 3 ≤ p * q := by
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
  by_contra! hc
  interval_cases k
  simp at hk
  have g₁: p*q + q*r + r*p = p+q+r := by linarith
  have g₂: p < p*q := by exact lt_mul_right (by linarith) (by linarith)
  have g₃: q < q*r := by exact lt_mul_right (by linarith) (by linarith)
  have g₄: r < r*p := by exact lt_mul_right (by linarith) (by linarith)
  have g₅: p+q+r < p*q + q*r + r*p := by linarith[g₂,g₃,g₄]
  linarith [g₁,g₅]


lemma imo_1992_p1_5_1
  (p q r k : ℤ)
  -- (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (h₁ : ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ))
  (hpl : 2 ≤ p)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1)) :
  0 < (↑k:ℚ) := by
  have g₁: 2 * 3 * 4 ≤ p * q * r := by
    have g₂: 2 * 3 ≤ p * q := by
      exact mul_le_mul hpl hql (by norm_num) (by linarith[hpl])
    exact mul_le_mul g₂ hrl (by norm_num) (by linarith[g₂])
  have g₂: 0 < (↑(p * q * r - 1):ℚ) := by
    norm_cast
    linarith[g₁]
  have g₃: 0 < (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    norm_cast
  rw [h₁]
  exact div_pos g₂ g₃


lemma imo_1992_p1_5_2
  (p q r : ℤ)
  -- (k : ℤ)
  -- (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  -- (h₁ : ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ))
  (hpl : 0 < (p - 1))
  (hql : 0 < (q - 1))
  (hrl : 0 < (r - 1)) :
  -- (hden: 0 < (p - 1) * (q - 1) * (r - 1)) :
  -- (g₁ : 2 * 3 * 4 ≤ p * q * r)
  -- (g₂ : 0 < (↑(p * q * r - 1):ℚ)) :
  0 < (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
  norm_cast
  refine mul_pos ?_ hrl
  exact mul_pos hpl hql


lemma imo_1992_p1_5_3
  (p q r : ℤ)
  -- (k : ℤ)
  -- (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  -- (h₁ : ↑k = ↑(p * q * r - 1) / ↑((p - 1) * (q - 1) * (r - 1)))
  (hpl : 2 ≤ p)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r) :
  0 < ↑(p * q * r - 1) := by
  have g₁: 2 * 3 * 4 ≤ p * q * r := by
    have g₂: 2 * 3 ≤ p * q := by
      exact mul_le_mul hpl hql (by norm_num) (by linarith[hpl])
    exact mul_le_mul g₂ hrl (by norm_num) (by linarith[g₂])
  norm_cast
  linarith[g₁]


lemma imo_1992_p1_5_4
  (p q r k : ℤ)
  (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (h₁ : ↑k = ↑(p * q * r - 1) / ↑((p - 1) * (q - 1) * (r - 1)))
  (hpl : 2 ≤ p)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  -- (hden : 0 < (p - 1) * (q - 1) * (r - 1))
  (hk0 : 0 < k) :
  1 < k := by
  by_contra! hc
  interval_cases k
  simp at hk
  have g₁: p*q + q*r + r*p = p+q+r := by linarith
  have g₂: p < p*q := by exact lt_mul_right (by linarith) (by linarith)
  have g₃: q < q*r := by exact lt_mul_right (by linarith) (by linarith)
  have g₄: r < r*p := by exact lt_mul_right (by linarith) (by linarith)
  have g₅: p+q+r < p*q + q*r + r*p := by linarith[g₂,g₃,g₄]
  linarith [g₁,g₅]


lemma imo_1992_p1_5_5
  (p q r : ℤ)
  -- (k : ℤ)
  (hpl : 2 ≤ p)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  -- (hden : 0 < (p - 1) * (q - 1) * (r - 1))
  (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * 1) :
  -- (h₁ : ↑1 = ↑(p * q * r - 1) / ↑((p - 1) * (q - 1) * (r - 1)))
  -- (hk0 : 0 < 1)
  -- (hc : 1 ≤ 1) :
  False := by
  simp at hk
  have g₁: p * q + q * r + r * p = p + q + r := by linarith
  have g₂: p < p * q := by exact lt_mul_right (by linarith) (by linarith)
  have g₃: q < q * r := by exact lt_mul_right (by linarith) (by linarith)
  have g₄: r < r * p := by exact lt_mul_right (by linarith) (by linarith)
  have g₅: p + q + r < p * q + q * r + r * p := by linarith[g₂,g₃,g₄]
  linarith [g₁,g₅]


lemma imo_1992_p1_5_6
  (p q r : ℤ)
  -- (k : ℤ)
  (hpl : 2 ≤ p)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  -- (hden : 0 < (p - 1) * (q - 1) * (r - 1))
  -- (h₁ : ↑1 = ↑(p * q * r - 1) / ↑((p - 1) * (q - 1) * (r - 1)))
  -- (hk0 : 0 < 1)
  -- (hc : 1 ≤ 1)
  -- (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1))
  (g₁ : p * q + q * r + r * p = p + q + r) :
  False := by
  have g₂: p < p * q := by exact lt_mul_right (by linarith) (by linarith)
  have g₃: q < q * r := by exact lt_mul_right (by linarith) (by linarith)
  have g₄: r < r * p := by exact lt_mul_right (by linarith) (by linarith)
  have g₅: p + q + r < p * q + q * r + r * p := by linarith[g₂,g₃,g₄]
  linarith [g₁,g₅]


lemma imo_1992_p1_5_7
  (p q r : ℤ)
  -- (k : ℤ)
  (hpl : 2 ≤ p)
  -- (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  -- (hden : 0 < (p - 1) * (q - 1) * (r - 1))
  -- (h₁ : ↑1 = ↑(p * q * r - 1) / ↑((p - 1) * (q - 1) * (r - 1)))
  -- (hk0 : 0 < 1)
  -- (hc : 1 ≤ 1)
  -- (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1))
  (g₁ : p * q + q * r + r * p = p + q + r)
  (g₂: p < p * q)
  (g₃: q < q * r) :
  False := by
  have g₄: r < r * p := by exact lt_mul_right (by linarith) (by linarith)
  have g₅: p + q + r < p * q + q * r + r * p := by linarith[g₂,g₃,g₄]
  linarith [g₁,g₅]


lemma imo_1992_p1_6
  (p q r k: ℤ)
  (h₀ : 1 < p ∧ p < q ∧ q < r)
  (hk: p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (h₁: ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ))
  (hpl: 2 ≤ p)
  (hql: 3 ≤ q)
  (hrl: 4 ≤ r)
  (hden: 0 < (p - 1) * (q - 1) * (r - 1) ) :
  (p < 4) := by
  by_contra! hcp
  have hcq: 5 ≤ q := by linarith
  have hcr: 6 ≤ r := by linarith
  have h₃: k < 2 := by exact imo_1992_p1_2 p q r k hk hcp hcq hcr hden
  have h₄: 1 < k := by exact imo_1992_p1_5 p q r k hk h₁ hpl hql hrl hden
  linarith


lemma imo_1992_p1_6_1
  (p q r k : ℤ)
  (h₀ : 1 < p ∧ p < q ∧ q < r)
  (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (h₁ : ↑k = ↑(p * q * r - 1) / ↑((p - 1) * (q - 1) * (r - 1)))
  (hpl : 2 ≤ p)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  (hden : 0 < (p - 1) * (q - 1) * (r - 1))
  (hcp : 4 ≤ p)
  (hcq : 5 ≤ q)
  (hcr : 6 ≤ r)
  (h₃ : k < 2)
  (h₄ : 1 < k) :
  p < 4 := by
  linarith


lemma imo_1992_p1_7
  (q r : ℤ)
  (p: ℕ)
  (h₀ : q * r = ↑p)
  (h₁: Nat.Prime p) :
  q = -1 ∨ q = 1 ∨ q = -p ∨ q = p := by
  have hq : q ≠ 0 := by
    intro h
    rw [h] at h₀
    simp at h₀
    symm at h₀
    norm_cast at h₀
    rw [h₀] at h₁
    exact Nat.not_prime_zero h₁
  have hr : r ≠ 0 := by
    intro h
    rw [h] at h₀
    simp at h₀
    norm_cast at h₀
    rw [← h₀] at h₁
    exact Nat.not_prime_zero h₁
  have hqr : abs q * abs r = p := by
    have h₃: abs q = q.natAbs := by exact abs_eq_natAbs q
    have h₄: abs r = r.natAbs := by exact abs_eq_natAbs r
    rw [h₃,h₄]
    norm_cast
    exact Int.natAbs_mul_natAbs_eq h₀
  have h_abs: abs (↑(q.natAbs):ℤ) = 1 ∨ abs q = p := by
    cases' Int.natAbs_eq q with h_1 h_2
    . rw [h_1] at hqr
      have h₂: abs (↑(q.natAbs):ℤ) ∣ p := by exact Dvd.intro (abs r) hqr
      have h₃: (↑(q.natAbs):ℕ) ∣ p := by
        norm_cast at *
      have h₄: (↑(q.natAbs):ℕ) = 1 ∨ (↑(q.natAbs):ℕ) = p := by
        exact Nat.Prime.eq_one_or_self_of_dvd h₁ (↑(q.natAbs):ℕ) h₃
      cases' h₄ with h₄₀ h₄₁
      . left
        norm_cast at *
      . have h₅: abs q = q.natAbs := by exact abs_eq_natAbs q
        right
        rw [h₅]
        norm_cast at *
    . rw [h_2] at hqr
      rw [abs_neg _] at hqr
      have h₂: abs (↑(q.natAbs):ℤ) ∣ p := by exact Dvd.intro (abs r) hqr
      have h₃: (↑(q.natAbs):ℕ) ∣ p := by
        norm_cast at *
      have h₄: (↑(q.natAbs):ℕ) = 1 ∨ (↑(q.natAbs):ℕ) = p := by
        exact Nat.Prime.eq_one_or_self_of_dvd h₁ (↑(q.natAbs):ℕ) h₃
      cases' h₄ with h₄₀ h₄₁
      . left
        norm_cast at *
      . have h₅: abs q = q.natAbs := by exact abs_eq_natAbs q
        right
        rw [h₅]
        norm_cast
  cases' h_abs with hq_abs hq_abs
  . norm_cast at *
    have h₄: q = ↑(q.natAbs) ∨ q = -↑(q.natAbs) := by
      exact Int.natAbs_eq q
    rw [hq_abs] at h₄
    norm_cast at h₄
    cases' h₄ with h₄₀ h₄₁
    . right
      left
      exact h₄₀
    . left
      exact h₄₁
  . right
    right
    have h₂: abs q = q.natAbs := by exact abs_eq_natAbs q
    rw [h₂] at hq_abs
    norm_cast at hq_abs
    refine or_comm.mp ?_
    refine (Int.natAbs_eq_natAbs_iff).mp ?_
    norm_cast


lemma imo_1992_p1_7_1
  (q r : ℤ)
  (p : ℕ)
  (h₀ : q * r = ↑p)
  (h₁ : Nat.Prime p) :
  q ≠ 0 := by
  intro h
  rw [h] at h₀
  simp at h₀
  symm at h₀
  norm_cast at h₀
  rw [h₀] at h₁
  exact Nat.not_prime_zero h₁


lemma imo_1992_p1_7_2
  (q r : ℤ)
  (p : ℕ)
  (h₀ : q * r = ↑p)
  (h₁ : Nat.Prime p)
  (hq : q ≠ 0) :
  r ≠ 0 := by
  intro h
  rw [h] at h₀
  simp at h₀
  norm_cast at h₀
  rw [← h₀] at h₁
  exact Nat.not_prime_zero h₁


lemma imo_1992_p1_7_3
  (q r : ℤ)
  (p : ℕ)
  (h₀ : q * r = ↑p) :
  -- (h₁ : Nat.Prime p)
  -- (hq : q ≠ 0)
  -- (hr : r ≠ 0) :
  |q| * |r| = ↑p := by
  have h₃: abs q = q.natAbs := by exact abs_eq_natAbs q
  have h₄: abs r = r.natAbs := by exact abs_eq_natAbs r
  rw [h₃,h₄]
  norm_cast
  exact Int.natAbs_mul_natAbs_eq h₀


lemma imo_1992_p1_7_4
  (q r : ℤ)
  (p : ℕ)
  (h₀ : q * r = ↑p)
  -- (h₁ : Nat.Prime p)
  -- (hq : q ≠ 0)
  -- (hr : r ≠ 0)
  (h₃ : |q| = ↑(natAbs q))
  (h₄ : |r| = ↑(natAbs r)) :
  |q| * |r| = ↑p := by
  rw [h₃,h₄]
  norm_cast
  exact Int.natAbs_mul_natAbs_eq h₀


lemma imo_1992_p1_7_5
  (q r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  (h₁ : Nat.Prime p)
  (hq : q ≠ 0)
  (hr : r ≠ 0)
  (hqr : |q| * |r| = ↑p) :
  |(↑(natAbs q):ℤ)| = 1 ∨ |q| = ↑p := by
  cases' Int.natAbs_eq q with h_1 h_2
  . rw [h_1] at hqr
    have h₂: abs (↑(q.natAbs):ℤ) ∣ p := by exact Dvd.intro (abs r) hqr
    have h₃: (↑(q.natAbs):ℕ) ∣ p := by
      norm_cast at *
    have h₄: (↑(q.natAbs):ℕ) = 1 ∨ (↑(q.natAbs):ℕ) = p := by
      exact Nat.Prime.eq_one_or_self_of_dvd h₁ (↑(q.natAbs):ℕ) h₃
    cases' h₄ with h₄₀ h₄₁
    . left
      norm_cast at *
    . have h₅: abs q = q.natAbs := by exact abs_eq_natAbs q
      right
      rw [h₅]
      norm_cast at *
  . rw [h_2] at hqr
    rw [abs_neg _] at hqr
    have h₂: abs (↑(q.natAbs):ℤ) ∣ p := by exact Dvd.intro (abs r) hqr
    have h₃: (↑(q.natAbs):ℕ) ∣ p := by
      norm_cast at *
    have h₄: (↑(q.natAbs):ℕ) = 1 ∨ (↑(q.natAbs):ℕ) = p := by
      exact Nat.Prime.eq_one_or_self_of_dvd h₁ (↑(q.natAbs):ℕ) h₃
    cases' h₄ with h₄₀ h₄₁
    . left
      norm_cast at *
    . have h₅: abs q = q.natAbs := by exact abs_eq_natAbs q
      right
      rw [h₅]
      norm_cast


lemma imo_1992_p1_7_6
  (q r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  (h₁ : Nat.Prime p)
  (hq : q ≠ 0)
  (hr : r ≠ 0)
  (hqr : |q| * |r| = ↑p)
  (h_1 : q = ↑(natAbs q)) :
  |(↑(natAbs q):ℤ)| = 1 ∨ |q| = ↑p := by
  rw [h_1] at hqr
  have h₂: abs (↑(q.natAbs):ℤ) ∣ p := by exact Dvd.intro (abs r) hqr
  have h₃: (↑(q.natAbs):ℕ) ∣ p := by
    norm_cast at *
  have h₄: (↑(q.natAbs):ℕ) = 1 ∨ (↑(q.natAbs):ℕ) = p := by
    exact Nat.Prime.eq_one_or_self_of_dvd h₁ (↑(q.natAbs):ℕ) h₃
  cases' h₄ with h₄₀ h₄₁
  . left
    norm_cast at *
  . have h₅: abs q = q.natAbs := by exact abs_eq_natAbs q
    right
    rw [h₅]
    norm_cast at *


lemma imo_1992_p1_7_7
  (q r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  -- (h₁ : Nat.Prime p)
  (hq : q ≠ 0)
  (hr : r ≠ 0)
  (hqr : |↑(natAbs q)| * |r| = ↑p)
  (h_1 : q = ↑(natAbs q))
  (h₂ : |(↑(natAbs q):ℤ)| ∣ ↑p)
  -- (h₃ : natAbs q ∣ p)
  (h₄ : natAbs q = 1 ∨ natAbs q = p) :
  |(↑(natAbs q):ℤ)| = 1 ∨ |q| = ↑p := by
  cases' h₄ with h₄₀ h₄₁
  . left
    norm_cast at *
  . have h₅: abs q = q.natAbs := by exact abs_eq_natAbs q
    right
    rw [h₅]
    norm_cast at *


lemma imo_1992_p1_7_8
  (q r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  -- (h₁ : Nat.Prime p)
  (hq : q ≠ 0)
  (hr : r ≠ 0)
  (hqr : |↑(natAbs q)| * |r| = ↑p)
  (h_1 : q = ↑(natAbs q))
  (h₂ : |(↑(natAbs q):ℤ)| ∣ ↑p)
  -- (h₃ : natAbs q ∣ p)
  (h₄₁ : natAbs q = p) :
  |(↑(natAbs q):ℤ)| = 1 ∨ |q| = ↑p := by
  have h₅: abs q = q.natAbs := by exact abs_eq_natAbs q
  right
  rw [h₅]
  norm_cast at *


lemma imo_1992_p1_7_9
  (q r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  (h₁ : Nat.Prime p)
  (hq : q ≠ 0)
  (hr : r ≠ 0)
  (hqr : |q| * |r| = ↑p)
  (h_2 : q = -↑(natAbs q)) :
  |(↑(natAbs q):ℤ)| = 1 ∨ |q| = ↑p := by
  rw [h_2] at hqr
  rw [abs_neg _] at hqr
  have h₂: abs (↑(q.natAbs):ℤ) ∣ p := by exact Dvd.intro (abs r) hqr
  have h₃: (↑(q.natAbs):ℕ) ∣ p := by
    norm_cast at *
  have h₄: (↑(q.natAbs):ℕ) = 1 ∨ (↑(q.natAbs):ℕ) = p := by
    exact Nat.Prime.eq_one_or_self_of_dvd h₁ (↑(q.natAbs):ℕ) h₃
  cases' h₄ with h₄₀ h₄₁
  . left
    norm_cast at *
  . have h₅: abs q = q.natAbs := by exact abs_eq_natAbs q
    right
    rw [h₅]
    norm_cast


lemma imo_1992_p1_7_10
  (q r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  -- (h₁ : Nat.Prime p)
  -- (hq : q ≠ 0)
  -- (hr : r ≠ 0)
  (hqr : |(↑(natAbs q):ℤ)| * |r| = ↑p)
  (h_2 : q = (-↑(q.natAbs):ℤ)) :
  |(↑(natAbs q):ℤ)| ∣ ↑p := by
  refine Dvd.intro (abs r) ?_
  simp at *
  exact hqr


lemma imo_1992_p1_7_11
  (q : ℤ)
  -- (r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  (h₁ : Nat.Prime p)
  -- (hq : q ≠ 0)
  -- (hr : r ≠ 0)
  -- (hqr : |↑(natAbs q)| * |r| = ↑p)
  -- (h_2 : q = -↑(natAbs q))
  (h₂ : |(↑(natAbs q):ℤ)| ∣ ↑p) :
  natAbs q = 1 ∨ natAbs q = p := by
  have h₃: (↑(q.natAbs):ℕ) ∣ p := by
    norm_cast at *
  exact Nat.Prime.eq_one_or_self_of_dvd h₁ (↑(q.natAbs):ℕ) h₃


lemma imo_1992_p1_7_12
  (q : ℤ)
  -- (r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  -- (h₁ : Nat.Prime p)
  -- (hq : q ≠ 0)
  -- (hr : r ≠ 0)
  -- (hqr : |↑(natAbs q)| * |r| = ↑p)
  -- (h_2 : q = -↑(natAbs q))
  -- (h₂ : |(↑(natAbs q):ℤ)| ∣ ↑p)
  -- (h₃ : natAbs q ∣ p)
  (h₄₁ : natAbs q = p) :
  |q| = ↑p := by
  have h₅: abs q = q.natAbs := by exact abs_eq_natAbs q
  rw [h₅]
  norm_cast


lemma imo_1992_p1_7_13
  (q r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  -- (h₁ : Nat.Prime p)
  (hq : q ≠ 0)
  (hr : r ≠ 0)
  -- (hqr : |q| * |r| = ↑p)
  (h_abs : |(↑(natAbs q):ℤ)| = 1 ∨ |q| = ↑p) :
  q = -1 ∨ q = 1 ∨ q = -↑p ∨ q = ↑p := by
  cases' h_abs with hq_abs hq_abs
  . norm_cast at *
    have h₄: q = ↑(q.natAbs) ∨ q = -↑(q.natAbs) := by
      exact Int.natAbs_eq q
    rw [hq_abs] at h₄
    norm_cast at h₄
    cases' h₄ with h₄₀ h₄₁
    . right
      left
      exact h₄₀
    . left
      exact h₄₁
  . right
    right
    have h₂: abs q = q.natAbs := by exact abs_eq_natAbs q
    rw [h₂] at hq_abs
    norm_cast at hq_abs
    refine or_comm.mp ?_
    refine (Int.natAbs_eq_natAbs_iff).mp ?_
    norm_cast


lemma imo_1992_p1_7_14
  (q r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  -- (h₁ : Nat.Prime p)
  (hq : q ≠ 0)
  (hr : r ≠ 0)
  -- (hqr : |q| * |r| = ↑p)
  (hq_abs : |(↑(natAbs q):ℤ)| = 1) :
  q = -1 ∨ q = 1 ∨ q = -↑p ∨ q = ↑p := by
  norm_cast at *
  have h₄: q = ↑(q.natAbs) ∨ q = -↑(q.natAbs) := by
    exact Int.natAbs_eq q
  rw [hq_abs] at h₄
  norm_cast at h₄
  cases' h₄ with h₄₀ h₄₁
  . right
    left
    exact h₄₀
  . left
    exact h₄₁


lemma imo_1992_p1_7_15
  (q r : ℤ)
  -- (p : ℕ)
  (hrq: r = q) :
  -- (h₀ : q * r = ↑p)
  -- (h₁ : Nat.Prime p)
  -- (hqr : |q| * |r| = ↑p)
  -- (hq : ¬q = 0)
  -- (hr : ¬r = 0)
  -- (hq_abs : natAbs q = 1) :
  r = ↑(natAbs q) ∨ r = -↑(natAbs q) := by
  rw [← hrq]
  exact Int.natAbs_eq r


lemma imo_1992_p1_7_16
  (q : ℤ)
  -- (r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  -- (h₁ : Nat.Prime p)
  -- (hq : q ≠ 0)
  -- (hr : r ≠ 0)
  -- (hqr : |q| * |r| = ↑p)
  (hq_abs : |q| = ↑p) :
  q = -1 ∨ q = 1 ∨ q = -↑p ∨ q = ↑p := by
  right
  right
  have h₂: abs q = q.natAbs := by exact abs_eq_natAbs q
  rw [h₂] at hq_abs
  norm_cast at hq_abs
  refine or_comm.mp ?_
  refine (Int.natAbs_eq_natAbs_iff).mp ?_
  norm_cast


lemma imo_1992_p1_7_17
  (q : ℤ)
  -- (r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  -- (h₁ : Nat.Prime p)
  -- (hq : q ≠ 0)
  -- (hr : r ≠ 0)
  -- (hqr : |q| * |r| = ↑p)
  (hq_abs : |q| = ↑p) :
  q = -↑p ∨ q = ↑p := by
  have h₂: abs q = q.natAbs := by exact abs_eq_natAbs q
  rw [h₂] at hq_abs
  norm_cast at hq_abs
  refine or_comm.mp ?_
  refine (Int.natAbs_eq_natAbs_iff).mp ?_
  norm_cast


lemma imo_1992_p1_7_18
  (q : ℤ)
  -- (r : ℤ)
  (p : ℕ)
  -- (h₀ : q * r = ↑p)
  -- (h₁ : Nat.Prime p)
  -- (hq : q ≠ 0)
  -- (hr : r ≠ 0)
  -- (hqr : |q| * |r| = ↑p)
  -- (h₂ : |q| = ↑(natAbs q))
  (hq_abs : natAbs q = p) :
  q = -↑p ∨ q = ↑p := by
  refine or_comm.mp ?_
  refine (Int.natAbs_eq_natAbs_iff).mp ?_
  norm_cast



-- my_case_k_2
lemma imo_1992_p1_8
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
    have g₂: (4-q)*(4-r) = 11 := by linarith
    have g₃: (4-q) = -1 ∨ (4-q) = 1 ∨ (4-q) = -11 ∨ (4-q) = 11 := by
      refine imo_1992_p1_7 (4-q) (4-r) 11 g₂ ?_
      decide
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


lemma imo_1992_p1_8_1
  (p q r : ℤ)
  (h₀ : 1 < p ∧ p < q ∧ q < r)
  (hpl : p = 2)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * 2) :
  False := by
  rw [hpl] at *
  norm_num at *
  have g₁: 2 * q + 2 * r = 3 := by
    linarith
  linarith [g₁,hql,hrl]


lemma imo_1992_p1_8_2
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 s≤ q)
  (hrl : 4 ≤ r)
  (h₀ : 1 < 3 ∧ 3 < q ∧ q < r)
  -- (hpl : 2 ≤ 3)
  -- (hpu : 3 < 4)
  (hk : 3 * q * r - 1 = (3 - 1) * (q - 1) * (r - 1) * 2) :
  (3, q, r) = (3, 5, 15) := by
  norm_num at *
  have g₂: (4-q)*(4-r) = 11 := by linarith
  have g₃: (4-q) = -1 ∨ (4-q) = 1 ∨ (4-q) = -11 ∨ (4-q) = 11 := by
    refine imo_1992_p1_7 (4-q) (4-r) 11 g₂ ?_
    decide
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
      . linarith


lemma imo_1992_p1_8_3
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  -- (h₀ : 3 < q ∧ q < r)
  -- (hk : 3 * q * r - 1 = 2 * (q - 1) * (r - 1) * 2)
  -- g₁ : q * r - 4 * q - 4 * r + 5 = 0
  (g₂ : (4 - q) * (4 - r) = 11) :
  4 - q = -1 ∨ 4 - q = 1 ∨ 4 - q = -11 ∨ 4 - q = 11 := by
  refine imo_1992_p1_7 (4-q) (4-r) 11 g₂ ?_
  decide


lemma imo_1992_p1_8_4
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  -- (h₀ : 3 < q ∧ q < r)
  -- (hk : 3 * q * r - 1 = 2 * (q - 1) * (r - 1) * 2)
  -- (g₁ : q * r - 4 * q - 4 * r + 5 = 0)
  (g₂ : (4 - q) * (4 - r) = 11)
  (g₃₁ : 4 - q = -1) :
  q = 5 ∧ r = 15 := by
  have hq: q = 5 := by linarith
  constructor
  . exact hq
  . rw [hq] at g₂
    linarith[g₂]


lemma imo_1992_p1_8_5
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  (h₀ : 3 < q ∧ q < r)
  -- (hk : 3 * q * r - 1 = 2 * (q - 1) * (r - 1) * 2)
  -- (g₁ : q * r - 4 * q - 4 * r + 5 = 0)
  (g₂ : (4 - q) * (4 - r) = 11)
  (g₃₂ : 4 - q = 1 ∨ 4 - q = -11 ∨ 4 - q = 11) :
  False := by
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
    . linarith


lemma imo_1992_p1_8_6
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  (h₀ : 3 < q ∧ q < r)
  -- (hk : 3 * q * r - 1 = 2 * (q - 1) * (r - 1) * 2)
  -- (g₁ : q * r - 4 * q - 4 * r + 5 = 0)
  (g₂ : (4 - q) * (4 - r) = 11)
  (g₃₂ : 4 - q = 1) :
  False := by
  have hq: q = 3 := by linarith[g₃₂]
  rw [hq] at g₂
  have hr: r = -7 := by linarith[g₂]
  linarith[hrl,hr]


lemma imo_1992_p1_8_7
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  (h₀ : 3 < q ∧ q < r)
  -- (hk : 3 * q * r - 1 = 2 * (q - 1) * (r - 1) * 2)
  -- (g₁ : q * r - 4 * q - 4 * r + 5 = 0)
  (g₂ : (4 - q) * (4 - r) = 11)
  (g₃₃ : 4 - q = -11) :
  False := by
  have hq: q = 15 := by linarith[g₃₃]
  rw [hq] at g₂
  have hr: r = 5 := by linarith[g₂]
  linarith[hq,hr,h₀.2]


lemma imo_1992_p1_8_8
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  (h₀ : q < r)
  (h₁ : 6 < -r)
  -- (hk : 3 * q * r - 1 = 2 * (q - 1) * (r - 1) * 2)
  -- (g₁ : q * r - 4 * q - 4 * r + 5 = 0)
  -- (g₂ : (4 - q) * (4 - r) = 11)
  (g₃₄ : 4 - q = 11) :
  False := by
  have h₂: q = -7 := by
    exact (Int.sub_right_inj 4).mp g₃₄
  have h₃: -6 ≤ r := by
    rw [h₂] at h₀
    exact h₀
  apply neg_le_neg at h₃
  exact Lean.Omega.Int.le_lt_asymm h₃ h₁


lemma imo_1992_p1_9
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
    have g₂: (q - 3) * (r - 3) = 5 := by linarith
    have g₃: (q - 3) = -1 ∨ (q - 3) = 1 ∨ (q - 3) = -5 ∨ (q - 3) = 5 := by
      refine imo_1992_p1_7 (q - 3) (r - 3) 5 g₂ ?_
      decide
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
  . right
    norm_num at *
    have g₂: (6 - 3*q) * (2 - r) = 5 := by linarith
    have g₃: (6 - 3*q) = -1 ∨ (6 - 3*q) = 1 ∨ (6 - 3*q) = -5 ∨ (6 - 3*q) = 5 := by
      refine imo_1992_p1_7 (6 - 3*q) (2 - r) 5 g₂ ?_
      decide
    exfalso
    cases' g₃ with g₃₁ g₃₂
    . linarith[g₃₁,q]
    . cases' g₃₂ with g₃₂ g₃₃
      . linarith[g₃₂,q]
      . cases' g₃₃ with g₃₃ g₃₄
        . linarith[g₃₃,q]
        . linarith[g₃₄,q]



lemma imo_1992_p1_9_1
  (q r : ℤ)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  (h₀ : 2 < q ∧ q < r)
  (hk : 2 * q * r - 1 = (q - 1) * (r - 1) * 3) :
  q = 4 ∧ r = 8 := by
  have g₂: (q - 3) * (r - 3) = 5 := by linarith
  have g₃: (q - 3) = -1 ∨ (q - 3) = 1 ∨ (q - 3) = -5 ∨ (q - 3) = 5 := by
    refine imo_1992_p1_7 (q - 3) (r - 3) 5 g₂ ?_
    decide
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



lemma imo_1992_p1_9_2
  (q r : ℤ)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  (h₀ : 2 < q ∧ q < r)
  (g₂ : (q - 3) * (r - 3) = 5) :
  q = 4 ∧ r = 8 := by
  have g₃: (q - 3) = -1 ∨ (q - 3) = 1 ∨ (q - 3) = -5 ∨ (q - 3) = 5 := by
    refine imo_1992_p1_7 (q - 3) (r - 3) 5 g₂ ?_
    decide
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


lemma imo_1992_p1_9_3
  (q r : ℤ)
  (g₂ : (q - 3) * (r - 3) = 5) :
  q - 3 = -1 ∨ q - 3 = 1 ∨ q - 3 = -5 ∨ q - 3 = 5 := by
  refine imo_1992_p1_7 (q - 3) (r - 3) 5 g₂ ?_
  decide


lemma imo_1992_p1_9_4
  -- (p : ℤ)
  (q r : ℤ)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  (h₀ : 2 < q ∧ q < r)
  -- (hk : 2 * q * r - 1 = (q - 1) * (r - 1) * 3)
  -- (g₁ : q * r - 3 * q - 3 * r + 4 = 0)
  (g₂ : (q - 3) * (r - 3) = 5)
  (g₃ : q - 3 = -1 ∨ q - 3 = 1 ∨ q - 3 = -5 ∨ q - 3 = 5) :
  q = 4 ∧ r = 8 := by
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


lemma imo_1992_p1_9_5
  -- (p : ℤ)
  (q r : ℤ)
  (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  -- (h₀ : 2 < q ∧ q < r)
  -- (hk : 2 * q * r - 1 = (q - 1) * (r - 1) * 3)
  -- (g₁ : q * r - 3 * q - 3 * r + 4 = 0)
  -- (g₂ : (q - 3) * (r - 3) = 5)
  (g₃₁ : q - 3 = -1) :
  q = 4 ∧ r = 8 := by
  exfalso
  linarith [hql,g₃₁]


lemma imo_1992_p1_9_6
  -- (p r : ℤ)
  (q r : ℤ)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  -- (h₀ : 2 < q ∧ q < r)
  -- (hk : 2 * q * r - 1 = (q - 1) * (r - 1) * 3)
  -- (g₁ : q * r - 3 * q - 3 * r + 4 = 0)
  -- (g₂ : (q - 3) * (r - 3) = 5)
  (g₃₁ : r * (q - 4) < r * (3 - r)) :
  False := by
  have h₀: 3 - r ≤ q - 4 := by
    exact sub_le_sub hql hrl
  have h₀: r * (3 - r) ≤ r * (q - 4) := by
    refine (mul_le_mul_left ?_).mpr h₀
    linarith
  linarith


lemma imo_1992_p1_9_7
  -- (p : ℤ)
  (q r : ℤ)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  (h₀ : 2 < q ∧ q < r)
  -- (hk : 2 * q * r - 1 = (q - 1) * (r - 1) * 3)
  -- (g₁ : q * r - 3 * q - 3 * r + 4 = 0)
  (g₂ : (q - 3) * (r - 3) = 5)
  (g₃₂ : q - 3 = 1 ∨ q - 3 = -5 ∨ q - 3 = 5) :
  q = 4 ∧ r = 8 := by
  cases' g₃₂ with g₃₂ g₃₃
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


lemma imo_1992_p1_9_8
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  -- (h₀ : 2 < q ∧ q < r)
  -- (hk : 2 * q * r - 1 = (q - 1) * (r - 1) * 3)
  -- (g₁ : q * r - 3 * q - 3 * r + 4 = 0)
  (g₂ : (q - 3) * (r - 3) = 5)
  (g₃₂ : q - 3 = 1) :
  q = 4 ∧ r = 8 := by
  have hq: q = 4 := by linarith
  rw [hq] at g₂
  have hr: r = 8 := by linarith[g₂]
  exact { left := hq, right := hr }


lemma imo_1992_p1_9_9
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  -- (h₀ : 2 < q ∧ q < r)
  -- (hk : 2 * q * r - 1 = (q - 1) * (r - 1) * 3)
  -- (g₁ : q * r - 3 * q - 3 * r + 4 = 0)
  (g₂ : (q - 3) * (r - 3) = 5)
  (g₃₂ : q - 3 = 1)
  (hq : q = 4) :
  q = 4 ∧ r = 8 := by
  rw [hq] at g₂
  have hr: r = 8 := by linarith[g₂]
  exact { left := hq, right := hr }


lemma imo_1992_p1_9_10
  -- (p : ℤ)
  (q r : ℤ)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  (h₀ : 2 < q ∧ q < r)
  -- (hk : 2 * q * r - 1 = (q - 1) * (r - 1) * 3)
  -- (g₁ : q * r - 3 * q - 3 * r + 4 = 0)
  (g₂ : (q - 3) * (r - 3) = 5)
  (g₃₃ : q - 3 = -5 ∨ q - 3 = 5) :
  False := by
  cases' g₃₃ with g₃₃ g₃₄
  . linarith[hql,g₃₃]
  . have hq: q = 8 := by linarith
    rw [hq] at g₂
    norm_num at g₂
    have hr: r = 4 := by linarith
    linarith[hrl,hr]


lemma imo_1992_p1_9_11
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  (h₀ : 2 < q ∧ q < r)
  -- (hk : 2 * q * r - 1 = (q - 1) * (r - 1) * 3)
  -- (g₁ : q * r - 3 * q - 3 * r + 4 = 0)
  (g₂ : (q - 3) * (r - 3) = 5)
  (g₃₄ : q - 3 = 5) :
  False := by
  have hq: q = 8 := by linarith
  rw [hq] at g₂
  norm_num at g₂
  have hr: r = 4 := by linarith
  linarith[hrl,hr]


lemma imo_1992_p1_9_12
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  (h₀ : 3 < q ∧ q < r)
  (hk : 3 * q * r - 1 = 2 * (q - 1) * (r - 1) * 3) :
  q = 5 ∧ r = 15 := by
  have g₂: (6 - 3*q) * (2 - r) = 5 := by linarith
  have g₃: (6 - 3*q) = -1 ∨ (6 - 3*q) = 1 ∨ (6 - 3*q) = -5 ∨ (6 - 3*q) = 5 := by
    refine imo_1992_p1_7 (6 - 3*q) (2 - r) 5 g₂ ?_
    decide
  exfalso
  cases' g₃ with g₃₁ g₃₂
  . linarith[g₃₁,q]
  . cases' g₃₂ with g₃₂ g₃₃
    . linarith[g₃₂,q]
    . cases' g₃₃ with g₃₃ g₃₄
      . linarith[g₃₃,q]
      . linarith[g₃₄,q]


lemma imo_1992_p1_9_13
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  (h₀ : 3 < q ∧ q < r)
  -- (hk : 3 * q * r - 1 = 2 * (q - 1) * (r - 1) * 3)
  -- (g₁ : 3 * q * r - 6 * q - 6 * r + 7 = 0)
  (g₂ : (6 - 3 * q) * (2 - r) = 5) :
  False := by
  have g₃: (6 - 3*q) = -1 ∨ (6 - 3*q) = 1 ∨ (6 - 3*q) = -5 ∨ (6 - 3*q) = 5 := by
    refine imo_1992_p1_7 (6 - 3*q) (2 - r) 5 g₂ ?_
    decide
  exfalso
  cases' g₃ with g₃₁ g₃₂
  . linarith[g₃₁,q]
  . cases' g₃₂ with g₃₂ g₃₃
    . linarith[g₃₂,q]
    . cases' g₃₃ with g₃₃ g₃₄
      . linarith[g₃₃,q]
      . linarith[g₃₄,q]


lemma imo_1992_p1_9_14
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  -- (h₀ : 3 < q ∧ q < r)
  -- (hk : 3 * q * r - 1 = 2 * (q - 1) * (r - 1) * 3)
  -- (g₁ : 3 * q * r - 6 * q - 6 * r + 7 = 0)
  (g₂ : (6 - 3 * q) * (2 - r) = 5) :
  6 - 3 * q = -1 ∨ 6 - 3 * q = 1 ∨ 6 - 3 * q = -5 ∨ 6 - 3 * q = 5 := by
  refine imo_1992_p1_7 (6 - 3*q) (2 - r) 5 g₂ ?_
  decide

lemma imo_1992_p1_9_15
  -- (p : ℤ)
  (q r : ℤ)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  (h₀ : 3 < q ∧ q < r)
  -- (hk : 3 * q * r - 1 = 2 * (q - 1) * (r - 1) * 3)
  -- (g₁ : 3 * q * r - 6 * q - 6 * r + 7 = 0)
  -- (g₂ : (6 - 3 * q) * (2 - r) = 5)
  (g₃ : 6 - 3 * q = -1 ∨ 6 - 3 * q = 1 ∨ 6 - 3 * q = -5 ∨ 6 - 3 * q = 5) :
  False := by
  exfalso
  cases' g₃ with g₃₁ g₃₂
  . linarith[g₃₁,q]
  . cases' g₃₂ with g₃₂ g₃₃
    . linarith[g₃₂,q]
    . cases' g₃₃ with g₃₃ g₃₄
      . linarith[g₃₃,q]
      . linarith[g₃₄,q]


lemma q_of_qr_eq_11_nat
  (q r : ℕ)
  (h₀ : q * r = 11) :
  q = 1 ∨ q = 11 := by
  have h₁: Nat.Prime (11:ℕ) := by decide
  have h₂: ↑q ∣ 11 := by
    exact Dvd.intro r h₀
  exact Nat.Prime.eq_one_or_self_of_dvd h₁ q h₂


lemma abs_q_r_product
  (q r : ℤ)
  (h₀ : q * r = 11) :
  q.natAbs * r.natAbs = (11:ℕ)  := by
  exact Int.natAbs_mul_natAbs_eq h₀
  -- Since q * r = 11, taking the absolute value of both sides gives |q * r| = 11.
  -- By properties of absolute values, |q * r| = |q| * |r|.


lemma myprime5 : Nat.Prime 5 := by
  rw [Nat.prime_def_lt']
  constructor
  . norm_num
  . intros m hm mu
    interval_cases m
    all_goals {try norm_num }



lemma abs_q_r_product_2
  (q r : ℤ)
  (h₀ : q * r = (11:ℕ)) :
  abs q * abs r = 11 := by
  have h₁: q.natAbs * r.natAbs = (11:ℕ) := by
    exact Int.natAbs_mul_natAbs_eq h₀
  have h₃: abs q = q.natAbs := by exact abs_eq_natAbs q
  have h₄: abs r = r.natAbs := by exact abs_eq_natAbs r
  rw [h₃,h₄]
  norm_cast


lemma imo_1992_p1_19_1
  (p q r : ℤ)
  -- (h₀ : 1 < p ∧ p < q ∧ q < r)
  (k : ℤ)
  (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  -- (hpl : 2 ≤ p)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  (hden : 0 < (p - 1) * (q - 1) * (r - 1)) :
  ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
  have g₁: ↑(p * q * r - 1) = ↑k * (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
    norm_cast
    linarith
  symm
  have g₂: (↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≠ 0 := by
    norm_cast
    linarith[hden]
  exact (div_eq_iff g₂).mpr g₁


lemma imo_1992_p1_19_2
  (p q r : ℤ)
  -- (h₀ : 1 < p ∧ p < q ∧ q < r)
  (k : ℤ)
  -- (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  -- (hpl : 2 ≤ p)
  -- (hql : 3 ≤ q)
  -- (hrl : 4 ≤ r)
  (hden : 0 < (p - 1) * (q - 1) * (r - 1))
  (g₁ : ↑(p * q * r - 1) = ↑k * (↑((p - 1) * (q - 1) * (r - 1)):ℚ)) :
  ↑k = (↑(p * q * r - 1):ℚ) / (↑((p - 1) * (q - 1) * (r - 1)):ℚ) := by
  symm
  have g₂: (↑((p - 1) * (q - 1) * (r - 1)):ℚ) ≠ 0 := by
    norm_cast
    linarith[hden]
  exact (div_eq_iff g₂).mpr g₁


lemma imo_1992_p1_19_3
  (p q r : ℤ)
  (h₀ : 1 < p ∧ p < q ∧ q < r)
  (k : ℤ)
  (hk : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) * k)
  (hpl : 2 ≤ p)
  (hql : 3 ≤ q)
  (hrl : 4 ≤ r)
  -- (hden : 0 < (p - 1) * (q - 1) * (r - 1))
  (h₁ : ↑k = ↑(p * q * r - 1) / ↑((p - 1) * (q - 1) * (r - 1)))
  (hk4 : k < 4)
  (hk1 : 1 < k)
  (hpu : p < 4) :
  (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  interval_cases k
  . exact imo_1992_p1_8 p q r h₀ hpl hql hrl hpu hk
  . exact imo_1992_p1_9 p q r h₀ hpl hql hrl hpu hk
