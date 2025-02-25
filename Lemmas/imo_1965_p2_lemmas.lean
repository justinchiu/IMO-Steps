import Mathlib
set_option linter.unusedVariables.analyzeTactics true

open Real



lemma imo_1965_p2_1
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  (hx0 : x = 0) :
  x = 0 ∧ y = 0 ∧ z = 0 := by
  constructor
  . exact hx0
  . rw [hx0] at h₇ h₈ h₉
    simp at h₇ h₈ h₉
    by_cases hy0: y = 0
    . constructor
      . exact hy0
      . rw [hy0] at h₇
        simp at h₇
        . cases' h₇ with h₇₀ h₇₁
          . exfalso
            linarith
          . exact h₇₁
    . by_cases hyn: y < 0
      . have g1: 0 < a 1 * y := by exact mul_pos_of_neg_of_neg h₁.1 hyn
        have g2: a 1 * y = -a 2 * z := by linarith
        rw [g2] at g1
        have g3: a 2 *z < 0 := by linarith
        have hzp: 0 < z := by exact pos_of_mul_neg_right g3 (le_of_lt h₁.2)
        exfalso
        have g4: a 4 * y < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 hyn
        have g5: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzp
        linarith
      . push_neg at hy0 hyn
        have hyp: 0 < y := by exact lt_of_le_of_ne hyn hy0.symm
        exfalso
        have g1: a 1 * y < 0 := by exact mul_neg_of_neg_of_pos h₁.1 hyp
        have g2: 0 < z * a 2 := by linarith
        have hzp: z < 0 := by exact neg_of_mul_pos_left g2 (le_of_lt h₁.2)
        have g3: 0 < a 4 * y := by exact mul_pos h₀.2.1 hyp
        have g4: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzp
        linarith


lemma imo_1965_p2_2
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  (hx0 : x = 0) :
  y = 0 ∧ z = 0 := by
  rw [hx0] at h₇ h₈ h₉
  by_cases hy0: y = 0
  . constructor
    . exact hy0
    . rw [hy0] at h₇
      simp at h₇
      . cases' h₇ with h₇₀ h₇₁
        . exfalso
          linarith
        . exact h₇₁
  . by_cases hyn: y < 0
    . have g1: 0 < a 1 * y := by exact mul_pos_of_neg_of_neg h₁.1 hyn
      have g2: a 1 * y = -a 2 * z := by linarith
      rw [g2] at g1
      have g3: a 2 *z < 0 := by linarith
      have hzp: 0 < z := by exact pos_of_mul_neg_right g3 (le_of_lt h₁.2)
      exfalso
      have g4: a 4 * y < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 hyn
      have g5: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzp
      linarith
    . push_neg at hy0 hyn
      have hyp: 0 < y := by exact lt_of_le_of_ne hyn hy0.symm
      exfalso
      have g1: a 1 * y < 0 := by exact mul_neg_of_neg_of_pos h₁.1 hyp
      have g2: 0 < z * a 2 := by linarith
      have hzp: z < 0 := by exact neg_of_mul_pos_left g2 (le_of_lt h₁.2)
      have g3: 0 < a 4 * y := by exact mul_pos h₀.2.1 hyp
      have g4: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzp
      linarith


lemma imo_1965_p2_3
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  (hx0: x = 0)
  (hy0 : y = 0) :
  y = 0 ∧ z = 0 := by
  rw [hx0] at h₇ h₈ h₉
  constructor
  . exact hy0
  . rw [hy0] at h₇
    simp at h₇
    . cases' h₇ with h₇₀ h₇₁
      . exfalso
        linarith
      . exact h₇₁


lemma imo_1965_p2_4
  -- (x : ℝ)
  (y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x = 0)
  (h₇ : a 1 * y + a 2 * z = 0)
  (h₈ : a 4 * y + a 5 * z = 0)
  (h₉ : a 7 * y + a 8 * z = 0)
  (hy0 : y = 0) :
  z = 0 := by
  rw [hy0] at h₇
  simp at h₇
  . cases' h₇ with h₇₀ h₇₁
    . exfalso
      linarith
    . exact h₇₁


lemma imo_1965_p2_5
  -- (x : ℝ)
  (y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x = 0)
  (h₇ : a 1 * y + a 2 * z = 0)
  (h₈ : a 4 * y + a 5 * z = 0)
  -- (h₉ : a 7 * y + a 8 * z = 0)
  -- (hy0 : ¬y = 0)
  (hyn : y < 0) :
  y = 0 ∧ z = 0 := by
  have g1: 0 < a 1 * y := by exact mul_pos_of_neg_of_neg h₁.1 hyn
  have g2: a 1 * y = -a 2 * z := by linarith
  rw [g2] at g1
  have g3: a 2 *z < 0 := by linarith
  have hzp: 0 < z := by exact pos_of_mul_neg_right g3 (le_of_lt h₁.2)
  exfalso
  have g4: a 4 * y < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 hyn
  have g5: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzp
  linarith


lemma imo_1965_p2_6
  -- (x : ℝ)
  (y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x = 0)
  (h₇ : a 1 * y + a 2 * z = 0)
  (h₈ : a 4 * y + a 5 * z = 0)
  -- (h₉ : a 7 * y + a 8 * z = 0)
  -- (hy0 : ¬y = 0)
  (hyn : y < 0) :
  False := by
  have g1: 0 < a 1 * y := by exact mul_pos_of_neg_of_neg h₁.1 hyn
  have g2: a 1 * y = -a 2 * z := by linarith
  rw [g2] at g1
  have g3: a 2 *z < 0 := by linarith
  have hzp: 0 < z := by exact pos_of_mul_neg_right g3 (le_of_lt h₁.2)
  have g4: a 4 * y < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 hyn
  have g5: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzp
  linarith


lemma imo_1965_p2_7
  -- (x : ℝ)
  (y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x = 0)
  -- (h₇ : a 1 * y + a 2 * z = 0)
  (h₈ : a 4 * y + a 5 * z = 0)
  -- (h₉ : a 7 * y + a 8 * z = 0)
  -- (hy0 : ¬y = 0)
  (hyn : y < 0)
  -- (g1 : 0 < -a 2 * z)
  -- (g2 : a 1 * y = -a 2 * z)
  -- (g3 : a 2 * z < 0)
  (hzp : 0 < z) :
  False := by
  have g4: a 4 * y < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 hyn
  have g5: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzp
  linarith


lemma imo_1965_p2_8
  -- (x : ℝ)
  (y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x = 0)
  (h₇ : a 1 * y + a 2 * z = 0)
  (h₈ : a 4 * y + a 5 * z = 0)
  -- (h₉ : a 7 * y + a 8 * z = 0)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y) :
  y = 0 ∧ z = 0 := by
  exfalso
  have g1: a 1 * y < 0 := by exact mul_neg_of_neg_of_pos h₁.1 hyp
  have g2: 0 < z * a 2 := by linarith
  have hzp: z < 0 := by exact neg_of_mul_pos_left g2 (le_of_lt h₁.2)
  have g3: 0 < a 4 * y := by exact mul_pos h₀.2.1 hyp
  have g4: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzp
  linarith


lemma imo_1965_p2_9
  -- (x : ℝ)
  (y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x = 0)
  (h₇ : a 1 * y + a 2 * z = 0)
  (h₈ : a 4 * y + a 5 * z = 0)
  -- (h₉ : a 7 * y + a 8 * z = 0)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y) :
  False := by
  have g1: a 1 * y < 0 := by exact mul_neg_of_neg_of_pos h₁.1 hyp
  have g2: 0 < z * a 2 := by linarith
  have hzp: z < 0 := by exact neg_of_mul_pos_left g2 (le_of_lt h₁.2)
  have g3: 0 < a 4 * y := by exact mul_pos h₀.2.1 hyp
  have g4: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzp
  linarith


lemma imo_1965_p2_10
  -- (x : ℝ)
  (y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x = 0)
  -- (h₇ : a 1 * y + a 2 * z = 0)
  (h₈ : a 4 * y + a 5 * z = 0)
  -- (h₉ : a 7 * y + a 8 * z = 0)
  -- (hy0 : y ≠ 0)
  -- (hyn : 0 ≤ y)
  (hyp : 0 < y)
  -- (g1 : a 1 * y < 0)
  (g2 : 0 < z * a 2) :
  False := by
  have hzp: z < 0 := by exact neg_of_mul_pos_left g2 (le_of_lt h₁.2)
  have g3: 0 < a 4 * y := by exact mul_pos h₀.2.1 hyp
  have g4: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzp
  linarith


lemma imo_1965_p2_11
  -- (x : ℝ)
  (y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x = 0)
  -- (h₇ : a 1 * y + a 2 * z = 0)
  (h₈ : a 4 * y + a 5 * z = 0)
  -- (h₉ : a 7 * y + a 8 * z = 0)
  -- (hy0 : y ≠ 0)
  -- (hyn : 0 ≤ y)
  (hyp : 0 < y)
  -- (g1 : a 1 * y < 0)
  -- (g2 : 0 < z * a 2)
  (hzp : z < 0) :
  False := by
  have g3: 0 < a 4 * y := by exact mul_pos h₀.2.1 hyp
  have g4: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzp
  linarith


lemma imo_1965_p2_12
  -- (x : ℝ)
  (y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x = 0)
  -- (h₇ : a 1 * y + a 2 * z = 0)
  (h₈ : a 4 * y + a 5 * z = 0)
  -- (h₉ : a 7 * y + a 8 * z = 0)
  -- (hy0 : y ≠ 0)
  -- (hyn : 0 ≤ y)
  -- (hyp : 0 < y)
  -- (g1 : a 1 * y < 0)
  -- (g2 : 0 < z * a 2)
  (hzp : z < 0)
  (g3 : 0 < a 4 * y) :
  False := by
  have g4: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzp
  linarith


lemma imo_1965_p2_13
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  (hx0 : ¬x = 0) :
  x = 0 ∧ y = 0 ∧ z = 0 := by
  exfalso
  push_neg at hx0
  by_cases hxp: 0 < x
  . by_cases hy0: y = 0
    . rw [hy0] at h₇ h₈ h₉
      simp at h₇ h₈ h₉
      have g1: 0 < a 0 * x := by exact mul_pos h₀.1 hxp
      have g2: a 2 * z < 0 := by linarith
      have hzn: 0 < z := by exact pos_of_mul_neg_right g2 (le_of_lt h₁.2)
      have g3: a 3 * x < 0 := by exact mul_neg_of_neg_of_pos h₂.1 hxp
      have g4: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzn
      linarith
    . push_neg at hy0
      by_cases hyp: 0 < y
      . have g1: a 6 * x < 0 := by exact mul_neg_of_neg_of_pos h₃.1 hxp
        have g2: a 7 * y < 0 := by exact mul_neg_of_neg_of_pos h₃.2 hyp
        have g3: 0 < z * a 8 := by linarith
        have hzp: 0 < z := by exact pos_of_mul_pos_left g3 (le_of_lt h₀.2.2)
        ------ here we consider all the possible relationships between x, y, z
        by_cases rxy: x ≤ y
        . by_cases ryz: y ≤ z
            -- x <= y <= z
          . have g2: 0 < (a 6 + a 7 + a 8) * y := by exact mul_pos h₆ hyp
            have g3: 0 ≤ a 6 * (x-y) := by
              exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₃.1) (by linarith)
            have g4: 0 ≤ a 8 * (z-y) := by exact mul_nonneg (le_of_lt h₀.2.2) (by linarith)
            linarith
          push_neg at ryz
          by_cases rxz: x ≤ z
            -- x <= z < y
          . have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
            have g3: 0 ≤ a 3 * (x-y) := by
              exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
            have g4: 0 < a 5 * (z-y) := by
              exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
            linarith
          push_neg at rxz -- z < x <= y
          have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
          have g3: 0 ≤ a 3 * (x-y) := by
            exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
          have g4: 0 < a 5 * (z-y) := by
            exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
          linarith
        push_neg at rxy
        by_cases rzy: z ≤ y
          -- z <= y < x
        . have g2: 0 < (a 0 + a 1 + a 2) * y := by exact mul_pos h₄ hyp
          have g3: 0 < a 0 * (x-y) := by exact mul_pos h₀.1 (by linarith)
          have g4: 0 ≤ a 2 * (z-y) := by
            exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₁.2) (by linarith)
          linarith
        . push_neg at rzy
          by_cases rzx: z ≤ x
            -- y < z <= x
          . have g2: 0 < (a 0 + a 1 + a 2) * z := by exact mul_pos h₄ hzp
            have g3: 0 ≤ a 0 * (x-z) := by exact mul_nonneg (le_of_lt h₀.1) (by linarith)
            have g4: 0 < a 1 * (y-z) := by exact mul_pos_of_neg_of_neg h₁.1 (by linarith)
            linarith
          . push_neg at rzx
              -- y < x < z
            have g2: 0 < (a 6 + a 7 + a 8) * z := by exact mul_pos h₆ hzp
            have g3: 0 < a 6 * (x-z) := by exact mul_pos_of_neg_of_neg h₃.1 (by linarith)
            have g4: 0 < a 7 * (y-z) := by exact mul_pos_of_neg_of_neg h₃.2 (by linarith)
            linarith
      -------- new world where y < 0 and 0 < x
      . push_neg at hyp
        have hyn: y < 0 :=  by exact lt_of_le_of_ne hyp hy0
        -- show from a 0 that 0 < z
        have g1: 0 < a 0 * x := by exact mul_pos h₀.1 hxp
        have g2: 0 < a 1 * y := by exact mul_pos_of_neg_of_neg h₁.1 hyn
        have g3: a 2 * z < 0 := by linarith
        have hzp: 0 < z := by exact pos_of_mul_neg_right g3 (le_of_lt h₁.2)
        -- then show from a 3 that's not possible
        have g4: a 3 * x < 0 := by exact mul_neg_of_neg_of_pos h₂.1 hxp
        have g5: a 4 * y < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 hyn
        have g6: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzp
        linarith
  . push_neg at hxp
    have hxn: x < 0 := by exact lt_of_le_of_ne hxp hx0
    by_cases hyp: 0 ≤ y
    . have g1: a 0 * x < 0 := by exact mul_neg_of_pos_of_neg h₀.1 hxn
      have g2: a 1 * y ≤ 0 := by
        refine mul_nonpos_iff.mpr ?_
        right
        constructor
        . exact le_of_lt h₁.1
        . exact hyp
      have g3: 0 < z * a 2 := by linarith
      have hzn: z < 0 := by exact neg_of_mul_pos_left g3 (le_of_lt h₁.2)
      -- demonstrate the contradiction
      have g4: 0 < a 3 * x := by exact mul_pos_of_neg_of_neg h₂.1 hxn
      have g5: 0 ≤ a 4 * y := by exact mul_nonneg (le_of_lt h₀.2.1) hyp
      have g6: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzn
      linarith
    . push_neg at hyp
      -- have hyn: y < 0, {exact lt_of_le_of_ne hyp hy0,},
      have g1: 0 < a 6 * x := by exact mul_pos_of_neg_of_neg h₃.1 hxn
      have g2: 0 < a 7 * y := by exact mul_pos_of_neg_of_neg h₃.2 hyp
      have g3: z * a 8 < 0 := by linarith
      have hzp: z < 0 := by exact neg_of_mul_neg_left g3 (le_of_lt h₀.2.2)
        -- we have x,y,z < 0 -- we will examine all the orders they can have
      by_cases rxy: x ≤ y
      . by_cases ryz: y ≤ z
          -- x <= y <= z
        . have g2: (a 0 + a 1 + a 2) * y < 0 := by exact mul_neg_of_pos_of_neg h₄ hyp
          have g3: a 0 * (x-y) ≤ 0 := by
            exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
          have g4: a 2 * (z-y) ≤ 0 := by
            exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₁.2) (by linarith)
          linarith
        . push_neg at ryz
          by_cases rxz: x ≤ z
            -- x <= z < y
          . have g2: (a 0 + a 1 + a 2) * z < 0 := by exact mul_neg_of_pos_of_neg h₄ hzp
            have g3: a 0 * (x-z) ≤ 0 := by
              exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
            have g4: a 1 * (y-z) < 0 := by
              exact mul_neg_of_neg_of_pos h₁.1 (by linarith)
            linarith
          . push_neg at rxz -- z < x <= y
            have g2: (a 6 + a 7 + a 8) * z < 0 := by exact mul_neg_of_pos_of_neg h₆ hzp
            have g3: a 6 * (x-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
            have g4: a 7 * (y-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.2 (by linarith)
            linarith
      . push_neg at rxy
        by_cases rzy: z ≤ y
          -- z <= y < x
        . have g2: (a 6 + a 7 + a 8) * y < 0 := by exact mul_neg_of_pos_of_neg h₆ hyp
          have g3: a 6 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
          have g4: a 8 * (z-y) ≤ 0 := by
            exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.2.2) (by linarith)
          linarith
        . push_neg at rzy
          by_cases rzx: z ≤ x
            -- y < z <= x
          . have g2: (a 3 + a 4 + a 5) * z < 0 := by exact mul_neg_of_pos_of_neg h₅ hzp
            have g3: a 3 * (x-z) ≤ 0 := by
              exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₂.1) (by linarith)
            have g4: a 4 * (y-z) < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 (by linarith)
            linarith
          . push_neg at rzx
            -- y < x < z
            have g2: (a 3 + a 4 + a 5) * y < 0 := by exact mul_neg_of_pos_of_neg h₅ hyp
            have g3: a 3 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.1 (by linarith)
            have g4: a 5 * (z-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.2 (by linarith)
            linarith


lemma imo_1965_p2_14
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  (hx0 : x ≠ 0) :
  False := by
  by_cases hxp: 0 < x
  . by_cases hy0: y = 0
    . rw [hy0] at h₇ h₈ h₉
      simp at h₇ h₈ h₉
      have g1: 0 < a 0 * x := by exact mul_pos h₀.1 hxp
      have g2: a 2 * z < 0 := by linarith
      have hzn: 0 < z := by exact pos_of_mul_neg_right g2 (le_of_lt h₁.2)
      have g3: a 3 * x < 0 := by exact mul_neg_of_neg_of_pos h₂.1 hxp
      have g4: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzn
      linarith
    . push_neg at hy0
      by_cases hyp: 0 < y
      . have g1: a 6 * x < 0 := by exact mul_neg_of_neg_of_pos h₃.1 hxp
        have g2: a 7 * y < 0 := by exact mul_neg_of_neg_of_pos h₃.2 hyp
        have g3: 0 < z * a 8 := by linarith
        have hzp: 0 < z := by exact pos_of_mul_pos_left g3 (le_of_lt h₀.2.2)
        ------ here we consider all the possible relationships between x, y, z
        by_cases rxy: x ≤ y
        . by_cases ryz: y ≤ z
            -- x <= y <= z
          . have g2: 0 < (a 6 + a 7 + a 8) * y := by exact mul_pos h₆ hyp
            have g3: 0 ≤ a 6 * (x-y) := by
              exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₃.1) (by linarith)
            have g4: 0 ≤ a 8 * (z-y) := by exact mul_nonneg (le_of_lt h₀.2.2) (by linarith)
            linarith
          push_neg at ryz
          by_cases rxz: x ≤ z
            -- x <= z < y
          . have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
            have g3: 0 ≤ a 3 * (x-y) := by
              exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
            have g4: 0 < a 5 * (z-y) := by
              exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
            linarith
          push_neg at rxz -- z < x <= y
          have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
          have g3: 0 ≤ a 3 * (x-y) := by
            exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
          have g4: 0 < a 5 * (z-y) := by
            exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
          linarith
        push_neg at rxy
        by_cases rzy: z ≤ y
          -- z <= y < x
        . have g2: 0 < (a 0 + a 1 + a 2) * y := by exact mul_pos h₄ hyp
          have g3: 0 < a 0 * (x-y) := by exact mul_pos h₀.1 (by linarith)
          have g4: 0 ≤ a 2 * (z-y) := by
            exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₁.2) (by linarith)
          linarith
        . push_neg at rzy
          by_cases rzx: z ≤ x
            -- y < z <= x
          . have g2: 0 < (a 0 + a 1 + a 2) * z := by exact mul_pos h₄ hzp
            have g3: 0 ≤ a 0 * (x-z) := by exact mul_nonneg (le_of_lt h₀.1) (by linarith)
            have g4: 0 < a 1 * (y-z) := by exact mul_pos_of_neg_of_neg h₁.1 (by linarith)
            linarith
          . push_neg at rzx
              -- y < x < z
            have g2: 0 < (a 6 + a 7 + a 8) * z := by exact mul_pos h₆ hzp
            have g3: 0 < a 6 * (x-z) := by exact mul_pos_of_neg_of_neg h₃.1 (by linarith)
            have g4: 0 < a 7 * (y-z) := by exact mul_pos_of_neg_of_neg h₃.2 (by linarith)
            linarith
      -------- new world where y < 0 and 0 < x
      . push_neg at hyp
        have hyn: y < 0 :=  by exact lt_of_le_of_ne hyp hy0
        -- show from a 0 that 0 < z
        have g1: 0 < a 0 * x := by exact mul_pos h₀.1 hxp
        have g2: 0 < a 1 * y := by exact mul_pos_of_neg_of_neg h₁.1 hyn
        have g3: a 2 * z < 0 := by linarith
        have hzp: 0 < z := by exact pos_of_mul_neg_right g3 (le_of_lt h₁.2)
        -- then show from a 3 that's not possible
        have g4: a 3 * x < 0 := by exact mul_neg_of_neg_of_pos h₂.1 hxp
        have g5: a 4 * y < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 hyn
        have g6: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzp
        linarith
  . push_neg at hxp
    have hxn: x < 0 := by exact lt_of_le_of_ne hxp hx0
    by_cases hyp: 0 ≤ y
    . have g1: a 0 * x < 0 := by exact mul_neg_of_pos_of_neg h₀.1 hxn
      have g2: a 1 * y ≤ 0 := by
        refine mul_nonpos_iff.mpr ?_
        right
        constructor
        . exact le_of_lt h₁.1
        . exact hyp
      have g3: 0 < z * a 2 := by linarith
      have hzn: z < 0 := by exact neg_of_mul_pos_left g3 (le_of_lt h₁.2)
      -- demonstrate the contradiction
      have g4: 0 < a 3 * x := by exact mul_pos_of_neg_of_neg h₂.1 hxn
      have g5: 0 ≤ a 4 * y := by exact mul_nonneg (le_of_lt h₀.2.1) hyp
      have g6: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzn
      linarith
    . push_neg at hyp
      -- have hyn: y < 0, {exact lt_of_le_of_ne hyp hy0,},
      have g1: 0 < a 6 * x := by exact mul_pos_of_neg_of_neg h₃.1 hxn
      have g2: 0 < a 7 * y := by exact mul_pos_of_neg_of_neg h₃.2 hyp
      have g3: z * a 8 < 0 := by linarith
      have hzp: z < 0 := by exact neg_of_mul_neg_left g3 (le_of_lt h₀.2.2)
        -- we have x,y,z < 0 -- we will examine all the orders they can have
      by_cases rxy: x ≤ y
      . by_cases ryz: y ≤ z
          -- x <= y <= z
        . have g2: (a 0 + a 1 + a 2) * y < 0 := by exact mul_neg_of_pos_of_neg h₄ hyp
          have g3: a 0 * (x-y) ≤ 0 := by
            exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
          have g4: a 2 * (z-y) ≤ 0 := by
            exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₁.2) (by linarith)
          linarith
        . push_neg at ryz
          by_cases rxz: x ≤ z
            -- x <= z < y
          . have g2: (a 0 + a 1 + a 2) * z < 0 := by exact mul_neg_of_pos_of_neg h₄ hzp
            have g3: a 0 * (x-z) ≤ 0 := by
              exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
            have g4: a 1 * (y-z) < 0 := by
              exact mul_neg_of_neg_of_pos h₁.1 (by linarith)
            linarith
          . push_neg at rxz -- z < x <= y
            have g2: (a 6 + a 7 + a 8) * z < 0 := by exact mul_neg_of_pos_of_neg h₆ hzp
            have g3: a 6 * (x-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
            have g4: a 7 * (y-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.2 (by linarith)
            linarith
      . push_neg at rxy
        by_cases rzy: z ≤ y
          -- z <= y < x
        . have g2: (a 6 + a 7 + a 8) * y < 0 := by exact mul_neg_of_pos_of_neg h₆ hyp
          have g3: a 6 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
          have g4: a 8 * (z-y) ≤ 0 := by
            exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.2.2) (by linarith)
          linarith
        . push_neg at rzy
          by_cases rzx: z ≤ x
            -- y < z <= x
          . have g2: (a 3 + a 4 + a 5) * z < 0 := by exact mul_neg_of_pos_of_neg h₅ hzp
            have g3: a 3 * (x-z) ≤ 0 := by
              exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₂.1) (by linarith)
            have g4: a 4 * (y-z) < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 (by linarith)
            linarith
          . push_neg at rzx
            -- y < x < z
            have g2: (a 3 + a 4 + a 5) * y < 0 := by exact mul_neg_of_pos_of_neg h₅ hyp
            have g3: a 3 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.1 (by linarith)
            have g4: a 5 * (z-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.2 (by linarith)
            linarith


lemma imo_1965_p2_15
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  (hx0 : x ≠ 0)
  (hxp : 0 < x) :
  False := by
  by_cases hy0: y = 0
  . rw [hy0] at h₇ h₈ h₉
    simp at h₇ h₈ h₉
    have g1: 0 < a 0 * x := by exact mul_pos h₀.1 hxp
    have g2: a 2 * z < 0 := by linarith
    have hzn: 0 < z := by exact pos_of_mul_neg_right g2 (le_of_lt h₁.2)
    have g3: a 3 * x < 0 := by exact mul_neg_of_neg_of_pos h₂.1 hxp
    have g4: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzn
    linarith
  . push_neg at hy0
    by_cases hyp: 0 < y
    . have g1: a 6 * x < 0 := by exact mul_neg_of_neg_of_pos h₃.1 hxp
      have g2: a 7 * y < 0 := by exact mul_neg_of_neg_of_pos h₃.2 hyp
      have g3: 0 < z * a 8 := by linarith
      have hzp: 0 < z := by exact pos_of_mul_pos_left g3 (le_of_lt h₀.2.2)
      ------ here we consider all the possible relationships between x, y, z
      by_cases rxy: x ≤ y
      . by_cases ryz: y ≤ z
          -- x <= y <= z
        . have g2: 0 < (a 6 + a 7 + a 8) * y := by exact mul_pos h₆ hyp
          have g3: 0 ≤ a 6 * (x-y) := by
            exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₃.1) (by linarith)
          have g4: 0 ≤ a 8 * (z-y) := by exact mul_nonneg (le_of_lt h₀.2.2) (by linarith)
          linarith
        push_neg at ryz
        by_cases rxz: x ≤ z
          -- x <= z < y
        . have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
          have g3: 0 ≤ a 3 * (x-y) := by
            exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
          have g4: 0 < a 5 * (z-y) := by
            exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
          linarith
        push_neg at rxz -- z < x <= y
        have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
        have g3: 0 ≤ a 3 * (x-y) := by
          exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
        have g4: 0 < a 5 * (z-y) := by
          exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
        linarith
      push_neg at rxy
      by_cases rzy: z ≤ y
        -- z <= y < x
      . have g2: 0 < (a 0 + a 1 + a 2) * y := by exact mul_pos h₄ hyp
        have g3: 0 < a 0 * (x-y) := by exact mul_pos h₀.1 (by linarith)
        have g4: 0 ≤ a 2 * (z-y) := by
          exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₁.2) (by linarith)
        linarith
      . push_neg at rzy
        by_cases rzx: z ≤ x
          -- y < z <= x
        . have g2: 0 < (a 0 + a 1 + a 2) * z := by exact mul_pos h₄ hzp
          have g3: 0 ≤ a 0 * (x-z) := by exact mul_nonneg (le_of_lt h₀.1) (by linarith)
          have g4: 0 < a 1 * (y-z) := by exact mul_pos_of_neg_of_neg h₁.1 (by linarith)
          linarith
        . push_neg at rzx
            -- y < x < z
          have g2: 0 < (a 6 + a 7 + a 8) * z := by exact mul_pos h₆ hzp
          have g3: 0 < a 6 * (x-z) := by exact mul_pos_of_neg_of_neg h₃.1 (by linarith)
          have g4: 0 < a 7 * (y-z) := by exact mul_pos_of_neg_of_neg h₃.2 (by linarith)
          linarith
    -------- new world where y < 0 and 0 < x
    . push_neg at hyp
      have hyn: y < 0 :=  by exact lt_of_le_of_ne hyp hy0
      -- show from a 0 that 0 < z
      have g1: 0 < a 0 * x := by exact mul_pos h₀.1 hxp
      have g2: 0 < a 1 * y := by exact mul_pos_of_neg_of_neg h₁.1 hyn
      have g3: a 2 * z < 0 := by linarith
      have hzp: 0 < z := by exact pos_of_mul_neg_right g3 (le_of_lt h₁.2)
      -- then show from a 3 that's not possible
      have g4: a 3 * x < 0 := by exact mul_neg_of_neg_of_pos h₂.1 hxp
      have g5: a 4 * y < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 hyn
      have g6: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzp
      linarith


lemma imo_1965_p2_16
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  (hx0 : x ≠ 0)
  (hxp : 0 < x)
  (hy0 : y = 0) :
  False := by
  rw [hy0] at h₇ h₈ h₉
  simp at h₇ h₈ h₉
  have g1: 0 < a 0 * x := by exact mul_pos h₀.1 hxp
  have g2: a 2 * z < 0 := by linarith
  have hzn: 0 < z := by exact pos_of_mul_neg_right g2 (le_of_lt h₁.2)
  have g3: a 3 * x < 0 := by exact mul_neg_of_neg_of_pos h₂.1 hxp
  have g4: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzn
  linarith


lemma imo_1965_p2_17
  -- (y : ℝ)
  (x z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x ≠ 0)
  (hxp : 0 < x)
  -- (hy0 : y = 0)
  (h₇ : a 0 * x + a 2 * z = 0)
  (h₈ : a 3 * x + a 5 * z = 0) :
  -- (h₉ : a 6 * x + a 8 * z = 0) :
  False := by
  have g1: 0 < a 0 * x := by exact mul_pos h₀.1 hxp
  have g2: a 2 * z < 0 := by linarith
  have hzn: 0 < z := by exact pos_of_mul_neg_right g2 (le_of_lt h₁.2)
  have g3: a 3 * x < 0 := by exact mul_neg_of_neg_of_pos h₂.1 hxp
  have g4: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzn
  linarith


lemma imo_1965_p2_18
  -- (y : ℝ)
  (x z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x ≠ 0)
  (hxp : 0 < x)
  -- (hy0 : y = 0)
  (h₇ : a 0 * x + a 2 * z = 0) :
  -- (h₈ : a 3 * x + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 8 * z = 0) :
  0 < z := by
  have g1: 0 < a 0 * x := by exact mul_pos h₀.1 hxp
  have g2: a 2 * z < 0 := by linarith
  exact pos_of_mul_neg_right g2 (le_of_lt h₁.2)


lemma imo_1965_p2_19
  -- (x y : ℝ)
  (z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y = 0)
  -- (h₇ : a 0 * x + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 8 * z = 0)
  -- (g1 : 0 < a 0 * x)
  (g2 : a 2 * z < 0) :
  0 < z := by
  refine pos_of_mul_neg_right g2 ?_
  exact le_of_lt h₁.2


lemma imo_1965_p2_20
  (x z : ℝ)
  -- (y : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x ≠ 0)
  (hxp : 0 < x)
  -- (hy0 : y = 0)
  -- (h₇ : a 0 * x + a 2 * z = 0)
  (h₈ : a 3 * x + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 8 * z = 0)
  -- (g1 : 0 < a 0 * x)
  -- (g2 : a 2 * z < 0)
  (hzn : 0 < z) :
  False := by
  have g3: a 3 * x < 0 := by exact mul_neg_of_neg_of_pos h₂.1 hxp
  have g4: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzn
  linarith


lemma imo_1965_p2_21
  -- (y : ℝ)
  (x z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y = 0)
  -- (h₇ : a 0 * x + a 2 * z = 0)
  (h₈ : a 3 * x + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 8 * z = 0)
  -- (g1 : 0 < a 0 * x)
  -- (g2 : a 2 * z < 0)
  (hzn : 0 < z)
  (g3 : a 3 * x < 0) :
  -- (g4 : a 5 * z < 0) :
  False := by
  have g4: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzn
  linarith


lemma imo_1965_p2_22
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  (hxp : 0 < x)
  (hy0 : ¬y = 0) :
  False := by
  push_neg at hy0
  by_cases hyp: 0 < y
  . have g1: a 6 * x < 0 := by exact mul_neg_of_neg_of_pos h₃.1 hxp
    have g2: a 7 * y < 0 := by exact mul_neg_of_neg_of_pos h₃.2 hyp
    have g3: 0 < z * a 8 := by linarith
    have hzp: 0 < z := by exact pos_of_mul_pos_left g3 (le_of_lt h₀.2.2)
    ------ here we consider all the possible relationships between x, y, z
    by_cases rxy: x ≤ y
    . by_cases ryz: y ≤ z
        -- x <= y <= z
      . have g2: 0 < (a 6 + a 7 + a 8) * y := by exact mul_pos h₆ hyp
        have g3: 0 ≤ a 6 * (x-y) := by
          exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₃.1) (by linarith)
        have g4: 0 ≤ a 8 * (z-y) := by exact mul_nonneg (le_of_lt h₀.2.2) (by linarith)
        linarith
      push_neg at ryz
      by_cases rxz: x ≤ z
        -- x <= z < y
      . have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
        have g3: 0 ≤ a 3 * (x-y) := by
          exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
        have g4: 0 < a 5 * (z-y) := by
          exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
        linarith
      push_neg at rxz -- z < x <= y
      have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
      have g3: 0 ≤ a 3 * (x-y) := by
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
      have g4: 0 < a 5 * (z-y) := by
        exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
      linarith
    push_neg at rxy
    by_cases rzy: z ≤ y
      -- z <= y < x
    . have g2: 0 < (a 0 + a 1 + a 2) * y := by exact mul_pos h₄ hyp
      have g3: 0 < a 0 * (x-y) := by exact mul_pos h₀.1 (by linarith)
      have g4: 0 ≤ a 2 * (z-y) := by
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₁.2) (by linarith)
      linarith
    . push_neg at rzy
      by_cases rzx: z ≤ x
        -- y < z <= x
      . have g2: 0 < (a 0 + a 1 + a 2) * z := by exact mul_pos h₄ hzp
        have g3: 0 ≤ a 0 * (x-z) := by exact mul_nonneg (le_of_lt h₀.1) (by linarith)
        have g4: 0 < a 1 * (y-z) := by exact mul_pos_of_neg_of_neg h₁.1 (by linarith)
        linarith
      . push_neg at rzx
          -- y < x < z
        have g2: 0 < (a 6 + a 7 + a 8) * z := by exact mul_pos h₆ hzp
        have g3: 0 < a 6 * (x-z) := by exact mul_pos_of_neg_of_neg h₃.1 (by linarith)
        have g4: 0 < a 7 * (y-z) := by exact mul_pos_of_neg_of_neg h₃.2 (by linarith)
        linarith
  -------- new world where y < 0 and 0 < x
  . push_neg at hyp
    have hyn: y < 0 :=  by exact lt_of_le_of_ne hyp hy0
    -- show from a 0 that 0 < z
    have g1: 0 < a 0 * x := by exact mul_pos h₀.1 hxp
    have g2: 0 < a 1 * y := by exact mul_pos_of_neg_of_neg h₁.1 hyn
    have g3: a 2 * z < 0 := by linarith
    have hzp: 0 < z := by exact pos_of_mul_neg_right g3 (le_of_lt h₁.2)
    -- then show from a 3 that's not possible
    have g4: a 3 * x < 0 := by exact mul_neg_of_neg_of_pos h₂.1 hxp
    have g5: a 4 * y < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 hyn
    have g6: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzp
    linarith


lemma imo_1965_p2_23
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y) :
  False := by
  have g1: a 6 * x < 0 := by exact mul_neg_of_neg_of_pos h₃.1 hxp
  have g2: a 7 * y < 0 := by exact mul_neg_of_neg_of_pos h₃.2 hyp
  have g3: 0 < z * a 8 := by linarith
  have hzp: 0 < z := by exact pos_of_mul_pos_left g3 (le_of_lt h₀.2.2)
  ------ here we consider all the possible relationships between x, y, z
  by_cases rxy: x ≤ y
  . by_cases ryz: y ≤ z
      -- x <= y <= z
    . have g2: 0 < (a 6 + a 7 + a 8) * y := by exact mul_pos h₆ hyp
      have g3: 0 ≤ a 6 * (x-y) := by
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₃.1) (by linarith)
      have g4: 0 ≤ a 8 * (z-y) := by exact mul_nonneg (le_of_lt h₀.2.2) (by linarith)
      linarith
    push_neg at ryz
    by_cases rxz: x ≤ z
      -- x <= z < y
    . have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
      have g3: 0 ≤ a 3 * (x-y) := by
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
      have g4: 0 < a 5 * (z-y) := by
        exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
      linarith
    push_neg at rxz -- z < x <= y
    have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
    have g3: 0 ≤ a 3 * (x-y) := by
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
    have g4: 0 < a 5 * (z-y) := by
      exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
    linarith
  push_neg at rxy
  by_cases rzy: z ≤ y
    -- z <= y < x
  . have g2: 0 < (a 0 + a 1 + a 2) * y := by exact mul_pos h₄ hyp
    have g3: 0 < a 0 * (x-y) := by exact mul_pos h₀.1 (by linarith)
    have g4: 0 ≤ a 2 * (z-y) := by
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₁.2) (by linarith)
    linarith
  . push_neg at rzy
    by_cases rzx: z ≤ x
      -- y < z <= x
    . have g2: 0 < (a 0 + a 1 + a 2) * z := by exact mul_pos h₄ hzp
      have g3: 0 ≤ a 0 * (x-z) := by exact mul_nonneg (le_of_lt h₀.1) (by linarith)
      have g4: 0 < a 1 * (y-z) := by exact mul_pos_of_neg_of_neg h₁.1 (by linarith)
      linarith
    . push_neg at rzx
        -- y < x < z
      have g2: 0 < (a 6 + a 7 + a 8) * z := by exact mul_pos h₆ hzp
      have g3: 0 < a 6 * (x-z) := by exact mul_pos_of_neg_of_neg h₃.1 (by linarith)
      have g4: 0 < a 7 * (y-z) := by exact mul_pos_of_neg_of_neg h₃.2 (by linarith)
      linarith


lemma imo_1965_p2_24
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y) :
  -- (g1 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8) :
  0 < z := by
  have g1: a 6 * x < 0 := by exact mul_neg_of_neg_of_pos h₃.1 hxp
  have g2: a 7 * y < 0 := by exact mul_neg_of_neg_of_pos h₃.2 hyp
  have g3: 0 < z * a 8 := by linarith
  refine pos_of_mul_pos_left g3 ?_
  exact le_of_lt h₀.2.2


lemma imo_1965_p2_25
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y)
  -- (g1 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  (hzp : 0 < z) :
  False := by
  by_cases rxy: x ≤ y
  . by_cases ryz: y ≤ z
      -- x <= y <= z
    . have g2: 0 < (a 6 + a 7 + a 8) * y := by exact mul_pos h₆ hyp
      have g3: 0 ≤ a 6 * (x-y) := by
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₃.1) (by linarith)
      have g4: 0 ≤ a 8 * (z-y) := by exact mul_nonneg (le_of_lt h₀.2.2) (by linarith)
      linarith
    . push_neg at ryz
      by_cases rxz: x ≤ z
        -- x <= z < y
      . have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
        have g3: 0 ≤ a 3 * (x-y) := by
          exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
        have g4: 0 < a 5 * (z-y) := by
          exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
        linarith
      . push_neg at rxz -- z < x <= y
        have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
        have g3: 0 ≤ a 3 * (x-y) := by
          exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
        have g4: 0 < a 5 * (z-y) := by
          exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
        linarith
  . push_neg at rxy
    by_cases rzy: z ≤ y
      -- z <= y < x
    . have g2: 0 < (a 0 + a 1 + a 2) * y := by exact mul_pos h₄ hyp
      have g3: 0 < a 0 * (x-y) := by exact mul_pos h₀.1 (by linarith)
      have g4: 0 ≤ a 2 * (z-y) := by
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₁.2) (by linarith)
      linarith
    . push_neg at rzy
      by_cases rzx: z ≤ x
        -- y < z <= x
      . have g2: 0 < (a 0 + a 1 + a 2) * z := by exact mul_pos h₄ hzp
        have g3: 0 ≤ a 0 * (x-z) := by exact mul_nonneg (le_of_lt h₀.1) (by linarith)
        have g4: 0 < a 1 * (y-z) := by exact mul_pos_of_neg_of_neg h₁.1 (by linarith)
        linarith
      . push_neg at rzx
          -- y < x < z
        have g2: 0 < (a 6 + a 7 + a 8) * z := by exact mul_pos h₆ hzp
        have g3: 0 < a 6 * (x-z) := by exact mul_pos_of_neg_of_neg h₃.1 (by linarith)
        have g4: 0 < a 7 * (y-z) := by exact mul_pos_of_neg_of_neg h₃.2 (by linarith)
        linarith


lemma imo_1965_p2_26
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y)
  -- (g1 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  -- (hzp : 0 < z)
  (rxy : x ≤ y) :
  False := by
  by_cases ryz: y ≤ z
    -- x <= y <= z
  . have g2: 0 < (a 6 + a 7 + a 8) * y := by exact mul_pos h₆ hyp
    have g3: 0 ≤ a 6 * (x-y) := by
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₃.1) (by linarith)
    have g4: 0 ≤ a 8 * (z-y) := by exact mul_nonneg (le_of_lt h₀.2.2) (by linarith)
    linarith
  . push_neg at ryz
    by_cases rxz: x ≤ z
      -- x <= z < y
    . have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
      have g3: 0 ≤ a 3 * (x-y) := by
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
      have g4: 0 < a 5 * (z-y) := by
        exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
      linarith
      -- z < x <= y
    . push_neg at rxz
      have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
      have g3: 0 ≤ a 3 * (x-y) := by
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
      have g4: 0 < a 5 * (z-y) := by
        exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
      linarith


lemma imo_1965_p2_27
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y)
  -- (g1 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  -- (hzp : 0 < z)
  (rxy : x ≤ y)
  (ryz : y ≤ z) :
  False := by
  have g2: 0 < (a 6 + a 7 + a 8) * y := by exact mul_pos h₆ hyp
  have g3: 0 ≤ a 6 * (x-y) := by
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₃.1) (by linarith)
  have g4: 0 ≤ a 8 * (z-y) := by exact mul_nonneg (le_of_lt h₀.2.2) (by linarith)
  linarith


lemma imo_1965_p2_28
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y)
  -- (g11 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  -- (hzp : 0 < z)
  (rxy : x ≤ y)
  (ryz : y ≤ z)
  (g1 : (a 6 + a 7 + a 8) * y + a 6 * (x - y) + a 8 * (z - y) = 0) :
  False := by
  have g2: 0 < (a 6 + a 7 + a 8) * y := by exact mul_pos h₆ hyp
  have g3: 0 ≤ a 6 * (x-y) := by
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₃.1) (by linarith)
  have g4: 0 ≤ a 8 * (z-y) := by exact mul_nonneg (le_of_lt h₀.2.2) (by linarith)
  linarith


lemma imo_1965_p2_29
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  -- (hyp : 0 < y)
  -- (g11 : a 6 * x < 0)
  -- (g21 : a 7 * y < 0)
  -- (g31 : 0 < z * a 8)
  -- (hzp : 0 < z)
  -- (rxy : x ≤ y)
  (ryz : y ≤ z)
  (g1 : (a 6 + a 7 + a 8) * y + a 6 * (x - y) + a 8 * (z - y) = 0)
  (g2 : 0 < (a 6 + a 7 + a 8) * y)
  (g3 : 0 ≤ a 6 * (x - y)) :
  False := by
  have g4: 0 ≤ a 8 * (z-y) := by exact mul_nonneg (le_of_lt h₀.2.2) (by linarith)
  linarith


lemma imo_1965_p2_30
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y)
  -- (g1 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  -- (hzp : 0 < z)
  (rxy : x ≤ y)
  (ryz : z < y) :
  False := by
  by_cases rxz: x ≤ z
    -- x <= z < y
  . have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
    have g3: 0 ≤ a 3 * (x-y) := by
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
    have g4: 0 < a 5 * (z-y) := by
      exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
    linarith
    -- z < x <= y
  . push_neg at rxz
    have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
    have g3: 0 ≤ a 3 * (x-y) := by
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
    have g4: 0 < a 5 * (z-y) := by
      exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
    linarith


lemma imo_1965_p2_31
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y)
  -- (g1 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  -- (hzp : 0 < z)
  -- (rxy : x ≤ y)
  (ryz : z < y)
  (rxz : x ≤ z) :
  False := by
  have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
  have g3: 0 ≤ a 3 * (x - y) := by
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
  have g4: 0 < a 5 * (z - y) := by
    exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
  linarith


lemma imo_1965_p2_32
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y)
  -- (g11 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  -- (hzp : 0 < z)
  -- (rxy : x ≤ y)
  (ryz : z < y)
  (rxz : x ≤ z)
  (g1 : (a 3 + a 4 + a 5) * y + a 3 * (x - y) + a 5 * (z - y) = 0) :
  False := by
  have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
  have g3: 0 ≤ a 3 * (x - y) := by
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
  have g4: 0 < a 5 * (z - y) := by
    exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
  linarith


lemma imo_1965_p2_33
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y)
  -- (g1 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  -- (hzp : 0 < z)
  (rxy : x ≤ y)
  (ryz : z < y) :
  -- (rxz : z < x) :
  False := by
  have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
  have g3: 0 ≤ a 3 * (x-y) := by
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
  have g4: 0 < a 5 * (z-y) := by
    exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
  linarith


lemma imo_1965_p2_34
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y)
  -- (g11 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  -- (hzp : 0 < z)
  (rxy : x ≤ y)
  (ryz : z < y)
  -- (rxz : z < x)
  (g1 : (a 3 + a 4 + a 5) * y + a 3 * (x - y) + a 5 * (z - y) = 0) :
  False := by
  have g2: 0 < (a 3 + a 4 + a 5) * y := by exact mul_pos h₅ hyp
  have g3: 0 ≤ a 3 * (x-y) := by
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₂.1) (by linarith)
  have g4: 0 < a 5 * (z-y) := by
    exact mul_pos_of_neg_of_neg h₂.2 (by linarith)
  linarith


lemma imo_1965_p2_35
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y)
  -- (g1 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  (hzp : 0 < z)
  (rxy : ¬x ≤ y) :
  False := by
  push_neg at rxy
  by_cases rzy: z ≤ y
    -- z <= y < x
  . have g2: 0 < (a 0 + a 1 + a 2) * y := by exact mul_pos h₄ hyp
    have g3: 0 < a 0 * (x-y) := by exact mul_pos h₀.1 (by linarith)
    have g4: 0 ≤ a 2 * (z-y) := by
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₁.2) (by linarith)
    linarith
  . push_neg at rzy
    by_cases rzx: z ≤ x
      -- y < z <= x
    . have g2: 0 < (a 0 + a 1 + a 2) * z := by exact mul_pos h₄ hzp
      have g3: 0 ≤ a 0 * (x-z) := by exact mul_nonneg (le_of_lt h₀.1) (by linarith)
      have g4: 0 < a 1 * (y-z) := by exact mul_pos_of_neg_of_neg h₁.1 (by linarith)
      linarith
    . push_neg at rzx
        -- y < x < z
      have g2: 0 < (a 6 + a 7 + a 8) * z := by exact mul_pos h₆ hzp
      have g3: 0 < a 6 * (x-z) := by exact mul_pos_of_neg_of_neg h₃.1 (by linarith)
      have g4: 0 < a 7 * (y-z) := by exact mul_pos_of_neg_of_neg h₃.2 (by linarith)
      linarith


lemma imo_1965_p2_36
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y)
  -- (g1 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  -- (hzp : 0 < z)
  (rxy : y < x)
  (rzy : z ≤ y) :
  False := by
  have g2: 0 < (a 0 + a 1 + a 2) * y := by exact mul_pos h₄ hyp
  have g3: 0 < a 0 * (x-y) := by exact mul_pos h₀.1 (by linarith)
  have g4: 0 ≤ a 2 * (z-y) := by
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₁.2) (by linarith)
  linarith


lemma imo_1965_p2_37
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  (hyp : 0 < y)
  -- (g11 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  -- (hzp : 0 < z)
  (rxy : y < x)
  (rzy : z ≤ y)
  (g1 : (a 0 + a 1 + a 2) * y + a 0 * (x - y) + a 2 * (z - y) = 0) :
  False := by
  have g2: 0 < (a 0 + a 1 + a 2) * y := by exact mul_pos h₄ hyp
  have g3: 0 < a 0 * (x-y) := by exact mul_pos h₀.1 (by linarith)
  have g4: 0 ≤ a 2 * (z-y) := by
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h₁.2) (by linarith)
  linarith


lemma imo_1965_p2_38
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  -- (hyp : 0 < y)
  -- (g1 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  (hzp : 0 < z)
  -- (rxy : y < x)
  (rzy : y < z) :
  False := by
  by_cases rzx: z ≤ x
    -- y < z <= x
  . have g2: 0 < (a 0 + a 1 + a 2) * z := by exact mul_pos h₄ hzp
    have g3: 0 ≤ a 0 * (x-z) := by exact mul_nonneg (le_of_lt h₀.1) (by linarith)
    have g4: 0 < a 1 * (y-z) := by exact mul_pos_of_neg_of_neg h₁.1 (by linarith)
    linarith
  . push_neg at rzx
      -- y < x < z
    have g2: 0 < (a 6 + a 7 + a 8) * z := by exact mul_pos h₆ hzp
    have g3: 0 < a 6 * (x-z) := by exact mul_pos_of_neg_of_neg h₃.1 (by linarith)
    have g4: 0 < a 7 * (y-z) := by exact mul_pos_of_neg_of_neg h₃.2 (by linarith)
    linarith


lemma imo_1965_p2_39
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  -- (hyp : 0 < y)
  -- (g1 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  (hzp : 0 < z)
  -- (rxy : y < x)
  (rzy : y < z)
  (rzx : z ≤ x) :
  False := by
  have g2: 0 < (a 0 + a 1 + a 2) * z := by exact mul_pos h₄ hzp
  have g3: 0 ≤ a 0 * (x-z) := by exact mul_nonneg (le_of_lt h₀.1) (by linarith)
  have g4: 0 < a 1 * (y-z) := by exact mul_pos_of_neg_of_neg h₁.1 (by linarith)
  linarith


lemma imo_1965_p2_40
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  -- (hyp : 0 < y)
  -- (g11 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  (hzp : 0 < z)
  -- (rxy : y < x)
  (rzy : y < z)
  (rzx : z ≤ x)
  (g1 : (a 0 + a 1 + a 2) * z + a 0 * (x-z) + a 1 * (y-z) = 0) :
  False := by
  have g2: 0 < (a 0 + a 1 + a 2) * z := by exact mul_pos h₄ hzp
  have g3: 0 ≤ a 0 * (x-z) := by exact mul_nonneg (le_of_lt h₀.1) (by linarith)
  have g4: 0 < a 1 * (y-z) := by exact mul_pos_of_neg_of_neg h₁.1 (by linarith)
  linarith


lemma imo_1965_p2_41
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  -- (hyp : 0 < y)
  -- (g1 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  (hzp : 0 < z)
  -- (rxy : y < x)
  (rzy : y < z)
  (rzx : x < z) :
  False := by
  have g2: 0 < (a 6 + a 7 + a 8) * z := by exact mul_pos h₆ hzp
  have g3: 0 < a 6 * (x-z) := by exact mul_pos_of_neg_of_neg h₃.1 (by linarith)
  have g4: 0 < a 7 * (y-z) := by exact mul_pos_of_neg_of_neg h₃.2 (by linarith)
  linarith


lemma imo_1965_p2_42
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  -- (hyp : 0 < y)
  -- (g11 : a 6 * x < 0)
  -- (g2 : a 7 * y < 0)
  -- (g3 : 0 < z * a 8)
  (hzp : 0 < z)
  -- (rxy : y < x)
  (rzy : y < z)
  (rzx : x < z)
  (g1 : (a 6 + a 7 + a 8) * z + a 6 * (x - z) + a 7 * (y - z) = 0) :
  False := by
  have g2: 0 < (a 6 + a 7 + a 8) * z := by exact mul_pos h₆ hzp
  have g3: 0 < a 6 * (x-z) := by exact mul_pos_of_neg_of_neg h₃.1 (by linarith)
  have g4: 0 < a 7 * (y-z) := by exact mul_pos_of_neg_of_neg h₃.2 (by linarith)
  linarith


lemma imo_1965_p2_43
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  (hxp : 0 < x)
  (hy0 : y ≠ 0)
  (hyp : y ≤ 0) :
  False := by
  have hyn: y < 0 :=  by exact lt_of_le_of_ne hyp hy0
  -- show from a 0 that 0 < z
  have g1: 0 < a 0 * x := by exact mul_pos h₀.1 hxp
  have g2: 0 < a 1 * y := by exact mul_pos_of_neg_of_neg h₁.1 hyn
  have g3: a 2 * z < 0 := by linarith
  have hzp: 0 < z := by exact pos_of_mul_neg_right g3 (le_of_lt h₁.2)
  -- then show from a 3 that's not possible
  have g4: a 3 * x < 0 := by exact mul_neg_of_neg_of_pos h₂.1 hxp
  have g5: a 4 * y < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 hyn
  have g6: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzp
  linarith


lemma imo_1965_p2_44
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  -- (hyp : y ≤ 0)
  (hyn : y < 0) :
  -- (g1 : 0 < a 0 * x)
  -- (g2 : 0 < a 1 * y)
  -- (g3 : a 2 * z < 0) :
  0 < z := by
  have g1: 0 < a 0 * x := by exact mul_pos h₀.1 hxp
  have g2: 0 < a 1 * y := by exact mul_pos_of_neg_of_neg h₁.1 hyn
  have g3: a 2 * z < 0 := by linarith
  exact pos_of_mul_neg_right g3 (le_of_lt h₁.2)


lemma imo_1965_p2_45
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  -- (hyp : y ≤ 0)
  (hyn : y < 0)
  -- (g1 : 0 < a 0 * x)
  -- (g2 : 0 < a 1 * y)
  -- (g3 : a 2 * z < 0)
  (hzp : 0 < z) :
  False := by
  have g4: a 3 * x < 0 := by exact mul_neg_of_neg_of_pos h₂.1 hxp
  have g5: a 4 * y < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 hyn
  have g6: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzp
  linarith


lemma imo_1965_p2_46
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : 0 < x)
  -- (hy0 : y ≠ 0)
  -- (hyp : y ≤ 0)
  -- (hyn : y < 0)
  -- (g1 : 0 < a 0 * x)
  -- (g2 : 0 < a 1 * y)
  -- (g3 : a 2 * z < 0)
  (hzp : 0 < z)
  (g4 : a 3 * x < 0)
  (g5 : a 4 * y < 0) :
  False := by
  have g6: a 5 * z < 0 := by exact mul_neg_of_neg_of_pos h₂.2 hzp
  linarith


lemma imo_1965_p2_47
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  (hx0 : x ≠ 0)
  (hxp : x ≤ 0) :
  False := by
  have hxn: x < 0 := by exact lt_of_le_of_ne hxp hx0
  by_cases hyp: 0 ≤ y
  . have g1: a 0 * x < 0 := by exact mul_neg_of_pos_of_neg h₀.1 hxn
    have g2: a 1 * y ≤ 0 := by
      refine mul_nonpos_iff.mpr ?_
      right
      constructor
      . exact le_of_lt h₁.1
      . exact hyp
    have g3: 0 < z * a 2 := by linarith
    have hzn: z < 0 := by exact neg_of_mul_pos_left g3 (le_of_lt h₁.2)
    -- demonstrate the contradiction
    have g4: 0 < a 3 * x := by exact mul_pos_of_neg_of_neg h₂.1 hxn
    have g5: 0 ≤ a 4 * y := by exact mul_nonneg (le_of_lt h₀.2.1) hyp
    have g6: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzn
    linarith
  . push_neg at hyp
    -- have hyn: y < 0, {exact lt_of_le_of_ne hyp hy0,},
    have g1: 0 < a 6 * x := by exact mul_pos_of_neg_of_neg h₃.1 hxn
    have g2: 0 < a 7 * y := by exact mul_pos_of_neg_of_neg h₃.2 hyp
    have g3: z * a 8 < 0 := by linarith
    have hzp: z < 0 := by exact neg_of_mul_neg_left g3 (le_of_lt h₀.2.2)
      -- we have x,y,z < 0 -- we will examine all the orders they can have
    by_cases rxy: x ≤ y
    . by_cases ryz: y ≤ z
        -- x <= y <= z
      . have g2: (a 0 + a 1 + a 2) * y < 0 := by exact mul_neg_of_pos_of_neg h₄ hyp
        have g3: a 0 * (x-y) ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
        have g4: a 2 * (z-y) ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₁.2) (by linarith)
        linarith
      . push_neg at ryz
        by_cases rxz: x ≤ z
          -- x <= z < y
        . have g2: (a 0 + a 1 + a 2) * z < 0 := by exact mul_neg_of_pos_of_neg h₄ hzp
          have g3: a 0 * (x-z) ≤ 0 := by
            exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
          have g4: a 1 * (y-z) < 0 := by
            exact mul_neg_of_neg_of_pos h₁.1 (by linarith)
          linarith
        . push_neg at rxz -- z < x <= y
          have g2: (a 6 + a 7 + a 8) * z < 0 := by exact mul_neg_of_pos_of_neg h₆ hzp
          have g3: a 6 * (x-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
          have g4: a 7 * (y-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.2 (by linarith)
          linarith
    . push_neg at rxy
      by_cases rzy: z ≤ y
        -- z <= y < x
      . have g2: (a 6 + a 7 + a 8) * y < 0 := by exact mul_neg_of_pos_of_neg h₆ hyp
        have g3: a 6 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
        have g4: a 8 * (z-y) ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.2.2) (by linarith)
        linarith
      . push_neg at rzy
        by_cases rzx: z ≤ x
          -- y < z <= x
        . have g2: (a 3 + a 4 + a 5) * z < 0 := by exact mul_neg_of_pos_of_neg h₅ hzp
          have g3: a 3 * (x-z) ≤ 0 := by
            exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₂.1) (by linarith)
          have g4: a 4 * (y-z) < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 (by linarith)
          linarith
        . push_neg at rzx
          -- y < x < z
          have g2: (a 3 + a 4 + a 5) * y < 0 := by exact mul_neg_of_pos_of_neg h₅ hyp
          have g3: a 3 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.1 (by linarith)
          have g4: a 5 * (z-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.2 (by linarith)
          linarith


lemma imo_1965_p2_48
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  (hxn : x < 0)
  (hyp : 0 ≤ y) :
  False := by
  have g1: a 0 * x < 0 := by exact mul_neg_of_pos_of_neg h₀.1 hxn
  have g2: a 1 * y ≤ 0 := by
    refine mul_nonpos_iff.mpr ?_
    right
    constructor
    . exact le_of_lt h₁.1
    . exact hyp
  have g3: 0 < z * a 2 := by linarith
  have hzn: z < 0 := by exact neg_of_mul_pos_left g3 (le_of_lt h₁.2)
  -- demonstrate the contradiction
  have g4: 0 < a 3 * x := by exact mul_pos_of_neg_of_neg h₂.1 hxn
  have g5: 0 ≤ a 4 * y := by exact mul_nonneg (le_of_lt h₀.2.1) hyp
  have g6: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzn
  linarith


lemma imo_1965_p2_49
  -- (x z : ℝ)
  (y : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  (hyp : 0 ≤ y) :
  -- (g1 : a 0 * x < 0) :
  a 1 * y ≤ 0 := by
  refine mul_nonpos_iff.mpr ?_
  right
  constructor
  . exact le_of_lt h₁.1
  . exact hyp


lemma imo_1965_p2_50
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  (hxn : x < 0)
  (hyp : 0 ≤ y) :
  -- g1 : a 0 * x < 0
  -- g2 : a 1 * y ≤ 0
  -- g3 : 0 < z * a 2
  z < 0 := by
  have g1: a 0 * x < 0 := by exact mul_neg_of_pos_of_neg h₀.1 hxn
  have g2: a 1 * y ≤ 0 := by
    refine mul_nonpos_iff.mpr ?_
    right
    constructor
    . exact le_of_lt h₁.1
    . exact hyp
  have g3: 0 < z * a 2 := by linarith
  exact neg_of_mul_pos_left g3 (le_of_lt h₁.2)


lemma imo_1965_p2_51
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  -- (hyp : 0 ≤ y)
  (g1 : a 0 * x < 0)
  (g2 : a 1 * y ≤ 0) :
  -- g3 : 0 < z * a 2
  z < 0 := by
  have g3: 0 < z * a 2 := by linarith
  exact neg_of_mul_pos_left g3 (le_of_lt h₁.2)


lemma imo_1965_p2_52
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  (hxn : x < 0)
  (hyp : 0 ≤ y)
  -- (g1 : a 0 * x < 0)
  -- (g2 : a 1 * y ≤ 0)
  -- (g3 : 0 < z * a 2)
  (hzn : z < 0) :
  False := by
  have g4: 0 < a 3 * x := by exact mul_pos_of_neg_of_neg h₂.1 hxn
  have g5: 0 ≤ a 4 * y := by exact mul_nonneg (le_of_lt h₀.2.1) hyp
  have g6: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzn
  linarith


lemma imo_1965_p2_53
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  (hyp : 0 ≤ y)
  -- (g1 : a 0 * x < 0)
  -- (g2 : a 1 * y ≤ 0)
  -- (g3 : 0 < z * a 2)
  (hzn : z < 0)
  (g4 : 0 < a 3 * x) :
  False := by
  have g5: 0 ≤ a 4 * y := by exact mul_nonneg (le_of_lt h₀.2.1) hyp
  have g6: 0 < a 5 * z := by exact mul_pos_of_neg_of_neg h₂.2 hzn
  linarith


lemma imo_1965_p2_54
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  (hxn : x < 0)
  (hyp : y < 0) :
  False := by
  have g1: 0 < a 6 * x := by exact mul_pos_of_neg_of_neg h₃.1 hxn
  have g2: 0 < a 7 * y := by exact mul_pos_of_neg_of_neg h₃.2 hyp
  have g3: z * a 8 < 0 := by linarith
  have hzp: z < 0 := by exact neg_of_mul_neg_left g3 (le_of_lt h₀.2.2)
    -- we have x,y,z < 0 -- we will examine all the orders they can have
  by_cases rxy: x ≤ y
  . by_cases ryz: y ≤ z
      -- x <= y <= z
    . have g2: (a 0 + a 1 + a 2) * y < 0 := by exact mul_neg_of_pos_of_neg h₄ hyp
      have g3: a 0 * (x-y) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
      have g4: a 2 * (z-y) ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₁.2) (by linarith)
      linarith
    . push_neg at ryz
      by_cases rxz: x ≤ z
        -- x <= z < y
      . have g2: (a 0 + a 1 + a 2) * z < 0 := by exact mul_neg_of_pos_of_neg h₄ hzp
        have g3: a 0 * (x-z) ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
        have g4: a 1 * (y-z) < 0 := by
          exact mul_neg_of_neg_of_pos h₁.1 (by linarith)
        linarith
      . push_neg at rxz -- z < x <= y
        have g2: (a 6 + a 7 + a 8) * z < 0 := by exact mul_neg_of_pos_of_neg h₆ hzp
        have g3: a 6 * (x-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
        have g4: a 7 * (y-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.2 (by linarith)
        linarith
  . push_neg at rxy
    by_cases rzy: z ≤ y
      -- z <= y < x
    . have g2: (a 6 + a 7 + a 8) * y < 0 := by exact mul_neg_of_pos_of_neg h₆ hyp
      have g3: a 6 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
      have g4: a 8 * (z-y) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.2.2) (by linarith)
      linarith
    . push_neg at rzy
      by_cases rzx: z ≤ x
        -- y < z <= x
      . have g2: (a 3 + a 4 + a 5) * z < 0 := by exact mul_neg_of_pos_of_neg h₅ hzp
        have g3: a 3 * (x-z) ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₂.1) (by linarith)
        have g4: a 4 * (y-z) < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 (by linarith)
        linarith
      . push_neg at rzx
        -- y < x < z
        have g2: (a 3 + a 4 + a 5) * y < 0 := by exact mul_neg_of_pos_of_neg h₅ hyp
        have g3: a 3 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.1 (by linarith)
        have g4: a 5 * (z-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.2 (by linarith)
        linarith


lemma imo_1965_p2_55
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  (hxn : x < 0)
  (hyp : y < 0) :
  z < 0 := by
  have g1: 0 < a 6 * x := by exact mul_pos_of_neg_of_neg h₃.1 hxn
  have g2: 0 < a 7 * y := by exact mul_pos_of_neg_of_neg h₃.2 hyp
  have g3: z * a 8 < 0 := by linarith
  exact neg_of_mul_neg_left g3 (le_of_lt h₀.2.2)


lemma imo_1965_p2_56
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  -- (hyp : y < 0)
  (g1 : 0 < a 6 * x)
  (g2 : 0 < a 7 * y) :
  z < 0 := by
  have g3: z * a 8 < 0 := by linarith
  exact neg_of_mul_neg_left g3 (le_of_lt h₀.2.2)


lemma imo_1965_p2_57
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  (hyp : y < 0)
  -- (g1 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  (hzp : z < 0) :
  False := by
  by_cases rxy: x ≤ y
  . by_cases ryz: y ≤ z
      -- x <= y <= z
    . have g2: (a 0 + a 1 + a 2) * y < 0 := by exact mul_neg_of_pos_of_neg h₄ hyp
      have g3: a 0 * (x-y) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
      have g4: a 2 * (z-y) ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₁.2) (by linarith)
      linarith
    . push_neg at ryz
      by_cases rxz: x ≤ z
        -- x <= z < y
      . have g2: (a 0 + a 1 + a 2) * z < 0 := by exact mul_neg_of_pos_of_neg h₄ hzp
        have g3: a 0 * (x-z) ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
        have g4: a 1 * (y-z) < 0 := by
          exact mul_neg_of_neg_of_pos h₁.1 (by linarith)
        linarith
      . push_neg at rxz -- z < x <= y
        have g2: (a 6 + a 7 + a 8) * z < 0 := by exact mul_neg_of_pos_of_neg h₆ hzp
        have g3: a 6 * (x-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
        have g4: a 7 * (y-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.2 (by linarith)
        linarith
  . push_neg at rxy
    by_cases rzy: z ≤ y
      -- z <= y < x
    . have g2: (a 6 + a 7 + a 8) * y < 0 := by exact mul_neg_of_pos_of_neg h₆ hyp
      have g3: a 6 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
      have g4: a 8 * (z-y) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.2.2) (by linarith)
      linarith
    . push_neg at rzy
      by_cases rzx: z ≤ x
        -- y < z <= x
      . have g2: (a 3 + a 4 + a 5) * z < 0 := by exact mul_neg_of_pos_of_neg h₅ hzp
        have g3: a 3 * (x-z) ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₂.1) (by linarith)
        have g4: a 4 * (y-z) < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 (by linarith)
        linarith
      . push_neg at rzx
        -- y < x < z
        have g2: (a 3 + a 4 + a 5) * y < 0 := by exact mul_neg_of_pos_of_neg h₅ hyp
        have g3: a 3 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.1 (by linarith)
        have g4: a 5 * (z-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.2 (by linarith)
        linarith


lemma imo_1965_p2_58
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  (hyp : y < 0)
  -- (g1 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  (hzp : z < 0)
  (rxy : x ≤ y) :
  False := by
  by_cases ryz: y ≤ z
    -- x <= y <= z
  . have g2: (a 0 + a 1 + a 2) * y < 0 := by exact mul_neg_of_pos_of_neg h₄ hyp
    have g3: a 0 * (x-y) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
    have g4: a 2 * (z-y) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₁.2) (by linarith)
    linarith
  . push_neg at ryz
    by_cases rxz: x ≤ z
      -- x <= z < y
    . have g2: (a 0 + a 1 + a 2) * z < 0 := by exact mul_neg_of_pos_of_neg h₄ hzp
      have g3: a 0 * (x-z) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
      have g4: a 1 * (y-z) < 0 := by
        exact mul_neg_of_neg_of_pos h₁.1 (by linarith)
      linarith
    . push_neg at rxz -- z < x <= y
      have g2: (a 6 + a 7 + a 8) * z < 0 := by exact mul_neg_of_pos_of_neg h₆ hzp
      have g3: a 6 * (x-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
      have g4: a 7 * (y-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.2 (by linarith)
      linarith


lemma imo_1965_p2_59
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  (hyp : y < 0)
  -- (g1 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  -- (hzp : z < 0)
  (rxy : x ≤ y)
  (ryz : y ≤ z) :
  False := by
  have g2: (a 0 + a 1 + a 2) * y < 0 := by exact mul_neg_of_pos_of_neg h₄ hyp
  have g3: a 0 * (x-y) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
  have g4: a 2 * (z-y) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₁.2) (by linarith)
  linarith


lemma imo_1965_p2_60
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  (hyp : y < 0)
  -- (g11 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  -- (hzp : z < 0)
  (rxy : x ≤ y)
  (ryz : y ≤ z)
  (g1 : (a 0 + a 1 + a 2) * y + a 0 * (x - y) + a 2 * (z - y) = 0) :
  False := by
  have g2: (a 0 + a 1 + a 2) * y < 0 := by exact mul_neg_of_pos_of_neg h₄ hyp
  have g3: a 0 * (x-y) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
  have g4: a 2 * (z-y) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₁.2) (by linarith)
  linarith


lemma imo_1965_p2_61
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  -- (hyp : y < 0)
  -- (g1 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  (hzp : z < 0)
  -- (rxy : x ≤ y)
  (ryz : z < y) :
  False := by
  by_cases rxz: x ≤ z
    -- x <= z < y
  . have g2: (a 0 + a 1 + a 2) * z < 0 := by exact mul_neg_of_pos_of_neg h₄ hzp
    have g3: a 0 * (x-z) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
    have g4: a 1 * (y-z) < 0 := by
      exact mul_neg_of_neg_of_pos h₁.1 (by linarith)
    linarith
  . push_neg at rxz -- z < x <= y
    have g2: (a 6 + a 7 + a 8) * z < 0 := by exact mul_neg_of_pos_of_neg h₆ hzp
    have g3: a 6 * (x-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
    have g4: a 7 * (y-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.2 (by linarith)
    linarith


lemma imo_1965_p2_62
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  -- (hyp : y < 0)
  -- (g1 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  (hzp : z < 0)
  -- (rxy : x ≤ y)
  (ryz : z < y)
  (rxz : x ≤ z) :
  False := by
  have g2: (a 0 + a 1 + a 2) * z < 0 := by exact mul_neg_of_pos_of_neg h₄ hzp
  have g3: a 0 * (x-z) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
  have g4: a 1 * (y-z) < 0 := by
    exact mul_neg_of_neg_of_pos h₁.1 (by linarith)
  linarith


lemma imo_1965_p2_63
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  -- (hyp : y < 0)
  -- (g11 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  (hzp : z < 0)
  -- (rxy : x ≤ y)
  (ryz : z < y)
  (rxz : x ≤ z)
  (g1 : (a 0 + a 1 + a 2) * z + a 0 * (x - z) + a 1 * (y - z) = 0) :
  False := by
  have g2: (a 0 + a 1 + a 2) * z < 0 := by exact mul_neg_of_pos_of_neg h₄ hzp
  have g3: a 0 * (x-z) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.1) (by linarith)
  have g4: a 1 * (y-z) < 0 := by
    exact mul_neg_of_neg_of_pos h₁.1 (by linarith)
  linarith


lemma imo_1965_p2_64
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  -- (hyp : y < 0)
  -- (g1 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  (hzp : z < 0)
  (rxy : x ≤ y)
  -- (ryz : z < y)
  (rxz : z < x) :
  False := by
  have g2: (a 6 + a 7 + a 8) * z < 0 := by exact mul_neg_of_pos_of_neg h₆ hzp
  have g3: a 6 * (x-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
  have g4: a 7 * (y-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.2 (by linarith)
  linarith


lemma imo_1965_p2_65
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  -- (hyp : y < 0)
  -- (g11 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  (hzp : z < 0)
  -- (rxy : x ≤ y)
  (ryz : z < y)
  (rxz : z < x)
  (g1 : (a 6 + a 7 + a 8) * z + a 6 * (x - z) + a 7 * (y - z) = 0) :
  False := by
  have g2: (a 6 + a 7 + a 8) * z < 0 := by exact mul_neg_of_pos_of_neg h₆ hzp
  have g3: a 6 * (x-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
  have g4: a 7 * (y-z) < 0 := by exact mul_neg_of_neg_of_pos h₃.2 (by linarith)
  linarith


lemma imo_1965_p2_66
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  (hyp : y < 0)
  -- (g1 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  (hzp : z < 0)
  (rxy : y < x) :
  False := by
  by_cases rzy: z ≤ y
    -- z <= y < x
  . have g2: (a 6 + a 7 + a 8) * y < 0 := by exact mul_neg_of_pos_of_neg h₆ hyp
    have g3: a 6 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
    have g4: a 8 * (z-y) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.2.2) (by linarith)
    linarith
  . push_neg at rzy
    by_cases rzx: z ≤ x
      -- y < z <= x
    . have g2: (a 3 + a 4 + a 5) * z < 0 := by exact mul_neg_of_pos_of_neg h₅ hzp
      have g3: a 3 * (x-z) ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₂.1) (by linarith)
      have g4: a 4 * (y-z) < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 (by linarith)
      linarith
    . push_neg at rzx
      -- y < x < z
      have g2: (a 3 + a 4 + a 5) * y < 0 := by exact mul_neg_of_pos_of_neg h₅ hyp
      have g3: a 3 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.1 (by linarith)
      have g4: a 5 * (z-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.2 (by linarith)
      linarith


lemma imo_1965_p2_67
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  (hyp : y < 0)
  -- (g1 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  -- (hzp : z < 0)
  (rxy : y < x)
  (rzy : z ≤ y) :
  False := by
  have g2: (a 6 + a 7 + a 8) * y < 0 := by exact mul_neg_of_pos_of_neg h₆ hyp
  have g3: a 6 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
  have g4: a 8 * (z-y) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.2.2) (by linarith)
  linarith


lemma imo_1965_p2_68
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  -- (h₂ : a 3 < 0 ∧ a 5 < 0)
  (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  -- (h₅ : 0 < a 3 + a 4 + a 5)
  (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  (hyp : y < 0)
  -- (g11 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  -- (hzp : z < 0)
  (rxy : y < x)
  (rzy : z ≤ y)
  (g1 : (a 6 + a 7 + a 8) * y + a 6 * (x - y) + a 8 * (z - y) = 0) :
  False := by
  have g2: (a 6 + a 7 + a 8) * y < 0 := by exact mul_neg_of_pos_of_neg h₆ hyp
  have g3: a 6 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₃.1 (by linarith)
  have g4: a 8 * (z-y) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h₀.2.2) (by linarith)
  linarith


lemma imo_1965_p2_69
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  (hyp : y < 0)
  -- (g1 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  (hzp : z < 0)
  (rxy : y < x)
  (rzy : y < z) :
  False := by
  by_cases rzx: z ≤ x
    -- y < z <= x
  . have g2: (a 3 + a 4 + a 5) * z < 0 := by exact mul_neg_of_pos_of_neg h₅ hzp
    have g3: a 3 * (x-z) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₂.1) (by linarith)
    have g4: a 4 * (y-z) < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 (by linarith)
    linarith
  . push_neg at rzx
    -- y < x < z
    have g2: (a 3 + a 4 + a 5) * y < 0 := by exact mul_neg_of_pos_of_neg h₅ hyp
    have g3: a 3 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.1 (by linarith)
    have g4: a 5 * (z-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.2 (by linarith)
    linarith


lemma imo_1965_p2_70
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  -- (hyp : y < 0)
  -- (g1 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  (hzp : z < 0)
  -- (rxy : y < x)
  (rzy : y < z)
  (rzx : z ≤ x) :
  False := by
  have g2: (a 3 + a 4 + a 5) * z < 0 := by exact mul_neg_of_pos_of_neg h₅ hzp
  have g3: a 3 * (x-z) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₂.1) (by linarith)
  have g4: a 4 * (y-z) < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 (by linarith)
  linarith


lemma imo_1965_p2_71
  (x y z : ℝ)
  (a : ℕ → ℝ)
  (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  -- (hyp : y < 0)
  -- (g11 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  (hzp : z < 0)
  -- (rxy : y < x)
  (rzy : y < z)
  (rzx : z ≤ x)
  (g1 : (a 3 + a 4 + a 5) * z + a 3 * (x - z) + a 4 * (y - z) = 0) :
  False := by
  have g2: (a 3 + a 4 + a 5) * z < 0 := by exact mul_neg_of_pos_of_neg h₅ hzp
  have g3: a 3 * (x-z) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h₂.1) (by linarith)
  have g4: a 4 * (y-z) < 0 := by exact mul_neg_of_pos_of_neg h₀.2.1 (by linarith)
  linarith


lemma imo_1965_p2_72
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  (hyp : y < 0)
  -- (g1 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  -- (hzp : z < 0)
  (rxy : y < x)
  (rzy : y < z) :
  -- (rzx : x < z) :
  False := by
  have g2: (a 3 + a 4 + a 5) * y < 0 := by exact mul_neg_of_pos_of_neg h₅ hyp
  have g3: a 3 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.1 (by linarith)
  have g4: a 5 * (z-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.2 (by linarith)
  linarith


lemma imo_1965_p2_73
  (x y z : ℝ)
  (a : ℕ → ℝ)
  -- (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
  -- (h₁ : a 1 < 0 ∧ a 2 < 0)
  (h₂ : a 3 < 0 ∧ a 5 < 0)
  -- (h₃ : a 6 < 0 ∧ a 7 < 0)
  -- (h₄ : 0 < a 0 + a 1 + a 2)
  (h₅ : 0 < a 3 + a 4 + a 5)
  -- (h₆ : 0 < a 6 + a 7 + a 8)
  -- (h₇ : a 0 * x + a 1 * y + a 2 * z = 0)
  -- (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
  -- (h₉ : a 6 * x + a 7 * y + a 8 * z = 0)
  -- (hx0 : x ≠ 0)
  -- (hxp : x ≤ 0)
  -- (hxn : x < 0)
  (hyp : y < 0)
  -- (g11 : 0 < a 6 * x)
  -- (g2 : 0 < a 7 * y)
  -- (g3 : z * a 8 < 0)
  -- (hzp : z < 0)
  (rxy : y < x)
  (rzy : y < z)
  -- (rzx : x < z)
  (g1 : (a 3 + a 4 + a 5) * y + a 3 * (x - y) + a 5 * (z - y) = 0) :
  False := by
  have g2: (a 3 + a 4 + a 5) * y < 0 := by exact mul_neg_of_pos_of_neg h₅ hyp
  have g3: a 3 * (x-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.1 (by linarith)
  have g4: a 5 * (z-y) < 0 := by exact mul_neg_of_neg_of_pos h₂.2 (by linarith)
  linarith
