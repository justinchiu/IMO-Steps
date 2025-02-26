import Mathlib

set_option linter.unusedVariables.analyzeTactics true


lemma imo_1983_p6_1
  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: z ≤ y ∧ y ≤ x) :
  a * z + c * y + b * x ≤ c * z + b * y + a * x := by
  suffices h₄: c * (y - z) + b * (x - y) ≤ a * (x - z)
  . linarith
  . have h₅: c * (y - z) + b * (x - y) ≤ b * (y - z) + b * (x - y) := by
      simp
      refine mul_le_mul h₂.1 ?_ ?_ ?_
      . exact le_rfl
      . exact sub_nonneg_of_le h₃.1
      . exact le_of_lt h₀.2.1
    refine le_trans h₅ ?_
    rw [mul_sub, mul_sub, add_comm]
    rw [← add_sub_assoc, sub_add_cancel]
    rw [← mul_sub]
    refine mul_le_mul h₂.2 ?_ ?_ ?_
    . exact le_rfl
    . refine sub_nonneg_of_le ?_
      exact le_trans h₃.1 h₃.2
    . exact le_of_lt h₀.1



lemma imo_1983_p6_1_1
  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂ : c ≤ b ∧ b ≤ a)
  (h₃ : z ≤ y ∧ y ≤ x) :
  c * (y - z) + b * (x - y) ≤ a * (x - z) := by
  have h₅: c * (y - z) + b * (x - y) ≤ b * (y - z) + b * (x - y) := by
    simp
    refine mul_le_mul h₂.1 ?_ ?_ ?_
    . exact le_rfl
    . exact sub_nonneg_of_le h₃.1
    . exact le_of_lt h₀.2.1
  refine le_trans h₅ ?_
  rw [mul_sub, mul_sub, add_comm]
  rw [← add_sub_assoc, sub_add_cancel]
  rw [← mul_sub]
  refine mul_le_mul h₂.2 ?_ ?_ ?_
  . exact le_rfl
  . refine sub_nonneg_of_le ?_
    exact le_trans h₃.1 h₃.2
  . exact le_of_lt h₀.1


lemma imo_1983_p6_1_2
  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂ : c ≤ b ∧ b ≤ a)
  (h₃ : z ≤ y ∧ y ≤ x) :
  c * (y - z) + b * (x - y) ≤ b * (y - z) + b * (x - y) := by
  simp
  refine mul_le_mul h₂.1 ?_ ?_ ?_
  . exact le_rfl
  . exact sub_nonneg_of_le h₃.1
  . exact le_of_lt h₀.2.1


lemma imo_1983_p6_1_3
  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂ : c ≤ b ∧ b ≤ a)
  (h₃ : z ≤ y ∧ y ≤ x)
  (h₅ : c * (y - z) + b * (x - y) ≤ b * (y - z) + b * (x - y)) :
  c * (y - z) + b * (x - y) ≤ a * (x - z) := by
  refine le_trans h₅ ?_
  rw [mul_sub, mul_sub, add_comm]
  rw [← add_sub_assoc, sub_add_cancel]
  rw [← mul_sub]
  refine mul_le_mul h₂.2 ?_ ?_ ?_
  . exact le_rfl
  . refine sub_nonneg_of_le ?_
    exact le_trans h₃.1 h₃.2
  . exact le_of_lt h₀.1


lemma imo_1983_p6_1_4
  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂ : c ≤ b ∧ b ≤ a)
  (h₃ : z ≤ y ∧ y ≤ x) :
  -- (h₅ : c * (y - z) + b * (x - y) ≤ b * (y - z) + b * (x - y)) :
  b * (y - z) + b * (x - y) ≤ a * (x - z) := by
  rw [mul_sub, mul_sub, add_comm]
  rw [← add_sub_assoc, sub_add_cancel]
  rw [← mul_sub]
  refine mul_le_mul h₂.2 ?_ ?_ ?_
  . exact le_rfl
  . refine sub_nonneg_of_le ?_
    exact le_trans h₃.1 h₃.2
  . exact le_of_lt h₀.1


lemma imo_1983_p6_1_5
  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂ : c ≤ b ∧ b ≤ a)
  (h₃ : z ≤ y ∧ y ≤ x) :
  -- (h₅ : c * (y - z) + b * (x - y) ≤ b * (y - z) + b * (x - y)) :
  b * (x - z) ≤ a * (x - z) := by
  refine mul_le_mul h₂.2 ?_ ?_ ?_
  . exact le_rfl
  . refine sub_nonneg_of_le ?_
    exact le_trans h₃.1 h₃.2
  . exact le_of_lt h₀.1




lemma imo_1983_p6_2
  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: z ≤ y ∧ y ≤ x) :
  b * z + a * y + c * x ≤ c * z + b * y + a * x := by
  suffices h₄: c * (x - z) + b * (z - y) ≤ a * (x - y)
  . linarith
  . have h₅: c * (x - z) + b * (z - y) ≤ b * (x - z) + b * (z - y) := by
      simp
      refine mul_le_mul h₂.1 ?_ ?_ ?_
      . exact le_rfl
      . refine sub_nonneg_of_le ?_
        exact le_trans h₃.1 h₃.2
      . exact le_of_lt h₀.2.1
    refine le_trans h₅ ?_
    rw [mul_sub, mul_sub]
    rw [← add_sub_assoc, sub_add_cancel]
    rw [← mul_sub]
    refine mul_le_mul h₂.2 ?_ ?_ ?_
    . exact le_rfl
    . exact sub_nonneg_of_le h₃.2
    . exact le_of_lt h₀.1


lemma imo_1983_p6_2_1
  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂ : c ≤ b ∧ b ≤ a)
  (h₃ : z ≤ y ∧ y ≤ x) :
  c * (x - z) + b * (z - y) ≤ a * (x - y) := by
  have h₅: c * (x - z) + b * (z - y) ≤ b * (x - z) + b * (z - y) := by
    simp
    refine mul_le_mul h₂.1 ?_ ?_ ?_
    . exact le_rfl
    . refine sub_nonneg_of_le ?_
      exact le_trans h₃.1 h₃.2
    . exact le_of_lt h₀.2.1
  refine le_trans h₅ ?_
  rw [mul_sub, mul_sub]
  rw [← add_sub_assoc, sub_add_cancel]
  rw [← mul_sub]
  refine mul_le_mul h₂.2 ?_ ?_ ?_
  . exact le_rfl
  . exact sub_nonneg_of_le h₃.2
  . exact le_of_lt h₀.1


lemma imo_1983_p6_2_2
  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂ : c ≤ b ∧ b ≤ a)
  (h₃ : z ≤ y ∧ y ≤ x) :
  c * (x - z) + b * (z - y) ≤ b * (x - z) + b * (z - y) := by
  simp
  refine mul_le_mul h₂.1 ?_ ?_ ?_
  . exact le_rfl
  . refine sub_nonneg_of_le ?_
    exact le_trans h₃.1 h₃.2
  . exact le_of_lt h₀.2.1


lemma imo_1983_p6_2_3
  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂ : c ≤ b ∧ b ≤ a)
  (h₃ : z ≤ y ∧ y ≤ x) :
  c * (x - z) ≤ b * (x - z) := by
  refine mul_le_mul h₂.1 ?_ ?_ ?_
  . exact le_rfl
  . refine sub_nonneg_of_le ?_
    exact le_trans h₃.1 h₃.2
  . exact le_of_lt h₀.2.1


lemma imo_1983_p6_2_4
  -- (a b c : ℝ)
  (x y z : ℝ)
  -- (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  -- (h₂ : c ≤ b ∧ b ≤ a)
  (h₃ : z ≤ y ∧ y ≤ x) :
  0 ≤ x - z := by
  refine sub_nonneg_of_le ?_
  exact le_trans h₃.1 h₃.2


lemma imo_1983_p6_2_5
  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂ : c ≤ b ∧ b ≤ a)
  (h₃ : z ≤ y ∧ y ≤ x) :
  -- (h₅ : c * (x - z) + b * (z - y) ≤ b * (x - z) + b * (z - y)) :
  b * (x - z) + b * (z - y) ≤ a * (x - y) := by
  rw [mul_sub, mul_sub]
  rw [← add_sub_assoc, sub_add_cancel]
  rw [← mul_sub]
  refine mul_le_mul h₂.2 ?_ ?_ ?_
  . exact le_rfl
  . exact sub_nonneg_of_le h₃.2
  . exact le_of_lt h₀.1


lemma imo_1983_p6_2_6
  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂ : c ≤ b ∧ b ≤ a)
  (h₃ : z ≤ y ∧ y ≤ x) :
  -- (h₅ : c * (x - z) + b * (z - y) ≤ b * (x - z) + b * (z - y)) :
  b * (x - y) ≤ a * (x - y) := by
  refine mul_le_mul h₂.2 ?_ ?_ ?_
  . exact le_rfl
  . exact sub_nonneg_of_le h₃.2
  . exact le_of_lt h₀.1



lemma imo_1983_p6_3
  (a b c : ℝ)
  (hap : 0 < a )
  (hbp : 0 < b )
  (hcp : 0 < c )
  (h₁ : c < a + b)
  -- (h₂ : b < a + c)
  (h₃ : a < b + c)
  (hba: b ≤ a)
  (hcb: c ≤ b) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  have g₀: b * c ≤ a * c := by exact (mul_le_mul_iff_of_pos_right hcp).mpr hba
  have g₁: a * c ≤ a * b := by exact (mul_le_mul_iff_of_pos_left hap).mpr hcb
  have g₂: a * (b + c - a) ≤ b * (a + c - b) := by
    have g₂₁: 0 ≤ (a-b) * (a+b-c) := by
      refine mul_nonneg ?_ ?_
      . exact sub_nonneg_of_le hba
      . refine le_of_lt ?_
        exact sub_pos.mpr h₁
    linarith
  have g₃: b * (a + c - b) ≤ c * (a + b - c) := by
    have g₃₁: 0 ≤ (b - c) * (b + c - a) := by
      refine mul_nonneg ?_ ?_
      . exact sub_nonneg_of_le hcb
      . refine le_of_lt ?_
        exact sub_pos.mpr h₃
    linarith
  have g₄: (a * b) * (a * (b + c - a)) + (b * c) * (b * (a + c - b)) + (a * c) * (c * (a + b - c))
      ≤ (b * c) * (a * (b + c - a)) + (a * c) * (b * (a + c - b)) + (a * b) * (c * (a + b - c)) := by
    refine imo_1983_p6_1 (a * b) (a * c) (b * c) (c * (a + b - c)) (b * (a + c - b)) (a * (b + c - a)) ?_ ?_ ?_
    . constructor
      . exact mul_pos hap hbp
      . constructor
        . exact mul_pos hap hcp
        . exact mul_pos hbp hcp
    . exact { left := g₀, right := g₁ }
    . exact { left := g₂, right := g₃ }
  linarith


lemma imo_1983_p6_3_1
  (a b c : ℝ)
  -- (hap : 0 < a)
  -- (hbp : 0 < b)
  -- (hcp : 0 < c)
  (h₁ : c < a + b)
  -- (h₃ : a < b + c)
  (hba : b ≤ a) :
  -- (hcb : c ≤ b)
  -- (g₀ : b * c ≤ a * c)
  -- (g₁ : a * c ≤ a * b) :
  a * (b + c - a) ≤ b * (a + c - b) := by
  have g₂₁: 0 ≤ (a-b) * (a+b-c) := by
    refine mul_nonneg ?_ ?_
    . exact sub_nonneg_of_le hba
    . refine le_of_lt ?_
      exact sub_pos.mpr h₁
  linarith


lemma imo_1983_p6_3_2
  (a b c : ℝ)
  -- (hap : 0 < a)
  -- (hbp : 0 < b)
  -- (hcp : 0 < c)
  -- (h₁ : c < a + b)
  (h₃ : a < b + c)
  -- (hba : b ≤ a)
  (hcb : c ≤ b) :
  -- (g₀ : b * c ≤ a * c)
  -- (g₁ : a * c ≤ a * b)
  -- (g₂ : a * (b + c - a) ≤ b * (a + c - b)) :
  b * (a + c - b) ≤ c * (a + b - c) := by
  have g₃: b * (a + c - b) ≤ c * (a + b - c) := by
    have g₃₁: 0 ≤ (b - c) * (b + c - a) := by
      refine mul_nonneg ?_ ?_
      . exact sub_nonneg_of_le hcb
      . refine le_of_lt ?_
        exact sub_pos.mpr h₃
    linarith
  linarith


lemma imo_1983_p6_3_3
  (a b c : ℝ)
  (hap : 0 < a)
  (hbp : 0 < b)
  (hcp : 0 < c)
  -- (h₁ : c < a + b)
  -- (h₃ : a < b + c)
  -- (hba : b ≤ a)
  -- (hcb : c ≤ b)
  (g₀ : b * c ≤ a * c)
  (g₁ : a * c ≤ a * b)
  (g₂ : a * (b + c - a) ≤ b * (a + c - b))
  (g₃ : b * (a + c - b) ≤ c * (a + b - c)) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  have g₄: (a * b) * (a * (b + c - a)) + (b * c) * (b * (a + c - b)) + (a * c) * (c * (a + b - c))
      ≤ (b * c) * (a * (b + c - a)) + (a * c) * (b * (a + c - b)) + (a * b) * (c * (a + b - c)) := by
    refine imo_1983_p6_1 (a * b) (a * c) (b * c) (c * (a + b - c)) (b * (a + c - b)) (a * (b + c - a)) ?_ ?_ ?_
    . constructor
      . exact mul_pos hap hbp
      . constructor
        . exact mul_pos hap hcp
        . exact mul_pos hbp hcp
    . exact { left := g₀, right := g₁ }
    . exact { left := g₂, right := g₃ }
  linarith


lemma imo_1983_p6_3_4
  (a b c : ℝ)
  (hap : 0 < a)
  (hbp : 0 < b)
  (hcp : 0 < c)
  -- (h₁ : c < a + b)
  -- (h₃ : a < b + c)
  -- (hba : b ≤ a)
  -- (hcb : c ≤ b)
  (g₀ : b * c ≤ a * c)
  (g₁ : a * c ≤ a * b)
  (g₂ : a * (b + c - a) ≤ b * (a + c - b))
  (g₃ : b * (a + c - b) ≤ c * (a + b - c)) :
  a * b * (a * (b + c - a)) + b * c * (b * (a + c - b)) + a * c * (c * (a + b - c)) ≤
    b * c * (a * (b + c - a)) + a * c * (b * (a + c - b)) + a * b * (c * (a + b - c)) := by
  refine imo_1983_p6_1 (a * b) (a * c) (b * c) (c * (a + b - c)) (b * (a + c - b)) (a * (b + c - a)) ?_ ?_ ?_
  . constructor
    . exact mul_pos hap hbp
    . constructor
      . exact mul_pos hap hcp
      . exact mul_pos hbp hcp
  . exact { left := g₀, right := g₁ }
  . exact { left := g₂, right := g₃ }



lemma imo_1983_p6_4
  (a b c : ℝ)
  (hap : 0 < a )
  (hbp : 0 < b )
  (hcp : 0 < c )
  (h₁ : c < a + b)
  -- (h₂ : b < a + c)
  (h₃ : a < b + c)
  (hba: b ≤ a)
  (hcb: c ≤ b) :
  0 ≤ a^2 * c * (a - c) + c^2 * b * (c - b) + b^2 * a * (b - a) := by
  have g₀: b * c ≤ a * c := by exact (mul_le_mul_iff_of_pos_right hcp).mpr hba
  have g₁: a * c ≤ a * b := by exact (mul_le_mul_iff_of_pos_left hap).mpr hcb
  have g₂: a * (b + c - a) ≤ b * (a + c - b) := by
    have g₂₁: 0 ≤ (a-b) * (a+b-c) := by
      refine mul_nonneg ?_ ?_
      . exact sub_nonneg_of_le hba
      . refine le_of_lt ?_
        exact sub_pos.mpr h₁
    linarith
  have g₃: b * (a + c - b) ≤ c * (a + b - c) := by
    have g₃₁: 0 ≤ (b - c) * (b + c - a) := by
      refine mul_nonneg ?_ ?_
      . exact sub_nonneg_of_le hcb
      . refine le_of_lt ?_
        exact sub_pos.mpr h₃
    linarith
  have g₄: (a * c) * (a * (b + c - a)) + (a * b) * (b * (a + c - b)) + (b * c) * (c * (a + b - c))
      ≤ (b * c) * (a * (b + c - a)) + (a * c) * (b * (a + c - b)) + (a * b) * (c * (a + b - c)) := by
    refine imo_1983_p6_2 (a * b) (a * c) (b * c) (c * (a + b - c)) (b * (a + c - b)) (a * (b + c - a)) ?_ ?_ ?_
    . constructor
      . exact mul_pos hap hbp
      . constructor
        . exact mul_pos hap hcp
        . exact mul_pos hbp hcp
    . exact { left := g₀, right := g₁ }
    . exact { left := g₂, right := g₃ }
  linarith


lemma imo_1983_p6_4_1
  (a b c : ℝ)
  (hap : 0 < a)
  (hbp : 0 < b)
  (hcp : 0 < c)
  (h₁ : c < a + b)
  (h₃ : a < b + c)
  (hba : b ≤ a)
  (hcb : c ≤ b)
  (g₀ : b * c ≤ a * c)
  (g₁ : a * c ≤ a * b) :
  0 ≤ a ^ 2 * c * (a - c) + c ^ 2 * b * (c - b) + b ^ 2 * a * (b - a) := by
  have g₂: a * (b + c - a) ≤ b * (a + c - b) := by
    have g₂₁: 0 ≤ (a-b) * (a+b-c) := by
      refine mul_nonneg ?_ ?_
      . exact sub_nonneg_of_le hba
      . refine le_of_lt ?_
        exact sub_pos.mpr h₁
    linarith
  have g₃: b * (a + c - b) ≤ c * (a + b - c) := by
    have g₃₁: 0 ≤ (b - c) * (b + c - a) := by
      refine mul_nonneg ?_ ?_
      . exact sub_nonneg_of_le hcb
      . refine le_of_lt ?_
        exact sub_pos.mpr h₃
    linarith
  have g₄: (a * c) * (a * (b + c - a)) + (a * b) * (b * (a + c - b)) + (b * c) * (c * (a + b - c))
      ≤ (b * c) * (a * (b + c - a)) + (a * c) * (b * (a + c - b)) + (a * b) * (c * (a + b - c)) := by
    refine imo_1983_p6_2 (a * b) (a * c) (b * c) (c * (a + b - c)) (b * (a + c - b)) (a * (b + c - a)) ?_ ?_ ?_
    . constructor
      . exact mul_pos hap hbp
      . constructor
        . exact mul_pos hap hcp
        . exact mul_pos hbp hcp
    . exact { left := g₀, right := g₁ }
    . exact { left := g₂, right := g₃ }
  linarith


lemma imo_1983_p6_4_2
  (a b c : ℝ)
  (hap : 0 < a)
  (hbp : 0 < b)
  (hcp : 0 < c)
  -- (h₁ : c < a + b)
  (h₃ : a < b + c)
  -- (hba : b ≤ a)
  (hcb : c ≤ b)
  (g₀ : b * c ≤ a * c)
  (g₁ : a * c ≤ a * b)
  (g₂ : a * (b + c - a) ≤ b * (a + c - b)) :
  0 ≤ a ^ 2 * c * (a - c) + c ^ 2 * b * (c - b) + b ^ 2 * a * (b - a) := by
  have g₃: b * (a + c - b) ≤ c * (a + b - c) := by
    have g₃₁: 0 ≤ (b - c) * (b + c - a) := by
      refine mul_nonneg ?_ ?_
      . exact sub_nonneg_of_le hcb
      . refine le_of_lt ?_
        exact sub_pos.mpr h₃
    linarith
  have g₄: (a * c) * (a * (b + c - a)) + (a * b) * (b * (a + c - b)) + (b * c) * (c * (a + b - c))
      ≤ (b * c) * (a * (b + c - a)) + (a * c) * (b * (a + c - b)) + (a * b) * (c * (a + b - c)) := by
    refine imo_1983_p6_2 (a * b) (a * c) (b * c) (c * (a + b - c)) (b * (a + c - b)) (a * (b + c - a)) ?_ ?_ ?_
    . constructor
      . exact mul_pos hap hbp
      . constructor
        . exact mul_pos hap hcp
        . exact mul_pos hbp hcp
    . exact { left := g₀, right := g₁ }
    . exact { left := g₂, right := g₃ }
  linarith


lemma imo_1983_p6_4_3
  (a b c : ℝ)
  (hap : 0 < a)
  (hbp : 0 < b)
  (hcp : 0 < c)
  -- (h₁ : c < a + b)
  -- (h₃ : a < b + c)
  -- (hba : b ≤ a)
  -- (hcb : c ≤ b)
  (g₀ : b * c ≤ a * c)
  (g₁ : a * c ≤ a * b)
  (g₂ : a * (b + c - a) ≤ b * (a + c - b))
  (g₃ : b * (a + c - b) ≤ c * (a + b - c)) :
  0 ≤ a ^ 2 * c * (a - c) + c ^ 2 * b * (c - b) + b ^ 2 * a * (b - a) := by
  have g₄: (a * c) * (a * (b + c - a)) + (a * b) * (b * (a + c - b)) + (b * c) * (c * (a + b - c))
      ≤ (b * c) * (a * (b + c - a)) + (a * c) * (b * (a + c - b)) + (a * b) * (c * (a + b - c)) := by
    refine imo_1983_p6_2 (a * b) (a * c) (b * c) (c * (a + b - c)) (b * (a + c - b)) (a * (b + c - a)) ?_ ?_ ?_
    . constructor
      . exact mul_pos hap hbp
      . constructor
        . exact mul_pos hap hcp
        . exact mul_pos hbp hcp
    . exact { left := g₀, right := g₁ }
    . exact { left := g₂, right := g₃ }
  linarith


lemma imo_1983_p6_4_4
  (a b c : ℝ)
  -- (hap : 0 < a)
  -- (hbp : 0 < b)
  -- (hcp : 0 < c)
  (h₁ : c < a + b)
  -- (h₃ : a < b + c)
  (hba : b ≤ a) :
  -- (hcb : c ≤ b)
  -- (g₀ : b * c ≤ a * c)
  -- (g₁ : a * c ≤ a * b) :
  a * (b + c - a) ≤ b * (a + c - b) := by
  have g₂₁: 0 ≤ (a-b) * (a+b-c) := by
    refine mul_nonneg ?_ ?_
    . exact sub_nonneg_of_le hba
    . refine le_of_lt ?_
      exact sub_pos.mpr h₁
  linarith


lemma imo_1983_p6_4_5
  (a b c : ℝ)
  -- (hap : 0 < a)
  -- (hbp : 0 < b)
  -- (hcp : 0 < c)
  (h₁ : c < a + b)
  -- (h₃ : a < b + c)
  (hba : b ≤ a) :
  -- (hcb : c ≤ b)
  -- (g₀ : b * c ≤ a * c)
  -- (g₁ : a * c ≤ a * b) :
  0 ≤ (a - b) * (a + b - c) := by
  refine mul_nonneg ?_ ?_
  . exact sub_nonneg_of_le hba
  . refine le_of_lt ?_
    exact sub_pos.mpr h₁


lemma imo_1983_p6_4_6
  (a b c : ℝ)
  -- (hap : 0 < a)
  -- (hbp : 0 < b)
  -- (hcp : 0 < c)
  -- (h₁ : c < a + b)
  (h₃ : a < b + c)
  -- (hba : b ≤ a)
  (hcb : c ≤ b) :
  -- (g₀ : b * c ≤ a * c)
  -- (g₁ : a * c ≤ a * b)
  -- (g₂ : a * (b + c - a) ≤ b * (a + c - b)) :
  b * (a + c - b) ≤ c * (a + b - c) := by
  have g₃₁: 0 ≤ (b - c) * (b + c - a) := by
    refine mul_nonneg ?_ ?_
    . exact sub_nonneg_of_le hcb
    . refine le_of_lt ?_
      exact sub_pos.mpr h₃
  linarith


lemma imo_1983_p6_4_7
  (a b c : ℝ)
  -- (hap : 0 < a)
  -- (hbp : 0 < b)
  -- (hcp : 0 < c)
  -- (h₁ : c < a + b)
  (h₃ : a < b + c)
  -- (hba : b ≤ a)
  (hcb : c ≤ b) :
  -- (g₀ : b * c ≤ a * c)
  -- (g₁ : a * c ≤ a * b)
  -- (g₂ : a * (b + c - a) ≤ b * (a + c - b)) :
  0 ≤ (b - c) * (b + c - a) := by
  refine mul_nonneg ?_ ?_
  . exact sub_nonneg_of_le hcb
  . refine le_of_lt ?_
    exact sub_pos.mpr h₃


lemma imo_1983_p6_4_8
  (a b c : ℝ)
  (hap : 0 < a)
  (hbp : 0 < b)
  (hcp : 0 < c)
  -- (h₁ : c < a + b)
  -- (h₃ : a < b + c)
  -- (hba : b ≤ a)
  -- (hcb : c ≤ b)
  (g₀ : b * c ≤ a * c)
  (g₁ : a * c ≤ a * b)
  (g₂ : a * (b + c - a) ≤ b * (a + c - b))
  (g₃ : b * (a + c - b) ≤ c * (a + b - c)) :
  a * c * (a * (b + c - a)) + a * b * (b * (a + c - b)) + b * c * (c * (a + b - c)) ≤
    b * c * (a * (b + c - a)) + a * c * (b * (a + c - b)) + a * b * (c * (a + b - c)) := by
  refine imo_1983_p6_2 (a * b) (a * c) (b * c) (c * (a + b - c)) (b * (a + c - b)) (a * (b + c - a)) ?_ ?_ ?_
  . constructor
    . exact mul_pos hap hbp
    . constructor
      . exact mul_pos hap hcp
      . exact mul_pos hbp hcp
  . exact { left := g₀, right := g₁ }
  . exact { left := g₂, right := g₃ }


lemma imo_1983_p6_5_1
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c)
  (ho₀ : a < b)
  (ho₁ : b < c) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  rw [add_comm] at h₁ h₂ h₃
  have g₀: 0 ≤ c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) := by
    exact imo_1983_p6_4 c b a h₀.2.2 h₀.2.1 h₀.1 h₃ h₁ (le_of_lt ho₁) (le_of_lt ho₀)
  linarith


lemma imo_1983_p6_5_2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c)
  (ho₀ : a < b)
  (ho₁ : c ≤ b)
  (ho₂ : a < c) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  rw [add_comm] at h₁ h₂
  have g₀: 0 ≤ b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) := by
    exact imo_1983_p6_3 b c a h₀.2.1 h₀.2.2 h₀.1 h₃ h₂ ho₁ (le_of_lt ho₂)
  linarith


lemma imo_1983_p6_5_3
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c)
  (ho₀ : a < b)
  (ho₁ : c ≤ b)
  (ho₂ : c ≤ a) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  rw [add_comm] at h₁
  have g₀: 0 ≤ b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) := by
    exact imo_1983_p6_4 b a c h₀.2.1 h₀.1 h₀.2.2 h₁ h₂ (le_of_lt ho₀) ho₂
  linarith


lemma imo_1983_p6_5_4
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c)
  (ho₀ : b ≤ a)
  (ho₁ : b < c)
  (ho₂ : a < c) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  rw [add_comm] at h₂ h₃
  have g₀: 0 ≤ c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) := by
    exact imo_1983_p6_3 c a b h₀.2.2 h₀.1 h₀.2.1 h₂ h₁ (le_of_lt ho₂) ho₀
  linarith


lemma imo_1983_p6_5_5
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  -- (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c)
  (ho₀ : b ≤ a)
  (ho₁ : b < c)
  (ho₂ : c ≤ a) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  rw [add_comm] at h₃
  exact imo_1983_p6_4 a c b h₀.1 h₀.2.2 h₀.2.1 h₂ h₃ ho₂ (le_of_lt ho₁)


lemma imo_1983_p6_5_6
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c)
  (ho₀ : a < b) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  wlog ho₁: c ≤ b generalizing a b c
  . clear this
    push_neg at ho₁ -- a < b < c
    rw [add_comm] at h₁ h₂ h₃
    have g₀: 0 ≤ c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) := by
      exact imo_1983_p6_4 c b a h₀.2.2 h₀.2.1 h₀.1 h₃ h₁ (le_of_lt ho₁) (le_of_lt ho₀)
    linarith
  . wlog ho₂: c ≤ a generalizing a b c
    . clear this -- a < c ≤ b
      push_neg at ho₂
      rw [add_comm] at h₁ h₂
      have g₀: 0 ≤ b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) := by
        exact imo_1983_p6_3 b c a h₀.2.1 h₀.2.2 h₀.1 h₃ h₂ ho₁ (le_of_lt ho₂)
      linarith
    . -- c ≤ a < b
      rw [add_comm] at h₁
      have g₀: 0 ≤ b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) := by
        exact imo_1983_p6_4 b a c h₀.2.1 h₀.1 h₀.2.2 h₁ h₂ (le_of_lt ho₀) ho₂
      linarith


lemma imo_1983_p6_5_7
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c)
  (ho₀ : a < b)
  (ho₁ : c ≤ b) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  wlog ho₂: c ≤ a generalizing a b c
  . clear this -- a < c ≤ b
    push_neg at ho₂
    rw [add_comm] at h₁ h₂
    have g₀: 0 ≤ b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) := by
      exact imo_1983_p6_3 b c a h₀.2.1 h₀.2.2 h₀.1 h₃ h₂ ho₁ (le_of_lt ho₂)
    linarith
  . -- c ≤ a < b
    rw [add_comm] at h₁
    have g₀: 0 ≤ b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) := by
      exact imo_1983_p6_4 b a c h₀.2.1 h₀.1 h₀.2.2 h₁ h₂ (le_of_lt ho₀) ho₂
    linarith


lemma imo_1983_p6_5_8
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c)
  (ho₀ : b ≤ a) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  wlog ho₁: c ≤ b generalizing a b c
  . clear this
    push_neg at ho₁
    wlog ho₂: c ≤ a generalizing a b c
    . clear this
      push_neg at ho₂ -- b < a < c
      rw [add_comm] at h₂ h₃
      have g₀: 0 ≤ c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) := by
        exact imo_1983_p6_3 c a b h₀.2.2 h₀.1 h₀.2.1 h₂ h₁ (le_of_lt ho₂) ho₀
      linarith
    . rw [add_comm] at h₃
      exact imo_1983_p6_4 a c b h₀.1 h₀.2.2 h₀.2.1 h₂ h₃ ho₂ (le_of_lt ho₁)
  . exact imo_1983_p6_3 a b c h₀.1 h₀.2.1 h₀.2.2 h₁ h₃ ho₀ ho₁



lemma imo_1983_p6_5_9
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c)
  (ho₀ : b ≤ a)
  (ho₁ : b < c) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  wlog ho₂: c ≤ a generalizing a b c
  . clear this
    push_neg at ho₂ -- b < a < c
    rw [add_comm] at h₂ h₃
    have g₀: 0 ≤ c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) := by
      exact imo_1983_p6_3 c a b h₀.2.2 h₀.1 h₀.2.1 h₂ h₁ (le_of_lt ho₂) ho₀
    linarith
  . rw [add_comm] at h₃
    exact imo_1983_p6_4 a c b h₀.1 h₀.2.2 h₀.2.1 h₂ h₃ ho₂ (le_of_lt ho₁)


lemma imo_1983_p6_6
  (a b c : ℝ)
  -- (hap : 0 < a )
  -- (hbp : 0 < b )
  (hcp : 0 < c )
  -- (h₁ : c < a + b)
  -- (h₂ : b < a + c)
  -- (h₃ : a < b + c)
  (hba: b ≤ a)
  (hcb: c ≤ b) :
  a^2 * c * (a - c) + c^2 * b * (c - b) + b^2 * a * (b - a) ≤
      a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  have h₄ : 0 ≤ (a + b + c) * (a - b) * (a - c) * (b - c) := by
    refine mul_nonneg ?_ (by linarith)
    refine mul_nonneg ?_ (by linarith)
    refine mul_nonneg ?_ (by linarith)
    linarith
  linarith


-- give the tight as a hypothesis, use it to prove each of the 6 cases
lemma imo_1983_p6_7_1
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  -- (h₂ : b < a + c)
  (h₃ : a < b + c)
  (ho₀ : a < b)
  (ho₁ : b < c)
  (ht : ∀ a b c :ℝ, (0 < a ∧ 0 < b ∧ 0 < c) → (c < a + b ∧ a < b + c) → (c ≤ b ∧ b ≤ a)
      → 0 ≤ a^2 * c * (a - c) + c^2 * b * (c - b) + b^2 * a * (b - a)) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  have h₄: 0 ≤ c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) := by
    refine ht c b a ?_ ?_ ?_
    . simp_all only [and_self]
    . constructor
      . rw [add_comm]
        exact h₃
      . rw [add_comm]
        exact h₁
    . constructor
      . exact le_of_lt ho₀
      . exact le_of_lt ho₁
  linarith


lemma imo_1983_p6_7_2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  -- (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c)
  -- (ho₀ : a < b)
  (ho₁ : c ≤ b)
  (ho₂ : a < c)
  (ht : ∀ a b c :ℝ, (0 < a ∧ 0 < b ∧ 0 < c) → (c < a + b ∧ a < b + c) → (c ≤ b ∧ b ≤ a)
      → 0 ≤ a^2 * c * (a - c) + c^2 * b * (c - b) + b^2 * a * (b - a)) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  have h₄: 0 ≤ b ^ 2 * a * (b - a) + a ^ 2 * c * (a - c) + c ^ 2 * b * (c - b) := by
    refine ht b c a ?_ ?_ ?_
    . simp_all only [and_self]
    . constructor
      . exact h₃
      . rw [add_comm]
        exact h₂
    . constructor
      . exact le_of_lt ho₂
      . exact ho₁
  refine le_trans h₄ ?_
  have h₅: b ^ 2 * a * (b - a) + a ^ 2 * c * (a - c) + c ^ 2 * b * (c - b) ≤
    b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) := by
    rw [add_comm] at h₂
    refine imo_1983_p6_6 b c a h₀.1 ho₁ ?_
    exact le_of_lt ho₂
  linarith


lemma imo_1983_p6_7_3
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  -- (h₃ : a < b + c)
  (ho₀ : a < b)
  -- (ho₁ : c ≤ b)
  (ho₂ : c ≤ a)
  (ht : ∀ a b c :ℝ, (0 < a ∧ 0 < b ∧ 0 < c) → (c < a + b ∧ a < b + c) → (c ≤ b ∧ b ≤ a)
      → 0 ≤ a^2 * c * (a - c) + c^2 * b * (c - b) + b^2 * a * (b - a)) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  have h₄: 0 ≤ b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) := by
    refine ht b a c ?_ ?_ ?_
    . simp_all only [and_self]
    . constructor
      . rw [add_comm]
        exact h₁
      . exact h₂
    . constructor
      . exact ho₂
      . exact le_of_lt ho₀
  linarith


lemma imo_1983_p6_7_4
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  -- (h₃ : a < b + c)
  (ho₀ : b ≤ a)
  -- (ho₁ : b < c)
  (ho₂ : a < c)
  (ht : ∀ a b c :ℝ, (0 < a ∧ 0 < b ∧ 0 < c) → (c < a + b ∧ a < b + c) → (c ≤ b ∧ b ≤ a)
      → 0 ≤ a^2 * c * (a - c) + c^2 * b * (c - b) + b^2 * a * (b - a)) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  have h₄: 0 ≤ c ^ 2 * b * (c - b) + b ^ 2 * a * (b - a) + a ^ 2 * c * (a - c) := by
    refine ht c a b ?_ ?_ ?_
    . simp_all only [and_self]
    . constructor
      . rw [add_comm]
        exact h₂
      . exact h₁
    . constructor
      . exact ho₀
      . exact le_of_lt ho₂
  refine le_trans h₄ ?_
  have h₅: c ^ 2 * b * (c - b) + b ^ 2 * a * (b - a) + a ^ 2 * c * (a - c) ≤
    c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) := by
    rw [add_comm] at h₂
    refine imo_1983_p6_6 c a b h₀.2.1 ?_ ho₀
    exact le_of_lt ho₂
  linarith


lemma imo_1983_p6_7_5
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  -- (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c)
  -- (ho₀ : b ≤ a)
  (ho₁ : b < c)
  (ho₂ : c ≤ a)
  (ht : ∀ a b c :ℝ, (0 < a ∧ 0 < b ∧ 0 < c) → (c < a + b ∧ a < b + c) → (c ≤ b ∧ b ≤ a)
      → 0 ≤ a^2 * c * (a - c) + c^2 * b * (c - b) + b^2 * a * (b - a)) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  refine ht a c b ?_ ?_ ?_
  . simp_all only [and_self]
  . simp_all only [true_and]
    rw [add_comm]
    exact h₃
  . constructor
    . exact le_of_lt ho₁
    . exact ho₂


lemma imo_1983_p6_7_6
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  -- (h₂ : b < a + c)
  (h₃ : a < b + c)
  (ho₀ : b ≤ a)
  (ho₁ : c ≤ b)
  (ht : ∀ a b c :ℝ, (0 < a ∧ 0 < b ∧ 0 < c) → (c < a + b ∧ a < b + c) → (c ≤ b ∧ b ≤ a)
      → 0 ≤ a^2 * c * (a - c) + c^2 * b * (c - b) + b^2 * a * (b - a)) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  have h₄: 0 ≤ a^2 * c * (a - c) + c^2 * b * (c - b) + b^2 * a * (b - a) := by
    refine ht a b c h₀ ?_ ?_
    . simp_all only [true_and]
    . constructor
      . exact ho₁
      . exact ho₀
  refine le_trans h₄ ?_
  refine imo_1983_p6_6 a b c h₀.2.2 ho₀ ho₁


lemma imo_1983_p6_8_1
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  -- (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c)
  -- (ho₀ : a < b)
  (ho₁ : c ≤ b)
  (ho₂ : a < c)
  (ht : ∀ a b c :ℝ, (0 < a ∧ 0 < b ∧ 0 < c) → (c < a + b ∧ a < b + c) → (c ≤ b ∧ b ≤ a)
      → 0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a)) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  have h₄: 0 ≤ b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) := by
    refine ht b c a ?_ ?_ ?_
    . exact and_rotate.mp h₀
    . simp_all only [true_and]
      linarith
    . constructor
      . exact le_of_lt ho₂
      . exact ho₁
  linarith


lemma imo_1983_p6_8_2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  -- (h₃ : a < b + c)
  (ho₀ : b ≤ a)
  -- (ho₁ : b < c)
  (ho₂ : a < c)
  (ht : ∀ a b c :ℝ, (0 < a ∧ 0 < b ∧ 0 < c) → (c < a + b ∧ a < b + c) → (c ≤ b ∧ b ≤ a)
      → 0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a)) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  have h₄: 0 ≤ c ^ 2 * a * (c - a) + a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) := by
    refine ht c a b ?_ ?_ ?_
    . exact and_rotate.mp (and_rotate.mp h₀)
    . constructor
      . rw [add_comm]
        exact h₂
      . exact h₁
    . constructor
      . exact ho₀
      . exact le_of_lt ho₂
  linarith


lemma imo_1983_p6_8_3
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  -- (h₂ : b < a + c)
  (h₃ : a < b + c)
  (ho₀ : b ≤ a)
  (ho₁ : c ≤ b)
  (ht : ∀ a b c :ℝ, (0 < a ∧ 0 < b ∧ 0 < c) → (c < a + b ∧ a < b + c) → (c ≤ b ∧ b ≤ a)
      → 0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a)) :
  0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  refine ht a b c h₀ ?_ ?_
  . simp_all only [true_and]
  . constructor
    . exact ho₁
    . exact ho₀


lemma mylemma_1x
  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  -- (h₁ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: x ≤ y ∧ y ≤ z) :
  x / c + y / a + z / b ≤ x / a + y / b + z / c := by
  have g3: (z - x) / b ≤ (z - x) / c := by
    have g31: 0 ≤ (z-x) := by
      refine sub_nonneg_of_le ?_
      exact le_trans h₃.1 h₃.2
    exact div_le_div_of_nonneg_left g31 (by linarith) h₂.1
  have g4: (y-x)/a + (z-y)/b ≤ (z-x)/b := by
    have g41: (y-x)/a + (z-y)/b ≤ (y-x)/b + (z-y)/b := by
      rw [add_le_add_iff_right ((z-y)/b)]
      have g411: 0 ≤ (y-x) := by linarith
      exact div_le_div_of_nonneg_left g411 (by linarith) h₂.2
    have g42: (y-x)/b + (z-y)/b = (z-x)/b := by ring
    linarith
  have g5: (y-x)/a + (z-y)/b ≤ (z-x)/c := by
    exact le_trans g4 g3
  ring_nf at g5
  ring_nf
  linarith


lemma my_lemma_2x
  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  -- (h₁ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: x ≤ y ∧ y ≤ z) :
  x/c + y/a + z/b ≤ x/a + y/b + z/c := by
  have g3: (z-x)/b ≤ (z-x)/c := by
    have g31: 0 ≤ (z-x) := by linarith
    exact div_le_div_of_nonneg_left g31 (by linarith) h₂.1
  have g4: (y-x)/a + (z-y)/b ≤ (z-x)/b := by
      have g41: (y-x)/a + (z-y)/b ≤ (y-x)/b + (z-y)/b := by
          rw [add_le_add_iff_right ((z-y)/b)]
          have g411: 0 ≤ (y-x) := by linarith
          exact div_le_div_of_nonneg_left g411 (by linarith) h₂.2
      have g42: (y-x)/b + (z-y)/b = (z-x)/b := by ring_nf
      linarith
  have g5: (y-x)/a + (z-y)/b ≤ (z-x)/c := by exact le_trans g4 g3
  ring_nf at g5
  ring_nf
  linarith


lemma my_lemma_3x
  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  -- (h₁ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: x ≤ y ∧ y ≤ z) :
  x/b + y/c + z/a ≤ x/a + y/b + z/c := by
  have g3: (z-y)/b ≤ (z-y)/c := by
    have g31: 0 ≤ (z-y) := by linarith
    exact div_le_div_of_nonneg_left g31 (by linarith) h₂.1
  have g4: (x-y)/b + (z-x)/a ≤ (z-y)/b := by
      have g41: (x-y)/b + (z-x)/a ≤ (x-y)/b + (z-x)/b := by
          rw [add_le_add_iff_left ((x-y)/b)]
          have g411: 0 ≤ (z-x) := by linarith
          exact div_le_div_of_nonneg_left g411 (by linarith) h₂.2
      have g42: (x-y)/b + (z-x)/b = (z-y)/b := by ring_nf
      linarith
  have g5: (x-y)/b + (z-x)/a ≤ (z-y)/c := by
    exact le_trans g4 g3
  ring_nf at g5
  ring_nf
  linarith


lemma my_lemma_4x
  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  -- (h₁ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: x ≤ y ∧ y ≤ z) :
  x/b + y/a + z/c ≤ x/a + y/b + z/c := by
  rw [add_le_add_iff_right (z/c)]
  have g2: (y-x)/a ≤ (y-x)/b := by
    exact div_le_div_of_nonneg_left (by linarith) h₀.2.1 h₂.2
  rw [sub_div] at g2
  rw [sub_div] at g2
  linarith


lemma my_lemma_5x
  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  -- (h₁ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: x ≤ y ∧ y ≤ z) :
  x/a + y/c + z/b ≤ x/a + y/b + z/c := by
  rw [add_assoc (x/a)]
  rw [add_assoc (x/a)]
  rw [add_le_add_iff_left (x/a)]
  have g1: (z-y)/b ≤ (z-y)/c := by
    exact div_le_div_of_nonneg_left (by linarith) h₀.2.2 h₂.1
  rw [sub_div] at g1
  rw [sub_div] at g1
  linarith


lemma my_lemma_6x
  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  -- (h₁ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: x ≤ y ∧ y ≤ z) :
  x/c + y/b + z/a ≤ x/a + y/b + z/c := by
  have g1: (z-x)/a ≤ (z-x)/c := by
    exact div_le_div_of_nonneg_left (by linarith) h₀.2.2 (by linarith)
  have g2: x/c + z/a ≤ x/a + z/c := by
    rw [sub_div] at g1
    rw [sub_div] at g1
    linarith
  linarith


lemma mylemma_7x
  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: x ≤ y ∧ y ≤ z) :
  x / c + y / a + z / b ≤ x / a + y / b + z / c := by
  have g3: (z - x) / b ≤ (z - x) / c := by
    have g31: 0 ≤ (z-x) := by
      refine sub_nonneg_of_le ?_
      exact le_trans h₃.1 h₃.2
    exact div_le_div_of_nonneg_left g31 (by linarith) h₂.1
  have g4: (y-x)/a + (z-y)/b ≤ (z-x)/b := by
    have g41: (y-x)/a + (z-y)/b ≤ (y-x)/b + (z-y)/b := by
      rw [add_le_add_iff_right ((z-y)/b)]
      have g411: 0 ≤ (y-x) := by linarith
      exact div_le_div_of_nonneg_left g411 (by linarith) h₂.2
    have g42: (y-x)/b + (z-y)/b = (z-x)/b := by ring
    linarith
  have g5: (y-x)/a + (z-y)/b ≤ (z-x)/c := by
    exact le_trans g4 g3
  ring_nf at g5
  ring_nf
  linarith
