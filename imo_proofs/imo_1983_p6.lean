import ImoSteps

open Real

lemma rearrangement_lemma
  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: z ≤ y ∧ y ≤ x) :
  a * z + c * y + b * x ≤ c * z + b * y + a * x := by
  have h₄: c * (y - z) + b * (x - y) ≤ a * (x - z) := by
    have h₅: c * (y - z) + b * (x - y) ≤ b * (y - z) + b * (x - y) := by
      simp [mul_le_mul_of_nonneg_right h₂.1 (sub_nonneg_of_le h₃.1)]
    calc c * (y - z) + b * (x - y) 
      ≤ b * (y - z) + b * (x - y) := h₅
      _ = b * ((y - z) + (x - y)) := by ring
      _ = b * (x - z) := by ring
      _ ≤ a * (x - z) := mul_le_mul_of_nonneg_right h₂.2 (sub_nonneg_of_le (le_trans h₃.1 h₃.2))
  linarith

lemma rearrangement_lemma'
  (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂: c ≤ b ∧ b ≤ a)
  (h₃: z ≤ y ∧ y ≤ x) :
  b * z + a * y + c * x ≤ c * z + b * y + a * x := by
  have h₄: c * (x - z) + b * (z - y) ≤ a * (x - y) := by
    have h₅: c * (x - z) ≤ b * (x - z) := by
      exact mul_le_mul_of_nonneg_right h₂.1 (sub_nonneg_of_le (le_trans h₃.1 h₃.2))
    calc c * (x - z) + b * (z - y) 
      ≤ b * (x - z) + b * (z - y) := by linarith
      _ = b * ((x - z) + (z - y)) := by ring
      _ = b * (x - y) := by ring
      _ ≤ a * (x - y) := mul_le_mul_of_nonneg_right h₂.2 (sub_nonneg_of_le h₃.2)
  linarith

lemma case_cba
  (a b c : ℝ)
  (hap : 0 < a)
  (hbp : 0 < b)
  (hcp : 0 < c)
  (h₁ : c < a + b)
  (h₃ : a < b + c)
  (hba: b ≤ a)
  (hcb: c ≤ b) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  have g₀: b * c ≤ a * c := mul_le_mul_of_nonneg_right hba (le_of_lt hcp)
  have g₁: a * c ≤ a * b := mul_le_mul_of_nonneg_left hcb (le_of_lt hap)
  have g₂: a * (b + c - a) ≤ b * (a + c - b) := by
    have : 0 ≤ (a - b) * (a + b - c) := 
      mul_nonneg (sub_nonneg_of_le hba) (sub_pos.mpr h₁)
    linarith
  have g₃: b * (a + c - b) ≤ c * (a + b - c) := by
    have : 0 ≤ (b - c) * (b + c - a) := 
      mul_nonneg (sub_nonneg_of_le hcb) (sub_pos.mpr h₃)
    linarith
  have key := rearrangement_lemma (a * b) (a * c) (b * c) 
    (c * (a + b - c)) (b * (a + c - b)) (a * (b + c - a))
    ⟨mul_pos hap hbp, mul_pos hap hcp, mul_pos hbp hcp⟩
    ⟨g₀, g₁⟩ ⟨g₂, g₃⟩
  linarith

lemma case_cba_tight
  (a b c : ℝ)
  (hap : 0 < a)
  (hbp : 0 < b)
  (hcp : 0 < c)
  (h₁ : c < a + b)
  (h₃ : a < b + c)
  (hba: b ≤ a)
  (hcb: c ≤ b) :
  0 ≤ a^2 * c * (a - c) + c^2 * b * (c - b) + b^2 * a * (b - a) := by
  have g₀: b * c ≤ a * c := mul_le_mul_of_nonneg_right hba (le_of_lt hcp)
  have g₁: a * c ≤ a * b := mul_le_mul_of_nonneg_left hcb (le_of_lt hap)
  have g₂: a * (b + c - a) ≤ b * (a + c - b) := by
    have : 0 ≤ (a - b) * (a + b - c) := 
      mul_nonneg (sub_nonneg_of_le hba) (sub_pos.mpr h₁)
    linarith
  have g₃: b * (a + c - b) ≤ c * (a + b - c) := by
    have : 0 ≤ (b - c) * (b + c - a) := 
      mul_nonneg (sub_nonneg_of_le hcb) (sub_pos.mpr h₃)
    linarith
  have key := rearrangement_lemma' (a * b) (a * c) (b * c) 
    (c * (a + b - c)) (b * (a + c - b)) (a * (b + c - a))
    ⟨mul_pos hap hbp, mul_pos hap hcp, mul_pos hbp hcp⟩
    ⟨g₀, g₁⟩ ⟨g₂, g₃⟩
  linarith

theorem imo_1983_p6
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  wlog ho₀: b ≤ a
  · push_neg at ho₀
    wlog ho₁: c ≤ b
    · push_neg at ho₁
      -- a < b < c
      rw [add_comm] at h₁ h₂ h₃
      have g₀ := case_cba_tight c b a h₀.2.2 h₀.2.1 h₀.1 h₃ h₁ (le_of_lt ho₁) (le_of_lt ho₀)
      linarith
    · wlog ho₂: c ≤ a
      · push_neg at ho₂
        -- a < c ≤ b
        rw [add_comm] at h₁ h₂
        have g₀ := case_cba b c a h₀.2.1 h₀.2.2 h₀.1 h₃ h₂ ho₁ (le_of_lt ho₂)
        linarith
      · -- c ≤ a < b
        rw [add_comm] at h₁
        have g₀ := case_cba_tight b a c h₀.2.1 h₀.1 h₀.2.2 h₁ h₂ (le_of_lt ho₀) ho₂
        linarith
  · wlog ho₁: c ≤ b
    · push_neg at ho₁
      wlog ho₂: c ≤ a
      · push_neg at ho₂
        -- b < a < c
        rw [add_comm] at h₂ h₃
        have g₀ := case_cba c a b h₀.2.2 h₀.1 h₀.2.1 h₂ h₁ (le_of_lt ho₂) ho₀
        linarith
      · rw [add_comm] at h₃
        exact case_cba_tight a c b h₀.1 h₀.2.2 h₀.2.1 h₂ h₃ ho₂ (le_of_lt ho₁)
    · exact case_cba a b c h₀.1 h₀.2.1 h₀.2.2 h₁ h₃ ho₀ ho₁