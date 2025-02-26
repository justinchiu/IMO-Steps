import Mathlib

set_option linter.unusedVariables.analyzeTactics true

open Real

lemma imo_2022_p2_simp_1
  (g : ℝ → ℝ)
  (h₀ : ∀ (x : ℝ), 0 < x → ∃ y,
  0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z) :
  ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y := by
  intros x y hp h₁
  by_contra! hc
  have g₁: 2 * x * x < g x + g x := by
    let ⟨p,h₁₁⟩ := h₀ x hp.1
    cases' h₁₁ with h₁₁ h₁₂
    cases' h₁₂ with h₁₂ h₁₃
    by_cases hxp: x ≠ p
    . have h₁₄: ¬ g x + g x ≤ 2 * x * x := by
        refine h₁₃ x ?_
        constructor
        . exact hp.1
        . exact hxp
      exact not_le.mp h₁₄
    . push_neg at hxp
      exfalso
      have hpy: y ≠ p := by exact Ne.trans_eq (id (Ne.symm hc)) hxp
      have hcy: ¬g x + g y ≤ 2 * x * y := by
        refine h₁₃ y ?_
        constructor
        . exact hp.2
        . exact hpy
      linarith
  have g₂: 2 * y * y < g y + g y := by
    let ⟨p,h₁₁⟩ := h₀ y hp.2
    cases' h₁₁ with h₁₁ h₁₂
    cases' h₁₂ with h₁₂ h₁₃
    by_cases hyp: y ≠ p
    . have h₁₄: ¬ g y + g y ≤ 2 * y * y := by
        refine h₁₃ y ?_
        constructor
        . exact hp.2
        . exact hyp
      exact not_le.mp h₁₄
    . push_neg at hyp
      exfalso
      have hpx: x ≠ p := by exact Ne.trans_eq hc hyp
      have hcy: ¬g x + g y ≤ 2 * x * y := by
        rw [add_comm, mul_right_comm]
        refine h₁₃ x ?_
        constructor
        . exact hp.1
        . exact hpx
      linarith
  ring_nf at g₁ g₂
  simp at g₁ g₂
  have g₆: (x - y) ≠ 0 := by exact sub_ne_zero.mpr hc
  have g₇: 0 < (x - y) ^ 2 := by exact (sq_pos_iff).mpr g₆
  linarith


lemma imo_2022_p2_simp_1_1
  (g : ℝ → ℝ)
  (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y
      ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  (h₁ : g x + g y ≤ 2 * x * y)
  (hc : x ≠ y) :
  2 * x * x < g x + g x := by
  let ⟨p,h₁₁⟩ := h₀ x hp.1
  cases' h₁₁ with h₁₁ h₁₂
  cases' h₁₂ with h₁₂ h₁₃
  by_cases hxp: x ≠ p
  . have h₁₄: ¬ g x + g x ≤ 2 * x * x := by
      refine h₁₃ x ?_
      constructor
      . exact hp.1
      . exact hxp
    exact not_le.mp h₁₄
  . push_neg at hxp
    exfalso
    have hpy: y ≠ p := by exact Ne.trans_eq (id (Ne.symm hc)) hxp
    have hcy: ¬g x + g y ≤ 2 * x * y := by
      refine h₁₃ y ?_
      constructor
      . exact hp.2
      . exact hpy
    linarith



lemma imo_2022_p2_simp_1_2
  (g : ℝ → ℝ)
  -- h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z
  (x y : ℝ)
  -- (hp : 0 < x ∧ 0 < y)
  (h₁ : g x + g y ≤ 2 * x * y)
  (hc : x ≠ y)
  (g₁ : 2 * x * x < g x + g x)
  (g₂ : 2 * y * y < g y + g y) :
  False := by
  ring_nf at g₁ g₂
  simp at g₁ g₂
  have g₆: (x - y) ≠ 0 := by exact sub_ne_zero.mpr hc
  have g₇: 0 < (x - y) ^ 2 := by exact (sq_pos_iff).mpr g₆
  linarith


lemma imo_2022_p2_simp_1_3
  -- (g : ℝ → ℝ)
  (x y : ℝ)
  -- (h₁ : g x + g y ≤ 2 * x * y)
  (hc : x ≠ y) :
  -- (g₁ : x ^ 2 < g x)
  -- (g₂ : y ^ 2 < g y) :
  0 < (x - y) ^ 2 := by
  refine (sq_pos_iff).mpr ?_
  exact sub_ne_zero.mpr hc


lemma imo_2022_p2_simp_1_4
  (g : ℝ → ℝ)
  -- h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z
  (x y : ℝ)
  -- (hp : 0 < x ∧ 0 < y)
  (h₁ : g x + g y ≤ 2 * x * y)
  -- (hc : x ≠ y)
  (g₁ : 2 * x * x < g x + g x)
  (g₂ : 2 * y * y < g y + g y) :
  (x - y) ^ 2 < 0 := by
  linarith


lemma imo_2022_p2_simp_1_5
  (g : ℝ → ℝ)
  -- h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  (h₁ : g x + g y ≤ 2 * x * y)
  (hc : x ≠ y)
  (p : ℝ)
  -- (h₁₁ : 0 < p)
  -- (h₁₂ : g x + g p ≤ 2 * x * p)
  (h₁₃ : ∀ (z : ℝ), 0 < z ∧ z ≠ p → ¬g x + g z ≤ 2 * x * z) :
  2 * x * x < g x + g x := by
  by_cases hxp: x ≠ p
  . have h₁₄: ¬ g x + g x ≤ 2 * x * x := by
      refine h₁₃ x ?_
      constructor
      . exact hp.1
      . exact hxp
    exact not_le.mp h₁₄
  . push_neg at hxp
    exfalso
    have hpy: y ≠ p := by exact Ne.trans_eq (id (Ne.symm hc)) hxp
    have hcy: ¬g x + g y ≤ 2 * x * y := by
      refine h₁₃ y ?_
      constructor
      . exact hp.2
      . exact hpy
    linarith


lemma imo_2022_p2_simp_1_6
  (g : ℝ → ℝ)
  (x y : ℝ)
  (hxyp : 0 < x ∧ 0 < y)
  -- h₁ : g x + g y ≤ 2 * x * y
  -- hc : x ≠ y
  (p : ℝ)
  (h₁₃ : ∀ (z : ℝ), 0 < z ∧ z ≠ p → ¬g x + g z ≤ 2 * x * z)
  (hxp : x ≠ p) :
  2 * x * x < g x + g x := by
  have h₁₄: ¬ g x + g x ≤ 2 * x * x := by
    refine h₁₃ x ?_
    constructor
    . exact hxyp.1
    . exact hxp
  exact not_le.mp h₁₄


lemma imo_2022_p2_simp_1_7
  (g : ℝ → ℝ)
  (x y : ℝ)
  (hxyp : 0 < x ∧ 0 < y)
  (p : ℝ)
  (h₁₃ : ∀ (z : ℝ), 0 < z ∧ z ≠ p → ¬g x + g z ≤ 2 * x * z)
  (hxp : x ≠ p) :
  ¬g x + g x ≤ 2 * x * x := by
  refine h₁₃ x ?_
  constructor
  . exact hxyp.1
  . exact hxp



lemma imo_2022_p2_simp_1_8
  (g : ℝ → ℝ)
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  (h₁ : g x + g y ≤ 2 * x * y)
  (hc : x ≠ y)
  (p : ℝ)
  (h₁₃ : ∀ (z : ℝ), 0 < z ∧ z ≠ p → ¬g x + g z ≤ 2 * x * z)
  (hxp : ¬x ≠ p) :
  2 * x * x < g x + g x := by
  push_neg at hxp
  exfalso
  have hpy: y ≠ p := by exact Ne.trans_eq (id (Ne.symm hc)) hxp
  have hcy: ¬g x + g y ≤ 2 * x * y := by
    refine h₁₃ y ?_
    constructor
    . exact hp.2
    . exact hpy
  linarith



lemma imo_2022_p2_simp_1_9
  (g : ℝ → ℝ)
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  (h₁ : g x + g y ≤ 2 * x * y)
  (hc : x ≠ y)
  (p : ℝ)
  (h₁₃ : ∀ (z : ℝ), 0 < z ∧ z ≠ p → ¬g x + g z ≤ 2 * x * z)
  (hxp : x = p) :
  False := by
  have hpy: y ≠ p := by exact Ne.trans_eq (id (Ne.symm hc)) hxp
  have hcy: ¬g x + g y ≤ 2 * x * y := by
    refine h₁₃ y ?_
    constructor
    . exact hp.2
    . exact hpy
  linarith




lemma imo_2022_p2_simp_2
  (g : ℝ → ℝ)
  (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧
      ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y) :
  ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2 := by
  intros x hxp
  let ⟨y,h₁₁⟩ := h₀ x hxp
  cases' h₁₁ with h₁₁ h₁₂
  cases' h₁₂ with h₁₂ h₁₃
  have hxy: x = y := by
    apply h₁ x y
    . exact { left := hxp, right := h₁₁ }
    . exact h₁₂
  rw [← hxy] at h₁₂
  linarith


lemma imo_2022_p2_simp_2_1
  (g : ℝ → ℝ)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y
  --   ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  (x y: ℝ)
  (hxp : 0 < x)
  (h₁₁ : 0 < y)
  (h₁₂ : g x + g y ≤ 2 * x * y) :
  -- (h₁₃ : ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z) :
  x = y := by
  apply h₁ x y
  . exact { left := hxp, right := h₁₁ }
  . exact h₁₂


lemma imo_2022_p2_simp_2_2
  (g : ℝ → ℝ)
  (x y : ℝ)
  (h₁₂ : g x + g y ≤ 2 * x * y)
  (hxy : x = y) :
  g x ≤ x ^ 2 := by
  rw [← hxy] at h₁₂
  linarith


lemma imo_2022_p2_simp_3
  (g : ℝ → ℝ)
  (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y
    ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2) :
  ∀ (x : ℝ), 0 < x → ¬g x < x ^ 2 := by
  simp
  by_contra! hc
  let ⟨x,hxp⟩ := hc
  cases' hxp with hxp h₃
  let d₁:ℝ := x ^ 2 - g x
  have hd₁ : g x = x ^ 2 - d₁ := by exact (sub_sub_self (x ^ 2) (g x)).symm
  let z:ℝ := x + Real.sqrt d₁
  have hz: z = x + Real.sqrt d₁ := by exact rfl
  have hzp: 0 < z := by
    refine add_pos hxp ?_
    refine Real.sqrt_pos_of_pos ?_
    exact sub_pos.mpr h₃
  have hxz: z ≠ x := by
    rw [hz]
    simp
    push_neg
    refine Real.sqrt_ne_zero'.mpr ?_
    exact sub_pos.mpr h₃
  -- have h₄: g z ≤ z ^ 2 := by exact h₂ z hzp
  have h₅: g x + g z ≤ 2 * x * z := by
    rw [hd₁]
    have h₅₁: - d₁ + Real.sqrt (x ^ 2 - (x ^ 2 - d₁)) ^ 2 ≤ 0 := by
      simp
      rw [Real.sq_sqrt]
      exact sub_nonneg_of_le (h₂ x hxp)
    have h₅₂: x ^ 2 - d₁ + z ^ 2 ≤ 2 * x * z := by
      rw [hz, mul_add, add_sq]
      ring_nf
      repeat rw [add_assoc]
      refine add_le_add_left ?_ (x * Real.sqrt (x ^ 2 - g x) * 2)
      rw [hd₁]
      linarith
    exact add_le_of_add_le_left h₅₂ (h₂ z hzp)
  let ⟨y,hyp⟩ := h₀ x hxp
  cases' hyp with hyp h₆
  cases' h₆ with h₆ h₇
  have hxy: x = y := by
    apply h₁
    . exact { left := hxp, right := hyp }
    . exact h₆
  have h₈: ¬g x + g z ≤ 2 * x * z := by
      refine h₇ z ?_
      constructor
      . exact hzp
      . exact Ne.trans_eq hxz hxy
  linarith[h₅,h₈]


lemma imo_2022_p2_simp_3_1
  (g : ℝ → ℝ)
  (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y
      ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2)
  (hc : ∃ x, 0 < x ∧ g x < x ^ 2) :
  False := by
  let ⟨x,hxp⟩ := hc
  cases' hxp with hxp h₃
  let d₁:ℝ := x ^ 2 - g x
  have hd₁ : g x = x ^ 2 - d₁ := by exact (sub_sub_self (x ^ 2) (g x)).symm
  let z:ℝ := x + Real.sqrt d₁
  have hz: z = x + Real.sqrt d₁ := by exact rfl
  have hzp: 0 < z := by
    refine add_pos hxp ?_
    refine Real.sqrt_pos_of_pos ?_
    exact sub_pos.mpr h₃
  have hxz: z ≠ x := by
    rw [hz]
    simp
    push_neg
    refine Real.sqrt_ne_zero'.mpr ?_
    exact sub_pos.mpr h₃
  have h₅: g x + g z ≤ 2 * x * z := by
    rw [hd₁]
    have h₅₁: - d₁ + Real.sqrt (x ^ 2 - (x ^ 2 - d₁)) ^ 2 ≤ 0 := by
      simp
      rw [Real.sq_sqrt]
      exact sub_nonneg_of_le (h₂ x hxp)
    have h₅₂: x ^ 2 - d₁ + z ^ 2 ≤ 2 * x * z := by
      rw [hz, mul_add, add_sq]
      ring_nf
      repeat rw [add_assoc]
      refine add_le_add_left ?_ (x * Real.sqrt (x ^ 2 - g x) * 2)
      rw [hd₁]
      linarith
    exact add_le_of_add_le_left h₅₂ (h₂ z hzp)
  let ⟨y,hyp⟩ := h₀ x hxp
  cases' hyp with hyp h₆
  cases' h₆ with h₆ h₇
  have hxy: x = y := by
    apply h₁
    . exact { left := hxp, right := hyp }
    . exact h₆
  have h₈: ¬g x + g z ≤ 2 * x * z := by
      refine h₇ z ?_
      constructor
      . exact hzp
      . exact Ne.trans_eq hxz hxy
  linarith[h₅,h₈]


lemma imo_2022_p2_simp_3_2
  (g : ℝ → ℝ)
  (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2)
  -- (hc : ∃ x, 0 < x ∧ g x < x ^ 2)
  (x z d₁ : ℝ)
  (hxp : 0 < x)
  (h₃ : g x < x ^ 2)
  (hd₀ : d₁ = x ^ 2 - g x)
  (hd₁ : g x = x ^ 2 - d₁)
  (hz : z = x + √d₁) :
  False := by
  have hzp: 0 < z := by
    rw [hz]
    refine add_pos hxp ?_
    refine Real.sqrt_pos_of_pos ?_
    rw [hd₀]
    exact sub_pos.mpr h₃
  have hxz: z ≠ x := by
    rw [hz]
    simp
    push_neg
    refine Real.sqrt_ne_zero'.mpr ?_
    rw [hd₀]
    exact sub_pos.mpr h₃
  have h₅: g x + g z ≤ 2 * x * z := by
    rw [hd₁]
    have h₅₂: x ^ 2 - d₁ + z ^ 2 ≤ 2 * x * z := by
      rw [hz, mul_add, add_sq]
      ring_nf
      repeat rw [add_assoc]
      refine add_le_add_left ?_ (x * √d₁ * 2)
      rw [sq_sqrt]
      simp
      linarith
    exact add_le_of_add_le_left h₅₂ (h₂ z hzp)
  let ⟨y,hyp⟩ := h₀ x hxp
  cases' hyp with hyp h₆
  cases' h₆ with h₆ h₇
  have hxy: x = y := by
    apply h₁
    . exact { left := hxp, right := hyp }
    . exact h₆
  have h₈: ¬g x + g z ≤ 2 * x * z := by
      refine h₇ z ?_
      constructor
      . exact hzp
      . exact Ne.trans_eq hxz hxy
  linarith[h₅,h₈]


lemma imo_2022_p2_simp_3_3
  (g : ℝ → ℝ)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2)
  -- (hc : ∃ x, 0 < x ∧ g x < x ^ 2)
  (x z d₁ : ℝ)
  (hxp : 0 < x)
  (h₃ : g x < x ^ 2)
  (hd₀ : d₁ = x ^ 2 - g x)
  -- (hd₁ : g x = x ^ 2 - d₁)
  (hz : z = x + √d₁) :
  0 < z := by
  rw [hz]
  refine add_pos hxp ?_
  refine Real.sqrt_pos_of_pos ?_
  rw [hd₀]
  exact sub_pos.mpr h₃


lemma imo_2022_p2_simp_3_4
  (g : ℝ → ℝ)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2)
  -- (hc : ∃ x, 0 < x ∧ g x < x ^ 2)
  (x z d₁: ℝ)
  -- (hxp : 0 < x)
  (h₃ : g x < x ^ 2)
  (hd₀ : d₁ = x ^ 2 - g x)
  -- (hd₁ : g x = x ^ 2 - d₁)
  (hz : z = x + √d₁) :
  -- (hzp : 0 < z) :
  z ≠ x := by
  rw [hz]
  simp
  push_neg
  refine Real.sqrt_ne_zero'.mpr ?_
  rw [hd₀]
  exact sub_pos.mpr h₃


lemma imo_2022_p2_simp_3_5
  (g : ℝ → ℝ)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2)
  -- (hc : ∃ x, 0 < x ∧ g x < x ^ 2)
  (x z d₁: ℝ)
  -- (hxp : 0 < x)
  (h₃ : g x < x ^ 2)
  -- (hd₀ : d₁ = x ^ 2 - g x)
  (hd₁ : g x = x ^ 2 - d₁)
  (hz : z = x + √d₁)
  (hzp : 0 < z) :
  -- (hxz : z ≠ x) :
  g x + g z ≤ 2 * x * z := by
  rw [hd₁]
  have h₅₂: x ^ 2 - d₁ + z ^ 2 ≤ 2 * x * z := by
    rw [hz, mul_add, add_sq]
    ring_nf
    repeat rw [add_assoc]
    refine add_le_add_left ?_ (x * √d₁ * 2)
    rw [sq_sqrt]
    simp
    linarith
  exact add_le_of_add_le_left h₅₂ (h₂ z hzp)


lemma imo_2022_p2_simp_3_6
  (g : ℝ → ℝ)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2)
  -- (hc : ∃ x, 0 < x ∧ g x < x ^ 2)
  (x z : ℝ)
  (hxp : 0 < x)
  -- (h₃ : g x < x ^ 2)
  -- (hd₀ : d₁ = x ^ 2 - g x)
  -- (hd₁ : g x = x ^ 2 - d₁)
  -- (hz : z = x + √d₁)
  (hzp : 0 < z)
  (hxz : z ≠ x)
  (h₅ : g x + g z ≤ 2 * x * z)
  (y : ℝ)
  (hyp : 0 < y)
  (h₆ : g x + g y ≤ 2 * x * y)
  (h₇ : ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z) :
  False := by
  have hxy: x = y := by
    apply h₁
    . exact { left := hxp, right := hyp }
    . exact h₆
  have h₈: ¬g x + g z ≤ 2 * x * z := by
      refine h₇ z ?_
      constructor
      . exact hzp
      . exact Ne.trans_eq hxz hxy
  linarith[h₅,h₈]


lemma imo_2022_p2_simp_3_7
  (g : ℝ → ℝ)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2)
  -- (hc : ∃ x, 0 < x ∧ g x < x ^ 2)
  (x : ℝ)
  (hxp : 0 < x)
  -- (h₃ : g x < x ^ 2)
  -- (hd₀ : d₁ = x ^ 2 - g x)
  -- (hd₁ : g x = x ^ 2 - d₁)
  -- (hz : z = x + √d₁)
  -- (hzp : 0 < z)
  -- (hxz : z ≠ x)
  -- (h₅ : g x + g z ≤ 2 * x * z)
  (y : ℝ)
  (hyp : 0 < y)
  (h₆ : g x + g y ≤ 2 * x * y) :
  -- (h₇ : ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z) :
  x = y := by
  apply h₁
  . exact { left := hxp, right := hyp }
  . exact h₆


lemma imo_2022_p2_simp_3_8
  (g : ℝ → ℝ)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2)
  -- (hc : ∃ x, 0 < x ∧ g x < x ^ 2)
  (x z : ℝ)
  -- (hxp : 0 < x)
  -- (h₃ : g x < x ^ 2)
  -- (hd₀ : d₁ = x ^ 2 - g x)
  -- (hd₁ : g x = x ^ 2 - d₁)
  -- (hz : z = x + √d₁)
  (hzp : 0 < z)
  (hxz : z ≠ x)
  -- (h₅ : g x + g z ≤ 2 * x * z)
  (y : ℝ)
  -- (hyp : 0 < y)
  -- (h₆ : g x + g y ≤ 2 * x * y)
  (h₇ : ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  (hxy : x = y) :
  ¬g x + g z ≤ 2 * x * z := by
  refine h₇ z ?_
  constructor
  . exact hzp
  . exact Ne.trans_eq hxz hxy


lemma imo_2022_p2_simp_3_9
  (g : ℝ → ℝ)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2)
  -- (hc : ∃ x, 0 < x ∧ g x < x ^ 2)
  (x d₁ : ℝ)
  (hxp : 0 < x)
  -- (h₃ : g x < x ^ 2)
  (hd₀ : d₁ = x ^ 2 - g x) :
  -- (hd₁ : g x = x ^ 2 - d₁)
  -- (hz : z = x + √d₁)
  -- (hzp : 0 < z)
  -- (hxz : z ≠ x) :
  -d₁ + √(x ^ 2 - (x ^ 2 - d₁)) ^ 2 ≤ 0 := by
  simp
  rw [Real.sq_sqrt]
  rw [hd₀]
  exact sub_nonneg_of_le (h₂ x hxp)


lemma imo_2022_p2_simp_3_10
  (g : ℝ → ℝ)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2)
  -- (hc : ∃ x, 0 < x ∧ g x < x ^ 2)
  (x z d₁ : ℝ)
  -- (hxp : 0 < x)
  (h₃ : g x < x ^ 2)
  -- (hd₀ : d₁ = x ^ 2 - g x)
  (hd₁ : g x = x ^ 2 - d₁)
  (hz : z = x + √d₁) :
  -- (hzp : 0 < z)
  -- (hxz : z ≠ x)
  -- (h₅₁ : -d₁ + √(x ^ 2 - (x ^ 2 - d₁)) ^ 2 ≤ 0) :
  x ^ 2 - d₁ + z ^ 2 ≤ 2 * x * z := by
  rw [hz, mul_add, add_sq]
  ring_nf
  repeat rw [add_assoc]
  refine add_le_add_left ?_ (x * √d₁ * 2)
  rw [sq_sqrt]
  simp
  linarith


lemma imo_2022_p2_simp_3_11
  (g : ℝ → ℝ)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2)
  -- (hc : ∃ x, 0 < x ∧ g x < x ^ 2)
  (x z d₁ : ℝ)
  -- (hxp : 0 < x)
  -- (h₃ : g x < x ^ 2)
  -- (hd₀ : d₁ = x ^ 2 - g x)
  -- (hd₁ : g x = x ^ 2 - d₁)
  -- (hz : z = x + √d₁)
  (hzp : 0 < z)
  -- (hxz : z ≠ x)
  -- (h₅₁ : -d₁ + √(x ^ 2 - (x ^ 2 - d₁)) ^ 2 ≤ 0)
  (h₅₂ : x ^ 2 - d₁ + z ^ 2 ≤ 2 * x * z) :
  x ^ 2 - d₁ + g z ≤ 2 * x * z := by
  refine add_le_of_add_le_left h₅₂ ?_
  exact h₂ z hzp


lemma imo_2022_p2_simp_4
  (g : ℝ → ℝ)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃ y, 0 < y ∧ g x + g y ≤ 2 * x * y
  --     ∧ ∀ (z : ℝ), 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → g x + g y ≤ 2 * x * y → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → g x ≤ x ^ 2)
  (h₃ : ∀ (x : ℝ), 0 < x → ¬g x < x ^ 2) :
  ∀ (x : ℝ), 0 < x → g x = x ^ 2 := by
  intros x hxp
  have g₂: g x ≤ x ^ 2 := by exact h₂ x hxp
  have g₃: ¬ g x < x ^ 2 := by exact h₃ x hxp
  linarith



lemma imo_2022_p2_1
  (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2) :
  ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y := by
  intros x y hp h₁
  by_contra! hc
  have h₁₀: x * f x + x * f x > 2 := by
    let ⟨z,h₁₁⟩ := h₀ x hp.1
    cases' h₁₁ with h₁₁ h₁₂
    have h₁₄: y = z := by
      apply h₁₂ y
      constructor
      . exact hp.2
      . exact h₁
    have hxz: ¬ x = z := by exact Ne.trans_eq hc h₁₄
    have h₁₆: ¬ (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) x := by
      exact mt (h₁₂ x) hxz
    have h₁₇: ¬ (0 < x ∧ x * f x + x * f x ≤ 2) := by exact h₁₆
    push_neg at h₁₇
    exact h₁₇ hp.1
  have h₁₁: y * f y + y * f y > 2 := by
    let ⟨z,h₁₁⟩ := h₀ y hp.2
    cases' h₁₁ with h₁₁ h₁₂
    have h₁₄: x = z := by
      apply h₁₂ x
      constructor
      . exact hp.1
      . rw [add_comm]
        exact h₁
    have hxz: ¬ y = z := by exact Ne.trans_eq (id (Ne.symm hc)) h₁₄
    have h₁₆: ¬ (fun y_2 => 0 < y_2 ∧ y * f y_2 + y_2 * f y ≤ 2) y := by
      exact mt (h₁₂ y) hxz
    have h₁₇: ¬ (0 < y ∧ y * f y + y * f y ≤ 2) := by exact h₁₆
    push_neg at h₁₇
    exact h₁₇ hp.2
  ring_nf at h₁₀ h₁₁
  simp at h₁₀ h₁₁
  have h₁₅: 1 / x < f x := by exact (div_lt_iff₀' hp.1).mpr (h₁₀)
  have h₁₆: 1 / y < f y := by exact (div_lt_iff₀' hp.2).mpr (h₁₁)
  have h₁₂: x / y + y / x < 2 := by
    refine lt_of_le_of_lt' h₁ ?_
    refine add_lt_add ?_ ?_
    . rw [← mul_one_div]
      exact (mul_lt_mul_left hp.1).mpr h₁₆
    . rw [← mul_one_div]
      exact (mul_lt_mul_left hp.2).mpr h₁₅
  have h₁₃: 2 < x / y + y / x := by
    refine lt_of_mul_lt_mul_right ?_ (le_of_lt hp.1)
    refine lt_of_mul_lt_mul_right ?_ (le_of_lt hp.2)
    repeat rw [add_mul, mul_assoc]
    rw [mul_comm x y, ← mul_assoc (x/y)]
    rw [div_mul_comm x y y, div_mul_comm y x x, div_self, div_self]
    . ring_nf
      refine lt_of_sub_pos ?_
      rw [mul_comm _ 2, ← mul_assoc]
      rw [← sub_sq']
      refine sq_pos_of_ne_zero ?_
      exact sub_ne_zero.mpr hc.symm
    . exact ne_of_gt hp.1
    . exact ne_of_gt hp.2
  linarith


lemma imo_2022_p2_1_1
  (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  (h₁ : x * f y + y * f x ≤ 2)
  (hc : x ≠ y) :
  x * f x + x * f x > 2 := by
  let ⟨z,h₁₁⟩ := h₀ x hp.1
  cases' h₁₁ with h₁₁ h₁₂
  have h₁₄: y = z := by
    apply h₁₂ y
    constructor
    . exact hp.2
    . exact h₁
  have hxz: ¬ x = z := by exact Ne.trans_eq hc h₁₄
  have h₁₆: ¬ (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) x := by
    exact mt (h₁₂ x) hxz
  have h₁₇: ¬ (0 < x ∧ x * f x + x * f x ≤ 2) := by exact h₁₆
  push_neg at h₁₇
  exact h₁₇ hp.1


lemma imo_2022_p2_1_2
  (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  (h₁ : x * f y + y * f x ≤ 2)
  (hc : x ≠ y)
  (z : ℝ)
  -- (h₁₁ : (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) z)
  (h₁₂ : ∀ (y : ℝ), (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) y → y = z) :
  x * f x + x * f x > 2 := by
  have h₁₄: y = z := by
    apply h₁₂ y
    constructor
    . exact hp.2
    . exact h₁
  have hxz: ¬ x = z := by exact Ne.trans_eq hc h₁₄
  have h₁₆: ¬ (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) x := by
    exact mt (h₁₂ x) hxz
  have h₁₇: ¬ (0 < x ∧ x * f x + x * f x ≤ 2) := by exact h₁₆
  push_neg at h₁₇
  exact h₁₇ hp.1


lemma imo_2022_p2_1_3
  (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  (h₁ : x * f y + y * f x ≤ 2)
  -- (hc : x ≠ y)
  (z : ℝ)
  -- (h₁₁ : (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) z)
  (h₁₂ : ∀ (y : ℝ), (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) y → y = z) :
  y = z := by
  apply h₁₂ y
  constructor
  . exact hp.2
  . exact h₁


lemma imo_2022_p2_1_4
  (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (x z : ℝ)
  -- (y : ℝ)
  -- (hp : 0 < x ∧ 0 < y)
  -- (h₁ : x * f y + y * f x ≤ 2)
  -- (hc : x ≠ y)
  -- (h₁₁ : (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) z)
  (h₁₂ : ∀ (y : ℝ), (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) y → y = z)
  -- (h₁₄ : y = z)
  (hxz : ¬x = z) :
  ¬(fun y => 0 < y ∧ x * f y + y * f x ≤ 2) x := by
  exact mt (h₁₂ x) hxz


lemma imo_2022_p2_1_5
  (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  -- (h₁ : x * f y + y * f x ≤ 2)
  -- (hc : x ≠ y)
  -- (z : ℝ)
  -- (h₁₁ : (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) z)
  -- (h₁₂ : ∀ (y : ℝ), (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) y → y = z)
  -- (h₁₄ : y = z)
  -- (hxz : ¬x = z)
  -- (h₁₆ : ¬(fun y => 0 < y ∧ x * f y + y * f x ≤ 2) x)
  (h₁₇ : ¬(0 < x ∧ x * f x + x * f x ≤ 2)) :
  x * f x + x * f x > 2 := by
  push_neg at h₁₇
  refine h₁₇ ?_
  exact hp.1


lemma imo_2022_p2_1_6
  (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  -- (h₁ : x * f y + y * f x ≤ 2)
  -- (hc : x ≠ y)
  -- (z : ℝ)
  -- (h₁₁ : (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) z)
  -- (h₁₂ : ∀ (y : ℝ), (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) y → y = z)
  -- (h₁₄ : y = z)
  -- (hxz : ¬x = z)
  -- (h₁₆ : ¬(fun y => 0 < y ∧ x * f y + y * f x ≤ 2) x)
  (h₁₇ : 0 < x → 2 < x * f x + x * f x) :
  x * f x + x * f x > 2 := by
  refine h₁₇ ?_
  exact hp.1


lemma imo_2022_p2_1_7
  (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  (h₁ : x * f y + y * f x ≤ 2)
  (hc : x ≠ y)
  (h₁₀ : 1 < x * f x)
  (h₁₁ : 1 < y * f y) :
  False := by
  have h₁₅: 1 / x < f x := by exact (div_lt_iff₀' hp.1).mpr (h₁₀)
  have h₁₆: 1 / y < f y := by exact (div_lt_iff₀' hp.2).mpr (h₁₁)
  have h₁₂: x / y + y / x < 2 := by
    refine lt_of_le_of_lt' h₁ ?_
    refine add_lt_add ?_ ?_
    . rw [← mul_one_div]
      exact (mul_lt_mul_left hp.1).mpr h₁₆
    . rw [← mul_one_div]
      exact (mul_lt_mul_left hp.2).mpr h₁₅
  have h₁₃: 2 < x / y + y / x := by
    refine lt_of_mul_lt_mul_right ?_ (le_of_lt hp.1)
    refine lt_of_mul_lt_mul_right ?_ (le_of_lt hp.2)
    repeat rw [add_mul, mul_assoc]
    -- rw [div_mul_mul_cancel x x y]
    rw [mul_comm x y, ← mul_assoc (x/y)]
    -- rw [mul_comm (x / y * y) x]
    rw [div_mul_comm x y y, div_mul_comm y x x, div_self, div_self]
    . ring_nf
      refine lt_of_sub_pos ?_
      rw [mul_comm _ 2, ← mul_assoc]
      rw [← sub_sq']
      refine sq_pos_of_ne_zero ?_
      exact sub_ne_zero.mpr hc.symm
    . exact ne_of_gt hp.1
    . exact ne_of_gt hp.2
  linarith


lemma imo_2022_p2_1_8
  (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  (h₁ : x * f y + y * f x ≤ 2)
  -- (hc : x ≠ y)
  -- (h₁₀ : 1 < x * f x)
  -- (h₁₁ : 1 < y * f y)
  (h₁₅ : 1 / x < f x)
  (h₁₆ : 1 / y < f y) :
  x / y + y / x < 2 := by
  refine lt_of_le_of_lt' h₁ ?_
  refine add_lt_add ?_ ?_
  . rw [← mul_one_div]
    exact (mul_lt_mul_left hp.1).mpr h₁₆
  . rw [← mul_one_div]
    exact (mul_lt_mul_left hp.2).mpr h₁₅


lemma imo_2022_p2_1_9
  (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  -- (h₁ : x * f y + y * f x ≤ 2)
  -- (hc : x ≠ y)
  -- (h₁₀ : 1 < x * f x)
  -- (h₁₁ : 1 < y * f y)
  -- (h₁₅ : 1 / x < f x)
  (h₁₆ : 1 / y < f y) :
  x / y < x * f y := by
  rw [← mul_one_div]
  exact (mul_lt_mul_left hp.1).mpr h₁₆


lemma imo_2022_p2_1_10
  -- (f : ℝ → ℝ)
  -- hfp : ∀ (x : ℝ), 0 < x → 0 < f x
  -- h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  -- h₁ : x * f y + y * f x ≤ 2
  (hc : x ≠ y) :
  -- h₁₀ : 1 < x * f x
  -- h₁₁ : 1 < y * f y
  -- h₁₅ : 1 / x < f x
  -- h₁₆ : 1 / y < f y
  -- (h₁₂ : x / y + y / x < 2) :
  2 < x / y + y / x := by
  refine lt_of_mul_lt_mul_right ?_ (le_of_lt hp.1)
  refine lt_of_mul_lt_mul_right ?_ (le_of_lt hp.2)
  repeat rw [add_mul, mul_assoc]
  -- rw [div_mul_mul_cancel x x y]
  rw [mul_comm x y, ← mul_assoc (x/y)]
  -- rw [mul_comm (x / y * y) x]
  rw [div_mul_comm x y y, div_mul_comm y x x, div_self, div_self]
  . ring_nf
    refine lt_of_sub_pos ?_
    rw [mul_comm _ 2, ← mul_assoc]
    rw [← sub_sq']
    refine sq_pos_of_ne_zero ?_
    exact sub_ne_zero.mpr hc.symm
  . exact ne_of_gt hp.1
  . exact ne_of_gt hp.2


lemma imo_2022_p2_1_11
  -- (f : ℝ → ℝ)
  (x y : ℝ)
  (hp : 0 < x ∧ 0 < y)
  (hc : x ≠ y) :
  2 * x * y < (x / y + y / x) * x * y := by
  repeat rw [add_mul, mul_assoc]
  -- rw [div_mul_mul_cancel x x y]
  rw [mul_comm x y, ← mul_assoc (x/y)]
  -- rw [mul_comm (x / y * y) x]
  rw [div_mul_comm x y y, div_mul_comm y x x, div_self, div_self]
  . ring_nf
    refine lt_of_sub_pos ?_
    rw [mul_comm _ 2, ← mul_assoc]
    rw [← sub_sq']
    refine sq_pos_of_ne_zero ?_
    exact sub_ne_zero.mpr hc.symm
  . exact ne_of_gt hp.1
  . exact ne_of_gt hp.2


lemma imo_2022_p2_1_12
  -- (f : ℝ → ℝ)
  (x y : ℝ)
  -- (hp : 0 < x ∧ 0 < y)
  (hc : x ≠ y) :
  y * x * 2 < y ^ 2 + x ^ 2 := by
  refine lt_of_sub_pos ?_
  rw [mul_comm _ 2, ← mul_assoc]
  rw [← sub_sq']
  refine sq_pos_of_ne_zero ?_
  exact sub_ne_zero.mpr hc.symm



lemma imo_2022_p2_2
  (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y) :
  ∀ (x : ℝ), 0 < x → x * f x ≤ 1 := by
  intros x hxp
  obtain ⟨y,h₂₁⟩ := h₀ x hxp
  cases' h₂₁ with h₂₁ h₂₂
  have hxy: x = y := by
    have h₂₃: 0 < y ∧ x * f y + y * f x ≤ 2 := by exact h₂₁
    apply h₁ x y
    . constructor
      . exact hxp
      . exact h₂₃.1
    . exact h₂₃.2
  rw [← hxy] at h₂₁
  linarith


lemma imo_2022_p2_2_1
  (f : ℝ → ℝ)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  (x : ℝ)
  (hxp : 0 < x)
  (y : ℝ)
  (h₂ : (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) y) :
  x * f x ≤ 1 := by
  have hxy: x = y := by
    apply h₁ x y
    . constructor
      . exact hxp
      . exact h₂.1
    . exact h₂.2
  rw [← hxy] at h₂
  linarith


lemma imo_2022_p2_2_2
  (f : ℝ → ℝ)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  (x : ℝ)
  (hxp : 0 < x)
  (y : ℝ)
  (h₂ : (fun y => 0 < y ∧ x * f y + y * f x ≤ 2) y) :
  x = y := by
  apply h₁ x y
  . constructor
    . exact hxp
    . exact h₂.1
  . exact h₂.2


lemma imo_2022_p2_2_3
  (f : ℝ → ℝ)
  -- h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y
  (x y : ℝ)
  -- (hxp : 0 < x)
  (h₂ : 0 < y ∧ x * f y + y * f x ≤ 2)
  (hxy : x = y) :
  x * f x ≤ 1 := by
  rw [← hxy] at h₂
  linarith



lemma imo_2022_p2_3
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1) :
  ∀ (x : ℝ), 0 < x → ¬x * f x < 1 := by
  by_contra! hc
  let ⟨x,hxp⟩ := hc
  cases' hxp with hxp h₃
  let d₁:ℝ := 1 - x * f x
  have hd₁ : x * f x = 1 - d₁ := by exact (sub_sub_self 1 (x * f x)).symm
  let z:ℝ := x + d₁ / f x
  have hz: z = x + d₁ / f x := by exact rfl
  have hzp: 0 < z := by
    refine add_pos hxp ?_
    refine div_pos ?_ ?_
    . exact sub_pos.mpr h₃
    . exact hfp x hxp
  have hxz: ¬ x = z := by
    by_contra! hcz₀
    rw [← hcz₀] at hz
    have hcz₁: 0 < d₁ / f x := by
      refine div_pos ?_ (hfp x hxp)
      exact sub_pos.mpr h₃
    linarith
  have h₄: ¬ (x * f z + z * f x ≤ 2) := by
    have h₄₁: x * f z + z * f x ≤ 2 → x = z := by
      exact h₁ x z { left := hxp, right := hzp }
    exact mt h₄₁ hxz
  have h₅: x * f z < 1 := by
    suffices h₅₁: z * f z ≤ 1 by
      refine lt_of_lt_of_le ?_ h₅₁
      refine (mul_lt_mul_right (hfp z hzp)).mpr ?_
      rw [hz]
      refine lt_add_of_pos_right x ?_
      refine div_pos ?_ (hfp x hxp)
      exact sub_pos.mpr h₃
    exact h₂ z hzp
  have h₆: x * f z + z * f x < 2 := by
    suffices h₇: z * f x ≤ 1 by
      linarith
    rw [hz, add_mul, hd₁]
    rw [div_mul_comm d₁ (f x) (f x)]
    rw [div_self]
    . rw [one_mul, sub_add_cancel]
    . exact Ne.symm (ne_of_lt (hfp x hxp))
  linarith


lemma imo_2022_p2_3_1
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  (hc : ∃ x, 0 < x ∧ x * f x < 1) :
  -- (x : ℝ)
  -- (hxp : 0 < x)
  -- (h₃ : x * f x < 1) :
  False := by
  let ⟨x,hxp⟩ := hc
  cases' hxp with hxp h₃
  let d₁:ℝ := 1 - x * f x
  have hd₁ : x * f x = 1 - d₁ := by exact (sub_sub_self 1 (x * f x)).symm
  let z:ℝ := x + d₁ / f x
  have hz: z = x + d₁ / f x := by exact rfl
  have hzp: 0 < z := by
    refine add_pos hxp ?_
    refine div_pos ?_ ?_
    . exact sub_pos.mpr h₃
    . exact hfp x hxp
  have hxz: ¬ x = z := by
    by_contra! hcz₀
    rw [← hcz₀] at hz
    have hcz₁: 0 < d₁ / f x := by
      refine div_pos ?_ (hfp x hxp)
      exact sub_pos.mpr h₃
    linarith
  have h₄: ¬ (x * f z + z * f x ≤ 2) := by
    have h₄₁: x * f z + z * f x ≤ 2 → x = z := by
      exact h₁ x z { left := hxp, right := hzp }
    exact mt h₄₁ hxz
  have h₅: x * f z < 1 := by
    suffices h₅₁: z * f z ≤ 1 by
      refine lt_of_lt_of_le ?_ h₅₁
      refine (mul_lt_mul_right (hfp z hzp)).mpr ?_
      rw [hz]
      refine lt_add_of_pos_right x ?_
      refine div_pos ?_ (hfp x hxp)
      exact sub_pos.mpr h₃
    exact h₂ z hzp
  have h₆: x * f z + z * f x < 2 := by
    suffices h₇: z * f x ≤ 1 by
      linarith
    rw [hz, add_mul, hd₁]
    rw [div_mul_comm d₁ (f x) (f x)]
    rw [div_self]
    . rw [one_mul, sub_add_cancel]
    . exact Ne.symm (ne_of_lt (hfp x hxp))
  linarith


lemma imo_2022_p2_3_2
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x z d₁: ℝ)
  (hxp : 0 < x)
  (h₃ : x * f x < 1)
  (hd₀ : d₁ = 1 - x * f x)
  (hd₁ : x * f x = 1 - d₁)
  (hz : z = x + d₁ / f x) :
  False := by
  have hzp: 0 < z := by
    rw [hz]
    refine add_pos hxp ?_
    refine div_pos ?_ ?_
    . rw [hd₀]
      exact sub_pos.mpr h₃
    . exact hfp x hxp
  have hxz: ¬ x = z := by
    by_contra! hcz₀
    rw [← hcz₀] at hz
    have hcz₁: 0 < d₁ / f x := by
      refine div_pos ?_ (hfp x hxp)
      rw [hd₀]
      exact sub_pos.mpr h₃
    linarith
  have h₄: ¬ (x * f z + z * f x ≤ 2) := by
    have h₄₁: x * f z + z * f x ≤ 2 → x = z := by
      exact h₁ x z { left := hxp, right := hzp }
    exact mt h₄₁ hxz
  have h₅: x * f z < 1 := by
    suffices h₅₁: z * f z ≤ 1 by
      refine lt_of_lt_of_le ?_ h₅₁
      refine (mul_lt_mul_right (hfp z hzp)).mpr ?_
      rw [hz]
      refine lt_add_of_pos_right x ?_
      refine div_pos ?_ (hfp x hxp)
      rw [hd₀]
      exact sub_pos.mpr h₃
    exact h₂ z hzp
  have h₆: x * f z + z * f x < 2 := by
    suffices h₇: z * f x ≤ 1 by
      linarith
    rw [hz, add_mul, hd₁]
    rw [div_mul_comm d₁ (f x) (f x)]
    rw [div_self]
    . rw [one_mul, sub_add_cancel]
    . exact Ne.symm (ne_of_lt (hfp x hxp))
  linarith


lemma imo_2022_p2_3_3
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x d₁ z : ℝ)
  (hxp : 0 < x)
  (h₃ : x * f x < 1)
  (hd₀ : d₁ = 1 - x * f x)
  -- (hd₁ : x * f x = 1 - d₁)
  (hz : z = x + d₁ / f x) :
  0 < z := by
  rw [hz]
  refine add_pos hxp ?_
  refine div_pos ?_ ?_
  . rw [hd₀]
    exact sub_pos.mpr h₃
  . exact hfp x hxp


lemma imo_2022_p2_3_4
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x d₁ : ℝ)
  (hxp : 0 < x)
  (h₃ : x * f x < 1)
  (hd₀ : d₁ = 1 - x * f x) :
  -- (hd₁ : x * f x = 1 - d₁)
  -- (hz : z = x + d₁ / f x) :
  0 < d₁ / f x := by
  refine div_pos ?_ ?_
  . rw [hd₀]
    exact sub_pos.mpr h₃
  . exact hfp x hxp


lemma imo_2022_p2_3_5
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x d₁ z: ℝ)
  (hxp : 0 < x)
  (h₃ : x * f x < 1)
  (hd₀ : d₁ = 1 - x * f x)
  -- (hd₁ : x * f x = 1 - d₁)
  (hz : z = x + d₁ / f x)
  (hzp : 0 < z) :
  ¬x = z := by
  by_contra! hcz₀
  rw [← hcz₀] at hz
  have hcz₁: 0 < d₁ / f x := by
    refine div_pos ?_ (hfp x hxp)
    rw [hd₀]
    exact sub_pos.mpr h₃
  linarith


lemma imo_2022_p2_3_6
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x d₁ : ℝ)
  (hxp : 0 < x)
  (h₃ : x * f x < 1)
  (hd₀ : d₁ = 1 - x * f x)
  -- (hd₁ : x * f x = 1 - d₁)
  (hz : x = x + d₁ / f x) :
  -- (hzp : 0 < z)
  -- (hcz₀ : x = z) :
  False := by
  have hcz₁: 0 < d₁ / f x := by
    refine div_pos ?_ (hfp x hxp)
    rw [hd₀]
    exact sub_pos.mpr h₃
  linarith


lemma imo_2022_p2_3_7
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x z d₁ : ℝ)
  (hxp : 0 < x)
  (h₃ : x * f x < 1)
  (hd₀ : d₁ = 1 - x * f x)
  (hd₁ : x * f x = 1 - d₁)
  (hz : z = x + d₁ / f x)
  (hzp : 0 < z)
  (hxz : ¬x = z) :
  ¬x * f z + z * f x ≤ 2 := by
  have h₄: ¬ (x * f z + z * f x ≤ 2) := by
    have h₄₁: x * f z + z * f x ≤ 2 → x = z := by
      exact h₁ x z { left := hxp, right := hzp }
    exact mt h₄₁ hxz
  have h₅: x * f z < 1 := by
    suffices h₅₁: z * f z ≤ 1 by
      refine lt_of_lt_of_le ?_ h₅₁
      refine (mul_lt_mul_right (hfp z hzp)).mpr ?_
      rw [hz]
      refine lt_add_of_pos_right x ?_
      refine div_pos ?_ (hfp x hxp)
      rw [hd₀]
      exact sub_pos.mpr h₃
    exact h₂ z hzp
  have h₆: x * f z + z * f x < 2 := by
    suffices h₇: z * f x ≤ 1 by
      linarith
    rw [hz, add_mul, hd₁]
    rw [div_mul_comm d₁ (f x) (f x)]
    rw [div_self]
    . rw [one_mul, sub_add_cancel]
    . exact Ne.symm (ne_of_lt (hfp x hxp))
  linarith


lemma imo_2022_p2_3_8
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x z d₁ : ℝ)
  (hxp : 0 < x)
  (h₃ : x * f x < 1)
  (hd₀ : d₁ = 1 - x * f x)
  (hd₁ : x * f x = 1 - d₁)
  (hz : z = x + d₁ / f x)
  (hzp : 0 < z)
  -- (hxz : ¬x = z)
  (h₄ : ¬x * f z + z * f x ≤ 2) :
  x * f z < 1 := by
  have h₅: x * f z < 1 := by
    suffices h₅₁: z * f z ≤ 1 by
      refine lt_of_lt_of_le ?_ h₅₁
      refine (mul_lt_mul_right (hfp z hzp)).mpr ?_
      rw [hz]
      refine lt_add_of_pos_right x ?_
      refine div_pos ?_ (hfp x hxp)
      rw [hd₀]
      exact sub_pos.mpr h₃
    exact h₂ z hzp
  have h₆: x * f z + z * f x < 2 := by
    suffices h₇: z * f x ≤ 1 by
      linarith
    rw [hz, add_mul, hd₁]
    rw [div_mul_comm d₁ (f x) (f x)]
    rw [div_self]
    . rw [one_mul, sub_add_cancel]
    . exact Ne.symm (ne_of_lt (hfp x hxp))
  linarith


lemma imo_2022_p2_3_9
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x z d₁ : ℝ)
  (hxp : 0 < x)
  (h₃ : x * f x < 1)
  (hd₀ : d₁ = 1 - x * f x)
  -- (hd₁ : x * f x = 1 - d₁)
  (hz : z = x + d₁ / f x)
  (hzp : 0 < z)
  -- (hxz : ¬x = z)
  -- (h₄ : ¬x * f z + z * f x ≤ 2)
  (h₅₁ : z * f z ≤ 1) :
  x * f z < 1 := by
  refine lt_of_lt_of_le ?_ h₅₁
  refine (mul_lt_mul_right (hfp z hzp)).mpr ?_
  rw [hz]
  refine lt_add_of_pos_right x ?_
  refine div_pos ?_ (hfp x hxp)
  rw [hd₀]
  exact sub_pos.mpr h₃


lemma imo_2022_p2_3_10
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x z d₁ : ℝ)
  (hxp : 0 < x)
  -- (h₃ : x * f x < 1)
  -- (hd₀ : d₁ = 1 - x * f x)
  (hd₁ : x * f x = 1 - d₁)
  (hz : z = x + d₁ / f x)
  -- (hzp : 0 < z)
  -- (hxz : ¬x = z)
  (h₄ : ¬x * f z + z * f x ≤ 2)
  (h₅ : x * f z < 1) :
  x * f z + z * f x < 2 := by
  have h₆: x * f z + z * f x < 2 := by
    suffices h₇: z * f x ≤ 1 by
      linarith
    rw [hz, add_mul, hd₁]
    rw [div_mul_comm d₁ (f x) (f x)]
    rw [div_self]
    . rw [one_mul, sub_add_cancel]
    . exact Ne.symm (ne_of_lt (hfp x hxp))
  linarith


lemma imo_2022_p2_3_11
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x z d₁ : ℝ)
  (hxp : 0 < x)
  -- (h₃ : x * f x < 1)
  -- (hd₀ : d₁ = 1 - x * f x)
  (hd₁ : x * f x = 1 - d₁)
  (hz : z = x + d₁ / f x)
  -- (hzp : 0 < z)
  -- (hxz : ¬x = z)
  (h₄ : ¬x * f z + z * f x ≤ 2)
  (h₅ : x * f z < 1) :
  z * f x ≤ 1 := by
  suffices h₇: z * f x ≤ 1 by
    linarith
  rw [hz, add_mul, hd₁]
  rw [div_mul_comm d₁ (f x) (f x)]
  rw [div_self]
  . rw [one_mul, sub_add_cancel]
  . exact Ne.symm (ne_of_lt (hfp x hxp))


lemma imo_2022_p2_3_12
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x d₁ : ℝ)
  (hxp : 0 < x) :
  -- (h₃ : x * f x < 1)
  -- (hd₀ : d₁ = 1 - x * f x)
  -- (hd₁ : x * f x = 1 - d₁)
  -- (hz : z = x + d₁ / f x)
  -- (hzp : 0 < z)
  -- (hxz : ¬x = z)
  -- (h₄ : ¬x * f z + z * f x ≤ 2)
  -- (h₅ : x * f z < 1) :
  1 - d₁ + d₁ / f x * f x ≤ 1 := by
  rw [div_mul_comm d₁ (f x) (f x)]
  rw [div_self]
  . rw [one_mul, sub_add_cancel]
  . exact Ne.symm (ne_of_lt (hfp x hxp))


lemma imo_2022_p2_3_13
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x d₁ : ℝ)
  (hxp : 0 < x) :
  -- (h₃ : x * f x < 1) :
  -- (hd₀ : d₁ = 1 - x * f x)
  -- (hd₁ : x * f x = 1 - d₁)
  -- (hz : z = x + d₁ / f x)
  -- (hzp : 0 < z)
  -- (hxz : ¬x = z)
  -- (h₄ : ¬x * f z + z * f x ≤ 2)
  -- (h₅ : x * f z < 1) :
  1 - d₁ + f x / f x * d₁ ≤ 1 := by
  rw [div_self]
  . rw [one_mul, sub_add_cancel]
  . exact Ne.symm (ne_of_lt (hfp x hxp))


lemma imo_2022_p2_3_14
  -- (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (d₁ : ℝ) :
  -- (hxp : 0 < x)
  -- (h₃ : x * f x < 1)
  -- (hd₀ : d₁ = 1 - x * f x)
  -- (hd₁ : x * f x = 1 - d₁)
  -- (hz : z = x + d₁ / f x)
  -- (hzp : 0 < z)
  -- (hxz : ¬x = z)
  -- (h₄ : ¬x * f z + z * f x ≤ 2)
  -- (h₅ : x * f z < 1) :
  1 - d₁ + 1 * d₁ ≤ 1 := by
  rw [one_mul]
  refine le_of_eq ?_
  exact sub_add_cancel 1 d₁


lemma imo_2022_p2_3_15
  (f : ℝ → ℝ)
  (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  -- (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  -- (hc : ∃ x, 0 < x ∧ x * f x < 1)
  (x : ℝ)
  (hxp : 0 < x) :
  -- (h₃ : x * f x < 1)
  -- (hd₀ : d₁ = 1 - x * f x)
  -- (hd₁ : x * f x = 1 - d₁)
  -- (hz : z = x + d₁ / f x)
  -- (hzp : 0 < z)
  -- (hxz : ¬x = z)
  -- (h₄ : ¬x * f z + z * f x ≤ 2)
  -- (h₅ : x * f z < 1) :
  f x ≠ 0 := by
  refine PartialHomeomorph.unitBallBall.proof_2 (f x) ?_
  exact (hfp x hxp)


lemma imo_2022_p2_4
  (f : ℝ → ℝ)
  -- (hfp : ∀ (x : ℝ), 0 < x → 0 < f x)
  -- (h₀ : ∀ (x : ℝ), 0 < x → ∃! y, 0 < y ∧ x * f y + y * f x ≤ 2)
  -- (h₁ : ∀ (x y : ℝ), 0 < x ∧ 0 < y → x * f y + y * f x ≤ 2 → x = y)
  (h₂ : ∀ (x : ℝ), 0 < x → x * f x ≤ 1)
  (h₃ : ∀ (x : ℝ), 0 < x → ¬x * f x < 1) :
  ∀ (x : ℝ), 0 < x → f x = 1 / x := by
  intros x hxp
  have h₄: x * f x ≤ 1 := by exact h₂ x hxp
  have h₅: ¬ x * f x < 1 := by exact h₃ x hxp
  refine eq_div_of_mul_eq ?_ ?_
  . exact ne_of_gt hxp
  . push_neg at h₅
    linarith


lemma imo_2022_p2_4_1
  (f : ℝ → ℝ)
  (x : ℝ)
  (hxp : 0 < x)
  (h₄ : x * f x ≤ 1)
  (h₅ : ¬x * f x < 1) :
  f x = 1 / x := by
  refine eq_div_of_mul_eq ?_ ?_
  . exact ne_of_gt hxp
  . push_neg at h₅
    rw [mul_comm]
    exact le_antisymm h₄ h₅
