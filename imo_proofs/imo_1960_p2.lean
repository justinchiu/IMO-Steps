import ImoSteps

open Real

theorem imo_1960_p2
  (x : ℝ)
  (h₀ : 0 ≤ 1 + 2 * x)
  (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9) :
  -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  constructor
  · linarith
  · have h₃: 4 * x ^ 2 < (2 * x + 9) * (1 - sqrt (1 + 2 * x) ) ^ 2 := by
      refine (div_lt_iff _).mp h₂
      exact h₁.bot_lt
    have h₄: (1 - sqrt (1 + 2 * x)) ^ 2 = 1 - 2 * sqrt (1 + 2 * x) + (1 + 2 * x) := by
      rw [sub_sq, Real.sq_sqrt h₀, one_pow]
    have h₄': (1 - sqrt (1 + 2 * x)) ^ 2 = 2 + 2 * x - 2 * sqrt (1 + 2 * x) := by
      rw [h₄]; ring
    rw [h₄'] at h₃
    have h₅: 4 * x ^ 2 < (2 * x + 9) * (2 + 2 * x - 2 * sqrt (1 + 2 * x)) := h₃
    have h₆: sqrt (1 + 2 * x) < (11 * x + 9) / (2 * x + 9) := by
      have pos : 0 < 2 * x + 9 := by
        by_contra h
        push_neg at h
        have : 2 * x + 9 < 0 ∨ 2 * x + 9 = 0 := lt_or_eq_of_le h
        cases this with
        | inl h' => 
          have : x < -9/2 := by linarith
          have : 1 + 2 * x < 0 := by linarith
          linarith [h₀]
        | inr h' =>
          have : x = -9/2 := by linarith
          rw [this] at h₃
          norm_num at h₃
      rw [div_lt_iff pos] at h₅
      have expanded := calc 4 * x^2 
        < 4 * x^2 + 4 * x + 18 * x + 18 - (4 * x + 18) * sqrt (1 + 2 * x) := by linarith
        _ = (2 * x + 9) * (2 + 2 * x) - (2 * x + 9) * 2 * sqrt (1 + 2 * x) := by ring
      have : (2 * x + 9) * 2 * sqrt (1 + 2 * x) < (2 * x + 9) * (2 + 2 * x) - 4 * x^2 := by linarith
      have : 2 * sqrt (1 + 2 * x) < (2 + 2 * x) - 4 * x^2 / (2 * x + 9) := by
        rw [← div_lt_iff pos] at this
        convert this using 2
        field_simp
      have final : sqrt (1 + 2 * x) < ((2 + 2 * x) * (2 * x + 9) - 4 * x^2) / (2 * (2 * x + 9)) := by
        linarith
      convert final using 2
      field_simp
      ring
    have h₇ : (2 * x + 9) * sqrt (1 + 2 * x) < 11 * x + 9 := by
      by_cases hpos : 0 < 2 * x + 9
      · rw [mul_comm]
        rw [← div_lt_iff hpos] at h₆
        exact h₆
      · push_neg at hpos
        have : 2 * x + 9 ≤ 0 := hpos
        have : (2 * x + 9) * sqrt (1 + 2 * x) ≤ 0 := mul_nonpos_of_nonpos_nonneg this (sqrt_nonneg _)
        linarith
    have h₈ : (2 * x + 9)^2 * (1 + 2 * x) < (11 * x + 9)^2 := by
      have : ((2 * x + 9) * sqrt (1 + 2 * x))^2 < (11 * x + 9)^2 := by
        exact sq_lt_sq' (by linarith : -(11 * x + 9) < (2 * x + 9) * sqrt (1 + 2 * x)) h₇
      rw [mul_pow, sq_sqrt h₀] at this
      exact this
    have h₉ : 8 * x^3 < 45 * x^2 := by linarith
    by_cases hx : x = 0
    · rw [hx]; norm_num
    · have : 8 * x < 45 := by
        have : x^2 * (8 * x) < x^2 * 45 := by linarith
        have hx2 : 0 < x^2 := sq_pos_of_ne_zero _ hx
        exact (mul_lt_mul_left hx2).mp this
      linarith