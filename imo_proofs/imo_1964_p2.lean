import ImoSteps

open Real

lemma le_a_sq (a b c : ℝ) :
  (a + b - c) * (a + c - b) ≤ a ^ 2 := by
  have h1: (a + b - c) * (a + c - b) = a ^ 2 - (b - c) ^ 2 := by ring
  rw [h1]
  simp [sq_nonneg]

theorem imo_1964_p2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  have ha : 0 < b + c - a := by linarith
  have hb : 0 < a + c - b := by linarith
  have hc : 0 < a + b - c := by linarith
  have h₄: ((a + b - c) * (a + c - b) * (b + c - a)) ^ 2 ≤ (a * b * c) ^ 2 := by
    have h₄₁: (a + b - c) * (a + c - b) ≤ a ^ 2 := le_a_sq a b c
    have h₄₂: (a + b - c) * (b + c - a) ≤ b ^ 2 := by
      rw [add_comm a b]
      exact le_a_sq b a c
    have h₄₃: (a + c - b) * (b + c - a) ≤ c ^ 2 := by
      rw [add_comm a c, add_comm b c]
      exact le_a_sq c a b
    calc ((a + b - c) * (a + c - b) * (b + c - a)) ^ 2 
      = ((a + b - c) * (a + c - b)) * ((a + b - c) * (b + c - a)) * ((a + c - b) * (b + c - a)) := by ring
      _ ≤ a^2 * b^2 * c^2 := by
        apply mul_le_mul
        · apply mul_le_mul h₄₁ h₄₂
          · exact mul_pos hc ha
          · exact sq_nonneg a
        · exact h₄₃
        · exact mul_pos hb ha
        · apply mul_nonneg
          apply mul_nonneg
          · exact sq_nonneg a
          · exact sq_nonneg b
      _ = (a * b * c) ^ 2 := by ring
  have h₅: (a + b - c) * (a + c - b) * (b + c - a) ≤ a * b * c := by
    have pos : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos h₀.1 h₀.2.1
      exact h₀.2.2
    exact le_of_sq_le_sq pos (le_of_lt (by apply mul_pos; apply mul_pos hc hb; exact ha)) h₄
  linarith