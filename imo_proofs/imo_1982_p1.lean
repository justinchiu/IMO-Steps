import Mathlib
import ImoSteps
set_option linter.unusedVariables.analyzeTactics true


open Nat ImoSteps

theorem imo_1982_p1
  (f : ℕ → ℤ)
  (h₀ : ∀ m n, (0 < m ∧ 0 < n) → f (m + n) - f m - f n = 0 ∨ f (m + n) - f m - f n = 1)
  (h₁ : f 2 = 0)
  (h₂ : 0 < f 3)
  (h₃ : f 9999 = 3333) :
  f 1982 = 660 := by
  have h₀' : ∀ m n, 0 < m → 0 < n → f (m + n) - f m - f n ∈ ({0, 1} : Set ℤ) := by
    intros m n hm hn
    have := h₀ m n ⟨hm, hn⟩
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact this
  have h₀₀ := subadditive_of_delta h₀'
  have h₀₁ := mult_bound_of_subadditive h₀₀
  have h₄: f 3 = 1 := by
    have g₀ : 3333 * f 3 ≤ f (9999) := by
      have := h₀₁ 3 3333 (by omega : 0 < 3) (by omega : 0 < 3333)
      simp only [mul_comm 3333 3] at this
      exact this
    linarith
  have h₅: f 1980 = 660 := by
    have h₅₀: f 1980 ≤ 660 := by
      have g₀ : f (5 * 1980) + f 99 ≤ f (9999) := by
        have := h₀₀ (5 * 1980) 99 (by omega) (by omega)
        simp only [add_comm (5 * 1980) 99, mul_comm 5 1980] at this ⊢
        norm_num at this ⊢
        exact this
      have g₁: 5 * f (1980) ≤ f (5 * 1980) := by
        exact h₀₁ 1980 5 (by omega) (by omega)
      have g₂: 33 * f 3 ≤ f 99 := by
        have := h₀₁ 3 33 (by omega) (by omega)
        simp only [mul_comm 33 3] at this
        norm_num at this
        exact this
      rw [h₃] at g₀
      linarith
    have h₅₁: 660 ≤ f 1980 := by
      have g₀ : 660 * f 3 ≤ f (1980) := by
        have := h₀₁ 3 660 (by omega) (by omega)
        simp only [mul_comm 660 3] at this
        norm_num at this
        exact this
      rw [h₄] at g₀
      exact g₀
    exact le_antisymm h₅₀ h₅₁
  have h₆: f 1982 - f 1980 - f 2 = 0 ∨ f 1982 - f 1980 - f 2 = 1 := by
    refine h₀ 1980 2 ?_
    omega
  cases' h₆ with h₆₀ h₆₁
  . linarith
  . exfalso
    rw [h₅, h₁] at h₆₁
    have h₆₂: f 1982 = 661 := by
      linarith
    have h₆₃: 5 * f 1982 + 29 ≤ 3333 := by
      have g₀ : f (5 * 1982) + f 89 ≤ f 9999 := by
        have := h₀₀ (5 * 1982) 89 (by omega) (by omega)
        simp only [add_comm (5 * 1982), mul_comm 5] at this ⊢
        norm_num at this ⊢
        exact this
      have g₁: f (29 * 3) + f 2 ≤ f 89 := by
        have := h₀₀ (29 * 3) 2 (by omega) (by omega)
        simp only [add_comm (29 * 3), mul_comm 29] at this ⊢
        norm_num at this ⊢
        exact this
      have g₂: 5 * f (1982) ≤ f (5 * 1982) := by
        exact h₀₁ 1982 5 (by omega) (by omega)
      have g₃: 29 * f 3 ≤ f (87) := by
        have := h₀₁ 3 29 (by omega) (by omega)
        simp only [mul_comm 29 3] at this
        norm_num at this
        exact this
      linarith
    rw [h₆₂] at h₆₃
    linarith
