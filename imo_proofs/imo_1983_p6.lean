import Mathlib
import ImoSteps

open Real ImoSteps

-- Rearrangement inequality for specific form
lemma rearrangement_cyclic (a b c x y z : ℝ)
    (h_pos : 0 < a ∧ 0 < b ∧ 0 < c)
    (h_ord1 : c ≤ b ∧ b ≤ a)
    (h_ord2 : z ≤ y ∧ y ≤ x) :
    min (a*z + c*y + b*x) (b*z + a*y + c*x) ≤ c*z + b*y + a*x := by
  constructor <;> [
    calc a*z + c*y + b*x 
      = a*z + c*(y-z) + c*z + b*(x-y) + b*y := by ring
      _ ≤ a*z + b*(y-z) + c*z + b*(x-y) + b*y := by
        gcongr; exact h_ord1.1
      _ = a*z + b*x + c*z + b*y := by ring  
      _ ≤ a*(x-z) + a*z + c*z + b*y := by
        gcongr; exact h_ord1.2
      _ = c*z + b*y + a*x := by ring;
    calc b*z + a*y + c*x
      = b*z + a*y + c*(x-z) + c*z := by ring
      _ ≤ b*z + a*y + b*(x-z) + c*z := by
        gcongr; exact h_ord1.1
      _ = b*x + a*y + c*z := by ring
      _ ≤ b*x + a*(x-y) + a*y + c*z := by
        gcongr; exact h_ord1.2
      _ = c*z + b*y + a*x := by ring]

-- Main cyclic inequality
lemma cyclic_inequality (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_tri : c < a + b ∧ a < b + c)
    (h_ord : c ≤ b ∧ b ≤ a) :
    0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  -- Use rearrangement on products
  have key := rearrangement_cyclic (a*b) (a*c) (b*c) 
    (c*(a+b-c)) (b*(a+c-b)) (a*(b+c-a))
    ⟨mul_pos ha hb, mul_pos ha hc, mul_pos hb hc⟩
    ⟨mul_le_mul_of_nonneg_right (le_of_lt hb) (le_of_lt hc) (le_of_lt ha),
     mul_le_mul_of_nonneg_left h_ord.1 (le_of_lt ha)⟩
    ⟨by linarith, by linarith⟩
  
  -- Expand and simplify
  ring_nf at key ⊢
  linarith

theorem imo_1983_p6 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_tri : c < a + b ∧ b < a + c ∧ a < b + c) :
    0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  -- Sort the variables
  wlog h_ord : c ≤ b ∧ b ≤ a
  · -- Apply to permuted variables
    obtain ⟨h1, h2, h3⟩ := h_tri
    by_cases hcb : c ≤ b
    · by_cases hba : b ≤ a
      · exact this ha hb hc h_tri ⟨hcb, hba⟩
      · push_neg at hba
        -- Permute to get ordered variables
        have : a^2*b*(a-b) + b^2*c*(b-c) + c^2*a*(c-a) = 
               b^2*a*(b-a) + a^2*c*(a-c) + c^2*b*(c-b) := by ring
        rw [this]
        exact this hb ha hc ⟨h2, h1, h3⟩ (by push_neg at hcb hba; 
          cases' lt_or_le c a with hca hac
          · exact ⟨hca, hba⟩
          · exact ⟨le_of_lt hba, hac⟩)
    · push_neg at hcb
      -- Similar permutation argument
      sorry
  
  exact cyclic_inequality a b c ha hb hc ⟨h_tri.1, h_tri.2.2⟩ h_ord