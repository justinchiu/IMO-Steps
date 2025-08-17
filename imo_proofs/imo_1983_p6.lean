import Mathlib
import ImoSteps

open Real ImoSteps

-- Specialized cyclic inequality
lemma cyclic_inequality (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_tri : c < a + b ∧ a < b + c)
    (h_ord : c ≤ b ∧ b ≤ a) :
    0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  -- Direct application of rearrangement inequality
  have r1 := rearrangement_three c b a (c*(a+b-c)) (b*(a+c-b)) (a*(b+c-a))
    h_ord.1 h_ord.2 (by linarith) (by linarith)
  ring_nf at r1 ⊢
  -- The rearranged form gives us the desired inequality
  calc a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a)
    = a * b * (a^2 - a * b) + b * c * (b^2 - b * c) + c * a * (c^2 - a * c) := by ring
    _ = a * b * a * (a - b) + b * c * b * (b - c) + c * a * c * (c - a) := by ring
    _ ≥ 0 := by linarith [r1, mul_pos ha hb, mul_pos hb hc, mul_pos hc ha]

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
      -- c > b, need to check other orderings
      by_cases hac : a ≤ c
      · -- Order is b ≤ a ≤ c, permute cyclically
        have : a^2*b*(a-b) + b^2*c*(b-c) + c^2*a*(c-a) = 
               c^2*b*(c-b) + b^2*a*(b-a) + a^2*c*(a-c) := by ring
        rw [this]
        exact this hc hb ha ⟨h1, h3, h2⟩ ⟨le_of_lt hcb, le_of_lt (lt_of_not_le hba)⟩
      · -- Order is b < c < a, permute 
        push_neg at hac
        have : a^2*b*(a-b) + b^2*c*(b-c) + c^2*a*(c-a) = 
               a^2*c*(a-c) + c^2*b*(c-b) + b^2*a*(b-a) := by ring
        rw [this]
        exact this ha hc hb ⟨h2, h3, h1⟩ ⟨le_of_lt hcb, le_of_lt hac⟩
  
  exact cyclic_inequality a b c ha hb hc ⟨h_tri.1, h_tri.2.2⟩ h_ord