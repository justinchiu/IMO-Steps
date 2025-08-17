import Mathlib
import ImoSteps

open Real ImoSteps

theorem imo_1964_p2 (a b c : ℝ) 
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_tri : c < a + b ∧ b < a + c ∧ a < b + c) :
    a^2*(b + c - a) + b^2*(c + a - b) + c^2*(a + b - c) ≤ 3*a*b*c := by
  have prod_bound : (a + b - c)*(a + c - b)*(b + c - a) ≤ a*b*c := by
    have : ((a + b - c)*(a + c - b)*(b + c - a))^2 ≤ (a*b*c)^2 := by
      calc ((a + b - c)*(a + c - b)*(b + c - a))^2
        = ((a + b - c)*(a + c - b))*((a + b - c)*(b + c - a))*((a + c - b)*(b + c - a)) := by ring
        _ ≤ a^2 * b^2 * c^2 := by
          apply mul_le_mul (mul_le_mul (triangle_aux a b c) 
            (by rw [add_comm a b]; exact triangle_aux b a c) _ _) 
            (by rw [add_comm a c, add_comm b c]; exact triangle_aux c a b) <;> positivity
        _ = (a*b*c)^2 := by ring
    exact le_of_sq_le_sq (mul_pos (mul_pos ha hb) hc |>.le) this
  linarith