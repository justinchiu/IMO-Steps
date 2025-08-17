import Mathlib

open Real

theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (ha : 0 < a)
    (hf : ∀ x, f (x + a) = 1/2 + sqrt (f x - (f x)^2))
    (hbounds : ∀ x, 1/2 ≤ f x ∧ f x ≤ 1) :
    ∃ b > 0, ∀ x, f (x + b) = f x := by
  use 2*a
  refine ⟨mul_pos two_pos ha, fun x => ?_⟩
  have key : f (x + a) - (f (x + a))^2 = (f x - 1/2)^2 := by
    have h := hf x
    rw [h, add_sq, sub_sq]
    simp [sq_sqrt (by nlinarith [hbounds x] : 0 ≤ f x - (f x)^2)]
    ring
  calc f (x + 2*a) 
    = f ((x + a) + a) := by ring_nf
    _ = 1/2 + sqrt (f (x + a) - (f (x + a))^2) := hf (x + a)
    _ = 1/2 + sqrt ((f x - 1/2)^2) := by rw [key]
    _ = 1/2 + |f x - 1/2| := by rw [sqrt_sq]
    _ = f x := by nlinarith [hbounds x]