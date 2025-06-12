import Mathlib

set_option linter.unusedVariables.analyzeTactics true
set_option linter.unusedVariables.analyzeTactics true
set_option pp.instanceTypes true
set_option pp.numericTypes true
set_option pp.coercions.types true
set_option pp.letVarTypes true
set_option pp.structureInstanceTypes true
set_option pp.instanceTypes true
set_option pp.mvars.withType true
set_option pp.coercions true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

open Real


/-- Let $a$ be a positive real number and $f$ be a real function such that $\\forall x \\in \\mathbb{R}, f(x+a)=\\frac{1}{2}+\\sqrt{f(x)-f(x)^2}$.
  Show that there exists a positive real number $b$ such that $\\forall x \\in \\mathbb{R}, f(x+b)=f(x)$.-/

theorem imo_1968_p5_1
  (a : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < a)
  (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - (f x)^2))
  (h₂ : ∀ x, 1 / 2 ≤ f x ∧ f x ≤ 1) :
  ∃ b > 0, ∀ (x:ℝ), f (x + b) = f x := by
  use (2 * a)
  constructor
  . exact mul_pos (by norm_num) h₀
  . intro x
    have h₃: f (x + a) = 1 / 2 + Real.sqrt (f x - (f x)^2) := by
      exact h₁ x
    have h₄: f (x + 2 * a) = 1 / 2 + Real.sqrt (f (x + a) - (f (x + a)^2)) := by
      rw [two_mul, ← add_assoc]
      exact h₁ (x + a)
    have h₅: f (x + a) - (f (x + a) ^ 2) = (f x - 1 / 2) ^ 2 := by
      have h₅₁: 0 ≤ f x - (f x)^2 := by
        refine sub_nonneg_of_le ?_
        rw [pow_two]
        nth_rw 3 [← mul_one (f x)]
        refine (mul_le_mul_left ?_).mpr ?_
        . linarith [h₂ x]
        . exact (h₂ x).2
      rw [h₃, add_sq, sub_sq, sq_sqrt h₅₁]
      ring_nf
    rw [h₅, sqrt_sq ?_] at h₄
    . linarith
    . have h₆: 1 / 2 ≤ f x := by
        exact (h₂ x).1
      linarith [h₆]
