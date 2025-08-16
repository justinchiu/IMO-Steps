/-
Copyright (c) 2024 IMO-Steps Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Mathlib

/-!
# Common Algebraic Lemmas for IMO Problems

This module contains frequently used algebraic identities and manipulations.
-/

namespace ImoSteps.Common.Algebra

variable {α : Type*} [CommRing α]

/-- Difference of squares -/
@[simp] lemma diff_of_squares (a b : α) : a^2 - b^2 = (a - b) * (a + b) := by
  ring

/-- Complete square expansion -/
@[simp] lemma complete_square (a b : α) : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  ring

/-- Complete square for difference -/
@[simp] lemma complete_square_sub (a b : α) : (a - b)^2 = a^2 - 2*a*b + b^2 := by
  ring

/-- Sum of cubes -/
@[simp] lemma sum_of_cubes (a b : α) : a^3 + b^3 = (a + b) * (a^2 - a*b + b^2) := by
  ring

/-- Difference of cubes -/
@[simp] lemma diff_of_cubes (a b : α) : a^3 - b^3 = (a - b) * (a^2 + a*b + b^2) := by
  ring

section Real

variable {a b c : ℝ}

/-- Square root of square -/
@[simp] lemma sqrt_sq_eq_abs (a : ℝ) : Real.sqrt (a^2) = |a| := by
  exact Real.sqrt_sq_eq_abs a

/-- Square of square root -/
@[simp] lemma sq_sqrt_eq_self (a : ℝ) (ha : 0 ≤ a) : (Real.sqrt a)^2 = a := by
  exact Real.sq_sqrt ha

end Real

end ImoSteps.Common.Algebra