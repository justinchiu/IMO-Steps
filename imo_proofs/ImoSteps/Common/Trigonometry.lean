/-
Copyright (c) 2024 IMO-Steps Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Mathlib

/-!
# Common Trigonometric Lemmas for IMO Problems

This module contains frequently used trigonometric identities.
-/

namespace ImoSteps.Common.Trigonometry

open Real

/-- Sine is bounded -/
@[simp] lemma sin_bound' : ∀ α : ℝ, |sin α| ≤ 1 := 
  abs_sin_le_one

/-- Cosine is bounded -/
@[simp] lemma cos_bound' : ∀ α : ℝ, |cos α| ≤ 1 := 
  abs_cos_le_one

end ImoSteps.Common.Trigonometry