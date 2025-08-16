/-
Copyright (c) 2024 IMO-Steps Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Mathlib

/-!
# Common Inequality Lemmas for IMO Problems

This module contains frequently used inequalities including AM-GM and basic positivity lemmas.
-/

namespace ImoSteps.Common.Inequalities

open Real

variable {a b c d : ℝ}

/-- AM-GM inequality for two variables -/
lemma am_gm_two (ha : 0 ≤ a) (hb : 0 ≤ b) : sqrt (a * b) ≤ (a + b) / 2 := by
  sorry

/-- Square is nonnegative -/
@[simp] lemma sq_nonneg' (a : ℝ) : 0 ≤ a^2 := by
  exact sq_nonneg a

/-- Square root is nonnegative -/
@[simp] lemma sqrt_nonneg' (a : ℝ) : 0 ≤ sqrt a := by
  exact sqrt_nonneg a

/-- Absolute value is nonnegative -/
@[simp] lemma abs_nonneg' (a : ℝ) : 0 ≤ |a| := by
  exact abs_nonneg a

end ImoSteps.Common.Inequalities