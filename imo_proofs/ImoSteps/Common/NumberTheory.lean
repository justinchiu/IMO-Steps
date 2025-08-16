/-
Copyright (c) 2024 IMO-Steps Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Mathlib

/-!
# Common Number Theory Lemmas for IMO Problems

This module contains frequently used number theory lemmas extracted from IMO solutions.
-/

namespace ImoSteps.Common.NumberTheory

open Nat

/-- GCD absorbs multiplication on one side -/
lemma gcd_mul_left_cancel {a b k : ℕ} : 
  Nat.gcd (k * a) (k * b) = k * Nat.gcd a b := by
  rw [Nat.gcd_mul_left]

/-- Common pattern in number theory problems -/
lemma gcd_eq_one_of_coprime {a b : ℕ} (h : Coprime a b) : Nat.gcd a b = 1 := h

/-- Prime is greater than one -/
lemma prime_gt_one {p : ℕ} (hp : p.Prime) : 1 < p := hp.one_lt

end ImoSteps.Common.NumberTheory