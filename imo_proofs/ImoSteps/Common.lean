import Mathlib

namespace ImoSteps.Common

-- ==============
-- Number Theory
-- ==============
namespace NumberTheory

open Nat

lemma not_sq_mod_5 (a : ℕ) : ¬ a ^ 2 ≡ 2 [MOD 5] ∧ ¬ a ^ 2 ≡ 3 [MOD 5] := by
  constructor
  . intro ha₀
    induction' a with n hn
    . simp at ha₀
      have ha₁: ¬ 0 ≡ 2 [MOD 5] := by decide
      exact ha₁ ha₀
    . let b:ℕ := n % 5
      have hb₀: b < 5 := by omega
      have hb₁: n ≡ b [MOD 5] := by exact Nat.ModEq.symm (Nat.mod_modEq n 5)
      have hb₂: (n + 1) ≡ (b + 1) [MOD 5] := by
        exact Nat.ModEq.add_right 1 hb₁
      have hb₃: (n + 1) ^ 2 ≡ (b + 1) ^ 2 [MOD 5] := by
        exact Nat.ModEq.pow 2 hb₂
      interval_cases b
      . simp at *
        have g₀: 1 ≡ 2 [MOD 5] := by
          refine Nat.ModEq.trans hb₃.symm ha₀
        have g₁: ¬ 1 ≡ 2 [MOD 5] := by decide
        exact g₁ g₀
      . simp at hb₃
        have g₀: 4 ≡ 2 [MOD 5] := by
          refine Nat.ModEq.trans hb₃.symm ha₀
        have g₁: ¬ 4 ≡ 2 [MOD 5] := by decide
        exact g₁ g₀
      . simp at hb₃
        have g₀: 9 ≡ 2 [MOD 5] := by
          refine Nat.ModEq.trans hb₃.symm ha₀
        have g₁: ¬ 9 ≡ 2 [MOD 5] := by decide
        exact g₁ g₀
      . simp at hb₃
        have g₀: 16 ≡ 2 [MOD 5] := by
          refine Nat.ModEq.trans hb₃.symm ha₀
        have g₁: ¬ 16 ≡ 2 [MOD 5] := by decide
        exact g₁ g₀
      . simp at hb₃
        have g₀: 25 ≡ 2 [MOD 5] := by
          refine Nat.ModEq.trans hb₃.symm ha₀
        have g₁: ¬ 25 ≡ 2 [MOD 5] := by decide
        exact g₁ g₀
  . intro ha₀
    induction' a with n hn
    . simp at ha₀
      have ha₁: ¬ 0 ≡ 3 [MOD 5] := by decide
      exact ha₁ ha₀
    . let b:ℕ := n % 5
      have hb₀: b < 5 := by omega
      have hb₁: n ≡ b [MOD 5] := by exact Nat.ModEq.symm (Nat.mod_modEq n 5)
      have hb₂: (n + 1) ≡ (b + 1) [MOD 5] := by
        exact Nat.ModEq.add_right 1 hb₁
      have hb₃: (n + 1) ^ 2 ≡ (b + 1) ^ 2 [MOD 5] := by
        exact Nat.ModEq.pow 2 hb₂
      interval_cases b
      . simp at *
        have g₀: 1 ≡ 3 [MOD 5] := by
          refine Nat.ModEq.trans hb₃.symm ha₀
        have g₁: ¬ 1 ≡ 3 [MOD 5] := by decide
        exact g₁ g₀
      . simp at hb₃
        have g₀: 4 ≡ 3 [MOD 5] := by
          refine Nat.ModEq.trans hb₃.symm ha₀
        have g₁: ¬ 4 ≡ 3 [MOD 5] := by decide
        exact g₁ g₀
      . simp at hb₃
        have g₀: 9 ≡ 3 [MOD 5] := by
          refine Nat.ModEq.trans hb₃.symm ha₀
        have g₁: ¬ 9 ≡ 3 [MOD 5] := by decide
        exact g₁ g₀
      . simp at hb₃
        have g₀: 16 ≡ 3 [MOD 5] := by
          refine Nat.ModEq.trans hb₃.symm ha₀
        have g₁: ¬ 16 ≡ 3 [MOD 5] := by decide
        exact g₁ g₀
      . simp at hb₃
        have g₀: 25 ≡ 3 [MOD 5] := by
          refine Nat.ModEq.trans hb₃.symm ha₀
        have g₁: ¬ 25 ≡ 3 [MOD 5] := by decide
        exact g₁ g₀

end NumberTheory

-- ==============
-- Algebra
-- ==============
namespace Algebra

open Real

lemma le_sq_of_sub_mul_sub (a b c : ℝ) : (a + b - c) * (a + c - b) ≤ a ^ 2 := by
  have h1: (a + b - c) * (a + c - b) = a ^ 2 - (b - c) ^ 2 := by
    linarith
  have h2: 0 ≤ (b - c) ^ 2 := by exact pow_two_nonneg (b - c)
  rw [h1]
  exact sub_le_self _ h2

lemma rearrangement_inequality
  (a b c x y z : ℝ)
  (h_a_pos : 0 < a) (h_b_pos : 0 < b) (_h_c_pos : 0 < c)
  (h_a_ord : c ≤ b ∧ b ≤ a)
  (h_x_ord : z ≤ y ∧ y ≤ x) :
  a * z + c * y + b * x ≤ c * z + b * y + a * x := by
  suffices h₄: c * (y - z) + b * (x - y) ≤ a * (x - z)
  . linarith
  . have h₅: c * (y - z) + b * (x - y) ≤ b * (y - z) + b * (x - y) := by
      simp
      refine mul_le_mul h_a_ord.1 ?_ ?_ ?_
      . exact le_rfl
      . exact sub_nonneg_of_le h_x_ord.1
      . exact le_of_lt h_b_pos
    refine le_trans h₅ ?_
    rw [mul_sub, mul_sub, add_comm]
    rw [← add_sub_assoc, sub_add_cancel]
    rw [← mul_sub]
    refine mul_le_mul h_a_ord.2 ?_ ?_ ?_
    . exact le_rfl
    . refine sub_nonneg_of_le ?_
      exact le_trans h_x_ord.1 h_x_ord.2
    . exact le_of_lt h_a_pos

end Algebra

-- ==============
-- Trigonometry
-- ==============
namespace Trigonometry

lemma sin_mul_cos (x y : ℝ) : Real.sin x * Real.cos y = (Real.sin (x + y) + Real.sin (x - y)) / 2 := by
  rw [Real.sin_add, Real.sin_sub]
  ring

end Trigonometry

end ImoSteps.Common