import Mathlib

set_option linter.unusedVariables.analyzeTactics true

open Nat BigOperators Finset



lemma aux_1_int
  (a : ℤ) :
  ¬ a ^ 2 ≡ 2 [ZMOD 5] := by
  intro ha₀
  let b:ℤ := a % 5
  have hb₀: b < 5 := by omega
  have hb₁: 0 ≤ b := by omega
  have hb₂: a ≡ b [ZMOD 5] := by exact Int.ModEq.symm (Int.mod_modEq a 5)
  have hb₃: a ^ 2 ≡ b ^ 2 [ZMOD 5] := by exact Int.ModEq.pow 2 hb₂
  interval_cases b
  . norm_num at hb₃
    have g₀: 2 ≡ 0 [ZMOD 5] := by
      exact Int.ModEq.trans ha₀.symm hb₃
    have g₁: ¬ 2 ≡ 0 [ZMOD 5] := by decide
    exact g₁ g₀
  . norm_num at hb₃
    have g₀: 2 ≡ 1 [ZMOD 5] := by
      exact Int.ModEq.trans ha₀.symm hb₃
    have g₁: ¬ 2 ≡ 1 [ZMOD 5] := by decide
    exact g₁ g₀
  . norm_num at hb₃
    have g₀: 2 ≡ 4 [ZMOD 5] := by
      exact Int.ModEq.trans ha₀.symm hb₃
    have g₁: ¬ 2 ≡ 4 [ZMOD 5] := by decide
    exact g₁ g₀
  . norm_num at hb₃
    have g₀: 2 ≡ 9 [ZMOD 5] := by
      exact Int.ModEq.trans ha₀.symm hb₃
    have g₁: ¬ 2 ≡ 9 [ZMOD 5] := by decide
    exact g₁ g₀
  . norm_num at hb₃
    have g₀: 2 ≡ 16 [ZMOD 5] := by
      exact Int.ModEq.trans ha₀.symm hb₃
    have g₁: ¬ 2 ≡ 16 [ZMOD 5] := by decide
    exact g₁ g₀
