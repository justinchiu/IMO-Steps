import Mathlib

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



/- Solve the system of equations\n\n$|a_1 - a_2| x_2 +|a_1 - a_3| x_3 +|a_1 - a_4| x_4 = 1\\\\ |a_2 - a_1| x_1 +|a_2 - a_3| x_3 +|a_2 - a_4| x_4 = 1\\\\ |a_3 - a_1| x_1 +|a_3 - a_2| x_2 +|a_3-a_4|x_4= 1\\\\ |a_4 - a_1| x_1 +|a_4 - a_2| x_2 +|a_4 - a_3| x_3 = 1$\n\
  where $a_1, a_2, a_3, a_4$ are four different real numbers and a_1 > a_2 > a_3 > a_4.
  Prove the following equalities:
  1. x 1 = 1 / (a 1 - a 4)
  2. x 2 = 0
  3. x 3 = 0
  4. x 4 = x 1
  -/

open Real Finset




lemma aux_3
  (x a : ℕ → ℝ)
  (j k l : ℕ)
  (h₆ : |a (1 : ℕ) - a (2 : ℕ)| * x (2 : ℕ) + |a (1 : ℕ) - a (3 : ℕ)| * x (3 : ℕ) + |a (1 : ℕ) - a (4 : ℕ)| * x (4 : ℕ) = (1 : ℝ))
  (h₇ : |a (2 : ℕ) - a (1 : ℕ)| * x (1 : ℕ) + |a (2 : ℕ) - a (3 : ℕ)| * x (3 : ℕ) + |a (2 : ℕ) - a (4 : ℕ)| * x (4 : ℕ) = (1 : ℝ))
  (h₈ : |a (3 : ℕ) - a (1 : ℕ)| * x (1 : ℕ) + |a (3 : ℕ) - a (2 : ℕ)| * x (2 : ℕ) + |a (3 : ℕ) - a (4 : ℕ)| * x (4 : ℕ) = (1 : ℝ))
  (h₉ : |a (4 : ℕ) - a (1 : ℕ)| * x (1 : ℕ) + |a (4 : ℕ) - a (2 : ℕ)| * x (2 : ℕ) + |a (4 : ℕ) - a (3 : ℕ)| * x (3 : ℕ) = (1 : ℝ))
  (hhk : k ≠ l)
  (hj₀ : (1 : ℕ) ≤ j)
  (hj₁ : j < (4 : ℕ))
  (hk₀ : (1 : ℕ) ≤ k)
  (hk₁ : k < (4 : ℕ))
  (hl₀ : (1 : ℕ) ≤ l)
  (hl₁ : l < (4 : ℕ))
  (hhj₀ : j ≠ k)
  (hhj₁ : j ≠ l) :
  |a l - a k| * x k + |a l - a j| * x j + |a l - a (4 : ℕ)| * x (4 : ℕ) = (1 : ℝ) ∧
    |a k - a l| * x l + |a k - a j| * x j + |a k - a (4 : ℕ)| * x (4 : ℕ) = (1 : ℝ) ∧
      |a j - a l| * x l + |a j - a k| * x k + |a j - a (4 : ℕ)| * x (4 : ℕ) = (1 : ℝ) ∧
        |a (4 : ℕ) - a l| * x l + |a (4 : ℕ) - a k| * x k + |a (4 : ℕ) - a j| * x j = (1 : ℝ) := by
  interval_cases j
  . interval_cases k
    . simp at hhj₀
    . interval_cases l
      . simp at hhj₁
      . simp at hhk
      . constructor
        . linarith
        constructor
        . linarith
        constructor
        . linarith
        . linarith
    . interval_cases l
      . simp at hhj₁
      . constructor
        . linarith
        constructor
        . linarith
        constructor
        . linarith
        . linarith
      . simp at hhk
  . interval_cases k
    . interval_cases l
      . simp at hhk
      . simp at hhj₁
      . constructor
        . linarith
        constructor
        . linarith
        constructor
        . linarith
        . linarith
    . simp at hhj₀
    . interval_cases l
      . constructor
        . linarith
        constructor
        . linarith
        constructor
        . linarith
        . linarith
      . simp at hhj₁
      . simp at hhk
  . interval_cases k
    . interval_cases l
      . simp at hhk
      . constructor
        . linarith
        constructor
        . linarith
        constructor
        . linarith
        . linarith
      . simp at hhj₁
    . interval_cases l
      . constructor
        . linarith
        constructor
        . linarith
        constructor
        . linarith
        . linarith
      . simp at hhk
      . simp at hhj₁
    . simp at hhj₀



lemma aux_2
  (x a : ℕ → ℝ)
  (j k l : ℕ)
  (h₆ : |a (1 : ℕ) - a (2 : ℕ)| * x (2 : ℕ) + |a (1 : ℕ) - a (3 : ℕ)| * x (3 : ℕ) + |a (1 : ℕ) - a (4 : ℕ)| * x (4 : ℕ) = (1 : ℝ))
  (h₇ : |a (2 : ℕ) - a (1 : ℕ)| * x (1 : ℕ) + |a (2 : ℕ) - a (3 : ℕ)| * x (3 : ℕ) + |a (2 : ℕ) - a (4 : ℕ)| * x (4 : ℕ) = (1 : ℝ))
  (h₈ : |a (3 : ℕ) - a (1 : ℕ)| * x (1 : ℕ) + |a (3 : ℕ) - a (2 : ℕ)| * x (2 : ℕ) + |a (3 : ℕ) - a (4 : ℕ)| * x (4 : ℕ) = (1 : ℝ))
  (h₉ : |a (4 : ℕ) - a (1 : ℕ)| * x (1 : ℕ) + |a (4 : ℕ) - a (2 : ℕ)| * x (2 : ℕ) + |a (4 : ℕ) - a (3 : ℕ)| * x (3 : ℕ) = (1 : ℝ))
  (hhk : k ≠ l)
  (hj₀ : (1 : ℕ) ≤ j)
  (hj₁ : j ≤ (4 : ℕ))
  (hk₀ : (1 : ℕ) ≤ k)
  (hk₁ : k ≤ (4 : ℕ))
  (hl₀ : (1 : ℕ) ≤ l)
  (hl₁ : l ≤ (4 : ℕ))
  (hhj₀ : j ≠ k)
  (hhj₁ : j ≠ l)
  (hhi₀ : (3 : ℕ) ≠ j)
  (hhi₁ : (3 : ℕ) ≠ k)
  (hhi₂ : (3 : ℕ) ≠ l) :
  |a l - a k| * x k + |a l - a j| * x j + |a l - a (3 : ℕ)| * x (3 : ℕ) = (1 : ℝ) ∧
    |a k - a l| * x l + |a k - a j| * x j + |a k - a (3 : ℕ)| * x (3 : ℕ) = (1 : ℝ) ∧
      |a j - a l| * x l + |a j - a k| * x k + |a j - a (3 : ℕ)| * x (3 : ℕ) = (1 : ℝ) ∧
        |a (3 : ℕ) - a l| * x l + |a (3 : ℕ) - a k| * x k + |a (3 : ℕ) - a j| * x j = (1 : ℝ) := by
  interval_cases j
  . interval_cases k
    . simp at hhj₀
    . interval_cases l
      . simp at hhj₁
      . simp at hhk
      . simp at hhi₂
      . constructor
        . linarith
        constructor
        . linarith
        constructor
        . linarith
        . linarith
    . simp at hhi₁
    . interval_cases l
      . simp at hhj₁
      . constructor
        . linarith
        constructor
        . linarith
        constructor
        . linarith
        . linarith
      . simp at hhi₂
      . simp at hhk
  . interval_cases k
    . interval_cases l
      . simp at hhk
      . simp at hhj₁
      . simp at hhi₂
      . constructor
        . bound
        constructor
        . bound
        constructor
        . bound
        . bound
    . simp at hhj₀
    . simp at hhi₁
    . interval_cases l
      . constructor
        . linarith
        constructor
        . linarith
        constructor
        . linarith
        . linarith
      . simp at hhj₁
      . simp at hhi₂
      . simp at hhk
  . simp at hhi₀
  . interval_cases k
    . interval_cases l
      . simp at hhk
      . constructor
        . linarith
        constructor
        . linarith
        constructor
        . bound
        . bound
      . simp at hhi₂
      . simp at hhj₁
    . interval_cases l
      . constructor
        . bound
        constructor
        . bound
        constructor
        . bound
        . bound
      . simp at hhk
      . simp at hhi₂
      . simp at hhj₁
    . simp at hhi₁
    . simp at hhj₀


lemma aux_1
  (x a : ℕ → ℝ)
  (i j k l : ℕ)
  (s : Finset ℕ)
  (hs₀ : s = Icc (1 : ℕ) (4 : ℕ))
  (h₆ : |a (1 : ℕ) - a (2 : ℕ)| * x (2 : ℕ) + |a (1 : ℕ) - a (3 : ℕ)| * x (3 : ℕ) + |a (1 : ℕ) - a (4 : ℕ)| * x (4 : ℕ) = (1 : ℝ))
  (h₇ : |a (2 : ℕ) - a (1 : ℕ)| * x (1 : ℕ) + |a (2 : ℕ) - a (3 : ℕ)| * x (3 : ℕ) + |a (2 : ℕ) - a (4 : ℕ)| * x (4 : ℕ) = (1 : ℝ))
  (h₈ : |a (3 : ℕ) - a (1 : ℕ)| * x (1 : ℕ) + |a (3 : ℕ) - a (2 : ℕ)| * x (2 : ℕ) + |a (3 : ℕ) - a (4 : ℕ)| * x (4 : ℕ) = (1 : ℝ))
  (h₉ : |a (4 : ℕ) - a (1 : ℕ)| * x (1 : ℕ) + |a (4 : ℕ) - a (2 : ℕ)| * x (2 : ℕ) + |a (4 : ℕ) - a (3 : ℕ)| * x (3 : ℕ) = (1 : ℝ))
  (hs₇ : i ∈ s ∧ j ∈ s ∧ k ∈ s ∧ l ∈ s)
  (hhi : i ≠ j ∧ i ≠ k ∧ i ≠ l)
  (hhj : j ≠ k ∧ j ≠ l)
  (hhk : k ≠ l) :
  |a l - a k| * x k + |a l - a j| * x j + |a l - a i| * x i = (1 : ℝ) ∧
    |a k - a l| * x l + |a k - a j| * x j + |a k - a i| * x i = (1 : ℝ) ∧
      |a j - a l| * x l + |a j - a k| * x k + |a j - a i| * x i = (1 : ℝ) ∧
        |a i - a l| * x l + |a i - a k| * x k + |a i - a j| * x j = (1 : ℝ) := by
  rw [hs₀] at hs₇
  cases' hs₇ with hi₀ hj₀
  cases' hj₀ with hj₀ hk₀
  cases' hk₀ with hk₀ hl₀
  apply mem_Icc.mp at hi₀
  apply mem_Icc.mp at hj₀
  apply mem_Icc.mp at hk₀
  apply mem_Icc.mp at hl₀
  cases' hi₀ with hi₀ hi₁
  cases' hj₀ with hj₀ hj₁
  cases' hk₀ with hk₀ hk₁
  cases' hl₀ with hl₀ hl₁
  cases' hhi with hhi₀ hhi₁
  cases' hhi₁ with hhi₁ hhi₂
  cases' hhj with hhj₀ hhj₁
  interval_cases i
  . interval_cases j
    . simp at hhi₀
    . interval_cases k
      . simp at hhi₁
      . simp at hhj₀
      . interval_cases l
        . simp at hhi₂
        . simp at hhj₁
        . simp at hhk
        . constructor
          . linarith
          constructor
          . linarith
          constructor
          . linarith
          . linarith
      . interval_cases l
        . simp at hhi₂
        . simp at hhj₁
        . constructor
          . linarith
          constructor
          . linarith
          constructor
          . linarith
          . linarith
        . simp at hhk
    . interval_cases k
      . simp at hhi₁
      . interval_cases l
        . simp at hhi₂
        . simp at hhk
        . simp at hhj₁
        . constructor
          . linarith
          constructor
          . linarith
          constructor
          . linarith
          . linarith
      . simp at hhj₀
      . interval_cases l
        . simp at hhi₂
        . constructor
          . linarith
          constructor
          . linarith
          constructor
          . linarith
          . linarith
        . simp at hhj₁
        . simp at hhk
    . interval_cases k
      . simp at hhi₁
      . interval_cases l
        . simp at hhi₂
        . simp at hhk
        . constructor
          . linarith
          constructor
          . linarith
          constructor
          . linarith
          . linarith
        . simp at hhj₁
      . interval_cases l
        . simp at hhi₂
        . constructor
          . linarith
          constructor
          . linarith
          constructor
          . linarith
          . linarith
        . simp at hhk
        . simp at hhj₁
      . simp at hhj₀
  . interval_cases j
    . interval_cases k
      . simp at hhj₀
      . simp at hhi₁
      . interval_cases l
        . simp at hhj₁
        . simp at hhi₂
        . simp at hhk
        . constructor
          . linarith
          constructor
          . linarith
          constructor
          . linarith
          . linarith
      . interval_cases l
        . simp at hhj₁
        . simp at hhi₂
        . constructor
          . linarith
          constructor
          . linarith
          constructor
          . linarith
          . linarith
        . simp at hhk
    . simp at hhi₀
    . interval_cases k
      . interval_cases l
        . simp at hhk
        . simp at hhi₂
        . simp at hhj₁
        . constructor
          . linarith
          constructor
          . linarith
          constructor
          . linarith
          . linarith
      . simp at hhi₁
      . simp at hhj₀
      . interval_cases l
        . constructor
          . linarith
          constructor
          . linarith
          constructor
          . linarith
          . linarith
        . simp at hhi₂
        . simp at hhj₁
        . simp at hhk
    . interval_cases k
      . interval_cases l
        . simp at hhk
        . simp at hhi₂
        . constructor
          . linarith
          constructor
          . linarith
          constructor
          . linarith
          . linarith
        . simp at hhj₁
      . simp at hhi₁
      . interval_cases l
        . constructor
          . linarith
          constructor
          . linarith
          constructor
          . linarith
          . linarith
        . simp at hhi₂
        . simp at hhk
        . simp at hhj₁
      . simp at hhj₀
  . exact aux_2 x a j k l h₆ h₇ h₈ h₉ hhk hj₀ hj₁ hk₀ hk₁ hl₀ hl₁ hhj₀ hhj₁ hhi₀ hhi₁ hhi₂
  . refine aux_3 x a j k l h₆ h₇ h₈ h₉ hhk hj₀ ?_ hk₀ ?_ hl₀ ?_ hhj₀ hhj₁
    . exact Nat.lt_of_le_of_ne hj₁ (Ne.symm hhi₀)
    . exact Nat.lt_of_le_of_ne hk₁ (Ne.symm hhi₁)
    . exact Nat.lt_of_le_of_ne hl₁ (Ne.symm hhi₂)



theorem imo_1966_p5
  (x a : ℕ → ℝ)
  (i j k l : ℕ)
  (s : Finset ℕ)
  (hs₀ : s = Finset.Icc 1 4)
  (h₀ : a 1 ≠ a 2)
  (h₁ : a 1 ≠ a 3)
  (h₂ : a 1 ≠ a 4)
  (h₃ : a 2 ≠ a 3)
  (h₄ : a 2 ≠ a 4)
  (h₅ : a 3 ≠ a 4)
  (h₆ : abs (a 1 - a 2) * x 2 + abs (a 1 - a 3) * x 3 + abs (a 1 - a 4) * x 4 = 1)
  (h₇ : abs (a 2 - a 1) * x 1 + abs (a 2 - a 3) * x 3 + abs (a 2 - a 4) * x 4 = 1)
  (h₈ : abs (a 3 - a 1) * x 1 + abs (a 3 - a 2) * x 2 + abs (a 3 - a 4) * x 4 = 1)
  (h₉ : abs (a 4 - a 1) * x 1 + abs (a 4 - a 2) * x 2 + abs (a 4 - a 3) * x 3 = 1)
  (hs₁: s = {i} ∪ {j} ∪ {k} ∪ {l})
  (hs₂: ∀ m ∈ s, m ≠ i → a i < a m)
  (hs₃: ∀ m ∈ s, m ≠ l → a m < a l):
  x i = 1 / (a l - a i) ∧ x j = 0 ∧ x k = 0 ∧ x l = x i := by
  have hs₄ : Finset.Icc 1 4 = {1,2,3,4} := by decide
  have hs₅ : ∀ m ∈ s, m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by
    intros m hm₀
    simp_all only [union_assoc, ne_eq, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
  have hs₆ : 1 ∈ s ∧ 2 ∈ s ∧ 3 ∈ s ∧ 4 ∈ s := by
    bound
  have hs₇ : i ∈ s ∧ j ∈ s ∧ k ∈ s ∧ l ∈ s := by
    rw [hs₁]
    bound
  have hs₈: ∀ (m n : ℕ), m ∈ s ∧ n ∈ s → m ≠ n → a m ≠ a n := by
    intros m n hmn hm₂
    cases' (hs₅ m hmn.1) with hm₁ hm₁
    all_goals try cases' hm₁ with hm₁ hm₁
    all_goals try rw [hm₁] at hm₂
    all_goals try cases' (hs₅ n hmn.2) with hn₁ hn₁
    all_goals try cases' hn₁ with hn₁ hn₁
    all_goals try cases' hm₁ with hm₁ hm₁
    all_goals try cases' hn₁ with hn₁ hn₁
    all_goals try rw [hm₁]
    all_goals try rw [hn₁]
    all_goals try assumption
    . omega
    . exact id (Ne.symm h₀)
    . omega
    . exact id (Ne.symm h₁)
    . exact id (Ne.symm h₂)
    . exact id (Ne.symm h₃)
    . exact id (Ne.symm h₄)
    . omega
    . exact id (Ne.symm h₅)
    . omega
  rw [union_assoc ({i} ∪ {j})] at hs₁
  have hs₉: s.card = 4 := by
    rw [hs₀]
    exact rfl
  have hhi: i ≠ j ∧ i ≠ k ∧ i ≠ l := by
    constructor
    . by_contra! hh₀
      rw [hh₀] at hs₁
      simp at hs₁
      have hh₁: s.card ≤ 3 := by
        rw [hs₁]
        refine le_trans (Finset.card_union_le _ ({k} ∪ {l})) ?_
        rw [@card_singleton, add_comm]
        refine Nat.add_le_of_le_sub ?_ ?_
        . exact NeZero.one_le
        . refine le_trans (Finset.card_union_le ({k}) ({l})) ?_
          rw [@card_singleton, @card_singleton]
      bound
    constructor
    . by_contra! hh₀
      rw [hh₀, union_comm {k} {j}, ← union_assoc, union_assoc {j}, Finset.union_self {k}] at hs₁
      simp at hs₁
      have hh₁: s.card ≤ 3 := by
        rw [hs₁]
        refine le_trans (Finset.card_union_le _ ({k} ∪ {l})) ?_
        rw [@card_singleton, add_comm]
        refine Nat.add_le_of_le_sub ?_ ?_
        . exact NeZero.one_le
        . refine le_trans (Finset.card_union_le ({k}) ({l})) ?_
          rw [@card_singleton, @card_singleton]
      bound
    . by_contra! hh₀
      rw [hh₀, union_comm ({l} ∪ {j}), ← union_assoc, union_assoc {k}, Finset.union_self {l}] at hs₁
      simp at hs₁
      have hh₁: s.card ≤ 3 := by
        rw [hs₁]
        refine le_trans (Finset.card_union_le _ ({l} ∪ {j})) ?_
        rw [@card_singleton, add_comm]
        refine Nat.add_le_of_le_sub ?_ ?_
        . exact NeZero.one_le
        . refine le_trans (Finset.card_union_le ({l}) ({j})) ?_
          rw [@card_singleton, @card_singleton]
      bound
  have hhj: j ≠ k ∧ j ≠ l := by
    constructor
    . by_contra! hh₀
      rw [hh₀] at hs₁
      simp at hs₁
      have hh₁: s.card ≤ 3 := by
        rw [hs₁]
        refine le_trans (Finset.card_union_le _ ({k} ∪ {l})) ?_
        rw [@card_singleton, add_comm]
        refine Nat.add_le_of_le_sub ?_ ?_
        . exact NeZero.one_le
        . refine le_trans (Finset.card_union_le ({k}) ({l})) ?_
          rw [@card_singleton, @card_singleton]
      bound
    . by_contra! hh₀
      rw [hh₀, union_comm {k} {l}, ← union_assoc, union_assoc {i}, Finset.union_self {l}] at hs₁
      simp at hs₁
      have hh₁: s.card ≤ 3 := by
        rw [hs₁]
        refine le_trans (Finset.card_union_le _ ({l} ∪ {k})) ?_
        rw [@card_singleton, add_comm]
        refine Nat.add_le_of_le_sub ?_ ?_
        . exact NeZero.one_le
        . refine le_trans (Finset.card_union_le ({l}) ({k})) ?_
          rw [@card_singleton, @card_singleton]
      bound
  have hhk: k ≠ l := by
    by_contra! hh₀
    rw [hh₀, Finset.union_self {l}] at hs₁
    have hh₁: s.card ≤ 3 := by
      rw [hs₁]
      simp
      refine le_trans (Finset.card_union_le _ ({j} ∪ {l})) ?_
      rw [@card_singleton, add_comm]
      refine Nat.add_le_of_le_sub ?_ ?_
      . exact NeZero.one_le
      . refine le_trans (Finset.card_union_le ({j}) ({l})) ?_
        rw [@card_singleton, @card_singleton]
    bound
  have hg: (abs (a l - a k) * x k + abs (a l - a j) * x j + abs (a l - a i) * x i = 1) →
    (abs (a k - a l) * x l + abs (a k - a j) * x j + abs (a k - a i) * x i = 1) →
    (abs (a j - a l) * x l + abs (a j - a k) * x k + abs (a j - a i) * x i = 1) →
    (abs (a i - a l) * x l + abs (a i - a k) * x k + abs (a i - a j) * x j = 1) →
    x i = 1 / (a l - a i) ∧ x j = 0 ∧ x k = 0 ∧ x l = x i := by
    intros hg₀ hg₁ hg₂ hg₃
    clear h₆ h₇ h₈ h₉
    have g₀: 0 < a l - a k := by
      refine sub_pos_of_lt ?_
      exact hs₃ k hs₇.2.2.1 hhk
    have g₁: 0 < a l - a j := by
      refine sub_pos_of_lt ?_
      exact hs₃ j hs₇.2.1 hhj.2
    have g₂: 0 < a l - a i := by
      refine sub_pos_of_lt ?_
      exact hs₃ i hs₇.1 hhi.2.2
    have g₃: a k - a l < 0 := by
      refine sub_neg_of_lt ?_
      exact hs₃ k hs₇.2.2.1 hhk
    have g₄: 0 < a k - a i := by
      refine sub_pos_of_lt ?_
      exact hs₂ k hs₇.2.2.1 hhi.2.1.symm
    have g₅: a j - a l < 0 := by
      refine sub_neg_of_lt ?_
      exact hs₃ j hs₇.2.1 hhj.2
    have g₆: 0 < a j - a i := by
      refine sub_pos_of_lt ?_
      exact hs₂ j hs₇.2.1 hhi.1.symm
    have g₇: a i - a l < 0 := by
      refine sub_neg_of_lt ?_
      exact hs₂ l hs₇.2.2.2 hhi.2.2.symm
    have g₈: a i - a k < 0 := by
      refine sub_neg_of_lt ?_
      exact hs₂ k hs₇.2.2.1 hhi.2.1.symm
    have g₉: a i - a j < 0 := by
      refine sub_neg_of_lt ?_
      exact hs₂ j hs₇.2.1 hhi.1.symm
    rw [abs_of_pos g₀, abs_of_pos g₁, abs_of_pos g₂, abs_of_pos g₄, abs_of_pos g₆] at *
    rw [abs_of_neg g₃, abs_of_neg g₅, abs_of_neg g₇, abs_of_neg g₈, abs_of_neg g₉] at *
    rw [neg_sub] at *
    wlog hg₄: a j < a k
    . have hg₅: x i = 1 / (a l - a i) ∧ x k = 0 ∧ x j = 0 ∧ x l = x i := by
        push_neg at hg₄
        have g₁₀: a k < a j := by
          clear this
          refine lt_of_le_of_ne hg₄ ?_
          refine hs₈ k j ?_ ?_
          . constructor
            . exact hs₇.2.2.1
            . exact hs₇.2.1
          . by_contra hc₀
            rw [hc₀, hs₀] at hs₁
            simp at hs₁
            have hc₁: (Finset.Icc 1 4).card = ({i, j, l}:Finset ℕ).card := by exact congrArg card hs₁
            have hc₂: (Finset.Icc 1 4).card = 4 := by decide
            have hc₃: ({i, j, l}:Finset ℕ).card ≤ 3 := by exact card_le_three
            linarith
        have g₁₁: a k - a j < 0 := by exact sub_neg.mpr g₁₀
        have g₁₂: 0 < a j - a k := by exact sub_pos.mpr g₁₀
        refine this x a i k j l s hs₀ h₀ h₁ h₂ h₃ h₄ h₅ ?_ hs₂ hs₃ hs₄ hs₅ hs₆ ?_ hs₈ ?_ ?_ ?_ ?_ (by linarith [g₁]) (by linarith [g₀]) ?_ ?_ ?_ g₀ g₂ g₅ g₆ g₃ g₄ g₇ g₉ g₈ g₁₀
        all_goals clear this
        . rw [hs₁]
          exact union_union_union_comm {i} {j} {k} {l}
        . simp_all only [union_assoc, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, implies_true,]
          decide
        all_goals try rw [abs_of_neg g₁₁] at *
        all_goals try rw [abs_of_pos g₁₂] at *
        all_goals try linarith
        all_goals try bound
      refine and_assoc.mp ?_
      rw [and_and_and_comm]
      refine and_assoc.mpr ?_
      exact hg₅
    . have g₁₀: 0 < a k - a j := by exact sub_pos_of_lt hg₄
      have g₁₁: a j - a k < 0 := by exact sub_neg_of_lt hg₄
      rw [abs_of_pos g₁₀, abs_of_neg g₁₁] at *
      have ho₀: a l - a k ≠ 0 := by exact ne_of_gt g₀
      have ho₁: a j - a i ≠ 0 := by exact ne_of_gt g₆
      have ho₂: a k - a j ≠ 0 := by exact ne_of_gt g₁₀
      have ho₃: a l - a i ≠ 0 := by exact ne_of_gt g₂
      clear g₀ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ g₉ g₁₀ g₁₁
      have hm₀: (a l - a k) * -x l + (a l - a k) * x k + (a l - a k) * x j + (a l - a k) * x i = 0 := by linarith [hg₀, hg₁]
      rw [← mul_add, ← mul_add, ← mul_add] at hm₀
      apply mul_eq_zero.mp at hm₀
      cases' hm₀ with hm₀ hm₀
      . exact False.elim (ho₀ hm₀)
      . have hm₁: (a j - a i) * -x l + (a j - a i) * -x k + (a j - a i) * -x j + (a j - a i) * x i = 0 := by linarith
        rw [← mul_add, ← mul_add, ← mul_add] at hm₁
        apply mul_eq_zero.mp at hm₁
        cases' hm₁ with hm₁ hm₁
        . exact False.elim (ho₁ hm₁)
        . have hr₀: x l = x i := by linarith
          have hm₂: (a k - a j) * -x l + (a k - a j) * -x k + (a k - a j) * x j + (a k - a j) * x i = 0 := by linarith
          rw [← mul_add, ← mul_add, ← mul_add] at hm₂
          apply mul_eq_zero.mp at hm₂
          cases' hm₂ with hm₂ hm₂
          . exact False.elim (ho₂ hm₂)
          . have hr₁: x k = x j := by linarith
            have hr₂: x k = 0 := by linarith
            have hr₃: x i = 1 / (a l - a i) := by
              rw [← hr₁, hr₂] at hg₀
              simp at hg₀
              rw [mul_comm] at hg₀
              exact eq_div_of_mul_eq ho₃ hg₀
            constructor
            . exact hr₃
            constructor
            . rw [← hr₁, hr₂]
            constructor
            . exact hr₂
            . exact hr₀
  have h₁₀: |a l - a k| * x k + |a l - a j| * x j + |a l - a i| * x i = (1 : ℝ) ∧ |a k - a l| * x l + |a k - a j| * x j + |a k - a i| * x i = (1 : ℝ)
    ∧ |a j - a l| * x l + |a j - a k| * x k + |a j - a i| * x i = (1 : ℝ) ∧ |a i - a l| * x l + |a i - a k| * x k + |a i - a j| * x j = (1 : ℝ) := by
    exact aux_1 x a i j k l s hs₀ h₆ h₇ h₈ h₉ hs₇ hhi hhj hhk
  refine hg ?_ ?_ ?_ ?_
  . exact h₁₀.1
  . exact h₁₀.2.1
  . exact h₁₀.2.2.1
  . exact h₁₀.2.2.2


theorem imo_1966_p5_easy
  (x a : ℕ → ℝ)
  (h₀ : a 1 ≠ a 2)
  (h₁ : a 1 ≠ a 3)
  (h₂ : a 1 ≠ a 4)
  (h₃ : a 2 ≠ a 3)
  (h₄ : a 2 ≠ a 4)
  (h₅ : a 3 ≠ a 4)
  (h₆ : a 1 > a 2)
  (h₇ : a 2 > a 3)
  (h₈ : a 3 > a 4)
  (h₉ : abs (a 1 - a 2) * x 2 + abs (a 1 - a 3) * x 3 + abs (a 1 - a 4) * x 4 = 1)
  (h₁₀ : abs (a 2 - a 1) * x 1 + abs (a 2 - a 3) * x 3 + abs (a 2 - a 4) * x 4 = 1)
  (h₁₁ : abs (a 3 - a 1) * x 1 + abs (a 3 - a 2) * x 2 + abs (a 3 - a 4) * x 4 = 1)
  (h₁₂ : abs (a 4 - a 1) * x 1 + abs (a 4 - a 2) * x 2 + abs (a 4 - a 3) * x 3 = 1) :
  x 2 = 0 ∧ x 3 = 0 ∧ x 1 = 1 / abs (a 1 - a 4) ∧ x 4 = 1 / abs (a 1 - a 4) := by
  let s : Finset ℕ := Finset.Icc 1 4
  let i : ℕ := 4
  let j : ℕ := 3
  let k : ℕ := 2
  let l : ℕ := 1
  have hs₂: ∀ b ∈ s, b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by
    intros b hb₀
    apply mem_Icc.mp at hb₀
    omega
  have h₁₃: x i = 1 / (a l - a i) ∧ x j = 0 ∧ x k = 0 ∧ x l = x i := by
    refine imo_1966_p5 x a i j k l s rfl h₀ h₁ h₂ h₃ h₄ h₅ h₉ h₁₀ h₁₁ h₁₂ ?_ ?_ ?_
    . decide
    . intro b hb₀ hb₁
      have hb₂: b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by exact hs₂ b hb₀
      cases' hb₂ with hb₂ hb₂
      . rw [hb₂]
        bound
      cases' hb₂ with hb₂ hb₂
      . rw [hb₂]
        bound
      cases' hb₂ with hb₂ hb₂
      . rw [hb₂]
        bound
      . omega
    . intro b hb₀ hb₁
      have hb₂: b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by exact hs₂ b hb₀
      cases' hb₂ with hb₂ hb₂
      . omega
      cases' hb₂ with hb₂ hb₂
      . rw [hb₂]
        bound
      cases' hb₂ with hb₂ hb₂
      . rw [hb₂]
        bound
      . rw [hb₂]
        bound
  have h₁₄: 0 < a 1 - a 4 := by bound
  constructor
  . exact h₁₃.2.2.1
  constructor
  . exact h₁₃.2.1
  constructor
  . rw [h₁₃.2.2.2, h₁₃.1]
    rw [abs_of_pos h₁₄]
  . rw [h₁₃.1]
    rw [abs_of_pos h₁₄]
