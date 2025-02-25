import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.unusedVariables.analyzeTactics true

open Real

lemma imo_2023_p4_1
  (x a: ℕ → ℝ)
  (hxp: ∀ (i : ℕ), 0 < x i)
  (h₀: ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) :
  ∀ (n : ℕ), (1 ≤ n ∧ n ≤ 2022) → a (n) < a (n + 1) := by
  intros n hn
  have h₂: a n = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
              * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
    refine h₀ n ?_
    constructor
    . exact hn.1
    . linarith
  have h₃: a (n + 1) = sqrt ((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k)
              * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k) := by
    refine h₀ (n + 1) ?_
    constructor
    . linarith
    . linarith
  rw [h₂,h₃]
  refine sqrt_lt_sqrt ?_ ?_
  . refine le_of_lt ?_
    refine mul_pos ?_ ?_
    . refine Finset.sum_pos ?_ ?_
      . exact fun i _ => hxp i
      . simp
        linarith
    . refine Finset.sum_pos ?_ ?_
      . intros i _
        exact one_div_pos.mpr (hxp i)
      . simp
        linarith
  . have g₀: 1 ≤ n + 1 := by linarith
    rw [Finset.sum_Ico_succ_top g₀ _, Finset.sum_Ico_succ_top g₀ _]
    repeat rw [add_mul, mul_add]
    have h₄: 0 < (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
      x (n + 1) * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + 1 / x (n + 1)) := by
        refine add_pos ?_ ?_
        . refine mul_pos ?_ ?_
          . refine Finset.sum_pos ?_ ?_
            . exact fun i _ => hxp i
            . simp
              linarith
          . exact one_div_pos.mpr (hxp (n + 1))
        . refine mul_pos ?_ ?_
          . exact hxp (n + 1)
          . refine add_pos ?_ ?_
            . refine Finset.sum_pos ?_ ?_
              . intros i _
                exact one_div_pos.mpr (hxp i)
              . simp
                linarith
            . exact one_div_pos.mpr (hxp (n + 1))
    linarith


lemma imo_2023_p4_1_1
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
  refine h₀ n ?_
  constructor
  . exact hn.1
  . linarith


lemma imo_2023_p4_1_2
  -- (x a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
  --     Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  1 ≤ n ∧ n ≤ 2023 := by
  constructor
  . exact hn.1
  . linarith


lemma imo_2023_p4_1_3
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022)
  (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) :
  a n < a (n + 1) := by
  have h₃: a (n + 1) = sqrt ((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k)
              * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k) := by
    refine h₀ (n + 1) ?_
    constructor
    . linarith
    . linarith
  rw [h₂,h₃]
  refine sqrt_lt_sqrt ?_ ?_
  . refine le_of_lt ?_
    refine mul_pos ?_ ?_
    . refine Finset.sum_pos ?_ ?_
      . exact fun i _ => hxp i
      . simp
        linarith
    . refine Finset.sum_pos ?_ ?_
      . intros i _
        exact one_div_pos.mpr (hxp i)
      . simp
        linarith
  . have g₀: 1 ≤ n + 1 := by linarith
    rw [Finset.sum_Ico_succ_top g₀ _, Finset.sum_Ico_succ_top g₀ _]
    repeat rw [add_mul, mul_add]
    have h₄: 0 < (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
      x (n + 1) * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + 1 / x (n + 1)) := by
        refine add_pos ?_ ?_
        . refine mul_pos ?_ ?_
          . refine Finset.sum_pos ?_ ?_
            . exact fun i _ => hxp i
            . simp
              linarith
          . exact one_div_pos.mpr (hxp (n + 1))
        . refine mul_pos ?_ ?_
          . exact hxp (n + 1)
          . refine add_pos ?_ ?_
            . refine Finset.sum_pos ?_ ?_
              . intros i _
                exact one_div_pos.mpr (hxp i)
              . simp
                linarith
            . exact one_div_pos.mpr (hxp (n + 1))
    linarith


lemma imo_2023_p4_1_4
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) :
  a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k) := by
  refine h₀ (n + 1) ?_
  constructor
  . linarith
  . linarith


lemma imo_2023_p4_1_5
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022)
  (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k)
  * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k)) :
  a n < a (n + 1) := by
  rw [h₂,h₃]
  refine sqrt_lt_sqrt ?_ ?_
  . refine le_of_lt ?_
    refine mul_pos ?_ ?_
    . refine Finset.sum_pos ?_ ?_
      . exact fun i _ => hxp i
      . simp
        linarith
    . refine Finset.sum_pos ?_ ?_
      . intros i _
        exact one_div_pos.mpr (hxp i)
      . simp
        linarith
  . have g₀: 1 ≤ n + 1 := by linarith
    rw [Finset.sum_Ico_succ_top g₀ _, Finset.sum_Ico_succ_top g₀ _]
    repeat rw [add_mul, mul_add]
    have h₄: 0 < (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
      x (n + 1) * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + 1 / x (n + 1)) := by
        refine add_pos ?_ ?_
        . refine mul_pos ?_ ?_
          . refine Finset.sum_pos ?_ ?_
            . exact fun i _ => hxp i
            . simp
              linarith
          . exact one_div_pos.mpr (hxp (n + 1))
        . refine mul_pos ?_ ?_
          . exact hxp (n + 1)
          . refine add_pos ?_ ?_
            . refine Finset.sum_pos ?_ ?_
              . intros i _
                exact one_div_pos.mpr (hxp i)
              . simp
                linarith
            . exact one_div_pos.mpr (hxp (n + 1))
    linarith


lemma imo_2023_p4_1_6
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k)) :
  √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
    Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) <
    √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) *
    Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k) := by
  refine sqrt_lt_sqrt ?_ ?_
  . refine le_of_lt ?_
    refine mul_pos ?_ ?_
    . refine Finset.sum_pos ?_ ?_
      . exact fun i _ => hxp i
      . simp
        linarith
    . refine Finset.sum_pos ?_ ?_
      . intros i _
        exact one_div_pos.mpr (hxp i)
      . simp
        linarith
  . have g₀: 1 ≤ n + 1 := by linarith
    rw [Finset.sum_Ico_succ_top g₀ _, Finset.sum_Ico_succ_top g₀ _]
    repeat rw [add_mul, mul_add]
    have h₄: 0 < (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
      x (n + 1) * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + 1 / x (n + 1)) := by
        refine add_pos ?_ ?_
        . refine mul_pos ?_ ?_
          . refine Finset.sum_pos ?_ ?_
            . exact fun i _ => hxp i
            . simp
              linarith
          . exact one_div_pos.mpr (hxp (n + 1))
        . refine mul_pos ?_ ?_
          . exact hxp (n + 1)
          . refine add_pos ?_ ?_
            . refine Finset.sum_pos ?_ ?_
              . intros i _
                exact one_div_pos.mpr (hxp i)
              . simp
                linarith
            . exact one_div_pos.mpr (hxp (n + 1))
    linarith


lemma imo_2023_p4_1_7
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k)) :
  0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k := by
  refine le_of_lt ?_
  refine mul_pos ?_ ?_
  . refine Finset.sum_pos ?_ ?_
    . exact fun i _ => hxp i
    . simp
      linarith
  . refine Finset.sum_pos ?_ ?_
    . intros i _
      exact one_div_pos.mpr (hxp i)
    . simp
      linarith


lemma imo_2023_p4_1_8
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k)) :
  0 < (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k := by
  refine mul_pos ?_ ?_
  . refine Finset.sum_pos ?_ ?_
    . exact fun i _ => hxp i
    . simp
      linarith
  . refine Finset.sum_pos ?_ ?_
    . intros i _
      exact one_div_pos.mpr (hxp i)
    . simp
      linarith


lemma imo_2023_p4_1_9
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k)) :
  0 < Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k := by
  refine Finset.sum_pos ?_ ?_
  . exact fun i _ => hxp i
  . simp
    linarith


lemma imo_2023_p4_1_10
  -- (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k)) :
  (Finset.Ico 1 (n + 1)).Nonempty := by
  simp
  linarith


lemma imo_2023_p4_1_11
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k)) :
  0 < Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k := by
  refine Finset.sum_pos ?_ ?_
  . intros i _
    exact one_div_pos.mpr (hxp i)
  . simp
    linarith


lemma imo_2023_p4_1_12
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2022)
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k)) :
  ∀ i ∈ Finset.Ico 1 (n + 1), 0 < 1 / x i := by
  intros i _
  exact one_div_pos.mpr (hxp i)


lemma imo_2023_p4_1_13
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k)) :
  ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) <
    (Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k := by
  have g₀: 1 ≤ n + 1 := by linarith
  rw [Finset.sum_Ico_succ_top g₀ _, Finset.sum_Ico_succ_top g₀ _]
  repeat rw [add_mul, mul_add]
  have h₄: 0 < (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
    x (n + 1) * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + 1 / x (n + 1)) := by
      refine add_pos ?_ ?_
      . refine mul_pos ?_ ?_
        . refine Finset.sum_pos ?_ ?_
          . exact fun i _ => hxp i
          . simp
            linarith
        . exact one_div_pos.mpr (hxp (n + 1))
      . refine mul_pos ?_ ?_
        . exact hxp (n + 1)
        . refine add_pos ?_ ?_
          . refine Finset.sum_pos ?_ ?_
            . intros i _
              exact one_div_pos.mpr (hxp i)
            . simp
              linarith
          . exact one_div_pos.mpr (hxp (n + 1))
  linarith


lemma imo_2023_p4_1_14
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022)
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k))
  (g₀ : 1 ≤ n + 1) :
  ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) <
    (Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k)
    * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k := by
  rw [Finset.sum_Ico_succ_top g₀ _, Finset.sum_Ico_succ_top g₀ _]
  repeat rw [add_mul, mul_add]
  have h₄: 0 < (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
    x (n + 1) * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + 1 / x (n + 1)) := by
      refine add_pos ?_ ?_
      . refine mul_pos ?_ ?_
        . refine Finset.sum_pos ?_ ?_
          . exact fun i _ => hxp i
          . simp
            linarith
        . exact one_div_pos.mpr (hxp (n + 1))
      . refine mul_pos ?_ ?_
        . exact hxp (n + 1)
        . refine add_pos ?_ ?_
          . refine Finset.sum_pos ?_ ?_
            . intros i _
              exact one_div_pos.mpr (hxp i)
            . simp
              linarith
          . exact one_div_pos.mpr (hxp (n + 1))
  linarith


lemma imo_2023_p4_1_15
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k))
  -- (g₀ : 1 ≤ n + 1) :
  ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) <
    ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) + x (n + 1)) *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + 1 / x (n + 1)) := by
  repeat rw [add_mul, mul_add]
  have h₄: 0 < (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
    x (n + 1) * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + 1 / x (n + 1)) := by
      refine add_pos ?_ ?_
      . refine mul_pos ?_ ?_
        . refine Finset.sum_pos ?_ ?_
          . exact fun i _ => hxp i
          . simp
            linarith
        . exact one_div_pos.mpr (hxp (n + 1))
      . refine mul_pos ?_ ?_
        . exact hxp (n + 1)
        . refine add_pos ?_ ?_
          . refine Finset.sum_pos ?_ ?_
            . intros i _
              exact one_div_pos.mpr (hxp i)
            . simp
              linarith
          . exact one_div_pos.mpr (hxp (n + 1))
  linarith


lemma imo_2023_p4_1_16
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k))
  -- (g₀ : 1 ≤ n + 1) :
  ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) <
    ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
      x (n + 1) * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + 1 / x (n + 1)) := by
  have h₄: 0 < (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
    x (n + 1) * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + 1 / x (n + 1)) := by
      refine add_pos ?_ ?_
      . refine mul_pos ?_ ?_
        . refine Finset.sum_pos ?_ ?_
          . exact fun i _ => hxp i
          . simp
            linarith
        . exact one_div_pos.mpr (hxp (n + 1))
      . refine mul_pos ?_ ?_
        . exact hxp (n + 1)
        . refine add_pos ?_ ?_
          . refine Finset.sum_pos ?_ ?_
            . intros i _
              exact one_div_pos.mpr (hxp i)
            . simp
              linarith
          . exact one_div_pos.mpr (hxp (n + 1))
  linarith


lemma imo_2023_p4_1_17
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k))
  -- (g₀ : 1 ≤ n + 1) :
  0 <
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
      x (n + 1) * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + 1 / x (n + 1)) := by
  refine add_pos ?_ ?_
  . refine mul_pos ?_ ?_
    . refine Finset.sum_pos ?_ ?_
      . exact fun i _ => hxp i
      . simp
        linarith
    . exact one_div_pos.mpr (hxp (n + 1))
  . refine mul_pos ?_ ?_
    . exact hxp (n + 1)
    . refine add_pos ?_ ?_
      . refine Finset.sum_pos ?_ ?_
        . intros i _
          exact one_div_pos.mpr (hxp i)
        . simp
          linarith
      . exact one_div_pos.mpr (hxp (n + 1))


lemma imo_2023_p4_1_18
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k))
  -- (g₀ : 1 ≤ n + 1) :
  0 < (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) := by
  refine mul_pos ?_ ?_
  . refine Finset.sum_pos ?_ ?_
    . exact fun i _ => hxp i
    . simp
      linarith
  . exact one_div_pos.mpr (hxp (n + 1))


lemma imo_2023_p4_1_19
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k))
  -- (g₀ : 1 ≤ n + 1) :
  0 < Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k := by
  refine Finset.sum_pos ?_ ?_
  . intros i _
    exact one_div_pos.mpr (hxp i)
  . simp
    linarith


lemma imo_2023_p4_1_20
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2022)
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k))
  -- (g₀ : 1 ≤ n + 1) :
  ∀ i ∈ Finset.Ico 1 (n + 1), 0 < 1 / x i := by
  intros i _
  exact one_div_pos.mpr (hxp i)


lemma imo_2023_p4_1_21
  -- (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2022) :
  -- (h₂ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₃ : a (n + 1) = √((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k))
  -- (g₀ : 1 ≤ n + 1) :
  (Finset.Ico 1 (n + 1)).Nonempty := by
  simp
  linarith






lemma imo_2023_p4_2
--  my_amgm
  (b1 b2 b3 b4 :ℝ)
  (hb1: 0 ≤ b1)
  (hb2: 0 ≤ b2)
  (hb3: 0 ≤ b3)
  (hb4: 0 ≤ b4) :
  (4 * (b1 * b2 * b3 * b4) ^ (4:ℝ)⁻¹ ≤ b1 + b2 + b3 + b4) := by
  let w1 : ℝ := (4:ℝ)⁻¹
  let w2 : ℝ := w1
  let w3 : ℝ := w2
  let w4 : ℝ := w3
  rw [mul_comm]
  refine mul_le_of_le_div₀ ?_ (by norm_num) ?_
  . refine add_nonneg ?_ hb4
    refine add_nonneg ?_ hb3
    exact add_nonneg hb1 hb2
  . have h₀: (b1^w1 * b2^w2 * b3^w3 * b4^w4) ≤ w1 * b1 + w2 * b2 + w3 * b3 + w4 * b4 := by
      refine geom_mean_le_arith_mean4_weighted (by norm_num) ?_ ?_ ?_ hb1 hb2 hb3 hb4 ?_
      . norm_num
      . norm_num
      . norm_num
      . norm_num
    repeat rw [mul_rpow _]
    . ring_nf at *
      linarith
    repeat { assumption }
    . exact mul_nonneg hb1 hb2
    . exact hb4
    . refine mul_nonneg ?_ hb3
      exact mul_nonneg hb1 hb2


lemma imo_2023_p4_2_1
  (b1 b2 b3 b4 : ℝ)
  (w1 w2 w3 w4 : ℝ)
  (hb1 : 0 ≤ b1)
  (hb2 : 0 ≤ b2)
  (hb3 : 0 ≤ b3)
  (hb4 : 0 ≤ b4)
  (hw1 : w1 = (4:ℝ)⁻¹)
  (hw2 : w2 = w1)
  (hw3 : w3 = w1)
  (hw4 : w4 = w1) :
  (b1 * b2 * b3 * b4) ^ (4:ℝ)⁻¹ * (4:ℝ) ≤ b1 + b2 + b3 + b4 := by
  refine mul_le_of_le_div₀ ?_ (by norm_num) ?_
  . refine add_nonneg ?_ hb4
    refine add_nonneg ?_ hb3
    exact add_nonneg hb1 hb2
  . have h₀: (b1^w1 * b2^w2 * b3^w3 * b4^w4) ≤ w1 * b1 + w2 * b2 + w3 * b3 + w4 * b4 := by
      have g₀ : 0 < w1 := by
        rw [hw1]
        norm_num
      refine geom_mean_le_arith_mean4_weighted ?_ (by linarith) (by linarith) ?_ hb1 hb2 hb3 hb4 ?_
      . exact le_of_lt g₀
      . linarith
      . rw [hw4, hw3, hw2, hw1]
        norm_num
    repeat rw [mul_rpow _]
    . rw [hw4, hw3, hw2, hw1] at *
      refine le_trans h₀ ?_
      ring_nf at *
      linarith
    repeat { assumption }
    . exact mul_nonneg hb1 hb2
    . exact hb4
    . refine mul_nonneg ?_ hb3
      exact mul_nonneg hb1 hb2


lemma imo_2023_p4_2_2
  (b1 b2 b3 b4 : ℝ)
  (hb1 : 0 ≤ b1)
  (hb2 : 0 ≤ b2)
  (hb3 : 0 ≤ b3)
  (hb4 : 0 ≤ b4) :
  -- (hw1 : w1 = (4:ℝ)⁻¹)
  -- (hw2 : w2 = w1)
  -- (hw3 : w3 = w2)
  -- (hw4 : w4 = w3)
  0 ≤ b1 + b2 + b3 + b4 := by
  refine add_nonneg ?_ hb4
  refine add_nonneg ?_ hb3
  exact add_nonneg hb1 hb2


lemma imo_2023_p4_2_3
  (b1 b2 b3 b4 : ℝ)
  (w1 w2 w3 w4 : ℝ)
  (hb1 : 0 ≤ b1)
  (hb2 : 0 ≤ b2)
  (hb3 : 0 ≤ b3)
  (hb4 : 0 ≤ b4)
  (hw1 : w1 = (4:ℝ)⁻¹)
  (hw2 : w2 = w1)
  (hw3 : w3 = w2)
  (hw4 : w4 = w3) :
  (b1 * b2 * b3 * b4) ^ ((4:ℝ)⁻¹) ≤ (b1 + b2 + b3 + b4) / 4 := by
  have h₀: (b1^w1 * b2^w2 * b3^w3 * b4^w4) ≤ w1 * b1 + w2 * b2 + w3 * b3 + w4 * b4 := by
    have g₀ : 0 < w1 := by
      rw [hw1]
      norm_num
    refine geom_mean_le_arith_mean4_weighted ?_ (by linarith) (by linarith) ?_ hb1 hb2 hb3 hb4 ?_
    . exact le_of_lt g₀
    . linarith
    . rw [hw4, hw3, hw2, hw1]
      norm_num
  repeat rw [mul_rpow _]
  . rw [hw4, hw3, hw2, hw1] at *
    refine le_trans h₀ ?_
    ring_nf at *
    linarith
  repeat { assumption }
  . exact mul_nonneg hb1 hb2
  . exact hb4
  . refine mul_nonneg ?_ hb3
    exact mul_nonneg hb1 hb2


lemma imo_2023_p4_2_4
  (b1 b2 b3 b4 : ℝ)
  (w1 w2 w3 w4 : ℝ)
  (hb1 : 0 ≤ b1)
  (hb2 : 0 ≤ b2)
  (hb3 : 0 ≤ b3)
  (hb4 : 0 ≤ b4)
  (hw1 : w1 = (4:ℝ)⁻¹)
  (hw2 : w2 = w1)
  (hw3 : w3 = w2)
  (hw4 : w4 = w3) :
  b1 ^ w1 * b2 ^ w2 * b3 ^ w3 * b4 ^ w4 ≤ w1 * b1 + w2 * b2 + w3 * b3 + w4 * b4 := by
  have g₀ : 0 < w1 := by
    rw [hw1]
    norm_num
  refine geom_mean_le_arith_mean4_weighted ?_ (by linarith) (by linarith) ?_ hb1 hb2 hb3 hb4 ?_
  . exact le_of_lt g₀
  . linarith
  . rw [hw4, hw3, hw2, hw1]
    norm_num


lemma imo_2023_p4_2_5
  (b1 b2 b3 b4 : ℝ)
  (w1 w2 w3 w4 : ℝ)
  (hb1 : 0 ≤ b1)
  (hb2 : 0 ≤ b2)
  (hb3 : 0 ≤ b3)
  (hb4 : 0 ≤ b4)
  (hw1 : w1 = ((4:ℝ)⁻¹))
  (hw2 : w2 = w1)
  (hw3 : w3 = w2)
  (hw4 : w4 = w3)
  (h₀ : b1 ^ w1 * b2 ^ w2 * b3 ^ w3 * b4 ^ w4 ≤ w1 * b1 + w2 * b2 + w3 * b3 + w4 * b4) :
  (b1 * b2 * b3 * b4) ^ (4:ℝ)⁻¹ ≤ (b1 + b2 + b3 + b4) / 4 := by
  repeat rw [mul_rpow _]
  . rw [hw4, hw3, hw2, hw1] at *
    refine le_trans h₀ ?_
    ring_nf at *
    linarith
  repeat { assumption }
  . exact mul_nonneg hb1 hb2
  . exact hb4
  . refine mul_nonneg ?_ hb3
    exact mul_nonneg hb1 hb2


lemma imo_2023_p4_2_6
  (b1 b2 b3 b4 : ℝ)
  (w1 w2 w3 w4 : ℝ)
  -- (hb1 : 0 ≤ b1)
  -- (hb2 : 0 ≤ b2)
  -- (hb3 : 0 ≤ b3)
  -- (hb4 : 0 ≤ b4)
  (hw1 : w1 = ((4:ℝ)⁻¹))
  (hw2 : w2 = w1)
  (hw3 : w3 = w2)
  (hw4 : w4 = w3)
  (h₀ : b1 ^ w1 * b2 ^ w2 * b3 ^ w3 * b4 ^ w4 ≤ w1 * b1 + w2 * b2 + w3 * b3 + w4 * b4) :
  b1 ^ (4:ℝ)⁻¹ * b2 ^ (4:ℝ)⁻¹ * b3 ^ (4:ℝ)⁻¹ * b4 ^ (4:ℝ)⁻¹ ≤ (b1 + b2 + b3 + b4) / 4 := by
  rw [hw4, hw3, hw2, hw1] at *
  refine le_trans h₀ ?_
  ring_nf at *
  linarith








lemma imo_2023_p4_3
--  my_2
  (x a: ℕ → ℝ)
  (hxp: ∀ (i : ℕ), 0 < x i)
  (h₀: ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
            * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)))
  (n: ℕ)
  (hn: 1 ≤ n ∧ n ≤ 2021) :
  (4 * a n ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1) + 1 / x (n + 2)) +
      (x (n + 1) + x (n + 2)) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
  repeat rw [mul_add, add_mul]
  have g₁₁: 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1 := by
    refine le_of_lt ?_
    refine Finset.sum_pos ?_ ?_
    . exact fun i _ => hxp i
    . simp
      linarith
  have g₁₂: 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹ := by
    refine le_of_lt ?_
    refine Finset.sum_pos ?_ ?_
    . intros i _
      exact inv_pos.mpr (hxp i)
    . simp
      linarith
  have h₃₂: 4 * ( ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))) *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) *
      (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) ) ^ (4:ℝ)⁻¹
    ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
      (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
      x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
    let b1:ℝ := (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))
    let b2:ℝ := (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))
    let b3:ℝ := (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
    let b4:ℝ := x (n + 2) * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
    have hb1: b1 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) := by
      exact rfl
    have hb2: b2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) := by
      exact rfl
    have hb3: b3 = (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact rfl
    have hb4: b4 = x (n + 2) * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact rfl
    rw [← hb1, ← hb2, ← hb3, ← hb4]
    have g₀: 4 * (b1 * b2 * b3 * b4) ^ (4:ℝ)⁻¹ ≤ b1 + b2 + b3 + b4 := by
      have b1p: 0 ≤ b1 := by
        rw [hb1]
        refine mul_nonneg ?_ ?_
        . ring_nf
          exact g₁₁
        . refine le_of_lt ?_
          exact one_div_pos.mpr (hxp (n + 1))
      have b2p: 0 ≤ b2 := by
        rw [hb2]
        refine mul_nonneg ?_ ?_
        . ring_nf
          exact g₁₁
        . refine le_of_lt ?_
          exact one_div_pos.mpr (hxp (n + 2))
      have b3p: 0 ≤ b3 := by
        rw [hb3]
        refine mul_nonneg ?_ ?_
        . exact LT.lt.le (hxp (n + 1))
        . ring_nf
          exact g₁₂
      have b4p: 0 ≤ b4 := by
        rw [hb4]
        refine mul_nonneg ?_ ?_
        . exact LT.lt.le (hxp (n + 2))
        . ring_nf
          exact g₁₂
      exact imo_2023_p4_2 b1 b2 b3 b4 b1p b2p b3p b4p
    linarith
  have h₃₃: 4 * a (n) = 4 * (((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))) *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) *
      (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) ) ^ (4:ℝ)⁻¹ := by
    simp
    ring_nf
    have g₀: (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2
        * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2
      = x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 := by
        linarith
    have g₁: x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1 := by
      rw [mul_assoc]
      have gg₁: x (1 + n) * (x (1 + n))⁻¹ = 1 := by
        refine div_self ?_
        exact ne_of_gt (hxp (1 + n))
      have gg₂: x (2 + n) * (x (2 + n))⁻¹ = 1 := by
        refine div_self ?_
        exact ne_of_gt (hxp (2 + n))
      rw [gg₁, gg₂]
      norm_num
    rw [g₁] at g₀
    rw [g₀]
    simp
    repeat rw [mul_rpow]
    . have g₂: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
          = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₁ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
      have g₃: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
          = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₂ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
      -- rw [g₂, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)]
      -- rw [g₃, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)]
      have g₄: a (n) = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
                * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
        refine h₀ n ?_
        constructor
        . exact hn.1
        . linarith
      norm_cast at *
      rw [g₂, g₃, ← mul_rpow g₁₁ g₁₂]
      rw [← sqrt_eq_rpow]
      ring_nf at g₄
      exact g₄
    . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
    . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  exact Eq.trans_le h₃₃ h₃₂


lemma imo_2023_p4_3_1
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021) :
  4 * a n ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
  have g₁₁: 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1 := by
    refine le_of_lt ?_
    refine Finset.sum_pos ?_ ?_
    . exact fun i _ => hxp i
    . simp
      linarith
  have g₁₂: 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹ := by
    refine le_of_lt ?_
    refine Finset.sum_pos ?_ ?_
    . intros i _
      exact inv_pos.mpr (hxp i)
    . simp
      linarith
  have h₃₂: 4 * ( ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))) *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) *
      (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) ) ^ (4:ℝ)⁻¹
    ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
      (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
      x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
    let b1:ℝ := (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))
    let b2:ℝ := (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))
    let b3:ℝ := (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
    let b4:ℝ := x (n + 2) * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
    have hb1: b1 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) := by
      exact rfl
    have hb2: b2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) := by
      exact rfl
    have hb3: b3 = (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact rfl
    have hb4: b4 = x (n + 2) * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact rfl
    rw [← hb1, ← hb2, ← hb3, ← hb4]
    have g₀: 4 * (b1 * b2 * b3 * b4) ^ (4:ℝ)⁻¹ ≤ b1 + b2 + b3 + b4 := by
      have b1p: 0 ≤ b1 := by
        rw [hb1]
        refine mul_nonneg ?_ ?_
        . ring_nf
          exact g₁₁
        . refine le_of_lt ?_
          exact one_div_pos.mpr (hxp (n + 1))
      have b2p: 0 ≤ b2 := by
        rw [hb2]
        refine mul_nonneg ?_ ?_
        . ring_nf
          exact g₁₁
        . refine le_of_lt ?_
          exact one_div_pos.mpr (hxp (n + 2))
      have b3p: 0 ≤ b3 := by
        rw [hb3]
        refine mul_nonneg ?_ ?_
        . exact LT.lt.le (hxp (n + 1))
        . ring_nf
          exact g₁₂
      have b4p: 0 ≤ b4 := by
        rw [hb4]
        refine mul_nonneg ?_ ?_
        . exact LT.lt.le (hxp (n + 2))
        . ring_nf
          exact g₁₂
      exact imo_2023_p4_2 b1 b2 b3 b4 b1p b2p b3p b4p
    linarith
  have h₃₃: 4 * a (n) = 4 * (((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))) *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) *
      (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) ) ^ (4:ℝ)⁻¹ := by
    simp
    ring_nf
    have g₀: (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2
        * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2
      = x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 := by
        linarith
    have g₁: x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1 := by
      rw [mul_assoc]
      have gg₁: x (1 + n) * (x (1 + n))⁻¹ = 1 := by
        refine div_self ?_
        exact ne_of_gt (hxp (1 + n))
      have gg₂: x (2 + n) * (x (2 + n))⁻¹ = 1 := by
        refine div_self ?_
        exact ne_of_gt (hxp (2 + n))
      rw [gg₁, gg₂]
      norm_num
    rw [g₁] at g₀
    rw [g₀]
    simp
    repeat rw [mul_rpow]
    . have g₂: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
          = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₁ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
      have g₃: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
          = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₂ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
      -- rw [g₂, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)]
      -- rw [g₃, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)]
      have g₄: a (n) = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
                * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
        refine h₀ n ?_
        constructor
        . exact hn.1
        . linarith
      norm_cast at *
      rw [g₂, g₃, ← mul_rpow g₁₁ g₁₂]
      rw [← sqrt_eq_rpow]
      ring_nf at g₄
      exact g₄
    . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
    . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  exact Eq.trans_le h₃₃ h₃₂


lemma imo_2023_p4_3_2
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021) :
  0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1 := by
  refine le_of_lt ?_
  refine Finset.sum_pos ?_ ?_
  . exact fun i _ => hxp i
  . simp
    linarith


lemma imo_2023_p4_3_3
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) :
  4 * a n ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
  have g₁₂: 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹ := by
    refine le_of_lt ?_
    refine Finset.sum_pos ?_ ?_
    . intros i _
      exact inv_pos.mpr (hxp i)
    . simp
      linarith
  have h₃₂: 4 * ( ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))) *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) *
      (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) ) ^ (4:ℝ)⁻¹
    ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
      (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
      x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
    let b1:ℝ := (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))
    let b2:ℝ := (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))
    let b3:ℝ := (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
    let b4:ℝ := x (n + 2) * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
    have hb1: b1 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) := by
      exact rfl
    have hb2: b2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) := by
      exact rfl
    have hb3: b3 = (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact rfl
    have hb4: b4 = x (n + 2) * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact rfl
    rw [← hb1, ← hb2, ← hb3, ← hb4]
    have g₀: 4 * (b1 * b2 * b3 * b4) ^ (4:ℝ)⁻¹ ≤ b1 + b2 + b3 + b4 := by
      have b1p: 0 ≤ b1 := by
        rw [hb1]
        refine mul_nonneg ?_ ?_
        . ring_nf
          exact g₁₁
        . refine le_of_lt ?_
          exact one_div_pos.mpr (hxp (n + 1))
      have b2p: 0 ≤ b2 := by
        rw [hb2]
        refine mul_nonneg ?_ ?_
        . ring_nf
          exact g₁₁
        . refine le_of_lt ?_
          exact one_div_pos.mpr (hxp (n + 2))
      have b3p: 0 ≤ b3 := by
        rw [hb3]
        refine mul_nonneg ?_ ?_
        . exact LT.lt.le (hxp (n + 1))
        . ring_nf
          exact g₁₂
      have b4p: 0 ≤ b4 := by
        rw [hb4]
        refine mul_nonneg ?_ ?_
        . exact LT.lt.le (hxp (n + 2))
        . ring_nf
          exact g₁₂
      exact imo_2023_p4_2 b1 b2 b3 b4 b1p b2p b3p b4p
    linarith
  have h₃₃: 4 * a (n) = 4 * (((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))) *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) *
      (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) ) ^ (4:ℝ)⁻¹ := by
    simp
    ring_nf
    have g₀: (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2
        * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2
      = x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 := by
        linarith
    have g₁: x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1 := by
      rw [mul_assoc]
      have gg₁: x (1 + n) * (x (1 + n))⁻¹ = 1 := by
        refine div_self ?_
        exact ne_of_gt (hxp (1 + n))
      have gg₂: x (2 + n) * (x (2 + n))⁻¹ = 1 := by
        refine div_self ?_
        exact ne_of_gt (hxp (2 + n))
      rw [gg₁, gg₂]
      norm_num
    rw [g₁] at g₀
    rw [g₀]
    simp
    repeat rw [mul_rpow]
    . have g₂: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
          = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₁ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
      have g₃: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
          = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₂ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
      -- rw [g₂, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)]
      -- rw [g₃, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)]
      have g₄: a (n) = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
                * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
        refine h₀ n ?_
        constructor
        . exact hn.1
        . linarith
      norm_cast at *
      rw [g₂, g₃, ← mul_rpow g₁₁ g₁₂]
      rw [← sqrt_eq_rpow]
      ring_nf at g₄
      exact g₄
    . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
    . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  exact Eq.trans_le h₃₃ h₃₂


lemma imo_2023_p4_3_4
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021) :
  -- (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) :
  0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹ := by
  refine le_of_lt ?_
  refine Finset.sum_pos ?_ ?_
  . intros i _
    exact inv_pos.mpr (hxp i)
  . simp
    linarith


lemma imo_2023_p4_3_5
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) :
  ∀ i ∈ Finset.Ico 1 (1 + n), 0 < (x i)⁻¹ := by
  intros i _
  exact inv_pos.mpr (hxp i)


lemma imo_2023_p4_3_6
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) :
  4 * a n ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
  have h₃₂: 4 * ( ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))) *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) *
      (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) ) ^ (4:ℝ)⁻¹
    ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
      (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
      x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
    let b1:ℝ := (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))
    let b2:ℝ := (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))
    let b3:ℝ := (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
    let b4:ℝ := x (n + 2) * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
    have hb1: b1 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) := by
      exact rfl
    have hb2: b2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) := by
      exact rfl
    have hb3: b3 = (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact rfl
    have hb4: b4 = x (n + 2) * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact rfl
    rw [← hb1, ← hb2, ← hb3, ← hb4]
    have g₀: 4 * (b1 * b2 * b3 * b4) ^ (4:ℝ)⁻¹ ≤ b1 + b2 + b3 + b4 := by
      have b1p: 0 ≤ b1 := by
        rw [hb1]
        refine mul_nonneg ?_ ?_
        . ring_nf
          exact g₁₁
        . refine le_of_lt ?_
          exact one_div_pos.mpr (hxp (n + 1))
      have b2p: 0 ≤ b2 := by
        rw [hb2]
        refine mul_nonneg ?_ ?_
        . ring_nf
          exact g₁₁
        . refine le_of_lt ?_
          exact one_div_pos.mpr (hxp (n + 2))
      have b3p: 0 ≤ b3 := by
        rw [hb3]
        refine mul_nonneg ?_ ?_
        . exact LT.lt.le (hxp (n + 1))
        . ring_nf
          exact g₁₂
      have b4p: 0 ≤ b4 := by
        rw [hb4]
        refine mul_nonneg ?_ ?_
        . exact LT.lt.le (hxp (n + 2))
        . ring_nf
          exact g₁₂
      exact imo_2023_p4_2 b1 b2 b3 b4 b1p b2p b3p b4p
    linarith
  have h₃₃: 4 * a (n) = 4 * (((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))) *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) *
      (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) ) ^ (4:ℝ)⁻¹ := by
    simp
    ring_nf
    have g₀: (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2
        * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2
      = x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 := by
        linarith
    have g₁: x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1 := by
      rw [mul_assoc]
      have gg₁: x (1 + n) * (x (1 + n))⁻¹ = 1 := by
        refine div_self ?_
        exact ne_of_gt (hxp (1 + n))
      have gg₂: x (2 + n) * (x (2 + n))⁻¹ = 1 := by
        refine div_self ?_
        exact ne_of_gt (hxp (2 + n))
      rw [gg₁, gg₂]
      norm_num
    rw [g₁] at g₀
    rw [g₀]
    simp
    repeat rw [mul_rpow]
    . have g₂: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
          = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₁ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
      have g₃: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
          = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₂ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
      -- rw [g₂, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)]
      -- rw [g₃, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)]
      have g₄: a (n) = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
                * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
        refine h₀ n ?_
        constructor
        . exact hn.1
        . linarith
      norm_cast at *
      rw [g₂, g₃, ← mul_rpow g₁₁ g₁₂]
      rw [← sqrt_eq_rpow]
      ring_nf at g₄
      exact g₄
    . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
    . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  exact Eq.trans_le h₃₃ h₃₂


lemma imo_2023_p4_3_7
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) :
  4 * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
        (4:ℝ)⁻¹ ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
  let b1:ℝ := (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))
  let b2:ℝ := (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))
  let b3:ℝ := (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  let b4:ℝ := x (n + 2) * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  have hb1: b1 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) := by
    exact rfl
  have hb2: b2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) := by
    exact rfl
  have hb3: b3 = (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
    exact rfl
  have hb4: b4 = x (n + 2) * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
    exact rfl
  rw [← hb1, ← hb2, ← hb3, ← hb4]
  have g₀: 4 * (b1 * b2 * b3 * b4) ^ (4:ℝ)⁻¹ ≤ b1 + b2 + b3 + b4 := by
    have b1p: 0 ≤ b1 := by
      rw [hb1]
      refine mul_nonneg ?_ ?_
      . ring_nf
        exact g₁₁
      . refine le_of_lt ?_
        exact one_div_pos.mpr (hxp (n + 1))
    have b2p: 0 ≤ b2 := by
      rw [hb2]
      refine mul_nonneg ?_ ?_
      . ring_nf
        exact g₁₁
      . refine le_of_lt ?_
        exact one_div_pos.mpr (hxp (n + 2))
    have b3p: 0 ≤ b3 := by
      rw [hb3]
      refine mul_nonneg ?_ ?_
      . exact LT.lt.le (hxp (n + 1))
      . ring_nf
        exact g₁₂
    have b4p: 0 ≤ b4 := by
      rw [hb4]
      refine mul_nonneg ?_ ?_
      . exact LT.lt.le (hxp (n + 2))
      . ring_nf
        exact g₁₂
    exact imo_2023_p4_2 b1 b2 b3 b4 b1p b2p b3p b4p
  linarith


lemma imo_2023_p4_3_8
  (x : ℕ → ℝ)
  (b1 b2 b3 b4 : ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  (hb1 : b1 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)))
  (hb2 : b2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)))
  (hb3 : b3 = x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (hb4 : b4 = x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) :
  4 * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
        (4:ℝ)⁻¹ ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
  rw [← hb1, ← hb2, ← hb3, ← hb4]
  have g₀: 4 * (b1 * b2 * b3 * b4) ^ (4:ℝ)⁻¹ ≤ b1 + b2 + b3 + b4 := by
    have b1p: 0 ≤ b1 := by
      rw [hb1]
      refine mul_nonneg ?_ ?_
      . ring_nf
        exact g₁₁
      . refine le_of_lt ?_
        exact one_div_pos.mpr (hxp (n + 1))
    have b2p: 0 ≤ b2 := by
      rw [hb2]
      refine mul_nonneg ?_ ?_
      . ring_nf
        exact g₁₁
      . refine le_of_lt ?_
        exact one_div_pos.mpr (hxp (n + 2))
    have b3p: 0 ≤ b3 := by
      rw [hb3]
      refine mul_nonneg ?_ ?_
      . exact LT.lt.le (hxp (n + 1))
      . ring_nf
        exact g₁₂
    have b4p: 0 ≤ b4 := by
      rw [hb4]
      refine mul_nonneg ?_ ?_
      . exact LT.lt.le (hxp (n + 2))
      . ring_nf
        exact g₁₂
    exact imo_2023_p4_2 b1 b2 b3 b4 b1p b2p b3p b4p
  linarith


lemma imo_2023_p4_3_9
  (x : ℕ → ℝ)
  (b1 b2 b3 b4 : ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  (hb1 : b1 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)))
  (hb2 : b2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)))
  (hb3 : b3 = x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (hb4 : b4 = x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) :
  4 * (b1 * b2 * b3 * b4) ^ (4:ℝ)⁻¹ ≤ b1 + b2 + (b3 + b4) := by
  have b1p: 0 ≤ b1 := by
    rw [hb1]
    refine mul_nonneg ?_ ?_
    . ring_nf
      exact g₁₁
    . refine le_of_lt ?_
      exact one_div_pos.mpr (hxp (n + 1))
  have b2p: 0 ≤ b2 := by
    rw [hb2]
    refine mul_nonneg ?_ ?_
    . ring_nf
      exact g₁₁
    . refine le_of_lt ?_
      exact one_div_pos.mpr (hxp (n + 2))
  have b3p: 0 ≤ b3 := by
    rw [hb3]
    refine mul_nonneg ?_ ?_
    . exact LT.lt.le (hxp (n + 1))
    . ring_nf
      exact g₁₂
  have b4p: 0 ≤ b4 := by
    rw [hb4]
    refine mul_nonneg ?_ ?_
    . exact LT.lt.le (hxp (n + 2))
    . ring_nf
      exact g₁₂
  rw [← add_assoc]
  exact imo_2023_p4_2 b1 b2 b3 b4 b1p b2p b3p b4p


lemma imo_2023_p4_3_10
  (x : ℕ → ℝ)
  (b1 : ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  -- (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  (hb1 : b1 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))) :
  -- (hb2 : b2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)))
  -- (hb3 : b3 = x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (hb4 : b4 = x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) :
  0 ≤ b1 := by
  rw [hb1]
  refine mul_nonneg ?_ ?_
  . ring_nf
    exact g₁₁
  . refine le_of_lt ?_
    exact one_div_pos.mpr (hxp (n + 1))


lemma imo_2023_p4_3_11
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  -- (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  -- (hb1 : b1 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)))
  -- (hb2 : b2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)))
  -- (hb3 : b3 = x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (hb4 : b4 = x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  0 ≤ 1 / x (n + 1) := by
  refine le_of_lt ?_
  exact one_div_pos.mpr (hxp (n + 1))


lemma imo_2023_p4_3_12
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  (h₃₂ : 4 *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
        (4:ℝ)⁻¹ ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) :
  4 * a n ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
  have h₃₃: 4 * a (n) = 4 * (((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1))) *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) *
      (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) ) ^ (4:ℝ)⁻¹ := by
    simp
    ring_nf
    have g₀: (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2
        * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2
      = x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 := by
        linarith
    have g₁: x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1 := by
      rw [mul_assoc]
      have gg₁: x (1 + n) * (x (1 + n))⁻¹ = 1 := by
        refine div_self ?_
        exact ne_of_gt (hxp (1 + n))
      have gg₂: x (2 + n) * (x (2 + n))⁻¹ = 1 := by
        refine div_self ?_
        exact ne_of_gt (hxp (2 + n))
      rw [gg₁, gg₂]
      norm_num
    rw [g₁] at g₀
    rw [g₀]
    simp
    repeat rw [mul_rpow]
    . have g₂: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
          = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₁ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
      have g₃: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
          = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₂ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
      -- rw [g₂, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)]
      -- rw [g₃, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)]
      have g₄: a (n) = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
                * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
        refine h₀ n ?_
        constructor
        . exact hn.1
        . linarith
      norm_cast at *
      rw [g₂, g₃, ← mul_rpow g₁₁ g₁₂]
      rw [← sqrt_eq_rpow]
      ring_nf at g₄
      exact g₄
    . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
    . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  exact Eq.trans_le h₃₃ h₃₂


lemma imo_2023_p4_3_13
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  (h₃₂ : 4 *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
        (4:ℝ)⁻¹ ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) :
  4 * a n =
    4 * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^ (4:ℝ)⁻¹ := by
  simp
  ring_nf
  have g₀: (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2
      * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2
    = x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 := by
      linarith
  have g₁: x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1 := by
    rw [mul_assoc]
    have gg₁: x (1 + n) * (x (1 + n))⁻¹ = 1 := by
      refine div_self ?_
      exact ne_of_gt (hxp (1 + n))
    have gg₂: x (2 + n) * (x (2 + n))⁻¹ = 1 := by
      refine div_self ?_
      exact ne_of_gt (hxp (2 + n))
    rw [gg₁, gg₂]
    norm_num
  rw [g₁] at g₀
  rw [g₀]
  simp
  repeat rw [mul_rpow]
  . have g₂: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
        = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1/(2:ℝ)) := by
      rw [← rpow_mul g₁₁ (2:ℝ) (4:ℝ)⁻¹]
      norm_num
    have g₃: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
        = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1/(2:ℝ)) := by
      rw [← rpow_mul g₁₂ (2:ℝ) (4:ℝ)⁻¹]
      norm_num
    -- rw [g₂, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)]
    -- rw [g₃, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)]
    have g₄: a (n) = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
              * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      refine h₀ n ?_
      constructor
      . exact hn.1
      . linarith
    norm_cast at *
    rw [g₂, g₃, ← mul_rpow g₁₁ g₁₂]
    rw [← sqrt_eq_rpow]
    ring_nf at g₄
    exact g₄
  . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)


lemma imo_2023_p4_3_14
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  (h₃₂ : 4 *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
        (4:ℝ)⁻¹ ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) :
  a n =
    ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) ^ (1 / (4:ℝ)) := by
  have g₀: (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2
      * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2
    = x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 := by
      linarith
  have g₁: x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1 := by
    rw [mul_assoc]
    have gg₁: x (1 + n) * (x (1 + n))⁻¹ = 1 := by
      refine div_self ?_
      exact ne_of_gt (hxp (1 + n))
    have gg₂: x (2 + n) * (x (2 + n))⁻¹ = 1 := by
      refine div_self ?_
      exact ne_of_gt (hxp (2 + n))
    rw [gg₁, gg₂]
    norm_num
  rw [g₁] at g₀
  rw [g₀]
  simp
  repeat rw [mul_rpow]
  have g₂: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
      = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₁ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
  have g₃: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
      = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₂ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
  have g₄: a (n) = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
            * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
    refine h₀ n ?_
    constructor
    . exact hn.1
    . linarith
  norm_cast at *
  rw [g₂, g₃]
  rw [← mul_rpow]
  rw [← sqrt_eq_rpow]
  ring_nf at g₄
  exact g₄
  . exact g₁₁
  . exact g₁₂
  . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)


lemma imo_2023_p4_3_15
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  (h₃₂ : 4 *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
        (4:ℝ)⁻¹ ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
    x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) :
  a n =
    ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) ^ (1 / (4:ℝ)) := by
  have g₁: x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1 := by
    rw [mul_assoc]
    have gg₁: x (1 + n) * (x (1 + n))⁻¹ = 1 := by
      refine div_self ?_
      exact ne_of_gt (hxp (1 + n))
    have gg₂: x (2 + n) * (x (2 + n))⁻¹ = 1 := by
      refine div_self ?_
      exact ne_of_gt (hxp (2 + n))
    rw [gg₁, gg₂]
    norm_num
  rw [g₁] at g₀
  rw [g₀]
  simp
  repeat rw [mul_rpow]
  have g₂: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
      = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₁ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
  have g₃: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
      = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₂ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
  have g₄: a (n) = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
            * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
    refine h₀ n ?_
    constructor
    . exact hn.1
    . linarith
  norm_cast at *
  rw [g₂, g₃]
  rw [← mul_rpow]
  rw [← sqrt_eq_rpow]
  ring_nf at g₄
  exact g₄
  . exact g₁₁
  . exact g₁₂
  . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)


lemma imo_2023_p4_3_16
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  -- (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  -- (h₃₂ : 4 *
  --     ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
  --             ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
  --           (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
  --         (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
  --       (4:ℝ)⁻¹ ≤
  --   (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
  --       (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
  --     ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
  --       x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
  --   x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) :
  x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1 := by
  rw [mul_assoc]
  have gg₁: x (1 + n) * (x (1 + n))⁻¹ = 1 := by
    refine div_self ?_
    exact ne_of_gt (hxp (1 + n))
  have gg₂: x (2 + n) * (x (2 + n))⁻¹ = 1 := by
    refine div_self ?_
    exact ne_of_gt (hxp (2 + n))
  rw [gg₁, gg₂]
  norm_num


lemma imo_2023_p4_3_17
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  -- (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  -- (h₃₂ : 4 *
  --     ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
  --             ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
  --           (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
  --         (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
  --       (4:ℝ)⁻¹ ≤
  --   (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
  --       (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
  --     ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
  --       x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
  --   x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) :
  x (1 + n) * (x (1 + n))⁻¹ = 1 := by
  refine div_self ?_
  exact ne_of_gt (hxp (1 + n))


lemma imo_2023_p4_3_18
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  -- (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  -- (h₃₂ : 4 *
  --     ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
  --             ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
  --           (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
  --         (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
  --       (4:ℝ)⁻¹ ≤
  --   (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
  --       (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
  --     ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
  --       x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
  --   x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2)
  (gg₁ : x (1 + n) * (x (1 + n))⁻¹ = 1)
  (gg₂ : x (2 + n) * (x (2 + n))⁻¹ = 1) :
  x (1 + n) * (x (1 + n))⁻¹ * (x (2 + n) * (x (2 + n))⁻¹) = 1 := by
  rw [gg₁, gg₂]
  norm_num


lemma imo_2023_p4_3_19
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  (h₃₂ : 4 *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
        (4:ℝ)⁻¹ ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2
                * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
                (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2
              = x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
                (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
                (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2)
  (g₁ : x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1) :
  a n =
    ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) ^ (1 / (4:ℝ)) := by
  rw [g₁] at g₀
  rw [g₀]
  simp
  repeat rw [mul_rpow]
  have g₂: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
      = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₁ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
  have g₃: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
      = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₂ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
  -- rw [g₂, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)]
  -- rw [g₃, ← sqrt_eq_rpow (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)]
  have g₄: a (n) = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
            * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
        refine h₀ n ?_
        constructor
        . exact hn.1
        . linarith
  norm_cast at *
  rw [g₂, g₃, ← mul_rpow]
  rw [← sqrt_eq_rpow]
  ring_nf at g₄
  exact g₄
  . exact g₁₁
  . exact g₁₂
  . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)


lemma imo_2023_p4_3_20
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  (h₃₂ : 4 *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
        (4:ℝ)⁻¹ ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * (x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹) *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
    1 * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2)
  (g₁ : x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1) :
  a n =
    ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
        (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) ^ (4:ℝ)⁻¹ := by
  repeat rw [mul_rpow]
  have g₂: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
      = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₁ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
  have g₃: ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
      = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1/(2:ℝ)) := by
        rw [← rpow_mul g₁₂ (2:ℝ) (4:ℝ)⁻¹]
        norm_num
  have g₄: a (n) = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
            * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
        refine h₀ n ?_
        constructor
        . exact hn.1
        . linarith
  norm_cast at *
  rw [g₂, g₃, ← mul_rpow]
  rw [← sqrt_eq_rpow]
  ring_nf at g₄
  exact g₄
  . exact g₁₁
  . exact g₁₂
  . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  . exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)


lemma imo_2023_p4_3_21
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  (h₃₂ : 4 *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
        (4:ℝ)⁻¹ ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
    1 * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2)
  (g₁ : x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1)
  (g₂ : ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
      = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1/(2:ℝ)))
  (g₃ : ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (2:ℝ)) ^ (4:ℝ)⁻¹
      = (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1/(2:ℝ))) :
  a n =
    ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2) ^ (4:ℝ)⁻¹ *
      ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) ^ (4:ℝ)⁻¹ := by
  have g₄: a (n) = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
            * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
    refine h₀ n ?_
    constructor
    . exact hn.1
    . linarith
  norm_cast at *
  rw [g₂, g₃]
  rw [← mul_rpow]
  rw [← sqrt_eq_rpow]
  ring_nf at g₄
  exact g₄
  . exact g₁₁
  . exact g₁₂


lemma imo_2023_p4_3_22
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021) :
  -- (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  -- (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  -- (h₃₂ : 4 *
  --     ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
  --             ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
  --           (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
  --         (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
  --       (4:ℝ)⁻¹ ≤
  --   (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
  --       (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
  --     ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
  --       x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
  --   1 * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2)
  -- (g₁ : x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1)
  -- (g₂ : ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2) ^ (4:ℝ)⁻¹ =
  --   (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1 / 2))
  -- (g₃ : ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) ^ (4:ℝ)⁻¹ =
  --   (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1 / 2)) :
  a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
    Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
  have g₄: a (n) = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
            * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
    refine h₀ n ?_
    constructor
    . exact hn.1
    . linarith
  norm_cast


lemma imo_2023_p4_3_23
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  (h₃₂ : 4 *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
        (4:ℝ)⁻¹ ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
    1 * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
      (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2)
  (g₁ : x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1)
  (g₂ : ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2) ^ (4:ℝ)⁻¹ =
    (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1 / (2:ℝ)))
  (g₃ : ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) ^ (4:ℝ)⁻¹ =
    (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1 / (2:ℝ)))
  (g₄ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
    Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) :
  a n =
    ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2) ^ (4:ℝ)⁻¹ *
      ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) ^ (4:ℝ)⁻¹ := by
  norm_cast at *
  rw [g₂, g₃, ← mul_rpow]
  . rw [← sqrt_eq_rpow]
    ring_nf at g₄
    exact g₄
  . exact g₁₁
  . exact g₁₂


lemma imo_2023_p4_3_24
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1))
  (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  -- (h₃₂ : 4 *
  --     ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
  --             ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
  --           (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1) *
  --         (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1)) ^
  --       (4:ℝ)⁻¹ ≤
  --   (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
  --       (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
  --     ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1) +
  --       x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1))
  -- (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
  --   1 * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2)
  -- (g₁ : x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1)
  (g₂ : ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2) ^ (4:ℝ)⁻¹ =
    (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1 / (2:ℝ)))
  (g₃ : ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) ^ (4:ℝ)⁻¹ =
    (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1 / (2:ℝ)))
  (g₄ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1)) :
  a n =
    ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2) ^ (4:ℝ)⁻¹ *
      ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) ^ (4:ℝ)⁻¹ := by
  rw [g₂, g₃, ← mul_rpow]
  . rw [← sqrt_eq_rpow]
    ring_nf at g₄
    exact g₄
  . exact g₁₁
  . exact g₁₂


lemma imo_2023_p4_3_25
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1) )
  -- (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  -- (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  -- (h₃₂ : 4 *
  --     ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
  --             ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
  --           (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1) *
  --         (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1)) ^
  --       (4:ℝ)⁻¹ ≤
  --   (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
  --       (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
  --     ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1) +
  --       x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1))
  -- (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
  --   1 * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2)
  -- (g₁ : x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1)
  -- (g₂ : ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2) ^ (4:ℝ)⁻¹ =
  --   (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1 / 2))
  -- (g₃ : ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) ^ (4:ℝ)⁻¹ =
  --   (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1 / 2))
  (g₄ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1)) :
  a n =
    ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) * Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^
      (1 / (2:ℝ)) := by
  rw [← sqrt_eq_rpow]
  ring_nf at g₄
  exact g₄


lemma imo_2023_p4_3_26
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1))
  -- (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  -- (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  -- (h₃₂ : 4 *
  --     ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
  --             ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
  --           (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1) *
  --         (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1)) ^
  --       (4:ℝ)⁻¹ ≤
  --   (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
  --       (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
  --     ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1) +
  --       x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1))
  -- (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
  --   1 * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2)
  -- (g₁ : x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1)
  -- (g₂ : ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2) ^ (4:ℝ)⁻¹ =
  --   (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ (1 / 2))
  -- (g₃ : ((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2) ^ (4:ℝ)⁻¹ =
  --   (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ (1 / 2))
  (g₄ : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
    Finset.sum (Finset.Ico 1 (n + 1)) fun x_1 => 1 / x x_1)) :
  a n = √((Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) *
      Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) := by
  ring_nf at g₄
  exact g₄


lemma imo_2023_p4_3_27
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  -- (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  -- (h₃₂ : 4 *
  --     ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
  --             ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
  --           (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
  --         (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
  --       (4:ℝ)⁻¹ ≤
  --   (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
  --       (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
  --     ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
  --       x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
  --   1 * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2)
  -- (g₁ : x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1) :
  0 ≤ (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 := by
  exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)


lemma imo_2023_p4_3_28
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  -- (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  -- (h₃₂ : 4 *
  --     ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
  --             ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
  --           (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
  --         (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
  --       (4:ℝ)⁻¹ ≤
  --   (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
  --       (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
  --     ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
  --       x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (g₀ : (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 * x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 =
  --   1 * (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1) ^ 2 *
  --     (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2)
  -- (g₁ : x (1 + n) * (x (1 + n))⁻¹ * x (2 + n) * (x (2 + n))⁻¹ = 1) :
  0 ≤ (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹) ^ 2 := by
  exact sq_nonneg (Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)


lemma imo_2023_p4_3_29
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₁₁ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => x x_1)
  -- (g₁₂ : 0 ≤ Finset.sum (Finset.Ico 1 (1 + n)) fun x_1 => (x x_1)⁻¹)
  (h₃₂ : 4 *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
        (4:ℝ)⁻¹ ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₃₃ : 4 * a n =
    4 *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) *
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2))) *
            (x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) *
          (x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) ^
        (4:ℝ)⁻¹) :
  4 * a n ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1)) +
        (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 2)) +
      ((x (n + 1) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        x (n + 2) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
  exact Eq.trans_le h₃₃ h₃₂








lemma imo_2023_p4_4
--  my_3
  (x a: ℕ → ℝ)
  (hxp: ∀ (i : ℕ), 0 < x i)
  (hx: ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀: ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
            * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)))
  (h₀₁: ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n) :
  (∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2)) := by
    intros n hn
    have g₀: 0 ≤ a n + 2 := by
      refine le_of_lt ?_
      refine add_pos ?_ (by norm_num)
      refine h₀₁ n ?_
      constructor
      . exact hn.1
      . linarith
    have g₁: 0 ≤ a (n + 2) := by
      refine le_of_lt ?_
      refine h₀₁ (n + 2) ?_
      constructor
      . linarith
      . linarith
    rw [← sqrt_sq g₀, ← sqrt_sq g₁]
    have g₂: 0 ≤ (a n + 2) ^ 2 := by exact sq_nonneg (a n + 2)
    simp
    refine Real.sqrt_lt_sqrt g₂ ?_
    have g₃: 0 ≤ ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
        * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) := by
          refine le_of_lt ?_
          refine mul_pos ?_ ?_
          . refine Finset.sum_pos ?_ ?_
            . exact fun i _ => hxp i
            . simp
              linarith
          . refine Finset.sum_pos ?_ ?_
            . intros i _
              exact one_div_pos.mpr (hxp i)
            . simp
              linarith
    have gn₀: a (n) ^ 2 = ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
        * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) := by
          rw [← sq_sqrt g₃]
          have g₄: 0 ≤ a n := by
            refine le_of_lt ?_
            refine h₀₁ n ?_
            constructor
            . exact hn.1
            . linarith
          refine (sq_eq_sq₀ g₄ ?_).mpr ?_
          . exact
            sqrt_nonneg
              ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
                Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
          refine h₀ (n) ?_
          constructor
          . exact hn.1
          . linarith
    have gn₁: a (n + 2) = sqrt ((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k)
        * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k) := by
          refine h₀ (n + 2) ?_
          constructor
          . linarith
          . linarith
    rw [add_sq, gn₁, sq_sqrt]
    . have ga₀: 1 ≤ n + 2 := by linarith
      rw [Finset.sum_Ico_succ_top ga₀ _, Finset.sum_Ico_succ_top ga₀ _]
      have ga₁: 1 ≤ n + 1 := by linarith
      rw [Finset.sum_Ico_succ_top ga₁ _, Finset.sum_Ico_succ_top ga₁ _]
      rw [add_assoc, add_assoc, add_assoc]
      rw [add_mul, mul_add]
      rw [← gn₀]
      repeat rw [add_assoc]
      refine add_lt_add_left ?_ (a (n) ^ 2)
      rw [mul_add (x (n + 1) + x (n + 2))]
      have h₂: 4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)) := by
        repeat rw [add_mul, mul_add, mul_add]
        repeat rw [mul_div_left_comm _ 1 _, one_mul]
        repeat rw [div_self ?_]
        . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
            = x (n + 1) * x (n + 1) := by
            rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
            simp
            exact ne_of_gt (hxp (n + 2))
          have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
            = x (n + 2) * x (n + 2) := by
            rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
            simp
            exact ne_of_gt (hxp (n + 1))
          have h₂₀: 0 < x (n + 1) * x (n + 2) := by
            refine mul_pos ?_ ?_
            . exact hxp (n + 1)
            . exact hxp (n + 2)
          have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
            refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
            rw [mul_add, hc₂, hc₃, ← sq, ← sq]
            refine lt_of_sub_pos ?_
            have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                      = (x (n + 1) - x (n + 2)) ^ 2 := by
                  rw [sub_sq]
                  linarith
            rw [gh₂₁]
            refine (sq_pos_iff).mpr ?_
            refine sub_ne_zero.mpr ?_
            exact hx (n+1) (n+2) (by linarith)
          linarith
        . exact ne_of_gt (hxp (n + 2))
        . exact ne_of_gt (hxp (n + 1))
      clear gn₀ gn₁ g₀ g₁ g₂ g₃ ga₀ ga₁
      have h₃: 4 * a (n) ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
          * (1 / x (n + 1) + 1 / x (n + 2)) +
          ((x (n + 1) + x (n + 2))
          * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
          exact imo_2023_p4_3 (fun k => x k) a hxp h₀ n hn
      linarith
    . refine mul_nonneg ?_ ?_
      . refine Finset.sum_nonneg ?_
        intros i _
        exact LT.lt.le (hxp i)
      . refine Finset.sum_nonneg ?_
        intros i _
        simp
        exact LT.lt.le (hxp i)


lemma imo_2023_p4_4_1
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021) :
  0 ≤ a n + 2 := by
  refine le_of_lt ?_
  refine add_pos ?_ (by norm_num)
  refine h₀₁ n ?_
  constructor
  . exact hn.1
  . linarith


lemma imo_2023_p4_4_2
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021) :
  0 < a n := by
  refine h₀₁ n ?_
  constructor
  . exact hn.1
  . linarith


lemma imo_2023_p4_4_3
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021) :
  -- (g₀ : 0 ≤ a n + 2) :
  0 ≤ a (n + 2) := by
  refine le_of_lt ?_
  refine h₀₁ (n + 2) ?_
  constructor
  . linarith
  . linarith


lemma imo_2023_p4_4_4
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : 0 ≤ a n + 2)
  (g₁ : 0 ≤ a (n + 2)) :
  a n + 2 < a (n + 2) := by
  rw [← sqrt_sq g₀, ← sqrt_sq g₁]
  have g₂: 0 ≤ (a n + 2) ^ 2 := by exact sq_nonneg (a n + 2)
  simp
  refine Real.sqrt_lt_sqrt g₂ ?_
  have g₃: 0 ≤ ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) := by
        refine le_of_lt ?_
        refine mul_pos ?_ ?_
        . refine Finset.sum_pos ?_ ?_
          . exact fun i _ => hxp i
          . simp
            linarith
        . refine Finset.sum_pos ?_ ?_
          . intros i _
            exact one_div_pos.mpr (hxp i)
          . simp
            linarith
  have gn₀: a (n) ^ 2 = ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) := by
        rw [← sq_sqrt g₃]
        have g₄: 0 ≤ a n := by
          refine le_of_lt ?_
          refine h₀₁ n ?_
          constructor
          . exact hn.1
          . linarith
        refine (sq_eq_sq₀ g₄ ?_).mpr ?_
        . exact
          sqrt_nonneg
            ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
              Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
        refine h₀ (n) ?_
        constructor
        . exact hn.1
        . linarith
  have gn₁: a (n + 2) = sqrt ((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k)
      * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k) := by
        refine h₀ (n + 2) ?_
        constructor
        . linarith
        . linarith
  rw [add_sq, gn₁, sq_sqrt]
  . have ga₀: 1 ≤ n + 2 := by linarith
    rw [Finset.sum_Ico_succ_top ga₀ _, Finset.sum_Ico_succ_top ga₀ _]
    have ga₁: 1 ≤ n + 1 := by linarith
    rw [Finset.sum_Ico_succ_top ga₁ _, Finset.sum_Ico_succ_top ga₁ _]
    rw [add_assoc, add_assoc, add_assoc]
    rw [add_mul, mul_add]
    rw [← gn₀]
    repeat rw [add_assoc]
    refine add_lt_add_left ?_ (a (n) ^ 2)
    rw [mul_add (x (n + 1) + x (n + 2))]
    have h₂: 4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)) := by
      repeat rw [add_mul, mul_add, mul_add]
      repeat rw [mul_div_left_comm _ 1 _, one_mul]
      repeat rw [div_self ?_]
      . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
          = x (n + 1) * x (n + 1) := by
          rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
          simp
          exact ne_of_gt (hxp (n + 2))
        have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
          = x (n + 2) * x (n + 2) := by
          rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
          simp
          exact ne_of_gt (hxp (n + 1))
        have h₂₀: 0 < x (n + 1) * x (n + 2) := by
          refine mul_pos ?_ ?_
          . exact hxp (n + 1)
          . exact hxp (n + 2)
        have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
          refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
          rw [mul_add, hc₂, hc₃, ← sq, ← sq]
          refine lt_of_sub_pos ?_
          have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                    = (x (n + 1) - x (n + 2)) ^ 2 := by
                rw [sub_sq]
                linarith
          rw [gh₂₁]
          refine (sq_pos_iff).mpr ?_
          refine sub_ne_zero.mpr ?_
          exact hx (n+1) (n+2) (by linarith)
        linarith
      . exact ne_of_gt (hxp (n + 2))
      . exact ne_of_gt (hxp (n + 1))
    clear gn₀ gn₁ g₀ g₁ g₂ g₃ ga₀ ga₁
    have h₃: 4 * a (n) ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
        * (1 / x (n + 1) + 1 / x (n + 2)) +
        ((x (n + 1) + x (n + 2))
        * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
        exact imo_2023_p4_3 (fun k => x k) a hxp h₀ n hn
    linarith
  . refine mul_nonneg ?_ ?_
    . refine Finset.sum_nonneg ?_
      intros i _
      exact LT.lt.le (hxp i)
    . refine Finset.sum_nonneg ?_
      intros i _
      simp
      exact LT.lt.le (hxp i)


lemma imo_2023_p4_4_5
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : 0 ≤ a n + 2)
  (g₁ : 0 ≤ a (n + 2)) :
  √((a n + 2) ^ 2) < √(a (n + 2) ^ 2) := by
  have g₂: 0 ≤ (a n + 2) ^ 2 := by exact sq_nonneg (a n + 2)
  simp
  refine Real.sqrt_lt_sqrt g₂ ?_
  have g₃: 0 ≤ ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) := by
        refine le_of_lt ?_
        refine mul_pos ?_ ?_
        . refine Finset.sum_pos ?_ ?_
          . exact fun i _ => hxp i
          . simp
            linarith
        . refine Finset.sum_pos ?_ ?_
          . intros i _
            exact one_div_pos.mpr (hxp i)
          . simp
            linarith
  have gn₀: a (n) ^ 2 = ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) := by
        rw [← sq_sqrt g₃]
        have g₄: 0 ≤ a n := by
          refine le_of_lt ?_
          refine h₀₁ n ?_
          constructor
          . exact hn.1
          . linarith
        refine (sq_eq_sq₀ g₄ ?_).mpr ?_
        . exact
          sqrt_nonneg
            ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
              Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
        refine h₀ (n) ?_
        constructor
        . exact hn.1
        . linarith
  have gn₁: a (n + 2) = sqrt ((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k)
      * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k) := by
        refine h₀ (n + 2) ?_
        constructor
        . linarith
        . linarith
  rw [add_sq, gn₁, sq_sqrt]
  . have ga₀: 1 ≤ n + 2 := by linarith
    rw [Finset.sum_Ico_succ_top ga₀ _, Finset.sum_Ico_succ_top ga₀ _]
    have ga₁: 1 ≤ n + 1 := by linarith
    rw [Finset.sum_Ico_succ_top ga₁ _, Finset.sum_Ico_succ_top ga₁ _]
    rw [add_assoc, add_assoc, add_assoc]
    rw [add_mul, mul_add]
    rw [← gn₀]
    repeat rw [add_assoc]
    refine add_lt_add_left ?_ (a (n) ^ 2)
    rw [mul_add (x (n + 1) + x (n + 2))]
    have h₂: 4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)) := by
      repeat rw [add_mul, mul_add, mul_add]
      repeat rw [mul_div_left_comm _ 1 _, one_mul]
      repeat rw [div_self ?_]
      . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
          = x (n + 1) * x (n + 1) := by
          rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
          simp
          exact ne_of_gt (hxp (n + 2))
        have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
          = x (n + 2) * x (n + 2) := by
          rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
          simp
          exact ne_of_gt (hxp (n + 1))
        have h₂₀: 0 < x (n + 1) * x (n + 2) := by
          refine mul_pos ?_ ?_
          . exact hxp (n + 1)
          . exact hxp (n + 2)
        have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
          refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
          rw [mul_add, hc₂, hc₃, ← sq, ← sq]
          refine lt_of_sub_pos ?_
          have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                    = (x (n + 1) - x (n + 2)) ^ 2 := by
                rw [sub_sq]
                linarith
          rw [gh₂₁]
          refine (sq_pos_iff).mpr ?_
          refine sub_ne_zero.mpr ?_
          exact hx (n+1) (n+2) (by linarith)
        linarith
      . exact ne_of_gt (hxp (n + 2))
      . exact ne_of_gt (hxp (n + 1))
    clear gn₀ gn₁ g₀ g₁ g₂ g₃ ga₀ ga₁
    have h₃: 4 * a (n) ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
        * (1 / x (n + 1) + 1 / x (n + 2)) +
        ((x (n + 1) + x (n + 2))
        * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
        exact imo_2023_p4_3 (fun k => x k) a hxp h₀ n hn
    linarith
  . refine mul_nonneg ?_ ?_
    . refine Finset.sum_nonneg ?_
      intros i _
      exact LT.lt.le (hxp i)
    . refine Finset.sum_nonneg ?_
      intros i _
      simp
      exact LT.lt.le (hxp i)


lemma imo_2023_p4_4_6
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : 0 ≤ a n + 2)
  (g₁ : 0 ≤ a (n + 2))
  (g₂ : 0 ≤ (a n + 2) ^ 2) :
  (a n + 2) ^ 2 < a (n + 2) ^ 2 := by
  have g₃: 0 ≤ ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) := by
    refine le_of_lt ?_
    refine mul_pos ?_ ?_
    . refine Finset.sum_pos ?_ ?_
      . exact fun i _ => hxp i
      . simp
        linarith
    . refine Finset.sum_pos ?_ ?_
      . intros i _
        exact one_div_pos.mpr (hxp i)
      . simp
        linarith
  have gn₀: a (n) ^ 2 = ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) := by
    rw [← sq_sqrt g₃]
    have g₄: 0 ≤ a n := by
      refine le_of_lt ?_
      refine h₀₁ n ?_
      constructor
      . exact hn.1
      . linarith
    refine (sq_eq_sq₀ g₄ ?_).mpr ?_
    . exact
      sqrt_nonneg
        ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
          Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
    . refine h₀ (n) ?_
      constructor
      . exact hn.1
      . linarith
  have gn₁: a (n + 2) = sqrt ((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k)
      * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k) := by
    refine h₀ (n + 2) ?_
    constructor
    . linarith
    . linarith
  rw [add_sq, gn₁, sq_sqrt]
  . have ga₀: 1 ≤ n + 2 := by linarith
    rw [Finset.sum_Ico_succ_top ga₀ _, Finset.sum_Ico_succ_top ga₀ _]
    have ga₁: 1 ≤ n + 1 := by linarith
    rw [Finset.sum_Ico_succ_top ga₁ _, Finset.sum_Ico_succ_top ga₁ _]
    rw [add_assoc, add_assoc, add_assoc]
    rw [add_mul, mul_add]
    rw [← gn₀]
    repeat rw [add_assoc]
    refine add_lt_add_left ?_ (a (n) ^ 2)
    rw [mul_add (x (n + 1) + x (n + 2))]
    have h₂: 4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)) := by
      repeat rw [add_mul, mul_add, mul_add]
      repeat rw [mul_div_left_comm _ 1 _, one_mul]
      repeat rw [div_self ?_]
      . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
          = x (n + 1) * x (n + 1) := by
          rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
          simp
          exact ne_of_gt (hxp (n + 2))
        have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
          = x (n + 2) * x (n + 2) := by
          rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
          simp
          exact ne_of_gt (hxp (n + 1))
        have h₂₀: 0 < x (n + 1) * x (n + 2) := by
          refine mul_pos ?_ ?_
          . exact hxp (n + 1)
          . exact hxp (n + 2)
        have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
          refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
          rw [mul_add, hc₂, hc₃, ← sq, ← sq]
          refine lt_of_sub_pos ?_
          have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                    = (x (n + 1) - x (n + 2)) ^ 2 := by
                rw [sub_sq]
                linarith
          rw [gh₂₁]
          refine (sq_pos_iff).mpr ?_
          refine sub_ne_zero.mpr ?_
          exact hx (n+1) (n+2) (by linarith)
        linarith
      . exact ne_of_gt (hxp (n + 2))
      . exact ne_of_gt (hxp (n + 1))
    clear gn₀ gn₁ g₀ g₁ g₂ g₃ ga₀ ga₁
    have h₃: 4 * a (n) ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
        * (1 / x (n + 1) + 1 / x (n + 2)) +
        ((x (n + 1) + x (n + 2))
        * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
        exact imo_2023_p4_3 (fun k => x k) a hxp h₀ n hn
    linarith
  . refine mul_nonneg ?_ ?_
    . refine Finset.sum_nonneg ?_
      intros i _
      exact LT.lt.le (hxp i)
    . refine Finset.sum_nonneg ?_
      intros i _
      simp
      exact LT.lt.le (hxp i)


lemma imo_2023_p4_4_7
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021) :
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2) :
  0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
    * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k := by
  refine le_of_lt ?_
  refine mul_pos ?_ ?_
  . refine Finset.sum_pos ?_ ?_
    . exact fun i _ => hxp i
    . simp
      linarith
  . refine Finset.sum_pos ?_ ?_
    . intros i _
      exact one_div_pos.mpr (hxp i)
    . simp
      linarith


lemma imo_2023_p4_4_8
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) :
  a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k := by
  rw [← sq_sqrt g₃]
  have g₄: 0 ≤ a n := by
    refine le_of_lt ?_
    refine h₀₁ n ?_
    constructor
    . exact hn.1
    . linarith
  refine (sq_eq_sq₀ g₄ ?_).mpr ?_
  . exact
    sqrt_nonneg
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
        Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  refine h₀ (n) ?_
  constructor
  . exact hn.1
  . linarith


lemma imo_2023_p4_4_9
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : 0 ≤ a n + 2)
  (g₁ : 0 ≤ a (n + 2))
  (g₂ : 0 ≤ (a n + 2) ^ 2)
  (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) :
  (a n + 2) ^ 2 < a (n + 2) ^ 2 := by
  have gn₀: a (n) ^ 2 = ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * (Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) := by
    rw [← sq_sqrt g₃]
    have g₄: 0 ≤ a n := by
      refine le_of_lt ?_
      refine h₀₁ n ?_
      constructor
      . exact hn.1
      . linarith
    refine (sq_eq_sq₀ g₄ ?_).mpr ?_
    . exact
      sqrt_nonneg
        ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
          Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
    . refine h₀ (n) ?_
      constructor
      . exact hn.1
      . linarith
  have gn₁: a (n + 2) = sqrt ((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k)
      * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k) := by
    refine h₀ (n + 2) ?_
    constructor
    . linarith
    . linarith
  rw [add_sq, gn₁, sq_sqrt]
  . have ga₀: 1 ≤ n + 2 := by linarith
    rw [Finset.sum_Ico_succ_top ga₀ _, Finset.sum_Ico_succ_top ga₀ _]
    have ga₁: 1 ≤ n + 1 := by linarith
    rw [Finset.sum_Ico_succ_top ga₁ _, Finset.sum_Ico_succ_top ga₁ _]
    rw [add_assoc, add_assoc, add_assoc]
    rw [add_mul, mul_add]
    rw [← gn₀]
    repeat rw [add_assoc]
    refine add_lt_add_left ?_ (a (n) ^ 2)
    rw [mul_add (x (n + 1) + x (n + 2))]
    have h₂: 4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)) := by
      repeat rw [add_mul, mul_add, mul_add]
      repeat rw [mul_div_left_comm _ 1 _, one_mul]
      repeat rw [div_self ?_]
      . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
          = x (n + 1) * x (n + 1) := by
          rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
          simp
          exact ne_of_gt (hxp (n + 2))
        have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
          = x (n + 2) * x (n + 2) := by
          rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
          simp
          exact ne_of_gt (hxp (n + 1))
        have h₂₀: 0 < x (n + 1) * x (n + 2) := by
          refine mul_pos ?_ ?_
          . exact hxp (n + 1)
          . exact hxp (n + 2)
        have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
          refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
          rw [mul_add, hc₂, hc₃, ← sq, ← sq]
          refine lt_of_sub_pos ?_
          have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                    = (x (n + 1) - x (n + 2)) ^ 2 := by
            rw [sub_sq]
            linarith
          rw [gh₂₁]
          refine (sq_pos_iff).mpr ?_
          refine sub_ne_zero.mpr ?_
          exact hx (n+1) (n+2) (by linarith)
        linarith
      . exact ne_of_gt (hxp (n + 2))
      . exact ne_of_gt (hxp (n + 1))
    clear gn₀ gn₁ g₀ g₁ g₂ g₃ ga₀ ga₁
    have h₃: 4 * a (n) ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
        * (1 / x (n + 1) + 1 / x (n + 2)) +
        ((x (n + 1) + x (n + 2))
        * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
        exact imo_2023_p4_3 (fun k => x k) a hxp h₀ n hn
    linarith
  . refine mul_nonneg ?_ ?_
    . refine Finset.sum_nonneg ?_
      intros i _
      exact LT.lt.le (hxp i)
    . refine Finset.sum_nonneg ?_
      intros i _
      simp
      exact LT.lt.le (hxp i)



lemma imo_2023_p4_4_10
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (g₄ : 0 ≤ a n) :
  a n ^ 2 = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
    * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) ^ 2 := by
  refine (sq_eq_sq₀ g₄ ?_).mpr ?_
  . exact
    sqrt_nonneg
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
        Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  . refine h₀ (n) ?_
    constructor
    . exact hn.1
    . linarith


lemma imo_2023_p4_4_11
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (g₄ : 0 ≤ a n) :
  0 ≤ √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
    Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
  exact sqrt_nonneg
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
        Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)


lemma imo_2023_p4_4_12
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : 0 ≤ a n + 2)
  (g₁ : 0 ≤ a (n + 2))
  (g₂ : 0 ≤ (a n + 2) ^ 2)
  (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (gn₁ : a (n + 2) =
    √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k)) :
  (a n + 2) ^ 2 < a (n + 2) ^ 2 := by
  rw [add_sq, gn₁, sq_sqrt]
  . have ga₀: 1 ≤ n + 2 := by linarith
    rw [Finset.sum_Ico_succ_top ga₀ _, Finset.sum_Ico_succ_top ga₀ _]
    have ga₁: 1 ≤ n + 1 := by linarith
    rw [Finset.sum_Ico_succ_top ga₁ _, Finset.sum_Ico_succ_top ga₁ _]
    rw [add_assoc, add_assoc, add_assoc]
    rw [add_mul, mul_add]
    rw [← gn₀]
    repeat rw [add_assoc]
    refine add_lt_add_left ?_ (a (n) ^ 2)
    rw [mul_add (x (n + 1) + x (n + 2))]
    have h₂: 4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)) := by
      repeat rw [add_mul, mul_add, mul_add]
      repeat rw [mul_div_left_comm _ 1 _, one_mul]
      repeat rw [div_self ?_]
      . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
          = x (n + 1) * x (n + 1) := by
          rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
          simp
          exact ne_of_gt (hxp (n + 2))
        have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
          = x (n + 2) * x (n + 2) := by
          rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
          simp
          exact ne_of_gt (hxp (n + 1))
        have h₂₀: 0 < x (n + 1) * x (n + 2) := by
          refine mul_pos ?_ ?_
          . exact hxp (n + 1)
          . exact hxp (n + 2)
        have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
          refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
          rw [mul_add, hc₂, hc₃, ← sq, ← sq]
          refine lt_of_sub_pos ?_
          have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                    = (x (n + 1) - x (n + 2)) ^ 2 := by
                rw [sub_sq]
                linarith
          rw [gh₂₁]
          refine (sq_pos_iff).mpr ?_
          refine sub_ne_zero.mpr ?_
          exact hx (n+1) (n+2) (by linarith)
        linarith
      . exact ne_of_gt (hxp (n + 2))
      . exact ne_of_gt (hxp (n + 1))
    clear gn₀ gn₁ g₀ g₁ g₂ g₃ ga₀ ga₁
    have h₃: 4 * a (n) ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
        * (1 / x (n + 1) + 1 / x (n + 2)) +
        ((x (n + 1) + x (n + 2))
        * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
        exact imo_2023_p4_3 (fun k => x k) a hxp h₀ n hn
    linarith
  . refine mul_nonneg ?_ ?_
    . refine Finset.sum_nonneg ?_
      intros i _
      exact LT.lt.le (hxp i)
    . refine Finset.sum_nonneg ?_
      intros i _
      simp
      exact LT.lt.le (hxp i)



lemma imo_2023_p4_4_13
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : 0 ≤ a n + 2)
  (g₁ : 0 ≤ a (n + 2))
  (g₂ : 0 ≤ (a n + 2) ^ 2)
  (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (gn₁ : a (n + 2) =
    √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k)) :
  a n ^ 2 + 2 * a n * 2 + 2 ^ 2 <
    (Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k)
    * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k := by
  have ga₀: 1 ≤ n + 2 := by linarith
  rw [Finset.sum_Ico_succ_top ga₀ _, Finset.sum_Ico_succ_top ga₀ _]
  have ga₁: 1 ≤ n + 1 := by linarith
  rw [Finset.sum_Ico_succ_top ga₁ _, Finset.sum_Ico_succ_top ga₁ _]
  rw [add_assoc, add_assoc, add_assoc]
  rw [add_mul, mul_add]
  rw [← gn₀]
  repeat rw [add_assoc]
  refine add_lt_add_left ?_ (a (n) ^ 2)
  rw [mul_add (x (n + 1) + x (n + 2))]
  have h₂: 4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)) := by
    repeat rw [add_mul, mul_add, mul_add]
    repeat rw [mul_div_left_comm _ 1 _, one_mul]
    repeat rw [div_self ?_]
    . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
        = x (n + 1) * x (n + 1) := by
        rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
        simp
        exact ne_of_gt (hxp (n + 2))
      have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
        = x (n + 2) * x (n + 2) := by
        rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
        simp
        exact ne_of_gt (hxp (n + 1))
      have h₂₀: 0 < x (n + 1) * x (n + 2) := by
        refine mul_pos ?_ ?_
        . exact hxp (n + 1)
        . exact hxp (n + 2)
      have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
        refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
        rw [mul_add, hc₂, hc₃, ← sq, ← sq]
        refine lt_of_sub_pos ?_
        have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                  = (x (n + 1) - x (n + 2)) ^ 2 := by
              rw [sub_sq]
              linarith
        rw [gh₂₁]
        refine (sq_pos_iff).mpr ?_
        refine sub_ne_zero.mpr ?_
        exact hx (n+1) (n+2) (by linarith)
      linarith
    . exact ne_of_gt (hxp (n + 2))
    . exact ne_of_gt (hxp (n + 1))
  clear gn₀ gn₁ g₀ g₁ g₂ g₃ ga₀ ga₁
  have h₃: 4 * a (n) ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * (1 / x (n + 1) + 1 / x (n + 2)) +
      ((x (n + 1) + x (n + 2))
      * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact imo_2023_p4_3 (fun k => x k) a hxp h₀ n hn
  linarith


lemma imo_2023_p4_4_14
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : 0 ≤ a n + 2)
  (g₁ : 0 ≤ a (n + 2))
  (g₂ : 0 ≤ (a n + 2) ^ 2)
  (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (gn₁ : a (n + 2) =
    √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  (ga₀ : 1 ≤ n + 2) :
  a n ^ 2 + 2 * a n * 2 + 2 ^ 2 <
    ((Finset.sum (Finset.Ico 1 (n + 2)) fun k => x k) + x (n + 2)) *
      ((Finset.sum (Finset.Ico 1 (n + 2)) fun k => 1 / x k) + 1 / x (n + 2)) := by
  have ga₁: 1 ≤ n + 1 := by linarith
  rw [Finset.sum_Ico_succ_top ga₁ _, Finset.sum_Ico_succ_top ga₁ _]
  rw [add_assoc, add_assoc, add_assoc]
  rw [add_mul, mul_add]
  rw [← gn₀]
  repeat rw [add_assoc]
  refine add_lt_add_left ?_ (a (n) ^ 2)
  rw [mul_add (x (n + 1) + x (n + 2))]
  have h₂: 4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)) := by
    repeat rw [add_mul, mul_add, mul_add]
    repeat rw [mul_div_left_comm _ 1 _, one_mul]
    repeat rw [div_self ?_]
    . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
        = x (n + 1) * x (n + 1) := by
        rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
        simp
        exact ne_of_gt (hxp (n + 2))
      have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
        = x (n + 2) * x (n + 2) := by
        rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
        simp
        exact ne_of_gt (hxp (n + 1))
      have h₂₀: 0 < x (n + 1) * x (n + 2) := by
        refine mul_pos ?_ ?_
        . exact hxp (n + 1)
        . exact hxp (n + 2)
      have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
        refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
        rw [mul_add, hc₂, hc₃, ← sq, ← sq]
        refine lt_of_sub_pos ?_
        have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                  = (x (n + 1) - x (n + 2)) ^ 2 := by
              rw [sub_sq]
              linarith
        rw [gh₂₁]
        refine (sq_pos_iff).mpr ?_
        refine sub_ne_zero.mpr ?_
        exact hx (n+1) (n+2) (by linarith)
      linarith
    . exact ne_of_gt (hxp (n + 2))
    . exact ne_of_gt (hxp (n + 1))
  clear gn₀ gn₁ g₀ g₁ g₂ g₃ ga₀ ga₁
  have h₃: 4 * a (n) ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * (1 / x (n + 1) + 1 / x (n + 2)) +
      ((x (n + 1) + x (n + 2))
      * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact imo_2023_p4_3 (fun k => x k) a hxp h₀ n hn
  linarith


lemma imo_2023_p4_4_15
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  (ga₀ : 1 ≤ n + 2)
  (ga₁ : 1 ≤ n + 1)
  (ga₂ : a n ^ 2 + (2 * a n * 2 + 2 ^ 2) <
    a n ^ 2 + (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1) + 1 / x (n + 2)) +
      (x (n + 1) + x (n + 2)) * ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + (1 / x (n + 1) + 1 / x (n + 2)))) :
  a n ^ 2 + 2 * a n * 2 + 2 ^ 2 <
    (Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k)
      * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k := by
  rw [Finset.sum_Ico_succ_top ga₀ _, Finset.sum_Ico_succ_top ga₀ _]
  rw [Finset.sum_Ico_succ_top ga₁ _, Finset.sum_Ico_succ_top ga₁ _]
  rw [add_assoc, add_assoc, add_assoc]
  rw [add_mul, mul_add]
  rw [← gn₀]
  repeat rw [add_assoc]
  refine add_lt_add_left ?_ (a (n) ^ 2)
  linarith


lemma imo_2023_p4_4_16
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : 0 ≤ a n + 2)
  (g₁ : 0 ≤ a (n + 2))
  (g₂ : 0 ≤ (a n + 2) ^ 2)
  (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (gn₁ : a (n + 2) =
    √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  (ga₀ : 1 ≤ n + 2)
  (ga₁ : 1 ≤ n + 1) :
  a n ^ 2 + (2 * a n * 2 + 2 ^ 2) <
    a n ^ 2 + (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1) + 1 / x (n + 2)) +
      (x (n + 1) + x (n + 2)) *
      ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) + (1 / x (n + 1) + 1 / x (n + 2))) := by
  repeat rw [add_assoc]
  refine add_lt_add_left ?_ (a (n) ^ 2)
  rw [mul_add (x (n + 1) + x (n + 2))]
  have h₂: 4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)) := by
    repeat rw [add_mul, mul_add, mul_add]
    repeat rw [mul_div_left_comm _ 1 _, one_mul]
    repeat rw [div_self ?_]
    . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
        = x (n + 1) * x (n + 1) := by
        rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
        simp
        exact ne_of_gt (hxp (n + 2))
      have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
        = x (n + 2) * x (n + 2) := by
        rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
        simp
        exact ne_of_gt (hxp (n + 1))
      have h₂₀: 0 < x (n + 1) * x (n + 2) := by
        refine mul_pos ?_ ?_
        . exact hxp (n + 1)
        . exact hxp (n + 2)
      have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
        refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
        rw [mul_add, hc₂, hc₃, ← sq, ← sq]
        refine lt_of_sub_pos ?_
        have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                  = (x (n + 1) - x (n + 2)) ^ 2 := by
              rw [sub_sq]
              linarith
        rw [gh₂₁]
        refine (sq_pos_iff).mpr ?_
        refine sub_ne_zero.mpr ?_
        exact hx (n+1) (n+2) (by linarith)
      linarith
    . exact ne_of_gt (hxp (n + 2))
    . exact ne_of_gt (hxp (n + 1))
  clear gn₀ gn₁ g₀ g₁ g₂ g₃ ga₀ ga₁
  have h₃: 4 * a (n) ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * (1 / x (n + 1) + 1 / x (n + 2)) +
      ((x (n + 1) + x (n + 2))
      * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact imo_2023_p4_3 (fun k => x k) a hxp h₀ n hn
  linarith


lemma imo_2023_p4_4_17
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1)
  (ga₂ : 2 * a n * 2 + 2 ^ 2 <
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1) + 1 / x (n + 2)) +
      (((x (n + 1) + x (n + 2)) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)))) :
  a n ^ 2 + 2 * a n * 2 + 2 ^ 2 <
    (Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) *
      Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k := by
  have ga₀: 1 ≤ n + 2 := by linarith
  rw [Finset.sum_Ico_succ_top ga₀ _, Finset.sum_Ico_succ_top ga₀ _]
  have ga₁: 1 ≤ n + 1 := by linarith
  rw [Finset.sum_Ico_succ_top ga₁ _, Finset.sum_Ico_succ_top ga₁ _]
  rw [add_assoc, add_assoc, add_assoc]
  rw [add_mul, mul_add]
  rw [← gn₀]
  repeat rw [add_assoc]
  refine add_lt_add_left ?_ (a (n) ^ 2)
  linarith


lemma imo_2023_p4_4_18
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1) :
  4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)) := by
  repeat rw [add_mul, mul_add, mul_add]
  repeat rw [mul_div_left_comm _ 1 _, one_mul]
  repeat rw [div_self ?_]
  . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
      = x (n + 1) * x (n + 1) := by
      rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
      simp
      exact ne_of_gt (hxp (n + 2))
    have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
      = x (n + 2) * x (n + 2) := by
      rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
      simp
      exact ne_of_gt (hxp (n + 1))
    have h₂₀: 0 < x (n + 1) * x (n + 2) := by
      refine mul_pos ?_ ?_
      . exact hxp (n + 1)
      . exact hxp (n + 2)
    have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
      refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
      rw [mul_add, hc₂, hc₃, ← sq, ← sq]
      refine lt_of_sub_pos ?_
      have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                = (x (n + 1) - x (n + 2)) ^ 2 := by
            rw [sub_sq]
            linarith
      rw [gh₂₁]
      refine (sq_pos_iff).mpr ?_
      refine sub_ne_zero.mpr ?_
      exact hx (n+1) (n+2) (by linarith)
    linarith
  . exact ne_of_gt (hxp (n + 2))
  . exact ne_of_gt (hxp (n + 1))


lemma imo_2023_p4_4_19
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1)
  -- (ga₂: 4 < x (n + 1) / x (n + 1) + x (n + 1) / x (n + 2) + (x (n + 2) / x (n + 1) + x (n + 2) / x (n + 2))) :
  4 < x (n + 1) / x (n + 1) + x (n + 1) / x (n + 2) + (x (n + 2) / x (n + 1) + x (n + 2) / x (n + 2)) := by
  repeat rw [div_self ?_]
  . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
      = x (n + 1) * x (n + 1) := by
      rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
      simp
      exact ne_of_gt (hxp (n + 2))
    have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
      = x (n + 2) * x (n + 2) := by
      rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
      simp
      exact ne_of_gt (hxp (n + 1))
    have h₂₀: 0 < x (n + 1) * x (n + 2) := by
      refine mul_pos ?_ ?_
      . exact hxp (n + 1)
      . exact hxp (n + 2)
    have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
      refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
      rw [mul_add, hc₂, hc₃, ← sq, ← sq]
      refine lt_of_sub_pos ?_
      have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                = (x (n + 1) - x (n + 2)) ^ 2 := by
            rw [sub_sq]
            linarith
      rw [gh₂₁]
      refine (sq_pos_iff).mpr ?_
      refine sub_ne_zero.mpr ?_
      exact hx (n+1) (n+2) (by linarith)
    linarith
  . exact ne_of_gt (hxp (n + 2))
  . exact ne_of_gt (hxp (n + 1))


lemma imo_2023_p4_4_20
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1) :
  4 < x (n + 1) / x (n + 1) + x (n + 1) / x (n + 2) +
    (x (n + 2) / x (n + 1) + x (n + 2) / x (n + 2)) := by
  -- repeat rw [mul_div_left_comm _ 1 _, one_mul]
  repeat rw [div_self ?_]
  . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
      = x (n + 1) * x (n + 1) := by
      rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
      simp
      exact ne_of_gt (hxp (n + 2))
    have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
      = x (n + 2) * x (n + 2) := by
      rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
      simp
      exact ne_of_gt (hxp (n + 1))
    have h₂₀: 0 < x (n + 1) * x (n + 2) := by
      refine mul_pos ?_ ?_
      . exact hxp (n + 1)
      . exact hxp (n + 2)
    have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
      refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
      rw [mul_add, hc₂, hc₃, ← sq, ← sq]
      refine lt_of_sub_pos ?_
      have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                = (x (n + 1) - x (n + 2)) ^ 2 := by
            rw [sub_sq]
            linarith
      rw [gh₂₁]
      refine (sq_pos_iff).mpr ?_
      refine sub_ne_zero.mpr ?_
      exact hx (n+1) (n+2) (by linarith)
    linarith
  . exact ne_of_gt (hxp (n + 2))
  . exact ne_of_gt (hxp (n + 1))


lemma imo_2023_p4_4_21
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1) :
  x (n + 2) ≠ 0 := by
  exact ne_of_gt (hxp (n + 2))


lemma imo_2023_p4_4_22
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1) :
  4 < 1 + x (n + 1) / x (n + 2) + (x (n + 2) / x (n + 1) + 1) := by
  have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
    = x (n + 1) * x (n + 1) := by
    rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
    simp
    exact ne_of_gt (hxp (n + 2))
  have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
    = x (n + 2) * x (n + 2) := by
    rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
    simp
    exact ne_of_gt (hxp (n + 1))
  have h₂₀: 0 < x (n + 1) * x (n + 2) := by
    refine mul_pos ?_ ?_
    . exact hxp (n + 1)
    . exact hxp (n + 2)
  have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
    refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
    rw [mul_add, hc₂, hc₃, ← sq, ← sq]
    refine lt_of_sub_pos ?_
    have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
              = (x (n + 1) - x (n + 2)) ^ 2 := by
          rw [sub_sq]
          linarith
    rw [gh₂₁]
    refine (sq_pos_iff).mpr ?_
    refine sub_ne_zero.mpr ?_
    exact hx (n+1) (n+2) (by linarith)
  linarith


lemma imo_2023_p4_4_23
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1) :
  x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2)) = x (n + 1) * x (n + 1) := by
  rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
  simp
  exact ne_of_gt (hxp (n + 2))


lemma imo_2023_p4_4_24
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1)
  -- (hc₂ : x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2)) = x (n + 1) * x (n + 1)) :
  x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1)) = x (n + 2) * x (n + 2) := by
  have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
    = x (n + 2) * x (n + 2) := by
    rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
    simp
    exact ne_of_gt (hxp (n + 1))
  linarith


lemma imo_2023_p4_4_25
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1)
  (hc₂ : x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2)) = x (n + 1) * x (n + 1))
  (hc₃ : x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1)) = x (n + 2) * x (n + 2))
  (h₂₀ : 0 < x (n + 1) * x (n + 2)) :
  4 < 1 + x (n + 1) / x (n + 2) + (x (n + 2) / x (n + 1) + 1) := by
  have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
    refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
    rw [mul_add, hc₂, hc₃, ← sq, ← sq]
    refine lt_of_sub_pos ?_
    have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
              = (x (n + 1) - x (n + 2)) ^ 2 := by
          rw [sub_sq]
          linarith
    rw [gh₂₁]
    refine (sq_pos_iff).mpr ?_
    refine sub_ne_zero.mpr ?_
    exact hx (n+1) (n+2) (by linarith)
  linarith


lemma imo_2023_p4_4_26
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1)
  (hc₂ : x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2)) = x (n + 1) * x (n + 1))
  (hc₃ : x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1)) = x (n + 2) * x (n + 2))
  (h₂₀ : 0 < x (n + 1) * x (n + 2)) :
  2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
  refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
  rw [mul_add, hc₂, hc₃, ← sq, ← sq]
  refine lt_of_sub_pos ?_
  have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
            = (x (n + 1) - x (n + 2)) ^ 2 := by
        rw [sub_sq]
        linarith
  rw [gh₂₁]
  refine (sq_pos_iff).mpr ?_
  refine sub_ne_zero.mpr ?_
  exact hx (n+1) (n+2) (by linarith)


lemma imo_2023_p4_4_27
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1)
  (hc₂ : x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2)) = x (n + 1) * x (n + 1))
  (hc₃ : x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1)) = x (n + 2) * x (n + 2)) :
  -- (h₂₀ : 0 < x (n + 1) * x (n + 2)) :
  x (n + 1) * x (n + 2) * 2 < x (n + 1) * x (n + 2) *
    (x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1)) := by
  rw [mul_add, hc₂, hc₃, ← sq, ← sq]
  refine lt_of_sub_pos ?_
  have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
            = (x (n + 1) - x (n + 2)) ^ 2 := by
        rw [sub_sq]
        linarith
  rw [gh₂₁]
  refine (sq_pos_iff).mpr ?_
  refine sub_ne_zero.mpr ?_
  exact hx (n+1) (n+2) (by linarith)


lemma imo_2023_p4_4_28
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1)
  (hc₂ : x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2)) = x (n + 1) * x (n + 1))
  (hc₃ : x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1)) = x (n + 2) * x (n + 2))
  (h₂₀ : 0 < x (n + 1) * x (n + 2)) :
  2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
  refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
  rw [mul_add, hc₂, hc₃, ← sq, ← sq]
  refine lt_of_sub_pos ?_
  have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
            = (x (n + 1) - x (n + 2)) ^ 2 := by
        rw [sub_sq]
        linarith
  rw [gh₂₁]
  refine (sq_pos_iff).mpr ?_
  refine sub_ne_zero.mpr ?_
  exact hx (n+1) (n+2) (by linarith)


lemma imo_2023_p4_4_29
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1)
  -- (hc₂ : x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2)) = x (n + 1) * x (n + 1))
  -- (hc₃ : x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1)) = x (n + 2) * x (n + 2))
  -- (h₂₀ : 0 < x (n + 1) * x (n + 2)) :
  x (n + 1) * x (n + 2) * 2 < x (n + 1) ^ 2 + x (n + 2) ^ 2 := by
  refine lt_of_sub_pos ?_
  have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
            = (x (n + 1) - x (n + 2)) ^ 2 := by
    rw [sub_sq]
    linarith
  rw [gh₂₁]
  refine (sq_pos_iff).mpr ?_
  refine sub_ne_zero.mpr ?_
  exact hx (n+1) (n+2) (by linarith)


lemma imo_2023_p4_4_30
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1)
  -- (hc₂ : x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2)) = x (n + 1) * x (n + 1))
  -- (hc₃ : x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1)) = x (n + 2) * x (n + 2))
  -- (h₂₀ : 0 < x (n + 1) * x (n + 2)) :
  0 < x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2 := by
  have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
            = (x (n + 1) - x (n + 2)) ^ 2 := by
    rw [sub_sq]
    linarith
  rw [gh₂₁]
  refine (sq_pos_iff).mpr ?_
  refine sub_ne_zero.mpr ?_
  exact hx (n+1) (n+2) (by linarith)


lemma imo_2023_p4_4_31
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1)
  -- (hc₂ : x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2)) = x (n + 1) * x (n + 1))
  -- (hc₃ : x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1)) = x (n + 2) * x (n + 2))
  -- (h₂₀ : 0 < x (n + 1) * x (n + 2)) :
  x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2 = (x (n + 1) - x (n + 2)) ^ 2 := by
  rw [sub_sq]
  linarith


lemma imo_2023_p4_4_32
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1)
  -- (hc₂ : x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2)) = x (n + 1) * x (n + 1))
  -- (hc₃ : x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1)) = x (n + 2) * x (n + 2))
  -- (h₂₀ : 0 < x (n + 1) * x (n + 2))
  (gh₂₁ : x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2 = (x (n + 1) - x (n + 2)) ^ 2) :
  0 < x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2 := by
  rw [gh₂₁]
  refine (sq_pos_iff).mpr ?_
  refine sub_ne_zero.mpr ?_
  exact hx (n+1) (n+2) (by linarith)


lemma imo_2023_p4_4_33
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k))
  -- (ga₀ : 1 ≤ n + 2)
  -- (ga₁ : 1 ≤ n + 1)
  -- (hc₂ : x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2)) = x (n + 1) * x (n + 1))
  -- (hc₃ : x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1)) = x (n + 2) * x (n + 2))
  -- (h₂₀ : 0 < x (n + 1) * x (n + 2))
  -- (gh₂₁ : x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2 = (x (n + 1) - x (n + 2)) ^ 2) :
  x (n + 1) - x (n + 2) ≠ 0 := by
  refine sub_ne_zero.mpr ?_
  exact hx (n+1) (n+2) (by linarith)


lemma imo_2023_p4_4_34
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (h₂ : 4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2))) :
  2 * a n * 2 + 2 ^ 2 <
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1) + 1 / x (n + 2)) +
      (((x (n + 1) + x (n + 2)) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2))) := by
  have h₃: 4 * a (n) ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * (1 / x (n + 1) + 1 / x (n + 2)) +
      ((x (n + 1) + x (n + 2))
      * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact imo_2023_p4_3 (fun k => x k) a hxp h₀ n hn
  linarith


lemma imo_2023_p4_4_35
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (h₂ : 4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)))
  (h₃ : 4 * a n ≤
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1) + 1 / x (n + 2)) +
      (x (n + 1) + x (n + 2)) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) :
  2 * a n * 2 + 2 ^ 2 <
    (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * (1 / x (n + 1) + 1 / x (n + 2)) +
      (((x (n + 1) + x (n + 2)) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) +
        (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2))) := by
  have h₂: 4 < (x (n + 1) + x (n + 2)) * (1 / x (n + 1) + 1 / x (n + 2)) := by
    repeat rw [add_mul, mul_add, mul_add]
    repeat rw [mul_div_left_comm _ 1 _, one_mul]
    repeat rw [div_self ?_]
    . have hc₂: x (n + 1) * x (n + 2) * (x (n + 1) / x (n + 2))
        = x (n + 1) * x (n + 1) := by
        rw [mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
        simp
        exact ne_of_gt (hxp (n + 2))
      have hc₃: x (n + 1) * x (n + 2) * (x (n + 2) / x (n + 1))
        = x (n + 2) * x (n + 2) := by
        rw [mul_comm (x (n + 1)) (x (n + 2)), mul_assoc, ← mul_div_assoc, mul_div_right_comm, div_self ?_]
        simp
        exact ne_of_gt (hxp (n + 1))
      have h₂₀: 0 < x (n + 1) * x (n + 2) := by
        refine mul_pos ?_ ?_
        . exact hxp (n + 1)
        . exact hxp (n + 2)
      have h₂₁: 2 < x (n + 1) / x (n + 2) + x (n + 2) / x (n + 1) := by
        refine lt_of_mul_lt_mul_left ?_ (le_of_lt h₂₀)
        rw [mul_add, hc₂, hc₃, ← sq, ← sq]
        refine lt_of_sub_pos ?_
        have gh₂₁: x (n + 1) ^ 2 + x (n + 2) ^ 2 - x (n + 1) * x (n + 2) * 2
                  = (x (n + 1) - x (n + 2)) ^ 2 := by
          rw [sub_sq]
          linarith
        rw [gh₂₁]
        refine (sq_pos_iff).mpr ?_
        refine sub_ne_zero.mpr ?_
        exact hx (n+1) (n+2) (by linarith)
      linarith
    . exact ne_of_gt (hxp (n + 2))
    . exact ne_of_gt (hxp (n + 1))
  linarith


lemma imo_2023_p4_4_36
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k)) :
  0 ≤ (Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) *
    Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k := by
  refine mul_nonneg ?_ ?_
  . refine Finset.sum_nonneg ?_
    intros i _
    exact LT.lt.le (hxp i)
  . refine Finset.sum_nonneg ?_
    intros i _
    simp
    exact LT.lt.le (hxp i)


lemma imo_2023_p4_4_37
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k)) :
  0 ≤ Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k := by
  refine Finset.sum_nonneg ?_
  intros i _
  exact LT.lt.le (hxp i)


lemma imo_2023_p4_4_38
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ) :
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : 0 ≤ a n + 2)
  -- (g₁ : 0 ≤ a (n + 2))
  -- (g₂ : 0 ≤ (a n + 2) ^ 2)
  -- (g₃ : 0 ≤ (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₀ : a n ^ 2 = (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)
  -- (gn₁ : a (n + 2) =
  --   √((Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k)) :
  0 ≤ Finset.sum (Finset.Ico 1 (n + 2 + 1)) fun k => 1 / x k := by
  refine Finset.sum_nonneg ?_
  intros i _
  simp
  exact LT.lt.le (hxp i)








lemma imo_2023_p4_5
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₁ : ∀ (n : ℕ), (1 ≤ n ∧ n ≤ 2023) → ∃ (kz:ℤ), (a n = ↑kz ))
  (ha1 : a 1 = 1) :
  3034 ≤ a 2023 := by
  have h₀₁: ∀ (n : ℕ), (1 ≤ n ∧ n ≤ 2023) → 0 < a n := by
    intros n hn
    have ha: a n = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
       * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
      exact h₀ (n) (hn)
    rw [ha]
    refine Real.sqrt_pos.mpr ?_
    refine mul_pos ?_ ?_
    . refine Finset.sum_pos ?_ ?_
      . intros i _
        exact hxp i
      . simp
        linarith
    . refine Finset.sum_pos ?_ ?_
      . intros i _
        exact one_div_pos.mpr (hxp i)
      . simp
        linarith
  have h₁₁: ∀ (n : ℕ), (1 ≤ n ∧ n ≤ 2023) → ∃ (kn:ℕ), a n = ↑kn := by
    intros n hn
    have g₁₁: 0 < a n := by
      exact h₀₁ n hn
    let ⟨p, gp⟩ := h₁ n hn
    let q:ℕ := Int.toNat p
    have g₁₂: ↑q = p := by
      refine Int.toNat_of_nonneg ?_
      rw [gp] at g₁₁
      norm_cast at g₁₁
      exact Int.le_of_lt g₁₁
    use q
    rw [gp]
    norm_cast
    exact id g₁₂.symm
  have h₂₁: ∀ (n:ℕ), (1 ≤ n ∧ n ≤ 2021) → a n + 2 < a (n+2) := by
    exact fun n a_1 => imo_2023_p4_4 (fun i => x i) a hxp hx h₀ h₀₁ n a_1
  have h₂: ∀ (n:ℕ), (1 ≤ n ∧ n ≤ 2021) → a n + 3 ≤ a (n+2) := by
    intros n hn
    have g₀: a n + 2 < a (n + 2) := by exact h₂₁ n hn
    have g₀₁: ∃ (p:ℕ), a n = ↑p := by
      apply h₁₁
      constructor
      . linarith
      . linarith
    have g₀₂: ∃ (q:ℕ), a (n + 2) = ↑q := by
      apply h₁₁
      constructor
      . linarith
      . linarith
    let ⟨p, _⟩ := g₀₁
    let ⟨q, _⟩ := g₀₂
    have g₁: p + 2 < q := by
      suffices g₁₁: ↑p + (2:ℝ) < ↑q
      . norm_cast at g₁₁
      . linarith
    have g₂: ↑p + (3:ℝ) ≤ ↑q := by norm_cast
    linarith
  have h₃: ∀ (n:ℕ), (0 ≤ n ∧ n ≤ 1010) → a 1 + 3 * (↑(n)  + 1) ≤ a (3 + 2 * n) := by
    intros n hn
    induction' n with d hd
    · simp
      exact h₂ (1) (by norm_num)
    · rw [mul_add]
      simp
      have g₀: a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1)) := by
        refine h₂ (3 + 2 * d) ?_
        constructor
        . linarith
        . linarith
      have g₁: a 1 + 3 * (↑d + 1) + 3 ≤ a (3 + 2 * d) + 3 := by
        refine add_le_add_right ?_ (3)
        apply hd
        constructor
        . linarith
        . linarith
      refine le_trans (by linarith[g₁]) g₀
  rw [ha1] at h₃
  have h₄: (3034:ℝ)  = 1 + 3 * (↑1010 + 1) := by norm_num
  rw [h₄]
  exact h₃ (1010) (by norm_num)



lemma imo_2023_p4_5_1
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) :
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ kz, a n = kz)
  -- (ha1 : a 1 = 1) :
  ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n := by
  intros n hn
  have ha: a n = sqrt ((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k)
      * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k) := by
    exact h₀ (n) (hn)
  rw [ha]
  refine Real.sqrt_pos.mpr ?_
  refine mul_pos ?_ ?_
  . refine Finset.sum_pos ?_ ?_
    . intros i _
      exact hxp i
    . simp
      linarith
  . refine Finset.sum_pos ?_ ?_
    . intros i _
      exact one_div_pos.mpr (hxp i)
    . simp
      linarith


lemma imo_2023_p4_5_2
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ kz, a n = kz)
  -- (ha1 : a 1 = 1)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2023)
  (ha : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) :
  0 < a n := by
  rw [ha]
  refine Real.sqrt_pos.mpr ?_
  refine mul_pos ?_ ?_
  . refine Finset.sum_pos ?_ ?_
    . intros i _
      exact hxp i
    . simp
      linarith
  . refine Finset.sum_pos ?_ ?_
    . intros i _
      exact one_div_pos.mpr (hxp i)
    . simp
      linarith


lemma imo_2023_p4_5_3
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ kz, a n = kz)
  -- (ha1 : a 1 = 1)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2023) :
  -- (ha : a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) :
  0 < (Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
    Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k := by
  refine mul_pos ?_ ?_
  . refine Finset.sum_pos ?_ ?_
    . intros i _
      exact hxp i
    . simp
      linarith
  . refine Finset.sum_pos ?_ ?_
    . intros i _
      exact one_div_pos.mpr (hxp i)
    . simp
      linarith


lemma imo_2023_p4_5_4
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = kz)
  (ha1 : a 1 = 1)
  (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n) :
  3034 ≤ a 2023 := by
  have h₁₁: ∀ (n : ℕ), (1 ≤ n ∧ n ≤ 2023) → ∃ (kn:ℕ), a n = ↑kn := by
    intros n hn
    have g₁₁: 0 < a n := by
      exact h₀₁ n hn
    let ⟨p, gp⟩ := h₁ n hn
    let q:ℕ := Int.toNat p
    have g₁₂: ↑q = p := by
      refine Int.toNat_of_nonneg ?_
      rw [gp] at g₁₁
      norm_cast at g₁₁
      exact Int.le_of_lt g₁₁
    use q
    rw [gp]
    norm_cast
    exact id g₁₂.symm
  have h₂₁: ∀ (n:ℕ), (1 ≤ n ∧ n ≤ 2021) → a n + 2 < a (n+2) := by
    exact fun n a_1 => imo_2023_p4_4 (fun i => x i) a hxp hx h₀ h₀₁ n a_1
  have h₂: ∀ (n:ℕ), (1 ≤ n ∧ n ≤ 2021) → a n + 3 ≤ a (n+2) := by
    intros n hn
    have g₀: a n + 2 < a (n + 2) := by exact h₂₁ n hn
    have g₀₁: ∃ (p:ℕ), a n = ↑p := by
      apply h₁₁
      constructor
      . linarith
      . linarith
    have g₀₂: ∃ (q:ℕ), a (n + 2) = ↑q := by
      apply h₁₁
      constructor
      . linarith
      . linarith
    let ⟨p, _⟩ := g₀₁
    let ⟨q, _⟩ := g₀₂
    have g₁: p + 2 < q := by
      suffices g₁₁: ↑p + (2:ℝ) < ↑q
      . norm_cast at g₁₁
      . linarith
    have g₂: ↑p + (3:ℝ) ≤ ↑q := by norm_cast
    linarith
  have h₃: ∀ (n:ℕ), (0 ≤ n ∧ n ≤ 1010) → a 1 + 3 * (↑(n)  + 1) ≤ a (3 + 2 * n) := by
    intros n hn
    induction' n with d hd
    · simp
      exact h₂ (1) (by norm_num)
    · rw [mul_add]
      simp
      have g₀: a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1)) := by
        refine h₂ (3 + 2 * d) ?_
        constructor
        . linarith
        . linarith
      have g₁: a 1 + 3 * (↑d + 1) + 3 ≤ a (3 + 2 * d) + 3 := by
        refine add_le_add_right ?_ (3)
        apply hd
        constructor
        . linarith
        . linarith
      refine le_trans (by linarith[g₁]) g₀
  rw [ha1] at h₃
  have h₄: (3034:ℝ)  = 1 + 3 * (↑1010 + 1) := by norm_num
  rw [h₄]
  exact h₃ (1010) (by norm_num)


lemma imo_2023_p4_5_5
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = kz)
  -- (ha1 : a 1 = 1)
  (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n) :
  ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn := by
  intros n hn
  have g₁₁: 0 < a n := by
    exact h₀₁ n hn
  let ⟨p, gp⟩ := h₁ n hn
  let q:ℕ := Int.toNat p
  have g₁₂: ↑q = p := by
    refine Int.toNat_of_nonneg ?_
    rw [gp] at g₁₁
    norm_cast at g₁₁
    exact Int.le_of_lt g₁₁
  use q
  rw [gp]
  norm_cast
  exact id g₁₂.symm


lemma imo_2023_p4_5_6
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2023)
  (g₁₁ : 0 < a n) :
  ∃ (kn:ℕ), a n = ↑kn := by
  let ⟨p, gp⟩ := h₁ n hn
  let q:ℕ := Int.toNat p
  have g₁₂: ↑q = p := by
    refine Int.toNat_of_nonneg ?_
    rw [gp] at g₁₁
    norm_cast at g₁₁
    exact Int.le_of_lt g₁₁
  use q
  rw [gp]
  norm_cast
  exact id g₁₂.symm


lemma imo_2023_p4_5_7
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n q : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2023)
  (g₁₁ : 0 < a n)
  (p : ℤ)
  (gp : a n = ↑p)
  (hq : q = Int.toNat p) :
  ∃ kn:ℕ, a n = ↑kn := by
  have g₁₂: (↑q:ℤ) = p := by
    rw [hq]
    refine Int.toNat_of_nonneg ?_
    rw [gp] at g₁₁
    norm_cast at g₁₁
    exact Int.le_of_lt g₁₁
  use q
  rw [gp]
  exact congrArg Int.cast (id g₁₂.symm)


lemma imo_2023_p4_5_8
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n q : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2023)
  (g₁₁ : 0 < a n)
  (p : ℤ)
  (gp : a n = ↑p)
  (hq : q = Int.toNat p) :
  ↑q = p := by
  rw [hq]
  refine Int.toNat_of_nonneg ?_
  rw [gp] at g₁₁
  norm_cast at g₁₁
  exact Int.le_of_lt g₁₁


lemma imo_2023_p4_5_9
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n q : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2023)
  (g₁₁ : 0 < a n)
  (p : ℤ)
  (gp : a n = ↑p)
  (hq : q = Int.toNat p) :
  0 ≤ p := by
  rw [gp] at g₁₁
  norm_cast at g₁₁
  exact Int.le_of_lt g₁₁


lemma imo_2023_p4_5_10
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n q : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2023)
  -- (g₁₁ : 0 < a n)
  (p : ℤ)
  (gp : a n = ↑p)
  -- (hq : q = Int.toNat p)
  (g₁₂ : ↑q = p) :
  ∃ (kn:ℕ), a n = ↑kn := by
  use q
  rw [gp]
  norm_cast
  exact id g₁₂.symm


lemma imo_2023_p4_5_11
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2023)
  -- (g₁₁ : 0 < a n)
  (p : ℤ)
  (gp : a n = ↑p)
  (q : ℕ := Int.toNat p)
  (g₁₂ : ↑q = p) :
  a n = ↑q := by
  rw [gp]
  norm_cast
  exact id g₁₂.symm


lemma imo_2023_p4_5_12
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  (ha1 : a 1 = 1)
  (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn) :
  3034 ≤ a 2023 := by
  have h₂₁: ∀ (n:ℕ), (1 ≤ n ∧ n ≤ 2021) → a n + 2 < a (n+2) := by
    exact fun n a_1 => imo_2023_p4_4 (fun i => x i) a hxp hx h₀ h₀₁ n a_1
  have h₂: ∀ (n:ℕ), (1 ≤ n ∧ n ≤ 2021) → a n + 3 ≤ a (n+2) := by
    intros n hn
    have g₀: a n + 2 < a (n + 2) := by exact h₂₁ n hn
    have g₀₁: ∃ (p:ℕ), a n = ↑p := by
      apply h₁₁
      constructor
      . linarith
      . linarith
    have g₀₂: ∃ (q:ℕ), a (n + 2) = ↑q := by
      apply h₁₁
      constructor
      . linarith
      . linarith
    let ⟨p, _⟩ := g₀₁
    let ⟨q, _⟩ := g₀₂
    have g₁: p + 2 < q := by
      suffices g₁₁: ↑p + (2:ℝ) < ↑q
      . norm_cast at g₁₁
      . linarith
    have g₂: ↑p + (3:ℝ) ≤ ↑q := by norm_cast
    linarith
  have h₃: ∀ (n:ℕ), (0 ≤ n ∧ n ≤ 1010) → a 1 + 3 * (↑(n)  + 1) ≤ a (3 + 2 * n) := by
    intros n hn
    induction' n with d hd
    · simp
      exact h₂ (1) (by norm_num)
    · rw [mul_add]
      simp
      have g₀: a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1)) := by
        refine h₂ (3 + 2 * d) ?_
        constructor
        . linarith
        . linarith
      have g₁: a 1 + 3 * (↑d + 1) + 3 ≤ a (3 + 2 * d) + 3 := by
        refine add_le_add_right ?_ (3)
        apply hd
        constructor
        . linarith
        . linarith
      refine le_trans (by linarith[g₁]) g₀
  rw [ha1] at h₃
  have h₄: (3034:ℝ)  = 1 + 3 * (↑1010 + 1) := by norm_num
  rw [h₄]
  exact h₃ (1010) (by norm_num)



lemma imo_2023_p4_5_13
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2)) :
  3034 ≤ a 2023 := by
  have h₂: ∀ (n:ℕ), (1 ≤ n ∧ n ≤ 2021) → a n + 3 ≤ a (n+2) := by
    intros n hn
    have g₀: a n + 2 < a (n + 2) := by exact h₂₁ n hn
    have g₀₁: ∃ (p:ℕ), a n = ↑p := by
      apply h₁₁
      constructor
      . linarith
      . linarith
    have g₀₂: ∃ (q:ℕ), a (n + 2) = ↑q := by
      apply h₁₁
      constructor
      . linarith
      . linarith
    let ⟨p, _⟩ := g₀₁
    let ⟨q, _⟩ := g₀₂
    have g₁: p + 2 < q := by
      suffices g₁₁: ↑p + (2:ℝ) < ↑q
      . norm_cast at g₁₁
      . linarith
    have g₂: ↑p + (3:ℝ) ≤ ↑q := by norm_cast
    linarith
  have h₃: ∀ (n:ℕ), (0 ≤ n ∧ n ≤ 1010) → a 1 + 3 * (↑(n)  + 1) ≤ a (3 + 2 * n) := by
    intros n hn
    induction' n with d hd
    · simp
      exact h₂ (1) (by norm_num)
    · rw [mul_add]
      simp
      have g₀: a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1)) := by
        refine h₂ (3 + 2 * d) ?_
        constructor
        . linarith
        . linarith
      have g₁: a 1 + 3 * (↑d + 1) + 3 ≤ a (3 + 2 * d) + 3 := by
        refine add_le_add_right ?_ (3)
        apply hd
        constructor
        . linarith
        . linarith
      refine le_trans (by linarith[g₁]) g₀
  rw [ha1] at h₃
  have h₄: (3034:ℝ)  = 1 + 3 * (↑1010 + 1) := by norm_num
  rw [h₄]
  exact h₃ (1010) (by norm_num)


lemma imo_2023_p4_5_14
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2)) :
  ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2) := by
  intros n hn
  have g₀: a n + 2 < a (n + 2) := by exact h₂₁ n hn
  have g₀₁: ∃ (p:ℕ), a n = ↑p := by
    apply h₁₁
    constructor
    . linarith
    . linarith
  have g₀₂: ∃ (q:ℕ), a (n + 2) = ↑q := by
    apply h₁₁
    constructor
    . linarith
    . linarith
  let ⟨p, _⟩ := g₀₁
  let ⟨q, _⟩ := g₀₂
  have g₁: p + 2 < q := by
    suffices g₁₁: ↑p + (2:ℝ) < ↑q
    . norm_cast at g₁₁
    . linarith
  have g₂: ↑p + (3:ℝ) ≤ ↑q := by norm_cast
  linarith


lemma imo_2023_p4_5_15
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : a n + 2 < a (n + 2)) :
  a n + 3 ≤ a (n + 2) := by
  have g₀₁: ∃ (p:ℕ), a n = ↑p := by
    apply h₁₁
    constructor
    . linarith
    . linarith
  have g₀₂: ∃ (q:ℕ), a (n + 2) = ↑q := by
    apply h₁₁
    constructor
    . linarith
    . linarith
  let ⟨p, _⟩ := g₀₁
  let ⟨q, _⟩ := g₀₂
  have g₁: p + 2 < q := by
    suffices g₁₁: ↑p + (2:ℝ) < ↑q
    . norm_cast at g₁₁
    . linarith
  have g₂: ↑p + (3:ℝ) ≤ ↑q := by norm_cast
  linarith


lemma imo_2023_p4_5_16
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021) :
  -- (g₀ : a n + 2 < a (n + 2)) :
  ∃ (p:ℕ), a n = ↑p := by
  apply h₁₁
  constructor
  . linarith
  . linarith


lemma imo_2023_p4_5_17
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (n : ℕ)
  (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : a n + 2 < a (n + 2))
  (g₀₁ : ∃ (p:ℕ), a n = ↑p) :
  a n + 3 ≤ a (n + 2) := by
  have g₀₂: ∃ (q:ℕ), a (n + 2) = ↑q := by
    apply h₁₁
    constructor
    . linarith
    . linarith
  let ⟨p, _⟩ := g₀₁
  let ⟨q, _⟩ := g₀₂
  have g₁: p + 2 < q := by
    suffices g₁₁: ↑p + (2:ℝ) < ↑q
    . norm_cast at g₁₁
    . linarith
  have g₂: ↑p + (3:ℝ) ≤ ↑q := by norm_cast
  linarith


lemma imo_2023_p4_5_18
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : a n + 2 < a (n + 2))
  (g₀₁ : ∃ (p:ℕ), a n = ↑p)
  (g₀₂ : ∃ (q:ℕ), a (n + 2) = ↑q) :
  a n + 3 ≤ a (n + 2) := by
  let ⟨p, _⟩ := g₀₁
  let ⟨q, _⟩ := g₀₂
  have g₁: p + 2 < q := by
    suffices g₁₁: ↑p + (2:ℝ) < ↑q
    . norm_cast at g₁₁
    . linarith
  have g₂: ↑p + (3:ℝ) ≤ ↑q := by norm_cast
  linarith


lemma imo_2023_p4_5_19
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : a n + 2 < a (n + 2))
  -- (g₀₁ : ∃ p, a n = ↑p)
  -- (g₀₂ : ∃ q, a (n + 2) = ↑q)
  (p : ℕ)
  (h₈ : a n = ↑p)
  (q : ℕ)
  (h₉ : a (n + 2) = ↑q) :
  a n + 3 ≤ a (n + 2) := by
  have g₁: p + 2 < q := by
    suffices g₁₁: ↑p + (2:ℝ) < ↑q
    . norm_cast at g₁₁
    . linarith
  have g₂: ↑p + (3:ℝ) ≤ ↑q := by norm_cast
  linarith


lemma imo_2023_p4_5_20
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  (g₀ : a n + 2 < a (n + 2))
  -- (g₀₁ : ∃ p, a n = ↑p)
  -- (g₀₂ : ∃ q, a (n + 2) = ↑q)
  (p : ℕ)
  (h₈ : a n = ↑p)
  (q : ℕ)
  (h₉ : a (n + 2) = ↑q) :
  p + 2 < q := by
  suffices g₁₁: ↑p + (2:ℝ) < ↑q
  . norm_cast at g₁₁
  . linarith


lemma imo_2023_p4_5_21
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (n : ℕ)
  -- (hn : 1 ≤ n ∧ n ≤ 2021)
  -- (g₀ : a n + 2 < a (n + 2))
  -- (g₀₁ : ∃ p, a n = ↑p)
  -- (g₀₂ : ∃ q, a (n + 2) = ↑q)
  (p : ℕ)
  (h₈ : a n = ↑p)
  (q : ℕ)
  (h₉ : a (n + 2) = ↑q)
  (g₁ : p + 2 < q) :
  a n + 3 ≤ a (n + 2) := by
  have g₂: ↑p + (3:ℝ) ≤ ↑q := by norm_cast
  linarith


lemma imo_2023_p4_5_22
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2)) :
  3034 ≤ a 2023 := by
  have h₃: ∀ (n:ℕ), (0 ≤ n ∧ n ≤ 1010) → a 1 + 3 * (↑(n)  + 1) ≤ a (3 + 2 * n) := by
    intros n hn
    induction' n with d hd
    · simp
      exact h₂ (1) (by norm_num)
    · rw [mul_add]
      simp
      have g₀: a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1)) := by
        refine h₂ (3 + 2 * d) ?_
        constructor
        . linarith
        . linarith
      have g₁: a 1 + 3 * (↑d + 1) + 3 ≤ a (3 + 2 * d) + 3 := by
        refine add_le_add_right ?_ (3)
        apply hd
        constructor
        . linarith
        . linarith
      refine le_trans (by linarith[g₁]) g₀
  rw [ha1] at h₃
  have h₄: (3034:ℝ)  = 1 + 3 * (↑1010 + 1) := by norm_num
  rw [h₄]
  exact h₃ (1010) (by norm_num)


lemma imo_2023_p4_5_23
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2)) :
  ∀ (n : ℕ), 0 ≤ n ∧ n ≤ 1010 → a 1 + 3 * (↑n + 1) ≤ a (3 + 2 * n) := by
  intros n hn
  induction' n with d hd
  · simp
    exact h₂ (1) (by norm_num)
  · rw [mul_add]
    simp
    have g₀: a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1)) := by
      refine h₂ (3 + 2 * d) ?_
      constructor
      . linarith
      . linarith
    have g₁: a 1 + 3 * (↑d + 1) + 3 ≤ a (3 + 2 * d) + 3 := by
      refine add_le_add_right ?_ (3)
      apply hd
      constructor
      . linarith
      . linarith
    refine le_trans (by linarith[g₁]) g₀


lemma imo_2023_p4_5_24
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2))
  (n : ℕ)
  (hn : 0 ≤ n ∧ n ≤ 1010) :
  a 1 + 3 * (↑n + 1) ≤ a (3 + 2 * n) := by
  induction' n with d hd
  · simp
    exact h₂ (1) (by norm_num)
  · rw [mul_add]
    simp
    have g₀: a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1)) := by
      refine h₂ (3 + 2 * d) ?_
      constructor
      . linarith
      . linarith
    have g₁: a 1 + 3 * (↑d + 1) + 3 ≤ a (3 + 2 * d) + 3 := by
      refine add_le_add_right ?_ (3)
      apply hd
      constructor
      . linarith
      . linarith
    refine le_trans (by linarith[g₁]) g₀


lemma imo_2023_p4_5_25
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2)) :
  -- (hn : 0 ≤ Nat.zero ∧ Nat.zero ≤ 1010) :
  a 1 + 3 * (↑Nat.zero + 1) ≤ a (3 + 2 * Nat.zero) := by
  simp
  exact h₂ (1) (by norm_num)


lemma imo_2023_p4_5_26
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2))
  (d : ℕ)
  (hd : 0 ≤ d ∧ d ≤ 1010 → a 1 + 3 * (↑d + 1) ≤ a (3 + 2 * d))
  (hn : 0 ≤ Nat.succ d ∧ Nat.succ d ≤ 1010) :
  a 1 + 3 * (↑(Nat.succ d) + 1) ≤ a (3 + 2 * Nat.succ d) := by
  rw [mul_add, Nat.succ_eq_add_one]
  simp
  have g₀: a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1)) := by
    refine h₂ (3 + 2 * d) ?_
    constructor
    . linarith
    . linarith
  have g₁: a 1 + 3 * (↑d + 1) + 3 ≤ a (3 + 2 * d) + 3 := by
    refine add_le_add_right ?_ (3)
    apply hd
    constructor
    . linarith
    . linarith
  refine le_trans (by linarith[g₁]) g₀


lemma imo_2023_p4_5_27
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2))
  (d : ℕ)
  (hd : 0 ≤ d ∧ d ≤ 1010 → a 1 + 3 * (↑d + 1) ≤ a (3 + 2 * d))
  (hn : 0 ≤ Nat.succ d ∧ Nat.succ d ≤ 1010) :
  a 1 + (3 * (↑d + 1) + 3) ≤ a (3 + 2 * (d + 1)) := by
  have g₀: a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1)) := by
    refine h₂ (3 + 2 * d) ?_
    constructor
    . linarith
    . linarith
  have g₁: a 1 + 3 * (↑d + 1) + 3 ≤ a (3 + 2 * d) + 3 := by
    refine add_le_add_right ?_ (3)
    apply hd
    constructor
    . linarith
    . linarith
  refine le_trans (by linarith[g₁]) g₀


lemma imo_2023_p4_5_28
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2))
  (d : ℕ)
  -- (hd : 0 ≤ d ∧ d ≤ 1010 → a 1 + 3 * (↑d + 1) ≤ a (3 + 2 * d))
  (hn : 0 ≤ Nat.succ d ∧ Nat.succ d ≤ 1010) :
  a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1)) := by
  refine h₂ (3 + 2 * d) ?_
  constructor
  . linarith
  . linarith


lemma imo_2023_p4_5_29
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  -- (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2))
  (d : ℕ)
  (hd : 0 ≤ d ∧ d ≤ 1010 → a 1 + 3 * (↑d + 1) ≤ a (3 + 2 * d))
  (hn : 0 ≤ Nat.succ d ∧ Nat.succ d ≤ 1010)
  (g₀ : a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1))) :
  a 1 + (3 * (↑d + 1) + 3) ≤ a (3 + 2 * (d + 1)) := by
  have g₁: a 1 + 3 * (↑d + 1) + 3 ≤ a (3 + 2 * d) + 3 := by
    refine add_le_add_right ?_ (3)
    apply hd
    constructor
    . linarith
    . linarith
  refine le_trans (by linarith[g₁]) g₀


lemma imo_2023_p4_5_30
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  -- (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2))
  (d : ℕ)
  (hd : 0 ≤ d ∧ d ≤ 1010 → a 1 + 3 * (↑d + 1) ≤ a (3 + 2 * d))
  (hn : 0 ≤ Nat.succ d ∧ Nat.succ d ≤ 1010) :
  -- (g₀ : a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1))) :
  a 1 + 3 * (↑d + 1) + 3 ≤ a (3 + 2 * d) + 3 := by
  refine add_le_add_right ?_ (3)
  apply hd
  constructor
  . linarith
  . linarith


lemma imo_2023_p4_5_31
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  -- (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2))
  (d : ℕ)
  (hd : 0 ≤ d ∧ d ≤ 1010 → a 1 + 3 * (↑d + 1) ≤ a (3 + 2 * d))
  (hn : 0 ≤ Nat.succ d ∧ Nat.succ d ≤ 1010) :
  -- (g₀ : a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1))) :
  a 1 + 3 * (↑d + 1) ≤ a (3 + 2 * d) := by
  apply hd
  constructor
  . linarith
  . linarith


lemma imo_2023_p4_5_32
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  -- (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2))
  (d : ℕ)
  -- (hd : 0 ≤ d ∧ d ≤ 1010 → a 1 + 3 * (↑d + 1) ≤ a (3 + 2 * d))
  -- (hn : 0 ≤ Nat.succ d ∧ Nat.succ d ≤ 1010)
  (g₀ : a (3 + 2 * d) + 3 ≤ a (3 + 2 * (d + 1)))
  (g₁ : a 1 + 3 * (↑d + 1) + 3 ≤ a (3 + 2 * d) + 3) :
  a 1 + (3 * (↑d + 1) + 3) ≤ a (3 + 2 * (d + 1)) := by
  exact le_trans (by linarith[g₁]) g₀


lemma imo_2023_p4_5_33
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  -- (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2))
  (h₃ : ∀ (n : ℕ), 0 ≤ n ∧ n ≤ 1010 → a 1 + 3 * (↑n + 1) ≤ a (3 + 2 * n)) :
  3034 ≤ a 2023 := by
  rw [ha1] at h₃
  have h₄: (3034:ℝ)  = 1 + 3 * (↑1010 + 1) := by norm_num
  rw [h₄]
  exact h₃ (1010) (by norm_num)


lemma imo_2023_p4_5_34
  -- (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  -- (ha1 : a 1 = 1)
  -- (h₀₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → 0 < a n)
  -- (h₁₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kn:ℕ), a n = ↑kn)
  -- (h₂₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 2 < a (n + 2))
  -- (h₂ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2021 → a n + 3 ≤ a (n + 2))
  (h₃ : ∀ (n : ℕ), 0 ≤ n ∧ n ≤ 1010 → 1 + 3 * (↑n + 1) ≤ a (3 + 2 * n))
  (h₄ : (3034:ℝ)  = 1 + 3 * (↑1010 + 1)) :
  3034 ≤ a 2023 := by
  rw [h₄]
  exact h₃ (1010) (by norm_num)








lemma imo_2023_p4_6
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
        Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) :
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz) :
  a 1 = 1 := by
  have g₀: sqrt ((Finset.sum (Finset.Ico 1 (1 + 1)) fun k => x k)
          * Finset.sum (Finset.Ico 1 (1 + 1)) fun k => 1 / x k) = 1 := by
    norm_num
    refine div_self ?_
    exact ne_of_gt (hxp 1)
  rw [← g₀]
  exact h₀ (1) (by norm_num)


lemma imo_2023_p4_6_1
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i) :
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) *
  --     Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k)) :
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz) :
  √((Finset.sum (Finset.Ico 1 (1 + 1)) fun k => x k) *
    Finset.sum (Finset.Ico 1 (1 + 1)) fun k => 1 / x k) = 1 := by
  norm_num
  refine div_self ?_
  exact ne_of_gt (hxp 1)


lemma imo_2023_p4_6_2
  (x : ℕ → ℝ)
  -- (a : ℕ → ℝ)
  (hxp : ∀ (i : ℕ), 0 < x i) :
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  -- (h₀ : ∀ (n : ℕ),
  --   1 ≤ n ∧ n ≤ 2023 →
  --     a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz) :
  x 1 * (x 1)⁻¹ = 1 := by
  refine div_self ?_
  exact ne_of_gt (hxp 1)


lemma imo_2023_p4_6_3
  (x : ℕ → ℝ)
  (a : ℕ → ℝ)
  -- (hxp : ∀ (i : ℕ), 0 < x i)
  -- (hx : ∀ (i j : ℕ), i ≠ j → x i ≠ x j)
  (h₀ : ∀ (n : ℕ),
    1 ≤ n ∧ n ≤ 2023 →
      a n = √((Finset.sum (Finset.Ico 1 (n + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (n + 1)) fun k => 1 / x k))
  -- (h₁ : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ 2023 → ∃ (kz:ℤ), a n = ↑kz)
  (g₀ : √((Finset.sum (Finset.Ico 1 (1 + 1)) fun k => x k) * Finset.sum (Finset.Ico 1 (1 + 1)) fun k => 1 / x k) = 1) :
  a 1 = 1 := by
  rw [← g₀]
  exact h₀ (1) (by norm_num)
