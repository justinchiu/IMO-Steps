import Mathlib

set_option linter.unusedVariables.analyzeTactics true

lemma imo_1985_p6_3
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y) :
  ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x := by
  intros n x hx₀
  cases' hx₀ with hn₀ hx₁
  have g₂₀: f n 1 ≤ f n x := by
    by_cases hx₂: 1 < x
    . refine le_of_lt ?_
      refine h₄ n 1 x ?_ hx₂
      exact Nat.zero_lt_of_lt hn₀
    . push_neg at hx₂
      have hx₃: x = 1 := by exact le_antisymm hx₂ hx₁
      rw [hx₃]
  have g₂₁: f 1 1 < f n 1 := by
    rw [h₀]
    refine Nat.le_induction ?_ ?_ n hn₀
    . rw [h₁ 1 1 (by norm_num), h₀]
      norm_num
    . intros m hm₀ hm₁
      rw [h₁ m 1 (by linarith)]
      refine one_lt_mul_of_lt_of_le hm₁ ?_
      norm_cast
      nth_rw 1 [← add_zero 1]
      refine add_le_add ?_ ?_
      . exact le_of_lt hm₁
      . refine one_div_nonneg.mpr ?_
        exact Nat.cast_nonneg' m
  refine lt_of_lt_of_le ?_ g₂₀
  exact (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (h₀ 1)) (f n 1))).mp g₂₁

lemma imo_1985_p6_6_3_1
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x):
   Continuous (f (Nat.succ 0)) := by
  have hn₁: f 1 = fun (x:NNReal) => (x:ℝ) := by exact (Set.eqOn_univ (f 1) fun x => ↑x).mp fun ⦃x⦄ _ => h₀ x
  rw [hn₁]
  exact NNReal.continuous_coe


lemma imo_1985_p6_6_4
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n)):
   ∀ (n : ℕ), Nat.succ 0 ≤ n → Continuous (f n) → Continuous (f (n + 1)) := by
  intros d hd₀ hd₁
  have hd₂: f (d + 1) = fun x => f d x * (f d x + 1 / ↑d) := by
    exact (Set.eqOn_univ (f (d + 1)) fun x => f d x * (f d x + 1 / ↑d)).mp fun ⦃x⦄ _ => h₁ d x hd₀
  rw [hd₂]
  refine Continuous.mul hd₁ ?_
  refine Continuous.add hd₁ ?_
  exact continuous_const


lemma imo_1985_p6_6_5
  (f : ℕ → NNReal → ℝ)
  (d : ℕ)
  (hd₁ : Continuous (f d))
  (hd₂ : f (d + 1) = fun x => f d x * (f d x + 1 / ↑d)):
   Continuous (f (d + 1)) := by
  rw [hd₂]
  refine Continuous.mul hd₁ ?_
  refine Continuous.add hd₁ ?_
  exact continuous_const




lemma imo_1985_p6_7
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₅ : ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (hmo₄ : ∀ (n : ℕ), 0 < n → Continuous (f₀ n)) :
  ∀ (n : ℕ), 0 < n → Function.Surjective (f₀ n) := by
  intros n hn₀
  refine Continuous.surjective (hmo₄ n hn₀) ?_ ?_
  . refine Monotone.tendsto_atTop_atTop ?_ ?_
    . exact StrictMono.monotone (hmo₂ n hn₀)
    . intro b
      use (b + 1)
      refine Nat.le_induction ?_ ?_ n hn₀
      . rw [hf₂ 1 (b + 1) (by linarith), h₀]
        simp
      . intros d hd₀ hd₁
        rw [hf₂ (d + 1) (b + 1) (by linarith), h₁ d (b + 1) (by linarith)]
        have hd₂: b ≤ f d (b + 1) := by
          rw [hf₂ d (b + 1) (by linarith)] at hd₁
          exact (Real.le_toNNReal_iff_coe_le (h₃ d (b + 1) hd₀)).mp hd₁
        have hd₃: 1 < (f d (b + 1) + 1 / ↑d) := by
          by_cases hd₄: 1 < d
          . refine lt_add_of_lt_of_pos ?_ ?_
            . refine h₅ d (b + 1) ?_
              constructor
              . exact hd₄
              . exact le_add_self
            . refine div_pos (by linarith) ?_
              exact Nat.cast_pos'.mpr hd₀
          . have hd₅: d = 1 := by linarith
            rw [hd₅, h₀]
            simp
            norm_cast
            refine add_pos_of_nonneg_of_pos ?_ ?_
            . exact _root_.zero_le b
            . exact zero_lt_one' NNReal
        refine NNReal.le_toNNReal_of_coe_le ?_
        nth_rw 1 [← mul_one (↑b:ℝ)]
        refine mul_le_mul hd₂ (le_of_lt hd₃) (by linarith) ?_
        exact h₃ d (b + 1) hd₀
  . refine Filter.tendsto_atBot_atBot.mpr ?_
    intro b
    use 0
    intro a ha₀
    have ha₁: a = 0 := by exact nonpos_iff_eq_zero.mp ha₀
    have ha₂: f₀ n 0 = 0 := by
      refine Nat.le_induction ?_ ?_ n hn₀
      . rw [hf₂ 1 0 (by linarith), h₀]
        exact Real.toNNReal_coe
      . intros d hd₀ hd₁
        rw [hf₂ (d + 1) 0 (by linarith), h₁ d 0 (by linarith)]
        have hd₂: 0 ≤ f d 0 := by exact h₃ d 0 hd₀
        have hd₃: f d 0 = 0 := by
          rw [hf₂ d 0 (by linarith)] at hd₁
          apply Real.toNNReal_eq_zero.mp at hd₁
          exact eq_of_le_of_le hd₁ hd₂
        rw [hd₃, zero_mul]
        exact Real.toNNReal_zero
    rw [ha₁, ha₂]
    exact _root_.zero_le b



lemma imo_1985_p6_7_1
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₅ : ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (n : ℕ)
  (hn₀ : 0 < n):
   Filter.Tendsto (f₀ n) Filter.atTop Filter.atTop := by
  refine Monotone.tendsto_atTop_atTop ?_ ?_
  . exact StrictMono.monotone (hmo₂ n hn₀)
  . intro b
    use (b + 1)
    refine Nat.le_induction ?_ ?_ n hn₀
    . rw [hf₂ 1 (b + 1) (by linarith), h₀]
      simp
    . intros d hd₀ hd₁
      rw [hf₂ (d + 1) (b + 1) (by linarith), h₁ d (b + 1) (by linarith)]
      have hd₂: b ≤ f d (b + 1) := by
        rw [hf₂ d (b + 1) (by linarith)] at hd₁
        exact (Real.le_toNNReal_iff_coe_le (h₃ d (b + 1) hd₀)).mp hd₁
      have hd₃: 1 < (f d (b + 1) + 1 / ↑d) := by
        by_cases hd₄: 1 < d
        . refine lt_add_of_lt_of_pos ?_ ?_
          . refine h₅ d (b + 1) ?_
            constructor
            . exact hd₄
            . exact le_add_self
          . refine div_pos (by linarith) ?_
            exact Nat.cast_pos'.mpr hd₀
        . have hd₅: d = 1 := by linarith
          rw [hd₅, h₀]
          simp
          norm_cast
          refine add_pos_of_nonneg_of_pos ?_ ?_
          . exact _root_.zero_le b
          . exact zero_lt_one' NNReal
      refine NNReal.le_toNNReal_of_coe_le ?_
      nth_rw 1 [← mul_one (↑b:ℝ)]
      refine mul_le_mul hd₂ (le_of_lt hd₃) (by linarith) ?_
      exact h₃ d (b + 1) hd₀


lemma imo_1985_p6_7_2
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₅ : ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n)
  (b : NNReal):
   ∃ a, b ≤ f₀ n a := by
  use (b + 1)
  refine Nat.le_induction ?_ ?_ n hn₀
  . rw [hf₂ 1 (b + 1) (by linarith), h₀]
    simp
  . intros d hd₀ hd₁
    rw [hf₂ (d + 1) (b + 1) (by linarith), h₁ d (b + 1) (by linarith)]
    have hd₂: b ≤ f d (b + 1) := by
      rw [hf₂ d (b + 1) (by linarith)] at hd₁
      exact (Real.le_toNNReal_iff_coe_le (h₃ d (b + 1) hd₀)).mp hd₁
    have hd₃: 1 < (f d (b + 1) + 1 / ↑d) := by
      by_cases hd₄: 1 < d
      . refine lt_add_of_lt_of_pos ?_ ?_
        . refine h₅ d (b + 1) ?_
          constructor
          . exact hd₄
          . exact le_add_self
        . refine div_pos (by linarith) ?_
          exact Nat.cast_pos'.mpr hd₀
      . have hd₅: d = 1 := by linarith
        rw [hd₅, h₀]
        simp
        norm_cast
        refine add_pos_of_nonneg_of_pos ?_ ?_
        . exact _root_.zero_le b
        . exact zero_lt_one' NNReal
    refine NNReal.le_toNNReal_of_coe_le ?_
    nth_rw 1 [← mul_one (↑b:ℝ)]
    refine mul_le_mul hd₂ (le_of_lt hd₃) (by linarith) ?_
    exact h₃ d (b + 1) hd₀


lemma imo_1985_p6_7_3
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₅ : ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n)
  (b : NNReal):
   b ≤ f₀ n (b + 1) := by
  refine Nat.le_induction ?_ ?_ n hn₀
  . rw [hf₂ 1 (b + 1) (by linarith), h₀]
    simp
  . intros d hd₀ hd₁
    rw [hf₂ (d + 1) (b + 1) (by linarith), h₁ d (b + 1) (by linarith)]
    have hd₂: b ≤ f d (b + 1) := by
      rw [hf₂ d (b + 1) (by linarith)] at hd₁
      exact (Real.le_toNNReal_iff_coe_le (h₃ d (b + 1) hd₀)).mp hd₁
    have hd₃: 1 < (f d (b + 1) + 1 / ↑d) := by
      by_cases hd₄: 1 < d
      . refine lt_add_of_lt_of_pos ?_ ?_
        . refine h₅ d (b + 1) ?_
          constructor
          . exact hd₄
          . exact le_add_self
        . refine div_pos (by linarith) ?_
          exact Nat.cast_pos'.mpr hd₀
      . have hd₅: d = 1 := by linarith
        rw [hd₅, h₀]
        simp
        norm_cast
        refine add_pos_of_nonneg_of_pos ?_ ?_
        . exact _root_.zero_le b
        . exact zero_lt_one' NNReal
    refine NNReal.le_toNNReal_of_coe_le ?_
    nth_rw 1 [← mul_one (↑b:ℝ)]
    refine mul_le_mul hd₂ (le_of_lt hd₃) (by linarith) ?_
    exact h₃ d (b + 1) hd₀

lemma imo_1985_p6_7_4
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (b : NNReal):
   b ≤ f₀ (Nat.succ 0) (b + 1) := by
  rw [hf₂ 1 (b + 1) (by linarith), h₀]
  simp


lemma imo_1985_p6_7_5
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₅ : ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (b : NNReal):
   ∀ (n : ℕ), Nat.succ 0 ≤ n → b ≤ f₀ n (b + 1) → b ≤ f₀ (n + 1) (b + 1) := by
  intros d hd₀ hd₁
  rw [hf₂ (d + 1) (b + 1) (by linarith), h₁ d (b + 1) (by linarith)]
  have hd₂: b ≤ f d (b + 1) := by
    rw [hf₂ d (b + 1) (by linarith)] at hd₁
    exact (Real.le_toNNReal_iff_coe_le (h₃ d (b + 1) hd₀)).mp hd₁
  have hd₃: 1 < (f d (b + 1) + 1 / ↑d) := by
    by_cases hd₄: 1 < d
    . refine lt_add_of_lt_of_pos ?_ ?_
      . refine h₅ d (b + 1) ?_
        constructor
        . exact hd₄
        . exact le_add_self
      . refine div_pos (by linarith) ?_
        exact Nat.cast_pos'.mpr hd₀
    . have hd₅: d = 1 := by linarith
      rw [hd₅, h₀]
      simp
      norm_cast
      refine add_pos_of_nonneg_of_pos ?_ ?_
      . exact _root_.zero_le b
      . exact zero_lt_one' NNReal
  refine NNReal.le_toNNReal_of_coe_le ?_
  nth_rw 1 [← mul_one (↑b:ℝ)]
  refine mul_le_mul hd₂ (le_of_lt hd₃) (by linarith) ?_
  exact h₃ d (b + 1) hd₀


lemma imo_1985_p6_7_6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₅ : ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (b : NNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d)
  (hd₁ : b ≤ f₀ d (b + 1)):
   b ≤ (f d (b + 1) * (f d (b + 1) + 1 / ↑d)).toNNReal := by
  have hd₂: b ≤ f d (b + 1) := by
    rw [hf₂ d (b + 1) (by linarith)] at hd₁
    exact (Real.le_toNNReal_iff_coe_le (h₃ d (b + 1) hd₀)).mp hd₁
  have hd₃: 1 < (f d (b + 1) + 1 / ↑d) := by
    by_cases hd₄: 1 < d
    . refine lt_add_of_lt_of_pos ?_ ?_
      . refine h₅ d (b + 1) ?_
        constructor
        . exact hd₄
        . exact le_add_self
      . refine div_pos (by linarith) ?_
        exact Nat.cast_pos'.mpr hd₀
    . have hd₅: d = 1 := by linarith
      rw [hd₅, h₀]
      simp
      norm_cast
      refine add_pos_of_nonneg_of_pos ?_ ?_
      . exact _root_.zero_le b
      . exact zero_lt_one' NNReal
  refine NNReal.le_toNNReal_of_coe_le ?_
  nth_rw 1 [← mul_one (↑b:ℝ)]
  refine mul_le_mul hd₂ (le_of_lt hd₃) (by linarith) ?_
  exact h₃ d (b + 1) hd₀

lemma imo_1985_p6_7_7
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (b : NNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d)
  (hd₁ : b ≤ f₀ d (b + 1)):
   ↑b ≤ f d (b + 1) := by
  rw [hf₂ d (b + 1) (by linarith)] at hd₁
  exact (Real.le_toNNReal_iff_coe_le (h₃ d (b + 1) hd₀)).mp hd₁


lemma imo_1985_p6_7_8
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₅ : ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x)
  (b : NNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d)
  (hd₂ : ↑b ≤ f d (b + 1)):
   b ≤ (f d (b + 1) * (f d (b + 1) + 1 / ↑d)).toNNReal := by
  have hd₃: 1 < (f d (b + 1) + 1 / ↑d) := by
    by_cases hd₄: 1 < d
    . refine lt_add_of_lt_of_pos ?_ ?_
      . refine h₅ d (b + 1) ?_
        constructor
        . exact hd₄
        . exact le_add_self
      . refine div_pos (by linarith) ?_
        exact Nat.cast_pos'.mpr hd₀
    . have hd₅: d = 1 := by linarith
      rw [hd₅, h₀]
      simp
      norm_cast
      refine add_pos_of_nonneg_of_pos ?_ ?_
      . exact _root_.zero_le b
      . exact zero_lt_one' NNReal
  refine NNReal.le_toNNReal_of_coe_le ?_
  nth_rw 1 [← mul_one (↑b:ℝ)]
  refine mul_le_mul hd₂ (le_of_lt hd₃) (by linarith) ?_
  exact h₃ d (b + 1) hd₀

lemma imo_1985_p6_7_9
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₅ : ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x)
  (b : NNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d):
   1 < f d (b + 1) + 1 / ↑d := by
  by_cases hd₄: 1 < d
  . refine lt_add_of_lt_of_pos ?_ ?_
    . refine h₅ d (b + 1) ?_
      constructor
      . exact hd₄
      . exact le_add_self
    . refine div_pos (by linarith) ?_
      exact Nat.cast_pos'.mpr hd₀
  . have hd₅: d = 1 := by linarith
    rw [hd₅, h₀]
    simp
    norm_cast
    refine add_pos_of_nonneg_of_pos ?_ ?_
    . exact _root_.zero_le b
    . exact zero_lt_one' NNReal


lemma imo_1985_p6_7_10
  (f : ℕ → NNReal → ℝ)
  (h₅ : ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x)
  (b : NNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d)
  (hd₄ : 1 < d):
   1 < f d (b + 1) + 1 / ↑d := by
  refine lt_add_of_lt_of_pos ?_ ?_
  . refine h₅ d (b + 1) ?_
    constructor
    . exact hd₄
    . exact le_add_self
  . refine div_pos (by linarith) ?_
    exact Nat.cast_pos'.mpr hd₀


lemma imo_1985_p6_7_11
  (f : ℕ → NNReal → ℝ)
  (h₅ : ∀ (n : ℕ) (x : NNReal), 1 < n ∧ 1 ≤ x → 1 < f n x)
  (b : NNReal)
  (d : ℕ)
  (hd₄ : 1 < d):
   1 < f d (b + 1) := by
  refine h₅ d (b + 1) ?_
  constructor
  . exact hd₄
  . exact le_add_self


lemma imo_1985_p6_7_12
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d) :
   0 < (1:ℝ) / ↑d := by
  refine div_pos (by linarith) ?_
  exact Nat.cast_pos'.mpr hd₀


lemma imo_1985_p6_7_13
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (b : NNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d)
  (hd₄ : ¬1 < d):
   1 < f d (b + 1) + 1 / ↑d := by
  have hd₅: d = 1 := by linarith
  rw [hd₅, h₀]
  simp
  norm_cast
  refine add_pos_of_nonneg_of_pos ?_ ?_
  . exact _root_.zero_le b
  . exact zero_lt_one' NNReal


lemma imo_1985_p6_7_14
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (b : NNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d)
  (hd₄ : ¬1 < d)
  (hd₅ : 1 < f d (b + 1) + 1 / ↑d):
   0 < b + 1 := by
  have hd₆: d = 1 := by linarith
  rw [hd₆, h₀] at hd₅
  simp at hd₅
  norm_cast at hd₅


lemma imo_1985_p6_7_15
  (b : NNReal):
   0 < b + 1 := by
  refine add_pos_of_nonneg_of_pos ?_ ?_
  . exact _root_.zero_le b
  . exact zero_lt_one' NNReal



lemma imo_1985_p6_7_16
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (b : NNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d)
  (hd₂ : ↑b ≤ f d (b + 1))
  (hd₃ : 1 < f d (b + 1) + 1 / ↑d):
   b ≤ (f d (b + 1) * (f d (b + 1) + 1 / ↑d)).toNNReal := by
  refine NNReal.le_toNNReal_of_coe_le ?_
  nth_rw 1 [← mul_one (↑b:ℝ)]
  refine mul_le_mul hd₂ (le_of_lt hd₃) (by linarith) ?_
  exact h₃ d (b + 1) hd₀


lemma imo_1985_p6_7_17
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (b : NNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d)
  (hd₂ : ↑b ≤ f d (b + 1))
  (hd₃ : 1 < f d (b + 1) + 1 / ↑d):
   ↑b ≤ f d (b + 1) * (f d (b + 1) + 1 / ↑d) := by
  nth_rw 1 [← mul_one (↑b:ℝ)]
  refine mul_le_mul hd₂ (le_of_lt hd₃) (by linarith) ?_
  exact h₃ d (b + 1) hd₀


lemma imo_1985_p6_7_18
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (b : NNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d)
  (hd₂ : ↑b ≤ f d (b + 1))
  (hd₃ : 1 < f d (b + 1) + 1 / ↑d):
   ↑b * 1 ≤ f d (b + 1) * (f d (b + 1) + 1 / ↑d) := by
  refine mul_le_mul hd₂ (le_of_lt hd₃) (by linarith) ?_
  exact h₃ d (b + 1) hd₀


lemma imo_1985_p6_7_19
  (f : ℕ → NNReal → ℝ)
  (b : NNReal)
  (d : ℕ)
  (hd₄ : ↑b * 1 ≤ f d (b + 1) * (f d (b + 1) + 1 / ↑d)):
   b ≤ (f d (b + 1) * (f d (b + 1) + 1 / ↑d)).toNNReal := by
  refine NNReal.le_toNNReal_of_coe_le ?_
  nth_rw 1 [← mul_one (↑b:ℝ)]
  exact hd₄


lemma imo_1985_p6_7_20
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n):
   Filter.Tendsto (f₀ n) Filter.atBot Filter.atBot := by
  refine Filter.tendsto_atBot_atBot.mpr ?_
  intro b
  use 0
  intro a ha₀
  have ha₁: a = 0 := by exact nonpos_iff_eq_zero.mp ha₀
  have ha₂: f₀ n 0 = 0 := by
    refine Nat.le_induction ?_ ?_ n hn₀
    . rw [hf₂ 1 0 (by linarith), h₀]
      exact Real.toNNReal_coe
    . intros d hd₀ hd₁
      rw [hf₂ (d + 1) 0 (by linarith), h₁ d 0 (by linarith)]
      have hd₂: 0 ≤ f d 0 := by exact h₃ d 0 hd₀
      have hd₃: f d 0 = 0 := by
        rw [hf₂ d 0 (by linarith)] at hd₁
        apply Real.toNNReal_eq_zero.mp at hd₁
        exact eq_of_le_of_le hd₁ hd₂
      rw [hd₃, zero_mul]
      exact Real.toNNReal_zero
  rw [ha₁, ha₂]
  exact _root_.zero_le b


lemma imo_1985_p6_7_21
  (f₀ : ℕ → NNReal → NNReal)
  (n : ℕ)
  (b a : NNReal)
  (ha₁ : a = 0)
  (ha₂ : f₀ n 0 = 0):
   f₀ n a ≤ b := by
  rw [ha₁, ha₂]
  exact _root_.zero_le b

lemma imo_1985_p6_7_22
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n):
   ∀ (b : NNReal), ∃ i, ∀ a ≤ i, f₀ n a ≤ b := by
  intro b
  use 0
  intro a ha₀
  have ha₁: a = 0 := by exact nonpos_iff_eq_zero.mp ha₀
  have ha₂: f₀ n 0 = 0 := by
    refine Nat.le_induction ?_ ?_ n hn₀
    . rw [hf₂ 1 0 (by linarith), h₀]
      exact Real.toNNReal_coe
    . intros d hd₀ hd₁
      rw [hf₂ (d + 1) 0 (by linarith), h₁ d 0 (by linarith)]
      have hd₂: 0 ≤ f d 0 := by exact h₃ d 0 hd₀
      have hd₃: f d 0 = 0 := by
        rw [hf₂ d 0 (by linarith)] at hd₁
        apply Real.toNNReal_eq_zero.mp at hd₁
        exact eq_of_le_of_le hd₁ hd₂
      rw [hd₃, zero_mul]
      exact Real.toNNReal_zero
  rw [ha₁, ha₂]
  exact _root_.zero_le b

lemma imo_1985_p6_7_23
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n)
  (b : NNReal):
   ∃ i, ∀ a ≤ i, f₀ n a ≤ b := by
  use 0
  intro a ha₀
  have ha₁: a = 0 := by exact nonpos_iff_eq_zero.mp ha₀
  have ha₂: f₀ n 0 = 0 := by
    refine Nat.le_induction ?_ ?_ n hn₀
    . rw [hf₂ 1 0 (by linarith), h₀]
      exact Real.toNNReal_coe
    . intros d hd₀ hd₁
      rw [hf₂ (d + 1) 0 (by linarith), h₁ d 0 (by linarith)]
      have hd₂: 0 ≤ f d 0 := by exact h₃ d 0 hd₀
      have hd₃: f d 0 = 0 := by
        rw [hf₂ d 0 (by linarith)] at hd₁
        apply Real.toNNReal_eq_zero.mp at hd₁
        exact eq_of_le_of_le hd₁ hd₂
      rw [hd₃, zero_mul]
      exact Real.toNNReal_zero
  rw [ha₁, ha₂]
  exact _root_.zero_le b

lemma imo_1985_p6_7_24
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n)
  (b a : NNReal)
  (ha₀ : a ≤ 0):
   f₀ n a ≤ b := by
  have ha₁: a = 0 := by exact nonpos_iff_eq_zero.mp ha₀
  have ha₂: f₀ n 0 = 0 := by
    refine Nat.le_induction ?_ ?_ n hn₀
    . rw [hf₂ 1 0 (by linarith), h₀]
      exact Real.toNNReal_coe
    . intros d hd₀ hd₁
      rw [hf₂ (d + 1) 0 (by linarith), h₁ d 0 (by linarith)]
      have hd₂: 0 ≤ f d 0 := by exact h₃ d 0 hd₀
      have hd₃: f d 0 = 0 := by
        rw [hf₂ d 0 (by linarith)] at hd₁
        apply Real.toNNReal_eq_zero.mp at hd₁
        exact eq_of_le_of_le hd₁ hd₂
      rw [hd₃, zero_mul]
      exact Real.toNNReal_zero
  rw [ha₁, ha₂]
  exact _root_.zero_le b

lemma imo_1985_p6_7_25
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n)
  (b a : NNReal)
  (ha₁ : a = 0):
   f₀ n a ≤ b := by
  have ha₂: f₀ n 0 = 0 := by
    refine Nat.le_induction ?_ ?_ n hn₀
    . rw [hf₂ 1 0 (by linarith), h₀]
      exact Real.toNNReal_coe
    . intros d hd₀ hd₁
      rw [hf₂ (d + 1) 0 (by linarith), h₁ d 0 (by linarith)]
      have hd₂: 0 ≤ f d 0 := by exact h₃ d 0 hd₀
      have hd₃: f d 0 = 0 := by
        rw [hf₂ d 0 (by linarith)] at hd₁
        apply Real.toNNReal_eq_zero.mp at hd₁
        exact eq_of_le_of_le hd₁ hd₂
      rw [hd₃, zero_mul]
      exact Real.toNNReal_zero
  rw [ha₁, ha₂]
  exact _root_.zero_le b

lemma imo_1985_p6_7_26
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n):
   f₀ n 0 = 0 := by
  refine Nat.le_induction ?_ ?_ n hn₀
  . rw [hf₂ 1 0 (by linarith), h₀]
    exact Real.toNNReal_coe
  . intros d hd₀ hd₁
    rw [hf₂ (d + 1) 0 (by linarith), h₁ d 0 (by linarith)]
    have hd₂: 0 ≤ f d 0 := by exact h₃ d 0 hd₀
    have hd₃: f d 0 = 0 := by
      rw [hf₂ d 0 (by linarith)] at hd₁
      apply Real.toNNReal_eq_zero.mp at hd₁
      exact eq_of_le_of_le hd₁ hd₂
    rw [hd₃, zero_mul]
    exact Real.toNNReal_zero


lemma imo_1985_p6_7_27
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal):
   f₀ (Nat.succ 0) 0 = 0 := by
  rw [hf₂ 1 0 (by linarith), h₀]
  exact Real.toNNReal_coe


lemma imo_1985_p6_7_28
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal):
   ∀ (n : ℕ), Nat.succ 0 ≤ n → f₀ n 0 = 0 → f₀ (n + 1) 0 = 0 := by
  intros d hd₀ hd₁
  rw [hf₂ (d + 1) 0 (by linarith), h₁ d 0 (by linarith)]
  have hd₂: 0 ≤ f d 0 := by exact h₃ d 0 hd₀
  have hd₃: f d 0 = 0 := by
    rw [hf₂ d 0 (by linarith)] at hd₁
    apply Real.toNNReal_eq_zero.mp at hd₁
    exact eq_of_le_of_le hd₁ hd₂
  rw [hd₃, zero_mul]
  exact Real.toNNReal_zero

lemma imo_1985_p6_7_29
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d)
  (hd₁ : f₀ d 0 = 0):
   (f d 0 * (f d 0 + 1 / ↑d)).toNNReal = 0 := by
  have hd₂: 0 ≤ f d 0 := by exact h₃ d 0 hd₀
  have hd₃: f d 0 = 0 := by
    rw [hf₂ d 0 (by linarith)] at hd₁
    apply Real.toNNReal_eq_zero.mp at hd₁
    exact eq_of_le_of_le hd₁ hd₂
  rw [hd₃, zero_mul]
  exact Real.toNNReal_zero

lemma imo_1985_p6_7_30
  (f : ℕ → NNReal → ℝ)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d)
  (hd₁ : f₀ d 0 = 0)
  (hd₂ : 0 ≤ f d 0):
   (f d 0 * (f d 0 + 1 / ↑d)).toNNReal = 0 := by
  have hd₃: f d 0 = 0 := by
    rw [hf₂ d 0 (by linarith)] at hd₁
    apply Real.toNNReal_eq_zero.mp at hd₁
    exact eq_of_le_of_le hd₁ hd₂
  rw [hd₃, zero_mul]
  exact Real.toNNReal_zero


lemma imo_1985_p6_7_31
  (f : ℕ → NNReal → ℝ)
  (d : ℕ)
  (hd₃ : f d 0 = 0):
   (f d 0 * (f d 0 + 1 / ↑d)).toNNReal = 0 := by
  rw [hd₃, zero_mul]
  exact Real.toNNReal_zero


lemma imo_1985_p6_7_32
  (f : ℕ → NNReal → ℝ)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (d : ℕ)
  (hd₀ : Nat.succ 0 ≤ d)
  (hd₁ : f₀ d 0 = 0)
  (hd₂ : 0 ≤ f d 0):
   f d 0 = 0 := by
  rw [hf₂ d 0 (by linarith)] at hd₁
  apply Real.toNNReal_eq_zero.mp at hd₁
  exact eq_of_le_of_le hd₁ hd₂


lemma imo_1985_p6_8
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hsn₁ : ∀ (n : ↑sn), ↑n ∈ sn ∧ 0 < n.1)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n) :
  ∀ (n : ↑sn), fb n < 1 := by
  intros n
  have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
  let z := fb n
  have hz₀: z = fb n := by rfl
  rw [← hz₀]
  by_contra! hc₀
  have hc₁: 1 ≤ f n z := by
    by_cases hn₁: 1 < (n:ℕ)
    . refine le_of_lt ?_
      refine imo_1985_p6_3 f h₀ h₁ ?_ (↑n) z ?_
      . exact fun n x y a a_1 ↦ hmo₀ n a a_1
      . exact ⟨hn₁, hc₀⟩
    . have hn₂: (n:ℕ) = 1 := by linarith
      rw [hn₂, h₀]
      exact hc₀
  have hz₁: f₀ n z = 1 - 1 / n := by
    exact hfb₁ n
  have hz₃: f n z = 1 - 1 / n := by
    rw [hf₂ n z hn₀] at hz₁
    by_cases hn₁: 1 < (n:ℕ)
    . have hz₂: 1 - 1 / (n:NNReal) ≠ 0 := by
        have g₀: (n:NNReal) ≠ 0 := by
          norm_cast
          linarith
        nth_rw 1 [← div_self g₀, ← NNReal.sub_div]
        refine div_ne_zero ?_ g₀
        norm_cast
        exact Nat.sub_ne_zero_iff_lt.mpr hn₁
      apply (Real.toNNReal_eq_iff_eq_coe hz₂).mp at hz₁
      rw [hz₁]
      exact Eq.symm ((fun {r} {p:NNReal} hp => (Real.toNNReal_eq_iff_eq_coe hp).mp) hz₂ (hmo₁ n hn₀ rfl))
    . have hn₂: (n:ℕ) = 1 := by linarith
      rw [hn₂, h₀] at hz₁
      simp at hz₁
      rw [hn₂, h₀, hz₁]
      simp
  rw [hz₃] at hc₁
  have hz₄: 0 < 1 / (n:ℝ) := by
    refine div_pos (by linarith) ?_
    exact Nat.cast_pos'.mpr hn₀
  linarith


lemma imo_1985_p6_8_1
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (n : ↑sn)
  (hn₀ : 0 < n.1):
   fb n < 1 := by
  let z := fb n
  have hz₀: z = fb n := by rfl
  rw [← hz₀]
  by_contra! hc₀
  have hc₁: 1 ≤ f n z := by
    by_cases hn₁: 1 < (n:ℕ)
    . refine le_of_lt ?_
      refine imo_1985_p6_3 f h₀ h₁ ?_ (↑n) z ?_
      . exact fun n x y a a_1 => hmo₀ n a a_1
      . exact ⟨hn₁, hc₀⟩
    . push_neg at hn₁
      have hn₂: n.1 = 1 := by linarith
      rw [hn₂, h₀]
      exact hc₀
  have hz₁: f₀ n z = 1 - 1 / n := by
    exact hfb₁ n
  have hz₃: f n z = 1 - 1 / n := by
    rw [hf₂ n z hn₀] at hz₁
    by_cases hn₁: 1 < (n:ℕ)
    . have hz₂: 1 - 1 / (n:NNReal) ≠ 0 := by
        have g₀: (n:NNReal) ≠ 0 := by
          norm_cast
          linarith
        nth_rw 1 [← div_self g₀, ← NNReal.sub_div]
        refine div_ne_zero ?_ g₀
        norm_cast
        exact Nat.sub_ne_zero_iff_lt.mpr hn₁
      apply (Real.toNNReal_eq_iff_eq_coe hz₂).mp at hz₁
      rw [hz₁]
      exact Eq.symm ((fun {r} {p:NNReal} hp => (Real.toNNReal_eq_iff_eq_coe hp).mp) hz₂ (hmo₁ n hn₀ rfl))
    . have hn₂: (n:ℕ) = 1 := by linarith
      rw [hn₂, h₀] at hz₁
      simp at hz₁
      rw [hn₂, h₀, hz₁]
      simp
  rw [hz₃] at hc₁
  have hz₄: 0 < 1 / (n:ℝ) := by
    refine div_pos (by linarith) ?_
    exact Nat.cast_pos'.mpr hn₀
  linarith

lemma imo_1985_p6_8_2
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (z : NNReal)
  (hz₀ : z = fb n)
  (hc₀ : 1 ≤ z):
   False := by
  have hc₁: 1 ≤ f n z := by
    by_cases hn₁: 1 < (n:ℕ)
    . refine le_of_lt ?_
      refine imo_1985_p6_3 f h₀ h₁ ?_ (↑n) z ?_
      . exact fun n x y a a_1 => hmo₀ n a a_1
      . exact ⟨hn₁, hc₀⟩
    . have hn₂: (n:ℕ) = 1 := by linarith
      rw [hn₂, h₀]
      exact hc₀
  have hz₁: f₀ n z = 1 - 1 / n := by
    rw [hz₀]
    exact hfb₁ n
  have hz₃: f n z = 1 - 1 / n := by
    rw [hf₂ n z hn₀] at hz₁
    by_cases hn₁: 1 < (n:ℕ)
    . have hz₂: 1 - 1 / (n:NNReal) ≠ 0 := by
        have g₀: (n:NNReal) ≠ 0 := by
          norm_cast
          linarith
        nth_rw 1 [← div_self g₀, ← NNReal.sub_div]
        refine div_ne_zero ?_ g₀
        norm_cast
        exact Nat.sub_ne_zero_iff_lt.mpr hn₁
      apply (Real.toNNReal_eq_iff_eq_coe hz₂).mp at hz₁
      rw [hz₁]
      exact Eq.symm ((fun {r} {p:NNReal} hp => (Real.toNNReal_eq_iff_eq_coe hp).mp) hz₂ (hmo₁ n hn₀ rfl))
    . have hn₂: (n:ℕ) = 1 := by linarith
      rw [hn₂, h₀] at hz₁
      simp at hz₁
      rw [hn₂, h₀, hz₁]
      simp
  rw [hz₃] at hc₁
  have hz₄: 0 < 1 / (n:ℝ) := by
    refine div_pos (by linarith) ?_
    exact Nat.cast_pos'.mpr hn₀
  linarith


lemma imo_1985_p6_8_3
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (z : NNReal)
  (hc₀ : 1 ≤ z):
   1 ≤ f (↑n) z := by
  by_cases hn₁: 1 < (n:ℕ)
  . refine le_of_lt ?_
    refine imo_1985_p6_3 f h₀ h₁ ?_ (↑n) z ?_
    . exact fun n x y a a_1 => hmo₀ n a a_1
    . exact ⟨hn₁, hc₀⟩
  . have hn₂: (n:ℕ) = 1 := by linarith
    rw [hn₂, h₀]
    exact hc₀

lemma imo_1985_p6_8_4
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (sn : Set ℕ)
  (n : ↑sn)
  (z : NNReal)
  (hc₀ : 1 ≤ z)
  (hn₁ : 1 < n.1):
   1 ≤ f (↑n) z := by
  refine le_of_lt ?_
  refine imo_1985_p6_3 f h₀ h₁ ?_ (↑n) z ?_
  . exact fun n x y a a_1 => hmo₀ n a a_1
  . exact ⟨hn₁, hc₀⟩

lemma imo_1985_p6_8_5
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (sn : Set ℕ)
  (n : ↑sn)
  (z : NNReal)
  (hc₀ : 1 ≤ z)
  (hn₁ : 1 < n.1):
   1 < f (↑n) z := by
  refine imo_1985_p6_3 f h₀ h₁ ?_ (↑n) z ?_
  . exact fun n x y a a_1 => hmo₀ n a a_1
  . exact ⟨hn₁, hc₀⟩

lemma imo_1985_p6_8_6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (z : NNReal)
  (hc₀ : 1 ≤ z)
  (hn₁ : ¬1 < n.1):
   1 ≤ f (↑n) z := by
  have hn₂: (n:ℕ) = 1 := by linarith
  rw [hn₂, h₀]
  exact hc₀

lemma imo_1985_p6_8_7
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (z : NNReal)
  (hz₀ : z = fb n)
  (hc₁ : 1 ≤ f (↑n) z):
   False := by
  have hz₁: f₀ n z = 1 - 1 / n := by
    rw [hz₀]
    exact hfb₁ n
  have hz₃: f n z = 1 - 1 / n := by
    rw [hf₂ n z hn₀] at hz₁
    by_cases hn₁: 1 < (n:ℕ)
    . have hz₂: 1 - 1 / (n:NNReal) ≠ 0 := by
        have g₀: (n:NNReal) ≠ 0 := by
          norm_cast
          linarith
        nth_rw 1 [← div_self g₀, ← NNReal.sub_div]
        refine div_ne_zero ?_ g₀
        norm_cast
        exact Nat.sub_ne_zero_iff_lt.mpr hn₁
      apply (Real.toNNReal_eq_iff_eq_coe hz₂).mp at hz₁
      rw [hz₁]
      exact Eq.symm ((fun {r} {p:NNReal} hp => (Real.toNNReal_eq_iff_eq_coe hp).mp) hz₂ (hmo₁ n hn₀ rfl))
    . have hn₂: (n:ℕ) = 1 := by linarith
      rw [hn₂, h₀] at hz₁
      simp at hz₁
      rw [hn₂, h₀, hz₁]
      simp
  rw [hz₃] at hc₁
  have hz₄: 0 < 1 / (n:ℝ) := by
    refine div_pos (by linarith) ?_
    exact Nat.cast_pos'.mpr hn₀
  linarith

lemma imo_1985_p6_8_8
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (z : NNReal)
  (hc₁ : 1 ≤ f (↑n) z)
  (hz₁ : f₀ (↑n) z = 1 - 1 / ↑↑n):
   False := by
  have hz₃: f n z = 1 - 1 / n := by
    rw [hf₂ n z hn₀] at hz₁
    by_cases hn₁: 1 < (n:ℕ)
    . have hz₂: 1 - 1 / (n:NNReal) ≠ 0 := by
        have g₀: (n:NNReal) ≠ 0 := by
          norm_cast
          linarith
        nth_rw 1 [← div_self g₀, ← NNReal.sub_div]
        refine div_ne_zero ?_ g₀
        norm_cast
        exact Nat.sub_ne_zero_iff_lt.mpr hn₁
      apply (Real.toNNReal_eq_iff_eq_coe hz₂).mp at hz₁
      rw [hz₁]
      exact Eq.symm ((fun {r} {p:NNReal} hp => (Real.toNNReal_eq_iff_eq_coe hp).mp) hz₂ (hmo₁ n hn₀ rfl))
    . have hn₂: (n:ℕ) = 1 := by linarith
      rw [hn₂, h₀] at hz₁
      simp at hz₁
      rw [hn₂, h₀, hz₁]
      simp
  rw [hz₃] at hc₁
  have hz₄: 0 < 1 / (n:ℝ) := by
    refine div_pos (by linarith) ?_
    exact Nat.cast_pos'.mpr hn₀
  linarith

lemma imo_1985_p6_8_9
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (z : NNReal)
  (hz₁ : f₀ (↑n) z = 1 - 1 / ↑↑n):
   f (↑n) z = 1 - 1 / ↑↑n := by
  rw [hf₂ n z hn₀] at hz₁
  by_cases hn₁: 1 < (n:ℕ)
  . have hz₂: 1 - 1 / (n:NNReal) ≠ 0 := by
      have g₀: (n:NNReal) ≠ 0 := by
        norm_cast
        linarith
      nth_rw 1 [← div_self g₀, ← NNReal.sub_div]
      refine div_ne_zero ?_ g₀
      norm_cast
      exact Nat.sub_ne_zero_iff_lt.mpr hn₁
    apply (Real.toNNReal_eq_iff_eq_coe hz₂).mp at hz₁
    rw [hz₁]
    exact Eq.symm ((fun {r} {p:NNReal} hp => (Real.toNNReal_eq_iff_eq_coe hp).mp) hz₂ (hmo₁ n hn₀ rfl))
  . have hn₂: (n:ℕ) = 1 := by linarith
    rw [hn₂, h₀] at hz₁
    simp at hz₁
    rw [hn₂, h₀, hz₁]
    simp

lemma imo_1985_p6_8_10
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (z : NNReal)
  (hz₁ : (f (↑n) z).toNNReal = 1 - 1 / ↑↑n):
   f (↑n) z = 1 - 1 / ↑↑n := by
  by_cases hn₁: 1 < (n:ℕ)
  . have hz₂: 1 - 1 / (n:NNReal) ≠ 0 := by
      have g₀: (n:NNReal) ≠ 0 := by
        norm_cast
        linarith
      nth_rw 1 [← div_self g₀, ← NNReal.sub_div]
      refine div_ne_zero ?_ g₀
      norm_cast
      exact Nat.sub_ne_zero_iff_lt.mpr hn₁
    apply (Real.toNNReal_eq_iff_eq_coe hz₂).mp at hz₁
    rw [hz₁]
    exact Eq.symm ((fun {r} {p:NNReal} hp => (Real.toNNReal_eq_iff_eq_coe hp).mp) hz₂ (hmo₁ n hn₀ rfl))
  . have hn₂: (n:ℕ) = 1 := by linarith
    rw [hn₂, h₀] at hz₁
    simp at hz₁
    rw [hn₂, h₀, hz₁]
    simp

lemma imo_1985_p6_8_11
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (z : NNReal)
  (hz₁ : (f (↑n) z).toNNReal = 1 - 1 / ↑↑n)
  (hn₁ : 1 < n.1):
   f (↑n) z = 1 - 1 / ↑↑n := by
  have hz₂: 1 - 1 / (n:NNReal) ≠ 0 := by
    have g₀: (n:NNReal) ≠ 0 := by
      norm_cast
      linarith
    nth_rw 1 [← div_self g₀, ← NNReal.sub_div]
    refine div_ne_zero ?_ g₀
    norm_cast
    exact Nat.sub_ne_zero_iff_lt.mpr hn₁
  apply (Real.toNNReal_eq_iff_eq_coe hz₂).mp at hz₁
  rw [hz₁]
  exact Eq.symm ((fun {r} {p:NNReal} hp => (Real.toNNReal_eq_iff_eq_coe hp).mp) hz₂ (hmo₁ n hn₀ rfl))


lemma imo_1985_p6_8_12
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₁ : 1 < n.1):
   1 - (1:NNReal) / n.1 ≠ 0 := by
  have g₀: ↑(n.1) ≠ (0:NNReal) := by
    norm_cast
    linarith
  nth_rw 1 [← div_self g₀, ← NNReal.sub_div]
  refine div_ne_zero ?_ g₀
  norm_cast
  exact Nat.sub_ne_zero_iff_lt.mpr hn₁


lemma imo_1985_p6_8_13
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₁ : 1 < n.1)
  (g₀ : ↑(n.1) ≠ (0:NNReal)):
   1 - (1:NNReal) / ↑↑n ≠ 0 := by
  nth_rw 1 [← div_self g₀, ← NNReal.sub_div]
  refine div_ne_zero ?_ g₀
  norm_cast
  exact Nat.sub_ne_zero_iff_lt.mpr hn₁


lemma imo_1985_p6_1
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n)) :
  ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x := by
  intros n x hp
  cases' hp with hn₀ hx₀
  by_cases hn₁: 1 < n
  . refine Nat.le_induction ?_ ?_ n hn₁
    . rw [h₁ 1 x (by norm_num)]
      rw [h₀ x]
      refine mul_pos hx₀ ?_
      refine add_pos hx₀ (by norm_num)
    . intros m hm₀ hm₁
      rw [h₁ m x (by linarith)]
      refine mul_pos hm₁ ?_
      refine add_pos hm₁ ?_
      refine one_div_pos.mpr ?_
      norm_cast
      exact Nat.zero_lt_of_lt hm₀
  . interval_cases n
    rw [h₀ x]
    exact hx₀


lemma imo_1985_p6_1_1
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (n : ℕ)
  (x : NNReal)
  (hx₀ : 0 < x)
  (hn₁ : 1 < n):
   0 < f n x := by
  refine Nat.le_induction ?_ ?_ n hn₁
  . rw [h₁ 1 x (by norm_num)]
    rw [h₀ x]
    refine mul_pos hx₀ ?_
    refine add_pos hx₀ (by norm_num)
  . intros m hm₀ hm₁
    rw [h₁ m x (by linarith)]
    refine mul_pos hm₁ ?_
    refine add_pos hm₁ ?_
    refine one_div_pos.mpr ?_
    norm_cast
    exact Nat.zero_lt_of_lt hm₀



lemma imo_1985_p6_1_2
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (n : ℕ)
  (x : NNReal)
  (hn₀ : 0 < n)
  (hx₀ : 0 < x)
  (hn₁ : ¬1 < n):
   0 < f n x := by
  interval_cases n
  rw [h₀ x]
  exact hx₀



lemma imo_1985_p6_1_3
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (x : NNReal)
  (hx₀ : 0 < x):
   0 < f (Nat.succ 1) x := by
  rw [h₁ 1 x (by norm_num)]
  rw [h₀ x]
  refine mul_pos hx₀ ?_
  refine add_pos hx₀ (by norm_num)


lemma imo_1985_p6_1_4
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (x : NNReal)
  (hx₀ : 0 < x):
   0 < f 1 x * (f 1 x + 1 / ↑1) := by
  rw [h₀ x]
  refine mul_pos hx₀ ?_
  refine add_pos hx₀ (by norm_num)


lemma imo_1985_p6_1_5
  (x : NNReal)
  (hx₀ : 0 < x):
   0 < ↑x * (↑x + 1 / ↑1) := by
  refine mul_pos hx₀ ?_
  refine add_pos hx₀ (by norm_num)

lemma imo_1985_p6_1_6
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (x : NNReal):
   ∀ (n : ℕ), Nat.succ 1 ≤ n → 0 < f n x → 0 < f (n + 1) x := by
  intros m hm₀ hm₁
  rw [h₁ m x (by linarith)]
  refine mul_pos hm₁ ?_
  refine add_pos hm₁ ?_
  refine one_div_pos.mpr ?_
  norm_cast
  exact Nat.zero_lt_of_lt hm₀


lemma imo_1985_p6_1_7
  (f : ℕ → NNReal → ℝ)
  (x : NNReal)
  (m : ℕ)
  (hm₀ : Nat.succ 1 ≤ m)
  (hm₁ : 0 < f m x):
   0 < f m x + 1 / ↑m := by
  have m_nonzero : m ≠ 0 :=
    fun h => by { rw [h] at hm₀; norm_num at hm₀ }
  have m_pos_nat : 0 < m := Nat.pos_of_ne_zero m_nonzero
  have m_pos : 0 < (↑m : ℝ) := Nat.cast_pos.mpr m_pos_nat
  have one_div_pos : 0 < (1 : ℝ) / (↑m : ℝ) := div_pos zero_lt_one m_pos
  exact add_pos hm₁ one_div_pos


lemma imo_1985_p6_1_8
  (f : ℕ → NNReal → ℝ)
  (x : NNReal)
  (m : ℕ)
  (hm₀ : Nat.succ 1 ≤ m)
  (hm₁ : 0 < f m x):
   0 < f m x + 1 / ↑m := by
  refine add_pos hm₁ ?_
  refine one_div_pos.mpr ?_
  norm_cast
  exact Nat.zero_lt_of_lt hm₀



lemma imo_1985_p6_2_1
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (n : ℕ)
  (x y : NNReal)
  (hxy : x < y)
  (hn₁ : 1 < n):
   f n x < f n y := by
  refine Nat.le_induction ?_ ?_ n hn₁
  . rw [h₁ 1 x (by norm_num)]
    rw [h₁ 1 y (by norm_num)]
    norm_num
    refine mul_lt_mul ?_ ?_ ?_ ?_
    . rw [h₀ x, h₀ y]
      exact hxy
    . refine _root_.add_le_add ?_ (by norm_num)
      rw [h₀ x, h₀ y]
      exact le_of_lt hxy
    . refine add_pos_of_nonneg_of_pos ?_ (by linarith)
      rw [h₀ x]
      exact NNReal.zero_le_coe
    . refine le_of_lt ?_
      refine h₂ 1 y ?_
      norm_num
      exact pos_of_gt hxy
  . intros m hm₀ hm₁
    rw [h₁ m x (by linarith)]
    rw [h₁ m y (by linarith)]
    refine mul_lt_mul hm₁ ?_ ?_ ?_
    . refine _root_.add_le_add ?_ (by norm_num)
      refine le_of_lt hm₁
    . refine add_pos_of_nonneg_of_pos ?_ ?_
      . exact h₃ m x (by linarith)
      . refine one_div_pos.mpr ?_
        norm_cast
        exact Nat.zero_lt_of_lt hm₀
    . refine le_of_lt ?_
      refine h₂ m y ?_
      constructor
      . exact Nat.zero_lt_of_lt hm₀
      . exact pos_of_gt hxy


lemma imo_1985_p6_2_2
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (n : ℕ)
  (x y : NNReal)
  (hn : 0 < n)
  (hxy : x < y)
  (hn₁ : ¬1 < n):
   f n x < f n y := by
  interval_cases n
  rw [h₀ x, h₀ y]
  exact hxy


lemma imo_1985_p6_2_3
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (x y : NNReal)
  (hxy : x < y):
   f (Nat.succ 1) x < f (Nat.succ 1) y := by
  rw [h₁ 1 x (by norm_num)]
  rw [h₁ 1 y (by norm_num)]
  norm_num
  refine mul_lt_mul ?_ ?_ ?_ ?_
  . rw [h₀ x, h₀ y]
    exact hxy
  . refine _root_.add_le_add ?_ (by norm_num)
    rw [h₀ x, h₀ y]
    exact le_of_lt hxy
  . refine add_pos_of_nonneg_of_pos ?_ (by linarith)
    rw [h₀ x]
    exact NNReal.zero_le_coe
  . refine le_of_lt ?_
    refine h₂ 1 y ?_
    norm_num
    exact pos_of_gt hxy


lemma imo_1985_p6_2_4
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (x y : NNReal)
  (hxy : x < y):
   ∀ (n : ℕ), Nat.succ 1 ≤ n → f n x < f n y → f (n + 1) x < f (n + 1) y := by
  intros m hm₀ hm₁
  rw [h₁ m x (by linarith)]
  rw [h₁ m y (by linarith)]
  refine mul_lt_mul hm₁ ?_ ?_ ?_
  . refine _root_.add_le_add ?_ (by norm_num)
    refine le_of_lt hm₁
  . refine add_pos_of_nonneg_of_pos ?_ ?_
    . exact h₃ m x (by linarith)
    . refine one_div_pos.mpr ?_
      norm_cast
      exact Nat.zero_lt_of_lt hm₀
  . refine le_of_lt ?_
    refine h₂ m y ?_
    constructor
    . exact Nat.zero_lt_of_lt hm₀
    . exact pos_of_gt hxy


lemma imo_1985_p6_2_5
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (x y : NNReal)
  (hxy : x < y):
   f 1 x * (f 1 x + 1 / ↑1) < f 1 y * (f 1 y + 1 / ↑1) := by
  norm_num
  refine mul_lt_mul ?_ ?_ ?_ ?_
  . rw [h₀ x, h₀ y]
    exact hxy
  . refine _root_.add_le_add ?_ (by norm_num)
    rw [h₀ x, h₀ y]
    exact le_of_lt hxy
  . refine add_pos_of_nonneg_of_pos ?_ (by linarith)
    rw [h₀ x]
    exact NNReal.zero_le_coe
  . refine le_of_lt ?_
    refine h₂ 1 y ?_
    norm_num
    exact pos_of_gt hxy


lemma imo_1985_p6_2_6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (x y : NNReal)
  (hxy : x < y):
   f 1 x + 1 ≤ f 1 y + 1 := by
  refine _root_.add_le_add ?_ (by norm_num)
  rw [h₀ x, h₀ y]
  exact le_of_lt hxy


lemma imo_1985_p6_2_7
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (x : NNReal):
   0 < f 1 x + 1 := by
  refine add_pos_of_nonneg_of_pos ?_ (by linarith)
  rw [h₀ x]
  exact NNReal.zero_le_coe

lemma imo_1985_p6_2_8
  (f : ℕ → NNReal → ℝ)
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (x y : NNReal)
  (hxy : x < y):
   0 ≤ f 1 y := by
  refine le_of_lt ?_
  refine h₂ 1 y ?_
  norm_num
  exact pos_of_gt hxy


lemma imo_1985_p6_2_9
  (f : ℕ → NNReal → ℝ)
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (x y : NNReal)
  (hxy : x < y)
  (m : ℕ)
  (hm₀ : Nat.succ 1 ≤ m)
  (hm₁ : f m x < f m y):
   f m x * (f m x + 1 / ↑m) < f m y * (f m y + 1 / ↑m) := by
  refine mul_lt_mul hm₁ ?_ ?_ ?_
  . refine _root_.add_le_add ?_ (by norm_num)
    refine le_of_lt hm₁
  . refine add_pos_of_nonneg_of_pos ?_ ?_
    . exact h₃ m x (by linarith)
    . refine one_div_pos.mpr ?_
      norm_cast
      exact Nat.zero_lt_of_lt hm₀
  . refine le_of_lt ?_
    refine h₂ m y ?_
    constructor
    . exact Nat.zero_lt_of_lt hm₀
    . exact pos_of_gt hxy


lemma imo_1985_p6_2_10
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (x : NNReal)
  (m : ℕ)
  (hm₀ : Nat.succ 1 ≤ m):
   0 < f m x + 1 / ↑m := by
  refine add_pos_of_nonneg_of_pos ?_ ?_
  . exact h₃ m x (by linarith)
  . refine one_div_pos.mpr ?_
    norm_cast
    exact Nat.zero_lt_of_lt hm₀


lemma imo_1985_p6_2_11
  (f : ℕ → NNReal → ℝ)
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (x y : NNReal)
  (hxy : x < y)
  (m : ℕ)
  (hm₀ : Nat.succ 1 ≤ m):
   0 ≤ f m y := by
  refine le_of_lt ?_
  refine h₂ m y ?_
  constructor
  . exact Nat.zero_lt_of_lt hm₀
  . exact pos_of_gt hxy


lemma imo_1985_p6_3_1
  (f : ℕ → NNReal → ℝ)
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y)
  (n : ℕ)
  (x : NNReal)
  (hn₀ : 1 < n)
  (hx₁ : 1 ≤ x):
   f n 1 ≤ f n x := by
  by_cases hx₂: 1 < x
  . refine le_of_lt ?_
    refine h₄ n 1 x ?_ hx₂
    exact Nat.zero_lt_of_lt hn₀
  . push_neg at hx₂
    have hx₃: x = 1 := by exact le_antisymm hx₂ hx₁
    rw [hx₃]


lemma imo_1985_p6_3_2
  (f : ℕ → NNReal → ℝ)
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y)
  (n : ℕ)
  (x : NNReal)
  (hn₀ : 1 < n)
  (hx₂ : 1 < x):
   f n 1 ≤ f n x := by
  refine le_of_lt ?_
  refine h₄ n 1 x ?_ hx₂
  exact Nat.zero_lt_of_lt hn₀


lemma imo_1985_p6_3_3
  (f : ℕ → NNReal → ℝ)
  (n : ℕ)
  (x : NNReal)
  (hx₁ : 1 ≤ x)
  (hx₂ : ¬1 < x):
   f n 1 ≤ f n x := by
  push_neg at hx₂
  have hx₃: x = 1 := by exact le_antisymm hx₂ hx₁
  rw [hx₃]


lemma imo_1985_p6_3_4
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (n : ℕ)
  (x : NNReal)
  (hn₀ : 1 < n)
  (g₂₀ : f n 1 ≤ f n x):
   1 < f n x := by
  have g₂₁: f 1 1 < f n 1 := by
    rw [h₀]
    refine Nat.le_induction ?_ ?_ n hn₀
    . rw [h₁ 1 1 (by norm_num), h₀]
      norm_num
    . intros m hm₀ hm₁
      rw [h₁ m 1 (by linarith)]
      refine one_lt_mul_of_lt_of_le hm₁ ?_
      nth_rw 1 [← add_zero 1]
      refine add_le_add ?_ ?_
      . exact le_of_lt hm₁
      . refine one_div_nonneg.mpr ?_
        exact Nat.cast_nonneg' m
  refine lt_of_lt_of_le ?_ g₂₀
  exact (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (h₀ 1)) (f n 1))).mp g₂₁


lemma imo_1985_p6_3_5
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (n : ℕ)
  (x : NNReal)
  (g₂₀ : f n 1 ≤ f n x)
  (g₂₁ : f 1 1 < f n 1):
   1 < f n x := by
  refine lt_of_lt_of_le ?_ g₂₀
  exact (lt_iff_lt_of_cmp_eq_cmp (congrFun (congrArg cmp (h₀ 1)) (f n 1))).mp g₂₁



lemma imo_1985_p6_3_6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (n : ℕ)
  (hn₀ : 1 < n):
   f 1 1 < f n 1 := by
  rw [h₀]
  refine Nat.le_induction ?_ ?_ n hn₀
  . rw [h₁ 1 1 (by norm_num), h₀]
    norm_num
  . intros m hm₀ hm₁
    rw [h₁ m 1 (by linarith)]
    refine one_lt_mul_of_lt_of_le hm₁ ?_
    nth_rw 1 [← add_zero 1]
    refine add_le_add ?_ ?_
    . exact le_of_lt hm₁
    . refine one_div_nonneg.mpr ?_
      exact Nat.cast_nonneg' m


lemma imo_1985_p6_3_7
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n)):
   ∀ (n : ℕ), Nat.succ 1 ≤ n → ↑1 < f n 1 → ↑1 < f (n + 1) 1 := by
  intros m hm₀ hm₁
  rw [h₁ m 1 (by linarith)]
  refine one_lt_mul_of_lt_of_le hm₁ ?_
  nth_rw 1 [← add_zero 1]
  refine add_le_add ?_ ?_
  . exact le_of_lt hm₁
  . refine one_div_nonneg.mpr ?_
    exact Nat.cast_nonneg' m


lemma imo_1985_p6_3_8
  (f : ℕ → NNReal → ℝ)
  (m : ℕ)
  (hm₁ : ↑1 < f m 1):
   ↑1 < f m 1 * (f m 1 + 1 / ↑m) := by
  refine one_lt_mul_of_lt_of_le hm₁ ?_
  nth_rw 1 [← add_zero 1]
  refine add_le_add ?_ ?_
  . exact le_of_lt hm₁
  . refine one_div_nonneg.mpr ?_
    exact Nat.cast_nonneg' m


lemma imo_1985_p6_3_9
  (f : ℕ → NNReal → ℝ)
  (m : ℕ)
  (hm₁ : ↑1 < f m 1):
   1 ≤ f m 1 + 1 / ↑m := by
  nth_rw 1 [← add_zero 1]
  refine add_le_add ?_ ?_
  . exact le_of_lt hm₁
  . refine one_div_nonneg.mpr ?_
    exact Nat.cast_nonneg' m


lemma imo_1985_p6_4_1
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n):
   Monotone (f₀ n) := by
  refine monotone_iff_forall_lt.mpr ?_
  intros a b hab
  refine le_of_lt ?_
  rw [hf₀]
  exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n a hn₀)).mpr (h₄ n a b hn₀ hab)

lemma imo_1985_p6_4_2
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n):
   ∀ ⦃a b : NNReal⦄, a < b → f₀ n a ≤ f₀ n b := by
  intros a b hab
  refine le_of_lt ?_
  rw [hf₀]
  exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n a hn₀)).mpr (h₄ n a b hn₀ hab)


lemma imo_1985_p6_4_3
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n)
  (a b : NNReal)
  (hab : a < b):
   f₀ n a < f₀ n b := by
  rw [hf₀]
  exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n a hn₀)).mpr (h₄ n a b hn₀ hab)

lemma imo_1985_p6_4_4
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n):
   Function.Injective (f₀ n) := by
  intros p q hpq
  contrapose! hpq
  apply lt_or_gt_of_ne at hpq
  cases' hpq with hpq hpq
  . refine ne_of_lt ?_
    rw [hf₀]
    exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n p hn₀)).mpr (h₄ n p q hn₀ hpq)
  . symm
    refine ne_of_lt ?_
    rw [hf₀]
    exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n q hn₀)).mpr (h₄ n q p hn₀ hpq)



lemma imo_1985_p6_4_5
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n)
  (p q : NNReal)
  (hpq : p ≠ q):
   f₀ n p ≠ f₀ n q := by
  apply lt_or_gt_of_ne at hpq
  cases' hpq with hpq hpq
  . refine ne_of_lt ?_
    rw [hf₀]
    exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n p hn₀)).mpr (h₄ n p q hn₀ hpq)
  . symm
    refine ne_of_lt ?_
    rw [hf₀]
    exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n q hn₀)).mpr (h₄ n q p hn₀ hpq)

lemma imo_1985_p6_4_6
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n)
  (p q : NNReal)
  (hpq : p < q):
   f₀ n p ≠ f₀ n q := by
  refine ne_of_lt ?_
  rw [hf₀]
  exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n p hn₀)).mpr (h₄ n p q hn₀ hpq)


lemma imo_1985_p6_4_7
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n)
  (p q : NNReal)
  (hpq : p > q):
   f₀ n p ≠ f₀ n q := by
  symm
  refine ne_of_lt ?_
  rw [hf₀]
  exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n q hn₀)).mpr (h₄ n q p hn₀ hpq)


lemma imo_1985_p6_5_1
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (n : ℕ)
  (x y : NNReal)
  (hn₀ : 0 < n)
  (hn₁ : f₀ n x = y):
   fi n y = x := by
  have hf₃: ∀ n y, fi n y = Function.invFun (f₀ n) y := by
    exact fun n y => congrFun (congrFun hfi n) y
  rw [← hn₁, hf₃]
  have hmo₃: ∀ n, 0 < n → Function.Injective (f₀ n) := by
    exact fun n a => StrictMono.injective (hmo₂ n a)
  have hn₂: (Function.invFun (f₀ n)) ∘ (f₀ n) = id := by exact Function.invFun_comp (hmo₃ n hn₀)
  rw [Function.comp_def (Function.invFun (f₀ n)) (f₀ n)] at hn₂
  have hn₃: (fun x => Function.invFun (f₀ n) (f₀ n x)) x = id x := by exact Eq.symm (NNReal.eq (congrArg NNReal.toReal (congrFun (id (Eq.symm hn₂)) x)))
  exact hmo₁ n hn₀ (congrArg (f n) hn₃)

lemma imo_1985_p6_5_2
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (n : ℕ)
  (x y : NNReal)
  (hn₀ : 0 < n)
  (hn₁ : f₀ n x = y)
  (hf₃ : ∀ (n : ℕ) (y : NNReal), fi n y = Function.invFun (f₀ n) y):
   fi n y = x := by
  rw [← hn₁, hf₃]
  have hmo₃: ∀ n, 0 < n → Function.Injective (f₀ n) := by
    exact fun n a => StrictMono.injective (hmo₂ n a)
  have hn₂: (Function.invFun (f₀ n)) ∘ (f₀ n) = id := by exact Function.invFun_comp (hmo₃ n hn₀)
  rw [Function.comp_def (Function.invFun (f₀ n)) (f₀ n)] at hn₂
  have hn₃: (fun x => Function.invFun (f₀ n) (f₀ n x)) x = id x := by exact Eq.symm (NNReal.eq (congrArg NNReal.toReal (congrFun (id (Eq.symm hn₂)) x)))
  exact hmo₁ n hn₀ (congrArg (f n) hn₃)

lemma imo_1985_p6_5_3
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (n : ℕ)
  (x : NNReal)
  (hn₀ : 0 < n):
   Function.invFun (f₀ n) (f₀ n x) = x := by
  have hmo₃: ∀ n, 0 < n → Function.Injective (f₀ n) := by
    exact fun n a => StrictMono.injective (hmo₂ n a)
  have hn₂: (Function.invFun (f₀ n)) ∘ (f₀ n) = id := by exact Function.invFun_comp (hmo₃ n hn₀)
  rw [Function.comp_def (Function.invFun (f₀ n)) (f₀ n)] at hn₂
  have hn₃: (fun x => Function.invFun (f₀ n) (f₀ n x)) x = id x := by exact Eq.symm (NNReal.eq (congrArg NNReal.toReal (congrFun (id (Eq.symm hn₂)) x)))
  exact hmo₁ n hn₀ (congrArg (f n) hn₃)

lemma imo_1985_p6_5_4
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (n : ℕ)
  (x : NNReal)
  (hn₀ : 0 < n)
  (hmo₃ : ∀ (n : ℕ), 0 < n → Function.Injective (f₀ n)):
   Function.invFun (f₀ n) (f₀ n x) = x := by
  have hn₂: (Function.invFun (f₀ n)) ∘ (f₀ n) = id := by exact Function.invFun_comp (hmo₃ n hn₀)
  rw [Function.comp_def (Function.invFun (f₀ n)) (f₀ n)] at hn₂
  have hn₃: (fun x => Function.invFun (f₀ n) (f₀ n x)) x = id x := by exact Eq.symm (NNReal.eq (congrArg NNReal.toReal (congrFun (id (Eq.symm hn₂)) x)))
  exact hmo₁ n hn₀ (congrArg (f n) hn₃)


lemma imo_1985_p6_5_5
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (n : ℕ)
  (x : NNReal)
  (hn₀ : 0 < n)
  (hn₂ : Function.invFun (f₀ n) ∘ f₀ n = id):
   Function.invFun (f₀ n) (f₀ n x) = x := by
  rw [Function.comp_def (Function.invFun (f₀ n)) (f₀ n)] at hn₂
  have hn₃: (fun x => Function.invFun (f₀ n) (f₀ n x)) x = id x := by exact Eq.symm (NNReal.eq (congrArg NNReal.toReal (congrFun (id (Eq.symm hn₂)) x)))
  exact hmo₁ n hn₀ (congrArg (f n) hn₃)

lemma imo_1985_p6_5_6
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (n : ℕ)
  (x : NNReal)
  (hn₀ : 0 < n)
  (hn₂ : (fun x ↦ Function.invFun (f₀ n) (f₀ n x)) = id):
   Function.invFun (f₀ n) (f₀ n x) = x := by
  have hn₃: (fun x => Function.invFun (f₀ n) (f₀ n x)) x = id x := by exact Eq.symm (NNReal.eq (congrArg NNReal.toReal (congrFun (id (Eq.symm hn₂)) x)))
  exact hmo₁ n hn₀ (congrArg (f n) hn₃)


lemma imo_1985_p6_6_1
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (n : ℕ)
  (hn₀ : 0 < n):
   Continuous ((fun n x ↦ (f n x).toNNReal) n) := by
  refine Continuous.comp' ?_ ?_
  . exact continuous_real_toNNReal
  . refine Nat.le_induction ?_ ?_ n hn₀
    . have hn₁: f 1 = fun (x:NNReal) => (x:ℝ) := by exact (Set.eqOn_univ (f 1) fun x => ↑x).mp fun ⦃x⦄ _ => h₀ x
      rw [hn₁]
      exact NNReal.continuous_coe
    . intros d hd₀ hd₁
      have hd₂: f (d + 1) = fun x => f d x * (f d x + 1 / ↑d) := by
        exact (Set.eqOn_univ (f (d + 1)) fun x => f d x * (f d x + 1 / ↑d)).mp fun ⦃x⦄ _ => h₁ d x hd₀
      rw [hd₂]
      refine Continuous.mul hd₁ ?_
      refine Continuous.add hd₁ ?_
      exact continuous_const


lemma imo_1985_p6_6_2
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (n : ℕ)
  (hn₀ : 0 < n):
   Continuous (f n) := by
  refine Nat.le_induction ?_ ?_ n hn₀
  . have hn₁: f 1 = fun (x:NNReal) => (x:ℝ) := by exact (Set.eqOn_univ (f 1) fun x => ↑x).mp fun ⦃x⦄ _ => h₀ x
    rw [hn₁]
    exact NNReal.continuous_coe
  . intros d hd₀ hd₁
    have hd₂: f (d + 1) = fun x => f d x * (f d x + 1 / ↑d) := by
      exact (Set.eqOn_univ (f (d + 1)) fun x => f d x * (f d x + 1 / ↑d)).mp fun ⦃x⦄ _ => h₁ d x hd₀
    rw [hd₂]
    refine Continuous.mul hd₁ ?_
    refine Continuous.add hd₁ ?_
    exact continuous_const


lemma imo_1985_p6_6_3
  (f : ℕ → NNReal → ℝ)
  (f₀ : ℕ → NNReal → NNReal := fun n x => (f n x).toNNReal)
  (hf₀ : f₀ = fun n x => (f n x).toNNReal)
  (hmo₄:  ∀ (n : ℕ), 0 < n → Continuous (f n)):
   ∀ (n : ℕ), 0 < n → Continuous (f₀ n) := by
  intros n hn₀
  rw [hf₀]
  refine Continuous.comp' ?_ ?_
  . exact continuous_real_toNNReal
  . exact hmo₄ n hn₀


lemma imo_1985_p6_bonus_1
  (f₀ : ℕ → NNReal → NNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n => Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n)) :
  ∀ (n : ℕ), 0 < n → Function.Bijective (f₀ n) := by
  intros n hn₀
  refine Function.bijective_iff_has_inverse.mpr ?_
  use fi n
  constructor
  . rw [hfi]
    refine Function.leftInverse_invFun ?_
    exact StrictMono.injective (hmo₂ n hn₀)
  . exact hmo₇ n hn₀


lemma imo_1985_p6_bonus_1_1
  (f₀ : ℕ → NNReal → NNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (n : ℕ)
  (hn₀ : 0 < n):
   ∃ g, Function.LeftInverse g (f₀ n) ∧ Function.RightInverse g (f₀ n) := by
  use fi n
  constructor
  . rw [hfi]
    refine Function.leftInverse_invFun ?_
    exact StrictMono.injective (hmo₂ n hn₀)
  . exact hmo₇ n hn₀


lemma imo_1985_p6_bonus_1_2
  (f₀ : ℕ → NNReal → NNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (n : ℕ)
  (hn₀ : 0 < n):
   Function.LeftInverse (fi n) (f₀ n) ∧ Function.RightInverse (fi n) (f₀ n) := by
  constructor
  . rw [hfi]
    refine Function.leftInverse_invFun ?_
    exact StrictMono.injective (hmo₂ n hn₀)
  . exact hmo₇ n hn₀


lemma imo_1985_p6_bonus_1_3
  (f₀ : ℕ → NNReal → NNReal)
  (fi : ℕ → NNReal → NNReal)
  (h₁ : ∀ n, Function.LeftInverse (fi n) (f₀ n) ∧ Function.RightInverse (fi n) (f₀ n)):
   ∀ (n : ℕ), 0 < n → Function.Bijective (f₀ n) := by
  intros n _
  refine Function.bijective_iff_has_inverse.mpr ?_
  use fi n
  exact h₁ n




lemma imo_1985_p6_bonus_2
  (f₀ : ℕ → NNReal → NNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n => Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n)) :
  ∀ (n : ℕ), 0 < n → ∃! c, f₀ n c = 1 := by
  intros n hn₀
  refine Function.Bijective.existsUnique ?_ 1
  refine Function.bijective_iff_has_inverse.mpr ?_
  use fi n
  constructor
  . rw [hfi]
    refine Function.leftInverse_invFun ?_
    exact StrictMono.injective (hmo₂ n hn₀)
  . exact hmo₇ n hn₀


lemma imo_1985_p6_bonus_3
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb : ↑sn → NNReal)
  (hfb₃ : StrictMono fb)
  (sb  : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x => ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br) :
  br ∉ sbr := by
  rw [hsbr]
  by_contra! hc₀
  apply (Set.mem_image fr sb br).mp at hc₀
  obtain ⟨x, hx₀, hx₁⟩ := hc₀
  rw [hsb₀] at hx₀
  apply Set.mem_range.mp at hx₀
  obtain ⟨nx, hnx₀⟩ := hx₀
  have hnx₁: (nx.1 + (1:ℕ)) ∈ sn := by
    let t : ℕ := nx.1 + 1
    have ht₀: t = nx.1 + 1 := by rfl
    rw [← ht₀, hsn]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_left 1 ↑nx
  let ny : ↑sn := ⟨(nx.1 + 1), hnx₁⟩
  have hx₂: fb nx < fb ny := by
    refine hfb₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    exact lt_add_one (↑nx:ℕ)
  have hx₃: fb ny ∈ sb := by
    rw [hsb₀]
    exact Set.mem_range_self ny
  have hx₄: fb ny ≤ br := by
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    rw [hfr]
    use (fb ny)
  have hc₁: br < fb ny := by
    rw [ ← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false br).mp ?_
  exact lt_of_lt_of_le hc₁ hx₄




lemma imo_1985_p6_bonus_3_1
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb : ↑sn → NNReal)
  (hfb₃ : StrictMono fb)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (hc₀ : br ∈ fr '' sb):
   False := by
  apply (Set.mem_image fr sb br).mp at hc₀
  obtain ⟨x, hx₀, hx₁⟩ := hc₀
  rw [hsb₀] at hx₀
  apply Set.mem_range.mp at hx₀
  obtain ⟨nx, hnx₀⟩ := hx₀
  have hnx₁: (nx.1 + (1:ℕ)) ∈ sn := by
    let t : ℕ := nx.1 + 1
    have ht₀: t = nx.1 + 1 := by rfl
    rw [← ht₀, hsn]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_left 1 ↑nx
  let ny : ↑sn := ⟨(nx.1 + 1), hnx₁⟩
  have hx₂: fb nx < fb ny := by
    refine hfb₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    exact lt_add_one (↑nx:ℕ)
  have hx₃: fb ny ∈ sb := by
    rw [hsb₀]
    exact Set.mem_range_self ny
  have hx₄: fb ny ≤ br := by
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    rw [hfr]
    use (fb ny)
  have hc₁: br < fb ny := by
    rw [ ← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false br).mp ?_
  exact lt_of_lt_of_le hc₁ hx₄

lemma imo_1985_p6_bonus_3_2
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb : ↑sn → NNReal)
  (hfb₃ : StrictMono fb)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (x : NNReal)
  (hx₀ : x ∈ sb)
  (hx₁ : fr x = br):
   False := by
  rw [hsb₀] at hx₀
  apply Set.mem_range.mp at hx₀
  obtain ⟨nx, hnx₀⟩ := hx₀
  have hnx₁: (nx.1 + (1:ℕ)) ∈ sn := by
    let t : ℕ := nx.1 + 1
    have ht₀: t = nx.1 + 1 := by rfl
    rw [← ht₀, hsn]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_left 1 ↑nx
  let ny : ↑sn := ⟨(nx.1 + 1), hnx₁⟩
  have hx₂: fb nx < fb ny := by
    refine hfb₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    exact lt_add_one (↑nx:ℕ)
  have hx₃: fb ny ∈ sb := by
    rw [hsb₀]
    exact Set.mem_range_self ny
  have hx₄: fb ny ≤ br := by
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    rw [hfr]
    use (fb ny)
  have hc₁: br < fb ny := by
    rw [ ← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false br).mp ?_
  exact lt_of_lt_of_le hc₁ hx₄


lemma imo_1985_p6_bonus_3_3
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb : ↑sn → NNReal)
  (hfb₃ : StrictMono fb)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (x : NNReal)
  (hx₁ : fr x = br)
  (nx : ↑sn)
  (hnx₀ : fb nx = x):
   False := by
  have hnx₁: (nx.1 + (1:ℕ)) ∈ sn := by
    let t : ℕ := nx.1 + 1
    have ht₀: t = nx.1 + 1 := by rfl
    rw [← ht₀, hsn]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_left 1 ↑nx
  let ny : ↑sn := ⟨(nx.1 + 1), hnx₁⟩
  have hx₂: fb nx < fb ny := by
    refine hfb₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    exact lt_add_one (↑nx:ℕ)
  have hx₃: fb ny ∈ sb := by
    rw [hsb₀]
    exact Set.mem_range_self ny
  have hx₄: fb ny ≤ br := by
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    rw [hfr]
    use (fb ny)
  have hc₁: br < fb ny := by
    rw [ ← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false br).mp ?_
  exact lt_of_lt_of_le hc₁ hx₄

lemma imo_1985_p6_bonus_3_4
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (nx : ↑sn):
  nx.1 + 1 ∈ sn := by
  let t : ℕ := nx.1 + 1
  have ht₀: t = nx.1 + 1 := by rfl
  rw [← ht₀, hsn]
  refine Set.mem_Ici.mpr ?_
  exact Nat.le_add_left 1 ↑nx

lemma imo_1985_p6_bonus_3_5
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₃ : StrictMono fb)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (x : NNReal)
  (hx₁ : fr x = br)
  (nx : ↑sn)
  (hnx₀ : fb nx = x)
  (hnx₁ : nx.1 + 1 ∈ sn)
  (ny : ↑sn)
  (hny : ny = ⟨↑nx + 1, hnx₁⟩) :
   False := by
  have hx₂: fb nx < fb ny := by
    refine hfb₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hny]
    exact lt_add_one (↑nx:ℕ)
  have hx₃: fb ny ∈ sb := by
    rw [hsb₀]
    exact Set.mem_range_self ny
  have hx₄: fb ny ≤ br := by
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    rw [hfr]
    use (fb ny)
  have hc₁: br < fb ny := by
    rw [ ← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false br).mp ?_
  exact lt_of_lt_of_le hc₁ hx₄


lemma imo_1985_p6_bonus_3_6
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₃ : StrictMono fb)
  (nx : ↑sn)
  (hnx₁ : nx.1 + 1 ∈ sn)
  (ny : ↑sn)
  (hny : ny = ⟨↑nx + 1, hnx₁⟩):
   fb nx < fb ny := by
  refine hfb₃ ?_
  refine Subtype.mk_lt_mk.mpr ?_
  rw [hny]
  exact lt_add_one (↑nx:ℕ)

lemma imo_1985_p6_bonus_3_7
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (x : NNReal)
  (hx₁ : fr x = br)
  (nx : ↑sn)
  (hnx₀ : fb nx = x)
  (ny : ↑sn)
  (hx₂ : fb nx < fb ny):
   False := by
  have hx₃: fb ny ∈ sb := by
    rw [hsb₀]
    exact Set.mem_range_self ny
  have hx₄: fb ny ≤ br := by
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    rw [hfr]
    use (fb ny)
  have hc₁: br < fb ny := by
    rw [ ← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false br).mp ?_
  exact lt_of_lt_of_le hc₁ hx₄

lemma imo_1985_p6_bonus_3_8
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (x : NNReal)
  (hx₁ : fr x = br)
  (nx : ↑sn)
  (hnx₀ : fb nx = x)
  (ny : ↑sn)
  (hx₂ : fb nx < fb ny)
  (hx₃ : fb ny ∈ sb):
   False := by
  have hx₄: fb ny ≤ br := by
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    rw [hfr]
    use (fb ny)
  have hc₁: br < fb ny := by
    rw [ ← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false br).mp ?_
  exact lt_of_lt_of_le hc₁ hx₄

lemma imo_1985_p6_bonus_3_9
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (ny : ↑sn)
  (hx₃ : fb ny ∈ sb):
   ↑(fb ny) ≤ br := by
  refine hbr₃ _ ?_
  rw [hsbr]
  refine (Set.mem_image fr sb _).mpr ?_
  rw [hfr]
  use (fb ny)

lemma imo_1985_p6_bonus_3_10
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (ny : ↑sn)
  (hx₃ : fb ny ∈ sb):
   ↑(fb ny) ∈ fr '' sb := by
  refine (Set.mem_image fr sb _).mpr ?_
  rw [hfr]
  use (fb ny)

lemma imo_1985_p6_bonus_3_11
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (br : ℝ)
  (x : NNReal)
  (hx₁ : fr x = br)
  (nx : ↑sn)
  (hnx₀ : fb nx = x)
  (ny : ↑sn)
  (hx₂ : fb nx < fb ny)
  (hx₄ : ↑(fb ny) ≤ br):
   False := by
  have hc₁: br < fb ny := by
    rw [ ← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false br).mp ?_
  exact lt_of_lt_of_le hc₁ hx₄






lemma imo_1985_p6_bonus_4
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x => ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x) :
  cr ∉ scr := by
  rw [hscr]
  by_contra! hc₀
  apply (Set.mem_image fr sc cr).mp at hc₀
  obtain ⟨x, hx₀, hx₁⟩ := hc₀
  rw [hsc₀] at hx₀
  apply Set.mem_range.mp at hx₀
  obtain ⟨nx, hnx₀⟩ := hx₀
  have hnx₁: nx.1 + 1 ∈ sn := by
    let t : ℕ := nx.1 + 1
    have ht₀: t = nx.1 + 1 := by rfl
    rw [← ht₀, hsn]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_left 1 ↑nx
  let ny : ↑sn := ⟨(nx.1 + 1), hnx₁⟩
  have hx₂: fc ny < fc nx := by
    refine hfc₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    exact lt_add_one (↑nx:ℕ)
  have hx₃: fc ny ∈ sc := by
    rw [hsc₀]
    exact Set.mem_range_self ny
  have hx₄: cr ≤ fc ny := by
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    rw [hfr]
    use (fc ny)
  have hc₁: fc ny < cr := by
    rw [← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false cr).mp ?_
  exact lt_of_le_of_lt hx₄ hc₁


lemma imo_1985_p6_bonus_4_1
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (hc₀ : cr ∈ fr '' sc):
   False := by
  apply (Set.mem_image fr sc cr).mp at hc₀
  obtain ⟨x, hx₀, hx₁⟩ := hc₀
  rw [hsc₀] at hx₀
  apply Set.mem_range.mp at hx₀
  obtain ⟨nx, hnx₀⟩ := hx₀
  have hnx₁: nx.1 + 1 ∈ sn := by
    let t : ℕ := nx.1 + 1
    have ht₀: t = nx.1 + 1 := by rfl
    rw [← ht₀, hsn]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_left 1 ↑nx
  let ny : ↑sn := ⟨(nx.1 + 1), hnx₁⟩
  have hx₂: fc ny < fc nx := by
    refine hfc₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    exact lt_add_one (↑nx:ℕ)
  have hx₃: fc ny ∈ sc := by
    rw [hsc₀]
    exact Set.mem_range_self ny
  have hx₄: cr ≤ fc ny := by
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    rw [hfr]
    use (fc ny)
  have hc₁: fc ny < cr := by
    rw [← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false cr).mp ?_
  exact lt_of_le_of_lt hx₄ hc₁

lemma imo_1985_p6_bonus_4_2
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (x : NNReal)
  (hx₀ : x ∈ sc)
  (hx₁ : fr x = cr):
   False := by
  rw [hsc₀] at hx₀
  apply Set.mem_range.mp at hx₀
  obtain ⟨nx, hnx₀⟩ := hx₀
  have hnx₁: nx.1 + 1 ∈ sn := by
    let t : ℕ := nx.1 + 1
    have ht₀: t = nx.1 + 1 := by rfl
    rw [← ht₀, hsn]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_left 1 ↑nx
  let ny : ↑sn := ⟨(nx.1 + 1), hnx₁⟩
  have hx₂: fc ny < fc nx := by
    refine hfc₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    exact lt_add_one (↑nx:ℕ)
  have hx₃: fc ny ∈ sc := by
    rw [hsc₀]
    exact Set.mem_range_self ny
  have hx₄: cr ≤ fc ny := by
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    rw [hfr]
    use (fc ny)
  have hc₁: fc ny < cr := by
    rw [← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false cr).mp ?_
  exact lt_of_le_of_lt hx₄ hc₁

lemma imo_1985_p6_bonus_4_3
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (x : NNReal)
  (hx₁ : fr x = cr)
  (hx₀ : ∃ y, fc y = x):
   False := by
  obtain ⟨nx, hnx₀⟩ := hx₀
  have hnx₁: nx.1 + 1 ∈ sn := by
    let t : ℕ := nx.1 + 1
    have ht₀: t = nx.1 + 1 := by rfl
    rw [← ht₀, hsn]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_left 1 ↑nx
  let ny : ↑sn := ⟨(nx.1 + 1), hnx₁⟩
  have hx₂: fc ny < fc nx := by
    refine hfc₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    exact lt_add_one (↑nx:ℕ)
  have hx₃: fc ny ∈ sc := by
    rw [hsc₀]
    exact Set.mem_range_self ny
  have hx₄: cr ≤ fc ny := by
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    rw [hfr]
    use (fc ny)
  have hc₁: fc ny < cr := by
    rw [← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false cr).mp ?_
  exact lt_of_le_of_lt hx₄ hc₁

lemma imo_1985_p6_bonus_4_4
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (x : NNReal)
  (hx₁ : fr x = cr)
  (nx : ↑sn)
  (hnx₀ : fc nx = x):
   False := by
  have hnx₁: nx.1 + 1 ∈ sn := by
    let t : ℕ := nx.1 + 1
    have ht₀: t = nx.1 + 1 := by rfl
    rw [← ht₀, hsn]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_left 1 ↑nx
  let ny : ↑sn := ⟨(nx.1 + 1), hnx₁⟩
  have hx₂: fc ny < fc nx := by
    refine hfc₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    exact lt_add_one (↑nx:ℕ)
  have hx₃: fc ny ∈ sc := by
    rw [hsc₀]
    exact Set.mem_range_self ny
  have hx₄: cr ≤ fc ny := by
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    rw [hfr]
    use (fc ny)
  have hc₁: fc ny < cr := by
    rw [← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false cr).mp ?_
  exact lt_of_le_of_lt hx₄ hc₁


lemma imo_1985_p6_bonus_4_5
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (nx : ↑sn):
  nx.1 + 1 ∈ sn := by
  let t : ℕ := nx.1 + 1
  have ht₀: t = nx.1 + 1 := by rfl
  rw [← ht₀, hsn]
  refine Set.mem_Ici.mpr ?_
  exact Nat.le_add_left 1 ↑nx

lemma imo_1985_p6_bonus_4_6
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (x : NNReal)
  (hx₁ : fr x = cr)
  (nx : ↑sn)
  (hnx₀ : fc nx = x)
  (hnx₁ : nx.1 + 1 ∈ sn)
  (ny : ↑sn)
  (hny : ny = ⟨↑nx + 1, hnx₁⟩):
   False := by
  have hx₂: fc ny < fc nx := by
    refine hfc₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hny]
    exact lt_add_one (↑nx:ℕ)
  have hx₃: fc ny ∈ sc := by
    rw [hsc₀]
    exact Set.mem_range_self ny
  have hx₄: cr ≤ fc ny := by
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    rw [hfr]
    use (fc ny)
  have hc₁: fc ny < cr := by
    rw [← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false cr).mp ?_
  exact lt_of_le_of_lt hx₄ hc₁

lemma imo_1985_p6_bonus_4_7
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (nx : ↑sn)
  (hnx₁ : nx.1 + 1 ∈ sn)
  (ny : ↑sn)
  (hny : ny = ⟨↑nx + 1, hnx₁⟩):
   fc ny < fc nx := by
  refine hfc₃ ?_
  refine Subtype.mk_lt_mk.mpr ?_
  rw [hny]
  exact lt_add_one (↑nx:ℕ)

lemma imo_1985_p6_bonus_4_8
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (x : NNReal)
  (hx₁ : fr x = cr)
  (nx : ↑sn)
  (hnx₀ : fc nx = x)
  (ny : ↑sn)
  (hx₂ : fc ny < fc nx):
   False := by
  have hx₃: fc ny ∈ sc := by
    rw [hsc₀]
    exact Set.mem_range_self ny
  have hx₄: cr ≤ fc ny := by
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    rw [hfr]
    use (fc ny)
  have hc₁: fc ny < cr := by
    rw [← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false cr).mp ?_
  exact lt_of_le_of_lt hx₄ hc₁

lemma imo_1985_p6_bonus_4_9
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (sc : Set NNReal)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (x : NNReal)
  (hx₁ : fr x = cr)
  (nx : ↑sn)
  (hnx₀ : fc nx = x)
  (ny : ↑sn)
  (hx₂ : fc ny < fc nx)
  (hx₃ : fc ny ∈ sc):
   False := by
  have hx₄: cr ≤ fc ny := by
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    rw [hfr]
    use (fc ny)
  have hc₁: fc ny < cr := by
    rw [← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false cr).mp ?_
  exact lt_of_le_of_lt hx₄ hc₁

lemma imo_1985_p6_bonus_4_10
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (sc : Set NNReal)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (ny : ↑sn)
  (hx₃ : fc ny ∈ sc):
   cr ≤ ↑(fc ny) := by
  refine hcr₃ _ ?_
  rw [hscr]
  refine (Set.mem_image fr sc _).mpr ?_
  rw [hfr]
  use (fc ny)

lemma imo_1985_p6_bonus_4_11
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (cr : ℝ)
  (x : NNReal)
  (hx₁ : fr x = cr)
  (nx : ↑sn)
  (hnx₀ : fc nx = x)
  (ny : ↑sn)
  (hx₂ : fc ny < fc nx)
  (hx₄ : cr ≤ ↑(fc ny)):
   False := by
  have hc₁: fc ny < cr := by
    rw [← hx₁, ← hnx₀, hfr]
    exact hx₂
  refine (lt_self_iff_false cr).mp ?_
  exact lt_of_le_of_lt hx₄ hc₁



lemma imo_1985_p6_bonus_5
  (f₀ : ℕ → NNReal → NNReal)
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hsn₁ : ∀ (n : ↑sn), ↑n ∈ sn ∧ 0 < n.1)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1) :
  ∀ (n : ↑sn), f₀ (↑n) (fc n) - f₀ (↑n) (fb n) = 1 / ↑↑n := by
  intros n
  have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
  rw [hfb₁ n, hfc₁ n]
  rw [NNReal.sub_def, NNReal.sub_def]
  norm_cast
  simp
  have g₀: 0 ≤ (1 - (↑n:ℝ)⁻¹) := by
    refine sub_nonneg.mpr ?_
    refine inv_le_one_of_one_le₀ ?_
    exact Nat.one_le_cast.mpr hn₀
  have g₁: max (1 - (↑n:ℝ)⁻¹) 0 = 1 - (↑n:ℝ)⁻¹ := by
    exact max_eq_left g₀
  rw [g₁, ← sub_add, sub_self, zero_add]
  rw [Real.toNNReal_inv]
  refine inv_inj.mpr ?_
  exact NNReal.toNNReal_coe_nat n



lemma imo_1985_p6_bonus_5_1
  (f₀ : ℕ → NNReal → NNReal)
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (n : ↑sn)
  (hn₀ : 0 < n.1):
   f₀ (↑n) (fc n) - f₀ (↑n) (fb n) = 1 / ↑↑n := by
  rw [hfb₁ n, hfc₁ n]
  rw [NNReal.sub_def, NNReal.sub_def]
  norm_cast
  simp
  have g₀: 0 ≤ (1 - (↑n:ℝ)⁻¹) := by
    refine sub_nonneg.mpr ?_
    refine inv_le_one_of_one_le₀ ?_
    exact Nat.one_le_cast.mpr hn₀
  have g₁: max (1 - (↑n:ℝ)⁻¹) 0 = 1 - (↑n:ℝ)⁻¹ := by
    exact max_eq_left g₀
  rw [g₁, ← sub_add, sub_self, zero_add]
  rw [Real.toNNReal_inv]
  refine inv_inj.mpr ?_
  exact NNReal.toNNReal_coe_nat n


lemma imo_1985_p6_bonus_5_2
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1):
  ((1:NNReal).toReal - ↑((1:NNReal).toReal - ↑((1) / ↑↑n)).toNNReal).toNNReal = (1:NNReal) / ↑↑n := by
  norm_cast
  simp
  have g₀: 0 ≤ (1 - (↑n:ℝ)⁻¹) := by
    refine sub_nonneg.mpr ?_
    refine inv_le_one_of_one_le₀ ?_
    exact Nat.one_le_cast.mpr hn₀
  have g₁: max (1 - (↑n:ℝ)⁻¹) 0 = 1 - (↑n:ℝ)⁻¹ := by
    exact max_eq_left g₀
  rw [g₁, ← sub_add, sub_self, zero_add]
  rw [Real.toNNReal_inv]
  refine inv_inj.mpr ?_
  exact NNReal.toNNReal_coe_nat n

lemma imo_1985_p6_bonus_5_3
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1):
   ((1:ℝ) - (1 - (↑↑n)⁻¹) ⊔ 0).toNNReal = (↑↑n)⁻¹ := by
  have g₀: 0 ≤ (1 - (↑n:ℝ)⁻¹) := by
    refine sub_nonneg.mpr ?_
    refine inv_le_one_of_one_le₀ ?_
    exact Nat.one_le_cast.mpr hn₀
  have g₁: max (1 - (↑n:ℝ)⁻¹) 0 = 1 - (↑n:ℝ)⁻¹ := by
    exact max_eq_left g₀
  rw [g₁, ← sub_add, sub_self, zero_add]
  rw [Real.toNNReal_inv]
  refine inv_inj.mpr ?_
  exact NNReal.toNNReal_coe_nat n

lemma imo_1985_p6_bonus_5_4
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1):
   (0:ℝ) ≤ 1 - (↑↑n)⁻¹ := by
  refine sub_nonneg.mpr ?_
  refine inv_le_one_of_one_le₀ ?_
  exact Nat.one_le_cast.mpr hn₀

lemma imo_1985_p6_bonus_5_5
  (sn : Set ℕ)
  (n : ↑sn)
  (g₀ : (0:ℝ) ≤ 1 - (↑↑n)⁻¹):
   ((1:ℝ) - (1 - (↑↑n)⁻¹) ⊔ 0).toNNReal = (↑↑n)⁻¹ := by
  have g₁: max (1 - (↑n:ℝ)⁻¹) 0 = 1 - (↑n:ℝ)⁻¹ := by
    exact max_eq_left g₀
  rw [g₁, ← sub_add, sub_self, zero_add]
  rw [Real.toNNReal_inv]
  refine inv_inj.mpr ?_
  exact NNReal.toNNReal_coe_nat n


lemma imo_1985_p6_2
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x) :
  ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y := by
  intros n x y hn hxy
  by_cases hn₁: 1 < n
  . refine Nat.le_induction ?_ ?_ n hn₁
    . rw [h₁ 1 x (by norm_num)]
      rw [h₁ 1 y (by norm_num)]
      norm_num
      refine mul_lt_mul ?_ ?_ ?_ ?_
      . rw [h₀ x, h₀ y]
        exact hxy
      . refine _root_.add_le_add ?_ (by norm_num)
        rw [h₀ x, h₀ y]
        exact le_of_lt hxy
      . refine add_pos_of_nonneg_of_pos ?_ (by linarith)
        rw [h₀ x]
        exact NNReal.zero_le_coe
      . refine le_of_lt ?_
        refine h₂ 1 y ?_
        norm_num
        exact pos_of_gt hxy
    . intros m hm₀ hm₁
      rw [h₁ m x (by linarith)]
      rw [h₁ m y (by linarith)]
      refine mul_lt_mul hm₁ ?_ ?_ ?_
      . refine _root_.add_le_add ?_ (by norm_num)
        refine le_of_lt hm₁
      . refine add_pos_of_nonneg_of_pos ?_ ?_
        . exact h₃ m x (by linarith)
        . refine one_div_pos.mpr ?_
          norm_cast
          exact Nat.zero_lt_of_lt hm₀
      . refine le_of_lt ?_
        refine h₂ m y ?_
        constructor
        . exact Nat.zero_lt_of_lt hm₀
        . exact pos_of_gt hxy
  . interval_cases n
    rw [h₀ x, h₀ y]
    exact hxy


lemma imo_1985_p6_4
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x => (f n x).toNNReal) :
  ∀ (n : ℕ), 0 < n → StrictMono (f₀ n) := by
  intros n hn₀
  refine Monotone.strictMono_of_injective ?_ ?_
  . refine monotone_iff_forall_lt.mpr ?_
    intros a b hab
    refine le_of_lt ?_
    rw [hf₀]
    exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n a hn₀)).mpr (h₄ n a b hn₀ hab)
  . intros p q hpq
    contrapose! hpq
    apply lt_or_gt_of_ne at hpq
    cases' hpq with hpq hpq
    . refine ne_of_lt ?_
      rw [hf₀]
      exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n p hn₀)).mpr (h₄ n p q hn₀ hpq)
    . symm
      refine ne_of_lt ?_
      rw [hf₀]
      exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (h₃ n q hn₀)).mpr (h₄ n q p hn₀ hpq)

lemma imo_1985_p6_5
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n => Function.invFun (f₀ n)):
  ∀ (n : ℕ) (x y : NNReal), 0 < n → f₀ n x = y → fi n y = x := by
  intros n x y hn₀ hn₁
  have hf₃: ∀ n y, fi n y = Function.invFun (f₀ n) y := by
    exact fun n y => congrFun (congrFun hfi n) y
  rw [← hn₁, hf₃]
  have hmo₃: ∀ n, 0 < n → Function.Injective (f₀ n) := by
    exact fun n a => StrictMono.injective (hmo₂ n a)
  have hn₂: (Function.invFun (f₀ n)) ∘ (f₀ n) = id := by exact Function.invFun_comp (hmo₃ n hn₀)
  rw [Function.comp_def (Function.invFun (f₀ n)) (f₀ n)] at hn₂
  have hn₃: (fun x => Function.invFun (f₀ n) (f₀ n x)) x = id x := by exact Eq.symm (NNReal.eq (congrArg NNReal.toReal (congrFun (id (Eq.symm hn₂)) x)))
  exact hmo₁ n hn₀ (congrArg (f n) hn₃)

lemma imo_1985_p6_6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x => (f n x).toNNReal) :
  ∀ (n : ℕ), 0 < n → Continuous (f₀ n) := by
  intros n hn₀
  rw [hf₀]
  refine Continuous.comp' ?_ ?_
  . exact continuous_real_toNNReal
  . refine Nat.le_induction ?_ ?_ n hn₀
    . have hn₁: f 1 = fun (x:NNReal) => (x:ℝ) := by exact (Set.eqOn_univ (f 1) fun x => ↑x).mp fun ⦃x⦄ _ => h₀ x
      rw [hn₁]
      exact NNReal.continuous_coe
    . intros d hd₀ hd₁
      have hd₂: f (d + 1) = fun x => f d x * (f d x + 1 / ↑d) := by
        exact (Set.eqOn_univ (f (d + 1)) fun x => f d x * (f d x + 1 / ↑d)).mp fun ⦃x⦄ _ => h₁ d x hd₀
      rw [hd₂]
      refine Continuous.mul hd₁ ?_
      refine Continuous.add hd₁ ?_
      exact continuous_const

lemma imo_1985_p6_11
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (hbr₀ : IsLUB sbr br)
  (hcr₀ : IsGLB scr cr)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n) :
  br ≤ cr := by
  have hfc₄: ∀ nb nc, fb nb < fc nc := by
    intros nb nc
    cases' (lt_or_le nb nc) with hn₀ hn₀
    . refine lt_trans ?_ (hfc₂ nc)
      exact hfb₃ hn₀
    cases' lt_or_eq_of_le hn₀ with hn₁ hn₁
    . refine lt_trans (hfc₂ nb) ?_
      exact hfc₃ hn₁
    . rw [hn₁]
      exact hfc₂ nb
  by_contra! hc₀
  have hc₁: ∃ x ∈ sbr, cr < x ∧ x ≤ br := by exact IsLUB.exists_between hbr₀ hc₀
  let ⟨x, hx₀, hx₁, _⟩ := hc₁
  have hc₂: ∃ y ∈ scr, cr ≤ y ∧ y < x := by exact IsGLB.exists_between hcr₀ hx₁
  let ⟨y, hy₀, _, hy₂⟩ := hc₂
  have hc₃: x < y := by
    have hx₃: x.toNNReal ∈ sb := by
      rw [hsbr] at hx₀
      apply (Set.mem_image fr sb x).mp at hx₀
      obtain ⟨z, hz₀, hz₁⟩ := hx₀
      rw [← hz₁, hfr, Real.toNNReal_coe]
      exact hz₀
    have hy₃: y.toNNReal ∈ sc := by
      rw [hscr] at hy₀
      apply (Set.mem_image fr sc y).mp at hy₀
      obtain ⟨z, hz₀, hz₁⟩ := hy₀
      rw [← hz₁, hfr, Real.toNNReal_coe]
      exact hz₀
    rw [hsb₀] at hx₃
    rw [hsc₀] at hy₃
    apply Set.mem_range.mp at hx₃
    apply Set.mem_range.mp at hy₃
    let ⟨nx, hnx₀⟩ := hx₃
    let ⟨ny, hny₀⟩ := hy₃
    have hy₄: 0 < y := by
      contrapose! hy₃
      have hy₅: y.toNNReal = 0 := by exact Real.toNNReal_of_nonpos hy₃
      intro z
      rw [hy₅]
      refine ne_of_gt ?_
      refine lt_of_le_of_lt ?_ (hfc₂ z)
      exact hfb₄ z
    refine (Real.toNNReal_lt_toNNReal_iff hy₄).mp ?_
    rw [← hnx₀, ← hny₀]
    exact hfc₄ nx ny
  refine (lt_self_iff_false x).mp ?_
  exact lt_trans hc₃ hy₂

lemma imo_1985_p6_9
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hf₅ : ∀ (x : NNReal), fi 1 x = x)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (fb : ℕ → NNReal)
  (hfb₀ : fb = fun n => fi n (1 - 1 / ↑n))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1) :
  StrictMonoOn fb sn := by
  rw [hsn]
  refine strictMonoOn_Ici_of_pred_lt ?hψ
  intros m hm₀
  rw [hfb₀]
  refine Nat.le_induction ?_ ?_ m hm₀
  . have g₁: fi 1 0 = 0 := by exact hf₅ 0
    have g₂: (2:NNReal).IsConjExponent (2:NNReal) := by
      refine (NNReal.isConjExponent_iff_eq_conjExponent ?_).mpr ?_
      . exact one_lt_two
      . norm_cast
        simp
    simp
    norm_cast
    rw [g₁, NNReal.IsConjExponent.one_sub_inv g₂]
    let x := fi 2 2⁻¹
    have hx₀: x = fi 2 2⁻¹ := by rfl
    have hx₁: f₀ 2 x = 2⁻¹ := by
      rw [hx₀]
      have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
      exact g₃ 2⁻¹
    rw [← hx₀]
    contrapose! hx₁
    have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
    have hc₃: f₀ 2 x = 0 := by
      rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
      norm_cast
      rw [zero_mul]
      exact Real.toNNReal_zero
    rw [hc₃]
    exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)
  . simp
    intros n hn₀ _
    let i := fi n (1 - (↑n)⁻¹)
    let j := fi (n + 1) (1 - ((↑n:NNReal) + 1)⁻¹)
    have hi₀: i = fi n (1 - (↑n)⁻¹) := by rfl
    have hj₀: j = fi (n + 1) (1 - ((↑n:NNReal) + 1)⁻¹) := by rfl
    have hi₁: f₀ n i = (1 - (↑n)⁻¹) := by exact (hf₇ n i (1 - (↑n:NNReal)⁻¹) (by linarith)).mpr hi₀.symm
    have hj₁: f₀ (n + 1) j = (1 - ((↑n:NNReal) + 1)⁻¹) := by
      exact (hf₇ (n + 1) j _ (by linarith)).mpr hj₀.symm
    have hj₂: (1 - ((↑n:NNReal) + 1)⁻¹) = (1 - ((n:ℝ) + 1)⁻¹).toNNReal := by
      exact rfl
    have hn₂: f₀ (n + 1) i < f₀ (n + 1) j := by
      rw [hj₁, hj₂, hf₂ (n + 1) _ (by linarith), h₁ n i (by linarith)]
      rw [hf₁ n i (by linarith), hi₁]
      refine (Real.toNNReal_lt_toNNReal_iff ?_).mpr ?_
      . refine sub_pos.mpr ?_
        refine inv_lt_one_of_one_lt₀ ?_
        norm_cast
        exact Nat.lt_add_right 1 hn₀
      . have g₀: (↑n:NNReal)⁻¹ ≤ 1 := by exact Nat.cast_inv_le_one n
        rw [NNReal.coe_sub g₀, NNReal.coe_inv]
        simp
        refine inv_strictAnti₀ ?_ ?_
        . norm_cast
          exact Nat.zero_lt_of_lt hn₀
        . norm_cast
          exact lt_add_one n
    refine (StrictMono.lt_iff_lt ?_).mp hn₂
    exact hmo₂ (n + 1) (by linarith)


lemma imo_1985_p6_10
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (sn : Set ℕ)
  (sb : Set NNReal)
  (fb : ↑sn → NNReal)
  (hsn₀ : sn = Set.Ici 1)
  (hfb₀ : fb = fun n:↑sn => fi (↑n) (1 - 1 / ↑↑n))
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr: fr = fun x => ↑x)
  (sbr : Set ℝ)
  (hsbr: sbr = fr '' sb)
  (br: ℝ)
  (hbr₀ : IsLUB sbr br) :
  0 < br := by
  have hnb₀: 2 ∈ sn := by
    rw [hsn₀]
    decide
  let nb : ↑sn := ⟨2, hnb₀⟩
  have g₀: 0 < fb nb := by
    have g₁: (2:NNReal).IsConjExponent (2:NNReal) := by
      refine (NNReal.isConjExponent_iff_eq_conjExponent ?_).mpr ?_
      . exact one_lt_two
      . norm_cast
        simp
    rw [hfb₀]
    simp
    have hnb₁: nb.val = 2 := by exact rfl
    rw [hnb₁]
    norm_cast
    rw [NNReal.IsConjExponent.one_sub_inv g₁]
    let x := fi 2 2⁻¹
    have hx₀: x = fi 2 2⁻¹ := by rfl
    have hx₁: f₀ 2 x = 2⁻¹ := by
      rw [hx₀]
      have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
      exact g₃ 2⁻¹
    rw [← hx₀]
    contrapose! hx₁
    have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
    have hc₃: f₀ 2 x = 0 := by
      rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
      norm_cast
      rw [zero_mul]
      exact Real.toNNReal_zero
    rw [hc₃]
    exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₁)
  have g₁: ∃ x, 0 < x ∧ x ∈ sbr := by
    use (fb nb).toReal
    constructor
    . exact g₀
    . rw [hsbr]
      simp
      use fb ↑nb
      constructor
      . rw [hsb₀]
        exact Set.mem_range_self nb
      . exact congrFun hfr (fb ↑nb)
  obtain ⟨x, hx₀, hx₁⟩ := g₁
  have hx₂: br ∈ upperBounds sbr := by
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  exact gt_of_ge_of_gt (hx₂ hx₁) hx₀


lemma imo_1985_p6_unique
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x) :
  ∀ (y₁ y₂ : NNReal),
    (∀ (n : ℕ), 0 < n → 0 < f n y₁ ∧ f n y₁ < f (n + 1) y₁ ∧ f (n + 1) y₁ < 1) →
      (∀ (n : ℕ), 0 < n → 0 < f n y₂ ∧ f n y₂ < f (n + 1) y₂ ∧ f (n + 1) y₂ < 1) → y₁ = y₂ := by
  intros x y hx₀ hy₀
  let sd : Set ℕ := Set.Ici 2
  let fd : NNReal → NNReal → ↑sd → ℝ := fun y₁ y₂ n => (f n.1 y₂ - f n.1 y₁)
  have hfd₁: ∀ y₁ y₂ n, fd y₁ y₂ n = f n.1 y₂ - f n.1 y₁ := by exact fun y₁ y₂ n => rfl
  have hd₁: ∀ n a b, a < b → 0 < fd a b n := by
    intros nd a b hnd₀
    rw [hfd₁]
    refine sub_pos.mpr ?_
    refine hmo₀ nd.1 ?_ hnd₀
    exact lt_of_lt_of_le (Nat.zero_lt_two) nd.2
  have hfd₂: ∀ a b, a < b → (∀ n:↑sd, f n.1 a < f (n.1 + 1) a ∧ f n.1 b < f (n.1 + 1) b)
      → Filter.Tendsto (fd a b) Filter.atTop Filter.atTop := by
    intros a b ha₀ ha₁
    have hd₀: ∀ nd:↑sd, (nd.1 + 1) ∈ sd := by
      intro nd
      have hd₀: 2 ≤ nd.1 := by exact nd.2
      refine Set.mem_Ici.mpr ?_
      exact Nat.le_add_right_of_le hd₀
    have hd₂: ∀ nd, fd a b nd  * (2 - 1 / nd.1) ≤ fd a b ⟨nd.1 + 1, hd₀ nd⟩ := by
      intro nd
      have hnd₀: 0 < nd.1 := by exact Nat.lt_add_left_iff_pos.mp (hd₀ nd)
      rw [hfd₁, hfd₁, h₁ nd.1 _ hnd₀, h₁ nd.1 _ hnd₀]
      have hnd₁: f (↑nd) b * (f (↑nd) b + 1 / ↑↑nd) - f (↑nd) a * (f (↑nd) a + 1 / ↑↑nd) =
        (f (↑nd) b - f (↑nd) a) * (f (↑nd) b + f (↑nd) a + 1 / nd.1) := by
        ring_nf
      rw [hnd₁]
      refine (mul_le_mul_left ?_).mpr ?_
      . rw [← hfd₁]
        exact hd₁ nd a b ha₀
      . refine le_sub_iff_add_le.mp ?_
        rw [sub_neg_eq_add]
        have hnd₂: 1 - 1 / nd.1 < f (↑nd) b := by
          exact h₇ nd.1 b hnd₀ (ha₁ nd).2
        have hnd₃: 1 - 1 / nd.1 < f (↑nd) a := by
          exact h₇ nd.1 a hnd₀ (ha₁ nd).1
        linarith
    let i : ↑sd := ⟨2, (by decide)⟩
    have hd₃: ∀ nd, fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd := by
      intro nd
      induction' nd with nd hnd₀
      refine Nat.le_induction ?_ ?_ nd hnd₀
      . simp
        exact le_of_eq (by rfl)
      . simp
        intros n hn₀ hn₁
        have hn₂: n - 1 = n - 2 + 1 := by
          simp
          exact (Nat.sub_eq_iff_eq_add hn₀).mp rfl
        refine le_trans ?_ (hd₂ ⟨n, hn₀⟩)
        rw [hn₂, pow_succ (3/2) (n - 2), ← mul_assoc (fd a b i)]
        refine mul_le_mul hn₁ ?_ (by linarith) ?_
        . refine (div_le_iff₀ (two_pos)).mpr ?_
          rw [sub_mul, one_div_mul_eq_div _ 2]
          refine le_sub_iff_add_le.mpr ?_
          refine le_sub_iff_add_le'.mp ?_
          refine (div_le_iff₀ ?_).mpr ?_
          . refine Nat.cast_pos.mpr ?_
            exact lt_of_lt_of_le (two_pos) hn₀
          . ring_nf
            exact Nat.ofNat_le_cast.mpr hn₀
        . exact le_of_lt (hd₁ ⟨n, hn₀⟩ a b ha₀)
    refine Filter.tendsto_atTop_atTop.mpr ?_
    intro z
    by_cases hz₀: z ≤ fd a b i
    . use i
      intros j _
      refine le_trans hz₀ ?_
      refine le_trans ?_ (hd₃ j)
      refine le_mul_of_one_le_right ?_ ?_
      . refine le_of_lt ?_
        exact hd₁ i a b ha₀
      . refine one_le_pow₀ ?_
        linarith
    . push_neg at hz₀
      have hz₁: 0 < fd a b i := by exact hd₁ i a b ha₀
      have hz₂: 0 < Real.log (z / fd a b i) := by
        refine Real.log_pos ?_
        exact (one_lt_div hz₁).mpr hz₀
      let j : ℕ := Nat.ceil (2 + Real.log (z / fd a b i) / Real.log (3 / 2))
      have hj₀: 2 < j := by
        refine Nat.lt_ceil.mpr ?_
        norm_cast
        refine lt_add_of_pos_right 2 ?_
        refine div_pos ?_ ?_
        . exact hz₂
        . refine Real.log_pos ?_
          linarith
      have hj₁: j ∈ sd := by
        exact Set.mem_Ici_of_Ioi hj₀
      use ⟨j, hj₁⟩
      intro k hk₀
      have hk₁: fd a b i * (3 / 2) ^ (k.1 - 2) ≤ fd a b k := by
        exact hd₃ k
      have hk₂: i < k := by
        refine lt_of_lt_of_le ?_ hk₀
        refine Subtype.mk_lt_mk.mpr ?_
        refine Nat.lt_ceil.mpr ?_
        norm_cast
        refine lt_add_of_pos_right 2 ?_
        refine div_pos ?_ ?_
        . exact hz₂
        . refine Real.log_pos ?_
          linarith
      refine le_trans ?_ hk₁
      refine (div_le_iff₀' ?_).mp ?_
      . exact hz₁
      . refine Real.le_pow_of_log_le (by linarith) ?_
        refine (div_le_iff₀ ?_).mp ?_
        . refine Real.log_pos ?_
          linarith
        . rw [Nat.cast_sub ?_]
          . rw [Nat.cast_two]
            refine le_sub_iff_add_le'.mpr ?_
            exact Nat.le_of_ceil_le hk₀
          . exact Nat.le_trans (hd₀ i) hk₂
  have hfd₃: ∀ a b, a < b → (∀ (n:↑sd), (1 - 1 / n.1 < f n.1 a ∧ 1 - 1 / n.1 < f n.1 b) ∧ (f n.1 a < 1 ∧ f n.1 b < 1))
      → Filter.Tendsto (fd a b) Filter.atTop (nhds 0) := by
    intros a b ha₀ ha₁
    refine tendsto_atTop_nhds.mpr ?_
    intros U hU₀ hU₁
    have hU₂: U ∈ nhds 0 := by exact IsOpen.mem_nhds hU₁ hU₀
    apply mem_nhds_iff_exists_Ioo_subset.mp at hU₂
    obtain ⟨l, u, hl₀, hl₁⟩ := hU₂
    have hl₂: 0 < u := by exact (Set.mem_Ioo.mpr hl₀).2
    let nd := 2 + Nat.ceil (1/u)
    have hnd₀: nd ∈ sd := by
      refine Set.mem_Ici.mpr ?_
      exact Nat.le_add_right 2 ⌈1 / u⌉₊
    use ⟨nd, hnd₀⟩
    intros n hn₀
    refine (IsOpen.mem_nhds_iff hU₁).mp ?_
    refine mem_nhds_iff.mpr ?_
    use Set.Ioo l u
    constructor
    . exact hl₁
    constructor
    . exact isOpen_Ioo
    . refine Set.mem_Ioo.mpr ?_
      constructor
      . refine lt_trans ?_ (hd₁ n a b ha₀)
        exact (Set.mem_Ioo.mp hl₀).1
      . have hn₁: fd a b n < 1 / n := by
          rw [hfd₁]
          have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
          have hb₁: f n b < 1 := by exact (ha₁ n).2.2
          refine sub_lt_iff_lt_add.mpr ?_
          refine lt_trans hb₁ ?_
          exact sub_lt_iff_lt_add'.mp ha₂
        have hn₂: (1:ℝ) / n ≤ 1 / nd := by
          refine one_div_le_one_div_of_le ?_ ?_
          . refine Nat.cast_pos.mpr ?_
            exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
          . exact Nat.cast_le.mpr hn₀
        refine lt_of_lt_of_le hn₁ ?_
        refine le_trans hn₂ ?_
        refine div_le_of_le_mul₀ ?_ ?_ ?_
        . exact Nat.cast_nonneg' nd
        . exact le_of_lt hl₂
        . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
            refine (mul_le_mul_left hl₂).mpr ?_
            rw [Nat.cast_add 2 _, Nat.cast_two]
            refine add_le_add_left ?_ 2
            exact Nat.le_ceil (1 / u)
          refine le_trans ?_ hl₃
          rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
          refine le_of_lt ?_
          refine sub_lt_iff_lt_add.mp ?_
          rw [sub_self 1]
          exact mul_pos hl₂ (two_pos)
  by_contra! hc₀
  by_cases hy₁: x < y
  . have hy₂: Filter.Tendsto (fd x y) Filter.atTop Filter.atTop := by
      refine hfd₂ x y hy₁ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (two_pos) nd.2
      constructor
      . exact (hx₀ nd.1 hnd₀).2.1
      . exact (hy₀ nd.1 hnd₀).2.1
    have hy₃: Filter.Tendsto (fd x y) Filter.atTop (nhds 0) := by
      refine hfd₃ x y hy₁ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by
        refine lt_of_lt_of_le ?_ nd.2
        exact Nat.zero_lt_two
      have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
      have hnd₂: 0 < nd.1 - 1 := by
        refine Nat.sub_pos_of_lt ?_
        refine lt_of_lt_of_le ?_ nd.2
        exact Nat.one_lt_two
      constructor
      . constructor
        . refine h₇ nd.1 x hnd₀ ?_
          exact (hx₀ (nd.1) hnd₀).2.1
        . refine h₇ nd.1 y hnd₀ ?_
          exact (hy₀ (nd.1) hnd₀).2.1
      . constructor
        . rw [← hnd₁]
          exact (hx₀ (nd.1 - 1) hnd₂).2.2
        . rw [← hnd₁]
          exact (hy₀ (nd.1 - 1) hnd₂).2.2
    apply Filter.tendsto_atTop_atTop.mp at hy₂
    apply tendsto_atTop_nhds.mp at hy₃
    contrapose! hy₃
    clear hy₃
    let sx : Set ℝ := Set.Ioo (-1) 1
    use sx
    constructor
    . refine Set.mem_Ioo.mpr ?_
      simp
    constructor
    . exact isOpen_Ioo
    . intro N
      have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
      obtain ⟨i, hi₀⟩ := hy₅
      have hi₁: (N.1 + i.1) ∈ sd := by
        refine Set.mem_Ici.mpr ?_
        rw [← add_zero 2]
        refine Nat.add_le_add ?_ ?_
        . exact N.2
        . refine le_trans ?_ i.2
          exact Nat.zero_le 2
      let a : ↑sd := ⟨N + i, hi₁⟩
      use a
      constructor
      . refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_right ↑N ↑i
      . refine Set.not_mem_Ioo_of_ge ?_
        have hi₂: ↑↑N + 3 ≤ fd x y a := by
          refine hi₀ a ?_
          refine Subtype.mk_le_mk.mpr ?_
          exact Nat.le_add_left ↑i ↑N
        refine le_trans ?_ hi₂
        norm_cast
        exact Nat.le_add_left 1 (↑N + 2)
  . have hy₂: y < x := by
      push_neg at hy₁
      exact lt_of_le_of_ne hy₁ hc₀.symm
    have hy₃: Filter.Tendsto (fd y x) Filter.atTop Filter.atTop := by
      refine hfd₂ y x hy₂ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (two_pos) nd.2
      constructor
      . exact (hy₀ nd.1 hnd₀).2.1
      . exact (hx₀ nd.1 hnd₀).2.1
    have hy₄: Filter.Tendsto (fd y x) Filter.atTop (nhds 0) := by
      refine hfd₃ y x hy₂ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (Nat.zero_lt_two) nd.2
      have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
      have hnd₂: 0 < nd.1 - 1 := by
        refine Nat.sub_pos_of_lt ?_
        exact lt_of_lt_of_le (Nat.one_lt_two) nd.2
      constructor
      . constructor
        . refine h₇ nd.1 y hnd₀ ?_
          exact (hy₀ (nd.1) hnd₀).2.1
        . refine h₇ nd.1 x hnd₀ ?_
          exact (hx₀ (nd.1) hnd₀).2.1
      . constructor
        . rw [← hnd₁]
          exact (hy₀ (nd.1 - 1) hnd₂).2.2
        . rw [← hnd₁]
          exact (hx₀ (nd.1 - 1) hnd₂).2.2
    apply Filter.tendsto_atTop_atTop.mp at hy₃
    apply tendsto_atTop_nhds.mp at hy₄
    contrapose! hy₄
    clear hy₄
    let sx : Set ℝ := Set.Ioo (-1) 1
    use sx
    constructor
    . refine Set.mem_Ioo.mpr ?_
      simp
    constructor
    . exact isOpen_Ioo
    . intro N
      have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd y x a := by exact hy₃ (N + 3)
      obtain ⟨i, hi₀⟩ := hy₅
      have hi₁: (N.1 + i.1) ∈ sd := by
        refine Set.mem_Ici.mpr ?_
        rw [← add_zero 2]
        refine Nat.add_le_add ?_ ?_
        . exact N.2
        . refine le_trans ?_ i.2
          exact Nat.zero_le 2
      let a : ↑sd := ⟨N + i, hi₁⟩
      use a
      constructor
      . refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_right ↑N ↑i
      . refine Set.not_mem_Ioo_of_ge ?_
        have hi₂: ↑↑N + 3 ≤ fd y x a := by
          refine hi₀ a ?_
          refine Subtype.mk_le_mk.mpr ?_
          exact Nat.le_add_left ↑i ↑N
        refine le_trans ?_ hi₂
        norm_cast
        exact Nat.le_add_left 1 (↑N + 2)


lemma imo_1985_p6_unique_22
  (f : ℕ → NNReal → ℝ)
  (x y : NNReal)
  (sd : Set ℕ := Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ := fun y₁ y₂ n ↦ f (↑n) y₂ - f (↑n) y₁)
  (sx : Set ℝ)
  (hsx : sx = Set.Ioo (-1) 1)
  (N i : ↑sd)
  (hi₀ : ∀ (a : ↑sd), i ≤ a → ↑↑N + 3 ≤ fd x y a)
  (hi₁ : N.1 + i.1 ∈ sd)
  (a : ↑sd)
  (ha : a = ⟨↑N + ↑i, hi₁⟩):
   N ≤ a ∧ fd x y a ∉ sx := by
  constructor
  . refine Subtype.mk_le_mk.mpr ?_
    rw [ha]
    exact Nat.le_add_right ↑N ↑i
  . rw [hsx]
    refine Set.not_mem_Ioo_of_ge ?_
    have hi₂: ↑↑N + 3 ≤ fd x y a := by
      refine hi₀ a ?_
      refine Subtype.mk_le_mk.mpr ?_
      rw [ha]
      exact Nat.le_add_left ↑i ↑N
    refine le_trans ?_ hi₂
    norm_cast
    exact Nat.le_add_left 1 (↑N + 2)

lemma imo_1985_p6_exists
  (f : ℕ → NNReal → ℝ)
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x => ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₁ : 0 < br)
  (hu₅ : br ≤ cr)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x) :
  ∃ x, ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1 := by
  cases' lt_or_eq_of_le hu₅ with hu₆ hu₆
  . apply exists_between at hu₆
    let ⟨a, ha₀, ha₁⟩ := hu₆
    have ha₂: 0 < a := by exact gt_trans ha₀ hbr₁
    have ha₃: 0 < a.toNNReal := by exact Real.toNNReal_pos.mpr ha₂
    use a.toNNReal
    intros n hn₀
    have hn₁: n ∈ sn := by
      rw [hsn₀]
      exact hn₀
    constructor
    . exact h₂ n a.toNNReal ⟨hn₀, ha₃⟩
    constructor
    . refine h₈ n a.toNNReal hn₀ ?_ ?_
      . exact Real.toNNReal_pos.mpr ha₂
      . let nn : ↑sn := ⟨n, hn₁⟩
        have hn₂: f n (fb nn) = 1 - 1 / n := by
          rw [hf₁ n _ hn₀, hfb₁ nn]
          refine NNReal.coe_sub ?_
          refine div_le_self ?_ ?_
          . exact zero_le_one' NNReal
          . exact Nat.one_le_cast.mpr hn₀
        rw [← hn₂]
        refine hmo₀ n hn₀ ?_
        refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
        refine lt_of_le_of_lt ?_ ha₀
        refine hbr₃ _ ?_
        rw [hsbr]
        refine (Set.mem_image fr sb _).mpr ?_
        use (fb nn)
        rw [hfr, hsb₀]
        refine ⟨?_, rfl⟩
        exact Set.mem_range_self nn
    . have hn₂: n + 1 ∈ sn := by
        rw [hsn₀]
        exact Set.mem_Ici.mpr (by linarith)
      let nn : ↑sn := ⟨n + 1, hn₂⟩
      have hn₃: f (n + 1) (fc (nn)) = 1 := by
        rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
        exact rfl
      rw [← hn₃]
      refine hmo₀ (n + 1) (by linarith) ?_
      refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt ha₂)).mpr ?_
      refine lt_of_lt_of_le ha₁ ?_
      refine hcr₃ _ ?_
      rw [hscr]
      refine (Set.mem_image fr sc _).mpr ?_
      use (fc nn)
      rw [hfr, hsc₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self nn
  . use br.toNNReal
    intros n hn₀
    have hn₁: n ∈ sn := by
      rw [hsn₀]
      exact hn₀
    constructor
    . refine h₂ n br.toNNReal ⟨hn₀, ?_⟩
      exact Real.toNNReal_pos.mpr hbr₁
    constructor
    . refine h₈ n br.toNNReal hn₀ ?_ ?_
      . exact Real.toNNReal_pos.mpr hbr₁
      . let nn : ↑sn := ⟨n, hn₁⟩
        have hn₂: fb nn < br := by
          by_contra! hc₀
          have hbr₅: (fb nn) = br := by
            refine eq_of_le_of_le ?_ hc₀
            refine hbr₃ _ ?_
            rw [hsbr]
            refine (Set.mem_image fr sb _).mpr ?_
            use (fb nn)
            rw [hfr, hsb₀]
            constructor
            . exact Set.mem_range_self nn
            . exact rfl
          have hn₂: n + 1 ∈ sn := by
            rw [hsn₀]
            refine Set.mem_Ici.mpr ?_
            exact Nat.le_add_right_of_le hn₀
          let ns : ↑sn := ⟨n + 1, hn₂⟩
          have hc₁: fb nn < fb ns := by
            refine hfb₃ ?_
            refine Subtype.mk_lt_mk.mpr ?_
            exact lt_add_one n
          have hbr₆: fb ns ≤ fb nn := by
            refine NNReal.coe_le_coe.mp ?_
            rw [hbr₅]
            refine hbr₃ _ ?_
            rw [hsbr]
            refine (Set.mem_image fr sb _).mpr ?_
            use (fb ns)
            rw [hfr, hsb₀]
            refine ⟨?_, rfl⟩
            exact Set.mem_range_self ns
          refine (lt_self_iff_false (fb nn)).mp ?_
          exact lt_of_lt_of_le hc₁ hbr₆
        have hn₃: f n (fb nn) = 1 - 1 / n := by
          rw [hf₁ n _ hn₀, hfb₁ nn]
          refine NNReal.coe_sub ?_
          refine div_le_self ?_ ?_
          . exact zero_le_one' NNReal
          . exact Nat.one_le_cast.mpr hn₀
        rw [← hn₃]
        refine hmo₀ n hn₀ ?_
        exact Real.lt_toNNReal_iff_coe_lt.mpr hn₂
    . have hn₂: n + 1 ∈ sn := by
        rw [hsn₀]
        exact Set.mem_Ici.mpr (by linarith)
      let nn : ↑sn := ⟨n + 1, hn₂⟩
      have hcr₁: 0 < cr := by exact gt_of_ge_of_gt hu₅ hbr₁
      have hn₃: f (n + 1) (fc (nn)) = 1 := by
        rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
        exact rfl
      rw [← hn₃, hu₆]
      refine hmo₀ (n + 1) (by linarith) ?_
      refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt hcr₁)).mpr ?_
      by_contra! hc₀
      have hc₁: fc nn = cr := by
        refine eq_of_le_of_le hc₀ ?_
        refine hcr₃ _ ?_
        rw [hscr]
        refine (Set.mem_image fr sc _).mpr ?_
        use (fc nn)
        rw [hfr, hsc₀]
        refine ⟨?_, rfl⟩
        exact Set.mem_range_self nn
      have hn₄: n + 2 ∈ sn := by
        rw [hsn₀]
        refine Set.mem_Ici.mpr ?_
        exact Nat.le_add_right_of_le hn₀
      let ns : ↑sn := ⟨n + 2, hn₄⟩
      have hn₅: fc ns < fc nn := by
        refine hfc₃ ?_
        refine Subtype.mk_lt_mk.mpr ?_
        exact Nat.lt_add_one (n + 1)
      have hc₂: fc nn ≤ fc ns := by
        refine NNReal.coe_le_coe.mp ?_
        rw [hc₁]
        refine hcr₃ _ ?_
        rw [hscr]
        refine (Set.mem_image fr sc _).mpr ?_
        use (fc ns)
        rw [hfr, hsc₀]
        refine ⟨?_, rfl⟩
        exact Set.mem_range_self ns
      refine (lt_self_iff_false (fc ns)).mp ?_
      exact lt_of_lt_of_le hn₅ hc₂


lemma imo_1985_p6_unique_23
  (f : ℕ → NNReal → ℝ)
  (x y : NNReal)
  (sd : Set ℕ := Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ := fun y₁ y₂ n ↦ f (↑n) y₂ - f (↑n) y₁)
  (sx : Set ℝ)
  (hsx : sx = Set.Ioo (-1) 1)
  (N i : ↑sd)
  (hi₀ : ∀ (a : ↑sd), i ≤ a → ↑↑N + 3 ≤ fd x y a)
  (hi₁ : N.1 + ↑i ∈ sd)
  (a : ↑sd)
  (ha : a = ⟨↑N + ↑i, hi₁⟩):
   fd x y a ∉ sx := by
  rw [hsx]
  refine Set.not_mem_Ioo_of_ge ?_
  have hi₂: ↑↑N + 3 ≤ fd x y a := by
    refine hi₀ a ?_
    refine Subtype.mk_le_mk.mpr ?_
    rw [ha]
    exact Nat.le_add_left ↑i ↑N
  refine le_trans ?_ hi₂
  norm_cast
  exact Nat.le_add_left 1 (↑N + 2)

lemma imo_1985_p6_unique_24
  (f : ℕ → NNReal → ℝ)
  (x y : NNReal)
  (sd : Set ℕ := Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ := fun y₁ y₂ n ↦ f (↑n) y₂ - f (↑n) y₁)
  (N i : ↑sd)
  (hi₀ : ∀ (a : ↑sd), i ≤ a → ↑↑N + 3 ≤ fd x y a)
  (hi₁ : N.1 + ↑i ∈ sd)
  (a : ↑sd)
  (ha : a = ⟨↑N + ↑i, hi₁⟩):
   ↑↑N + 3 ≤ fd x y a := by
  refine hi₀ a ?_
  refine Subtype.mk_le_mk.mpr ?_
  rw [ha]
  exact Nat.le_add_left ↑i ↑N


lemma imo_1985_p6_main_1
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have h₃: ∀ n x, 0 < n → 0 ≤ f n x := by
    intros n x hn
    refine Nat.le_induction ?_ ?_ n hn
    . rw [h₀ x]
      exact NNReal.zero_le_coe
    . intros d hd₀ hd₁
      rw [h₁ d x hd₀]
      refine mul_nonneg hd₁ ?_
      refine add_nonneg hd₁ ?_
      refine div_nonneg (by linarith) ?_
      exact Nat.cast_nonneg' d
  have hmo₀: ∀ n, 0 < n → StrictMono (f n) := by
    intros n hn₀
    refine Monotone.strictMono_of_injective ?h₁ ?h₂
    . refine monotone_iff_forall_lt.mpr ?h₁.a
      intros a b hab
      refine le_of_lt ?_
      exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n a b hn₀ hab
    . intros p q hpq
      contrapose! hpq
      apply lt_or_gt_of_ne at hpq
      cases' hpq with hpq hpq
      . refine ne_of_lt ?_
        exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n p q hn₀ hpq
      . symm
        refine ne_of_lt ?_
        exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n q p hn₀ hpq
  have hmo₁: ∀ n, 0 < n → Function.Injective (f n) := by exact fun n a => StrictMono.injective (hmo₀ n a)
  let f₀: ℕ → NNReal → NNReal := fun n x => (f n x).toNNReal
  have hf₀: f₀ = fun n x => (f n x).toNNReal := by rfl
  have hf₁: ∀ n x, 0 < n → f n x = f₀ n x := by
    intros n x hn₀
    rw [hf₀]
    simp
    exact h₃ n x hn₀
  have hf₂: ∀ n x, 0 < n → f₀ n x = (f n x).toNNReal := by
    intros n x _
    rw [hf₀]
  have hmo₂: ∀ n, 0 < n → StrictMono (f₀ n) := by
    intros n hn₀
    refine imo_1985_p6_4 f h₃ ?_ f₀ hf₀ n hn₀
    exact fun n x y a a_1 => hmo₀ n a a_1
  let fi : ℕ → NNReal → NNReal := fun n => Function.invFun (f₀ n)
  have hmo₇: ∀ n, 0 < n → Function.RightInverse (fi n) (f₀ n) := by
    intros n hn₀
    refine Function.rightInverse_invFun ?_
    have h₄: ∀ n x y, 0 < n → x < y → f n x < f n y := by
      exact fun n x y a a_1 => imo_1985_p6_2 f h₀ h₁ h₂ h₃ n x y a a_1
    refine imo_1985_p6_7 f h₀ h₁ h₃ ?_ f₀ hf₂ hmo₂ ?_ n hn₀
    . exact fun n x a => imo_1985_p6_3 f h₀ h₁ h₄ n x a
    . intros m hm₀
      exact imo_1985_p6_6 f h₀ h₁ f₀ hf₀ m hm₀
  have hf₇: ∀ n x y, 0 < n → (f₀ n x = y ↔ fi n y = x) := by
    intros n x y hn₀
    constructor
    . intro hn₁
      rw [← hn₁, hf₀]
      have hn₂: (Function.invFun (f n)) ∘ (f n) = id := by exact Function.invFun_comp (hmo₁ n hn₀)
      rw [Function.comp_def (Function.invFun (f n)) (f n)] at hn₂
      exact imo_1985_p6_5 f hmo₁ f₀ hmo₂ fi rfl n x ((fun n x => (f n x).toNNReal) n x) hn₀ (hf₂ n x hn₀)
    . intro hn₁
      rw [← hn₁]
      exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ y))
  let sn : Set ℕ := Set.Ici 1
  let fb : ↑sn → NNReal := sn.restrict (fun (n:ℕ) => fi n (1 - 1 / (n:NNReal)))
  let fc : ↑sn → NNReal := sn.restrict (fun (n:ℕ) => fi n 1)
  have hsn₁: ∀ n:↑sn, ↑n ∈ sn ∧ 0 < (↑n:ℕ) := by
    intro n
    have hn₀: ↑n ∈ sn := by exact Subtype.coe_prop n
    constructor
    . exact Subtype.coe_prop n
    . exact hn₀
  have hfb₀: fb = fun (n:↑sn) => fi n (1 - 1 / (n:NNReal)) := by rfl
  have hfc₀: fc = fun (n:↑sn) => fi n 1 := by rfl
  have hfb₁: ∀ n:↑sn, f₀ n (fb n) = 1 - 1 / (n:NNReal) := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfb₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ (1 - 1 / (n:NNReal))))
  have hfc₁: ∀ n:↑sn, f₀ n (fc n) = 1 := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfc₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ 1))
  have hu₁: ∀ n:↑sn, fb n < 1 := by
    exact imo_1985_p6_8 f h₀ h₁ hmo₀ hmo₁ f₀ hf₂ sn fb hsn₁ hfb₁
  have hfc₂: ∀ n:↑sn, fb n < fc n := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    have g₀: f₀ n (fb n) < f₀ n (fc n) := by
      rw [hfb₁ n, hfc₁ n]
      simp
      exact (hsn₁ n).2
    exact (StrictMono.lt_iff_lt (hmo₂ n hn₀)).mp g₀
  have hfb₃: StrictMono fb := by
    refine StrictMonoOn.restrict ?_
    refine imo_1985_p6_9 f h₀ h₁ f₀ hf₁ hf₂ hmo₂ fi ?_ hmo₇ hf₇ _ (by rfl) sn (by rfl)
    intro x
    refine (hf₇ 1 x x (by linarith)).mp ?_
    rw [hf₂ 1 x (by linarith), h₀]
    exact Real.toNNReal_coe
  have hfc₃: StrictAnti fc := by
    have g₀: StrictAntiOn (fun n => fi n 1) sn := by
      refine strictAntiOn_Ici_of_lt_pred ?_
      intros m hm₀
      have hm₁: 0 < m - 1 := by exact Nat.zero_lt_sub_of_lt hm₀
      have hm₂: m = m - 1 + 1 := by rw [Nat.sub_add_cancel (le_of_lt hm₀)]
      have hm₃: 0 < m := by exact Nat.zero_lt_of_lt hm₀
      simp
      let x := fi m 1
      let y := fi (m - 1) 1
      have hx₀: x = fi m 1 := by rfl
      have hy₀: y = fi (m - 1) 1 := by rfl
      have hx₁: f₀ m x = 1 := by exact (hf₇ m x 1 (by linarith)).mpr hx₀.symm
      have hy₁: f₀ (m - 1) y = 1 := by
        exact (hf₇ (m - 1) y 1 hm₁).mpr hy₀.symm
      have hy₂: f (m - 1) y = 1 := by
        rw [hf₁ (m - 1) y hm₁, hy₁]
        exact rfl
      have hf: StrictMono (f m) := by exact hmo₀ m hm₃
      refine (StrictMono.lt_iff_lt hf).mp ?_
      rw [← hx₀, ← hy₀]
      rw [hf₁ m x hm₃, hf₁ m y hm₃]
      refine NNReal.coe_lt_coe.mpr ?_
      rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
      simp
      exact hm₀
    intros m n hmn
    rw [hfc₀]
    simp
    let mn : ℕ := ↑m
    let nn : ℕ := ↑n
    have hm₀: mn ∈ sn := by exact Subtype.coe_prop m
    have hn₀: nn ∈ sn := by exact Subtype.coe_prop n
    exact g₀ hm₀ hn₀ hmn
  let sb := Set.range fb
  let sc := Set.range fc
  have hsb₀: sb = Set.range fb := by rfl
  have hsc₀: sc = Set.range fc := by rfl
  let fr : NNReal → ℝ := fun x => x.toReal
  let sbr := Set.image fr sb
  let scr := Set.image fr sc
  have hu₃: ∃ br, IsLUB sbr br := by
    refine Real.exists_isLUB ?_ ?_
    . exact Set.Nonempty.of_subtype
    . refine NNReal.bddAbove_coe.mpr ?_
      refine (bddAbove_iff_exists_ge 1).mpr ?_
      use 1
      constructor
      . exact Preorder.le_refl 1
      . intros y hy₀
        apply Set.mem_range.mp at hy₀
        obtain ⟨na, hna₀⟩ := hy₀
        refine le_of_lt ?_
        rw [← hna₀]
        exact hu₁ na
  have hu₄: ∃ cr, IsGLB scr cr := by
    refine Real.exists_isGLB ?_ ?_
    . refine Set.Nonempty.image fr ?_
      exact Set.range_nonempty fc
    . exact NNReal.bddBelow_coe sc
  obtain ⟨br, hbr₀⟩ := hu₃
  obtain ⟨cr, hcr₀⟩ := hu₄
  have h₇: ∀ n x, 0 < n → (f n x < f (n + 1) x → 1 - 1 / n < f n x) := by
    intros n x hn₀ hn₁
    rw [h₁ n x hn₀] at hn₁
    nth_rw 1 [← mul_one (f n x)] at hn₁
    suffices g₀: 1 < f n x + 1 / ↑n
    . exact sub_right_lt_of_lt_add g₀
    . refine lt_of_mul_lt_mul_left hn₁ ?_
      exact h₃ n x hn₀
  have h₈: ∀ n x, 0 < n → 0 < x → 1 - 1 / n < f n x → f n x < f (n + 1) x := by
    intros n x hn₀ hx₀ hn₁
    rw [h₁ n x hn₀]
    suffices g₀: 1 < f n x + 1 / ↑n
    . nth_rw 1 [← mul_one (f n x)]
      refine mul_lt_mul' ?_ g₀ ?_ ?_
      . exact Preorder.le_refl (f n x)
      . exact zero_le_one' ℝ
      . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
    . exact lt_add_of_tsub_lt_right hn₁
  have hbr₁: 0 < br := by
    exact imo_1985_p6_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb rfl hfb₀ hsb₀ fr rfl sbr rfl br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by exact hfb₀
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn (by rfl) fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀



lemma imo_1985_p6_main_2
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (n : ℕ)
  (x : NNReal)
  (hn : 0 < n):
   0 ≤ f n x := by
  refine Nat.le_induction ?_ ?_ n hn
  . rw [h₀ x]
    exact NNReal.zero_le_coe
  . intros d hd₀ hd₁
    rw [h₁ d x hd₀]
    refine mul_nonneg hd₁ ?_
    refine add_nonneg hd₁ ?_
    refine div_nonneg (by linarith) ?_
    exact Nat.cast_nonneg' d

lemma imo_1985_p6_main_3
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (x : NNReal):
   ∀ (n : ℕ), Nat.succ 0 ≤ n → 0 ≤ f n x → 0 ≤ f (n + 1) x := by
  intros d hd₀ hd₁
  rw [h₁ d x hd₀]
  refine mul_nonneg hd₁ ?_
  refine add_nonneg hd₁ ?_
  refine div_nonneg (by linarith) ?_
  exact Nat.cast_nonneg' d


lemma imo_1985_p6_main_4
  (f : ℕ → NNReal → ℝ)
  (x : NNReal)
  (d : ℕ)
  (hd₁ : 0 ≤ f d x):
   0 ≤ f d x * (f d x + 1 / ↑d) := by
  refine mul_nonneg hd₁ ?_
  refine add_nonneg hd₁ ?_
  refine div_nonneg (by linarith) ?_
  exact Nat.cast_nonneg' d


lemma imo_1985_p6_main_5
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have hmo₀: ∀ n, 0 < n → StrictMono (f n) := by
    intros n hn₀
    refine Monotone.strictMono_of_injective ?h₁ ?h₂
    . refine monotone_iff_forall_lt.mpr ?h₁.a
      intros a b hab
      refine le_of_lt ?_
      exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n a b hn₀ hab
    . intros p q hpq
      contrapose! hpq
      apply lt_or_gt_of_ne at hpq
      cases' hpq with hpq hpq
      . refine ne_of_lt ?_
        exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n p q hn₀ hpq
      . symm
        refine ne_of_lt ?_
        exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n q p hn₀ hpq
  have hmo₁: ∀ n, 0 < n → Function.Injective (f n) := by exact fun n a => StrictMono.injective (hmo₀ n a)
  let f₀: ℕ → NNReal → NNReal := fun n x => (f n x).toNNReal
  have hf₀: f₀ = fun n x => (f n x).toNNReal := by rfl
  have hf₁: ∀ n x, 0 < n → f n x = f₀ n x := by
    intros n x hn₀
    rw [hf₀]
    simp
    exact h₃ n x hn₀
  have hf₂: ∀ n x, 0 < n → f₀ n x = (f n x).toNNReal := by
    intros n x _
    rw [hf₀]
  have hmo₂: ∀ n, 0 < n → StrictMono (f₀ n) := by
    intros n hn₀
    refine imo_1985_p6_4 f h₃ ?_ f₀ hf₀ n hn₀
    exact fun n x y a a_1 => hmo₀ n a a_1
  let fi : ℕ → NNReal → NNReal := fun n => Function.invFun (f₀ n)
  have hmo₇: ∀ n, 0 < n → Function.RightInverse (fi n) (f₀ n) := by
    intros n hn₀
    refine Function.rightInverse_invFun ?_
    have h₄: ∀ n x y, 0 < n → x < y → f n x < f n y := by
      exact fun n x y a a_1 => imo_1985_p6_2 f h₀ h₁ h₂ h₃ n x y a a_1
    refine imo_1985_p6_7 f h₀ h₁ h₃ ?_ f₀ hf₂ hmo₂ ?_ n hn₀
    . exact fun n x a => imo_1985_p6_3 f h₀ h₁ h₄ n x a
    . intros m hm₀
      exact imo_1985_p6_6 f h₀ h₁ f₀ hf₀ m hm₀
  have hf₇: ∀ n x y, 0 < n → (f₀ n x = y ↔ fi n y = x) := by
    intros n x y hn₀
    constructor
    . intro hn₁
      rw [← hn₁, hf₀]
      have hn₂: (Function.invFun (f n)) ∘ (f n) = id := by exact Function.invFun_comp (hmo₁ n hn₀)
      rw [Function.comp_def (Function.invFun (f n)) (f n)] at hn₂
      exact imo_1985_p6_5 f hmo₁ f₀ hmo₂ fi rfl n x ((fun n x => (f n x).toNNReal) n x) hn₀ (hf₂ n x hn₀)
    . intro hn₁
      rw [← hn₁]
      exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ y))
  let sn : Set ℕ := Set.Ici 1
  let fb : ↑sn → NNReal := sn.restrict (fun (n:ℕ) => fi n (1 - 1 / (n:NNReal)))
  let fc : ↑sn → NNReal := sn.restrict (fun (n:ℕ) => fi n 1)
  have hsn₁: ∀ n:↑sn, ↑n ∈ sn ∧ 0 < (↑n:ℕ) := by
    intro n
    have hn₀: ↑n ∈ sn := by exact Subtype.coe_prop n
    constructor
    . exact Subtype.coe_prop n
    . exact hn₀
  have hfb₀: fb = fun (n:↑sn) => fi n (1 - 1 / (n:NNReal)) := by rfl
  have hfc₀: fc = fun (n:↑sn) => fi n 1 := by rfl
  have hfb₁: ∀ n:↑sn, f₀ n (fb n) = 1 - 1 / (n:NNReal) := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfb₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ (1 - 1 / (n:NNReal))))
  have hfc₁: ∀ n:↑sn, f₀ n (fc n) = 1 := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfc₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ 1))
  have hu₁: ∀ n:↑sn, fb n < 1 := by
    exact imo_1985_p6_8 f h₀ h₁ hmo₀ hmo₁ f₀ hf₂ sn fb hsn₁ hfb₁
  have hfc₂: ∀ n:↑sn, fb n < fc n := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    have g₀: f₀ n (fb n) < f₀ n (fc n) := by
      rw [hfb₁ n, hfc₁ n]
      simp
      exact (hsn₁ n).2
    exact (StrictMono.lt_iff_lt (hmo₂ n hn₀)).mp g₀
  have hfb₃: StrictMono fb := by
    refine StrictMonoOn.restrict ?_
    refine imo_1985_p6_9 f h₀ h₁ f₀ hf₁ hf₂ hmo₂ fi ?_ hmo₇ hf₇ _ (by rfl) sn (by rfl)
    intro x
    refine (hf₇ 1 x x (by linarith)).mp ?_
    rw [hf₂ 1 x (by linarith), h₀]
    exact Real.toNNReal_coe
  have hfc₃: StrictAnti fc := by
    have g₀: StrictAntiOn (fun n => fi n 1) sn := by
      refine strictAntiOn_Ici_of_lt_pred ?_
      intros m hm₀
      have hm₁: 0 < m - 1 := by exact Nat.zero_lt_sub_of_lt hm₀
      have hm₂: m = m - 1 + 1 := by rw [Nat.sub_add_cancel (le_of_lt hm₀)]
      have hm₃: 0 < m := by exact Nat.zero_lt_of_lt hm₀
      simp
      let x := fi m 1
      let y := fi (m - 1) 1
      have hx₀: x = fi m 1 := by rfl
      have hy₀: y = fi (m - 1) 1 := by rfl
      have hx₁: f₀ m x = 1 := by exact (hf₇ m x 1 (by linarith)).mpr hx₀.symm
      have hy₁: f₀ (m - 1) y = 1 := by
        exact (hf₇ (m - 1) y 1 hm₁).mpr hy₀.symm
      have hy₂: f (m - 1) y = 1 := by
        rw [hf₁ (m - 1) y hm₁, hy₁]
        exact rfl
      have hf: StrictMono (f m) := by exact hmo₀ m hm₃
      refine (StrictMono.lt_iff_lt hf).mp ?_
      rw [← hx₀, ← hy₀]
      rw [hf₁ m x hm₃, hf₁ m y hm₃]
      refine NNReal.coe_lt_coe.mpr ?_
      rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
      simp
      exact hm₀
    intros m n hmn
    rw [hfc₀]
    simp
    let mn : ℕ := ↑m
    let nn : ℕ := ↑n
    have hm₀: mn ∈ sn := by exact Subtype.coe_prop m
    have hn₀: nn ∈ sn := by exact Subtype.coe_prop n
    exact g₀ hm₀ hn₀ hmn
  let sb := Set.range fb
  let sc := Set.range fc
  have hsb₀: sb = Set.range fb := by rfl
  have hsc₀: sc = Set.range fc := by rfl
  let fr : NNReal → ℝ := fun x => x.toReal
  let sbr := Set.image fr sb
  let scr := Set.image fr sc
  have hu₃: ∃ br, IsLUB sbr br := by
    refine Real.exists_isLUB ?_ ?_
    . exact Set.Nonempty.of_subtype
    . refine NNReal.bddAbove_coe.mpr ?_
      refine (bddAbove_iff_exists_ge 1).mpr ?_
      use 1
      constructor
      . exact Preorder.le_refl 1
      . intros y hy₀
        apply Set.mem_range.mp at hy₀
        obtain ⟨na, hna₀⟩ := hy₀
        refine le_of_lt ?_
        rw [← hna₀]
        exact hu₁ na
  have hu₄: ∃ cr, IsGLB scr cr := by
    refine Real.exists_isGLB ?_ ?_
    . refine Set.Nonempty.image fr ?_
      exact Set.range_nonempty fc
    . exact NNReal.bddBelow_coe sc
  obtain ⟨br, hbr₀⟩ := hu₃
  obtain ⟨cr, hcr₀⟩ := hu₄
  have h₇: ∀ n x, 0 < n → (f n x < f (n + 1) x → 1 - 1 / n < f n x) := by
    intros n x hn₀ hn₁
    rw [h₁ n x hn₀] at hn₁
    nth_rw 1 [← mul_one (f n x)] at hn₁
    suffices g₀: 1 < f n x + 1 / ↑n
    . exact sub_right_lt_of_lt_add g₀
    . refine lt_of_mul_lt_mul_left hn₁ ?_
      exact h₃ n x hn₀
  have h₈: ∀ n x, 0 < n → 0 < x → 1 - 1 / n < f n x → f n x < f (n + 1) x := by
    intros n x hn₀ hx₀ hn₁
    rw [h₁ n x hn₀]
    suffices g₀: 1 < f n x + 1 / ↑n
    . nth_rw 1 [← mul_one (f n x)]
      refine mul_lt_mul' ?_ g₀ ?_ ?_
      . exact Preorder.le_refl (f n x)
      . exact zero_le_one' ℝ
      . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
    . exact lt_add_of_tsub_lt_right hn₁
  have hbr₁: 0 < br := by
    exact imo_1985_p6_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb rfl hfb₀ hsb₀ fr rfl sbr rfl br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by exact hfb₀
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn (by rfl) fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀



lemma imo_1985_p6_main_6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (n : ℕ)
  (hn₀ : 0 < n):
   StrictMono (f n) := by
  refine Monotone.strictMono_of_injective ?h₁ ?h₂
  . refine monotone_iff_forall_lt.mpr ?h₁.a
    intros a b hab
    refine le_of_lt ?_
    exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n a b hn₀ hab
  . intros p q hpq
    contrapose! hpq
    apply lt_or_gt_of_ne at hpq
    cases' hpq with hpq hpq
    . refine ne_of_lt ?_
      exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n p q hn₀ hpq
    . symm
      refine ne_of_lt ?_
      exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n q p hn₀ hpq

lemma imo_1985_p6_main_7
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (n : ℕ)
  (hn₀ : 0 < n):
   Monotone (f n) := by
  refine monotone_iff_forall_lt.mpr ?h₁.a
  intros a b hab
  refine le_of_lt ?_
  exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n a b hn₀ hab

lemma imo_1985_p6_main_8
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (n : ℕ)
  (hn₀ : 0 < n):
   Function.Injective (f n) := by
  intros p q hpq
  contrapose! hpq
  apply lt_or_gt_of_ne at hpq
  cases' hpq with hpq hpq
  . refine ne_of_lt ?_
    exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n p q hn₀ hpq
  . symm
    refine ne_of_lt ?_
    exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n q p hn₀ hpq

lemma imo_1985_p6_main_9
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (n : ℕ)
  (hn₀ : 0 < n)
  (p q : NNReal)
  (hpq : p ≠ q):
   f n p ≠ f n q := by
  apply lt_or_gt_of_ne at hpq
  cases' hpq with hpq hpq
  . refine ne_of_lt ?_
    exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n p q hn₀ hpq
  . symm
    refine ne_of_lt ?_
    exact imo_1985_p6_2 f h₀ h₁ h₂ h₃ n q p hn₀ hpq

lemma imo_1985_p6_main_10
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n)):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have hmo₁: ∀ n, 0 < n → Function.Injective (f n) := by exact fun n a => StrictMono.injective (hmo₀ n a)
  let f₀: ℕ → NNReal → NNReal := fun n x => (f n x).toNNReal
  have hf₀: f₀ = fun n x => (f n x).toNNReal := by rfl
  have hf₁: ∀ n x, 0 < n → f n x = f₀ n x := by
    intros n x hn₀
    rw [hf₀]
    simp
    exact h₃ n x hn₀
  have hf₂: ∀ n x, 0 < n → f₀ n x = (f n x).toNNReal := by
    intros n x _
    rw [hf₀]
  have hmo₂: ∀ n, 0 < n → StrictMono (f₀ n) := by
    intros n hn₀
    refine imo_1985_p6_4 f h₃ ?_ f₀ hf₀ n hn₀
    exact fun n x y a a_1 => hmo₀ n a a_1
  let fi : ℕ → NNReal → NNReal := fun n => Function.invFun (f₀ n)
  have hmo₇: ∀ n, 0 < n → Function.RightInverse (fi n) (f₀ n) := by
    intros n hn₀
    refine Function.rightInverse_invFun ?_
    have h₄: ∀ n x y, 0 < n → x < y → f n x < f n y := by
      exact fun n x y a a_1 => imo_1985_p6_2 f h₀ h₁ h₂ h₃ n x y a a_1
    refine imo_1985_p6_7 f h₀ h₁ h₃ ?_ f₀ hf₂ hmo₂ ?_ n hn₀
    . exact fun n x a => imo_1985_p6_3 f h₀ h₁ h₄ n x a
    . intros m hm₀
      exact imo_1985_p6_6 f h₀ h₁ f₀ hf₀ m hm₀
  have hf₇: ∀ n x y, 0 < n → (f₀ n x = y ↔ fi n y = x) := by
    intros n x y hn₀
    constructor
    . intro hn₁
      rw [← hn₁, hf₀]
      have hn₂: (Function.invFun (f n)) ∘ (f n) = id := by exact Function.invFun_comp (hmo₁ n hn₀)
      rw [Function.comp_def (Function.invFun (f n)) (f n)] at hn₂
      exact imo_1985_p6_5 f hmo₁ f₀ hmo₂ fi rfl n x ((fun n x => (f n x).toNNReal) n x) hn₀ (hf₂ n x hn₀)
    . intro hn₁
      rw [← hn₁]
      exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ y))
  let sn : Set ℕ := Set.Ici 1
  let fb : ↑sn → NNReal := sn.restrict (fun (n:ℕ) => fi n (1 - 1 / (n:NNReal)))
  let fc : ↑sn → NNReal := sn.restrict (fun (n:ℕ) => fi n 1)
  have hsn₁: ∀ n:↑sn, ↑n ∈ sn ∧ 0 < (↑n:ℕ) := by
    intro n
    have hn₀: ↑n ∈ sn := by exact Subtype.coe_prop n
    constructor
    . exact Subtype.coe_prop n
    . exact hn₀
  have hfb₀: fb = fun (n:↑sn) => fi n (1 - 1 / (n:NNReal)) := by rfl
  have hfc₀: fc = fun (n:↑sn) => fi n 1 := by rfl
  have hfb₁: ∀ n:↑sn, f₀ n (fb n) = 1 - 1 / (n:NNReal) := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfb₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ (1 - 1 / (n:NNReal))))
  have hfc₁: ∀ n:↑sn, f₀ n (fc n) = 1 := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfc₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ 1))
  have hu₁: ∀ n:↑sn, fb n < 1 := by
    exact imo_1985_p6_8 f h₀ h₁ hmo₀ hmo₁ f₀ hf₂ sn fb hsn₁ hfb₁
  have hfc₂: ∀ n:↑sn, fb n < fc n := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    have g₀: f₀ n (fb n) < f₀ n (fc n) := by
      rw [hfb₁ n, hfc₁ n]
      simp
      exact (hsn₁ n).2
    exact (StrictMono.lt_iff_lt (hmo₂ n hn₀)).mp g₀
  have hfb₃: StrictMono fb := by
    refine StrictMonoOn.restrict ?_
    refine imo_1985_p6_9 f h₀ h₁ f₀ hf₁ hf₂ hmo₂ fi ?_ hmo₇ hf₇ _ (by rfl) sn (by rfl)
    intro x
    refine (hf₇ 1 x x (by linarith)).mp ?_
    rw [hf₂ 1 x (by linarith), h₀]
    exact Real.toNNReal_coe
  have hfc₃: StrictAnti fc := by
    have g₀: StrictAntiOn (fun n => fi n 1) sn := by
      refine strictAntiOn_Ici_of_lt_pred ?_
      intros m hm₀
      have hm₁: 0 < m - 1 := by exact Nat.zero_lt_sub_of_lt hm₀
      have hm₂: m = m - 1 + 1 := by rw [Nat.sub_add_cancel (le_of_lt hm₀)]
      have hm₃: 0 < m := by exact Nat.zero_lt_of_lt hm₀
      simp
      let x := fi m 1
      let y := fi (m - 1) 1
      have hx₀: x = fi m 1 := by rfl
      have hy₀: y = fi (m - 1) 1 := by rfl
      have hx₁: f₀ m x = 1 := by exact (hf₇ m x 1 (by linarith)).mpr hx₀.symm
      have hy₁: f₀ (m - 1) y = 1 := by
        exact (hf₇ (m - 1) y 1 hm₁).mpr hy₀.symm
      have hy₂: f (m - 1) y = 1 := by
        rw [hf₁ (m - 1) y hm₁, hy₁]
        exact rfl
      have hf: StrictMono (f m) := by exact hmo₀ m hm₃
      refine (StrictMono.lt_iff_lt hf).mp ?_
      rw [← hx₀, ← hy₀]
      rw [hf₁ m x hm₃, hf₁ m y hm₃]
      refine NNReal.coe_lt_coe.mpr ?_
      rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
      simp
      exact hm₀
    intros m n hmn
    rw [hfc₀]
    simp
    let mn : ℕ := ↑m
    let nn : ℕ := ↑n
    have hm₀: mn ∈ sn := by exact Subtype.coe_prop m
    have hn₀: nn ∈ sn := by exact Subtype.coe_prop n
    exact g₀ hm₀ hn₀ hmn
  let sb := Set.range fb
  let sc := Set.range fc
  have hsb₀: sb = Set.range fb := by rfl
  have hsc₀: sc = Set.range fc := by rfl
  let fr : NNReal → ℝ := fun x => x.toReal
  let sbr := Set.image fr sb
  let scr := Set.image fr sc
  have hu₃: ∃ br, IsLUB sbr br := by
    refine Real.exists_isLUB ?_ ?_
    . exact Set.Nonempty.of_subtype
    . refine NNReal.bddAbove_coe.mpr ?_
      refine (bddAbove_iff_exists_ge 1).mpr ?_
      use 1
      constructor
      . exact Preorder.le_refl 1
      . intros y hy₀
        apply Set.mem_range.mp at hy₀
        obtain ⟨na, hna₀⟩ := hy₀
        refine le_of_lt ?_
        rw [← hna₀]
        exact hu₁ na
  have hu₄: ∃ cr, IsGLB scr cr := by
    refine Real.exists_isGLB ?_ ?_
    . refine Set.Nonempty.image fr ?_
      exact Set.range_nonempty fc
    . exact NNReal.bddBelow_coe sc
  obtain ⟨br, hbr₀⟩ := hu₃
  obtain ⟨cr, hcr₀⟩ := hu₄
  have h₇: ∀ n x, 0 < n → (f n x < f (n + 1) x → 1 - 1 / n < f n x) := by
    intros n x hn₀ hn₁
    rw [h₁ n x hn₀] at hn₁
    nth_rw 1 [← mul_one (f n x)] at hn₁
    suffices g₀: 1 < f n x + 1 / ↑n
    . exact sub_right_lt_of_lt_add g₀
    . refine lt_of_mul_lt_mul_left hn₁ ?_
      exact h₃ n x hn₀
  have h₈: ∀ n x, 0 < n → 0 < x → 1 - 1 / n < f n x → f n x < f (n + 1) x := by
    intros n x hn₀ hx₀ hn₁
    rw [h₁ n x hn₀]
    suffices g₀: 1 < f n x + 1 / ↑n
    . nth_rw 1 [← mul_one (f n x)]
      refine mul_lt_mul' ?_ g₀ ?_ ?_
      . exact Preorder.le_refl (f n x)
      . exact zero_le_one' ℝ
      . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
    . exact lt_add_of_tsub_lt_right hn₁
  have hbr₁: 0 < br := by
    exact imo_1985_p6_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb rfl hfb₀ hsb₀ fr rfl sbr rfl br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by exact hfb₀
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn (by rfl) fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀



lemma imo_1985_p6_main_11
  (f : ℕ → NNReal → ℝ)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal):
   ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x) := by
  intros n x hn₀
  rw [hf₀]
  simp
  exact h₃ n x hn₀

lemma imo_1985_p6_main_12
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x)):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have hf₂: ∀ n x, 0 < n → f₀ n x = (f n x).toNNReal := by
    intros n x _
    rw [hf₀]
  have hmo₂: ∀ n, 0 < n → StrictMono (f₀ n) := by
    intros n hn₀
    refine imo_1985_p6_4 f h₃ ?_ f₀ hf₀ n hn₀
    exact fun n x y a a_1 => hmo₀ n a a_1
  let fi : ℕ → NNReal → NNReal := fun n => Function.invFun (f₀ n)
  have hmo₇: ∀ n, 0 < n → Function.RightInverse (fi n) (f₀ n) := by
    intros n hn₀
    refine Function.rightInverse_invFun ?_
    have h₄: ∀ n x y, 0 < n → x < y → f n x < f n y := by
      exact fun n x y a a_1 => imo_1985_p6_2 f h₀ h₁ h₂ h₃ n x y a a_1
    refine imo_1985_p6_7 f h₀ h₁ h₃ ?_ f₀ hf₂ hmo₂ ?_ n hn₀
    . exact fun n x a => imo_1985_p6_3 f h₀ h₁ h₄ n x a
    . intros m hm₀
      exact imo_1985_p6_6 f h₀ h₁ f₀ hf₀ m hm₀
  have hf₇: ∀ n x y, 0 < n → (f₀ n x = y ↔ fi n y = x) := by
    intros n x y hn₀
    constructor
    . intro hn₁
      rw [← hn₁, hf₀]
      have hn₂: (Function.invFun (f n)) ∘ (f n) = id := by exact Function.invFun_comp (hmo₁ n hn₀)
      rw [Function.comp_def (Function.invFun (f n)) (f n)] at hn₂
      exact imo_1985_p6_5 f hmo₁ f₀ hmo₂ fi rfl n x ((fun n x => (f n x).toNNReal) n x) hn₀ (hf₂ n x hn₀)
    . intro hn₁
      rw [← hn₁]
      exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ y))
  let sn : Set ℕ := Set.Ici 1
  let fb : ↑sn → NNReal := sn.restrict (fun (n:ℕ) => fi n (1 - 1 / (n:NNReal)))
  let fc : ↑sn → NNReal := sn.restrict (fun (n:ℕ) => fi n 1)
  have hsn₁: ∀ n:↑sn, ↑n ∈ sn ∧ 0 < (↑n:ℕ) := by
    intro n
    have hn₀: ↑n ∈ sn := by exact Subtype.coe_prop n
    constructor
    . exact Subtype.coe_prop n
    . exact hn₀
  have hfb₀: fb = fun (n:↑sn) => fi n (1 - 1 / (n:NNReal)) := by rfl
  have hfc₀: fc = fun (n:↑sn) => fi n 1 := by rfl
  have hfb₁: ∀ n:↑sn, f₀ n (fb n) = 1 - 1 / (n:NNReal) := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfb₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ (1 - 1 / (n:NNReal))))
  have hfc₁: ∀ n:↑sn, f₀ n (fc n) = 1 := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfc₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ 1))
  have hu₁: ∀ n:↑sn, fb n < 1 := by
    exact imo_1985_p6_8 f h₀ h₁ hmo₀ hmo₁ f₀ hf₂ sn fb hsn₁ hfb₁
  have hfc₂: ∀ n:↑sn, fb n < fc n := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    have g₀: f₀ n (fb n) < f₀ n (fc n) := by
      rw [hfb₁ n, hfc₁ n]
      simp
      exact (hsn₁ n).2
    exact (StrictMono.lt_iff_lt (hmo₂ n hn₀)).mp g₀
  have hfb₃: StrictMono fb := by
    refine StrictMonoOn.restrict ?_
    refine imo_1985_p6_9 f h₀ h₁ f₀ hf₁ hf₂ hmo₂ fi ?_ hmo₇ hf₇ _ (by rfl) sn (by rfl)
    intro x
    refine (hf₇ 1 x x (by linarith)).mp ?_
    rw [hf₂ 1 x (by linarith), h₀]
    exact Real.toNNReal_coe
  have hfc₃: StrictAnti fc := by
    have g₀: StrictAntiOn (fun n => fi n 1) sn := by
      refine strictAntiOn_Ici_of_lt_pred ?_
      intros m hm₀
      have hm₁: 0 < m - 1 := by exact Nat.zero_lt_sub_of_lt hm₀
      have hm₂: m = m - 1 + 1 := by rw [Nat.sub_add_cancel (le_of_lt hm₀)]
      have hm₃: 0 < m := by exact Nat.zero_lt_of_lt hm₀
      simp
      let x := fi m 1
      let y := fi (m - 1) 1
      have hx₀: x = fi m 1 := by rfl
      have hy₀: y = fi (m - 1) 1 := by rfl
      have hx₁: f₀ m x = 1 := by exact (hf₇ m x 1 (by linarith)).mpr hx₀.symm
      have hy₁: f₀ (m - 1) y = 1 := by
        exact (hf₇ (m - 1) y 1 hm₁).mpr hy₀.symm
      have hy₂: f (m - 1) y = 1 := by
        rw [hf₁ (m - 1) y hm₁, hy₁]
        exact rfl
      have hf: StrictMono (f m) := by exact hmo₀ m hm₃
      refine (StrictMono.lt_iff_lt hf).mp ?_
      rw [← hx₀, ← hy₀]
      rw [hf₁ m x hm₃, hf₁ m y hm₃]
      refine NNReal.coe_lt_coe.mpr ?_
      rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
      simp
      exact hm₀
    intros m n hmn
    rw [hfc₀]
    simp
    let mn : ℕ := ↑m
    let nn : ℕ := ↑n
    have hm₀: mn ∈ sn := by exact Subtype.coe_prop m
    have hn₀: nn ∈ sn := by exact Subtype.coe_prop n
    exact g₀ hm₀ hn₀ hmn
  let sb := Set.range fb
  let sc := Set.range fc
  have hsb₀: sb = Set.range fb := by rfl
  have hsc₀: sc = Set.range fc := by rfl
  let fr : NNReal → ℝ := fun x => x.toReal
  let sbr := Set.image fr sb
  let scr := Set.image fr sc
  have hu₃: ∃ br, IsLUB sbr br := by
    refine Real.exists_isLUB ?_ ?_
    . exact Set.Nonempty.of_subtype
    . refine NNReal.bddAbove_coe.mpr ?_
      refine (bddAbove_iff_exists_ge 1).mpr ?_
      use 1
      constructor
      . exact Preorder.le_refl 1
      . intros y hy₀
        apply Set.mem_range.mp at hy₀
        obtain ⟨na, hna₀⟩ := hy₀
        refine le_of_lt ?_
        rw [← hna₀]
        exact hu₁ na
  have hu₄: ∃ cr, IsGLB scr cr := by
    refine Real.exists_isGLB ?_ ?_
    . refine Set.Nonempty.image fr ?_
      exact Set.range_nonempty fc
    . exact NNReal.bddBelow_coe sc
  obtain ⟨br, hbr₀⟩ := hu₃
  obtain ⟨cr, hcr₀⟩ := hu₄
  have h₇: ∀ n x, 0 < n → (f n x < f (n + 1) x → 1 - 1 / n < f n x) := by
    intros n x hn₀ hn₁
    rw [h₁ n x hn₀] at hn₁
    nth_rw 1 [← mul_one (f n x)] at hn₁
    suffices g₀: 1 < f n x + 1 / ↑n
    . exact sub_right_lt_of_lt_add g₀
    . refine lt_of_mul_lt_mul_left hn₁ ?_
      exact h₃ n x hn₀
  have h₈: ∀ n x, 0 < n → 0 < x → 1 - 1 / n < f n x → f n x < f (n + 1) x := by
    intros n x hn₀ hx₀ hn₁
    rw [h₁ n x hn₀]
    suffices g₀: 1 < f n x + 1 / ↑n
    . nth_rw 1 [← mul_one (f n x)]
      refine mul_lt_mul' ?_ g₀ ?_ ?_
      . exact Preorder.le_refl (f n x)
      . exact zero_le_one' ℝ
      . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
    . exact lt_add_of_tsub_lt_right hn₁
  have hbr₁: 0 < br := by
    exact imo_1985_p6_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb rfl hfb₀ hsb₀ fr rfl sbr rfl br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by exact hfb₀
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn (by rfl) fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀


lemma imo_1985_p6_main_13
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (n : ℕ)
  (hn₀ : 0 < n):
   Function.RightInverse (fi n) (f₀ n) := by
  rw [hfi]
  refine Function.rightInverse_invFun ?_
  have h₄: ∀ n x y, 0 < n → x < y → f n x < f n y := by
    exact fun n x y a a_1 => imo_1985_p6_2 f h₀ h₁ h₂ h₃ n x y a a_1
  refine imo_1985_p6_7 f h₀ h₁ h₃ ?_ f₀ hf₂ hmo₂ ?_ n hn₀
  . exact fun n x a => imo_1985_p6_3 f h₀ h₁ h₄ n x a
  . intros m hm₀
    exact imo_1985_p6_6 f h₀ h₁ f₀ hf₀ m hm₀

lemma imo_1985_p6_main_14
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (n : ℕ)
  (hn₀ : 0 < n)
  (h₄ : ∀ (n : ℕ) (x y : NNReal), 0 < n → x < y → f n x < f n y):
   Function.Surjective (f₀ n) := by
  refine imo_1985_p6_7 f h₀ h₁ h₃ ?_ f₀ hf₂ hmo₂ ?_ n hn₀
  . exact fun n x a => imo_1985_p6_3 f h₀ h₁ h₄ n x a
  . intros m hm₀
    exact imo_1985_p6_6 f h₀ h₁ f₀ hf₀ m hm₀

lemma imo_1985_p6_main_15
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n)):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have hf₇: ∀ n x y, 0 < n → (f₀ n x = y ↔ fi n y = x) := by
    intros n x y hn₀
    constructor
    . intro hn₁
      rw [← hn₁, hf₀]
      have hn₂: (Function.invFun (f n)) ∘ (f n) = id := by exact Function.invFun_comp (hmo₁ n hn₀)
      rw [Function.comp_def (Function.invFun (f n)) (f n)] at hn₂
      exact imo_1985_p6_5 f hmo₁ f₀ hmo₂ fi hfi n x ((fun n x => (f n x).toNNReal) n x) hn₀ (hf₂ n x hn₀)
    . intro hn₁
      rw [← hn₁]
      exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ y))
  let sn : Set ℕ := Set.Ici 1
  let fb : ↑sn → NNReal := sn.restrict (fun (n:ℕ) => fi n (1 - 1 / (n:NNReal)))
  let fc : ↑sn → NNReal := sn.restrict (fun (n:ℕ) => fi n 1)
  have hsn₁: ∀ n:↑sn, ↑n ∈ sn ∧ 0 < (↑n:ℕ) := by
    intro n
    have hn₀: ↑n ∈ sn := by exact Subtype.coe_prop n
    constructor
    . exact Subtype.coe_prop n
    . exact hn₀
  have hfb₀: fb = fun (n:↑sn) => fi n (1 - 1 / (n:NNReal)) := by rfl
  have hfc₀: fc = fun (n:↑sn) => fi n 1 := by rfl
  have hfb₁: ∀ n:↑sn, f₀ n (fb n) = 1 - 1 / (n:NNReal) := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfb₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ (1 - 1 / (n:NNReal))))
  have hfc₁: ∀ n:↑sn, f₀ n (fc n) = 1 := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfc₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ 1))
  have hu₁: ∀ n:↑sn, fb n < 1 := by
    exact imo_1985_p6_8 f h₀ h₁ hmo₀ hmo₁ f₀ hf₂ sn fb hsn₁ hfb₁
  have hfc₂: ∀ n:↑sn, fb n < fc n := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    have g₀: f₀ n (fb n) < f₀ n (fc n) := by
      rw [hfb₁ n, hfc₁ n]
      simp
      exact (hsn₁ n).2
    exact (StrictMono.lt_iff_lt (hmo₂ n hn₀)).mp g₀
  have hfb₃: StrictMono fb := by
    refine StrictMonoOn.restrict ?_
    refine imo_1985_p6_9 f h₀ h₁ f₀ hf₁ hf₂ hmo₂ fi ?_ hmo₇ hf₇ _ (by rfl) sn (by rfl)
    intro x
    refine (hf₇ 1 x x (by linarith)).mp ?_
    rw [hf₂ 1 x (by linarith), h₀]
    exact Real.toNNReal_coe
  have hfc₃: StrictAnti fc := by
    have g₀: StrictAntiOn (fun n => fi n 1) sn := by
      refine strictAntiOn_Ici_of_lt_pred ?_
      intros m hm₀
      have hm₁: 0 < m - 1 := by exact Nat.zero_lt_sub_of_lt hm₀
      have hm₂: m = m - 1 + 1 := by rw [Nat.sub_add_cancel (le_of_lt hm₀)]
      have hm₃: 0 < m := by exact Nat.zero_lt_of_lt hm₀
      simp
      let x := fi m 1
      let y := fi (m - 1) 1
      have hx₀: x = fi m 1 := by rfl
      have hy₀: y = fi (m - 1) 1 := by rfl
      have hx₁: f₀ m x = 1 := by exact (hf₇ m x 1 (by linarith)).mpr hx₀.symm
      have hy₁: f₀ (m - 1) y = 1 := by
        exact (hf₇ (m - 1) y 1 hm₁).mpr hy₀.symm
      have hy₂: f (m - 1) y = 1 := by
        rw [hf₁ (m - 1) y hm₁, hy₁]
        exact rfl
      have hf: StrictMono (f m) := by exact hmo₀ m hm₃
      refine (StrictMono.lt_iff_lt hf).mp ?_
      rw [← hx₀, ← hy₀]
      rw [hf₁ m x hm₃, hf₁ m y hm₃]
      refine NNReal.coe_lt_coe.mpr ?_
      rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
      simp
      exact hm₀
    intros m n hmn
    rw [hfc₀]
    simp
    let mn : ℕ := ↑m
    let nn : ℕ := ↑n
    have hm₀: mn ∈ sn := by exact Subtype.coe_prop m
    have hn₀: nn ∈ sn := by exact Subtype.coe_prop n
    exact g₀ hm₀ hn₀ hmn
  let sb := Set.range fb
  let sc := Set.range fc
  have hsb₀: sb = Set.range fb := by rfl
  have hsc₀: sc = Set.range fc := by rfl
  let fr : NNReal → ℝ := fun x => x.toReal
  let sbr := Set.image fr sb
  let scr := Set.image fr sc
  have hu₃: ∃ br, IsLUB sbr br := by
    refine Real.exists_isLUB ?_ ?_
    . exact Set.Nonempty.of_subtype
    . refine NNReal.bddAbove_coe.mpr ?_
      refine (bddAbove_iff_exists_ge 1).mpr ?_
      use 1
      constructor
      . exact Preorder.le_refl 1
      . intros y hy₀
        apply Set.mem_range.mp at hy₀
        obtain ⟨na, hna₀⟩ := hy₀
        refine le_of_lt ?_
        rw [← hna₀]
        exact hu₁ na
  have hu₄: ∃ cr, IsGLB scr cr := by
    refine Real.exists_isGLB ?_ ?_
    . refine Set.Nonempty.image fr ?_
      exact Set.range_nonempty fc
    . exact NNReal.bddBelow_coe sc
  obtain ⟨br, hbr₀⟩ := hu₃
  obtain ⟨cr, hcr₀⟩ := hu₄
  have h₇: ∀ n x, 0 < n → (f n x < f (n + 1) x → 1 - 1 / n < f n x) := by
    intros n x hn₀ hn₁
    rw [h₁ n x hn₀] at hn₁
    nth_rw 1 [← mul_one (f n x)] at hn₁
    suffices g₀: 1 < f n x + 1 / ↑n
    . exact sub_right_lt_of_lt_add g₀
    . refine lt_of_mul_lt_mul_left hn₁ ?_
      exact h₃ n x hn₀
  have h₈: ∀ n x, 0 < n → 0 < x → 1 - 1 / n < f n x → f n x < f (n + 1) x := by
    intros n x hn₀ hx₀ hn₁
    rw [h₁ n x hn₀]
    suffices g₀: 1 < f n x + 1 / ↑n
    . nth_rw 1 [← mul_one (f n x)]
      refine mul_lt_mul' ?_ g₀ ?_ ?_
      . exact Preorder.le_refl (f n x)
      . exact zero_le_one' ℝ
      . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
    . exact lt_add_of_tsub_lt_right hn₁
  have hbr₁: 0 < br := by
    exact imo_1985_p6_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb rfl hfb₀ hsb₀ fr rfl sbr rfl br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by rw [hfb₀, hfi]
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn (by rfl) fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀


lemma imo_1985_p6_main_16
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (n : ℕ)
  (x y : NNReal)
  (hn₀ : 0 < n):
   f₀ n x = y ↔ fi n y = x := by
  constructor
  . intro hn₁
    rw [← hn₁, hf₀]
    have hn₂: (Function.invFun (f n)) ∘ (f n) = id := by exact Function.invFun_comp (hmo₁ n hn₀)
    rw [Function.comp_def (Function.invFun (f n)) (f n)] at hn₂
    exact imo_1985_p6_5 f hmo₁ f₀ hmo₂ fi hfi n x ((fun n x => (f n x).toNNReal) n x) hn₀ (hf₂ n x hn₀)
  . intro hn₁
    rw [← hn₁]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ y))


lemma imo_1985_p6_main_17
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₀ : f₀ = fun n x ↦ (f n x).toNNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (n : ℕ)
  (x y : NNReal)
  (hn₀ : 0 < n)
  (hn₁ : f₀ n x = y):
   fi n y = x := by
  rw [← hn₁, hf₀]
  have hn₂: (Function.invFun (f n)) ∘ (f n) = id := by exact Function.invFun_comp (hmo₁ n hn₀)
  rw [Function.comp_def (Function.invFun (f n)) (f n)] at hn₂
  exact imo_1985_p6_5 f hmo₁ f₀ hmo₂ fi hfi n x ((fun n x => (f n x).toNNReal) n x) hn₀ (hf₂ n x hn₀)

lemma imo_1985_p6_main_18
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (n : ℕ)
  (x : NNReal)
  (hn₀ : 0 < n) :
   fi n ((fun n x ↦ (f n x).toNNReal) n x) = x := by
  have hn₂: (Function.invFun (f n)) ∘ (f n) = id := by exact Function.invFun_comp (hmo₁ n hn₀)
  rw [Function.comp_def (Function.invFun (f n)) (f n)] at hn₂
  exact imo_1985_p6_5 f hmo₁ f₀ hmo₂ fi hfi n x ((fun n x => (f n x).toNNReal) n x) hn₀ (hf₂ n x hn₀)

lemma imo_1985_p6_main_19
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (n : ℕ)
  (x : NNReal)
  (hn₀ : 0 < n)
  (hn₂ : Function.invFun (f n) ∘ f n = id):
   fi n ((fun n x ↦ (f n x).toNNReal) n x) = x := by
  rw [Function.comp_def (Function.invFun (f n)) (f n)] at hn₂
  exact imo_1985_p6_5 f hmo₁ f₀ hmo₂ fi hfi n x ((fun n x => (f n x).toNNReal) n x) hn₀ (hf₂ n x hn₀)

lemma imo_1985_p6_main_20
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (n : ℕ)
  (x y : NNReal)
  (hn₀ : 0 < n):
   fi n y = x → f₀ n x = y := by
  intro hn₁
  rw [← hn₁]
  exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ y))

lemma imo_1985_p6_main_21
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₀: fb = sn.restrict fun n => fi n (1 - 1 / (n:NNReal)))
  (hfc₀ : fc = sn.restrict fun n ↦ fi n 1):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have hsn₁: ∀ n:↑sn, ↑n ∈ sn ∧ 0 < (↑n:ℕ) := by
    intro n
    constructor
    . exact Subtype.coe_prop n
    . refine Nat.lt_of_succ_le ?_
      refine Set.mem_Ici.mp ?_
      rw [← hsn]
      exact n.2
  have hfb₁: ∀ n:↑sn, f₀ n (fb n) = 1 - 1 / (n:NNReal) := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfb₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ (1 - 1 / (n:NNReal))))
  have hfc₁: ∀ n:↑sn, f₀ n (fc n) = 1 := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    rw [hfc₀]
    exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ 1))
  have hu₁: ∀ n:↑sn, fb n < 1 := by
    exact imo_1985_p6_8 f h₀ h₁ hmo₀ hmo₁ f₀ hf₂ sn fb hsn₁ hfb₁
  have hfc₂: ∀ n:↑sn, fb n < fc n := by
    intros n
    have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
    have g₀: f₀ n (fb n) < f₀ n (fc n) := by
      rw [hfb₁ n, hfc₁ n]
      simp
      exact (hsn₁ n).2
    exact (StrictMono.lt_iff_lt (hmo₂ n hn₀)).mp g₀
  have hfb₃: StrictMono fb := by
    rw [hfb₀]
    refine StrictMonoOn.restrict ?_
    refine imo_1985_p6_9 f h₀ h₁ f₀ hf₁ hf₂ hmo₂ fi ?_ hmo₇ hf₇ _ (by rfl) sn hsn
    intro x
    refine (hf₇ 1 x x (by linarith)).mp ?_
    rw [hf₂ 1 x (by linarith), h₀]
    exact Real.toNNReal_coe
  have hfc₃: StrictAnti fc := by
    have g₀: StrictAntiOn (fun n => fi n 1) sn := by
      rw [hsn]
      refine strictAntiOn_Ici_of_lt_pred ?_
      intros m hm₀
      have hm₁: 0 < m - 1 := by exact Nat.zero_lt_sub_of_lt hm₀
      have hm₂: m = m - 1 + 1 := by rw [Nat.sub_add_cancel (le_of_lt hm₀)]
      have hm₃: 0 < m := by exact Nat.zero_lt_of_lt hm₀
      simp
      let x := fi m 1
      let y := fi (m - 1) 1
      have hx₀: x = fi m 1 := by rfl
      have hy₀: y = fi (m - 1) 1 := by rfl
      have hx₁: f₀ m x = 1 := by exact (hf₇ m x 1 (by linarith)).mpr hx₀.symm
      have hy₁: f₀ (m - 1) y = 1 := by
        exact (hf₇ (m - 1) y 1 hm₁).mpr hy₀.symm
      have hy₂: f (m - 1) y = 1 := by
        rw [hf₁ (m - 1) y hm₁, hy₁]
        exact rfl
      have hf: StrictMono (f m) := by exact hmo₀ m hm₃
      refine (StrictMono.lt_iff_lt hf).mp ?_
      rw [← hx₀, ← hy₀]
      rw [hf₁ m x hm₃, hf₁ m y hm₃]
      refine NNReal.coe_lt_coe.mpr ?_
      rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
      simp
      exact hm₀
    intros m n hmn
    rw [hfc₀]
    simp
    let mn : ℕ := ↑m
    let nn : ℕ := ↑n
    have hm₀: mn ∈ sn := by exact Subtype.coe_prop m
    have hn₀: nn ∈ sn := by exact Subtype.coe_prop n
    exact g₀ hm₀ hn₀ hmn
  let sb := Set.range fb
  let sc := Set.range fc
  have hsb₀: sb = Set.range fb := by rfl
  have hsc₀: sc = Set.range fc := by rfl
  let fr : NNReal → ℝ := fun x => x.toReal
  let sbr := Set.image fr sb
  let scr := Set.image fr sc
  have hsn₂: Nonempty ↑sn := by
    rw [hsn]
    exact Set.nonempty_Ici_subtype
  have hu₃: ∃ br, IsLUB sbr br := by
    refine Real.exists_isLUB ?_ ?_
    . exact Set.Nonempty.of_subtype
    . refine NNReal.bddAbove_coe.mpr ?_
      refine (bddAbove_iff_exists_ge 1).mpr ?_
      use 1
      constructor
      . exact Preorder.le_refl 1
      . intros y hy₀
        apply Set.mem_range.mp at hy₀
        obtain ⟨na, hna₀⟩ := hy₀
        refine le_of_lt ?_
        rw [← hna₀]
        exact hu₁ na
  have hu₄: ∃ cr, IsGLB scr cr := by
    refine Real.exists_isGLB ?_ ?_
    . refine Set.Nonempty.image fr ?_
      rw [hsc₀]
      exact Set.range_nonempty fc
    . exact NNReal.bddBelow_coe sc
  obtain ⟨br, hbr₀⟩ := hu₃
  obtain ⟨cr, hcr₀⟩ := hu₄
  have h₇: ∀ n x, 0 < n → (f n x < f (n + 1) x → 1 - 1 / n < f n x) := by
    intros n x hn₀ hn₁
    rw [h₁ n x hn₀] at hn₁
    nth_rw 1 [← mul_one (f n x)] at hn₁
    suffices g₀: 1 < f n x + 1 / ↑n
    . exact sub_right_lt_of_lt_add g₀
    . refine lt_of_mul_lt_mul_left hn₁ ?_
      exact h₃ n x hn₀
  have h₈: ∀ n x, 0 < n → 0 < x → 1 - 1 / n < f n x → f n x < f (n + 1) x := by
    intros n x hn₀ hx₀ hn₁
    rw [h₁ n x hn₀]
    suffices g₀: 1 < f n x + 1 / ↑n
    . nth_rw 1 [← mul_one (f n x)]
      refine mul_lt_mul' ?_ g₀ ?_ ?_
      . exact Preorder.le_refl (f n x)
      . exact zero_le_one' ℝ
      . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
    . exact lt_add_of_tsub_lt_right hn₁
  have hbr₁: 0 < br := by
    exact imo_1985_p6_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb hsn hfb₀ hsb₀ fr rfl sbr rfl br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by
      rw [hfb₀, hfi]
      exact rfl
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn hsn fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀


lemma imo_1985_p6_main_22
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (n : ↑sn):
  n.1 ∈ sn ∧ 0 < n.1 := by
  constructor
  . exact Subtype.coe_prop n
  . refine Nat.lt_of_succ_le ?_
    refine Set.mem_Ici.mp ?_
    rw [← hsn]
    exact n.2

lemma imo_1985_p6_main_23
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hsn₁ : ∀ (n : ↑sn), n.1 ∈ sn ∧ 0 < n.1)
  (hfb₀ : fb = sn.restrict fun n ↦ fi (↑n) (1 - 1 / ↑↑n)) :
   ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n := by
  intros n
  have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
  rw [hfb₀]
  exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ (1 - 1 / (n:NNReal))))


lemma imo_1985_p6_main_24
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (hsn₁ : ∀ (n : ↑sn), n.1 ∈ sn ∧ 0 < n.1)
  (hfc₀ : fc = sn.restrict fun n ↦ fi (↑n) 1)
  (n : ↑sn):
   f₀ (↑n) (fc n) = 1 := by
  have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
  rw [hfc₀]
  exact hmo₁ n hn₀ (congrArg (f n) (hmo₇ n hn₀ 1))

lemma imo_1985_p6_main_25
  (f₀ : ℕ → NNReal → NNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hsn₁ : ∀ (n : ↑sn), n.1 ∈ sn ∧ 0 < n.1)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1) :
   ∀ (n : ↑sn), fb n < fc n := by
  intros n
  have hn₀: 0 < (n:ℕ) := by exact (hsn₁ n).2
  have g₀: f₀ n (fb n) < f₀ n (fc n) := by
    rw [hfb₁ n, hfc₁ n]
    simp
    exact (hsn₁ n).2
  exact (StrictMono.lt_iff_lt (hmo₂ n hn₀)).mp g₀


lemma imo_1985_p6_main_26
  (f₀ : ℕ → NNReal → NNReal)
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hsn₁ : ∀ (n : ↑sn), n.1 ∈ sn ∧ 0 < n.1)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (n : ↑sn) :
   f₀ (↑n) (fb n) < f₀ (↑n) (fc n) := by
  rw [hfb₁ n, hfc₁ n]
  simp
  exact (hsn₁ n).2

lemma imo_1985_p6_main_27
  (f₀ : ℕ → NNReal → NNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (g₀ : f₀ (↑n) (fb n) < f₀ (↑n) (fc n)):
   fb n < fc n := by
  refine (StrictMono.lt_iff_lt ?_).mp g₀
  exact hmo₂ n hn₀

lemma imo_1985_p6_main_28
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₀ : fb = sn.restrict fun n ↦ fi (↑n) (1 - 1 / ↑↑n))
  (hfc₀ : fc = sn.restrict fun n ↦ fi (↑n) 1)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hu₁ : ∀ (n : ↑sn), fb n < 1)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have hfb₃: StrictMono fb := by
    rw [hfb₀]
    refine StrictMonoOn.restrict ?_
    refine imo_1985_p6_9 f h₀ h₁ f₀ hf₁ hf₂ hmo₂ fi ?_ hmo₇ hf₇ _ (by rfl) sn hsn
    intro x
    refine (hf₇ 1 x x (by linarith)).mp ?_
    rw [hf₂ 1 x (by linarith), h₀]
    exact Real.toNNReal_coe
  have hfc₃: StrictAnti fc := by
    have g₀: StrictAntiOn (fun n => fi n 1) sn := by
      rw [hsn]
      refine strictAntiOn_Ici_of_lt_pred ?_
      intros m hm₀
      have hm₁: 0 < m - 1 := by exact Nat.zero_lt_sub_of_lt hm₀
      have hm₂: m = m - 1 + 1 := by rw [Nat.sub_add_cancel (le_of_lt hm₀)]
      have hm₃: 0 < m := by exact Nat.zero_lt_of_lt hm₀
      simp
      let x := fi m 1
      let y := fi (m - 1) 1
      have hx₀: x = fi m 1 := by rfl
      have hy₀: y = fi (m - 1) 1 := by rfl
      have hx₁: f₀ m x = 1 := by exact (hf₇ m x 1 (by linarith)).mpr hx₀.symm
      have hy₁: f₀ (m - 1) y = 1 := by
        exact (hf₇ (m - 1) y 1 hm₁).mpr hy₀.symm
      have hy₂: f (m - 1) y = 1 := by
        rw [hf₁ (m - 1) y hm₁, hy₁]
        exact rfl
      have hf: StrictMono (f m) := by exact hmo₀ m hm₃
      refine (StrictMono.lt_iff_lt hf).mp ?_
      rw [← hx₀, ← hy₀]
      rw [hf₁ m x hm₃, hf₁ m y hm₃]
      refine NNReal.coe_lt_coe.mpr ?_
      rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
      simp
      exact hm₀
    intros m n hmn
    rw [hfc₀]
    simp
    let mn : ℕ := ↑m
    let nn : ℕ := ↑n
    have hm₀: mn ∈ sn := by exact Subtype.coe_prop m
    have hn₀: nn ∈ sn := by exact Subtype.coe_prop n
    exact g₀ hm₀ hn₀ hmn
  let sb := Set.range fb
  let sc := Set.range fc
  have hsb₀: sb = Set.range fb := by rfl
  have hsc₀: sc = Set.range fc := by rfl
  let fr : NNReal → ℝ := fun x => x.toReal
  let sbr := Set.image fr sb
  let scr := Set.image fr sc
  have hsn₂: Nonempty ↑sn := by
    rw [hsn]
    exact Set.nonempty_Ici_subtype
  have hu₃: ∃ br, IsLUB sbr br := by
    refine Real.exists_isLUB ?_ ?_
    . exact Set.Nonempty.of_subtype
    . refine NNReal.bddAbove_coe.mpr ?_
      refine (bddAbove_iff_exists_ge 1).mpr ?_
      use 1
      constructor
      . exact Preorder.le_refl 1
      . intros y hy₀
        apply Set.mem_range.mp at hy₀
        obtain ⟨na, hna₀⟩ := hy₀
        refine le_of_lt ?_
        rw [← hna₀]
        exact hu₁ na
  have hu₄: ∃ cr, IsGLB scr cr := by
    refine Real.exists_isGLB ?_ ?_
    . refine Set.Nonempty.image fr ?_
      exact Set.range_nonempty fc
    . exact NNReal.bddBelow_coe sc
  obtain ⟨br, hbr₀⟩ := hu₃
  obtain ⟨cr, hcr₀⟩ := hu₄
  have h₇: ∀ n x, 0 < n → (f n x < f (n + 1) x → 1 - 1 / n < f n x) := by
    intros n x hn₀ hn₁
    rw [h₁ n x hn₀] at hn₁
    nth_rw 1 [← mul_one (f n x)] at hn₁
    suffices g₀: 1 < f n x + 1 / ↑n
    . exact sub_right_lt_of_lt_add g₀
    . refine lt_of_mul_lt_mul_left hn₁ ?_
      exact h₃ n x hn₀
  have h₈: ∀ n x, 0 < n → 0 < x → 1 - 1 / n < f n x → f n x < f (n + 1) x := by
    intros n x hn₀ hx₀ hn₁
    rw [h₁ n x hn₀]
    suffices g₀: 1 < f n x + 1 / ↑n
    . nth_rw 1 [← mul_one (f n x)]
      refine mul_lt_mul' ?_ g₀ ?_ ?_
      . exact Preorder.le_refl (f n x)
      . exact zero_le_one' ℝ
      . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
    . exact lt_add_of_tsub_lt_right hn₁
  have hbr₁: 0 < br := by
    exact imo_1985_p6_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb hsn hfb₀ hsb₀ fr rfl sbr rfl br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by
      rw [hfb₀, hfi]
      exact rfl
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn hsn fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀


lemma imo_1985_p6_main_29
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb : ↑sn → NNReal)
  (hfb₀ : fb = sn.restrict fun n ↦ fi (↑n) (1 - 1 / ↑↑n)) :
  StrictMono fb := by
  rw [hfb₀]
  refine StrictMonoOn.restrict ?_
  refine imo_1985_p6_9 f h₀ h₁ f₀ hf₁ hf₂ hmo₂ fi ?_ hmo₇ hf₇ _ (by rfl) sn hsn
  intro x
  refine (hf₇ 1 x x (by linarith)).mp ?_
  rw [hf₂ 1 x (by linarith), h₀]
  exact Real.toNNReal_coe

lemma imo_1985_p6_main_30
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1):
  StrictMonoOn (fun n ↦ fi n (1 - 1 / ↑n)) sn := by
  refine imo_1985_p6_9 f h₀ h₁ f₀ hf₁ hf₂ hmo₂ fi ?_ hmo₇ hf₇ _ (by rfl) sn hsn
  intro x
  refine (hf₇ 1 x x (by linarith)).mp ?_
  rw [hf₂ 1 x (by linarith), h₀]
  exact Real.toNNReal_coe

lemma imo_1985_p6_main_31
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (x : NNReal):
   fi 1 x = x := by
  refine (hf₇ 1 x x (by linarith)).mp ?_
  rw [hf₂ 1 x (by linarith), h₀]
  exact Real.toNNReal_coe

lemma imo_1985_p6_main_32
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₀ : fc = sn.restrict fun n ↦ fi (↑n) 1):
   StrictAnti fc := by
  have g₀: StrictAntiOn (fun n => fi n 1) sn := by
    rw [hsn]
    refine strictAntiOn_Ici_of_lt_pred ?_
    intros m hm₀
    have hm₁: 0 < m - 1 := by exact Nat.zero_lt_sub_of_lt hm₀
    have hm₂: m = m - 1 + 1 := by rw [Nat.sub_add_cancel (le_of_lt hm₀)]
    have hm₃: 0 < m := by exact Nat.zero_lt_of_lt hm₀
    simp
    let x := fi m 1
    let y := fi (m - 1) 1
    have hx₀: x = fi m 1 := by rfl
    have hy₀: y = fi (m - 1) 1 := by rfl
    have hx₁: f₀ m x = 1 := by exact (hf₇ m x 1 (by linarith)).mpr hx₀.symm
    have hy₁: f₀ (m - 1) y = 1 := by
      exact (hf₇ (m - 1) y 1 hm₁).mpr hy₀.symm
    have hy₂: f (m - 1) y = 1 := by
      rw [hf₁ (m - 1) y hm₁, hy₁]
      exact rfl
    have hf: StrictMono (f m) := by exact hmo₀ m hm₃
    refine (StrictMono.lt_iff_lt hf).mp ?_
    rw [← hx₀, ← hy₀]
    rw [hf₁ m x hm₃, hf₁ m y hm₃]
    refine NNReal.coe_lt_coe.mpr ?_
    rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
    simp
    exact hm₀
  intros m n hmn
  rw [hfc₀]
  simp
  let mn : ℕ := ↑m
  let nn : ℕ := ↑n
  have hm₀: mn ∈ sn := by exact Subtype.coe_prop m
  have hn₀: nn ∈ sn := by exact Subtype.coe_prop n
  exact g₀ hm₀ hn₀ hmn

lemma imo_1985_p6_main_33
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1) :
  StrictAntiOn (fun n ↦ fi n 1) sn := by
  rw [hsn]
  refine strictAntiOn_Ici_of_lt_pred ?_
  intros m hm₀
  have hm₁: 0 < m - 1 := by exact Nat.zero_lt_sub_of_lt hm₀
  have hm₂: m = m - 1 + 1 := by rw [Nat.sub_add_cancel (le_of_lt hm₀)]
  have hm₃: 0 < m := by exact Nat.zero_lt_of_lt hm₀
  simp
  let x := fi m 1
  let y := fi (m - 1) 1
  have hx₀: x = fi m 1 := by rfl
  have hy₀: y = fi (m - 1) 1 := by rfl
  have hx₁: f₀ m x = 1 := by exact (hf₇ m x 1 (by linarith)).mpr hx₀.symm
  have hy₁: f₀ (m - 1) y = 1 := by
    exact (hf₇ (m - 1) y 1 hm₁).mpr hy₀.symm
  have hy₂: f (m - 1) y = 1 := by
    rw [hf₁ (m - 1) y hm₁, hy₁]
    exact rfl
  have hf: StrictMono (f m) := by exact hmo₀ m hm₃
  refine (StrictMono.lt_iff_lt hf).mp ?_
  rw [← hx₀, ← hy₀]
  rw [hf₁ m x hm₃, hf₁ m y hm₃]
  refine NNReal.coe_lt_coe.mpr ?_
  rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
  simp
  exact hm₀

lemma imo_1985_p6_main_34
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (m : ℕ)
  (hm₀ : 1 < m):
   fi m 1 < fi (Order.pred m) 1 := by
  have hm₁: 0 < m - 1 := by exact Nat.zero_lt_sub_of_lt hm₀
  have hm₂: m = m - 1 + 1 := by rw [Nat.sub_add_cancel (le_of_lt hm₀)]
  have hm₃: 0 < m := by exact Nat.zero_lt_of_lt hm₀
  simp
  let x := fi m 1
  let y := fi (m - 1) 1
  have hx₀: x = fi m 1 := by rfl
  have hy₀: y = fi (m - 1) 1 := by rfl
  have hx₁: f₀ m x = 1 := by exact (hf₇ m x 1 (by linarith)).mpr hx₀.symm
  have hy₁: f₀ (m - 1) y = 1 := by
    exact (hf₇ (m - 1) y 1 hm₁).mpr hy₀.symm
  have hy₂: f (m - 1) y = 1 := by
    rw [hf₁ (m - 1) y hm₁, hy₁]
    exact rfl
  have hf: StrictMono (f m) := by exact hmo₀ m hm₃
  refine (StrictMono.lt_iff_lt hf).mp ?_
  rw [← hx₀, ← hy₀]
  rw [hf₁ m x hm₃, hf₁ m y hm₃]
  refine NNReal.coe_lt_coe.mpr ?_
  rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
  simp
  exact hm₀

lemma imo_1985_p6_main_35
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (m : ℕ)
  (hm₀ : 1 < m)
  (hm₁ : 0 < m - 1)
  (hm₂ : m = m - 1 + 1)
  (hm₃ : 0 < m):
   fi m 1 < fi (m - 1) 1 := by
  let x := fi m 1
  let y := fi (m - 1) 1
  have hx₀: x = fi m 1 := by rfl
  have hy₀: y = fi (m - 1) 1 := by rfl
  have hx₁: f₀ m x = 1 := by exact (hf₇ m x 1 (by linarith)).mpr hx₀.symm
  have hy₁: f₀ (m - 1) y = 1 := by
    exact (hf₇ (m - 1) y 1 hm₁).mpr hy₀.symm
  have hy₂: f (m - 1) y = 1 := by
    rw [hf₁ (m - 1) y hm₁, hy₁]
    exact rfl
  have hf: StrictMono (f m) := by exact hmo₀ m hm₃
  refine (StrictMono.lt_iff_lt hf).mp ?_
  rw [← hx₀, ← hy₀]
  rw [hf₁ m x hm₃, hf₁ m y hm₃]
  refine NNReal.coe_lt_coe.mpr ?_
  rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
  simp
  exact hm₀

lemma imo_1985_p6_main_36
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (m : ℕ)
  (hm₀ : 1 < m)
  (hm₁ : 0 < m - 1)
  (hm₂ : m = m - 1 + 1)
  (hm₃ : 0 < m)
  (x : NNReal := fi m 1)
  (y : NNReal := fi (m - 1) 1)
  (hx₀ : x = fi m 1)
  (hy₀ : y = fi (m - 1) 1)
  (hx₁ : f₀ m x = 1)
  (hy₂ : f (m - 1) y = 1):
   fi m 1 < fi (m - 1) 1 := by
  have hf: StrictMono (f m) := by exact hmo₀ m hm₃
  refine (StrictMono.lt_iff_lt hf).mp ?_
  rw [← hx₀, ← hy₀]
  rw [hf₁ m x hm₃, hf₁ m y hm₃]
  refine NNReal.coe_lt_coe.mpr ?_
  rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
  simp
  exact hm₀

lemma imo_1985_p6_main_37
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (m : ℕ)
  (hm₀ : 1 < m)
  (hm₁ : 0 < m - 1)
  (hm₂ : m = m - 1 + 1)
  (hm₃ : 0 < m)
  (x : NNReal := fi m 1)
  (y : NNReal := fi (m - 1) 1)
  (hx₀ : x = fi m 1)
  (hy₀ : y = fi (m - 1) 1)
  (hx₁ : f₀ m x = 1)
  (hy₂ : f (m - 1) y = 1)
  (hf : StrictMono (f m)):
   fi m 1 < fi (m - 1) 1 := by
  refine (StrictMono.lt_iff_lt hf).mp ?_
  rw [← hx₀, ← hy₀]
  rw [hf₁ m x hm₃, hf₁ m y hm₃]
  refine NNReal.coe_lt_coe.mpr ?_
  rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
  simp
  exact hm₀

lemma imo_1985_p6_main_38
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (m : ℕ)
  (hm₀ : 1 < m)
  (hm₁ : 0 < m - 1)
  (hm₂ : m = m - 1 + 1)
  (hm₃ : 0 < m)
  (x : NNReal := fi m 1)
  (y : NNReal := fi (m - 1) 1)
  (hx₀ : x = fi m 1)
  (hy₀ : y = fi (m - 1) 1)
  (hx₁ : f₀ m x = 1)
  (hy₂ : f (m - 1) y = 1):
   f m (fi m 1) < f m (fi (m - 1) 1) := by
  rw [← hx₀, ← hy₀]
  rw [hf₁ m x hm₃, hf₁ m y hm₃]
  refine NNReal.coe_lt_coe.mpr ?_
  rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
  simp
  exact hm₀

lemma imo_1985_p6_main_39
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (m : ℕ)
  (hm₀ : 1 < m)
  (hm₁ : 0 < m - 1)
  (hm₂ : m = m - 1 + 1)
  (hm₃ : 0 < m)
  (x : NNReal := fi m 1)
  (y : NNReal := fi (m - 1) 1)
  (hx₁ : f₀ m x = 1)
  (hy₂ : f (m - 1) y = 1):
   f m x < f m y := by
  rw [hf₁ m x hm₃, hf₁ m y hm₃]
  refine NNReal.coe_lt_coe.mpr ?_
  rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
  simp
  exact hm₀

lemma imo_1985_p6_main_40
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (m : ℕ)
  (hm₀ : 1 < m)
  (hm₁ : 0 < m - 1)
  (hm₂ : m = m - 1 + 1)
  (hm₃ : 0 < m)
  (x : NNReal := fi m 1)
  (y : NNReal := fi (m - 1) 1)
  (hx₁ : f₀ m x = 1)
  (hy₂ : f (m - 1) y = 1):
  (↑(f₀ m x):ℝ) < ↑(f₀ m y) := by
  refine NNReal.coe_lt_coe.mpr ?_
  rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
  simp
  exact hm₀

lemma imo_1985_p6_main_41
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (m : ℕ)
  (hm₀ : 1 < m)
  (hm₁ : 0 < m - 1)
  (hm₂ : m = m - 1 + 1)
  (hm₃ : 0 < m)
  (x : NNReal := fi m 1)
  (y : NNReal := fi (m - 1) 1)
  (hx₁ : f₀ m x = 1)
  (hy₂ : f (m - 1) y = 1):
   f₀ m x < f₀ m y := by
  rw [hx₁, hf₂ m y hm₃, hm₂, h₁ (m - 1) y hm₁, hy₂]
  simp
  exact hm₀

lemma imo_1985_p6_main_42
  (fi : ℕ → NNReal → NNReal)
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (hfc₀ : fc = sn.restrict fun n ↦ fi (↑n) 1)
  (g₀ : StrictAntiOn (fun n ↦ fi n 1) sn)
  (m n : ↑sn)
  (hmn : m < n):
   fc n < fc m := by
  rw [hfc₀]
  simp
  let mn : ℕ := ↑m
  let nn : ℕ := ↑n
  have hm₀: mn ∈ sn := by exact Subtype.coe_prop m
  have hn₀: nn ∈ sn := by exact Subtype.coe_prop n
  exact g₀ hm₀ hn₀ hmn

lemma imo_1985_p6_main_43
  (fi : ℕ → NNReal → NNReal)
  (sn : Set ℕ)
  (g₀ : StrictAntiOn (fun n ↦ fi n 1) sn)
  (m n : ↑sn)
  (hmn : m < n):
   fi (↑n) 1 < fi (↑m) 1 := by
  let mn : ℕ := ↑m
  let nn : ℕ := ↑n
  have hm₀: mn ∈ sn := by exact Subtype.coe_prop m
  have hn₀: nn ∈ sn := by exact Subtype.coe_prop n
  exact g₀ hm₀ hn₀ hmn

lemma imo_1985_p6_main_44
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₀ : fb = sn.restrict fun n ↦ fi (↑n) (1 - 1 / ↑↑n))
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hu₁ : ∀ (n : ↑sn), fb n < 1)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  let sb := Set.range fb
  let sc := Set.range fc
  have hsb₀: sb = Set.range fb := by rfl
  have hsc₀: sc = Set.range fc := by rfl
  let fr : NNReal → ℝ := fun x => x.toReal
  let sbr := Set.image fr sb
  let scr := Set.image fr sc
  have hsn₂: Nonempty ↑sn := by
    rw [hsn]
    exact Set.nonempty_Ici_subtype
  have hu₃: ∃ br, IsLUB sbr br := by
    refine Real.exists_isLUB ?_ ?_
    . exact Set.Nonempty.of_subtype
    . refine NNReal.bddAbove_coe.mpr ?_
      refine (bddAbove_iff_exists_ge 1).mpr ?_
      use 1
      constructor
      . exact Preorder.le_refl 1
      . intros y hy₀
        apply Set.mem_range.mp at hy₀
        obtain ⟨na, hna₀⟩ := hy₀
        refine le_of_lt ?_
        rw [← hna₀]
        exact hu₁ na
  have hu₄: ∃ cr, IsGLB scr cr := by
    refine Real.exists_isGLB ?_ ?_
    . refine Set.Nonempty.image fr ?_
      exact Set.range_nonempty fc
    . exact NNReal.bddBelow_coe sc
  obtain ⟨br, hbr₀⟩ := hu₃
  obtain ⟨cr, hcr₀⟩ := hu₄
  have h₇: ∀ n x, 0 < n → (f n x < f (n + 1) x → 1 - 1 / n < f n x) := by
    intros n x hn₀ hn₁
    rw [h₁ n x hn₀] at hn₁
    nth_rw 1 [← mul_one (f n x)] at hn₁
    suffices g₀: 1 < f n x + 1 / ↑n
    . exact sub_right_lt_of_lt_add g₀
    . refine lt_of_mul_lt_mul_left hn₁ ?_
      exact h₃ n x hn₀
  have h₈: ∀ n x, 0 < n → 0 < x → 1 - 1 / n < f n x → f n x < f (n + 1) x := by
    intros n x hn₀ hx₀ hn₁
    rw [h₁ n x hn₀]
    suffices g₀: 1 < f n x + 1 / ↑n
    . nth_rw 1 [← mul_one (f n x)]
      refine mul_lt_mul' ?_ g₀ ?_ ?_
      . exact Preorder.le_refl (f n x)
      . exact zero_le_one' ℝ
      . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
    . exact lt_add_of_tsub_lt_right hn₁
  have hbr₁: 0 < br := by
    exact imo_1985_p6_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb hsn hfb₀ hsb₀ fr rfl sbr rfl br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by
      rw [hfb₀, hfi]
      exact rfl
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn hsn fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr (by rfl) sbr scr (by rfl) (by rfl) br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀



lemma imo_1985_p6_main_45
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₀ : fb = sn.restrict fun n ↦ fi (↑n) (1 - 1 / ↑↑n))
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hu₁ : ∀ (n : ↑sn), fb n < 1)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have hsn₂: Nonempty ↑sn := by
    rw [hsn]
    exact Set.nonempty_Ici_subtype
  have hu₃: ∃ br, IsLUB sbr br := by
    refine Real.exists_isLUB ?_ ?_
    . rw [hsbr]
      refine Set.Nonempty.image fr ?_
      rw [hsb₀]
      exact Set.range_nonempty fb
    . rw [hsbr, hfr]
      refine NNReal.bddAbove_coe.mpr ?_
      refine (bddAbove_iff_exists_ge 1).mpr ?_
      use 1
      constructor
      . exact Preorder.le_refl 1
      . intros y hy₀
        rw [hsb₀] at hy₀
        apply Set.mem_range.mp at hy₀
        obtain ⟨na, hna₀⟩ := hy₀
        refine le_of_lt ?_
        rw [← hna₀]
        exact hu₁ na
  have hu₄: ∃ cr, IsGLB scr cr := by
    refine Real.exists_isGLB ?_ ?_
    . rw [hscr]
      refine Set.Nonempty.image fr ?_
      rw [hsc₀]
      exact Set.range_nonempty fc
    . rw [hscr, hfr]
      exact NNReal.bddBelow_coe sc
  obtain ⟨br, hbr₀⟩ := hu₃
  obtain ⟨cr, hcr₀⟩ := hu₄
  have h₇: ∀ n x, 0 < n → (f n x < f (n + 1) x → 1 - 1 / n < f n x) := by
    intros n x hn₀ hn₁
    rw [h₁ n x hn₀] at hn₁
    nth_rw 1 [← mul_one (f n x)] at hn₁
    suffices g₀: 1 < f n x + 1 / ↑n
    . exact sub_right_lt_of_lt_add g₀
    . refine lt_of_mul_lt_mul_left hn₁ ?_
      exact h₃ n x hn₀
  have h₈: ∀ n x, 0 < n → 0 < x → 1 - 1 / n < f n x → f n x < f (n + 1) x := by
    intros n x hn₀ hx₀ hn₁
    rw [h₁ n x hn₀]
    suffices g₀: 1 < f n x + 1 / ↑n
    . nth_rw 1 [← mul_one (f n x)]
      refine mul_lt_mul' ?_ g₀ ?_ ?_
      . exact Preorder.le_refl (f n x)
      . exact zero_le_one' ℝ
      . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
    . exact lt_add_of_tsub_lt_right hn₁
  have hbr₁: 0 < br := by
    exact imo_1985_p6_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb hsn hfb₀ hsb₀ fr hfr sbr hsbr br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by
      rw [hfb₀, hfi]
      exact rfl
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn hsn fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀



lemma imo_1985_p6_main_46
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb : ↑sn → NNReal)
  (hu₁ : ∀ (n : ↑sn), fb n < 1)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun (x:NNReal) ↦ (↑x:ℝ))
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb):
   ∃ br, IsLUB sbr br := by
  have hsn₂: Nonempty ↑sn := by
    rw [hsn]
    exact Set.nonempty_Ici_subtype
  refine Real.exists_isLUB ?_ ?_
  . rw [hsbr]
    refine Set.Nonempty.image fr ?_
    rw [hsb₀]
    refine Set.range_nonempty fb
  . rw [hsbr, hfr]
    refine NNReal.bddAbove_coe.mpr ?_
    refine (bddAbove_iff_exists_ge 1).mpr ?_
    use 1
    constructor
    . exact Preorder.le_refl 1
    . intros y hy₀
      rw [hsb₀] at hy₀
      apply Set.mem_range.mp at hy₀
      obtain ⟨na, hna₀⟩ := hy₀
      refine le_of_lt ?_
      rw [← hna₀]
      exact hu₁ na


lemma imo_1985_p6_main_47
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hu₁ : ∀ (n : ↑sn), fb n < 1)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb) :
  BddAbove sbr := by
  rw [hsbr, hfr]
  refine NNReal.bddAbove_coe.mpr ?_
  refine (bddAbove_iff_exists_ge 1).mpr ?_
  use 1
  constructor
  . exact Preorder.le_refl 1
  . intros y hy₀
    rw [hsb₀] at hy₀
    apply Set.mem_range.mp at hy₀
    obtain ⟨na, hna₀⟩ := hy₀
    refine le_of_lt ?_
    rw [← hna₀]
    exact hu₁ na


lemma imo_1985_p6_main_50
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hu₁ : ∀ (n : ↑sn), fb n < 1)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb):
   ∀ y ∈ sb, y ≤ 1 := by
  intros y hy₀
  rw [hsb₀] at hy₀
  apply Set.mem_range.mp at hy₀
  obtain ⟨na, hna₀⟩ := hy₀
  refine le_of_lt ?_
  rw [← hna₀]
  exact hu₁ na

lemma imo_1985_p6_main_51
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₀ : fb = sn.restrict fun n ↦ fi (↑n) (1 - 1 / ↑↑n))
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (hu₃ : ∃ br, IsLUB sbr br):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have hsn₂: Nonempty ↑sn := by
    rw [hsn]
    exact Set.nonempty_Ici_subtype
  have hu₄: ∃ cr, IsGLB scr cr := by
    refine Real.exists_isGLB ?_ ?_
    . rw [hscr]
      refine Set.Nonempty.image fr ?_
      rw [hsc₀]
      exact Set.range_nonempty fc
    . rw [hscr, hfr]
      exact NNReal.bddBelow_coe sc
  obtain ⟨br, hbr₀⟩ := hu₃
  obtain ⟨cr, hcr₀⟩ := hu₄
  have h₇: ∀ n x, 0 < n → (f n x < f (n + 1) x → 1 - 1 / n < f n x) := by
    intros n x hn₀ hn₁
    rw [h₁ n x hn₀] at hn₁
    nth_rw 1 [← mul_one (f n x)] at hn₁
    suffices g₀: 1 < f n x + 1 / ↑n
    . exact sub_right_lt_of_lt_add g₀
    . refine lt_of_mul_lt_mul_left hn₁ ?_
      exact h₃ n x hn₀
  have h₈: ∀ n x, 0 < n → 0 < x → 1 - 1 / n < f n x → f n x < f (n + 1) x := by
    intros n x hn₀ hx₀ hn₁
    rw [h₁ n x hn₀]
    suffices g₀: 1 < f n x + 1 / ↑n
    . nth_rw 1 [← mul_one (f n x)]
      refine mul_lt_mul' ?_ g₀ ?_ ?_
      . exact Preorder.le_refl (f n x)
      . exact zero_le_one' ℝ
      . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
    . exact lt_add_of_tsub_lt_right hn₁
  have hbr₁: 0 < br := by
    exact imo_1985_p6_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb hsn hfb₀ hsb₀ fr hfr sbr hsbr br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by
      rw [hfb₀, hfi]
      exact rfl
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn hsn fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀

lemma imo_1985_p6_main_53
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₀ : fb = sn.restrict fun n ↦ fi (↑n) (1 - 1 / ↑↑n))
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (hu₃ : ∃ br, IsLUB sbr br)
  (hu₄ : ∃ cr, IsGLB scr cr):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  obtain ⟨br, hbr₀⟩ := hu₃
  obtain ⟨cr, hcr₀⟩ := hu₄
  have h₇: ∀ n x, 0 < n → (f n x < f (n + 1) x → 1 - 1 / n < f n x) := by
    intros n x hn₀ hn₁
    rw [h₁ n x hn₀] at hn₁
    nth_rw 1 [← mul_one (f n x)] at hn₁
    suffices g₀: 1 < f n x + 1 / ↑n
    . exact sub_right_lt_of_lt_add g₀
    . refine lt_of_mul_lt_mul_left hn₁ ?_
      exact h₃ n x hn₀
  have h₈: ∀ n x, 0 < n → 0 < x → 1 - 1 / n < f n x → f n x < f (n + 1) x := by
    intros n x hn₀ hx₀ hn₁
    rw [h₁ n x hn₀]
    suffices g₀: 1 < f n x + 1 / ↑n
    . nth_rw 1 [← mul_one (f n x)]
      refine mul_lt_mul' ?_ g₀ ?_ ?_
      . exact Preorder.le_refl (f n x)
      . exact zero_le_one' ℝ
      . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
    . exact lt_add_of_tsub_lt_right hn₁
  have hbr₁: 0 < br := by
    exact imo_1985_p6_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb hsn hfb₀ hsb₀ fr hfr sbr hsbr br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by
      rw [hfb₀, hfi]
      exact rfl
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn hsn fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀

lemma imo_1985_p6_main_56
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₀ : fb = sn.restrict fun n ↦ fi (↑n) (1 - 1 / ↑↑n))
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (br : ℝ)
  (hbr₀ : IsLUB sbr br)
  (cr : ℝ)
  (hcr₀ : IsGLB scr cr)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have hbr₁: 0 < br := by
    exact imo_1985_p6_10 f h₀ h₁ f₀ hf₂ fi hmo₇ sn sb fb hsn hfb₀ hsb₀ fr hfr sbr hsbr br hbr₀
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by
      rw [hfb₀, hfi]
      exact rfl
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn hsn fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀

lemma imo_1985_p6_main_57
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₀ : fb = sn.restrict fun n ↦ fi (↑n) (1 - 1 / ↑↑n))
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (br : ℝ)
  (hbr₀ : IsLUB sbr br)
  (cr : ℝ)
  (hcr₀ : IsGLB scr cr)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₁ : 0 < br):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have hfb₄: ∀ n, 0 ≤ fb n := by
    intro n
    have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by
      rw [hfb₀, hfi]
      exact rfl
    rw [hfb₂]
    simp
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn hsn fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀


lemma imo_1985_p6_main_59
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (br : ℝ)
  (hbr₀ : IsLUB sbr br)
  (cr : ℝ)
  (hcr₀ : IsGLB scr cr)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₁ : 0 < br)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have hu₅: br ≤ cr := by
    exact imo_1985_p6_11 sn fb fc hfc₂ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr hbr₀ hcr₀ hfb₄
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn hsn fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀


lemma imo_1985_p6_main_60
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (br : ℝ)
  (hbr₀ : IsLUB sbr br)
  (cr : ℝ)
  (hcr₀ : IsGLB scr cr)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₁ : 0 < br)
  (hu₅ : br ≤ cr):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  have hbr₃: ∀ x ∈ sbr, x ≤ br := by
    refine mem_upperBounds.mp ?_
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  have hcr₃: ∀ x ∈ scr, cr ≤ x := by
      refine mem_lowerBounds.mp ?_
      refine (le_isGLB_iff hcr₀).mp ?_
      exact Preorder.le_refl cr
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn hsn fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀

lemma imo_1985_p6_main_48
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hu₁ : ∀ (n : ↑sn), fb n < 1)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb):
   BddAbove sb := by
  refine (bddAbove_iff_exists_ge 1).mpr ?_
  use 1
  constructor
  . exact Preorder.le_refl 1
  . intros y hy₀
    rw [hsb₀] at hy₀
    apply Set.mem_range.mp at hy₀
    obtain ⟨na, hna₀⟩ := hy₀
    refine le_of_lt ?_
    rw [← hna₀]
    exact hu₁ na

lemma imo_1985_p6_main_49
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hu₁ : ∀ (n : ↑sn), fb n < 1)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb):
   ∃ x, 1 ≤ x ∧ ∀ y ∈ sb, y ≤ x := by
  use 1
  constructor
  . exact Preorder.le_refl 1
  . intros y hy₀
    rw [hsb₀] at hy₀
    apply Set.mem_range.mp at hy₀
    obtain ⟨na, hna₀⟩ := hy₀
    refine le_of_lt ?_
    rw [← hna₀]
    exact hu₁ na



lemma imo_1985_p6_main_52
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc):
   ∃ cr, IsGLB scr cr := by
  have hsn₂: Nonempty ↑sn := by
    rw [hsn]
    exact Set.nonempty_Ici_subtype
  refine Real.exists_isGLB ?_ ?_
  . rw [hscr]
    refine Set.Nonempty.image fr ?_
    rw [hsc₀]
    exact Set.range_nonempty fc
  . rw [hscr, hfr]
    exact NNReal.bddBelow_coe sc



lemma imo_1985_p6_main_54
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (n : ℕ)
  (x : NNReal)
  (hn₀ : 0 < n)
  (hn₁ : f n x < f (n + 1) x):
   1 - 1 / ↑n < f n x := by
  rw [h₁ n x hn₀] at hn₁
  nth_rw 1 [← mul_one (f n x)] at hn₁
  suffices g₀: 1 < f n x + 1 / ↑n
  . exact sub_right_lt_of_lt_add g₀
  . refine lt_of_mul_lt_mul_left hn₁ ?_
    exact h₃ n x hn₀

lemma imo_1985_p6_main_55
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₃ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 ≤ f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (n : ℕ)
  (x : NNReal)
  (hn₀ : 0 < n)
  (hx₀ : 0 < x)
  (hn₁ : 1 - 1 / ↑n < f n x):
   f n x < f (n + 1) x := by
  rw [h₁ n x hn₀]
  suffices g₀: 1 < f n x + 1 / ↑n
  . nth_rw 1 [← mul_one (f n x)]
    refine mul_lt_mul' ?_ g₀ ?_ ?_
    . exact Preorder.le_refl (f n x)
    . exact zero_le_one' ℝ
    . exact gt_of_gt_of_ge (hmo₀ n hn₀ hx₀) (h₃ n 0 hn₀)
  . exact lt_add_of_tsub_lt_right hn₁


lemma imo_1985_p6_main_58
  (f₀ : ℕ → NNReal → NNReal)
  (fi : ℕ → NNReal → NNReal)
  (hfi : fi = fun n ↦ Function.invFun (f₀ n))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₀ : fb = sn.restrict fun n ↦ fi (↑n) (1 - 1 / ↑↑n))
  (n : ↑sn):
   0 ≤ fb n := by
  have hfb₂: fb = fun (n:↑sn) => Function.invFun (f₀ n) (1 - 1 / ↑n) := by
    rw [hfb₀, hfi]
    exact rfl
  rw [hfb₂]
  simp


lemma imo_1985_p6_main_61
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (br : ℝ)
  (cr : ℝ)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₁ : 0 < br)
  (hu₅ : br ≤ cr)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x):
   ∃! a, ∀ (n : ℕ), 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  . exact imo_1985_p6_exists f h₂ hmo₀ f₀ hf₁ sn hsn fb fc hfb₁ hfc₁ hfb₃ hfc₃ sb sc hsb₀ hsc₀ fr hfr sbr scr hsbr hscr br cr h₈ hbr₁ hu₅ hbr₃ hcr₃
  . intros x y hx₀ hy₀
    exact imo_1985_p6_unique f h₁ hmo₀ h₇ x y hx₀ hy₀

set_option linter.unusedVariables.analyzeTactics true

lemma imo_1985_p6_unique_top_19
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩)
  (z : ℝ)
  (hz₁ : 0 < fd a b i)
  (j : ℕ)
  (hj : j = ⌈2 + Real.log (z / fd a b i) / Real.log (3 / 2)⌉₊)
  (hj₁ : j ∈ sd)
  (k : ↑sd)
  (hk₀ : ⟨j, hj₁⟩ ≤ k)
  (hk₁ : fd a b i * (3 / 2) ^ (k.1 - 2) ≤ fd a b k)
  (hk₂ : i < k):
   z ≤ fd a b k := by
  refine le_trans ?_ hk₁
  refine (div_le_iff₀' ?_).mp ?_
  . exact hz₁
  . refine Real.le_pow_of_log_le (by linarith) ?_
    refine (div_le_iff₀ ?_).mp ?_
    . refine Real.log_pos ?_
      linarith
    . rw [Nat.cast_sub ?_]
      . rw [Nat.cast_two]
        refine le_sub_iff_add_le'.mpr ?_
        refine Nat.le_of_ceil_le ?_
        exact le_of_eq_of_le (id (Eq.symm hj)) hk₀
      . rw [hi₁] at hk₂
        exact Nat.le_of_succ_le hk₂

lemma imo_1985_p6_unique_top_20
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩)
  (z : ℝ)
  (j : ℕ)
  (hj : j = ⌈2 + Real.log (z / fd a b i) / Real.log (3 / 2)⌉₊)
  (hj₁ : j ∈ sd)
  (k : ↑sd)
  (hk₀ : ⟨j, hj₁⟩ ≤ k)
  (hk₂ : i < k):
   z / fd a b i ≤ (3 / 2) ^ (k.1 - 2) := by
  refine Real.le_pow_of_log_le (by linarith) ?_
  refine (div_le_iff₀ ?_).mp ?_
  . refine Real.log_pos ?_
    linarith
  . rw [Nat.cast_sub ?_]
    . rw [Nat.cast_two]
      refine le_sub_iff_add_le'.mpr ?_
      refine Nat.le_of_ceil_le ?_
      exact le_of_eq_of_le (id (Eq.symm hj)) hk₀
    . rw [hi₁] at hk₂
      exact Nat.le_of_succ_le hk₂

lemma imo_1985_p6_unique_top_21
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩)
  (z : ℝ)
  (j : ℕ)
  (hj : j = ⌈2 + Real.log (z / fd a b i) / Real.log (3 / 2)⌉₊)
  (hj₁ : j ∈ sd)
  (k : ↑sd)
  (hk₀ : ⟨j, hj₁⟩ ≤ k)
  (hk₂ : i < k):
   Real.log (z / fd a b i) ≤ ↑(k.1 - 2) * Real.log (3 / 2) := by
  refine (div_le_iff₀ ?_).mp ?_
  . refine Real.log_pos ?_
    linarith
  . rw [Nat.cast_sub ?_]
    . rw [Nat.cast_two]
      refine le_sub_iff_add_le'.mpr ?_
      refine Nat.le_of_ceil_le ?_
      exact le_of_eq_of_le (id (Eq.symm hj)) hk₀
    . rw [hi₁] at hk₂
      exact Nat.le_of_succ_le hk₂


lemma imo_1985_p6_unique_top_22
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩)
  (z : ℝ)
  (j : ℕ)
  (hj : j = ⌈2 + Real.log (z / fd a b i) / Real.log (3 / 2)⌉₊)
  (hj₁ : j ∈ sd)
  (k : ↑sd)
  (hk₀ : ⟨j, hj₁⟩ ≤ k)
  (hk₂ : i < k):
   Real.log (z / fd a b i) / Real.log (3 / 2) ≤ ↑(k.1 - 2) := by
  rw [Nat.cast_sub ?_]
  . rw [Nat.cast_two]
    refine le_sub_iff_add_le'.mpr ?_
    refine Nat.le_of_ceil_le ?_
    exact le_of_eq_of_le (id (Eq.symm hj)) hk₀
  . rw [hi₁] at hk₂
    exact Nat.le_of_succ_le hk₂




lemma imo_1985_p6_unique_nhds
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n) :
  ∀ (a b : NNReal),
    a < b →
      (∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1) →
        Filter.Tendsto (fd a b) Filter.atTop (nhds 0) := by
  intros a b ha₀ ha₁
  have hsd₁: Nonempty ↑sd := by
    rw [hsd]
    refine Set.Nonempty.to_subtype ?_
    exact Set.nonempty_Ici
  refine tendsto_atTop_nhds.mpr ?_
  intros U hU₀ hU₁
  have hU₂: U ∈ nhds 0 := by exact IsOpen.mem_nhds hU₁ hU₀
  apply mem_nhds_iff_exists_Ioo_subset.mp at hU₂
  obtain ⟨l, u, hl₀, hl₁⟩ := hU₂
  have hl₂: 0 < u := by exact (Set.mem_Ioo.mpr hl₀).2
  let nd := 2 + Nat.ceil (1/u)
  have hnd₀: nd ∈ sd := by
    rw [hsd]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right 2 ⌈1 / u⌉₊
  use ⟨nd, hnd₀⟩
  intros n hn₀
  refine (IsOpen.mem_nhds_iff hU₁).mp ?_
  refine mem_nhds_iff.mpr ?_
  use Set.Ioo l u
  constructor
  . exact hl₁
  constructor
  . exact isOpen_Ioo
  . refine Set.mem_Ioo.mpr ?_
    constructor
    . refine lt_trans ?_ (hd₁ n a b ha₀)
      exact (Set.mem_Ioo.mp hl₀).1
    . have hn₁: fd a b n < 1 / n := by
        rw [hfd₁]
        have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
        have hb₁: f n b < 1 := by exact (ha₁ n).2.2
        refine sub_lt_iff_lt_add.mpr ?_
        refine lt_trans hb₁ ?_
        exact sub_lt_iff_lt_add'.mp ha₂
      have hn₂: (1:ℝ) / n ≤ 1 / nd := by
        refine one_div_le_one_div_of_le ?_ ?_
        . refine Nat.cast_pos.mpr ?_
          rw [hsd] at hnd₀
          exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
        . exact Nat.cast_le.mpr hn₀
      refine lt_of_lt_of_le hn₁ ?_
      refine le_trans hn₂ ?_
      refine div_le_of_le_mul₀ ?_ ?_ ?_
      . exact Nat.cast_nonneg' nd
      . exact le_of_lt hl₂
      . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
          refine (mul_le_mul_left hl₂).mpr ?_
          rw [Nat.cast_add 2 _, Nat.cast_two]
          refine add_le_add_left ?_ 2
          exact Nat.le_ceil (1 / u)
        refine le_trans ?_ hl₃
        rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
        refine le_of_lt ?_
        refine sub_lt_iff_lt_add.mp ?_
        rw [sub_self 1]
        exact mul_pos hl₂ (two_pos)


lemma imo_1985_p6_unique_nhds_1
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2):
   Nonempty ↑sd := by
  rw [hsd]
  refine Set.Nonempty.to_subtype ?_
  exact Set.nonempty_Ici


lemma imo_1985_p6_unique_nhds_2
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1)
  (hsd₁ : Nonempty ↑sd):
   Filter.Tendsto (fd a b) Filter.atTop (nhds 0) := by
  refine tendsto_atTop_nhds.mpr ?_
  intros U hU₀ hU₁
  have hU₂: U ∈ nhds 0 := by exact IsOpen.mem_nhds hU₁ hU₀
  apply mem_nhds_iff_exists_Ioo_subset.mp at hU₂
  obtain ⟨l, u, hl₀, hl₁⟩ := hU₂
  have hl₂: 0 < u := by exact (Set.mem_Ioo.mpr hl₀).2
  let nd := 2 + Nat.ceil (1/u)
  have hnd₀: nd ∈ sd := by
    rw [hsd]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right 2 ⌈1 / u⌉₊
  use ⟨nd, hnd₀⟩
  intros n hn₀
  refine (IsOpen.mem_nhds_iff hU₁).mp ?_
  refine mem_nhds_iff.mpr ?_
  use Set.Ioo l u
  constructor
  . exact hl₁
  constructor
  . exact isOpen_Ioo
  . refine Set.mem_Ioo.mpr ?_
    constructor
    . refine lt_trans ?_ (hd₁ n a b ha₀)
      exact (Set.mem_Ioo.mp hl₀).1
    . have hn₁: fd a b n < 1 / n := by
        rw [hfd₁]
        have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
        have hb₁: f n b < 1 := by exact (ha₁ n).2.2
        refine sub_lt_iff_lt_add.mpr ?_
        refine lt_trans hb₁ ?_
        exact sub_lt_iff_lt_add'.mp ha₂
      have hn₂: (1:ℝ) / n ≤ 1 / nd := by
        refine one_div_le_one_div_of_le ?_ ?_
        . refine Nat.cast_pos.mpr ?_
          rw [hsd] at hnd₀
          exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
        . exact Nat.cast_le.mpr hn₀
      refine lt_of_lt_of_le hn₁ ?_
      refine le_trans hn₂ ?_
      refine div_le_of_le_mul₀ ?_ ?_ ?_
      . exact Nat.cast_nonneg' nd
      . exact le_of_lt hl₂
      . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
          refine (mul_le_mul_left hl₂).mpr ?_
          rw [Nat.cast_add 2 _, Nat.cast_two]
          refine add_le_add_left ?_ 2
          exact Nat.le_ceil (1 / u)
        refine le_trans ?_ hl₃
        rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
        refine le_of_lt ?_
        refine sub_lt_iff_lt_add.mp ?_
        rw [sub_self 1]
        exact mul_pos hl₂ (two_pos)


lemma imo_1985_p6_unique_nhds_3
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1)
  (U : Set ℝ)
  (hU₀ : 0 ∈ U)
  (hU₁ : IsOpen U):
   ∃ N, ∀ (n : ↑sd), N ≤ n → fd a b n ∈ U := by
  have hU₂: U ∈ nhds 0 := by exact IsOpen.mem_nhds hU₁ hU₀
  apply mem_nhds_iff_exists_Ioo_subset.mp at hU₂
  obtain ⟨l, u, hl₀, hl₁⟩ := hU₂
  have hl₂: 0 < u := by exact (Set.mem_Ioo.mpr hl₀).2
  let nd := 2 + Nat.ceil (1/u)
  have hnd₀: nd ∈ sd := by
    rw [hsd]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right 2 ⌈1 / u⌉₊
  use ⟨nd, hnd₀⟩
  intros n hn₀
  refine (IsOpen.mem_nhds_iff hU₁).mp ?_
  refine mem_nhds_iff.mpr ?_
  use Set.Ioo l u
  constructor
  . exact hl₁
  constructor
  . exact isOpen_Ioo
  . refine Set.mem_Ioo.mpr ?_
    constructor
    . refine lt_trans ?_ (hd₁ n a b ha₀)
      exact (Set.mem_Ioo.mp hl₀).1
    . have hn₁: fd a b n < 1 / n := by
        rw [hfd₁]
        have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
        have hb₁: f n b < 1 := by exact (ha₁ n).2.2
        refine sub_lt_iff_lt_add.mpr ?_
        refine lt_trans hb₁ ?_
        exact sub_lt_iff_lt_add'.mp ha₂
      have hn₂: (1:ℝ) / n ≤ 1 / nd := by
        refine one_div_le_one_div_of_le ?_ ?_
        . refine Nat.cast_pos.mpr ?_
          rw [hsd] at hnd₀
          exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
        . exact Nat.cast_le.mpr hn₀
      refine lt_of_lt_of_le hn₁ ?_
      refine le_trans hn₂ ?_
      refine div_le_of_le_mul₀ ?_ ?_ ?_
      . exact Nat.cast_nonneg' nd
      . exact le_of_lt hl₂
      . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
          refine (mul_le_mul_left hl₂).mpr ?_
          rw [Nat.cast_add 2 _, Nat.cast_two]
          refine add_le_add_left ?_ 2
          exact Nat.le_ceil (1 / u)
        refine le_trans ?_ hl₃
        rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
        refine le_of_lt ?_
        refine sub_lt_iff_lt_add.mp ?_
        rw [sub_self 1]
        exact mul_pos hl₂ (two_pos)


lemma imo_1985_p6_unique_nhds_4
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1)
  (U : Set ℝ)
  (hU₁ : IsOpen U)
  (hU₂ : ∃ l u, 0 ∈ Set.Ioo l u ∧ Set.Ioo l u ⊆ U):
   ∃ N, ∀ (n : ↑sd), N ≤ n → fd a b n ∈ U := by
  obtain ⟨l, u, hl₀, hl₁⟩ := hU₂
  have hl₂: 0 < u := by exact (Set.mem_Ioo.mpr hl₀).2
  let nd := 2 + Nat.ceil (1/u)
  have hnd₀: nd ∈ sd := by
    rw [hsd]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right 2 ⌈1 / u⌉₊
  use ⟨nd, hnd₀⟩
  intros n hn₀
  refine (IsOpen.mem_nhds_iff hU₁).mp ?_
  refine mem_nhds_iff.mpr ?_
  use Set.Ioo l u
  constructor
  . exact hl₁
  constructor
  . exact isOpen_Ioo
  . refine Set.mem_Ioo.mpr ?_
    constructor
    . refine lt_trans ?_ (hd₁ n a b ha₀)
      exact (Set.mem_Ioo.mp hl₀).1
    . have hn₁: fd a b n < 1 / n := by
        rw [hfd₁]
        have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
        have hb₁: f n b < 1 := by exact (ha₁ n).2.2
        refine sub_lt_iff_lt_add.mpr ?_
        refine lt_trans hb₁ ?_
        exact sub_lt_iff_lt_add'.mp ha₂
      have hn₂: (1:ℝ) / n ≤ 1 / nd := by
        refine one_div_le_one_div_of_le ?_ ?_
        . refine Nat.cast_pos.mpr ?_
          rw [hsd] at hnd₀
          exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
        . exact Nat.cast_le.mpr hn₀
      refine lt_of_lt_of_le hn₁ ?_
      refine le_trans hn₂ ?_
      refine div_le_of_le_mul₀ ?_ ?_ ?_
      . exact Nat.cast_nonneg' nd
      . exact le_of_lt hl₂
      . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
          refine (mul_le_mul_left hl₂).mpr ?_
          rw [Nat.cast_add 2 _, Nat.cast_two]
          refine add_le_add_left ?_ 2
          exact Nat.le_ceil (1 / u)
        refine le_trans ?_ hl₃
        rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
        refine le_of_lt ?_
        refine sub_lt_iff_lt_add.mp ?_
        rw [sub_self 1]
        exact mul_pos hl₂ (two_pos)


lemma imo_1985_p6_unique_nhds_5
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1)
  (U : Set ℝ)
  (hU₁ : IsOpen U)
  (l u : ℝ)
  (hl₀ : 0 ∈ Set.Ioo l u)
  (hl₁ : Set.Ioo l u ⊆ U):
   ∃ N, ∀ (n : ↑sd), N ≤ n → fd a b n ∈ U := by
  have hl₂: 0 < u := by exact (Set.mem_Ioo.mpr hl₀).2
  let nd := 2 + Nat.ceil (1/u)
  have hnd₀: nd ∈ sd := by
    rw [hsd]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right 2 ⌈1 / u⌉₊
  use ⟨nd, hnd₀⟩
  intros n hn₀
  refine (IsOpen.mem_nhds_iff hU₁).mp ?_
  refine mem_nhds_iff.mpr ?_
  use Set.Ioo l u
  constructor
  . exact hl₁
  constructor
  . exact isOpen_Ioo
  . refine Set.mem_Ioo.mpr ?_
    constructor
    . refine lt_trans ?_ (hd₁ n a b ha₀)
      exact (Set.mem_Ioo.mp hl₀).1
    . have hn₁: fd a b n < 1 / n := by
        rw [hfd₁]
        have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
        have hb₁: f n b < 1 := by exact (ha₁ n).2.2
        refine sub_lt_iff_lt_add.mpr ?_
        refine lt_trans hb₁ ?_
        exact sub_lt_iff_lt_add'.mp ha₂
      have hn₂: (1:ℝ) / n ≤ 1 / nd := by
        refine one_div_le_one_div_of_le ?_ ?_
        . refine Nat.cast_pos.mpr ?_
          rw [hsd] at hnd₀
          exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
        . exact Nat.cast_le.mpr hn₀
      refine lt_of_lt_of_le hn₁ ?_
      refine le_trans hn₂ ?_
      refine div_le_of_le_mul₀ ?_ ?_ ?_
      . exact Nat.cast_nonneg' nd
      . exact le_of_lt hl₂
      . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
          refine (mul_le_mul_left hl₂).mpr ?_
          rw [Nat.cast_add 2 _, Nat.cast_two]
          refine add_le_add_left ?_ 2
          exact Nat.le_ceil (1 / u)
        refine le_trans ?_ hl₃
        rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
        refine le_of_lt ?_
        refine sub_lt_iff_lt_add.mp ?_
        rw [sub_self 1]
        exact mul_pos hl₂ (two_pos)


lemma imo_1985_p6_unique_nhds_6
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (u : ℝ)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊):
  nd ∈ sd := by
  rw [hsd, hnd]
  refine Set.mem_Ici.mpr ?_
  exact Nat.le_add_right 2 ⌈1 / u⌉₊

lemma imo_1985_p6_unique_nhds_7
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1)
  (U : Set ℝ)
  (hU₁ : IsOpen U)
  (l u : ℝ)
  (hl₀ : 0 ∈ Set.Ioo l u)
  (hl₁ : Set.Ioo l u ⊆ U)
  (hl₂ : 0 < u)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊)
  (hnd₀ : nd ∈ sd):
   ∃ N, ∀ (n : ↑sd), N ≤ n → fd a b n ∈ U := by
  use ⟨nd, hnd₀⟩
  intros n hn₀
  refine (IsOpen.mem_nhds_iff hU₁).mp ?_
  refine mem_nhds_iff.mpr ?_
  use Set.Ioo l u
  constructor
  . exact hl₁
  constructor
  . exact isOpen_Ioo
  . refine Set.mem_Ioo.mpr ?_
    constructor
    . refine lt_trans ?_ (hd₁ n a b ha₀)
      exact (Set.mem_Ioo.mp hl₀).1
    . have hn₁: fd a b n < 1 / n := by
        rw [hfd₁]
        have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
        have hb₁: f n b < 1 := by exact (ha₁ n).2.2
        refine sub_lt_iff_lt_add.mpr ?_
        refine lt_trans hb₁ ?_
        exact sub_lt_iff_lt_add'.mp ha₂
      have hn₂: (1:ℝ) / n ≤ 1 / nd := by
        refine one_div_le_one_div_of_le ?_ ?_
        . refine Nat.cast_pos.mpr ?_
          rw [hsd] at hnd₀
          exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
        . exact Nat.cast_le.mpr hn₀
      refine lt_of_lt_of_le hn₁ ?_
      refine le_trans hn₂ ?_
      refine div_le_of_le_mul₀ ?_ ?_ ?_
      . exact Nat.cast_nonneg' nd
      . exact le_of_lt hl₂
      . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
          refine (mul_le_mul_left hl₂).mpr ?_
          rw [Nat.cast_add 2 _, Nat.cast_two]
          refine add_le_add_left ?_ 2
          exact Nat.le_ceil (1 / u)
        rw [hnd]
        refine le_trans ?_ hl₃
        rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
        refine le_of_lt ?_
        refine sub_lt_iff_lt_add.mp ?_
        rw [sub_self 1]
        exact mul_pos hl₂ (two_pos)


lemma imo_1985_p6_unique_nhds_8
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1)
  (U : Set ℝ)
  (hU₁ : IsOpen U)
  (l u : ℝ)
  (hl₀ : 0 ∈ Set.Ioo l u)
  (hl₁ : Set.Ioo l u ⊆ U)
  (hl₂ : 0 < u)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊)
  (hnd₀ : nd ∈ sd)
  (n : ↑sd)
  (hn₀ : ⟨nd, hnd₀⟩ ≤ n):
   fd a b n ∈ U := by
  refine (IsOpen.mem_nhds_iff hU₁).mp ?_
  refine mem_nhds_iff.mpr ?_
  use Set.Ioo l u
  constructor
  . exact hl₁
  constructor
  . exact isOpen_Ioo
  . refine Set.mem_Ioo.mpr ?_
    constructor
    . refine lt_trans ?_ (hd₁ n a b ha₀)
      exact (Set.mem_Ioo.mp hl₀).1
    . have hn₁: fd a b n < 1 / n := by
        rw [hfd₁]
        have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
        have hb₁: f n b < 1 := by exact (ha₁ n).2.2
        refine sub_lt_iff_lt_add.mpr ?_
        refine lt_trans hb₁ ?_
        exact sub_lt_iff_lt_add'.mp ha₂
      have hn₂: (1:ℝ) / n ≤ 1 / nd := by
        refine one_div_le_one_div_of_le ?_ ?_
        . refine Nat.cast_pos.mpr ?_
          rw [hsd] at hnd₀
          exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
        . exact Nat.cast_le.mpr hn₀
      refine lt_of_lt_of_le hn₁ ?_
      refine le_trans hn₂ ?_
      refine div_le_of_le_mul₀ ?_ ?_ ?_
      . exact Nat.cast_nonneg' nd
      . exact le_of_lt hl₂
      . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
          refine (mul_le_mul_left hl₂).mpr ?_
          rw [Nat.cast_add 2 _, Nat.cast_two]
          refine add_le_add_left ?_ 2
          exact Nat.le_ceil (1 / u)
        rw [hnd]
        refine le_trans ?_ hl₃
        rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
        refine le_of_lt ?_
        refine sub_lt_iff_lt_add.mp ?_
        rw [sub_self 1]
        exact mul_pos hl₂ (two_pos)

lemma imo_1985_p6_unique_nhds_9
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1)
  (U : Set ℝ)
  (l u : ℝ)
  (hl₀ : 0 ∈ Set.Ioo l u)
  (hl₁ : Set.Ioo l u ⊆ U)
  (hl₂ : 0 < u)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊)
  (hnd₀ : nd ∈ sd)
  (n : ↑sd)
  (hn₀ : ⟨nd, hnd₀⟩ ≤ n):
   U ∈ nhds (fd a b n) := by
  refine mem_nhds_iff.mpr ?_
  use Set.Ioo l u
  constructor
  . exact hl₁
  constructor
  . exact isOpen_Ioo
  . refine Set.mem_Ioo.mpr ?_
    constructor
    . refine lt_trans ?_ (hd₁ n a b ha₀)
      exact (Set.mem_Ioo.mp hl₀).1
    . have hn₁: fd a b n < 1 / n := by
        rw [hfd₁]
        have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
        have hb₁: f n b < 1 := by exact (ha₁ n).2.2
        refine sub_lt_iff_lt_add.mpr ?_
        refine lt_trans hb₁ ?_
        exact sub_lt_iff_lt_add'.mp ha₂
      have hn₂: (1:ℝ) / n ≤ 1 / nd := by
        refine one_div_le_one_div_of_le ?_ ?_
        . refine Nat.cast_pos.mpr ?_
          rw [hsd] at hnd₀
          exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
        . exact Nat.cast_le.mpr hn₀
      refine lt_of_lt_of_le hn₁ ?_
      refine le_trans hn₂ ?_
      refine div_le_of_le_mul₀ ?_ ?_ ?_
      . exact Nat.cast_nonneg' nd
      . exact le_of_lt hl₂
      . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
          refine (mul_le_mul_left hl₂).mpr ?_
          rw [Nat.cast_add 2 _, Nat.cast_two]
          refine add_le_add_left ?_ 2
          exact Nat.le_ceil (1 / u)
        rw [hnd]
        refine le_trans ?_ hl₃
        rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
        refine le_of_lt ?_
        refine sub_lt_iff_lt_add.mp ?_
        rw [sub_self 1]
        exact mul_pos hl₂ (two_pos)

lemma imo_1985_p6_unique_nhds_10
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1)
  (U : Set ℝ)
  (l u : ℝ)
  (hl₀ : 0 ∈ Set.Ioo l u)
  (hl₁ : Set.Ioo l u ⊆ U)
  (hl₂ : 0 < u)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊)
  (hnd₀ : nd ∈ sd)
  (n : ↑sd)
  (hn₀ : ⟨nd, hnd₀⟩ ≤ n):
   ∃ t ⊆ U, IsOpen t ∧ fd a b n ∈ t := by
  use Set.Ioo l u
  constructor
  . exact hl₁
  constructor
  . exact isOpen_Ioo
  . refine Set.mem_Ioo.mpr ?_
    constructor
    . refine lt_trans ?_ (hd₁ n a b ha₀)
      exact (Set.mem_Ioo.mp hl₀).1
    . have hn₁: fd a b n < 1 / n := by
        rw [hfd₁]
        have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
        have hb₁: f n b < 1 := by exact (ha₁ n).2.2
        refine sub_lt_iff_lt_add.mpr ?_
        refine lt_trans hb₁ ?_
        exact sub_lt_iff_lt_add'.mp ha₂
      have hn₂: (1:ℝ) / n ≤ 1 / nd := by
        refine one_div_le_one_div_of_le ?_ ?_
        . refine Nat.cast_pos.mpr ?_
          rw [hsd] at hnd₀
          exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
        . exact Nat.cast_le.mpr hn₀
      refine lt_of_lt_of_le hn₁ ?_
      refine le_trans hn₂ ?_
      refine div_le_of_le_mul₀ ?_ ?_ ?_
      . exact Nat.cast_nonneg' nd
      . exact le_of_lt hl₂
      . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
          refine (mul_le_mul_left hl₂).mpr ?_
          rw [Nat.cast_add 2 _, Nat.cast_two]
          refine add_le_add_left ?_ 2
          exact Nat.le_ceil (1 / u)
        rw [hnd]
        refine le_trans ?_ hl₃
        rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
        refine le_of_lt ?_
        refine sub_lt_iff_lt_add.mp ?_
        rw [sub_self 1]
        exact mul_pos hl₂ (two_pos)

lemma imo_1985_p6_unique_nhds_11
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (U : Set ℝ)
  (hU₁ : IsOpen U)
  (nd : ℕ)
  (hnd₀ : nd ∈ sd)
  (hnd₁: ∀ n:↑ sd, ∃ t ⊆ U, IsOpen t ∧ fd a b n ∈ t):
   ∃ N, ∀ (n : ↑sd), N ≤ n → fd a b n ∈ U := by
  use ⟨nd, hnd₀⟩
  intros n _
  refine (IsOpen.mem_nhds_iff hU₁).mp ?_
  refine mem_nhds_iff.mpr ?_
  exact hnd₁ n

lemma imo_1985_p6_unique_nhds_12
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1)
  (U : Set ℝ)
  (l u : ℝ)
  (hl₀ : 0 ∈ Set.Ioo l u)
  (hl₁ : Set.Ioo l u ⊆ U)
  (hl₂ : 0 < u)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊)
  (hnd₀ : nd ∈ sd)
  (n : ↑sd)
  (hn₀ : ⟨nd, hnd₀⟩ ≤ n):
   Set.Ioo l u ⊆ U ∧ IsOpen (Set.Ioo l u) ∧ fd a b n ∈ Set.Ioo l u := by
  constructor
  . exact hl₁
  constructor
  . exact isOpen_Ioo
  . refine Set.mem_Ioo.mpr ?_
    constructor
    . refine lt_trans ?_ (hd₁ n a b ha₀)
      exact (Set.mem_Ioo.mp hl₀).1
    . have hn₁: fd a b n < 1 / n := by
        rw [hfd₁]
        have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
        have hb₁: f n b < 1 := by exact (ha₁ n).2.2
        refine sub_lt_iff_lt_add.mpr ?_
        refine lt_trans hb₁ ?_
        exact sub_lt_iff_lt_add'.mp ha₂
      have hn₂: (1:ℝ) / n ≤ 1 / nd := by
        refine one_div_le_one_div_of_le ?_ ?_
        . refine Nat.cast_pos.mpr ?_
          rw [hsd] at hnd₀
          exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
        . exact Nat.cast_le.mpr hn₀
      refine lt_of_lt_of_le hn₁ ?_
      refine le_trans hn₂ ?_
      refine div_le_of_le_mul₀ ?_ ?_ ?_
      . exact Nat.cast_nonneg' nd
      . exact le_of_lt hl₂
      . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
          refine (mul_le_mul_left hl₂).mpr ?_
          rw [Nat.cast_add 2 _, Nat.cast_two]
          refine add_le_add_left ?_ 2
          exact Nat.le_ceil (1 / u)
        rw [hnd]
        refine le_trans ?_ hl₃
        rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
        refine le_of_lt ?_
        refine sub_lt_iff_lt_add.mp ?_
        rw [sub_self 1]
        exact mul_pos hl₂ (two_pos)


lemma imo_1985_p6_unique_nhds_13
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1)
  (l u : ℝ)
  (hl₀ : 0 ∈ Set.Ioo l u)
  (hl₂ : 0 < u)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊)
  (hnd₀ : nd ∈ sd)
  (n : ↑sd)
  (hn₀ : ⟨nd, hnd₀⟩ ≤ n):
   fd a b n ∈ Set.Ioo l u := by
  refine Set.mem_Ioo.mpr ?_
  constructor
  . refine lt_trans ?_ (hd₁ n a b ha₀)
    exact (Set.mem_Ioo.mp hl₀).1
  . have hn₁: fd a b n < 1 / n := by
      rw [hfd₁]
      have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
      have hb₁: f n b < 1 := by exact (ha₁ n).2.2
      refine sub_lt_iff_lt_add.mpr ?_
      refine lt_trans hb₁ ?_
      exact sub_lt_iff_lt_add'.mp ha₂
    have hn₂: (1:ℝ) / n ≤ 1 / nd := by
      refine one_div_le_one_div_of_le ?_ ?_
      . refine Nat.cast_pos.mpr ?_
        rw [hsd] at hnd₀
        exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
      . exact Nat.cast_le.mpr hn₀
    refine lt_of_lt_of_le hn₁ ?_
    refine le_trans hn₂ ?_
    refine div_le_of_le_mul₀ ?_ ?_ ?_
    . exact Nat.cast_nonneg' nd
    . exact le_of_lt hl₂
    . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
        refine (mul_le_mul_left hl₂).mpr ?_
        rw [Nat.cast_add 2 _, Nat.cast_two]
        refine add_le_add_left ?_ 2
        exact Nat.le_ceil (1 / u)
      rw [hnd]
      refine le_trans ?_ hl₃
      rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
      refine le_of_lt ?_
      refine sub_lt_iff_lt_add.mp ?_
      rw [sub_self 1]
      exact mul_pos hl₂ (two_pos)


lemma imo_1985_p6_unique_nhds_14
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (l u : ℝ)
  (hl₀ : 0 ∈ Set.Ioo l u)
  (n : ↑sd):
   l < fd a b n := by
  refine lt_trans ?_ (hd₁ n a b ha₀)
  exact (Set.mem_Ioo.mp hl₀).1

lemma imo_1985_p6_unique_nhds_15
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (a b : NNReal)
  (ha₁ : ∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1)
  (u : ℝ)
  (hl₂ : 0 < u)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊)
  (hnd₀ : nd ∈ sd)
  (n : ↑sd)
  (hn₀ : ⟨nd, hnd₀⟩ ≤ n):
   fd a b n < u := by
  have hn₁: fd a b n < 1 / n := by
    rw [hfd₁]
    have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
    have hb₁: f n b < 1 := by exact (ha₁ n).2.2
    refine sub_lt_iff_lt_add.mpr ?_
    refine lt_trans hb₁ ?_
    exact sub_lt_iff_lt_add'.mp ha₂
  have hn₂: (1:ℝ) / n ≤ 1 / nd := by
    refine one_div_le_one_div_of_le ?_ ?_
    . refine Nat.cast_pos.mpr ?_
      rw [hsd] at hnd₀
      exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
    . exact Nat.cast_le.mpr hn₀
  refine lt_of_lt_of_le hn₁ ?_
  refine le_trans hn₂ ?_
  refine div_le_of_le_mul₀ ?_ ?_ ?_
  . exact Nat.cast_nonneg' nd
  . exact le_of_lt hl₂
  . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
      refine (mul_le_mul_left hl₂).mpr ?_
      rw [Nat.cast_add 2 _, Nat.cast_two]
      refine add_le_add_left ?_ 2
      exact Nat.le_ceil (1 / u)
    rw [hnd]
    refine le_trans ?_ hl₃
    rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
    refine le_of_lt ?_
    refine sub_lt_iff_lt_add.mp ?_
    rw [sub_self 1]
    exact mul_pos hl₂ (two_pos)



lemma imo_1985_p6_unique_nhds_16
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (a b : NNReal)
  (ha₁ : ∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1)
  (n : ↑sd):
   fd a b n < 1 / ↑↑n := by
  rw [hfd₁]
  have ha₂: 1 - 1 / n < f n a := by exact (ha₁ n).1.1
  have hb₁: f n b < 1 := by exact (ha₁ n).2.2
  refine sub_lt_iff_lt_add.mpr ?_
  refine lt_trans hb₁ ?_
  exact sub_lt_iff_lt_add'.mp ha₂


lemma imo_1985_p6_unique_nhds_17
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (u : ℝ)
  (hl₂ : 0 < u)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊)
  (hnd₀ : nd ∈ sd)
  (n : ↑sd)
  (hn₀ : ⟨nd, hnd₀⟩ ≤ n)
  (hn₁ : fd a b n < 1 / ↑↑n):
   fd a b n < u := by
  have hn₂: (1:ℝ) / n ≤ 1 / nd := by
    refine one_div_le_one_div_of_le ?_ ?_
    . refine Nat.cast_pos.mpr ?_
      rw [hsd] at hnd₀
      exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
    . exact Nat.cast_le.mpr hn₀
  refine lt_of_lt_of_le hn₁ ?_
  refine le_trans hn₂ ?_
  refine div_le_of_le_mul₀ ?_ ?_ ?_
  . exact Nat.cast_nonneg' nd
  . exact le_of_lt hl₂
  . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
      refine (mul_le_mul_left hl₂).mpr ?_
      rw [Nat.cast_add 2 _, Nat.cast_two]
      refine add_le_add_left ?_ 2
      exact Nat.le_ceil (1 / u)
    rw [hnd]
    refine le_trans ?_ hl₃
    rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
    refine le_of_lt ?_
    refine sub_lt_iff_lt_add.mp ?_
    rw [sub_self 1]
    exact mul_pos hl₂ (two_pos)



lemma imo_1985_p6_unique_nhds_18
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (nd : ℕ)
  (hnd₀ : nd ∈ sd)
  (n : ↑sd)
  (hn₀ : ⟨nd, hnd₀⟩ ≤ n):
   (1:ℝ) / n ≤ 1 / nd := by
  refine one_div_le_one_div_of_le ?_ ?_
  . refine Nat.cast_pos.mpr ?_
    rw [hsd] at hnd₀
    exact lt_of_lt_of_le (Nat.zero_lt_two) hnd₀
  . exact Nat.cast_le.mpr hn₀

lemma imo_1985_p6_unique_nhds_19
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (u : ℝ)
  (hl₂ : 0 < u)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊)
  (n : ↑sd)
  (hn₁ : fd a b n < 1 / ↑↑n)
  (hn₂ : (1:ℝ) / ↑↑n ≤ 1 / ↑nd):
   fd a b n < u := by
  refine lt_of_lt_of_le hn₁ ?_
  refine le_trans hn₂ ?_
  refine div_le_of_le_mul₀ ?_ ?_ ?_
  . exact Nat.cast_nonneg' nd
  . exact le_of_lt hl₂
  . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
      refine (mul_le_mul_left hl₂).mpr ?_
      rw [Nat.cast_add 2 _, Nat.cast_two]
      refine add_le_add_left ?_ 2
      exact Nat.le_ceil (1 / u)
    rw [hnd]
    refine le_trans ?_ hl₃
    rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
    refine le_of_lt ?_
    refine sub_lt_iff_lt_add.mp ?_
    rw [sub_self 1]
    exact mul_pos hl₂ (two_pos)

lemma imo_1985_p6_unique_nhds_20
  (u : ℝ)
  (hl₂ : 0 < u)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊):
   1 / ↑nd ≤ u := by
  refine div_le_of_le_mul₀ ?_ ?_ ?_
  . exact Nat.cast_nonneg' nd
  . exact le_of_lt hl₂
  . have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
      refine (mul_le_mul_left hl₂).mpr ?_
      rw [Nat.cast_add 2 _, Nat.cast_two]
      refine add_le_add_left ?_ 2
      exact Nat.le_ceil (1 / u)
    rw [hnd]
    refine le_trans ?_ hl₃
    rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
    refine le_of_lt ?_
    refine sub_lt_iff_lt_add.mp ?_
    rw [sub_self 1]
    exact mul_pos hl₂ (two_pos)

lemma imo_1985_p6_unique_nhds_21
  (u : ℝ)
  (hl₂ : 0 < u)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊):
   1 ≤ u * ↑nd := by
  have hl₃: u * (2 + 1 / u) ≤ u * ↑((2:ℕ) + ⌈(1:ℝ) / u⌉₊) := by
    refine (mul_le_mul_left hl₂).mpr ?_
    rw [Nat.cast_add 2 _, Nat.cast_two]
    refine add_le_add_left ?_ 2
    exact Nat.le_ceil (1 / u)
  rw [hnd]
  refine le_trans ?_ hl₃
  rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
  refine le_of_lt ?_
  refine sub_lt_iff_lt_add.mp ?_
  rw [sub_self 1]
  exact mul_pos hl₂ (two_pos)


lemma imo_1985_p6_unique_nhds_22
  (u : ℝ)
  (hl₂ : 0 < u):
   u * (2 + 1 / u) ≤ u * ↑(2 + ⌈1 / u⌉₊) := by
  refine (mul_le_mul_left hl₂).mpr ?_
  rw [Nat.cast_add 2 _, Nat.cast_two]
  refine add_le_add_left ?_ 2
  exact Nat.le_ceil (1 / u)

lemma imo_1985_p6_unique_nhds_23
  (u : ℝ)
  (hl₂ : 0 < u)
  (nd : ℕ)
  (hnd : nd = 2 + ⌈1 / u⌉₊)
  (hl₃ : u * (2 + 1 / u) ≤ u * ↑(2 + ⌈1 / u⌉₊)):
   1 ≤ u * ↑nd := by
  rw [hnd]
  refine le_trans ?_ hl₃
  rw [mul_add, mul_one_div u u, div_self (ne_of_gt hl₂)]
  refine le_of_lt ?_
  refine sub_lt_iff_lt_add.mp ?_
  rw [sub_self 1]
  exact mul_pos hl₂ (two_pos)

lemma imo_1985_p6_unique_top_ind
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (hd₃: ∀ (nd : ↑sd), nd.1 + (1:ℕ) ∈ sd)
  (hd₂ : ∀ (nd : ↑sd), fd a b nd * (2 - 1 / ↑↑nd) ≤ fd a b ⟨nd.1 + 1, hd₃ nd⟩)
  (hi₀ : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi₀⟩) :
  ∀ (nd : ↑sd), fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd := by
  intro nd
  rw [hfd₁ a b nd]
  have hnd₀: 2 ≤ nd.1 := by
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  refine Nat.le_induction ?_ ?_ nd.1 hnd₀
  . have hi₂: i.val = (2:ℕ) := by
      simp_all only [Subtype.forall]
    rw [hfd₁ a b i, hi₂]
    simp
  . simp
    intros n hn₀ hn₁
    have hn₂: n - 1 = n - 2 + 1 := by
      simp
      exact (Nat.sub_eq_iff_eq_add hn₀).mp rfl
    have hn₃: n ∈ sd := by
      rw [hsd]
      exact hn₀
    let nn : ↑sd := ⟨n, hn₃⟩
    have hnn: nn.1 = n := by exact rfl
    have hn₄: nn.1 + 1 ∈ sd := by
      rw [hnn, hsd]
      refine Set.mem_Ici.mpr ?_
      exact Nat.le_add_right_of_le hn₀
    have hn₅: fd a b nn * (2 - 1 / ↑n) ≤ fd a b ⟨nn.1 + 1, hn₄⟩ := by exact hd₂ nn
    rw [hfd₁ a b ⟨nn.1 + 1, hn₄⟩] at hn₅
    have hn₆: f (↑nn + 1) b - f (↑nn + 1) a = f (n + 1) b - f (n + 1) a := by exact rfl
    rw [hn₆] at hn₅
    refine le_trans ?_ hn₅
    rw [hn₂, pow_succ (3/2) (n - 2), ← mul_assoc (fd a b i)]
    refine mul_le_mul ?_ ?_ (by linarith) ?_
    . refine le_of_le_of_eq hn₁ ?_
      rw [hfd₁]
    . refine (div_le_iff₀ (two_pos)).mpr ?_
      rw [sub_mul, one_div_mul_eq_div _ 2]
      refine le_sub_iff_add_le.mpr ?_
      refine le_sub_iff_add_le'.mp ?_
      refine (div_le_iff₀ ?_).mpr ?_
      . refine Nat.cast_pos.mpr ?_
        exact lt_of_lt_of_le (two_pos) hn₀
      . ring_nf
        exact Nat.ofNat_le_cast.mpr hn₀
    . exact le_of_lt (hd₁ nn a b ha₀)



lemma imo_1985_p6_unique_top
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n) :
  ∀ (a b : NNReal),
    a < b →
      (∀ (n : ↑sd), f (↑n) a < f (↑n + 1) a ∧ f (↑n) b < f (↑n + 1) b)
      → Filter.Tendsto (fd a b) Filter.atTop Filter.atTop := by
  intros a b ha₀ ha₁
  have hd₀: ∀ (nd:↑sd), (nd.1 + 1) ∈ sd := by
    intro nd
    let t : ℕ := nd.1
    have ht: t = nd.1 := by rfl
    rw [← ht, hsd]
    refine Set.mem_Ici.mpr ?_
    refine Nat.le_add_right_of_le ?_
    refine Set.mem_Ici.mp ?_
    rw [ht, ← hsd]
    exact nd.2
  have hd₂: ∀ nd, fd a b nd  * (2 - 1 / nd.1) ≤ fd a b ⟨nd.1 + 1, hd₀ nd⟩ := by
    intro nd
    have hnd₀: 0 < nd.1 := by
      have g₀: 2 ≤ nd.1 := by
        refine Set.mem_Ici.mp ?_
        rw [← hsd]
        exact nd.2
      exact Nat.zero_lt_of_lt g₀
    rw [hfd₁, hfd₁, h₁ nd.1 _ hnd₀, h₁ nd.1 _ hnd₀]
    have hnd₁: f (↑nd) b * (f (↑nd) b + 1 / ↑↑nd) - f (↑nd) a * (f (↑nd) a + 1 / ↑↑nd) =
      (f (↑nd) b - f (↑nd) a) * (f (↑nd) b + f (↑nd) a + 1 / nd.1) := by
      ring_nf
    rw [hnd₁]
    refine (mul_le_mul_left ?_).mpr ?_
    . rw [← hfd₁]
      exact hd₁ nd a b ha₀
    . refine le_sub_iff_add_le.mp ?_
      rw [sub_neg_eq_add]
      have hnd₂: 1 - 1 / nd.1 < f (↑nd) b := by
        exact h₇ nd.1 b hnd₀ (ha₁ nd).2
      have hnd₃: 1 - 1 / nd.1 < f (↑nd) a := by
        exact h₇ nd.1 a hnd₀ (ha₁ nd).1
      linarith
  have hi: 2 ∈ sd := by
    rw [hsd]
    decide
  let i : ↑sd := ⟨(2:ℕ), hi⟩
  have hd₃: ∀ nd, fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd := by
    intro nd
    exact imo_1985_p6_unique_top_ind f sd hsd fd hfd₁ hd₁ a b ha₀ hd₀ hd₂ hi i rfl nd
  have hsd₁: Nonempty ↑sd := by
    refine Set.Nonempty.to_subtype ?_
    exact Set.nonempty_of_mem (hd₀ i)
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro z
  by_cases hz₀: z ≤ fd a b i
  . use i
    intros j _
    refine le_trans hz₀ ?_
    refine le_trans ?_ (hd₃ j)
    refine le_mul_of_one_le_right ?_ ?_
    . refine le_of_lt ?_
      exact hd₁ i a b ha₀
    . refine one_le_pow₀ ?_
      linarith
  . push_neg at hz₀
    have hz₁: 0 < fd a b i := by exact hd₁ i a b ha₀
    have hz₂: 0 < Real.log (z / fd a b i) := by
      refine Real.log_pos ?_
      exact (one_lt_div hz₁).mpr hz₀
    let j : ℕ := Nat.ceil (2 + Real.log (z / fd a b i) / Real.log (3 / 2))
    have hj₀: 2 < j := by
      refine Nat.lt_ceil.mpr ?_
      norm_cast
      refine lt_add_of_pos_right 2 ?_
      refine div_pos ?_ ?_
      . exact hz₂
      . refine Real.log_pos ?_
        linarith
    have hj₁: j ∈ sd := by
      rw [hsd]
      exact Set.mem_Ici_of_Ioi hj₀
    use ⟨j, hj₁⟩
    intro k hk₀
    have hk₁: fd a b i * (3 / 2) ^ (k.1 - 2) ≤ fd a b k := by
      exact hd₃ k
    have hk₂: i < k := by
      refine lt_of_lt_of_le ?_ hk₀
      refine Subtype.mk_lt_mk.mpr ?_
      refine Nat.lt_ceil.mpr ?_
      norm_cast
      refine lt_add_of_pos_right 2 ?_
      refine div_pos ?_ ?_
      . exact hz₂
      . refine Real.log_pos ?_
        linarith
    refine le_trans ?_ hk₁
    refine (div_le_iff₀' ?_).mp ?_
    . exact hz₁
    . refine Real.le_pow_of_log_le (by linarith) ?_
      refine (div_le_iff₀ ?_).mp ?_
      . refine Real.log_pos ?_
        linarith
      . rw [Nat.cast_sub ?_]
        . rw [Nat.cast_two]
          refine le_sub_iff_add_le'.mpr ?_
          exact Nat.le_of_ceil_le hk₀
        . exact Nat.le_of_succ_le hk₂


lemma imo_1985_p6_unique_1
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁):
   ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n := by
  intros nd a b hnd₀
  rw [hfd₁]
  refine sub_pos.mpr ?_
  refine hmo₀ nd.1 ?_ hnd₀
  refine lt_of_lt_of_le (Nat.zero_lt_two) ?_
  refine Set.mem_Ici.mp ?_
  rw [← hsd]
  exact Subtype.coe_prop nd



lemma imo_1985_p6_unique_2
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (x y : NNReal)
  (hx₀ : ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1)
  (hy₀ : ∀ (n : ℕ), 0 < n → 0 < f n y ∧ f n y < f (n + 1) y ∧ f (n + 1) y < 1)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n):
   x = y := by
  have hfd₂: ∀ a b, a < b → (∀ n:↑sd, f n.1 a < f (n.1 + 1) a ∧ f n.1 b < f (n.1 + 1) b)
      → Filter.Tendsto (fd a b) Filter.atTop Filter.atTop := by
    intros a b ha₀ ha₁
    exact imo_1985_p6_unique_top f h₁ h₇ sd hsd fd hfd₁ hd₁ a b ha₀ ha₁
  have hfd₃: ∀ a b, a < b → (∀ (n:↑sd), (1 - 1 / n.1 < f n.1 a ∧ 1 - 1 / n.1 < f n.1 b) ∧ (f n.1 a < 1 ∧ f n.1 b < 1))
      → Filter.Tendsto (fd a b) Filter.atTop (nhds 0) := by
    intros a b ha₀ ha₁
    exact imo_1985_p6_unique_nhds f sd hsd fd hfd₁ hd₁ a b ha₀ ha₁
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  have hd₂: Nonempty ↑sd := by
    refine Set.Nonempty.to_subtype ?_
    rw [hsd]
    exact Set.nonempty_Ici
  by_contra! hc₀
  by_cases hy₁: x < y
  . have hy₂: Filter.Tendsto (fd x y) Filter.atTop Filter.atTop := by
      refine hfd₂ x y hy₁ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (two_pos) (hd₁ nd)
      constructor
      . exact (hx₀ nd.1 hnd₀).2.1
      . exact (hy₀ nd.1 hnd₀).2.1
    have hy₃: Filter.Tendsto (fd x y) Filter.atTop (nhds 0) := by
      refine hfd₃ x y hy₁ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by
        refine lt_of_lt_of_le ?_ (hd₁ nd)
        exact Nat.zero_lt_two
      have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
      have hnd₂: 0 < nd.1 - 1 := by
        refine Nat.sub_pos_of_lt ?_
        refine lt_of_lt_of_le ?_ (hd₁ nd)
        exact Nat.one_lt_two
      constructor
      . constructor
        . refine h₇ nd.1 x hnd₀ ?_
          exact (hx₀ (nd.1) hnd₀).2.1
        . refine h₇ nd.1 y hnd₀ ?_
          exact (hy₀ (nd.1) hnd₀).2.1
      . constructor
        . rw [← hnd₁]
          exact (hx₀ (nd.1 - 1) hnd₂).2.2
        . rw [← hnd₁]
          exact (hy₀ (nd.1 - 1) hnd₂).2.2
    apply Filter.tendsto_atTop_atTop.mp at hy₂
    apply tendsto_atTop_nhds.mp at hy₃
    contrapose! hy₃
    clear hy₃
    let sx : Set ℝ := Set.Ioo (-1) 1
    use sx
    constructor
    . refine Set.mem_Ioo.mpr ?_
      simp
    constructor
    . exact isOpen_Ioo
    . intro N
      have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
      obtain ⟨i, hi₀⟩ := hy₅
      have hi₁: (N.1 + i.1) ∈ sd := by
        nth_rw 1 [hsd]
        refine Set.mem_Ici.mpr ?_
        rw [← add_zero 2]
        refine Nat.add_le_add ?_ ?_
        . exact (hd₁ N)
        . refine le_trans ?_ (hd₁ i)
          exact Nat.zero_le 2
      let a : ↑sd := ⟨N + i, hi₁⟩
      use a
      constructor
      . refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_right ↑N ↑i
      . refine Set.not_mem_Ioo_of_ge ?_
        have hi₂: ↑↑N + 3 ≤ fd x y a := by
          refine hi₀ a ?_
          refine Subtype.mk_le_mk.mpr ?_
          exact Nat.le_add_left ↑i ↑N
        refine le_trans ?_ hi₂
        norm_cast
        exact Nat.le_add_left 1 (↑N + 2)
  . have hy₂: y < x := by
      push_neg at hy₁
      exact lt_of_le_of_ne hy₁ hc₀.symm
    have hy₃: Filter.Tendsto (fd y x) Filter.atTop Filter.atTop := by
      refine hfd₂ y x hy₂ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (two_pos) (hd₁ nd)
      constructor
      . exact (hy₀ nd.1 hnd₀).2.1
      . exact (hx₀ nd.1 hnd₀).2.1
    have hy₄: Filter.Tendsto (fd y x) Filter.atTop (nhds 0) := by
      refine hfd₃ y x hy₂ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (Nat.zero_lt_two) (hd₁ nd)
      have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
      have hnd₂: 0 < nd.1 - 1 := by
        refine Nat.sub_pos_of_lt ?_
        exact lt_of_lt_of_le (Nat.one_lt_two) (hd₁ nd)
      constructor
      . constructor
        . refine h₇ nd.1 y hnd₀ ?_
          exact (hy₀ (nd.1) hnd₀).2.1
        . refine h₇ nd.1 x hnd₀ ?_
          exact (hx₀ (nd.1) hnd₀).2.1
      . constructor
        . rw [← hnd₁]
          exact (hy₀ (nd.1 - 1) hnd₂).2.2
        . rw [← hnd₁]
          exact (hx₀ (nd.1 - 1) hnd₂).2.2
    apply Filter.tendsto_atTop_atTop.mp at hy₃
    apply tendsto_atTop_nhds.mp at hy₄
    contrapose! hy₄
    clear hy₄
    let sx : Set ℝ := Set.Ioo (-1) 1
    use sx
    constructor
    . refine Set.mem_Ioo.mpr ?_
      simp
    constructor
    . exact isOpen_Ioo
    . intro N
      have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd y x a := by exact hy₃ (N + 3)
      obtain ⟨i, hi₀⟩ := hy₅
      have hi₁: (N.1 + i.1) ∈ sd := by
        nth_rw 1 [hsd]
        refine Set.mem_Ici.mpr ?_
        rw [← add_zero 2]
        refine Nat.add_le_add ?_ ?_
        . exact hd₁ N
        . refine le_trans ?_ (hd₁ i)
          exact Nat.zero_le 2
      let a : ↑sd := ⟨N + i, hi₁⟩
      use a
      constructor
      . refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_right ↑N ↑i
      . refine Set.not_mem_Ioo_of_ge ?_
        have hi₂: ↑↑N + 3 ≤ fd y x a := by
          refine hi₀ a ?_
          refine Subtype.mk_le_mk.mpr ?_
          exact Nat.le_add_left ↑i ↑N
        refine le_trans ?_ hi₂
        norm_cast
        exact Nat.le_add_left 1 (↑N + 2)




lemma imo_1985_p6_unique_3
  (f : ℕ → NNReal → ℝ)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (x y : NNReal)
  (hx₀ : ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1)
  (hy₀ : ∀ (n : ℕ), 0 < n → 0 < f n y ∧ f n y < f (n + 1) y ∧ f (n + 1) y < 1)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₂ : ∀ (a b : NNReal),
    (a < b →
      (∀ (n : ↑sd), f (↑n) a < f (↑n + 1) a ∧ f (↑n) b < f (↑n + 1) b) → Filter.Tendsto (fd a b) Filter.atTop Filter.atTop))
  (hfd₃ : ∀ (a b : NNReal),
    a < b →
      (∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1) →
        (Filter.Tendsto (fd a b) Filter.atTop (nhds 0)) ):
   x = y := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  have hd₂: Nonempty ↑sd := by
    refine Set.Nonempty.to_subtype ?_
    rw [hsd]
    exact Set.nonempty_Ici
  by_contra! hc₀
  by_cases hy₁: x < y
  . have hy₂: Filter.Tendsto (fd x y) Filter.atTop Filter.atTop := by
      refine hfd₂ x y hy₁ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (two_pos) (hd₁ nd)
      constructor
      . exact (hx₀ nd.1 hnd₀).2.1
      . exact (hy₀ nd.1 hnd₀).2.1
    have hy₃: Filter.Tendsto (fd x y) Filter.atTop (nhds 0) := by
      refine hfd₃ x y hy₁ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by
        refine lt_of_lt_of_le ?_ (hd₁ nd)
        exact Nat.zero_lt_two
      have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
      have hnd₂: 0 < nd.1 - 1 := by
        refine Nat.sub_pos_of_lt ?_
        refine lt_of_lt_of_le ?_ (hd₁ nd)
        exact Nat.one_lt_two
      constructor
      . constructor
        . refine h₇ nd.1 x hnd₀ ?_
          exact (hx₀ (nd.1) hnd₀).2.1
        . refine h₇ nd.1 y hnd₀ ?_
          exact (hy₀ (nd.1) hnd₀).2.1
      . constructor
        . rw [← hnd₁]
          exact (hx₀ (nd.1 - 1) hnd₂).2.2
        . rw [← hnd₁]
          exact (hy₀ (nd.1 - 1) hnd₂).2.2
    apply Filter.tendsto_atTop_atTop.mp at hy₂
    apply tendsto_atTop_nhds.mp at hy₃
    contrapose! hy₃
    clear hy₃
    let sx : Set ℝ := Set.Ioo (-1) 1
    use sx
    constructor
    . refine Set.mem_Ioo.mpr ?_
      simp
    constructor
    . exact isOpen_Ioo
    . intro N
      have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
      obtain ⟨i, hi₀⟩ := hy₅
      have hi₁: (N.1 + i.1) ∈ sd := by
        nth_rw 1 [hsd]
        refine Set.mem_Ici.mpr ?_
        rw [← add_zero 2]
        refine Nat.add_le_add ?_ ?_
        . exact hd₁ N
        . refine le_trans ?_ (hd₁ i)
          exact Nat.zero_le 2
      let a : ↑sd := ⟨N + i, hi₁⟩
      use a
      constructor
      . refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_right ↑N ↑i
      . refine Set.not_mem_Ioo_of_ge ?_
        have hi₂: ↑↑N + 3 ≤ fd x y a := by
          refine hi₀ a ?_
          refine Subtype.mk_le_mk.mpr ?_
          exact Nat.le_add_left ↑i ↑N
        refine le_trans ?_ hi₂
        norm_cast
        exact Nat.le_add_left 1 (↑N + 2)
  . have hy₂: y < x := by
      push_neg at hy₁
      exact lt_of_le_of_ne hy₁ hc₀.symm
    have hy₃: Filter.Tendsto (fd y x) Filter.atTop Filter.atTop := by
      refine hfd₂ y x hy₂ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (two_pos) (hd₁ nd)
      constructor
      . exact (hy₀ nd.1 hnd₀).2.1
      . exact (hx₀ nd.1 hnd₀).2.1
    have hy₄: Filter.Tendsto (fd y x) Filter.atTop (nhds 0) := by
      refine hfd₃ y x hy₂ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (Nat.zero_lt_two) (hd₁ nd)
      have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
      have hnd₂: 0 < nd.1 - 1 := by
        refine Nat.sub_pos_of_lt ?_
        exact lt_of_lt_of_le (Nat.one_lt_two) (hd₁ nd)
      constructor
      . constructor
        . refine h₇ nd.1 y hnd₀ ?_
          exact (hy₀ (nd.1) hnd₀).2.1
        . refine h₇ nd.1 x hnd₀ ?_
          exact (hx₀ (nd.1) hnd₀).2.1
      . constructor
        . rw [← hnd₁]
          exact (hy₀ (nd.1 - 1) hnd₂).2.2
        . rw [← hnd₁]
          exact (hx₀ (nd.1 - 1) hnd₂).2.2
    apply Filter.tendsto_atTop_atTop.mp at hy₃
    apply tendsto_atTop_nhds.mp at hy₄
    contrapose! hy₄
    clear hy₄
    let sx : Set ℝ := Set.Ioo (-1) 1
    use sx
    constructor
    . refine Set.mem_Ioo.mpr ?_
      simp
    constructor
    . exact isOpen_Ioo
    . intro N
      have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd y x a := by exact hy₃ (N + 3)
      obtain ⟨i, hi₀⟩ := hy₅
      have hi₁: (N.1 + i.1) ∈ sd := by
        nth_rw 1 [hsd]
        refine Set.mem_Ici.mpr ?_
        rw [← add_zero 2]
        refine Nat.add_le_add ?_ ?_
        . exact hd₁ N
        . refine le_trans ?_ (hd₁ i)
          exact Nat.zero_le 2
      let a : ↑sd := ⟨N + i, hi₁⟩
      use a
      constructor
      . refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_right ↑N ↑i
      . refine Set.not_mem_Ioo_of_ge ?_
        have hi₂: ↑↑N + 3 ≤ fd y x a := by
          refine hi₀ a ?_
          refine Subtype.mk_le_mk.mpr ?_
          exact Nat.le_add_left ↑i ↑N
        refine le_trans ?_ hi₂
        norm_cast
        exact Nat.le_add_left 1 (↑N + 2)



lemma imo_1985_p6_unique_4
  (f : ℕ → NNReal → ℝ)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (x y : NNReal)
  (hx₀ : ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1)
  (hy₀ : ∀ (n : ℕ), 0 < n → 0 < f n y ∧ f n y < f (n + 1) y ∧ f (n + 1) y < 1)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₂ : ∀ (a b : NNReal),
    a < b →
      ((∀ (n : ↑sd), f (↑n) a < f (↑n + 1) a ∧ f (↑n) b < f (↑n + 1) b) → Filter.Tendsto (fd a b) Filter.atTop Filter.atTop))
  (hfd₃ : ∀ (a b : NNReal),
    a < b →
      (∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1) →
        (Filter.Tendsto (fd a b) Filter.atTop (nhds 0)))
  (hc₀ : x ≠ y):
   False := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  have hd₂: Nonempty ↑sd := by
    refine Set.Nonempty.to_subtype ?_
    rw [hsd]
    exact Set.nonempty_Ici
  by_cases hy₁: x < y
  . have hy₂: Filter.Tendsto (fd x y) Filter.atTop Filter.atTop := by
      refine hfd₂ x y hy₁ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (two_pos) (hd₁ nd)
      constructor
      . exact (hx₀ nd.1 hnd₀).2.1
      . exact (hy₀ nd.1 hnd₀).2.1
    have hy₃: Filter.Tendsto (fd x y) Filter.atTop (nhds 0) := by
      refine hfd₃ x y hy₁ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by
        refine lt_of_lt_of_le ?_ (hd₁ nd)
        exact Nat.zero_lt_two
      have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
      have hnd₂: 0 < nd.1 - 1 := by
        refine Nat.sub_pos_of_lt ?_
        refine lt_of_lt_of_le ?_ (hd₁ nd)
        exact Nat.one_lt_two
      constructor
      . constructor
        . refine h₇ nd.1 x hnd₀ ?_
          exact (hx₀ (nd.1) hnd₀).2.1
        . refine h₇ nd.1 y hnd₀ ?_
          exact (hy₀ (nd.1) hnd₀).2.1
      . constructor
        . rw [← hnd₁]
          exact (hx₀ (nd.1 - 1) hnd₂).2.2
        . rw [← hnd₁]
          exact (hy₀ (nd.1 - 1) hnd₂).2.2
    apply Filter.tendsto_atTop_atTop.mp at hy₂
    apply tendsto_atTop_nhds.mp at hy₃
    contrapose! hy₃
    clear hy₃
    let sx : Set ℝ := Set.Ioo (-1) 1
    use sx
    constructor
    . refine Set.mem_Ioo.mpr ?_
      simp
    constructor
    . exact isOpen_Ioo
    . intro N
      have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
      obtain ⟨i, hi₀⟩ := hy₅
      have hi₁: (N.1 + i.1) ∈ sd := by
        nth_rw 1 [hsd]
        refine Set.mem_Ici.mpr ?_
        rw [← add_zero 2]
        refine Nat.add_le_add ?_ ?_
        . exact (hd₁ N)
        . refine le_trans ?_ (hd₁ i)
          exact Nat.zero_le 2
      let a : ↑sd := ⟨N + i, hi₁⟩
      use a
      constructor
      . refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_right ↑N ↑i
      . refine Set.not_mem_Ioo_of_ge ?_
        have hi₂: ↑↑N + 3 ≤ fd x y a := by
          refine hi₀ a ?_
          refine Subtype.mk_le_mk.mpr ?_
          exact Nat.le_add_left ↑i ↑N
        refine le_trans ?_ hi₂
        norm_cast
        exact Nat.le_add_left 1 (↑N + 2)
  . have hy₂: y < x := by
      push_neg at hy₁
      exact lt_of_le_of_ne hy₁ hc₀.symm
    have hy₃: Filter.Tendsto (fd y x) Filter.atTop Filter.atTop := by
      refine hfd₂ y x hy₂ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (two_pos) (hd₁ nd)
      constructor
      . exact (hy₀ nd.1 hnd₀).2.1
      . exact (hx₀ nd.1 hnd₀).2.1
    have hy₄: Filter.Tendsto (fd y x) Filter.atTop (nhds 0) := by
      refine hfd₃ y x hy₂ ?_
      intro nd
      have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (Nat.zero_lt_two) (hd₁ nd)
      have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
      have hnd₂: 0 < nd.1 - 1 := by
        refine Nat.sub_pos_of_lt ?_
        exact lt_of_lt_of_le (Nat.one_lt_two) (hd₁ nd)
      constructor
      . constructor
        . refine h₇ nd.1 y hnd₀ ?_
          exact (hy₀ (nd.1) hnd₀).2.1
        . refine h₇ nd.1 x hnd₀ ?_
          exact (hx₀ (nd.1) hnd₀).2.1
      . constructor
        . rw [← hnd₁]
          exact (hy₀ (nd.1 - 1) hnd₂).2.2
        . rw [← hnd₁]
          exact (hx₀ (nd.1 - 1) hnd₂).2.2
    apply Filter.tendsto_atTop_atTop.mp at hy₃
    apply tendsto_atTop_nhds.mp at hy₄
    contrapose! hy₄
    clear hy₄
    let sx : Set ℝ := Set.Ioo (-1) 1
    use sx
    constructor
    . refine Set.mem_Ioo.mpr ?_
      simp
    constructor
    . exact isOpen_Ioo
    . intro N
      have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd y x a := by exact hy₃ (N + 3)
      obtain ⟨i, hi₀⟩ := hy₅
      have hi₁: (N.1 + i.1) ∈ sd := by
        nth_rw 1 [hsd]
        refine Set.mem_Ici.mpr ?_
        rw [← add_zero 2]
        refine Nat.add_le_add ?_ ?_
        . exact hd₁ N
        . refine le_trans ?_ (hd₁ i)
          exact Nat.zero_le 2
      let a : ↑sd := ⟨N + i, hi₁⟩
      use a
      constructor
      . refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_right ↑N ↑i
      . refine Set.not_mem_Ioo_of_ge ?_
        have hi₂: ↑↑N + 3 ≤ fd y x a := by
          refine hi₀ a ?_
          refine Subtype.mk_le_mk.mpr ?_
          exact Nat.le_add_left ↑i ↑N
        refine le_trans ?_ hi₂
        norm_cast
        exact Nat.le_add_left 1 (↑N + 2)



lemma imo_1985_p6_unique_5
  (f : ℕ → NNReal → ℝ)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (x y : NNReal)
  (hx₀ : ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1)
  (hy₀ : ∀ (n : ℕ), 0 < n → 0 < f n y ∧ f n y < f (n + 1) y ∧ f (n + 1) y < 1)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₂ : ∀ (a b : NNReal),
    a < b →
      ((∀ (n : ↑sd), f (↑n) a < f (↑n + 1) a ∧ f (↑n) b < f (↑n + 1) b) → Filter.Tendsto (fd a b) Filter.atTop Filter.atTop))
  (hfd₃ : ∀ (a b : NNReal),
    a < b →
      (∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1) →
        (Filter.Tendsto (fd a b) Filter.atTop (nhds 0)))
  (hy₁ : x < y):
   False := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  have hd₂: Nonempty ↑sd := by
    refine Set.Nonempty.to_subtype ?_
    rw [hsd]
    exact Set.nonempty_Ici
  have hy₂: Filter.Tendsto (fd x y) Filter.atTop Filter.atTop := by
    refine hfd₂ x y hy₁ ?_
    intro nd
    have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (two_pos) (hd₁ nd)
    constructor
    . exact (hx₀ nd.1 hnd₀).2.1
    . exact (hy₀ nd.1 hnd₀).2.1
  have hy₃: Filter.Tendsto (fd x y) Filter.atTop (nhds 0) := by
    refine hfd₃ x y hy₁ ?_
    intro nd
    have hnd₀: 0 < nd.1 := by
      refine lt_of_lt_of_le ?_ (hd₁ nd)
      exact Nat.zero_lt_two
    have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
    have hnd₂: 0 < nd.1 - 1 := by
      refine Nat.sub_pos_of_lt ?_
      refine lt_of_lt_of_le ?_ (hd₁ nd)
      exact Nat.one_lt_two
    constructor
    . constructor
      . refine h₇ nd.1 x hnd₀ ?_
        exact (hx₀ (nd.1) hnd₀).2.1
      . refine h₇ nd.1 y hnd₀ ?_
        exact (hy₀ (nd.1) hnd₀).2.1
    . constructor
      . rw [← hnd₁]
        exact (hx₀ (nd.1 - 1) hnd₂).2.2
      . rw [← hnd₁]
        exact (hy₀ (nd.1 - 1) hnd₂).2.2
  apply Filter.tendsto_atTop_atTop.mp at hy₂
  apply tendsto_atTop_nhds.mp at hy₃
  contrapose! hy₃
  clear hy₃
  let sx : Set ℝ := Set.Ioo (-1) 1
  use sx
  constructor
  . refine Set.mem_Ioo.mpr ?_
    simp
  constructor
  . exact isOpen_Ioo
  . intro N
    have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
    obtain ⟨i, hi₀⟩ := hy₅
    have hi₁: (N.1 + i.1) ∈ sd := by
      nth_rw 1 [hsd]
      refine Set.mem_Ici.mpr ?_
      rw [← add_zero 2]
      refine Nat.add_le_add ?_ ?_
      . exact hd₁ N
      . refine le_trans ?_ (hd₁ i)
        exact Nat.zero_le 2
    let a : ↑sd := ⟨N + i, hi₁⟩
    use a
    constructor
    . refine Subtype.mk_le_mk.mpr ?_
      exact Nat.le_add_right ↑N ↑i
    . refine Set.not_mem_Ioo_of_ge ?_
      have hi₂: ↑↑N + 3 ≤ fd x y a := by
        refine hi₀ a ?_
        refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_left ↑i ↑N
      refine le_trans ?_ hi₂
      norm_cast
      exact Nat.le_add_left 1 (↑N + 2)

lemma imo_1985_p6_unique_6
  (f : ℕ → NNReal → ℝ)
  (x y : NNReal)
  (hx₀ : ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1)
  (hy₀ : ∀ (n : ℕ), 0 < n → 0 < f n y ∧ f n y < f (n + 1) y ∧ f (n + 1) y < 1)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₂ : ∀ (a b : NNReal),
    a < b →
      (∀ (n : ↑sd), f (↑n) a < f (↑n + 1) a ∧ f (↑n) b < f (↑n + 1) b) → Filter.Tendsto (fd a b) Filter.atTop Filter.atTop)
  (hy₁ : x < y):
   Filter.Tendsto (fd x y) Filter.atTop Filter.atTop := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  refine hfd₂ x y hy₁ ?_
  intro nd
  have hnd₀: 0 < nd.1 := by exact lt_of_lt_of_le (two_pos) (hd₁ nd)
  constructor
  . exact (hx₀ nd.1 hnd₀).2.1
  . exact (hy₀ nd.1 hnd₀).2.1

lemma imo_1985_p6_unique_7
  (f : ℕ → NNReal → ℝ)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (x y : NNReal)
  (hx₀ : ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1)
  (hy₀ : ∀ (n : ℕ), 0 < n → 0 < f n y ∧ f n y < f (n + 1) y ∧ f (n + 1) y < 1)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₃ : ∀ (a b : NNReal),
    a < b →
      (∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1) →
        (Filter.Tendsto (fd a b) Filter.atTop (nhds 0)))
  (hy₁ : x < y)
  (hy₂ : Filter.Tendsto (fd x y) Filter.atTop Filter.atTop):
   False := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  have hd₂: Nonempty ↑sd := by
    refine Set.Nonempty.to_subtype ?_
    rw [hsd]
    exact Set.nonempty_Ici
  have hy₃: Filter.Tendsto (fd x y) Filter.atTop (nhds 0) := by
    refine hfd₃ x y hy₁ ?_
    intro nd
    have hnd₀: 0 < nd.1 := by
      refine lt_of_lt_of_le ?_ (hd₁ nd)
      exact Nat.zero_lt_two
    have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
    have hnd₂: 0 < nd.1 - 1 := by
      refine Nat.sub_pos_of_lt ?_
      refine lt_of_lt_of_le ?_ (hd₁ nd)
      exact Nat.one_lt_two
    constructor
    . constructor
      . refine h₇ nd.1 x hnd₀ ?_
        exact (hx₀ (nd.1) hnd₀).2.1
      . refine h₇ nd.1 y hnd₀ ?_
        exact (hy₀ (nd.1) hnd₀).2.1
    . constructor
      . rw [← hnd₁]
        exact (hx₀ (nd.1 - 1) hnd₂).2.2
      . rw [← hnd₁]
        exact (hy₀ (nd.1 - 1) hnd₂).2.2
  apply Filter.tendsto_atTop_atTop.mp at hy₂
  apply tendsto_atTop_nhds.mp at hy₃
  contrapose! hy₃
  clear hy₃
  let sx : Set ℝ := Set.Ioo (-1) 1
  use sx
  constructor
  . refine Set.mem_Ioo.mpr ?_
    simp
  constructor
  . exact isOpen_Ioo
  . intro N
    have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
    obtain ⟨i, hi₀⟩ := hy₅
    have hi₁: (N.1 + i.1) ∈ sd := by
      nth_rw 1 [hsd]
      refine Set.mem_Ici.mpr ?_
      rw [← add_zero 2]
      refine Nat.add_le_add ?_ ?_
      . exact hd₁ N
      . refine le_trans ?_ (hd₁ i)
        exact Nat.zero_le 2
    let a : ↑sd := ⟨N + i, hi₁⟩
    use a
    constructor
    . refine Subtype.mk_le_mk.mpr ?_
      exact Nat.le_add_right ↑N ↑i
    . refine Set.not_mem_Ioo_of_ge ?_
      have hi₂: ↑↑N + 3 ≤ fd x y a := by
        refine hi₀ a ?_
        refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_left ↑i ↑N
      refine le_trans ?_ hi₂
      norm_cast
      exact Nat.le_add_left 1 (↑N + 2)


lemma imo_1985_p6_unique_8
  (f : ℕ → NNReal → ℝ)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (x y : NNReal)
  (hx₀ : ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1)
  (hy₀ : ∀ (n : ℕ), 0 < n → 0 < f n y ∧ f n y < f (n + 1) y ∧ f (n + 1) y < 1)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₃ : ∀ (a b : NNReal),
    a < b →
      (∀ (n : ↑sd), (1 - 1 / ↑↑n < f (↑n) a ∧ 1 - 1 / ↑↑n < f (↑n) b) ∧ f (↑n) a < 1 ∧ f (↑n) b < 1) →
        (Filter.Tendsto (fd a b) Filter.atTop (nhds 0)))
  (hy₁ : x < y):
   Filter.Tendsto (fd x y) Filter.atTop (nhds 0) := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  refine hfd₃ x y hy₁ ?_
  intro nd
  have hnd₀: 0 < nd.1 := by
    refine lt_of_lt_of_le ?_ (hd₁ nd)
    exact Nat.zero_lt_two
  have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
  have hnd₂: 0 < nd.1 - 1 := by
    refine Nat.sub_pos_of_lt ?_
    refine lt_of_lt_of_le ?_ (hd₁ nd)
    exact Nat.one_lt_two
  constructor
  . constructor
    . refine h₇ nd.1 x hnd₀ ?_
      exact (hx₀ (nd.1) hnd₀).2.1
    . refine h₇ nd.1 y hnd₀ ?_
      exact (hy₀ (nd.1) hnd₀).2.1
  . constructor
    . rw [← hnd₁]
      exact (hx₀ (nd.1 - 1) hnd₂).2.2
    . rw [← hnd₁]
      exact (hy₀ (nd.1 - 1) hnd₂).2.2

lemma imo_1985_p6_unique_9
  (f : ℕ → NNReal → ℝ)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (x y : NNReal)
  (hx₀ : ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1)
  (hy₀ : ∀ (n : ℕ), 0 < n → 0 < f n y ∧ f n y < f (n + 1) y ∧ f (n + 1) y < 1)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (nd : ↑sd):
   (1 - 1 / ↑↑nd < f (↑nd) x ∧ 1 - 1 / ↑↑nd < f (↑nd) y) ∧ f (↑nd) x < 1 ∧ f (↑nd) y < 1 := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  have hnd₀: 0 < nd.1 := by
    refine lt_of_lt_of_le ?_ (hd₁ nd)
    exact Nat.zero_lt_two
  have hnd₁: nd.1 - 1 + 1 = nd.1 := by exact Nat.sub_add_cancel hnd₀
  have hnd₂: 0 < nd.1 - 1 := by
    refine Nat.sub_pos_of_lt ?_
    refine lt_of_lt_of_le ?_ (hd₁ nd)
    exact Nat.one_lt_two
  constructor
  . constructor
    . refine h₇ nd.1 x hnd₀ ?_
      exact (hx₀ (nd.1) hnd₀).2.1
    . refine h₇ nd.1 y hnd₀ ?_
      exact (hy₀ (nd.1) hnd₀).2.1
  . constructor
    . rw [← hnd₁]
      exact (hx₀ (nd.1 - 1) hnd₂).2.2
    . rw [← hnd₁]
      exact (hy₀ (nd.1 - 1) hnd₂).2.2

lemma imo_1985_p6_unique_10
  (x y : NNReal)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hy₂ : Filter.Tendsto (fd x y) Filter.atTop Filter.atTop)
  (hy₃ : Filter.Tendsto (fd x y) Filter.atTop (nhds 0)):
   False := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  have hd₂: Nonempty ↑sd := by
    refine Set.Nonempty.to_subtype ?_
    rw [hsd]
    exact Set.nonempty_Ici
  apply Filter.tendsto_atTop_atTop.mp at hy₂
  apply tendsto_atTop_nhds.mp at hy₃
  contrapose! hy₃
  clear hy₃
  let sx : Set ℝ := Set.Ioo (-1) 1
  use sx
  constructor
  . refine Set.mem_Ioo.mpr ?_
    simp
  constructor
  . exact isOpen_Ioo
  . intro N
    have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
    obtain ⟨i, hi₀⟩ := hy₅
    have hi₁: (N.1 + i.1) ∈ sd := by
      nth_rw 1 [hsd]
      refine Set.mem_Ici.mpr ?_
      rw [← add_zero 2]
      refine Nat.add_le_add ?_ ?_
      . exact hd₁ N
      . refine le_trans ?_ (hd₁ i)
        exact Nat.zero_le 2
    let a : ↑sd := ⟨N + i, hi₁⟩
    use a
    constructor
    . refine Subtype.mk_le_mk.mpr ?_
      exact Nat.le_add_right ↑N ↑i
    . refine Set.not_mem_Ioo_of_ge ?_
      have hi₂: ↑↑N + 3 ≤ fd x y a := by
        refine hi₀ a ?_
        refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_left ↑i ↑N
      refine le_trans ?_ hi₂
      norm_cast
      exact Nat.le_add_left 1 (↑N + 2)


lemma imo_1985_p6_unique_11
  (x y : NNReal)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hy₃ : Filter.Tendsto (fd x y) Filter.atTop (nhds 0))
  (hy₂ : ∀ (b : ℝ), ∃ i, ∀ (a : ↑sd), i ≤ a → b ≤ fd x y a):
   False := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  have hd₂: Nonempty ↑sd := by
    refine Set.Nonempty.to_subtype ?_
    rw [hsd]
    exact Set.nonempty_Ici
  apply tendsto_atTop_nhds.mp at hy₃
  contrapose! hy₃
  clear hy₃
  let sx : Set ℝ := Set.Ioo (-1) 1
  use sx
  constructor
  . refine Set.mem_Ioo.mpr ?_
    simp
  constructor
  . exact isOpen_Ioo
  . intro N
    have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
    obtain ⟨i, hi₀⟩ := hy₅
    have hi₁: (N.1 + i.1) ∈ sd := by
      nth_rw 1 [hsd]
      refine Set.mem_Ici.mpr ?_
      rw [← add_zero 2]
      refine Nat.add_le_add ?_ ?_
      . exact hd₁ N
      . refine le_trans ?_ (hd₁ i)
        exact Nat.zero_le 2
    let a : ↑sd := ⟨N + i, hi₁⟩
    use a
    constructor
    . refine Subtype.mk_le_mk.mpr ?_
      exact Nat.le_add_right ↑N ↑i
    . refine Set.not_mem_Ioo_of_ge ?_
      have hi₂: ↑↑N + 3 ≤ fd x y a := by
        refine hi₀ a ?_
        refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_left ↑i ↑N
      refine le_trans ?_ hi₂
      norm_cast
      exact Nat.le_add_left 1 (↑N + 2)


lemma imo_1985_p6_unique_12
  (x y : NNReal)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hy₂ : ∀ (b : ℝ), ∃ i, ∀ (a : ↑sd), i ≤ a → b ≤ fd x y a)
  (hy₃ : ∀ (U : Set ℝ), 0 ∈ U → IsOpen U → ∃ N, ∀ (n : ↑sd), N ≤ n → fd x y n ∈ U):
   False := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  contrapose! hy₃
  clear hy₃
  let sx : Set ℝ := Set.Ioo (-1) 1
  use sx
  constructor
  . refine Set.mem_Ioo.mpr ?_
    simp
  constructor
  . exact isOpen_Ioo
  . intro N
    have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
    obtain ⟨i, hi₀⟩ := hy₅
    have hi₁: (N.1 + i.1) ∈ sd := by
      nth_rw 1 [hsd]
      refine Set.mem_Ici.mpr ?_
      rw [← add_zero 2]
      refine Nat.add_le_add ?_ ?_
      . exact hd₁ N
      . refine le_trans ?_ (hd₁ i)
        exact Nat.zero_le 2
    let a : ↑sd := ⟨N + i, hi₁⟩
    use a
    constructor
    . refine Subtype.mk_le_mk.mpr ?_
      exact Nat.le_add_right ↑N ↑i
    . refine Set.not_mem_Ioo_of_ge ?_
      have hi₂: ↑↑N + 3 ≤ fd x y a := by
        refine hi₀ a ?_
        refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_left ↑i ↑N
      refine le_trans ?_ hi₂
      norm_cast
      exact Nat.le_add_left 1 (↑N + 2)

lemma imo_1985_p6_unique_13
  (x y : NNReal)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hy₂ : ∀ (b : ℝ), ∃ i, ∀ (a : ↑sd), i ≤ a → b ≤ fd x y a):
   ∃ U, 0 ∈ U ∧ IsOpen U ∧ ∀ (N : ↑sd), ∃ n, N ≤ n ∧ fd x y n ∉ U := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  let sx : Set ℝ := Set.Ioo (-1) 1
  use sx
  constructor
  . refine Set.mem_Ioo.mpr ?_
    simp
  constructor
  . exact isOpen_Ioo
  . intro N
    have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
    obtain ⟨i, hi₀⟩ := hy₅
    have hi₁: (N.1 + i.1) ∈ sd := by
      nth_rw 1 [hsd]
      refine Set.mem_Ici.mpr ?_
      rw [← add_zero 2]
      refine Nat.add_le_add ?_ ?_
      . exact hd₁ N
      . refine le_trans ?_ (hd₁ i)
        exact Nat.zero_le 2
    let a : ↑sd := ⟨N + i, hi₁⟩
    use a
    constructor
    . refine Subtype.mk_le_mk.mpr ?_
      exact Nat.le_add_right ↑N ↑i
    . refine Set.not_mem_Ioo_of_ge ?_
      have hi₂: ↑↑N + 3 ≤ fd x y a := by
        refine hi₀ a ?_
        refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_left ↑i ↑N
      refine le_trans ?_ hi₂
      norm_cast
      exact Nat.le_add_left 1 (↑N + 2)


lemma imo_1985_p6_unique_14
  (x y : NNReal)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hy₂ : ∀ (b : ℝ), ∃ i, ∀ (a : ↑sd), i ≤ a → b ≤ fd x y a)
  (sx : Set ℝ)
  (hsx : sx = Set.Ioo (-1) 1):
   ∃ U, 0 ∈ U ∧ IsOpen U ∧ ∀ (N : ↑sd), ∃ n, N ≤ n ∧ fd x y n ∉ U := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  use sx
  constructor
  . rw [hsx]
    refine Set.mem_Ioo.mpr ?_
    simp
  constructor
  . rw [hsx]
    exact isOpen_Ioo
  . intro N
    have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
    obtain ⟨i, hi₀⟩ := hy₅
    have hi₁: (N.1 + i.1) ∈ sd := by
      nth_rw 1 [hsd]
      refine Set.mem_Ici.mpr ?_
      rw [← add_zero 2]
      refine Nat.add_le_add ?_ ?_
      . exact hd₁ N
      . refine le_trans ?_ (hd₁ i)
        exact Nat.zero_le 2
    let a : ↑sd := ⟨N + i, hi₁⟩
    use a
    constructor
    . refine Subtype.mk_le_mk.mpr ?_
      exact Nat.le_add_right ↑N ↑i
    . rw [hsx]
      refine Set.not_mem_Ioo_of_ge ?_
      have hi₂: ↑↑N + 3 ≤ fd x y a := by
        refine hi₀ a ?_
        refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_left ↑i ↑N
      refine le_trans ?_ hi₂
      norm_cast
      exact Nat.le_add_left 1 (↑N + 2)

lemma imo_1985_p6_unique_15
  (x y : NNReal)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hy₂ : ∀ (b : ℝ), ∃ i, ∀ (a : ↑sd), i ≤ a → b ≤ fd x y a)
  (sx : Set ℝ)
  (hsx : sx = Set.Ioo (-1) 1):
   0 ∈ sx ∧ IsOpen sx ∧ ∀ (N : ↑sd), ∃ n, N ≤ n ∧ fd x y n ∉ sx := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  constructor
  . rw [hsx]
    refine Set.mem_Ioo.mpr ?_
    simp
  constructor
  . rw [hsx]
    exact isOpen_Ioo
  . intro N
    have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
    obtain ⟨i, hi₀⟩ := hy₅
    have hi₁: (N.1 + i.1) ∈ sd := by
      nth_rw 1 [hsd]
      refine Set.mem_Ici.mpr ?_
      rw [← add_zero 2]
      refine Nat.add_le_add ?_ ?_
      . exact hd₁ N
      . refine le_trans ?_ (hd₁ i)
        exact Nat.zero_le 2
    let a : ↑sd := ⟨N + i, hi₁⟩
    use a
    constructor
    . refine Subtype.mk_le_mk.mpr ?_
      exact Nat.le_add_right ↑N ↑i
    . rw [hsx]
      refine Set.not_mem_Ioo_of_ge ?_
      have hi₂: ↑↑N + 3 ≤ fd x y a := by
        refine hi₀ a ?_
        refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_left ↑i ↑N
      refine le_trans ?_ hi₂
      norm_cast
      exact Nat.le_add_left 1 (↑N + 2)

lemma imo_1985_p6_unique_16
  (x y : NNReal)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hy₂ : ∀ (b : ℝ), ∃ i, ∀ (a : ↑sd), i ≤ a → b ≤ fd x y a)
  (sx : Set ℝ)
  (hsx : sx = Set.Ioo (-1) 1):
   IsOpen sx ∧ ∀ (N : ↑sd), ∃ n, N ≤ n ∧ fd x y n ∉ sx := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  constructor
  . rw [hsx]
    exact isOpen_Ioo
  . intro N
    have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
    obtain ⟨i, hi₀⟩ := hy₅
    have hi₁: (N.1 + i.1) ∈ sd := by
      nth_rw 1 [hsd]
      refine Set.mem_Ici.mpr ?_
      rw [← add_zero 2]
      refine Nat.add_le_add ?_ ?_
      . exact hd₁ N
      . refine le_trans ?_ (hd₁ i)
        exact Nat.zero_le 2
    let a : ↑sd := ⟨N + i, hi₁⟩
    use a
    constructor
    . refine Subtype.mk_le_mk.mpr ?_
      exact Nat.le_add_right ↑N ↑i
    . rw [hsx]
      refine Set.not_mem_Ioo_of_ge ?_
      have hi₂: ↑↑N + 3 ≤ fd x y a := by
        refine hi₀ a ?_
        refine Subtype.mk_le_mk.mpr ?_
        exact Nat.le_add_left ↑i ↑N
      refine le_trans ?_ hi₂
      norm_cast
      exact Nat.le_add_left 1 (↑N + 2)

lemma imo_1985_p6_unique_17
  (x y : NNReal)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hy₂ : ∀ (b : ℝ), ∃ i, ∀ (a : ↑sd), i ≤ a → b ≤ fd x y a)
  (sx : Set ℝ)
  (hsx : sx = Set.Ioo (-1) 1)
  (N : ↑sd):
   ∃ n, N ≤ n ∧ fd x y n ∉ sx := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  have hy₅: ∃ i, ∀ (a : ↑sd), i ≤ a → N + 3 ≤ fd x y a := by exact hy₂ (N + 3)
  obtain ⟨i, hi₀⟩ := hy₅
  have hi₁: (N.1 + i.1) ∈ sd := by
    nth_rw 1 [hsd]
    refine Set.mem_Ici.mpr ?_
    rw [← add_zero 2]
    refine Nat.add_le_add ?_ ?_
    . exact hd₁ N
    . refine le_trans ?_ (hd₁ i)
      exact Nat.zero_le 2
  let a : ↑sd := ⟨N + i, hi₁⟩
  use a
  constructor
  . refine Subtype.mk_le_mk.mpr ?_
    exact Nat.le_add_right ↑N ↑i
  . rw [hsx]
    refine Set.not_mem_Ioo_of_ge ?_
    have hi₂: ↑↑N + 3 ≤ fd x y a := by
      refine hi₀ a ?_
      refine Subtype.mk_le_mk.mpr ?_
      exact Nat.le_add_left ↑i ↑N
    refine le_trans ?_ hi₂
    norm_cast
    exact Nat.le_add_left 1 (↑N + 2)

lemma imo_1985_p6_unique_18
  (x y : NNReal)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (sx : Set ℝ)
  (hsx : sx = Set.Ioo (-1) 1)
  (N i : ↑sd)
  (hi₀ : ∀ (a : ↑sd), i ≤ a → ↑↑N + 3 ≤ fd x y a):
   ∃ n, N ≤ n ∧ fd x y n ∉ sx := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  have hi₁: (N.1 + i.1) ∈ sd := by
    nth_rw 1 [hsd]
    refine Set.mem_Ici.mpr ?_
    rw [← add_zero 2]
    refine Nat.add_le_add ?_ ?_
    . exact hd₁ N
    . refine le_trans ?_ (hd₁ i)
      exact Nat.zero_le 2
  let a : ↑sd := ⟨N + i, hi₁⟩
  use a
  constructor
  . refine Subtype.mk_le_mk.mpr ?_
    exact Nat.le_add_right ↑N ↑i
  . rw [hsx]
    refine Set.not_mem_Ioo_of_ge ?_
    have hi₂: ↑↑N + 3 ≤ fd x y a := by
      refine hi₀ a ?_
      refine Subtype.mk_le_mk.mpr ?_
      exact Nat.le_add_left ↑i ↑N
    refine le_trans ?_ hi₂
    norm_cast
    exact Nat.le_add_left 1 (↑N + 2)

lemma imo_1985_p6_unique_19
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (N i : ↑sd):
   N.1 + ↑i ∈ sd := by
  have hd₁: ∀ nd:↑sd, 2 ≤ nd.1 := by
    intro nd
    refine Set.mem_Ici.mp ?_
    rw [← hsd]
    exact nd.2
  nth_rw 1 [hsd]
  refine Set.mem_Ici.mpr ?_
  rw [← add_zero 2]
  refine Nat.add_le_add ?_ ?_
  . exact hd₁ N
  . refine le_trans ?_ (hd₁ i)
    exact Nat.zero_le 2

lemma imo_1985_p6_unique_20
  (x y : NNReal)
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (sx : Set ℝ)
  (hsx : sx = Set.Ioo (-1) 1)
  (N i : ↑sd)
  (hi₀ : ∀ (a : ↑sd), i ≤ a → ↑↑N + 3 ≤ fd x y a)
  (hi₁ : N.1 + ↑i ∈ sd):
   ∃ n, N ≤ n ∧ fd x y n ∉ sx := by
  let a : ↑sd := ⟨N + i, hi₁⟩
  use a
  constructor
  . refine Subtype.mk_le_mk.mpr ?_
    exact Nat.le_add_right ↑N ↑i
  . rw [hsx]
    refine Set.not_mem_Ioo_of_ge ?_
    have hi₂: ↑↑N + 3 ≤ fd x y a := by
      refine hi₀ a ?_
      refine Subtype.mk_le_mk.mpr ?_
      exact Nat.le_add_left ↑i ↑N
    refine le_trans ?_ hi₂
    norm_cast
    exact Nat.le_add_left 1 (↑N + 2)

lemma imo_1985_p6_unique_21
  (x y : NNReal)
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (sx : Set ℝ)
  (hsx : sx = Set.Ioo (-1) 1)
  (N i : ↑sd)
  (hi₀ : ∀ (a : ↑sd), i ≤ a → ↑↑N + 3 ≤ fd x y a)
  (hi₁ : N.1 + ↑i ∈ sd)
  (a : ↑sd)
  (ha : a = ⟨↑N + ↑i, hi₁⟩):
   ∃ n, N ≤ n ∧ fd x y n ∉ sx := by
  use a
  constructor
  . refine Subtype.mk_le_mk.mpr ?_
    rw [ha]
    exact Nat.le_add_right ↑N ↑i
  . rw [hsx]
    refine Set.not_mem_Ioo_of_ge ?_
    have hi₂: ↑↑N + 3 ≤ fd x y a := by
      refine hi₀ a ?_
      refine Subtype.mk_le_mk.mpr ?_
      rw [ha]
      exact Nat.le_add_left ↑i ↑N
    refine le_trans ?_ hi₂
    norm_cast
    exact Nat.le_add_left 1 (↑N + 2)


lemma imo_1985_p6_exists_27
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (nn : ↑sn) :
   ↑(fb nn) ∈ fr '' sb := by
  refine (Set.mem_image fr sb _).mpr ?_
  use (fb nn)
  rw [hfr, hsb₀]
  constructor
  . exact Set.mem_range_self nn
  . exact rfl

lemma imo_1985_p6_exists_28
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (nn : ↑sn) :
   ∃ x ∈ sb, fr x = ↑(fb nn) := by
  use (fb nn)
  rw [hfr, hsb₀]
  constructor
  . exact Set.mem_range_self nn
  . exact rfl

lemma imo_1985_p6_exists_29
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb : ↑sn → NNReal)
  (hfb₃ : StrictMono fb)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n, hn₁⟩)
  (hbr₅ : ↑(fb nn) = br):
   False := by
  have hn₂: n + 1 ∈ sn := by
    rw [hsn₀]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right_of_le hn₀
  let ns : ↑sn := ⟨n + 1, hn₂⟩
  have hc₁: fb nn < fb ns := by
    refine hfb₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hnn]
    exact lt_add_one n
  have hbr₆: fb ns ≤ fb nn := by
    refine NNReal.coe_le_coe.mp ?_
    rw [hbr₅]
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    use (fb ns)
    rw [hfr, hsb₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self ns
  refine (lt_self_iff_false (fb nn)).mp ?_
  exact lt_of_lt_of_le hc₁ hbr₆

lemma imo_1985_p6_exists_30
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₃ : StrictMono fb)
  (n : ℕ)
  (hn₁ : n ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n, hn₁⟩)
  (hn₂ : n + 1 ∈ sn)
  (ns : ↑sn)
  (hns : ns = ⟨n + 1, hn₂⟩):
   fb nn < fb ns := by
  refine hfb₃ ?_
  rw [hnn, hns]
  refine Subtype.mk_lt_mk.mpr ?_
  exact lt_add_one n


lemma imo_1985_p6_exists_31
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (nn : ↑sn)
  (hbr₅ : ↑(fb nn) = br)
  (ns : ↑sn)
  (hc₁ : fb nn < fb ns):
   False := by
  have hbr₆: fb ns ≤ fb nn := by
    refine NNReal.coe_le_coe.mp ?_
    rw [hbr₅]
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    use (fb ns)
    rw [hfr, hsb₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self ns
  refine (lt_self_iff_false (fb nn)).mp ?_
  exact lt_of_lt_of_le hc₁ hbr₆

lemma imo_1985_p6_exists_32
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (nn : ↑sn)
  (hbr₅ : ↑(fb nn) = br)
  (ns : ↑sn):
   fb ns ≤ fb nn := by
  refine NNReal.coe_le_coe.mp ?_
  rw [hbr₅]
  refine hbr₃ _ ?_
  rw [hsbr]
  refine (Set.mem_image fr sb _).mpr ?_
  use (fb ns)
  rw [hfr, hsb₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self ns

lemma imo_1985_p6_exists_33
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (br : ℝ)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n, hn₁⟩)
  (hn₂ : ↑(fb nn) < br):
   1 - 1 / ↑n < f n br.toNNReal := by
  have hn₃: f n (fb nn) = 1 - 1 / n := by
    rw [hf₁ n _ hn₀, hnn, hfb₁ ⟨n, hn₁⟩]
    refine NNReal.coe_sub ?_
    refine div_le_self ?_ ?_
    . exact zero_le_one' NNReal
    . exact Nat.one_le_cast.mpr hn₀
  rw [← hn₃]
  refine hmo₀ n hn₀ ?_
  exact Real.lt_toNNReal_iff_coe_lt.mpr hn₂

lemma imo_1985_p6_exists_34
  (f : ℕ → NNReal → ℝ)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n, hn₁⟩):
   f n (fb nn) = 1 - 1 / ↑n := by
  rw [hf₁ n _ hn₀, hnn, hfb₁ ⟨n, hn₁⟩]
  refine NNReal.coe_sub ?_
  refine div_le_self ?_ ?_
  . exact zero_le_one' NNReal
  . exact Nat.one_le_cast.mpr hn₀

lemma imo_1985_p6_exists_35
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (br : ℝ)
  (n : ℕ)
  (hn₀ : 0 < n)
  (nn : ↑sn)
  (hn₂ : ↑(fb nn) < br)
  (hn₃ : f n (fb nn) = 1 - 1 / ↑n):
   1 - 1 / ↑n < f n br.toNNReal := by
  rw [← hn₃]
  refine hmo₀ n hn₀ ?_
  exact Real.lt_toNNReal_iff_coe_lt.mpr hn₂


lemma imo_1985_p6_exists_36
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfc₃ : StrictAnti fc)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (hbr₁ : 0 < br)
  (hu₅ : br ≤ cr)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (hu₆ : br = cr)
  (n : ℕ)
  (hn₀ : 0 < n):
  f (n + 1) br.toNNReal < 1 := by
  have hn₂: n + 1 ∈ sn := by
    rw [hsn₀]
    exact Set.mem_Ici.mpr (by linarith)
  let nn : ↑sn := ⟨n + 1, hn₂⟩
  have hcr₁: 0 < cr := by exact gt_of_ge_of_gt hu₅ hbr₁
  have hn₃: f (n + 1) (fc (nn)) = 1 := by
    rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
    exact rfl
  rw [← hn₃, hu₆]
  refine hmo₀ (n + 1) (by linarith) ?_
  refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt hcr₁)).mpr ?_
  by_contra! hc₀
  have hc₁: fc nn = cr := by
    refine eq_of_le_of_le hc₀ ?_
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc nn)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self nn
  have hn₄: n + 2 ∈ sn := by
    rw [hsn₀]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right_of_le hn₀
  let ns : ↑sn := ⟨n + 2, hn₄⟩
  have hn₅: fc ns < fc nn := by
    refine hfc₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    exact Nat.lt_add_one (n + 1)
  have hc₂: fc nn ≤ fc ns := by
    refine NNReal.coe_le_coe.mp ?_
    rw [hc₁]
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc ns)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self ns
  refine (lt_self_iff_false (fc ns)).mp ?_
  exact lt_of_lt_of_le hn₅ hc₂

lemma imo_1985_p6_exists_37
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (hu₆ : br = cr)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₂ : n + 1 ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n + 1, hn₂⟩)
  (hcr₁ : 0 < cr)
  (hn₃ : f (n + 1) (fc nn) = 1):
   f (n + 1) br.toNNReal < 1 := by
  rw [← hn₃, hu₆]
  refine hmo₀ (n + 1) (by linarith) ?_
  refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt hcr₁)).mpr ?_
  by_contra! hc₀
  have hc₁: fc nn = cr := by
    refine eq_of_le_of_le hc₀ ?_
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc nn)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self nn
  have hn₄: n + 2 ∈ sn := by
    rw [hsn₀]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right_of_le hn₀
  let ns : ↑sn := ⟨n + 2, hn₄⟩
  have hn₅: fc ns < fc nn := by
    refine hfc₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hnn]
    exact Nat.lt_add_one (n + 1)
  have hc₂: fc nn ≤ fc ns := by
    refine NNReal.coe_le_coe.mp ?_
    rw [hc₁]
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc ns)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self ns
  refine (lt_self_iff_false (fc ns)).mp ?_
  exact lt_of_lt_of_le hn₅ hc₂


lemma imo_1985_p6_exists_38
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₂ : n + 1 ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n + 1, hn₂⟩)
  (hcr₁ : 0 < cr):
   f (n + 1) cr.toNNReal < f (n + 1) (fc nn) := by
  refine hmo₀ (n + 1) (by linarith) ?_
  refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt hcr₁)).mpr ?_
  by_contra! hc₀
  have hc₁: fc nn = cr := by
    refine eq_of_le_of_le hc₀ ?_
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc nn)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self nn
  have hn₄: n + 2 ∈ sn := by
    rw [hsn₀]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right_of_le hn₀
  let ns : ↑sn := ⟨n + 2, hn₄⟩
  have hn₅: fc ns < fc nn := by
    refine hfc₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hnn]
    exact Nat.lt_add_one (n + 1)
  have hc₂: fc nn ≤ fc ns := by
    refine NNReal.coe_le_coe.mp ?_
    rw [hc₁]
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc ns)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self ns
  refine (lt_self_iff_false (fc ns)).mp ?_
  exact lt_of_lt_of_le hn₅ hc₂

lemma imo_1985_p6_exists_39
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₂ : n + 1 ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n + 1, hn₂⟩)
  (hcr₁ : 0 < cr):
   cr.toNNReal < fc nn := by
  refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt hcr₁)).mpr ?_
  by_contra! hc₀
  have hc₁: fc nn = cr := by
    refine eq_of_le_of_le hc₀ ?_
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc nn)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self nn
  have hn₄: n + 2 ∈ sn := by
    rw [hsn₀]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right_of_le hn₀
  let ns : ↑sn := ⟨n + 2, hn₄⟩
  have hn₅: fc ns < fc nn := by
    refine hfc₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hnn]
    exact Nat.lt_add_one (n + 1)
  have hc₂: fc nn ≤ fc ns := by
    refine NNReal.coe_le_coe.mp ?_
    rw [hc₁]
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc ns)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self ns
  refine (lt_self_iff_false (fc ns)).mp ?_
  exact lt_of_lt_of_le hn₅ hc₂

lemma imo_1985_p6_exists_40
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₂ : n + 1 ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n + 1, hn₂⟩):
   cr < ↑(fc nn) := by
  by_contra! hc₀
  have hc₁: fc nn = cr := by
    refine eq_of_le_of_le hc₀ ?_
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc nn)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self nn
  have hn₄: n + 2 ∈ sn := by
    rw [hsn₀]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right_of_le hn₀
  let ns : ↑sn := ⟨n + 2, hn₄⟩
  have hn₅: fc ns < fc nn := by
    refine hfc₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hnn]
    exact Nat.lt_add_one (n + 1)
  have hc₂: fc nn ≤ fc ns := by
    refine NNReal.coe_le_coe.mp ?_
    rw [hc₁]
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc ns)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self ns
  refine (lt_self_iff_false (fc ns)).mp ?_
  exact lt_of_lt_of_le hn₅ hc₂



lemma imo_1985_p6_exists_41
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₂ : n + 1 ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n + 1, hn₂⟩)
  (hc₀ : ↑(fc nn) ≤ cr):
   False := by
  have hc₁: fc nn = cr := by
    refine eq_of_le_of_le hc₀ ?_
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc nn)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self nn
  have hn₄: n + 2 ∈ sn := by
    rw [hsn₀]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right_of_le hn₀
  let ns : ↑sn := ⟨n + 2, hn₄⟩
  have hn₅: fc ns < fc nn := by
    refine hfc₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hnn]
    exact Nat.lt_add_one (n + 1)
  have hc₂: fc nn ≤ fc ns := by
    refine NNReal.coe_le_coe.mp ?_
    rw [hc₁]
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc ns)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self ns
  refine (lt_self_iff_false (fc ns)).mp ?_
  exact lt_of_lt_of_le hn₅ hc₂


lemma imo_1985_p6_exists_42
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (nn : ↑sn)
  (hc₀ : ↑(fc nn) ≤ cr):
   ↑(fc nn) = cr := by
  refine eq_of_le_of_le hc₀ ?_
  refine hcr₃ _ ?_
  rw [hscr]
  refine (Set.mem_image fr sc _).mpr ?_
  use (fc nn)
  rw [hfr, hsc₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self nn

lemma imo_1985_p6_exists_43
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (n : ℕ)
  (hn₀ : 0 < n):
  n + 2 ∈ sn := by
  rw [hsn₀]
  refine Set.mem_Ici.mpr ?_
  exact Nat.le_add_right_of_le hn₀

lemma imo_1985_p6_exists_44
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (hfc₃ : StrictAnti fc)
  (n : ℕ)
  (hn₂ : n + 1 ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n + 1, hn₂⟩)
  (hn₄ : n + 2 ∈ sn)
  (ns : ↑sn)
  (hns : ns = ⟨n + 2, hn₄⟩):
  fc ns < fc nn := by
  refine hfc₃ ?_
  rw [hnn, hns]
  refine Subtype.mk_lt_mk.mpr ?_
  exact Nat.lt_add_one (n + 1)


lemma imo_1985_p6_exists_45
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (n : ℕ)
  (nn : ↑sn)
  (hc₁ : ↑(fc nn) = cr)
  (hn₄ : n + 2 ∈ sn)
  (ns : ↑sn := ⟨n + 2, hn₄⟩)
  (hn₅ : fc ns < fc nn):
   False := by
  have hc₂: fc nn ≤ fc ns := by
    refine NNReal.coe_le_coe.mp ?_
    rw [hc₁]
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc ns)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self ns
  refine (lt_self_iff_false (fc ns)).mp ?_
  exact lt_of_lt_of_le hn₅ hc₂


lemma imo_1985_p6_exists_46
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (n : ℕ)
  (nn : ↑sn)
  (hc₁ : ↑(fc nn) = cr)
  (hn₄ : n + 2 ∈ sn)
  (ns : ↑sn := ⟨n + 2, hn₄⟩):
   fc nn ≤ fc ns := by
  refine NNReal.coe_le_coe.mp ?_
  rw [hc₁]
  refine hcr₃ _ ?_
  rw [hscr]
  refine (Set.mem_image fr sc _).mpr ?_
  use (fc ns)
  rw [hfr, hsc₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self ns


lemma imo_1985_p6_unique_top_ind_1
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (hd₃ : ∀ (nd : ↑sd), nd.1 + 1 ∈ sd)
  (hd₂ : ∀ (nd : ↑sd), fd a b nd * (2 - 1 / ↑↑nd) ≤ fd a b ⟨nd.1 + 1, hd₃ nd⟩)
  (hi₀ : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi₀⟩)
  (nd : ↑sd)
  (hnd₀ : 2 ≤ nd.1):
   fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ f (↑nd) b - f (↑nd) a := by
  refine Nat.le_induction ?_ ?_ nd.1 hnd₀
  . have hi₂: i.val = (2:ℕ) := by
      simp_all only [Subtype.forall]
    rw [hfd₁ a b i, hi₂]
    simp
  . simp
    intros n hn₀ hn₁
    have hn₂: n - 1 = n - 2 + 1 := by
      simp
      exact (Nat.sub_eq_iff_eq_add hn₀).mp rfl
    have hn₃: n ∈ sd := by
      rw [hsd]
      exact hn₀
    let nn : ↑sd := ⟨n, hn₃⟩
    have hnn: nn.1 = n := by exact rfl
    have hn₄: nn.1 + 1 ∈ sd := by
      rw [hnn, hsd]
      refine Set.mem_Ici.mpr ?_
      exact Nat.le_add_right_of_le hn₀
    have hn₅: fd a b nn * (2 - 1 / ↑n) ≤ fd a b ⟨nn.1 + 1, hn₄⟩ := by exact hd₂ nn
    rw [hfd₁ a b ⟨nn.1 + 1, hn₄⟩] at hn₅
    have hn₆: f (↑nn + 1) b - f (↑nn + 1) a = f (n + 1) b - f (n + 1) a := by exact rfl
    rw [hn₆] at hn₅
    refine le_trans ?_ hn₅
    rw [hn₂, pow_succ (3/2) (n - 2), ← mul_assoc (fd a b i)]
    refine mul_le_mul ?_ ?_ (by linarith) ?_
    . refine le_of_le_of_eq hn₁ ?_
      rw [hfd₁]
    . refine (div_le_iff₀ (two_pos)).mpr ?_
      rw [sub_mul, one_div_mul_eq_div _ 2]
      refine le_sub_iff_add_le.mpr ?_
      refine le_sub_iff_add_le'.mp ?_
      refine (div_le_iff₀ ?_).mpr ?_
      . refine Nat.cast_pos.mpr ?_
        exact lt_of_lt_of_le (two_pos) hn₀
      . ring_nf
        exact Nat.ofNat_le_cast.mpr hn₀
    . exact le_of_lt (hd₁ nn a b ha₀)






lemma imo_1985_p6_unique_top_ind_2
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (a b : NNReal)
  (hi₀ : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi₀⟩):
   fd a b i * (3 / 2) ^ (2 - 2) ≤ f 2 b - f 2 a := by
  have hi₂: i.val = (2:ℕ) := by
    simp_all only [Subtype.forall]
  rw [hfd₁ a b i, hi₂]
  simp


lemma imo_1985_p6_unique_top_ind_3
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (hd₃ : ∀ (nd : ↑sd), nd.1 + 1 ∈ sd)
  (hd₂ : ∀ (nd : ↑sd), fd a b nd * (2 - 1 / ↑↑nd) ≤ fd a b ⟨nd.1 + 1, hd₃ nd⟩)
  (i : ↑sd):
   ∀ (n : ℕ),
    2 ≤ n → fd a b i * (3 / 2) ^ (n - 2) ≤ f n b - f n a → fd a b i * (3 / 2) ^ (n + 1 - 2) ≤ f (n + 1) b - f (n + 1) a := by
  simp
  intros n hn₀ hn₁
  have hn₂: n - 1 = n - 2 + 1 := by
    simp
    exact (Nat.sub_eq_iff_eq_add hn₀).mp rfl
  have hn₃: n ∈ sd := by
    rw [hsd]
    exact hn₀
  let nn : ↑sd := ⟨n, hn₃⟩
  have hnn: nn.1 = n := by exact rfl
  have hn₄: nn.1 + 1 ∈ sd := by
    rw [hnn, hsd]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right_of_le hn₀
  have hn₅: fd a b nn * (2 - 1 / ↑n) ≤ fd a b ⟨nn.1 + 1, hn₄⟩ := by exact hd₂ nn
  rw [hfd₁ a b ⟨nn.1 + 1, hn₄⟩] at hn₅
  have hn₆: f (↑nn + 1) b - f (↑nn + 1) a = f (n + 1) b - f (n + 1) a := by exact rfl
  rw [hn₆] at hn₅
  refine le_trans ?_ hn₅
  rw [hn₂, pow_succ (3/2) (n - 2), ← mul_assoc (fd a b i)]
  refine mul_le_mul ?_ ?_ (by linarith) ?_
  . refine le_of_le_of_eq hn₁ ?_
    rw [hfd₁]
  . refine (div_le_iff₀ (two_pos)).mpr ?_
    rw [sub_mul, one_div_mul_eq_div _ 2]
    refine le_sub_iff_add_le.mpr ?_
    refine le_sub_iff_add_le'.mp ?_
    refine (div_le_iff₀ ?_).mpr ?_
    . refine Nat.cast_pos.mpr ?_
      exact lt_of_lt_of_le (two_pos) hn₀
    . ring_nf
      exact Nat.ofNat_le_cast.mpr hn₀
  . exact le_of_lt (hd₁ nn a b ha₀)

lemma imo_1985_p6_unique_top_ind_4
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (hd₃ : ∀ (nd : ↑sd), nd.1 + 1 ∈ sd)
  (hd₂ : ∀ (nd : ↑sd), fd a b nd * (2 - 1 / ↑↑nd) ≤ fd a b ⟨nd.1 + 1, hd₃ nd⟩)
  (i : ↑sd)
  (n : ℕ)
  (hn₀ : 2 ≤ n)
  (hn₁ : fd a b i * (3 / 2) ^ (n - 2) ≤ f n b - f n a)
  (hn₂ : n - 1 = n - 2 + 1):
   fd a b i * (3 / 2) ^ (n - 1) ≤ f (n + 1) b - f (n + 1) a := by
  have hn₃: n ∈ sd := by
    rw [hsd]
    exact hn₀
  let nn : ↑sd := ⟨n, hn₃⟩
  have hnn: nn.1 = n := by exact rfl
  have hn₄: nn.1 + 1 ∈ sd := by
    rw [hnn, hsd]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right_of_le hn₀
  have hn₅: fd a b nn * (2 - 1 / ↑n) ≤ fd a b ⟨nn.1 + 1, hn₄⟩ := by exact hd₂ nn
  rw [hfd₁ a b ⟨nn.1 + 1, hn₄⟩] at hn₅
  have hn₆: f (↑nn + 1) b - f (↑nn + 1) a = f (n + 1) b - f (n + 1) a := by exact rfl
  rw [hn₆] at hn₅
  refine le_trans ?_ hn₅
  rw [hn₂, pow_succ (3/2) (n - 2), ← mul_assoc (fd a b i)]
  refine mul_le_mul ?_ ?_ (by linarith) ?_
  . refine le_of_le_of_eq hn₁ ?_
    rw [hfd₁]
  . refine (div_le_iff₀ (two_pos)).mpr ?_
    rw [sub_mul, one_div_mul_eq_div _ 2]
    refine le_sub_iff_add_le.mpr ?_
    refine le_sub_iff_add_le'.mp ?_
    refine (div_le_iff₀ ?_).mpr ?_
    . refine Nat.cast_pos.mpr ?_
      exact lt_of_lt_of_le (two_pos) hn₀
    . ring_nf
      exact Nat.ofNat_le_cast.mpr hn₀
  . exact le_of_lt (hd₁ nn a b ha₀)

lemma imo_1985_p6_unique_top_ind_5
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (hd₃ : ∀ (nd : ↑sd), nd.1 + 1 ∈ sd)
  (hd₂ : ∀ (nd : ↑sd), fd a b nd * (2 - 1 / ↑↑nd) ≤ fd a b ⟨nd.1 + 1, hd₃ nd⟩)
  (i : ↑sd)
  (n : ℕ)
  (hn₀ : 2 ≤ n)
  (hn₁ : fd a b i * (3 / 2) ^ (n - 2) ≤ f n b - f n a)
  (hn₂ : n - 1 = n - 2 + 1)
  (hn₃ : n ∈ sd)
  (nn : ↑sd := ⟨n, hn₃⟩)
  (hnn : nn.1 = n)
  (hn₄ : nn.1 + 1 ∈ sd) :
  fd a b i * (3 / 2) ^ (n - 1) ≤ f (n + 1) b - f (n + 1) a := by
  have hn₅: fd a b nn * (2 - 1 / ↑n) ≤ fd a b ⟨nn.1 + 1, hn₄⟩ := by
    rw [← hnn]
    exact hd₂ nn
  rw [hfd₁ a b ⟨nn.1 + 1, hn₄⟩] at hn₅
  have hn₆: f (↑nn + 1) b - f (↑nn + 1) a = f (n + 1) b - f (n + 1) a := by rw [hnn]
  rw [hn₆] at hn₅
  refine le_trans ?_ hn₅
  rw [hn₂, pow_succ (3/2) (n - 2), ← mul_assoc (fd a b i)]
  refine mul_le_mul ?_ ?_ (by linarith) ?_
  . refine le_of_le_of_eq hn₁ ?_
    rw [hfd₁, hnn]
  . refine (div_le_iff₀ (two_pos)).mpr ?_
    rw [sub_mul, one_div_mul_eq_div _ 2]
    refine le_sub_iff_add_le.mpr ?_
    refine le_sub_iff_add_le'.mp ?_
    refine (div_le_iff₀ ?_).mpr ?_
    . refine Nat.cast_pos.mpr ?_
      exact lt_of_lt_of_le (two_pos) hn₀
    . ring_nf
      exact Nat.ofNat_le_cast.mpr hn₀
  . exact le_of_lt (hd₁ nn a b ha₀)


lemma imo_1985_p6_unique_top_ind_6
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (i : ↑sd)
  (n : ℕ)
  (hn₀ : 2 ≤ n)
  (hn₁ : fd a b i * (3 / 2) ^ (n - 2) ≤ f n b - f n a)
  (hn₂ : n - 1 = n - 2 + 1)
  (hn₃ : n ∈ sd)
  (nn : ↑sd := ⟨n, hn₃⟩)
  (hnn : ↑nn = n)
  (hn₄ : nn.1 + 1 ∈ sd)
  (hn₅ : fd a b nn * (2 - 1 / ↑n) ≤ fd a b ⟨↑nn + 1, hn₄⟩):
   fd a b i * (3 / 2) ^ (n - 1) ≤ f (n + 1) b - f (n + 1) a := by
  rw [hfd₁ a b ⟨nn.1 + 1, hn₄⟩] at hn₅
  have hn₆: f (↑nn + 1) b - f (↑nn + 1) a = f (n + 1) b - f (n + 1) a := by rw [hnn]
  rw [hn₆] at hn₅
  refine le_trans ?_ hn₅
  rw [hn₂, pow_succ (3/2) (n - 2), ← mul_assoc (fd a b i)]
  refine mul_le_mul ?_ ?_ (by linarith) ?_
  . refine le_of_le_of_eq hn₁ ?_
    rw [hfd₁, hnn]
  . refine (div_le_iff₀ (two_pos)).mpr ?_
    rw [sub_mul, one_div_mul_eq_div _ 2]
    refine le_sub_iff_add_le.mpr ?_
    refine le_sub_iff_add_le'.mp ?_
    refine (div_le_iff₀ ?_).mpr ?_
    . refine Nat.cast_pos.mpr ?_
      exact lt_of_lt_of_le (two_pos) hn₀
    . ring_nf
      exact Nat.ofNat_le_cast.mpr hn₀
  . exact le_of_lt (hd₁ nn a b ha₀)

lemma imo_1985_p6_unique_top_ind_7
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (i : ↑sd)
  (n : ℕ)
  (hn₀ : 2 ≤ n)
  (hn₁ : fd a b i * (3 / 2) ^ (n - 2) ≤ f n b - f n a)
  (hn₂ : n - 1 = n - 2 + 1)
  (hn₃ : n ∈ sd)
  (nn : ↑sd := ⟨n, hn₃⟩)
  (hnn : ↑nn = n)
  (hn₅ : fd a b nn * (2 - 1 / ↑n) ≤ f (n + 1) b - f (n + 1) a):
   fd a b i * (3 / 2) ^ (n - 1) ≤ f (n + 1) b - f (n + 1) a := by
  refine le_trans ?_ hn₅
  rw [hn₂, pow_succ (3/2) (n - 2), ← mul_assoc (fd a b i)]
  refine mul_le_mul ?_ ?_ (by linarith) ?_
  . refine le_of_le_of_eq hn₁ ?_
    rw [hfd₁, hnn]
  . refine (div_le_iff₀ (two_pos)).mpr ?_
    rw [sub_mul, one_div_mul_eq_div _ 2]
    refine le_sub_iff_add_le.mpr ?_
    refine le_sub_iff_add_le'.mp ?_
    refine (div_le_iff₀ ?_).mpr ?_
    . refine Nat.cast_pos.mpr ?_
      exact lt_of_lt_of_le (two_pos) hn₀
    . ring_nf
      exact Nat.ofNat_le_cast.mpr hn₀
  . exact le_of_lt (hd₁ nn a b ha₀)

lemma imo_1985_p6_unique_top_ind_8
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (i : ↑sd)
  (n : ℕ)
  (hn₀ : 2 ≤ n)
  (hn₁ : fd a b i * (3 / 2) ^ (n - 2) ≤ f n b - f n a)
  (hn₂ : n - 1 = n - 2 + 1)
  (hn₃ : n ∈ sd)
  (nn : ↑sd := ⟨n, hn₃⟩)
  (hnn : ↑nn = n):
   fd a b i * (3 / 2) ^ (n - 1) ≤ fd a b nn * (2 - 1 / ↑n) := by
  rw [hn₂, pow_succ (3/2) (n - 2), ← mul_assoc (fd a b i)]
  refine mul_le_mul ?_ ?_ (by linarith) ?_
  . refine le_of_le_of_eq hn₁ ?_
    rw [hfd₁, hnn]
  . refine (div_le_iff₀ (two_pos)).mpr ?_
    rw [sub_mul, one_div_mul_eq_div _ 2]
    refine le_sub_iff_add_le.mpr ?_
    refine le_sub_iff_add_le'.mp ?_
    refine (div_le_iff₀ ?_).mpr ?_
    . refine Nat.cast_pos.mpr ?_
      exact lt_of_lt_of_le (two_pos) hn₀
    . ring_nf
      exact Nat.ofNat_le_cast.mpr hn₀
  . exact le_of_lt (hd₁ nn a b ha₀)

lemma imo_1985_p6_unique_top_ind_9
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (i : ↑sd)
  (n : ℕ)
  (hn₀ : 2 ≤ n)
  (hn₁ : fd a b i * (3 / 2) ^ (n - 2) ≤ f n b - f n a)
  (hn₃ : n ∈ sd)
  (nn : ↑sd := ⟨n, hn₃⟩)
  (hnn : ↑nn = n):
   fd a b i * (3 / 2) ^ (n - 2) * (3 / 2) ≤ fd a b nn * (2 - 1 / ↑n) := by
  refine mul_le_mul ?_ ?_ (by linarith) ?_
  . refine le_of_le_of_eq hn₁ ?_
    rw [hfd₁, hnn]
  . refine (div_le_iff₀ (two_pos)).mpr ?_
    rw [sub_mul, one_div_mul_eq_div _ 2]
    refine le_sub_iff_add_le.mpr ?_
    refine le_sub_iff_add_le'.mp ?_
    refine (div_le_iff₀ ?_).mpr ?_
    . refine Nat.cast_pos.mpr ?_
      exact lt_of_lt_of_le (two_pos) hn₀
    . ring_nf
      exact Nat.ofNat_le_cast.mpr hn₀
  . exact le_of_lt (hd₁ nn a b ha₀)

lemma imo_1985_p6_unique_top_ind_10
  (n : ℕ)
  (hn₀ : 2 ≤ n):
  (3:ℝ) / 2 ≤ 2 - 1 / ↑n := by
  refine (div_le_iff₀ (two_pos)).mpr ?_
  rw [sub_mul, one_div_mul_eq_div _ 2]
  refine le_sub_iff_add_le.mpr ?_
  refine le_sub_iff_add_le'.mp ?_
  refine (div_le_iff₀ ?_).mpr ?_
  . refine Nat.cast_pos.mpr ?_
    exact lt_of_lt_of_le (two_pos) hn₀
  . ring_nf
    exact Nat.ofNat_le_cast.mpr hn₀

lemma imo_1985_p6_unique_top_1
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), f (↑n) a < f (↑n + 1) a ∧ f (↑n) b < f (↑n + 1) b)
  (hd₀ : ∀ (nd : ↑sd), nd.1 + 1 ∈ sd) :
  ∀ (nd : ↑sd), fd a b nd * (2 - 1 / ↑↑nd) ≤ fd a b ⟨↑nd + 1, hd₀ nd⟩ := by
  intro nd
  have hnd₀: 0 < nd.1 := by
    have g₀: 2 ≤ nd.1 := by
      refine Set.mem_Ici.mp ?_
      rw [← hsd]
      exact nd.2
    exact Nat.zero_lt_of_lt g₀
  rw [hfd₁, hfd₁, h₁ nd.1 _ hnd₀, h₁ nd.1 _ hnd₀]
  have hnd₁: f (↑nd) b * (f (↑nd) b + 1 / ↑↑nd) - f (↑nd) a * (f (↑nd) a + 1 / ↑↑nd) =
    (f (↑nd) b - f (↑nd) a) * (f (↑nd) b + f (↑nd) a + 1 / nd.1) := by
    ring_nf
  rw [hnd₁]
  refine (mul_le_mul_left ?_).mpr ?_
  . rw [← hfd₁]
    exact hd₁ nd a b ha₀
  . refine le_sub_iff_add_le.mp ?_
    rw [sub_neg_eq_add]
    have hnd₂: 1 - 1 / nd.1 < f (↑nd) b := by
      exact h₇ nd.1 b hnd₀ (ha₁ nd).2
    have hnd₃: 1 - 1 / nd.1 < f (↑nd) a := by
      exact h₇ nd.1 a hnd₀ (ha₁ nd).1
    linarith

lemma imo_1985_p6_unique_top_2
  (f : ℕ → NNReal → ℝ)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), f (↑n) a < f (↑n + 1) a ∧ f (↑n) b < f (↑n + 1) b)
  (nd : ↑sd)
  (hnd₀ : 0 < nd.1):
   (f (↑nd) b - f (↑nd) a) * (2 - 1 / ↑↑nd) ≤ f (↑nd) b * (f (↑nd) b + 1 / ↑↑nd) - f (↑nd) a * (f (↑nd) a + 1 / ↑↑nd) := by
  have hnd₁: f (↑nd) b * (f (↑nd) b + 1 / ↑↑nd) - f (↑nd) a * (f (↑nd) a + 1 / ↑↑nd) =
      (f (↑nd) b - f (↑nd) a) * (f (↑nd) b + f (↑nd) a + 1 / nd.1) := by
    ring_nf
  rw [hnd₁]
  refine (mul_le_mul_left ?_).mpr ?_
  . rw [← hfd₁]
    exact hd₁ nd a b ha₀
  . refine le_sub_iff_add_le.mp ?_
    rw [sub_neg_eq_add]
    have hnd₂: 1 - 1 / nd.1 < f (↑nd) b := by
      exact h₇ nd.1 b hnd₀ (ha₁ nd).2
    have hnd₃: 1 - 1 / nd.1 < f (↑nd) a := by
      exact h₇ nd.1 a hnd₀ (ha₁ nd).1
    linarith


lemma imo_1985_p6_unique_top_3
  (f : ℕ → NNReal → ℝ)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (ha₁ : ∀ (n : ↑sd), f (↑n) a < f (↑n + 1) a ∧ f (↑n) b < f (↑n + 1) b)
  (nd : ↑sd)
  (hnd₀ : 0 < nd.1)
  (hnd₁ : f (↑nd) b * (f (↑nd) b + 1 / ↑↑nd) - f (↑nd) a * (f (↑nd) a + 1 / ↑↑nd) =
    ((f (↑nd) b - f (↑nd) a) * (f (↑nd) b + f (↑nd) a + 1 / ↑↑nd))) :
   (f (↑nd) b - f (↑nd) a) * (2 - 1 / ↑↑nd) ≤ f (↑nd) b * (f (↑nd) b + 1 / ↑↑nd) - f (↑nd) a * (f (↑nd) a + 1 / ↑↑nd) := by
  rw [hnd₁]
  refine (mul_le_mul_left ?_).mpr ?_
  . rw [← hfd₁]
    exact hd₁ nd a b ha₀
  . refine le_sub_iff_add_le.mp ?_
    rw [sub_neg_eq_add]
    have hnd₂: 1 - 1 / nd.1 < f (↑nd) b := by
      exact h₇ nd.1 b hnd₀ (ha₁ nd).2
    have hnd₃: 1 - 1 / nd.1 < f (↑nd) a := by
      exact h₇ nd.1 a hnd₀ (ha₁ nd).1
    linarith

lemma imo_1985_p6_unique_top_4
  (f : ℕ → NNReal → ℝ)
  (h₇ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x < f (n + 1) x → 1 - 1 / ↑n < f n x)
  (sd : Set ℕ)
  (a b : NNReal)
  (ha₁ : ∀ (n : ↑sd), f (↑n) a < f (↑n + 1) a ∧ f (↑n) b < f (↑n + 1) b)
  (nd : ↑sd)
  (hnd₀ : 0 < nd.1):
   2 - 1 / ↑↑nd ≤ f (↑nd) b + f (↑nd) a + 1 / ↑↑nd := by
  refine le_sub_iff_add_le.mp ?_
  rw [sub_neg_eq_add]
  have hnd₂: 1 - 1 / nd.1 < f (↑nd) b := by
    exact h₇ nd.1 b hnd₀ (ha₁ nd).2
  have hnd₃: 1 - 1 / nd.1 < f (↑nd) a := by
    exact h₇ nd.1 a hnd₀ (ha₁ nd).1
  linarith

lemma imo_1985_p6_unique_top_5
  (f : ℕ → NNReal → ℝ)
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hfd₁ : ∀ (y₁ y₂ : NNReal) (n : ↑sd), fd y₁ y₂ n = f (↑n) y₂ - f (↑n) y₁)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (hd₀ : ∀ (nd : ↑sd), nd.1 + 1 ∈ sd)
  (hd₂ : ∀ (nd : ↑sd), fd a b nd * (2 - 1 / ↑↑nd) ≤ fd a b ⟨↑nd + 1, hd₀ nd⟩)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩) :
  Filter.Tendsto (fd a b) Filter.atTop Filter.atTop := by
  have hd₃: ∀ nd, fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd := by
    intro nd
    exact imo_1985_p6_unique_top_ind f sd hsd fd hfd₁ hd₁ a b ha₀ hd₀ hd₂ hi i hi₁ nd
  have hsd₁: Nonempty ↑sd := by
    refine Set.Nonempty.to_subtype ?_
    exact Set.nonempty_of_mem (hd₀ i)
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro z
  by_cases hz₀: z ≤ fd a b i
  . use i
    intros j _
    refine le_trans hz₀ ?_
    refine le_trans ?_ (hd₃ j)
    refine le_mul_of_one_le_right ?_ ?_
    . refine le_of_lt ?_
      exact hd₁ i a b ha₀
    . refine one_le_pow₀ ?_
      linarith
  . push_neg at hz₀
    have hz₁: 0 < fd a b i := by exact hd₁ i a b ha₀
    have hz₂: 0 < Real.log (z / fd a b i) := by
      refine Real.log_pos ?_
      exact (one_lt_div hz₁).mpr hz₀
    let j : ℕ := Nat.ceil (2 + Real.log (z / fd a b i) / Real.log (3 / 2))
    have hj₀: 2 < j := by
      refine Nat.lt_ceil.mpr ?_
      norm_cast
      refine lt_add_of_pos_right 2 ?_
      refine div_pos ?_ ?_
      . exact hz₂
      . refine Real.log_pos ?_
        linarith
    have hj₁: j ∈ sd := by
      rw [hsd]
      exact Set.mem_Ici_of_Ioi hj₀
    use ⟨j, hj₁⟩
    intro k hk₀
    have hk₁: fd a b i * (3 / 2) ^ (k.1 - 2) ≤ fd a b k := by
      exact hd₃ k
    have hk₂: i < k := by
      refine lt_of_lt_of_le ?_ hk₀
      refine Subtype.mk_lt_mk.mpr ?_
      refine Nat.lt_ceil.mpr ?_
      rw [hi₁]
      refine lt_add_of_pos_right 2 ?_
      refine div_pos ?_ ?_
      . rw [← hi₁]
        exact hz₂
      . refine Real.log_pos ?_
        linarith
    refine le_trans ?_ hk₁
    refine (div_le_iff₀' ?_).mp ?_
    . exact hz₁
    . refine Real.le_pow_of_log_le (by linarith) ?_
      refine (div_le_iff₀ ?_).mp ?_
      . refine Real.log_pos ?_
        linarith
      . rw [Nat.cast_sub ?_]
        . rw [Nat.cast_two]
          refine le_sub_iff_add_le'.mpr ?_
          exact Nat.le_of_ceil_le hk₀
        . rw [hi₁] at hk₂
          exact Nat.le_of_succ_le hk₂


lemma imo_1985_p6_unique_top_6
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (hd₀ : ∀ (nd : ↑sd), nd.1 + 1 ∈ sd)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩)
  (hd₃ : ∀ (nd : ↑sd), fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd):
   Filter.Tendsto (fd a b) Filter.atTop Filter.atTop := by
  have hsd₁: Nonempty ↑sd := by
    refine Set.Nonempty.to_subtype ?_
    exact Set.nonempty_of_mem (hd₀ i)
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro z
  by_cases hz₀: z ≤ fd a b i
  . use i
    intros j _
    refine le_trans hz₀ ?_
    refine le_trans ?_ (hd₃ j)
    refine le_mul_of_one_le_right ?_ ?_
    . refine le_of_lt ?_
      exact hd₁ i a b ha₀
    . refine one_le_pow₀ ?_
      linarith
  . push_neg at hz₀
    have hz₁: 0 < fd a b i := by exact hd₁ i a b ha₀
    have hz₂: 0 < Real.log (z / fd a b i) := by
      refine Real.log_pos ?_
      exact (one_lt_div hz₁).mpr hz₀
    let j : ℕ := Nat.ceil (2 + Real.log (z / fd a b i) / Real.log (3 / 2))
    have hj₀: 2 < j := by
      refine Nat.lt_ceil.mpr ?_
      norm_cast
      refine lt_add_of_pos_right 2 ?_
      refine div_pos ?_ ?_
      . exact hz₂
      . refine Real.log_pos ?_
        linarith
    have hj₁: j ∈ sd := by
      rw [hsd]
      exact Set.mem_Ici_of_Ioi hj₀
    use ⟨j, hj₁⟩
    intro k hk₀
    have hk₁: fd a b i * (3 / 2) ^ (k.1 - 2) ≤ fd a b k := by
      exact hd₃ k
    have hk₂: i < k := by
      refine lt_of_lt_of_le ?_ hk₀
      refine Subtype.mk_lt_mk.mpr ?_
      refine Nat.lt_ceil.mpr ?_
      norm_cast
      rw [hi₁]
      refine lt_add_of_pos_right 2 ?_
      refine div_pos ?_ ?_
      . rw [← hi₁]
        exact hz₂
      . refine Real.log_pos ?_
        linarith
    refine le_trans ?_ hk₁
    refine (div_le_iff₀' ?_).mp ?_
    . exact hz₁
    . refine Real.le_pow_of_log_le (by linarith) ?_
      refine (div_le_iff₀ ?_).mp ?_
      . refine Real.log_pos ?_
        linarith
      . rw [Nat.cast_sub ?_]
        . rw [Nat.cast_two]
          refine le_sub_iff_add_le'.mpr ?_
          exact Nat.le_of_ceil_le hk₀
        . rw [hi₁] at hk₂
          exact Nat.le_of_succ_le hk₂


lemma imo_1985_p6_unique_top_7
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩)
  (hd₃ : ∀ (nd : ↑sd), fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd)
  (hsd₁ : Nonempty ↑sd):
   Filter.Tendsto (fd a b) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro z
  by_cases hz₀: z ≤ fd a b i
  . use i
    intros j _
    refine le_trans hz₀ ?_
    refine le_trans ?_ (hd₃ j)
    refine le_mul_of_one_le_right ?_ ?_
    . refine le_of_lt ?_
      exact hd₁ i a b ha₀
    . refine one_le_pow₀ ?_
      linarith
  . push_neg at hz₀
    have hz₁: 0 < fd a b i := by exact hd₁ i a b ha₀
    have hz₂: 0 < Real.log (z / fd a b i) := by
      refine Real.log_pos ?_
      exact (one_lt_div hz₁).mpr hz₀
    let j : ℕ := Nat.ceil (2 + Real.log (z / fd a b i) / Real.log (3 / 2))
    have hj₀: 2 < j := by
      refine Nat.lt_ceil.mpr ?_
      norm_cast
      refine lt_add_of_pos_right 2 ?_
      refine div_pos ?_ ?_
      . exact hz₂
      . refine Real.log_pos ?_
        linarith
    have hj₁: j ∈ sd := by
      rw [hsd]
      exact Set.mem_Ici_of_Ioi hj₀
    use ⟨j, hj₁⟩
    intro k hk₀
    have hk₁: fd a b i * (3 / 2) ^ (k.1 - 2) ≤ fd a b k := by
      exact hd₃ k
    have hk₂: i < k := by
      refine lt_of_lt_of_le ?_ hk₀
      refine Subtype.mk_lt_mk.mpr ?_
      refine Nat.lt_ceil.mpr ?_
      norm_cast
      rw [hi₁]
      refine lt_add_of_pos_right 2 ?_
      refine div_pos ?_ ?_
      . rw [← hi₁]
        exact hz₂
      . refine Real.log_pos ?_
        linarith
    refine le_trans ?_ hk₁
    refine (div_le_iff₀' ?_).mp ?_
    . exact hz₁
    . refine Real.le_pow_of_log_le (by linarith) ?_
      refine (div_le_iff₀ ?_).mp ?_
      . refine Real.log_pos ?_
        linarith
      . rw [Nat.cast_sub ?_]
        . rw [Nat.cast_two]
          refine le_sub_iff_add_le'.mpr ?_
          exact Nat.le_of_ceil_le hk₀
        . rw [hi₁] at hk₂
          exact Nat.le_of_succ_le hk₂

lemma imo_1985_p6_unique_top_8
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩)
  (hd₃ : ∀ (nd : ↑sd), fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd)
  (z : ℝ):
   ∃ i, ∀ (a_1 : ↑sd), i ≤ a_1 → z ≤ fd a b a_1 := by
  by_cases hz₀: z ≤ fd a b i
  . use i
    intros j _
    refine le_trans hz₀ ?_
    refine le_trans ?_ (hd₃ j)
    refine le_mul_of_one_le_right ?_ ?_
    . refine le_of_lt ?_
      exact hd₁ i a b ha₀
    . refine one_le_pow₀ ?_
      linarith
  . push_neg at hz₀
    have hz₁: 0 < fd a b i := by exact hd₁ i a b ha₀
    have hz₂: 0 < Real.log (z / fd a b i) := by
      refine Real.log_pos ?_
      exact (one_lt_div hz₁).mpr hz₀
    let j : ℕ := Nat.ceil (2 + Real.log (z / fd a b i) / Real.log (3 / 2))
    have hj₀: 2 < j := by
      refine Nat.lt_ceil.mpr ?_
      norm_cast
      refine lt_add_of_pos_right 2 ?_
      refine div_pos ?_ ?_
      . exact hz₂
      . refine Real.log_pos ?_
        linarith
    have hj₁: j ∈ sd := by
      rw [hsd]
      exact Set.mem_Ici_of_Ioi hj₀
    use ⟨j, hj₁⟩
    intro k hk₀
    have hk₁: fd a b i * (3 / 2) ^ (k.1 - 2) ≤ fd a b k := by
      exact hd₃ k
    have hk₂: i < k := by
      refine lt_of_lt_of_le ?_ hk₀
      refine Subtype.mk_lt_mk.mpr ?_
      refine Nat.lt_ceil.mpr ?_
      norm_cast
      rw [hi₁]
      refine lt_add_of_pos_right 2 ?_
      refine div_pos ?_ ?_
      . rw [← hi₁]
        exact hz₂
      . refine Real.log_pos ?_
        linarith
    refine le_trans ?_ hk₁
    refine (div_le_iff₀' ?_).mp ?_
    . exact hz₁
    . refine Real.le_pow_of_log_le (by linarith) ?_
      refine (div_le_iff₀ ?_).mp ?_
      . refine Real.log_pos ?_
        linarith
      . rw [Nat.cast_sub ?_]
        . rw [Nat.cast_two]
          refine le_sub_iff_add_le'.mpr ?_
          exact Nat.le_of_ceil_le hk₀
        . rw [hi₁] at hk₂
          exact Nat.le_of_succ_le hk₂



lemma imo_1985_p6_unique_top_9
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (i : ↑sd)
  (hd₃ : ∀ (nd : ↑sd), fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd)
  (z : ℝ)
  (hz₀ : z ≤ fd a b i):
   ∃ i, ∀ (a_1 : ↑sd), i ≤ a_1 → z ≤ fd a b a_1 := by
  use i
  intros j _
  refine le_trans hz₀ ?_
  refine le_trans ?_ (hd₃ j)
  refine le_mul_of_one_le_right ?_ ?_
  . refine le_of_lt ?_
    exact hd₁ i a b ha₀
  . refine one_le_pow₀ ?_
    linarith

lemma imo_1985_p6_unique_top_10
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (i : ↑sd)
  (hd₃ : ∀ (nd : ↑sd), fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd)
  (z : ℝ)
  (hz₀ : z ≤ fd a b i):
   ∀ (a_1 : ↑sd), i ≤ a_1 → z ≤ fd a b a_1 := by
  intros j _
  refine le_trans hz₀ ?_
  refine le_trans ?_ (hd₃ j)
  refine le_mul_of_one_le_right ?_ ?_
  . refine le_of_lt ?_
    exact hd₁ i a b ha₀
  . refine one_le_pow₀ ?_
    linarith

lemma imo_1985_p6_unique_top_11
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (i : ↑sd)
  (hd₃ : ∀ (nd : ↑sd), fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd)
  (j : ↑sd) :
   fd a b i ≤ fd a b j := by
  refine le_trans ?_ (hd₃ j)
  refine le_mul_of_one_le_right ?_ ?_
  . refine le_of_lt ?_
    exact hd₁ i a b ha₀
  . refine one_le_pow₀ ?_
    linarith

lemma imo_1985_p6_unique_top_12
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (hd₁ : ∀ (n : ↑sd) (a b : NNReal), a < b → 0 < fd a b n)
  (a b : NNReal)
  (ha₀ : a < b)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩)
  (hd₃ : ∀ (nd : ↑sd), fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd)
  (z : ℝ)
  (hz₀ : fd a b i < z):
   ∃ i, ∀ (a_1 : ↑sd), i ≤ a_1 → z ≤ fd a b a_1 := by
  have hz₁: 0 < fd a b i := by exact hd₁ i a b ha₀
  have hz₂: 0 < Real.log (z / fd a b i) := by
    refine Real.log_pos ?_
    exact (one_lt_div hz₁).mpr hz₀
  let j : ℕ := Nat.ceil (2 + Real.log (z / fd a b i) / Real.log (3 / 2))
  have hj₀: 2 < j := by
    refine Nat.lt_ceil.mpr ?_
    norm_cast
    refine lt_add_of_pos_right 2 ?_
    refine div_pos ?_ ?_
    . exact hz₂
    . refine Real.log_pos ?_
      linarith
  have hj₁: j ∈ sd := by
    rw [hsd]
    exact Set.mem_Ici_of_Ioi hj₀
  use ⟨j, hj₁⟩
  intro k hk₀
  have hk₁: fd a b i * (3 / 2) ^ (k.1 - 2) ≤ fd a b k := by
    exact hd₃ k
  have hk₂: i < k := by
    refine lt_of_lt_of_le ?_ hk₀
    refine Subtype.mk_lt_mk.mpr ?_
    refine Nat.lt_ceil.mpr ?_
    norm_cast
    rw [hi₁]
    refine lt_add_of_pos_right 2 ?_
    refine div_pos ?_ ?_
    . rw [← hi₁]
      exact hz₂
    . refine Real.log_pos ?_
      linarith
  refine le_trans ?_ hk₁
  refine (div_le_iff₀' ?_).mp ?_
  . exact hz₁
  . refine Real.le_pow_of_log_le (by linarith) ?_
    refine (div_le_iff₀ ?_).mp ?_
    . refine Real.log_pos ?_
      linarith
    . rw [Nat.cast_sub ?_]
      . rw [Nat.cast_two]
        refine le_sub_iff_add_le'.mpr ?_
        exact Nat.le_of_ceil_le hk₀
      . rw [hi₁] at hk₂
        exact Nat.le_of_succ_le hk₂

lemma imo_1985_p6_unique_top_13
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (i : ↑sd)
  (z : ℝ)
  (hz₂ : 0 < Real.log (z / fd a b i))
  (j : ℕ)
  (hj : j = ⌈2 + Real.log (z / fd a b i) / Real.log (3 / 2)⌉₊):
  2 < j := by
  rw [hj]
  refine Nat.lt_ceil.mpr ?_
  norm_cast
  refine lt_add_of_pos_right 2 ?_
  refine div_pos ?_ ?_
  . exact hz₂
  . refine Real.log_pos ?_
    linarith

lemma imo_1985_p6_unique_top_14
  (sd : Set ℕ)
  (hsd : sd = Set.Ici 2)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩)
  (hd₃ : ∀ (nd : ↑sd), fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd)
  (z : ℝ)
  (hz₁ : 0 < fd a b i)
  (hz₂ : 0 < Real.log (z / fd a b i))
  (j : ℕ)
  (hj : j = ⌈2 + Real.log (z / fd a b i) / Real.log (3 / 2)⌉₊)
  (hj₀ : 2 < j):
   ∃ i, ∀ (a_1 : ↑sd), i ≤ a_1 → z ≤ fd a b a_1 := by
  have hj₁: j ∈ sd := by
    rw [hsd]
    exact Set.mem_Ici_of_Ioi hj₀
  use ⟨j, hj₁⟩
  intro k hk₀
  have hk₁: fd a b i * (3 / 2) ^ (k.1 - 2) ≤ fd a b k := by
    exact hd₃ k
  have hk₂: i < k := by
    refine lt_of_lt_of_le ?_ hk₀
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hj, hi₁]
    refine Nat.lt_ceil.mpr ?_
    refine lt_add_of_pos_right 2 ?_
    refine div_pos ?_ ?_
    . rw [← hi₁]
      exact hz₂
    . refine Real.log_pos ?_
      linarith
  refine le_trans ?_ hk₁
  refine (div_le_iff₀' ?_).mp ?_
  . exact hz₁
  . refine Real.le_pow_of_log_le (by linarith) ?_
    refine (div_le_iff₀ ?_).mp ?_
    . refine Real.log_pos ?_
      linarith
    . rw [Nat.cast_sub ?_]
      . rw [Nat.cast_two]
        refine le_sub_iff_add_le'.mpr ?_
        refine Nat.le_of_ceil_le ?_
        exact le_of_eq_of_le (id (Eq.symm hj)) hk₀
      . rw [hi₁] at hk₂
        exact Nat.le_of_succ_le hk₂

lemma imo_1985_p6_unique_top_15
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩)
  (hd₃ : ∀ (nd : ↑sd), fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd)
  (z : ℝ)
  (hz₁ : 0 < fd a b i)
  (hz₂ : 0 < Real.log (z / fd a b i))
  (j : ℕ)
  (hj : j = ⌈2 + Real.log (z / fd a b i) / Real.log (3 / 2)⌉₊)
  (hj₁ : j ∈ sd):
   ∃ i, ∀ (a_1 : ↑sd), i ≤ a_1 → z ≤ fd a b a_1 := by
  use ⟨j, hj₁⟩
  intro k hk₀
  have hk₁: fd a b i * (3 / 2) ^ (k.1 - 2) ≤ fd a b k := by
    exact hd₃ k
  have hk₂: i < k := by
    refine lt_of_lt_of_le ?_ hk₀
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hj, hi₁]
    refine Nat.lt_ceil.mpr ?_
    norm_cast
    refine lt_add_of_pos_right 2 ?_
    refine div_pos ?_ ?_
    . rw [← hi₁]
      exact hz₂
    . refine Real.log_pos ?_
      linarith
  refine le_trans ?_ hk₁
  refine (div_le_iff₀' ?_).mp ?_
  . exact hz₁
  . refine Real.le_pow_of_log_le (by linarith) ?_
    refine (div_le_iff₀ ?_).mp ?_
    . refine Real.log_pos ?_
      linarith
    . rw [Nat.cast_sub ?_]
      . rw [Nat.cast_two]
        refine le_sub_iff_add_le'.mpr ?_
        refine Nat.le_of_ceil_le ?_
        exact le_of_eq_of_le (id (Eq.symm hj)) hk₀
      . rw [hi₁] at hk₂
        exact Nat.le_of_succ_le hk₂

lemma imo_1985_p6_unique_top_16
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩)
  (hd₃ : ∀ (nd : ↑sd), fd a b i * (3 / 2) ^ (nd.1 - 2) ≤ fd a b nd)
  (z : ℝ)
  (hz₁ : 0 < fd a b i)
  (hz₂ : 0 < Real.log (z / fd a b i))
  (j : ℕ)
  (hj : j = ⌈2 + Real.log (z / fd a b i) / Real.log (3 / 2)⌉₊)
  (hj₁ : j ∈ sd):
   ∀ (a_1 : ↑sd), ⟨j, hj₁⟩ ≤ a_1 → z ≤ fd a b a_1 := by
  intro k hk₀
  have hk₁: fd a b i * (3 / 2) ^ (k.1 - 2) ≤ fd a b k := by
    exact hd₃ k
  have hk₂: i < k := by
    refine lt_of_lt_of_le ?_ hk₀
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hj, hi₁]
    refine Nat.lt_ceil.mpr ?_
    norm_cast
    refine lt_add_of_pos_right 2 ?_
    refine div_pos ?_ ?_
    . rw [← hi₁]
      exact hz₂
    . refine Real.log_pos ?_
      linarith
  refine le_trans ?_ hk₁
  refine (div_le_iff₀' ?_).mp ?_
  . exact hz₁
  . refine Real.le_pow_of_log_le (by linarith) ?_
    refine (div_le_iff₀ ?_).mp ?_
    . refine Real.log_pos ?_
      linarith
    . rw [Nat.cast_sub ?_]
      . rw [Nat.cast_two]
        refine le_sub_iff_add_le'.mpr ?_
        refine Nat.le_of_ceil_le ?_
        exact le_of_eq_of_le (id (Eq.symm hj)) hk₀
      . rw [hi₁] at hk₂
        exact Nat.le_of_succ_le hk₂


lemma imo_1985_p6_unique_top_17
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (hi : 2 ∈ sd)
  (i : ↑sd)
  (hi₁ : i = ⟨2, hi⟩)
  (z : ℝ)
  (hz₂ : 0 < Real.log (z / fd a b i))
  (j : ℕ)
  (hj : j = ⌈2 + Real.log (z / fd a b i) / Real.log (3 / 2)⌉₊)
  (hj₁ : j ∈ sd)
  (k : ↑sd)
  (hk₀ : ⟨j, hj₁⟩ ≤ k):
   i < k := by
  refine lt_of_lt_of_le ?_ hk₀
  refine Subtype.mk_lt_mk.mpr ?_
  rw [hj, hi₁]
  refine Nat.lt_ceil.mpr ?_
  norm_cast
  refine lt_add_of_pos_right 2 ?_
  refine div_pos ?_ ?_
  . rw [← hi₁]
    exact hz₂
  . refine Real.log_pos ?_
    linarith

lemma imo_1985_p6_unique_top_18
  (sd : Set ℕ)
  (fd : NNReal → NNReal → ↑sd → ℝ)
  (a b : NNReal)
  (i : ↑sd)
  (z : ℝ)
  (hz₂ : 0 < Real.log (z / fd a b i)):
   2 < 2 + Real.log (z / fd a b i) / Real.log (3 / 2) := by
  refine lt_add_of_pos_right 2 ?_
  refine div_pos ?_ ?_
  . exact hz₂
  . refine Real.log_pos ?_
    linarith


lemma imo_1985_p6_bonus_5_6
  (sn : Set ℕ)
  (n : ↑sn)
  (g₁ : ((1:ℝ) - (↑↑n)⁻¹) ⊔ 0 = 1 - (↑↑n)⁻¹):
  ((1:ℝ) - (1 - (↑↑n)⁻¹) ⊔ 0).toNNReal = (↑↑n)⁻¹ := by
  rw [g₁, ← sub_add, sub_self, zero_add]
  rw [Real.toNNReal_inv]
  refine inv_inj.mpr ?_
  exact NNReal.toNNReal_coe_nat n


lemma imo_1985_p6_bonus_6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hsn₀ : sn = Set.Ici 1)
  (hsn₁ : ∀ (n : ↑sn), 0 < n.1)
  (hfb₀ : fb = fun (n : ↑sn) => fi (↑n) (1 - 1 / ↑↑n))
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x) :
  1 / 2 ∉ sb := by
  have g₀: ∀ (n:↑sn), fb n ≠ (1 / 2:NNReal) := by
    intro n
    have hfb₄: ∀ n, fb n = fi (n.1) (1 - 1 / ↑↑n) := by
      rw [hfb₀]
      simp
    rw [hfb₄]
    by_contra! hn₀
    apply (hf₇ n.1 _ _ (hsn₁ n)).mpr at hn₀
    contrapose! hn₀
    clear hn₀
    refine ne_of_gt ?_
    rw [hf₂ n.1 _ (hsn₁ n)]
    induction' n with n hn₀
    refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
    simp
    have g₀: (↑n)⁻¹ ≤ (1:NNReal) := by
      exact Nat.cast_inv_le_one n
    rw [NNReal.coe_sub g₀, NNReal.coe_inv, NNReal.coe_natCast]
    norm_cast
    rw [hsn₀] at hn₀
    have hn₁: 1 ≤ n := by exact hn₀
    have g₁: f 2 2⁻¹ = 3 / 4 := by
      rw [h₁ 1 _ (by linarith), h₀, inv_eq_one_div 2, NNReal.coe_div 1 2]
      rw [NNReal.coe_ofNat]
      norm_cast
      ring_nf
    by_cases hn₂: 4 ≤ n
    . have hn₃: 1 < f n 2⁻¹ := by
        refine Nat.le_induction ?_ ?_ n hn₂
        . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
          ring_nf
          linarith
        . intros m hm₀ hm₁
          refine lt_trans hm₁ ?_
          refine h₈ m _ (by linarith) ?_ ?_
          . refine inv_pos.mpr ?_
            exact zero_lt_two
          . refine lt_trans ?_ hm₁
            refine sub_lt_self 1 ?_
            refine one_div_pos.mpr ?_
            refine Nat.cast_pos.mpr ?_
            exact Nat.zero_lt_of_lt hm₀
      have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
        refine sub_lt_self 1 ?_
        refine inv_pos.mpr ?_
        exact Nat.cast_pos'.mpr hn₀
      exact gt_trans hn₃ hn₄
    . interval_cases n
      . rw [h₀]
        norm_cast
        rw [inv_one, sub_self 1]
        refine inv_pos.mpr ?_
        exact Nat.ofNat_pos'
      . rw [g₁]
        ring_nf
        linarith
      . rw [h₁ 2 _ (by linarith), g₁]
        ring_nf
        linarith
  rw [hsb₀]
  contrapose! g₀
  exact g₀


lemma imo_1985_p6_bonus_6_1
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hsn₀ : sn = Set.Ici 1)
  (hsn₁ : ∀ (n : ↑sn), 0 < n.1)
  (hfb₀ : fb = fun (n:↑sn) => fi (↑n) (1 - 1 / ↑↑n))
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x):
   ∀ (n : ↑sn), fb n ≠ 1 / 2 := by
  intro n
  have hfb₄: ∀ n, fb n = fi (n.1) (1 - 1 / ↑↑n) := by
    rw [hfb₀]
    simp
  rw [hfb₄]
  by_contra! hn₀
  apply (hf₇ n.1 _ _ (hsn₁ n)).mpr at hn₀
  contrapose! hn₀
  clear hn₀
  refine ne_of_gt ?_
  rw [hf₂ n.1 _ (hsn₁ n)]
  induction' n with n hn₀
  refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
  simp
  have g₀: (↑n)⁻¹ ≤ (1:NNReal) := by
    exact Nat.cast_inv_le_one n
  rw [NNReal.coe_sub g₀, NNReal.coe_inv, NNReal.coe_natCast]
  norm_cast
  rw [hsn₀] at hn₀
  have hn₁: 1 ≤ n := by exact hn₀
  have g₁: f 2 2⁻¹ = 3 / 4 := by
    rw [h₁ 1 _ (by linarith), h₀, inv_eq_one_div 2, NNReal.coe_div 1 2]
    rw [NNReal.coe_ofNat]
    norm_cast
    ring_nf
  by_cases hn₂: 4 ≤ n
  . have hn₃: 1 < f n 2⁻¹ := by
      refine Nat.le_induction ?_ ?_ n hn₂
      . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
        ring_nf
        linarith
      . intros m hm₀ hm₁
        refine lt_trans hm₁ ?_
        refine h₈ m _ (by linarith) ?_ ?_
        . refine inv_pos.mpr ?_
          exact zero_lt_two
        . refine lt_trans ?_ hm₁
          refine sub_lt_self 1 ?_
          refine one_div_pos.mpr ?_
          refine Nat.cast_pos.mpr ?_
          exact Nat.zero_lt_of_lt hm₀
    have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
      refine sub_lt_self 1 ?_
      refine inv_pos.mpr ?_
      exact Nat.cast_pos'.mpr hn₀
    exact gt_trans hn₃ hn₄
  . interval_cases n
    . rw [h₀]
      norm_cast
      rw [inv_one, sub_self 1]
      refine inv_pos.mpr ?_
      exact Nat.ofNat_pos'
    . rw [g₁]
      ring_nf
      linarith
    . rw [h₁ 2 _ (by linarith), g₁]
      ring_nf
      linarith


lemma imo_1985_p6_bonus_6_2
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (g₀ : ∀ (n : ↑sn), fb n ≠ 1 / 2):
   1 / 2 ∉ sb := by
  rw [hsb₀]
  contrapose! g₀
  exact g₀


lemma imo_1985_p6_bonus_6_3
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (hsn₁ : ∀ (n : ↑sn), 0 < n.1)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (n : ↑sn):
   fi (↑n) (1 - 1 / ↑↑n) ≠ 1 / 2 := by
  by_contra! hn₀
  apply (hf₇ n.1 _ _ (hsn₁ n)).mpr at hn₀
  contrapose! hn₀
  clear hn₀
  refine ne_of_gt ?_
  rw [hf₂ n.1 _ (hsn₁ n)]
  induction' n with n hn₀
  refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
  simp
  have g₀: (↑n)⁻¹ ≤ (1:NNReal) := by
    exact Nat.cast_inv_le_one n
  rw [NNReal.coe_sub g₀, NNReal.coe_inv, NNReal.coe_natCast]
  norm_cast
  rw [hsn₀] at hn₀
  have hn₁: 1 ≤ n := by exact hn₀
  have g₁: f 2 2⁻¹ = 3 / 4 := by
    rw [h₁ 1 _ (by linarith), h₀, inv_eq_one_div 2, NNReal.coe_div 1 2]
    rw [NNReal.coe_ofNat]
    norm_cast
    ring_nf
  by_cases hn₂: 4 ≤ n
  . have hn₃: 1 < f n 2⁻¹ := by
      refine Nat.le_induction ?_ ?_ n hn₂
      . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
        ring_nf
        linarith
      . intros m hm₀ hm₁
        refine lt_trans hm₁ ?_
        refine h₈ m _ (by linarith) ?_ ?_
        . refine inv_pos.mpr ?_
          exact zero_lt_two
        . refine lt_trans ?_ hm₁
          refine sub_lt_self 1 ?_
          refine one_div_pos.mpr ?_
          refine Nat.cast_pos.mpr ?_
          exact Nat.zero_lt_of_lt hm₀
    have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
      refine sub_lt_self 1 ?_
      refine inv_pos.mpr ?_
      exact Nat.cast_pos'.mpr hn₀
    exact gt_trans hn₃ hn₄
  . interval_cases n
    . rw [h₀]
      norm_cast
      rw [inv_one, sub_self 1]
      refine inv_pos.mpr ?_
      exact Nat.ofNat_pos'
    . rw [g₁]
      ring_nf
      linarith
    . rw [h₁ 2 _ (by linarith), g₁]
      ring_nf
      linarith



lemma imo_1985_p6_bonus_6_4
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (hsn₁ : ∀ (n : ↑sn), 0 < n.1)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (n : ↑sn)
  (hn₀ : fi (↑n) (1 - 1 / ↑↑n) = 1 / 2):
   False := by
  apply (hf₇ n.1 _ _ (hsn₁ n)).mpr at hn₀
  contrapose! hn₀
  clear hn₀
  refine ne_of_gt ?_
  rw [hf₂ n.1 _ (hsn₁ n)]
  induction' n with n hn₀
  refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
  simp
  have g₀: (↑n)⁻¹ ≤ (1:NNReal) := by
    exact Nat.cast_inv_le_one n
  rw [NNReal.coe_sub g₀, NNReal.coe_inv, NNReal.coe_natCast]
  norm_cast
  rw [hsn₀] at hn₀
  have hn₁: 1 ≤ n := by exact hn₀
  have g₁: f 2 2⁻¹ = 3 / 4 := by
    rw [h₁ 1 _ (by linarith), h₀, inv_eq_one_div 2, NNReal.coe_div 1 2]
    rw [NNReal.coe_ofNat]
    norm_cast
    ring_nf
  by_cases hn₂: 4 ≤ n
  . have hn₃: 1 < f n 2⁻¹ := by
      refine Nat.le_induction ?_ ?_ n hn₂
      . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
        ring_nf
        linarith
      . intros m hm₀ hm₁
        refine lt_trans hm₁ ?_
        refine h₈ m _ (by linarith) ?_ ?_
        . refine inv_pos.mpr ?_
          exact zero_lt_two
        . refine lt_trans ?_ hm₁
          refine sub_lt_self 1 ?_
          refine one_div_pos.mpr ?_
          refine Nat.cast_pos.mpr ?_
          exact Nat.zero_lt_of_lt hm₀
    have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
      refine sub_lt_self 1 ?_
      refine inv_pos.mpr ?_
      exact Nat.cast_pos'.mpr hn₀
    exact gt_trans hn₃ hn₄
  . interval_cases n
    . rw [h₀]
      norm_cast
      rw [inv_one, sub_self 1]
      refine inv_pos.mpr ?_
      exact Nat.ofNat_pos'
    . rw [g₁]
      ring_nf
      linarith
    . rw [h₁ 2 _ (by linarith), g₁]
      ring_nf
      linarith


lemma imo_1985_p6_bonus_6_5
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (hsn₁ : ∀ (n : ↑sn), 0 < n.1)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (n : ↑sn):
   f₀ (↑n) (1 / 2) ≠ 1 - 1 / ↑↑n := by
  refine ne_of_gt ?_
  rw [hf₂ n.1 _ (hsn₁ n)]
  induction' n with n hn₀
  refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
  simp
  have g₀: (↑n)⁻¹ ≤ (1:NNReal) := by
    exact Nat.cast_inv_le_one n
  rw [NNReal.coe_sub g₀, NNReal.coe_inv, NNReal.coe_natCast]
  norm_cast
  rw [hsn₀] at hn₀
  have hn₁: 1 ≤ n := by exact hn₀
  have g₁: f 2 2⁻¹ = 3 / 4 := by
    rw [h₁ 1 _ (by linarith), h₀, inv_eq_one_div 2, NNReal.coe_div 1 2]
    rw [NNReal.coe_ofNat]
    norm_cast
    ring_nf
  by_cases hn₂: 4 ≤ n
  . have hn₃: 1 < f n 2⁻¹ := by
      refine Nat.le_induction ?_ ?_ n hn₂
      . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
        ring_nf
        linarith
      . intros m hm₀ hm₁
        refine lt_trans hm₁ ?_
        refine h₈ m _ (by linarith) ?_ ?_
        . refine inv_pos.mpr ?_
          exact zero_lt_two
        . refine lt_trans ?_ hm₁
          refine sub_lt_self 1 ?_
          refine one_div_pos.mpr ?_
          refine Nat.cast_pos.mpr ?_
          exact Nat.zero_lt_of_lt hm₀
    have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
      refine sub_lt_self 1 ?_
      refine inv_pos.mpr ?_
      exact Nat.cast_pos'.mpr hn₀
    exact gt_trans hn₃ hn₄
  . interval_cases n
    . rw [h₀]
      norm_cast
      rw [inv_one, sub_self 1]
      refine inv_pos.mpr ?_
      exact Nat.ofNat_pos'
    . rw [g₁]
      ring_nf
      linarith
    . rw [h₁ 2 _ (by linarith), g₁]
      ring_nf
      linarith



lemma imo_1985_p6_bonus_6_6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (hsn₁ : ∀ (n : ↑sn), 0 < n.1)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (n : ↑sn):
   1 - 1 / ↑↑n < f₀ (↑n) (1 / 2) := by
  rw [hf₂ n.1 _ (hsn₁ n)]
  induction' n with n hn₀
  refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
  simp
  have g₀: (↑n)⁻¹ ≤ (1:NNReal) := by
    exact Nat.cast_inv_le_one n
  rw [NNReal.coe_sub g₀, NNReal.coe_inv, NNReal.coe_natCast]
  norm_cast
  rw [hsn₀] at hn₀
  have hn₁: 1 ≤ n := by exact hn₀
  have g₁: f 2 2⁻¹ = 3 / 4 := by
    rw [h₁ 1 _ (by linarith), h₀, inv_eq_one_div 2, NNReal.coe_div 1 2]
    rw [NNReal.coe_ofNat]
    norm_cast
    ring_nf
  by_cases hn₂: 4 ≤ n
  . have hn₃: 1 < f n 2⁻¹ := by
      refine Nat.le_induction ?_ ?_ n hn₂
      . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
        ring_nf
        linarith
      . intros m hm₀ hm₁
        refine lt_trans hm₁ ?_
        refine h₈ m _ (by linarith) ?_ ?_
        . refine inv_pos.mpr ?_
          exact zero_lt_two
        . refine lt_trans ?_ hm₁
          refine sub_lt_self 1 ?_
          refine one_div_pos.mpr ?_
          refine Nat.cast_pos.mpr ?_
          exact Nat.zero_lt_of_lt hm₀
    have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
      refine sub_lt_self 1 ?_
      refine inv_pos.mpr ?_
      exact Nat.cast_pos'.mpr hn₀
    exact gt_trans hn₃ hn₄
  . interval_cases n
    . rw [h₀]
      norm_cast
      rw [inv_one, sub_self 1]
      refine inv_pos.mpr ?_
      exact Nat.ofNat_pos'
    . rw [g₁]
      ring_nf
      linarith
    . rw [h₁ 2 _ (by linarith), g₁]
      ring_nf
      linarith


lemma imo_1985_p6_bonus_6_7
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (n : ↑sn):
   1 - 1 / ↑↑n < (f (↑n) (1 / 2)).toNNReal := by
  induction' n with n hn₀
  refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
  simp
  have g₀: (↑n)⁻¹ ≤ (1:NNReal) := by
    exact Nat.cast_inv_le_one n
  rw [NNReal.coe_sub g₀, NNReal.coe_inv, NNReal.coe_natCast]
  norm_cast
  rw [hsn₀] at hn₀
  have hn₁: 1 ≤ n := by exact hn₀
  have g₁: f 2 2⁻¹ = 3 / 4 := by
    rw [h₁ 1 _ (by linarith), h₀, inv_eq_one_div 2, NNReal.coe_div 1 2]
    rw [NNReal.coe_ofNat]
    norm_cast
    ring_nf
  by_cases hn₂: 4 ≤ n
  . have hn₃: 1 < f n 2⁻¹ := by
      refine Nat.le_induction ?_ ?_ n hn₂
      . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
        ring_nf
        linarith
      . intros m hm₀ hm₁
        refine lt_trans hm₁ ?_
        refine h₈ m _ (by linarith) ?_ ?_
        . refine inv_pos.mpr ?_
          exact zero_lt_two
        . refine lt_trans ?_ hm₁
          refine sub_lt_self 1 ?_
          refine one_div_pos.mpr ?_
          refine Nat.cast_pos.mpr ?_
          exact Nat.zero_lt_of_lt hm₀
    have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
      refine sub_lt_self 1 ?_
      refine inv_pos.mpr ?_
      exact Nat.cast_pos'.mpr hn₀
    exact gt_trans hn₃ hn₄
  . interval_cases n
    . rw [h₀]
      norm_cast
      rw [inv_one, sub_self 1]
      refine inv_pos.mpr ?_
      exact Nat.ofNat_pos'
    . rw [g₁]
      ring_nf
      linarith
    . rw [h₁ 2 _ (by linarith), g₁]
      ring_nf
      linarith


lemma imo_1985_p6_bonus_6_8
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (n : ℕ)
  (hn₀ : n ∈ sn):
  (1:NNReal) - 1 / ↑n < (f n (1 / 2)).toNNReal := by
  refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
  simp
  have g₀: (↑n)⁻¹ ≤ (1:NNReal) := by
    exact Nat.cast_inv_le_one n
  rw [NNReal.coe_sub g₀, NNReal.coe_inv, NNReal.coe_natCast]
  norm_cast
  rw [hsn₀] at hn₀
  have hn₁: 1 ≤ n := by exact hn₀
  have g₁: f 2 2⁻¹ = 3 / 4 := by
    rw [h₁ 1 _ (by linarith), h₀, inv_eq_one_div 2, NNReal.coe_div 1 2]
    rw [NNReal.coe_ofNat]
    norm_cast
    ring_nf
  by_cases hn₂: 4 ≤ n
  . have hn₃: 1 < f n 2⁻¹ := by
      refine Nat.le_induction ?_ ?_ n hn₂
      . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
        ring_nf
        linarith
      . intros m hm₀ hm₁
        refine lt_trans hm₁ ?_
        refine h₈ m _ (by linarith) ?_ ?_
        . refine inv_pos.mpr ?_
          exact zero_lt_two
        . refine lt_trans ?_ hm₁
          refine sub_lt_self 1 ?_
          refine one_div_pos.mpr ?_
          refine Nat.cast_pos.mpr ?_
          exact Nat.zero_lt_of_lt hm₀
    have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
      refine sub_lt_self 1 ?_
      refine inv_pos.mpr ?_
      exact Nat.cast_pos'.mpr hn₀
    exact gt_trans hn₃ hn₄
  . interval_cases n
    . rw [h₀]
      norm_cast
      rw [inv_one, sub_self 1]
      refine inv_pos.mpr ?_
      exact Nat.ofNat_pos'
    . rw [g₁]
      ring_nf
      linarith
    . rw [h₁ 2 _ (by linarith), g₁]
      ring_nf
      linarith


lemma imo_1985_p6_bonus_6_9
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (n : ℕ)
  (hn₀ : n ∈ sn):
   ↑((1:NNReal) - 1 / n) < f n (1 / 2) := by
  simp
  have g₀: (↑n)⁻¹ ≤ (1:NNReal) := by
    exact Nat.cast_inv_le_one n
  rw [NNReal.coe_sub g₀, NNReal.coe_inv, NNReal.coe_natCast]
  norm_cast
  rw [hsn₀] at hn₀
  have hn₁: 1 ≤ n := by exact hn₀
  have g₁: f 2 2⁻¹ = 3 / 4 := by
    rw [h₁ 1 _ (by linarith), h₀, inv_eq_one_div 2, NNReal.coe_div 1 2]
    rw [NNReal.coe_ofNat]
    norm_cast
    ring_nf
  by_cases hn₂: 4 ≤ n
  . have hn₃: 1 < f n 2⁻¹ := by
      refine Nat.le_induction ?_ ?_ n hn₂
      . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
        ring_nf
        linarith
      . intros m hm₀ hm₁
        refine lt_trans hm₁ ?_
        refine h₈ m _ (by linarith) ?_ ?_
        . refine inv_pos.mpr ?_
          exact zero_lt_two
        . refine lt_trans ?_ hm₁
          refine sub_lt_self 1 ?_
          refine one_div_pos.mpr ?_
          refine Nat.cast_pos.mpr ?_
          exact Nat.zero_lt_of_lt hm₀
    have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
      refine sub_lt_self 1 ?_
      refine inv_pos.mpr ?_
      exact Nat.cast_pos'.mpr hn₀
    exact gt_trans hn₃ hn₄
  . interval_cases n
    . rw [h₀]
      norm_cast
      rw [inv_one, sub_self 1]
      refine inv_pos.mpr ?_
      exact Nat.ofNat_pos'
    . rw [g₁]
      ring_nf
      linarith
    . rw [h₁ 2 _ (by linarith), g₁]
      ring_nf
      linarith


lemma imo_1985_p6_bonus_6_10
  (f : ℕ → NNReal → ℝ)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hsn₁ : ∀ (n : ↑sn), 0 < n.1)
  (n : ↑sn)
  (hfb₄ : ∀ (n : ↑sn), fb n = fi (↑n) (1 - 1 / ↑↑n))
  (hfb₅: ↑((1:NNReal) - 1 / n) < f n (1 / 2)):
   fb n ≠ 1 / 2 := by
  rw [hfb₄]
  by_contra! hn₀
  apply (hf₇ n.1 _ _ (hsn₁ n)).mpr at hn₀
  contrapose! hn₀
  clear hn₀
  refine ne_of_gt ?_
  rw [hf₂ n.1 _ (hsn₁ n)]
  induction' n with n hn₀
  exact Real.lt_toNNReal_iff_coe_lt.mpr hfb₅


lemma imo_1985_p6_bonus_6_11
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (n : ℕ)
  (hn₀ : n ∈ sn):
  ↑((1:NNReal) - (↑n)⁻¹) < f n 2⁻¹ := by
  have g₀: (↑n)⁻¹ ≤ (1:NNReal) := by
    exact Nat.cast_inv_le_one n
  rw [NNReal.coe_sub g₀, NNReal.coe_inv, NNReal.coe_natCast]
  norm_cast
  rw [hsn₀] at hn₀
  have hn₁: 1 ≤ n := by exact hn₀
  have g₁: f 2 2⁻¹ = 3 / 4 := by
    rw [h₁ 1 _ (by linarith), h₀, inv_eq_one_div 2, NNReal.coe_div 1 2]
    rw [NNReal.coe_ofNat]
    norm_cast
    ring_nf
  by_cases hn₂: 4 ≤ n
  . have hn₃: 1 < f n 2⁻¹ := by
      refine Nat.le_induction ?_ ?_ n hn₂
      . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
        ring_nf
        linarith
      . intros m hm₀ hm₁
        refine lt_trans hm₁ ?_
        refine h₈ m _ (by linarith) ?_ ?_
        . refine inv_pos.mpr ?_
          exact zero_lt_two
        . refine lt_trans ?_ hm₁
          refine sub_lt_self 1 ?_
          refine one_div_pos.mpr ?_
          refine Nat.cast_pos.mpr ?_
          exact Nat.zero_lt_of_lt hm₀
    have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
      refine sub_lt_self 1 ?_
      refine inv_pos.mpr ?_
      exact Nat.cast_pos'.mpr hn₀
    exact gt_trans hn₃ hn₄
  . interval_cases n
    . rw [h₀]
      norm_cast
      rw [inv_one, sub_self 1]
      refine inv_pos.mpr ?_
      exact Nat.ofNat_pos'
    . rw [g₁]
      ring_nf
      linarith
    . rw [h₁ 2 _ (by linarith), g₁]
      ring_nf
      linarith


lemma imo_1985_p6_bonus_6_12
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (n : ℕ)
  (hn₀ : n ∈ sn)
  (g₀ : (↑n)⁻¹ ≤ (1:NNReal)):
   1 - (↑n)⁻¹ < f n 2⁻¹ := by
  rw [hsn₀] at hn₀
  have hn₁: 1 ≤ n := by exact hn₀
  have g₁: f 2 2⁻¹ = 3 / 4 := by
    rw [h₁ 1 _ (by linarith), h₀, inv_eq_one_div 2, NNReal.coe_div 1 2]
    rw [NNReal.coe_ofNat]
    norm_cast
    ring_nf
  by_cases hn₂: 4 ≤ n
  . have hn₃: 1 < f n 2⁻¹ := by
      refine Nat.le_induction ?_ ?_ n hn₂
      . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
        ring_nf
        linarith
      . intros m hm₀ hm₁
        refine lt_trans hm₁ ?_
        refine h₈ m _ (by linarith) ?_ ?_
        . refine inv_pos.mpr ?_
          exact zero_lt_two
        . refine lt_trans ?_ hm₁
          refine sub_lt_self 1 ?_
          refine one_div_pos.mpr ?_
          refine Nat.cast_pos.mpr ?_
          exact Nat.zero_lt_of_lt hm₀
    have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
      refine sub_lt_self 1 ?_
      refine inv_pos.mpr ?_
      exact Nat.cast_pos'.mpr hn₀
    exact gt_trans hn₃ hn₄
  . interval_cases n
    . rw [h₀]
      norm_cast
      rw [inv_one, sub_self 1]
      refine inv_pos.mpr ?_
      exact Nat.ofNat_pos'
    . rw [g₁]
      ring_nf
      linarith
    . rw [h₁ 2 _ (by linarith), g₁]
      ring_nf
      linarith


lemma imo_1985_p6_bonus_6_13
  (f : ℕ → NNReal → ℝ)
  (n : ℕ)
  (hn₁ : 1 - (↑n)⁻¹ < f n 2⁻¹):
   ↑((1:NNReal) - (↑n)⁻¹) < f n 2⁻¹ := by
  have g₀: (↑n)⁻¹ ≤ (1:NNReal) := by
    exact Nat.cast_inv_le_one n
  rw [NNReal.coe_sub g₀, NNReal.coe_inv, NNReal.coe_natCast]
  exact hn₁


lemma imo_1985_p6_bonus_6_14
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n)):
   f 2 2⁻¹ = 3 / 4 := by
  rw [h₁ 1 _ (by linarith), h₀, inv_eq_one_div 2, NNReal.coe_div 1 2]
  rw [NNReal.coe_ofNat]
  norm_cast
  ring_nf


lemma imo_1985_p6_bonus_6_15
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (n : ℕ)
  (hn₀ : n ∈ Set.Ici 1)
  (g₀ : (↑n)⁻¹ ≤ (1:NNReal))
  (hn₁ : 1 ≤ n)
  (g₁ : f 2 2⁻¹ = 3 / 4):
   1 - (↑n)⁻¹ < f n 2⁻¹ := by
  by_cases hn₂: 4 ≤ n
  . have hn₃: 1 < f n 2⁻¹ := by
      refine Nat.le_induction ?_ ?_ n hn₂
      . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
        ring_nf
        linarith
      . intros m hm₀ hm₁
        refine lt_trans hm₁ ?_
        refine h₈ m _ (by linarith) ?_ ?_
        . refine inv_pos.mpr ?_
          exact zero_lt_two
        . refine lt_trans ?_ hm₁
          refine sub_lt_self 1 ?_
          refine one_div_pos.mpr ?_
          refine Nat.cast_pos.mpr ?_
          exact Nat.zero_lt_of_lt hm₀
    have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
      refine sub_lt_self 1 ?_
      refine inv_pos.mpr ?_
      exact Nat.cast_pos'.mpr hn₀
    exact gt_trans hn₃ hn₄
  . interval_cases n
    . rw [h₀]
      norm_cast
      rw [inv_one, sub_self 1]
      refine inv_pos.mpr ?_
      exact Nat.ofNat_pos'
    . rw [g₁]
      ring_nf
      linarith
    . rw [h₁ 2 _ (by linarith), g₁]
      ring_nf
      linarith


lemma imo_1985_p6_bonus_6_16
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (n : ℕ)
  (hn₀ : n ∈ Set.Ici 1)
  (g₁ : f 2 2⁻¹ = 3 / 4)
  (hn₂ : 4 ≤ n):
   1 - (↑n)⁻¹ < f n 2⁻¹ := by
  have hn₃: 1 < f n 2⁻¹ := by
    refine Nat.le_induction ?_ ?_ n hn₂
    . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
      ring_nf
      linarith
    . intros m hm₀ hm₁
      refine lt_trans hm₁ ?_
      refine h₈ m _ (by linarith) ?_ ?_
      . refine inv_pos.mpr ?_
        exact zero_lt_two
      . refine lt_trans ?_ hm₁
        refine sub_lt_self 1 ?_
        refine one_div_pos.mpr ?_
        refine Nat.cast_pos.mpr ?_
        exact Nat.zero_lt_of_lt hm₀
  have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
    refine sub_lt_self 1 ?_
    refine inv_pos.mpr ?_
    exact Nat.cast_pos'.mpr hn₀
  exact gt_trans hn₃ hn₄

lemma imo_1985_p6_bonus_6_17
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (n : ℕ)
  (g₁ : f 2 2⁻¹ = 3 / 4)
  (hn₂ : 4 ≤ n):
   1 < f n 2⁻¹ := by
  refine Nat.le_induction ?_ ?_ n hn₂
  . rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
    ring_nf
    linarith
  . intros m hm₀ hm₁
    refine lt_trans hm₁ ?_
    refine h₈ m _ (by linarith) ?_ ?_
    . refine inv_pos.mpr ?_
      exact zero_lt_two
    . refine lt_trans ?_ hm₁
      refine sub_lt_self 1 ?_
      refine one_div_pos.mpr ?_
      refine Nat.cast_pos.mpr ?_
      exact Nat.zero_lt_of_lt hm₀


lemma imo_1985_p6_bonus_6_18
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (g₁ : f 2 2⁻¹ = 3 / 4):
   1 < f 4 2⁻¹ := by
  rw [h₁ 3 _ (by linarith), h₁ 2 _ (by linarith), g₁]
  ring_nf
  linarith


lemma imo_1985_p6_bonus_6_19
  (f : ℕ → NNReal → ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x):
  ∀ (n : ℕ), 4 ≤ n → 1 < f n 2⁻¹ → 1 < f (n + 1) 2⁻¹ := by
  intros m hm₀ hm₁
  refine lt_trans hm₁ ?_
  refine h₈ m _ (by linarith) ?_ ?_
  . refine inv_pos.mpr ?_
    exact zero_lt_two
  . refine lt_trans ?_ hm₁
    refine sub_lt_self 1 ?_
    refine one_div_pos.mpr ?_
    refine Nat.cast_pos.mpr ?_
    exact Nat.zero_lt_of_lt hm₀


lemma imo_1985_p6_bonus_6_20
  (f : ℕ → NNReal → ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (m : ℕ)
  (hm₀ : 4 ≤ m)
  (hm₁ : 1 < f m 2⁻¹):
   f m 2⁻¹ < f (m + 1) 2⁻¹ := by
  refine h₈ m _ (by linarith) ?_ ?_
  . refine inv_pos.mpr ?_
    exact zero_lt_two
  . refine lt_trans ?_ hm₁
    refine sub_lt_self 1 ?_
    refine one_div_pos.mpr ?_
    refine Nat.cast_pos.mpr ?_
    exact Nat.zero_lt_of_lt hm₀

lemma imo_1985_p6_bonus_6_21
  (f : ℕ → NNReal → ℝ)
  (m : ℕ)
  (hm₀ : 4 ≤ m)
  (hm₁ : 1 < f m 2⁻¹):
   1 - 1 / ↑m < f m 2⁻¹ := by
  refine lt_trans ?_ hm₁
  refine sub_lt_self 1 ?_
  refine one_div_pos.mpr ?_
  refine Nat.cast_pos.mpr ?_
  exact Nat.zero_lt_of_lt hm₀

lemma imo_1985_p6_bonus_6_22
  (f : ℕ → NNReal → ℝ)
  (n : ℕ)
  (hn₀ : n ∈ Set.Ici 1)
  (hn₃ : 1 < f n 2⁻¹):
   1 - (↑n)⁻¹ < f n 2⁻¹ := by
  have hn₄: (1:ℝ) - (↑n)⁻¹ < 1 := by
    refine sub_lt_self 1 ?_
    refine inv_pos.mpr ?_
    exact Nat.cast_pos'.mpr hn₀
  exact gt_trans hn₃ hn₄

lemma imo_1985_p6_bonus_6_23
  (n : ℕ)
  (hn₀ : n ∈ Set.Ici 1):
  (1:ℝ) - (↑n)⁻¹ < 1 := by
  refine sub_lt_self 1 ?_
  refine inv_pos.mpr ?_
  exact Nat.cast_pos'.mpr hn₀

lemma imo_1985_p6_bonus_6_24
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (n : ℕ)
  (hn₀ : n ∈ Set.Ici 1)
  (g₀ : (↑n)⁻¹ ≤ (1:NNReal))
  (hn₁ : 1 ≤ n)
  (g₁ : f 2 2⁻¹ = 3 / 4)
  (hn₂ : ¬4 ≤ n):
   1 - (↑n)⁻¹ < f n 2⁻¹ := by
  interval_cases n
  . rw [h₀]
    norm_cast
    rw [inv_one, sub_self 1]
    refine inv_pos.mpr ?_
    exact Nat.ofNat_pos'
  . rw [g₁]
    ring_nf
    linarith
  . rw [h₁ 2 _ (by linarith), g₁]
    ring_nf
    linarith

lemma imo_1985_p6_bonus_6_25
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x):
   1 - (↑1)⁻¹ < f 1 2⁻¹ := by
  rw [h₀]
  norm_cast
  rw [inv_one, sub_self 1]
  refine inv_pos.mpr ?_
  exact Nat.ofNat_pos'

lemma imo_1985_p6_bonus_6_26
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (g₁ : f 2 2⁻¹ = 3 / 4):
   1 - (↑3)⁻¹ < f 3 2⁻¹ := by
  rw [h₁ 2 _ (by linarith), g₁]
  ring_nf
  linarith


lemma imo_1985_p6_10_16
  (sn : Set ℕ)
  (sb : Set NNReal)
  (fb : ↑sn → NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x => ↑x)
  (hnb₀ : 2 ∈ sn)
  (nb : ↑sn := ⟨2, hnb₀⟩) :
   ∃ x ∈ sb, fr x = ↑(fb nb) := by
  use fb ↑nb
  constructor
  . rw [hsb₀]
    exact Set.mem_range_self nb
  . exact congrFun hfr (fb ↑nb)


lemma imo_1985_p6_10_17
  (sn : Set ℕ)
  (sb : Set NNReal)
  (fb : ↑sn → NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x => ↑x)
  (hnb₀ : 2 ∈ sn)
  (nb : ↑sn := ⟨2, hnb₀⟩):
   fb nb ∈ sb ∧ fr (fb nb) = ↑(fb nb) := by
  constructor
  . rw [hsb₀]
    exact Set.mem_range_self nb
  . exact congrFun hfr (fb ↑nb)


lemma imo_1985_p6_10_18
  (sbr : Set ℝ)
  (br : ℝ)
  (hbr₀ : IsLUB sbr br)
  (g₁ : ∃ x, 0 < x ∧ x ∈ sbr):
   0 < br := by
  obtain ⟨x, hx₀, hx₁⟩ := g₁
  have hx₂: br ∈ upperBounds sbr := by
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  exact gt_of_ge_of_gt (hx₂ hx₁) hx₀


lemma imo_1985_p6_10_19
  (sbr : Set ℝ)
  (br : ℝ)
  (hbr₀ : IsLUB sbr br)
  (x : ℝ)
  (hx₀ : 0 < x)
  (hx₁ : x ∈ sbr):
   0 < br := by
  have hx₂: br ∈ upperBounds sbr := by
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  exact gt_of_ge_of_gt (hx₂ hx₁) hx₀


lemma imo_1985_p6_10_20
  (sbr : Set ℝ)
  (br : ℝ)
  (hbr₀ : IsLUB sbr br):
   br ∈ upperBounds sbr := by
  refine (isLUB_le_iff hbr₀).mp ?_
  exact Preorder.le_refl br




lemma imo_1985_p6_11_1
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc):
   ∀ (nb nc : ↑sn), fb nb < fc nc := by
  intros nb nc
  cases' (lt_or_le nb nc) with hn₀ hn₀
  . refine lt_trans ?_ (hfc₂ nc)
    exact hfb₃ hn₀
  cases' lt_or_eq_of_le hn₀ with hn₁ hn₁
  . refine lt_trans (hfc₂ nb) ?_
    exact hfc₃ hn₁
  . rw [hn₁]
    exact hfc₂ nb

lemma imo_1985_p6_11_2
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₃ : StrictMono fb)
  (nb nc : ↑sn)
  (hn₀ : nb < nc):
   fb nb < fc nc := by
  refine lt_trans ?_ (hfc₂ nc)
  exact hfb₃ hn₀

lemma imo_1985_p6_11_3
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfc₃ : StrictAnti fc)
  (nb nc : ↑sn)
  (hn₀ : nc ≤ nb):
   fb nb < fc nc := by
  cases' lt_or_eq_of_le hn₀ with hn₁ hn₁
  . refine lt_trans (hfc₂ nb) ?_
    exact hfc₃ hn₁
  . rw [hn₁]
    exact hfc₂ nb

lemma imo_1985_p6_11_4
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (hbr₀ : IsLUB sbr br)
  (hcr₀ : IsGLB scr cr)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n)
  (hfc₄ : ∀ (nb nc : ↑sn), fb nb < fc nc):
   br ≤ cr := by
  by_contra! hc₀
  have hc₁: ∃ x ∈ sbr, cr < x ∧ x ≤ br := by exact IsLUB.exists_between hbr₀ hc₀
  let ⟨x, hx₀, hx₁, _⟩ := hc₁
  have hc₂: ∃ y ∈ scr, cr ≤ y ∧ y < x := by exact IsGLB.exists_between hcr₀ hx₁
  let ⟨y, hy₀, _, hy₂⟩ := hc₂
  have hc₃: x < y := by
    have hx₃: x.toNNReal ∈ sb := by
      rw [hsbr] at hx₀
      apply (Set.mem_image fr sb x).mp at hx₀
      obtain ⟨z, hz₀, hz₁⟩ := hx₀
      rw [← hz₁, hfr, Real.toNNReal_coe]
      exact hz₀
    have hy₃: y.toNNReal ∈ sc := by
      rw [hscr] at hy₀
      apply (Set.mem_image fr sc y).mp at hy₀
      obtain ⟨z, hz₀, hz₁⟩ := hy₀
      rw [← hz₁, hfr, Real.toNNReal_coe]
      exact hz₀
    rw [hsb₀] at hx₃
    rw [hsc₀] at hy₃
    apply Set.mem_range.mp at hx₃
    apply Set.mem_range.mp at hy₃
    let ⟨nx, hnx₀⟩ := hx₃
    let ⟨ny, hny₀⟩ := hy₃
    have hy₄: 0 < y := by
      contrapose! hy₃
      have hy₅: y.toNNReal = 0 := by exact Real.toNNReal_of_nonpos hy₃
      intro z
      rw [hy₅]
      refine ne_of_gt ?_
      refine lt_of_le_of_lt ?_ (hfc₂ z)
      exact hfb₄ z
    refine (Real.toNNReal_lt_toNNReal_iff hy₄).mp ?_
    rw [← hnx₀, ← hny₀]
    exact hfc₄ nx ny
  refine (lt_self_iff_false x).mp ?_
  exact lt_trans hc₃ hy₂

lemma imo_1985_p6_11_5
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (hcr₀ : IsGLB scr cr)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n)
  (hfc₄ : ∀ (nb nc : ↑sn), fb nb < fc nc)
  (hc₁ : ∃ x ∈ sbr, cr < x ∧ x ≤ br):
   False := by
  let ⟨x, hx₀, hx₁, _⟩ := hc₁
  have hc₂: ∃ y ∈ scr, cr ≤ y ∧ y < x := by exact IsGLB.exists_between hcr₀ hx₁
  let ⟨y, hy₀, _, hy₂⟩ := hc₂
  have hc₃: x < y := by
    have hx₃: x.toNNReal ∈ sb := by
      rw [hsbr] at hx₀
      apply (Set.mem_image fr sb x).mp at hx₀
      obtain ⟨z, hz₀, hz₁⟩ := hx₀
      rw [← hz₁, hfr, Real.toNNReal_coe]
      exact hz₀
    have hy₃: y.toNNReal ∈ sc := by
      rw [hscr] at hy₀
      apply (Set.mem_image fr sc y).mp at hy₀
      obtain ⟨z, hz₀, hz₁⟩ := hy₀
      rw [← hz₁, hfr, Real.toNNReal_coe]
      exact hz₀
    rw [hsb₀] at hx₃
    rw [hsc₀] at hy₃
    apply Set.mem_range.mp at hx₃
    apply Set.mem_range.mp at hy₃
    let ⟨nx, hnx₀⟩ := hx₃
    let ⟨ny, hny₀⟩ := hy₃
    have hy₄: 0 < y := by
      contrapose! hy₃
      have hy₅: y.toNNReal = 0 := by exact Real.toNNReal_of_nonpos hy₃
      intro z
      rw [hy₅]
      refine ne_of_gt ?_
      refine lt_of_le_of_lt ?_ (hfc₂ z)
      exact hfb₄ z
    refine (Real.toNNReal_lt_toNNReal_iff hy₄).mp ?_
    rw [← hnx₀, ← hny₀]
    exact hfc₄ nx ny
  refine (lt_self_iff_false x).mp ?_
  exact lt_trans hc₃ hy₂


lemma imo_1985_p6_11_6
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n)
  (hfc₄ : ∀ (nb nc : ↑sn), fb nb < fc nc)
  (x : ℝ)
  (hx₀ : x ∈ sbr)
  (y : ℝ)
  (hy₀ : y ∈ scr)
  (hy₂ : y < x):
   False := by
  have hc₃: x < y := by
    have hx₃: x.toNNReal ∈ sb := by
      rw [hsbr] at hx₀
      apply (Set.mem_image fr sb x).mp at hx₀
      obtain ⟨z, hz₀, hz₁⟩ := hx₀
      rw [← hz₁, hfr, Real.toNNReal_coe]
      exact hz₀
    have hy₃: y.toNNReal ∈ sc := by
      rw [hscr] at hy₀
      apply (Set.mem_image fr sc y).mp at hy₀
      obtain ⟨z, hz₀, hz₁⟩ := hy₀
      rw [← hz₁, hfr, Real.toNNReal_coe]
      exact hz₀
    rw [hsb₀] at hx₃
    rw [hsc₀] at hy₃
    apply Set.mem_range.mp at hx₃
    apply Set.mem_range.mp at hy₃
    let ⟨nx, hnx₀⟩ := hx₃
    let ⟨ny, hny₀⟩ := hy₃
    have hy₄: 0 < y := by
      contrapose! hy₃
      have hy₅: y.toNNReal = 0 := by exact Real.toNNReal_of_nonpos hy₃
      intro z
      rw [hy₅]
      refine ne_of_gt ?_
      refine lt_of_le_of_lt ?_ (hfc₂ z)
      exact hfb₄ z
    refine (Real.toNNReal_lt_toNNReal_iff hy₄).mp ?_
    rw [← hnx₀, ← hny₀]
    exact hfc₄ nx ny
  refine (lt_self_iff_false x).mp ?_
  exact lt_trans hc₃ hy₂

lemma imo_1985_p6_11_7
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n)
  (hfc₄ : ∀ (nb nc : ↑sn), fb nb < fc nc)
  (x : ℝ)
  (hx₀ : x ∈ sbr)
  (y : ℝ)
  (hy₀ : y ∈ scr):
   x < y := by
  have hx₃: x.toNNReal ∈ sb := by
    rw [hsbr] at hx₀
    apply (Set.mem_image fr sb x).mp at hx₀
    obtain ⟨z, hz₀, hz₁⟩ := hx₀
    rw [← hz₁, hfr, Real.toNNReal_coe]
    exact hz₀
  have hy₃: y.toNNReal ∈ sc := by
    rw [hscr] at hy₀
    apply (Set.mem_image fr sc y).mp at hy₀
    obtain ⟨z, hz₀, hz₁⟩ := hy₀
    rw [← hz₁, hfr, Real.toNNReal_coe]
    exact hz₀
  rw [hsb₀] at hx₃
  rw [hsc₀] at hy₃
  apply Set.mem_range.mp at hx₃
  apply Set.mem_range.mp at hy₃
  let ⟨nx, hnx₀⟩ := hx₃
  let ⟨ny, hny₀⟩ := hy₃
  have hy₄: 0 < y := by
    contrapose! hy₃
    have hy₅: y.toNNReal = 0 := by exact Real.toNNReal_of_nonpos hy₃
    intro z
    rw [hy₅]
    refine ne_of_gt ?_
    refine lt_of_le_of_lt ?_ (hfc₂ z)
    exact hfb₄ z
  refine (Real.toNNReal_lt_toNNReal_iff hy₄).mp ?_
  rw [← hnx₀, ← hny₀]
  exact hfc₄ nx ny

lemma imo_1985_p6_11_8
  (sb : Set NNReal)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (x : ℝ)
  (hx₀ : x ∈ sbr):
   x.toNNReal ∈ sb := by
  rw [hsbr] at hx₀
  apply (Set.mem_image fr sb x).mp at hx₀
  obtain ⟨z, hz₀, hz₁⟩ := hx₀
  rw [← hz₁, hfr, Real.toNNReal_coe]
  exact hz₀

lemma imo_1985_p6_11_9
  (sb : Set NNReal)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (x : ℝ)
  (hx₀ : ∃ x_1 ∈ sb, fr x_1 = x):
   x.toNNReal ∈ sb := by
  obtain ⟨z, hz₀, hz₁⟩ := hx₀
  rw [← hz₁, hfr, Real.toNNReal_coe]
  exact hz₀

lemma imo_1985_p6_11_10
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n)
  (hfc₄ : ∀ (nb nc : ↑sn), fb nb < fc nc)
  (x : ℝ)
  (y : ℝ)
  (hy₀ : y ∈ scr)
  (hx₃ : x.toNNReal ∈ sb):
   x < y := by
  have hy₃: y.toNNReal ∈ sc := by
    rw [hscr] at hy₀
    apply (Set.mem_image fr sc y).mp at hy₀
    obtain ⟨z, hz₀, hz₁⟩ := hy₀
    rw [← hz₁, hfr, Real.toNNReal_coe]
    exact hz₀
  rw [hsb₀] at hx₃
  rw [hsc₀] at hy₃
  apply Set.mem_range.mp at hx₃
  apply Set.mem_range.mp at hy₃
  let ⟨nx, hnx₀⟩ := hx₃
  let ⟨ny, hny₀⟩ := hy₃
  have hy₄: 0 < y := by
    contrapose! hy₃
    have hy₅: y.toNNReal = 0 := by exact Real.toNNReal_of_nonpos hy₃
    intro z
    rw [hy₅]
    refine ne_of_gt ?_
    refine lt_of_le_of_lt ?_ (hfc₂ z)
    exact hfb₄ z
  refine (Real.toNNReal_lt_toNNReal_iff hy₄).mp ?_
  rw [← hnx₀, ← hny₀]
  exact hfc₄ nx ny

lemma imo_1985_p6_11_11
  (sc : Set NNReal)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (y : ℝ)
  (hy₀ : y ∈ scr):
   y.toNNReal ∈ sc := by
  rw [hscr] at hy₀
  apply (Set.mem_image fr sc y).mp at hy₀
  obtain ⟨z, hz₀, hz₁⟩ := hy₀
  rw [← hz₁, hfr, Real.toNNReal_coe]
  exact hz₀


lemma imo_1985_p6_11_12
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n)
  (hfc₄ : ∀ (nb nc : ↑sn), fb nb < fc nc)
  (x : ℝ)
  (y : ℝ)
  (hx₃ : x.toNNReal ∈ sb)
  (hy₃ : y.toNNReal ∈ sc):
   x < y := by
  rw [hsb₀] at hx₃
  rw [hsc₀] at hy₃
  apply Set.mem_range.mp at hx₃
  apply Set.mem_range.mp at hy₃
  let ⟨nx, hnx₀⟩ := hx₃
  let ⟨ny, hny₀⟩ := hy₃
  have hy₄: 0 < y := by
    contrapose! hy₃
    have hy₅: y.toNNReal = 0 := by exact Real.toNNReal_of_nonpos hy₃
    intro z
    rw [hy₅]
    refine ne_of_gt ?_
    refine lt_of_le_of_lt ?_ (hfc₂ z)
    exact hfb₄ z
  refine (Real.toNNReal_lt_toNNReal_iff hy₄).mp ?_
  rw [← hnx₀, ← hny₀]
  exact hfc₄ nx ny

lemma imo_1985_p6_11_13
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n)
  (hfc₄ : ∀ (nb nc : ↑sn), fb nb < fc nc)
  (x : ℝ)
  (y : ℝ)
  (hx₃ : ∃ y, fb y = x.toNNReal)
  (hy₃ : ∃ y_1, fc y_1 = y.toNNReal):
   x < y := by
  let ⟨nx, hnx₀⟩ := hx₃
  let ⟨ny, hny₀⟩ := hy₃
  have hy₄: 0 < y := by
    contrapose! hy₃
    have hy₅: y.toNNReal = 0 := by exact Real.toNNReal_of_nonpos hy₃
    intro z
    rw [hy₅]
    refine ne_of_gt ?_
    refine lt_of_le_of_lt ?_ (hfc₂ z)
    exact hfb₄ z
  refine (Real.toNNReal_lt_toNNReal_iff hy₄).mp ?_
  rw [← hnx₀, ← hny₀]
  exact hfc₄ nx ny

lemma imo_1985_p6_11_14
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n)
  (y : ℝ)
  (hy₃ : ∃ y_1, fc y_1 = y.toNNReal):
   0 < y := by
  contrapose! hy₃
  have hy₅: y.toNNReal = 0 := by exact Real.toNNReal_of_nonpos hy₃
  intro z
  rw [hy₅]
  refine ne_of_gt ?_
  refine lt_of_le_of_lt ?_ (hfc₂ z)
  exact hfb₄ z

lemma imo_1985_p6_11_15
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n)
  (y : ℝ)
  (hy₃ : y ≤ 0):
   ∀ (y_1 : ↑sn), fc y_1 ≠ y.toNNReal := by
  have hy₅: y.toNNReal = 0 := by exact Real.toNNReal_of_nonpos hy₃
  intro z
  rw [hy₅]
  refine ne_of_gt ?_
  refine lt_of_le_of_lt ?_ (hfc₂ z)
  exact hfb₄ z

lemma imo_1985_p6_11_16
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₂ : ∀ (n : ↑sn), fb n < fc n)
  (hfb₄ : ∀ (n : ↑sn), 0 ≤ fb n)
  (y : ℝ)
  (hy₅ : y.toNNReal = 0)
  (z : ↑sn):
   fc z ≠ y.toNNReal := by
  rw [hy₅]
  refine ne_of_gt ?_
  refine lt_of_le_of_lt ?_ (hfc₂ z)
  exact hfb₄ z


lemma imo_1985_p6_11_17
  (sn : Set ℕ)
  (fb fc : ↑sn → NNReal)
  (hfc₄ : ∀ (nb nc : ↑sn), fb nb < fc nc)
  (x : ℝ)
  (y : ℝ)
  (nx : ↑sn)
  (hnx₀ : fb nx = x.toNNReal)
  (ny : ↑sn)
  (hny₀ : fc ny = y.toNNReal)
  (hy₄ : 0 < y):
   x < y := by
  refine (Real.toNNReal_lt_toNNReal_iff hy₄).mp ?_
  rw [← hnx₀, ← hny₀]
  exact hfc₄ nx ny



lemma imo_1985_p6_exists_1
  (f : ℕ → NNReal → ℝ)
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₁ : 0 < br)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (hu₆ : br < cr):
   ∃ x, ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1 := by
  apply exists_between at hu₆
  let ⟨a, ha₀, ha₁⟩ := hu₆
  have ha₂: 0 < a := by exact gt_trans ha₀ hbr₁
  have ha₃: 0 < a.toNNReal := by exact Real.toNNReal_pos.mpr ha₂
  use a.toNNReal
  intros n hn₀
  have hn₁: n ∈ sn := by
    rw [hsn₀]
    exact hn₀
  constructor
  . exact h₂ n a.toNNReal ⟨hn₀, ha₃⟩
  constructor
  . refine h₈ n a.toNNReal hn₀ ?_ ?_
    . exact Real.toNNReal_pos.mpr ha₂
    . let nn : ↑sn := ⟨n, hn₁⟩
      have hn₂: f n (fb nn) = 1 - 1 / n := by
        rw [hf₁ n _ hn₀, hfb₁ nn]
        refine NNReal.coe_sub ?_
        refine div_le_self ?_ ?_
        . exact zero_le_one' NNReal
        . exact Nat.one_le_cast.mpr hn₀
      rw [← hn₂]
      refine hmo₀ n hn₀ ?_
      refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
      refine lt_of_le_of_lt ?_ ha₀
      refine hbr₃ _ ?_
      rw [hsbr]
      refine (Set.mem_image fr sb _).mpr ?_
      use (fb nn)
      rw [hfr, hsb₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self nn
  . have hn₂: n + 1 ∈ sn := by
      rw [hsn₀]
      exact Set.mem_Ici.mpr (by linarith)
    let nn : ↑sn := ⟨n + 1, hn₂⟩
    have hn₃: f (n + 1) (fc (nn)) = 1 := by
      rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
      exact rfl
    rw [← hn₃]
    refine hmo₀ (n + 1) (by linarith) ?_
    refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt ha₂)).mpr ?_
    refine lt_of_lt_of_le ha₁ ?_
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc nn)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self nn


lemma imo_1985_p6_exists_2
  (f : ℕ → NNReal → ℝ)
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (a : ℝ)
  (ha₀ : br < a)
  (ha₁ : a < cr)
  (ha₂ : 0 < a)
  (ha₃ : 0 < a.toNNReal):
   ∃ x, ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1 := by
  use a.toNNReal
  intros n hn₀
  have hn₁: n ∈ sn := by
    rw [hsn₀]
    exact hn₀
  constructor
  . exact h₂ n a.toNNReal ⟨hn₀, ha₃⟩
  constructor
  . refine h₈ n a.toNNReal hn₀ ?_ ?_
    . exact Real.toNNReal_pos.mpr ha₂
    . let nn : ↑sn := ⟨n, hn₁⟩
      have hn₂: f n (fb nn) = 1 - 1 / n := by
        rw [hf₁ n _ hn₀, hfb₁ nn]
        refine NNReal.coe_sub ?_
        refine div_le_self ?_ ?_
        . exact zero_le_one' NNReal
        . exact Nat.one_le_cast.mpr hn₀
      rw [← hn₂]
      refine hmo₀ n hn₀ ?_
      refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
      refine lt_of_le_of_lt ?_ ha₀
      refine hbr₃ _ ?_
      rw [hsbr]
      refine (Set.mem_image fr sb _).mpr ?_
      use (fb nn)
      rw [hfr, hsb₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self nn
  . have hn₂: n + 1 ∈ sn := by
      rw [hsn₀]
      exact Set.mem_Ici.mpr (by linarith)
    let nn : ↑sn := ⟨n + 1, hn₂⟩
    have hn₃: f (n + 1) (fc (nn)) = 1 := by
      rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
      exact rfl
    rw [← hn₃]
    refine hmo₀ (n + 1) (by linarith) ?_
    refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt ha₂)).mpr ?_
    refine lt_of_lt_of_le ha₁ ?_
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc nn)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self nn

lemma imo_1985_p6_exists_3
  (f : ℕ → NNReal → ℝ)
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (a : ℝ)
  (ha₀ : br < a)
  (ha₁ : a < cr)
  (ha₂ : 0 < a)
  (ha₃ : 0 < a.toNNReal)
  (n : ℕ)
  (hn₀ : 0 < n):
   0 < f n a.toNNReal ∧ f n a.toNNReal < f (n + 1) a.toNNReal ∧ f (n + 1) a.toNNReal < 1 := by
  have hn₁: n ∈ sn := by
    rw [hsn₀]
    exact hn₀
  constructor
  . exact h₂ n a.toNNReal ⟨hn₀, ha₃⟩
  constructor
  . refine h₈ n a.toNNReal hn₀ ?_ ?_
    . exact Real.toNNReal_pos.mpr ha₂
    . let nn : ↑sn := ⟨n, hn₁⟩
      have hn₂: f n (fb nn) = 1 - 1 / n := by
        rw [hf₁ n _ hn₀, hfb₁ nn]
        refine NNReal.coe_sub ?_
        refine div_le_self ?_ ?_
        . exact zero_le_one' NNReal
        . exact Nat.one_le_cast.mpr hn₀
      rw [← hn₂]
      refine hmo₀ n hn₀ ?_
      refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
      refine lt_of_le_of_lt ?_ ha₀
      refine hbr₃ _ ?_
      rw [hsbr]
      refine (Set.mem_image fr sb _).mpr ?_
      use (fb nn)
      rw [hfr, hsb₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self nn
  . have hn₂: n + 1 ∈ sn := by
      rw [hsn₀]
      exact Set.mem_Ici.mpr (by linarith)
    let nn : ↑sn := ⟨n + 1, hn₂⟩
    have hn₃: f (n + 1) (fc (nn)) = 1 := by
      rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
      exact rfl
    rw [← hn₃]
    refine hmo₀ (n + 1) (by linarith) ?_
    refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt ha₂)).mpr ?_
    refine lt_of_lt_of_le ha₁ ?_
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc nn)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self nn

lemma imo_1985_p6_exists_4
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (a : ℝ)
  (ha₀ : br < a)
  (ha₁ : a < cr)
  (ha₂ : 0 < a)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn):
   f n a.toNNReal < f (n + 1) a.toNNReal ∧ f (n + 1) a.toNNReal < 1 := by
  constructor
  . refine h₈ n a.toNNReal hn₀ ?_ ?_
    . exact Real.toNNReal_pos.mpr ha₂
    . let nn : ↑sn := ⟨n, hn₁⟩
      have hn₂: f n (fb nn) = 1 - 1 / n := by
        rw [hf₁ n _ hn₀, hfb₁ nn]
        refine NNReal.coe_sub ?_
        refine div_le_self ?_ ?_
        . exact zero_le_one' NNReal
        . exact Nat.one_le_cast.mpr hn₀
      rw [← hn₂]
      refine hmo₀ n hn₀ ?_
      refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
      refine lt_of_le_of_lt ?_ ha₀
      refine hbr₃ _ ?_
      rw [hsbr]
      refine (Set.mem_image fr sb _).mpr ?_
      use (fb nn)
      rw [hfr, hsb₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self nn
  . have hn₂: n + 1 ∈ sn := by
      rw [hsn₀]
      exact Set.mem_Ici.mpr (by linarith)
    let nn : ↑sn := ⟨n + 1, hn₂⟩
    have hn₃: f (n + 1) (fc (nn)) = 1 := by
      rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
      exact rfl
    rw [← hn₃]
    refine hmo₀ (n + 1) (by linarith) ?_
    refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt ha₂)).mpr ?_
    refine lt_of_lt_of_le ha₁ ?_
    refine hcr₃ _ ?_
    rw [hscr]
    refine (Set.mem_image fr sc _).mpr ?_
    use (fc nn)
    rw [hfr, hsc₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self nn


lemma imo_1985_p6_exists_5
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (a : ℝ)
  (ha₀ : br < a)
  (ha₂ : 0 < a)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn):
   f n a.toNNReal < f (n + 1) a.toNNReal := by
  refine h₈ n a.toNNReal hn₀ ?_ ?_
  . exact Real.toNNReal_pos.mpr ha₂
  . let nn : ↑sn := ⟨n, hn₁⟩
    have hn₂: f n (fb nn) = 1 - 1 / n := by
      rw [hf₁ n _ hn₀, hfb₁ nn]
      refine NNReal.coe_sub ?_
      refine div_le_self ?_ ?_
      . exact zero_le_one' NNReal
      . exact Nat.one_le_cast.mpr hn₀
    rw [← hn₂]
    refine hmo₀ n hn₀ ?_
    refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
    refine lt_of_le_of_lt ?_ ha₀
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    use (fb nn)
    rw [hfr, hsb₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self nn

lemma imo_1985_p6_exists_6
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (a : ℝ)
  (ha₀ : br < a)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn):
   1 - 1 / ↑n < f n a.toNNReal := by
  let nn : ↑sn := ⟨n, hn₁⟩
  have hn₂: f n (fb nn) = 1 - 1 / n := by
    rw [hf₁ n _ hn₀, hfb₁ nn]
    refine NNReal.coe_sub ?_
    refine div_le_self ?_ ?_
    . exact zero_le_one' NNReal
    . exact Nat.one_le_cast.mpr hn₀
  rw [← hn₂]
  refine hmo₀ n hn₀ ?_
  refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
  refine lt_of_le_of_lt ?_ ha₀
  refine hbr₃ _ ?_
  rw [hsbr]
  refine (Set.mem_image fr sb _).mpr ?_
  use (fb nn)
  rw [hfr, hsb₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self nn

lemma imo_1985_p6_exists_7
  (f : ℕ → NNReal → ℝ)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n, hn₁⟩):
  f n (fb nn) = 1 - 1 / ↑n := by
  rw [hf₁ n _ hn₀, hnn, hfb₁ ⟨n, hn₁⟩]
  refine NNReal.coe_sub ?_
  refine div_le_self ?_ ?_
  . exact zero_le_one' NNReal
  . exact Nat.one_le_cast.mpr hn₀

lemma imo_1985_p6_exists_8
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (a : ℝ)
  (ha₀ : br < a)
  (n : ℕ)
  (hn₀ : 0 < n)
  (nn : ↑sn):
   f n (fb nn) < f n a.toNNReal := by
  refine hmo₀ n hn₀ ?_
  refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
  refine lt_of_le_of_lt ?_ ha₀
  refine hbr₃ _ ?_
  rw [hsbr]
  refine (Set.mem_image fr sb _).mpr ?_
  use (fb nn)
  rw [hfr, hsb₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self nn

lemma imo_1985_p6_exists_9
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (a : ℝ)
  (ha₀ : br < a)
  (nn : ↑sn):
   fb nn < a.toNNReal := by
  refine Real.lt_toNNReal_iff_coe_lt.mpr ?_
  refine lt_of_le_of_lt ?_ ha₀
  refine hbr₃ _ ?_
  rw [hsbr]
  refine (Set.mem_image fr sb _).mpr ?_
  use (fb nn)
  rw [hfr, hsb₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self nn

lemma imo_1985_p6_exists_10
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (a : ℝ)
  (ha₀ : br < a)
  (nn : ↑sn):
   ↑(fb nn) < a := by
  refine lt_of_le_of_lt ?_ ha₀
  refine hbr₃ _ ?_
  rw [hsbr]
  refine (Set.mem_image fr sb _).mpr ?_
  use (fb nn)
  rw [hfr, hsb₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self nn


lemma imo_1985_p6_exists_11
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (nn : ↑sn):
   ∃ x ∈ sb, fr x = ↑(fb nn) := by
  use (fb nn)
  rw [hfr, hsb₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self nn

lemma imo_1985_p6_exists_12
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fc : ↑sn → NNReal)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (a : ℝ)
  (ha₁ : a < cr)
  (ha₂ : 0 < a)
  (n : ℕ)
  (hn₀ : 0 < n):
   f (n + 1) a.toNNReal < 1 := by
  have hn₂: n + 1 ∈ sn := by
    rw [hsn₀]
    exact Set.mem_Ici.mpr (by linarith)
  let nn : ↑sn := ⟨n + 1, hn₂⟩
  have hn₃: f (n + 1) (fc (nn)) = 1 := by
    rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
    exact rfl
  rw [← hn₃]
  refine hmo₀ (n + 1) (by linarith) ?_
  refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt ha₂)).mpr ?_
  refine lt_of_lt_of_le ha₁ ?_
  refine hcr₃ _ ?_
  rw [hscr]
  refine (Set.mem_image fr sc _).mpr ?_
  use (fc nn)
  rw [hfr, hsc₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self nn

lemma imo_1985_p6_exists_13
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (a : ℝ)
  (ha₁ : a < cr)
  (ha₂ : 0 < a)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₂ : n + 1 ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n + 1, hn₂⟩):
  f (n + 1) a.toNNReal < 1 := by
  have hn₃: f (n + 1) (fc (nn)) = 1 := by
    rw [hf₁ (n + 1) _ (by linarith), hnn, hfc₁ ⟨n + 1, hn₂⟩]
    exact rfl
  rw [← hn₃]
  refine hmo₀ (n + 1) (by linarith) ?_
  refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt ha₂)).mpr ?_
  refine lt_of_lt_of_le ha₁ ?_
  refine hcr₃ _ ?_
  rw [hscr]
  refine (Set.mem_image fr sc _).mpr ?_
  use (fc nn)
  rw [hfr, hsc₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self nn


lemma imo_1985_p6_exists_14
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (a : ℝ)
  (ha₁ : a < cr)
  (ha₂ : 0 < a)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₂ : n + 1 ∈ sn)
  (nn : ↑sn := ⟨n + 1, hn₂⟩):
   f (n + 1) a.toNNReal < f (n + 1) (fc nn) := by
  refine hmo₀ (n + 1) (by linarith) ?_
  refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt ha₂)).mpr ?_
  refine lt_of_lt_of_le ha₁ ?_
  refine hcr₃ _ ?_
  rw [hscr]
  refine (Set.mem_image fr sc _).mpr ?_
  use (fc nn)
  rw [hfr, hsc₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self nn


lemma imo_1985_p6_exists_15
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (a : ℝ)
  (ha₁ : a < cr)
  (ha₂ : 0 < a)
  (n : ℕ)
  (hn₂ : n + 1 ∈ sn)
  (nn : ↑sn := ⟨n + 1, hn₂⟩):
   a.toNNReal < fc nn := by
  refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt ha₂)).mpr ?_
  refine lt_of_lt_of_le ha₁ ?_
  refine hcr₃ _ ?_
  rw [hscr]
  refine (Set.mem_image fr sc _).mpr ?_
  use (fc nn)
  rw [hfr, hsc₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self nn


lemma imo_1985_p6_exists_16
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (scr : Set ℝ)
  (hscr : scr = fr '' sc)
  (cr : ℝ)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (n : ℕ)
  (hn₂ : n + 1 ∈ sn)
  (nn : ↑sn := ⟨n + 1, hn₂⟩):
   cr ≤ ↑(fc nn) := by
  refine hcr₃ _ ?_
  rw [hscr]
  refine (Set.mem_image fr sc _).mpr ?_
  use (fc nn)
  rw [hfr, hsc₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self nn


lemma imo_1985_p6_exists_17
  (sn : Set ℕ)
  (fc : ↑sn → NNReal)
  (sc : Set NNReal)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (n : ℕ)
  (hn₂ : n + 1 ∈ sn)
  (nn : ↑sn := ⟨n + 1, hn₂⟩):
   ∃ x ∈ sc, fr x = ↑(fc nn) := by
  use (fc nn)
  rw [hfr, hsc₀]
  refine ⟨?_, rfl⟩
  exact Set.mem_range_self nn

lemma imo_1985_p6_exists_18
  (f : ℕ → NNReal → ℝ)
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₁ : 0 < br)
  (hu₅ : br ≤ cr)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (hu₆ : br = cr):
   ∃ x, ∀ (n : ℕ), 0 < n → 0 < f n x ∧ f n x < f (n + 1) x ∧ f (n + 1) x < 1 := by
  use br.toNNReal
  intros n hn₀
  have hn₁: n ∈ sn := by
    rw [hsn₀]
    exact hn₀
  constructor
  . refine h₂ n br.toNNReal ⟨hn₀, ?_⟩
    exact Real.toNNReal_pos.mpr hbr₁
  constructor
  . refine h₈ n br.toNNReal hn₀ ?_ ?_
    . exact Real.toNNReal_pos.mpr hbr₁
    . let nn : ↑sn := ⟨n, hn₁⟩
      have hn₂: fb nn < br := by
        by_contra! hc₀
        have hbr₅: (fb nn) = br := by
          refine eq_of_le_of_le ?_ hc₀
          refine hbr₃ _ ?_
          rw [hsbr]
          refine (Set.mem_image fr sb _).mpr ?_
          use (fb nn)
          rw [hfr, hsb₀]
          constructor
          . exact Set.mem_range_self nn
          . exact rfl
        have hn₂: n + 1 ∈ sn := by
          rw [hsn₀]
          refine Set.mem_Ici.mpr ?_
          exact Nat.le_add_right_of_le hn₀
        let ns : ↑sn := ⟨n + 1, hn₂⟩
        have hc₁: fb nn < fb ns := by
          refine hfb₃ ?_
          refine Subtype.mk_lt_mk.mpr ?_
          exact lt_add_one n
        have hbr₆: fb ns ≤ fb nn := by
          refine NNReal.coe_le_coe.mp ?_
          rw [hbr₅]
          refine hbr₃ _ ?_
          rw [hsbr]
          refine (Set.mem_image fr sb _).mpr ?_
          use (fb ns)
          rw [hfr, hsb₀]
          refine ⟨?_, rfl⟩
          exact Set.mem_range_self ns
        refine (lt_self_iff_false (fb nn)).mp ?_
        exact lt_of_lt_of_le hc₁ hbr₆
      have hn₃: f n (fb nn) = 1 - 1 / n := by
        rw [hf₁ n _ hn₀, hfb₁ nn]
        refine NNReal.coe_sub ?_
        refine div_le_self ?_ ?_
        . exact zero_le_one' NNReal
        . exact Nat.one_le_cast.mpr hn₀
      rw [← hn₃]
      refine hmo₀ n hn₀ ?_
      exact Real.lt_toNNReal_iff_coe_lt.mpr hn₂
  . have hn₂: n + 1 ∈ sn := by
      rw [hsn₀]
      exact Set.mem_Ici.mpr (by linarith)
    let nn : ↑sn := ⟨n + 1, hn₂⟩
    have hcr₁: 0 < cr := by exact gt_of_ge_of_gt hu₅ hbr₁
    have hn₃: f (n + 1) (fc (nn)) = 1 := by
      rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
      exact rfl
    rw [← hn₃, hu₆]
    refine hmo₀ (n + 1) (by linarith) ?_
    refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt hcr₁)).mpr ?_
    by_contra! hc₀
    have hc₁: fc nn = cr := by
      refine eq_of_le_of_le hc₀ ?_
      refine hcr₃ _ ?_
      rw [hscr]
      refine (Set.mem_image fr sc _).mpr ?_
      use (fc nn)
      rw [hfr, hsc₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self nn
    have hn₄: n + 2 ∈ sn := by
      rw [hsn₀]
      refine Set.mem_Ici.mpr ?_
      exact Nat.le_add_right_of_le hn₀
    let ns : ↑sn := ⟨n + 2, hn₄⟩
    have hn₅: fc ns < fc nn := by
      refine hfc₃ ?_
      refine Subtype.mk_lt_mk.mpr ?_
      exact Nat.lt_add_one (n + 1)
    have hc₂: fc nn ≤ fc ns := by
      refine NNReal.coe_le_coe.mp ?_
      rw [hc₁]
      refine hcr₃ _ ?_
      rw [hscr]
      refine (Set.mem_image fr sc _).mpr ?_
      use (fc ns)
      rw [hfr, hsc₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self ns
    refine (lt_self_iff_false (fc ns)).mp ?_
    exact lt_of_lt_of_le hn₅ hc₂


lemma imo_1985_p6_exists_19
  (f : ℕ → NNReal → ℝ)
  (h₂ : ∀ (n : ℕ) (x : NNReal), 0 < n ∧ 0 < x → 0 < f n x)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₁ : 0 < br)
  (hu₅ : br ≤ cr)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (hu₆ : br = cr)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn):
   0 < f n br.toNNReal ∧ f n br.toNNReal < f (n + 1) br.toNNReal ∧ f (n + 1) br.toNNReal < 1 := by
  constructor
  . refine h₂ n br.toNNReal ⟨hn₀, ?_⟩
    exact Real.toNNReal_pos.mpr hbr₁
  constructor
  . refine h₈ n br.toNNReal hn₀ ?_ ?_
    . exact Real.toNNReal_pos.mpr hbr₁
    . let nn : ↑sn := ⟨n, hn₁⟩
      have hn₂: fb nn < br := by
        by_contra! hc₀
        have hbr₅: (fb nn) = br := by
          refine eq_of_le_of_le ?_ hc₀
          refine hbr₃ _ ?_
          rw [hsbr]
          refine (Set.mem_image fr sb _).mpr ?_
          use (fb nn)
          rw [hfr, hsb₀]
          constructor
          . exact Set.mem_range_self nn
          . exact rfl
        have hn₂: n + 1 ∈ sn := by
          rw [hsn₀]
          refine Set.mem_Ici.mpr ?_
          exact Nat.le_add_right_of_le hn₀
        let ns : ↑sn := ⟨n + 1, hn₂⟩
        have hc₁: fb nn < fb ns := by
          refine hfb₃ ?_
          refine Subtype.mk_lt_mk.mpr ?_
          exact lt_add_one n
        have hbr₆: fb ns ≤ fb nn := by
          refine NNReal.coe_le_coe.mp ?_
          rw [hbr₅]
          refine hbr₃ _ ?_
          rw [hsbr]
          refine (Set.mem_image fr sb _).mpr ?_
          use (fb ns)
          rw [hfr, hsb₀]
          refine ⟨?_, rfl⟩
          exact Set.mem_range_self ns
        refine (lt_self_iff_false (fb nn)).mp ?_
        exact lt_of_lt_of_le hc₁ hbr₆
      have hn₃: f n (fb nn) = 1 - 1 / n := by
        rw [hf₁ n _ hn₀, hfb₁ nn]
        refine NNReal.coe_sub ?_
        refine div_le_self ?_ ?_
        . exact zero_le_one' NNReal
        . exact Nat.one_le_cast.mpr hn₀
      rw [← hn₃]
      refine hmo₀ n hn₀ ?_
      exact Real.lt_toNNReal_iff_coe_lt.mpr hn₂
  . have hn₂: n + 1 ∈ sn := by
      rw [hsn₀]
      exact Set.mem_Ici.mpr (by linarith)
    let nn : ↑sn := ⟨n + 1, hn₂⟩
    have hcr₁: 0 < cr := by exact gt_of_ge_of_gt hu₅ hbr₁
    have hn₃: f (n + 1) (fc (nn)) = 1 := by
      rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
      exact rfl
    rw [← hn₃, hu₆]
    refine hmo₀ (n + 1) (by linarith) ?_
    refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt hcr₁)).mpr ?_
    by_contra! hc₀
    have hc₁: fc nn = cr := by
      refine eq_of_le_of_le hc₀ ?_
      refine hcr₃ _ ?_
      rw [hscr]
      refine (Set.mem_image fr sc _).mpr ?_
      use (fc nn)
      rw [hfr, hsc₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self nn
    have hn₄: n + 2 ∈ sn := by
      rw [hsn₀]
      refine Set.mem_Ici.mpr ?_
      exact Nat.le_add_right_of_le hn₀
    let ns : ↑sn := ⟨n + 2, hn₄⟩
    have hn₅: fc ns < fc nn := by
      refine hfc₃ ?_
      refine Subtype.mk_lt_mk.mpr ?_
      exact Nat.lt_add_one (n + 1)
    have hc₂: fc nn ≤ fc ns := by
      refine NNReal.coe_le_coe.mp ?_
      rw [hc₁]
      refine hcr₃ _ ?_
      rw [hscr]
      refine (Set.mem_image fr sc _).mpr ?_
      use (fc ns)
      rw [hfr, hsc₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self ns
    refine (lt_self_iff_false (fc ns)).mp ?_
    exact lt_of_lt_of_le hn₅ hc₂

lemma imo_1985_p6_exists_20
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb fc : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfc₁ : ∀ (n : ↑sn), f₀ (↑n) (fc n) = 1)
  (hfb₃ : StrictMono fb)
  (hfc₃ : StrictAnti fc)
  (sb sc : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (hsc₀ : sc = Set.range fc)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr scr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (hscr : scr = fr '' sc)
  (br cr : ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₁ : 0 < br)
  (hu₅ : br ≤ cr)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (hcr₃ : ∀ x ∈ scr, cr ≤ x)
  (hu₆ : br = cr)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn):
   f n br.toNNReal < f (n + 1) br.toNNReal ∧ f (n + 1) br.toNNReal < 1 := by
  constructor
  . refine h₈ n br.toNNReal hn₀ ?_ ?_
    . exact Real.toNNReal_pos.mpr hbr₁
    . let nn : ↑sn := ⟨n, hn₁⟩
      have hn₂: fb nn < br := by
        by_contra! hc₀
        have hbr₅: (fb nn) = br := by
          refine eq_of_le_of_le ?_ hc₀
          refine hbr₃ _ ?_
          rw [hsbr]
          refine (Set.mem_image fr sb _).mpr ?_
          use (fb nn)
          rw [hfr, hsb₀]
          constructor
          . exact Set.mem_range_self nn
          . exact rfl
        have hn₂: n + 1 ∈ sn := by
          rw [hsn₀]
          refine Set.mem_Ici.mpr ?_
          exact Nat.le_add_right_of_le hn₀
        let ns : ↑sn := ⟨n + 1, hn₂⟩
        have hc₁: fb nn < fb ns := by
          refine hfb₃ ?_
          refine Subtype.mk_lt_mk.mpr ?_
          exact lt_add_one n
        have hbr₆: fb ns ≤ fb nn := by
          refine NNReal.coe_le_coe.mp ?_
          rw [hbr₅]
          refine hbr₃ _ ?_
          rw [hsbr]
          refine (Set.mem_image fr sb _).mpr ?_
          use (fb ns)
          rw [hfr, hsb₀]
          refine ⟨?_, rfl⟩
          exact Set.mem_range_self ns
        refine (lt_self_iff_false (fb nn)).mp ?_
        exact lt_of_lt_of_le hc₁ hbr₆
      have hn₃: f n (fb nn) = 1 - 1 / n := by
        rw [hf₁ n _ hn₀, hfb₁ nn]
        refine NNReal.coe_sub ?_
        refine div_le_self ?_ ?_
        . exact zero_le_one' NNReal
        . exact Nat.one_le_cast.mpr hn₀
      rw [← hn₃]
      refine hmo₀ n hn₀ ?_
      exact Real.lt_toNNReal_iff_coe_lt.mpr hn₂
  . have hn₂: n + 1 ∈ sn := by
      rw [hsn₀]
      exact Set.mem_Ici.mpr (by linarith)
    let nn : ↑sn := ⟨n + 1, hn₂⟩
    have hcr₁: 0 < cr := by exact gt_of_ge_of_gt hu₅ hbr₁
    have hn₃: f (n + 1) (fc (nn)) = 1 := by
      rw [hf₁ (n + 1) _ (by linarith), hfc₁ nn]
      exact rfl
    rw [← hn₃, hu₆]
    refine hmo₀ (n + 1) (by linarith) ?_
    refine (Real.toNNReal_lt_iff_lt_coe (le_of_lt hcr₁)).mpr ?_
    by_contra! hc₀
    have hc₁: fc nn = cr := by
      refine eq_of_le_of_le hc₀ ?_
      refine hcr₃ _ ?_
      rw [hscr]
      refine (Set.mem_image fr sc _).mpr ?_
      use (fc nn)
      rw [hfr, hsc₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self nn
    have hn₄: n + 2 ∈ sn := by
      rw [hsn₀]
      refine Set.mem_Ici.mpr ?_
      exact Nat.le_add_right_of_le hn₀
    let ns : ↑sn := ⟨n + 2, hn₄⟩
    have hn₅: fc ns < fc nn := by
      refine hfc₃ ?_
      refine Subtype.mk_lt_mk.mpr ?_
      exact Nat.lt_add_one (n + 1)
    have hc₂: fc nn ≤ fc ns := by
      refine NNReal.coe_le_coe.mp ?_
      rw [hc₁]
      refine hcr₃ _ ?_
      rw [hscr]
      refine (Set.mem_image fr sc _).mpr ?_
      use (fc ns)
      rw [hfr, hsc₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self ns
    refine (lt_self_iff_false (fc ns)).mp ?_
    exact lt_of_lt_of_le hn₅ hc₂




lemma imo_1985_p6_exists_21
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfb₃ : StrictMono fb)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (h₈ : ∀ (n : ℕ) (x : NNReal), 0 < n → 0 < x → 1 - 1 / ↑n < f n x → f n x < f (n + 1) x)
  (hbr₁ : 0 < br)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn):
   f n br.toNNReal < f (n + 1) br.toNNReal := by
  refine h₈ n br.toNNReal hn₀ ?_ ?_
  . exact Real.toNNReal_pos.mpr hbr₁
  . let nn : ↑sn := ⟨n, hn₁⟩
    have hn₂: fb nn < br := by
      by_contra! hc₀
      have hbr₅: (fb nn) = br := by
        refine eq_of_le_of_le ?_ hc₀
        refine hbr₃ _ ?_
        rw [hsbr]
        refine (Set.mem_image fr sb _).mpr ?_
        use (fb nn)
        rw [hfr, hsb₀]
        constructor
        . exact Set.mem_range_self nn
        . exact rfl
      have hn₂: n + 1 ∈ sn := by
        rw [hsn₀]
        refine Set.mem_Ici.mpr ?_
        exact Nat.le_add_right_of_le hn₀
      let ns : ↑sn := ⟨n + 1, hn₂⟩
      have hc₁: fb nn < fb ns := by
        refine hfb₃ ?_
        refine Subtype.mk_lt_mk.mpr ?_
        exact lt_add_one n
      have hbr₆: fb ns ≤ fb nn := by
        refine NNReal.coe_le_coe.mp ?_
        rw [hbr₅]
        refine hbr₃ _ ?_
        rw [hsbr]
        refine (Set.mem_image fr sb _).mpr ?_
        use (fb ns)
        rw [hfr, hsb₀]
        refine ⟨?_, rfl⟩
        exact Set.mem_range_self ns
      refine (lt_self_iff_false (fb nn)).mp ?_
      exact lt_of_lt_of_le hc₁ hbr₆
    have hn₃: f n (fb nn) = 1 - 1 / n := by
      rw [hf₁ n _ hn₀, hfb₁ nn]
      refine NNReal.coe_sub ?_
      refine div_le_self ?_ ?_
      . exact zero_le_one' NNReal
      . exact Nat.one_le_cast.mpr hn₀
    rw [← hn₃]
    refine hmo₀ n hn₀ ?_
    exact Real.lt_toNNReal_iff_coe_lt.mpr hn₂


lemma imo_1985_p6_exists_22
  (f : ℕ → NNReal → ℝ)
  (hmo₀ : ∀ (n : ℕ), 0 < n → StrictMono (f n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb : ↑sn → NNReal)
  (hfb₁ : ∀ (n : ↑sn), f₀ (↑n) (fb n) = 1 - 1 / ↑↑n)
  (hfb₃ : StrictMono fb)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n, hn₁⟩):
   1 - 1 / ↑n < f n br.toNNReal := by
  have hn₂: fb nn < br := by
    by_contra! hc₀
    have hbr₅: (fb nn) = br := by
      refine eq_of_le_of_le ?_ hc₀
      refine hbr₃ _ ?_
      rw [hsbr]
      refine (Set.mem_image fr sb _).mpr ?_
      use (fb nn)
      rw [hfr, hsb₀]
      constructor
      . exact Set.mem_range_self nn
      . exact rfl
    have hn₂: n + 1 ∈ sn := by
      rw [hsn₀]
      refine Set.mem_Ici.mpr ?_
      exact Nat.le_add_right_of_le hn₀
    let ns : ↑sn := ⟨n + 1, hn₂⟩
    have hc₁: fb nn < fb ns := by
      refine hfb₃ ?_
      refine Subtype.mk_lt_mk.mpr ?_
      rw [hnn]
      exact lt_add_one n
    have hbr₆: fb ns ≤ fb nn := by
      refine NNReal.coe_le_coe.mp ?_
      rw [hbr₅]
      refine hbr₃ _ ?_
      rw [hsbr]
      refine (Set.mem_image fr sb _).mpr ?_
      use (fb ns)
      rw [hfr, hsb₀]
      refine ⟨?_, rfl⟩
      exact Set.mem_range_self ns
    refine (lt_self_iff_false (fb nn)).mp ?_
    exact lt_of_lt_of_le hc₁ hbr₆
  have hn₃: f n (fb nn) = 1 - 1 / n := by
    rw [hf₁ n _ hn₀, hnn, hfb₁ ⟨n, hn₁⟩]
    refine NNReal.coe_sub ?_
    refine div_le_self ?_ ?_
    . exact zero_le_one' NNReal
    . exact Nat.one_le_cast.mpr hn₀
  rw [← hn₃]
  refine hmo₀ n hn₀ ?_
  exact Real.lt_toNNReal_iff_coe_lt.mpr hn₂


lemma imo_1985_p6_exists_23
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb : ↑sn → NNReal)
  (hfb₃ : StrictMono fb)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n, hn₁⟩):
   ↑(fb nn) < br := by
  by_contra! hc₀
  have hbr₅: (fb nn) = br := by
    refine eq_of_le_of_le ?_ hc₀
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    use (fb nn)
    rw [hfr, hsb₀]
    constructor
    . exact Set.mem_range_self nn
    . exact rfl
  have hn₂: n + 1 ∈ sn := by
    rw [hsn₀]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right_of_le hn₀
  let ns : ↑sn := ⟨n + 1, hn₂⟩
  have hc₁: fb nn < fb ns := by
    refine hfb₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hnn]
    exact lt_add_one n
  have hbr₆: fb ns ≤ fb nn := by
    refine NNReal.coe_le_coe.mp ?_
    rw [hbr₅]
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    use (fb ns)
    rw [hfr, hsb₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self ns
  refine (lt_self_iff_false (fb nn)).mp ?_
  exact lt_of_lt_of_le hc₁ hbr₆

lemma imo_1985_p6_exists_24
  (sn : Set ℕ)
  (hsn₀ : sn = Set.Ici 1)
  (fb : ↑sn → NNReal)
  (hfb₃ : StrictMono fb)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (n : ℕ)
  (hn₀ : 0 < n)
  (hn₁ : n ∈ sn)
  (nn : ↑sn)
  (hnn : nn = ⟨n, hn₁⟩)
  (hc₀ : br ≤ ↑(fb nn)):
   False := by
  have hbr₅: (fb nn) = br := by
    refine eq_of_le_of_le ?_ hc₀
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    use (fb nn)
    rw [hfr, hsb₀]
    constructor
    . exact Set.mem_range_self nn
    . exact rfl
  have hn₂: n + 1 ∈ sn := by
    rw [hsn₀]
    refine Set.mem_Ici.mpr ?_
    exact Nat.le_add_right_of_le hn₀
  let ns : ↑sn := ⟨n + 1, hn₂⟩
  have hc₁: fb nn < fb ns := by
    refine hfb₃ ?_
    refine Subtype.mk_lt_mk.mpr ?_
    rw [hnn]
    exact lt_add_one n
  have hbr₆: fb ns ≤ fb nn := by
    refine NNReal.coe_le_coe.mp ?_
    rw [hbr₅]
    refine hbr₃ _ ?_
    rw [hsbr]
    refine (Set.mem_image fr sb _).mpr ?_
    use (fb ns)
    rw [hfr, hsb₀]
    refine ⟨?_, rfl⟩
    exact Set.mem_range_self ns
  refine (lt_self_iff_false (fb nn)).mp ?_
  exact lt_of_lt_of_le hc₁ hbr₆

lemma imo_1985_p6_exists_25
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (nn : ↑sn)
  (hc₀ : br ≤ ↑(fb nn)):
   ↑(fb nn) = br := by
  refine eq_of_le_of_le ?_ hc₀
  refine hbr₃ _ ?_
  rw [hsbr]
  refine (Set.mem_image fr sb _).mpr ?_
  use (fb nn)
  rw [hfr, hsb₀]
  constructor
  . exact Set.mem_range_self nn
  . exact rfl

lemma imo_1985_p6_exists_26
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (sb : Set NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x ↦ ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₃ : ∀ x ∈ sbr, x ≤ br)
  (nn : ↑sn):
   ↑(fb nn) ≤ br := by
  refine hbr₃ _ ?_
  rw [hsbr]
  refine (Set.mem_image fr sb _).mpr ?_
  use (fb nn)
  rw [hfr, hsb₀]
  constructor
  . exact Set.mem_range_self nn
  . exact rfl


lemma imo_1985_p6_8_14
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₁ : 1 < n.1)
  (g₀ : ↑↑n ≠ (0:NNReal)):
   (↑↑n - 1) / ↑↑n ≠ (0:NNReal) := by
  refine div_ne_zero ?_ g₀
  norm_cast
  exact Nat.sub_ne_zero_iff_lt.mpr hn₁

lemma imo_1985_p6_8_15
  (f : ℕ → NNReal → ℝ)
  (hmo₁ : ∀ (n : ℕ), 0 < n → Function.Injective (f n))
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (z : NNReal)
  (hz₁ : (f (↑n) z).toNNReal = 1 - 1 / ↑↑n)
  (hz₂ : 1 - 1 / ↑↑n ≠ (0:NNReal)):
   f (↑n) z = 1 - 1 / ↑↑n := by
  apply (Real.toNNReal_eq_iff_eq_coe hz₂).mp at hz₁
  rw [hz₁]
  exact Eq.symm ((fun {r} {p:NNReal} hp => (Real.toNNReal_eq_iff_eq_coe hp).mp) hz₂ (hmo₁ n hn₀ rfl))


lemma imo_1985_p6_8_16
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (z : NNReal)
  (hz₁ : (f (↑n) z).toNNReal = 1 - 1 / ↑↑n)
  (hn₁ : ¬ (1:ℕ) < ↑n):
  f (↑n) z = 1 - 1 / ↑↑n := by
  have hn₂: n.1 = 1 := by linarith
  rw [hn₂, h₀] at hz₁
  simp at hz₁
  rw [hn₂, h₀, hz₁]
  simp

lemma imo_1985_p6_8_17
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (sn : Set ℕ)
  (n : ↑sn)
  (z : NNReal)
  (hz₁ : (↑z:ℝ).toNNReal = 1 - 1 / ↑1)
  (hn₂ : ↑n.1 = 1):
   f (↑n) z = 1 - 1 / ↑↑n := by
  simp at hz₁
  rw [hn₂, h₀, hz₁]
  simp



lemma imo_1985_p6_8_18
  (f : ℕ → NNReal → ℝ)
  (f₀ : ℕ → NNReal → NNReal)
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (z : NNReal)
  (hc₁ : 1 ≤ f (↑n) z)
  (hz₁ : f₀ (↑n) z = 1 - 1 / ↑↑n)
  (hz₃ : f (↑n) z = 1 - 1 / ↑↑n):
   False := by
  rw [hz₃] at hc₁
  have hz₄: 0 < 1 / (n:ℝ) := by
    refine div_pos (by linarith) ?_
    exact Nat.cast_pos'.mpr hn₀
  linarith

lemma imo_1985_p6_8_19
  (f : ℕ → NNReal → ℝ)
  (f₀ : ℕ → NNReal → NNReal)
  (sn : Set ℕ)
  (n : ↑sn)
  (hn₀ : 0 < n.1)
  (z : NNReal)
  (hc₁ : 1 ≤ f (↑n) z)
  (hz₁ : f₀ (↑n) z = 1 - 1 / ↑↑n)
  (hz₃ : f (↑n) z = 1 - 1 / ↑↑n):
   False := by
  rw [hz₃] at hc₁
  have hz₄: 0 < 1 / (n:ℝ) := by
    refine div_pos (by linarith) ?_
    exact Nat.cast_pos'.mpr hn₀
  linarith


lemma imo_1985_p6_9_1
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hf₅ : ∀ (x : NNReal), fi 1 x = x)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (fb : ℕ → NNReal)
  (hfb₀ : fb = fun n => fi n (1 - 1 / ↑n))
  (m : ℕ)
  (hm₀ : 1 < m):
   fb (Order.pred m) < fb m := by
  rw [hfb₀]
  refine Nat.le_induction ?_ ?_ m hm₀
  . have g₁: fi 1 0 = 0 := by exact hf₅ 0
    have g₂: (2:NNReal).IsConjExponent (2:NNReal) := by
      refine (NNReal.isConjExponent_iff_eq_conjExponent ?_).mpr ?_
      . exact one_lt_two
      . norm_cast
        simp
    simp
    norm_cast
    rw [g₁, NNReal.IsConjExponent.one_sub_inv g₂]
    let x := fi 2 2⁻¹
    have hx₀: x = fi 2 2⁻¹ := by rfl
    have hx₁: f₀ 2 x = 2⁻¹ := by
      rw [hx₀]
      have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
      exact g₃ 2⁻¹
    rw [← hx₀]
    contrapose! hx₁
    have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
    have hc₃: f₀ 2 x = 0 := by
      rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
      norm_cast
      rw [zero_mul]
      exact Real.toNNReal_zero
    rw [hc₃]
    exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)
  . simp
    intros n hn₀ _
    let i := fi n (1 - (↑n)⁻¹)
    let j := fi (n + 1) (1 - ((↑n:NNReal) + 1)⁻¹)
    have hi₀: i = fi n (1 - (↑n)⁻¹) := by rfl
    have hj₀: j = fi (n + 1) (1 - ((↑n:NNReal) + 1)⁻¹) := by rfl
    have hi₁: f₀ n i = (1 - (↑n)⁻¹) := by exact (hf₇ n i (1 - (↑n:NNReal)⁻¹) (by linarith)).mpr hi₀.symm
    have hj₁: f₀ (n + 1) j = (1 - ((↑n:NNReal) + 1)⁻¹) := by
      exact (hf₇ (n + 1) j _ (by linarith)).mpr hj₀.symm
    have hj₂: (1 - ((↑n:NNReal) + 1)⁻¹) = (1 - ((n:ℝ) + 1)⁻¹).toNNReal := by
      exact rfl
    have hn₂: f₀ (n + 1) i < f₀ (n + 1) j := by
      rw [hj₁, hj₂, hf₂ (n + 1) _ (by linarith), h₁ n i (by linarith)]
      rw [hf₁ n i (by linarith), hi₁]
      refine (Real.toNNReal_lt_toNNReal_iff ?_).mpr ?_
      . refine sub_pos.mpr ?_
        refine inv_lt_one_of_one_lt₀ ?_
        norm_cast
        exact Nat.lt_add_right 1 hn₀
      . have g₀: (↑n:NNReal)⁻¹ ≤ 1 := by exact Nat.cast_inv_le_one n
        rw [NNReal.coe_sub g₀, NNReal.coe_inv]
        simp
        refine inv_strictAnti₀ ?_ ?_
        . norm_cast
          exact Nat.zero_lt_of_lt hn₀
        . norm_cast
          exact lt_add_one n
    refine (StrictMono.lt_iff_lt ?_).mp hn₂
    exact hmo₂ (n + 1) (by linarith)


lemma imo_1985_p6_9_2
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hf₅ : ∀ (x : NNReal), fi 1 x = x)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (m : ℕ)
  (hm₀ : 1 < m):
   (fun n => fi n (1 - 1 / ↑n)) (Order.pred m) < (fun n => fi n (1 - 1 / ↑n)) m := by
  refine Nat.le_induction ?_ ?_ m hm₀
  . have g₁: fi 1 0 = 0 := by exact hf₅ 0
    have g₂: (2:NNReal).IsConjExponent (2:NNReal) := by
      refine (NNReal.isConjExponent_iff_eq_conjExponent ?_).mpr ?_
      . exact one_lt_two
      . norm_cast
        simp
    simp
    norm_cast
    rw [g₁, NNReal.IsConjExponent.one_sub_inv g₂]
    let x := fi 2 2⁻¹
    have hx₀: x = fi 2 2⁻¹ := by rfl
    have hx₁: f₀ 2 x = 2⁻¹ := by
      rw [hx₀]
      have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
      exact g₃ 2⁻¹
    rw [← hx₀]
    contrapose! hx₁
    have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
    have hc₃: f₀ 2 x = 0 := by
      rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
      norm_cast
      rw [zero_mul]
      exact Real.toNNReal_zero
    rw [hc₃]
    exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)
  . simp
    intros n hn₀ _
    let i := fi n (1 - (↑n)⁻¹)
    let j := fi (n + 1) (1 - ((↑n:NNReal) + 1)⁻¹)
    have hi₀: i = fi n (1 - (↑n)⁻¹) := by rfl
    have hj₀: j = fi (n + 1) (1 - ((↑n:NNReal) + 1)⁻¹) := by rfl
    have hi₁: f₀ n i = (1 - (↑n)⁻¹) := by exact (hf₇ n i (1 - (↑n:NNReal)⁻¹) (by linarith)).mpr hi₀.symm
    have hj₁: f₀ (n + 1) j = (1 - ((↑n:NNReal) + 1)⁻¹) := by
      exact (hf₇ (n + 1) j _ (by linarith)).mpr hj₀.symm
    have hj₂: (1 - ((↑n:NNReal) + 1)⁻¹) = (1 - ((n:ℝ) + 1)⁻¹).toNNReal := by
      exact rfl
    have hn₂: f₀ (n + 1) i < f₀ (n + 1) j := by
      rw [hj₁, hj₂, hf₂ (n + 1) _ (by linarith), h₁ n i (by linarith)]
      rw [hf₁ n i (by linarith), hi₁]
      refine (Real.toNNReal_lt_toNNReal_iff ?_).mpr ?_
      . refine sub_pos.mpr ?_
        refine inv_lt_one_of_one_lt₀ ?_
        norm_cast
        exact Nat.lt_add_right 1 hn₀
      . have g₀: (↑n:NNReal)⁻¹ ≤ 1 := by exact Nat.cast_inv_le_one n
        rw [NNReal.coe_sub g₀, NNReal.coe_inv]
        simp
        refine inv_strictAnti₀ ?_ ?_
        . norm_cast
          exact Nat.zero_lt_of_lt hn₀
        . norm_cast
          exact lt_add_one n
    refine (StrictMono.lt_iff_lt ?_).mp hn₂
    exact hmo₂ (n + 1) (by linarith)

lemma imo_1985_p6_9_3
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hf₅ : ∀ (x : NNReal), fi 1 x = x)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n)):
   (fun n => fi n (1 - 1 / ↑n)) (Order.pred (Nat.succ 1)) < (fun n => fi n (1 - 1 / ↑n)) (Nat.succ 1) := by
  have g₁: fi 1 0 = 0 := by exact hf₅ 0
  have g₂: (2:NNReal).IsConjExponent (2:NNReal) := by
    refine (NNReal.isConjExponent_iff_eq_conjExponent ?_).mpr ?_
    . exact one_lt_two
    . norm_cast
      simp
  simp
  norm_cast
  rw [g₁, NNReal.IsConjExponent.one_sub_inv g₂]
  let x := fi 2 2⁻¹
  have hx₀: x = fi 2 2⁻¹ := by rfl
  have hx₁: f₀ 2 x = 2⁻¹ := by
    rw [hx₀]
    have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
    exact g₃ 2⁻¹
  rw [← hx₀]
  contrapose! hx₁
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)


lemma imo_1985_p6_9_4
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (g₁ : fi 1 0 = 0):
   (fun n => fi n (1 - 1 / ↑n)) (Order.pred (Nat.succ 1)) < (fun n => fi n (1 - 1 / ↑n)) (Nat.succ 1) := by
  have g₂: (2:NNReal).IsConjExponent (2:NNReal) := by
    refine (NNReal.isConjExponent_iff_eq_conjExponent ?_).mpr ?_
    . exact one_lt_two
    . norm_cast
      simp
  simp
  norm_cast
  rw [g₁, NNReal.IsConjExponent.one_sub_inv g₂]
  let x := fi 2 2⁻¹
  have hx₀: x = fi 2 2⁻¹ := by rfl
  have hx₁: f₀ 2 x = 2⁻¹ := by
    rw [hx₀]
    have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
    exact g₃ 2⁻¹
  rw [← hx₀]
  contrapose! hx₁
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)

lemma imo_1985_p6_9_5
  (fi : ℕ → NNReal → NNReal)
  (m : ℕ):
   NNReal.IsConjExponent 2 2 := by
  refine (NNReal.isConjExponent_iff_eq_conjExponent ?_).mpr ?_
  . exact one_lt_two
  . norm_cast
    simp

lemma imo_1985_p6_9_6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (g₁ : fi 1 0 = 0)
  (g₂ : NNReal.IsConjExponent 2 2):
   (fun n => fi n (1 - 1 / ↑n)) (Order.pred (Nat.succ 1)) < (fun n => fi n (1 - 1 / ↑n)) (Nat.succ 1) := by
  simp
  norm_cast
  rw [g₁, NNReal.IsConjExponent.one_sub_inv g₂]
  let x := fi 2 2⁻¹
  have hx₀: x = fi 2 2⁻¹ := by rfl
  have hx₁: f₀ 2 x = 2⁻¹ := by
    rw [hx₀]
    have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
    exact g₃ 2⁻¹
  rw [← hx₀]
  contrapose! hx₁
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)


lemma imo_1985_p6_9_7
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (g₁ : fi 1 0 = 0)
  (g₂ : NNReal.IsConjExponent 2 2):
   fi 1 0 < fi 2 (1 - 2⁻¹) := by
  rw [g₁, NNReal.IsConjExponent.one_sub_inv g₂]
  let x := fi 2 2⁻¹
  have hx₀: x = fi 2 2⁻¹ := by rfl
  have hx₁: f₀ 2 x = 2⁻¹ := by
    rw [hx₀]
    have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
    exact g₃ 2⁻¹
  rw [← hx₀]
  contrapose! hx₁
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)


lemma imo_1985_p6_9_8
  (fi : ℕ → NNReal → NNReal)
  (g₁ : fi 1 0 = 0)
  (g₂ : NNReal.IsConjExponent 2 2)
  (g₃ : 0 < fi 2 2⁻¹) :
  (fun n ↦ fi n (1 - 1 / ↑n)) (Order.pred (Nat.succ 1)) < (fun n ↦ fi n (1 - 1 / ↑n)) (Nat.succ 1) := by
  simp
  norm_cast
  rw [g₁, NNReal.IsConjExponent.one_sub_inv g₂]
  exact g₃



lemma imo_1985_p6_9_9
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (g₂ : NNReal.IsConjExponent 2 2):
   0 < fi 2 2⁻¹ := by
  let x := fi 2 2⁻¹
  have hx₀: x = fi 2 2⁻¹ := by rfl
  have hx₁: f₀ 2 x = 2⁻¹ := by
    rw [hx₀]
    have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
    exact g₃ 2⁻¹
  rw [← hx₀]
  contrapose! hx₁
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)


lemma imo_1985_p6_9_10
  (f₀ : ℕ → NNReal → NNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (x : NNReal := fi 2 2⁻¹)
  (hx₀ : x = fi 2 2⁻¹):
   f₀ 2 x = 2⁻¹ := by
  rw [hx₀]
  have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
  exact g₃ 2⁻¹


lemma imo_1985_p6_9_11
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (g₂ : NNReal.IsConjExponent 2 2)
  (x : NNReal := fi 2 2⁻¹)
  (hx₀ : x = fi 2 2⁻¹)
  (hx₁ : f₀ 2 x = 2⁻¹):
   0 < fi 2 2⁻¹ := by
  rw [← hx₀]
  contrapose! hx₁
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)


lemma imo_1985_p6_9_12
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (g₂ : NNReal.IsConjExponent 2 2)
  (x : NNReal := fi 2 2⁻¹)
  (hx₁ : x ≤ 0):
   f₀ 2 x ≠ 2⁻¹ := by
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)


lemma imo_1985_p6_9_13
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (g₂ : NNReal.IsConjExponent 2 2)
  (x : NNReal := fi 2 2⁻¹)
  (hc₁ : x = 0):
   f₀ 2 x ≠ 2⁻¹ := by
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)


lemma imo_1985_p6_9_14
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (x : NNReal := fi 2 2⁻¹)
  (hc₁ : x = 0):
   f₀ 2 x = 0 := by
  rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
  norm_cast
  rw [zero_mul]
  exact Real.toNNReal_zero

lemma imo_1985_p6_9_15
  (f₀ : ℕ → NNReal → NNReal)
  (fi : ℕ → NNReal → NNReal)
  (g₂ : NNReal.IsConjExponent 2 2)
  (x : NNReal := fi 2 2⁻¹)
  (hc₃ : f₀ 2 x = 0):
   f₀ 2 x ≠ 2⁻¹ := by
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₂)

lemma imo_1985_p6_9_16
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x)):
  ∀ (n : ℕ), Nat.succ 1 ≤ n →
    (fun n => fi n (1 - 1 / ↑n)) (Order.pred n) < (fun n => fi n (1 - 1 / ↑n)) n →
      (fun n => fi n (1 - 1 / ↑n)) (Order.pred (n + 1)) < (fun n => fi n (1 - 1 / ↑n)) (n + 1) := by
  simp
  intros n hn₀ _
  let i := fi n (1 - (↑n)⁻¹)
  let j := fi (n + 1) (1 - ((↑n:NNReal) + 1)⁻¹)
  have hi₀: i = fi n (1 - (↑n)⁻¹) := by rfl
  have hj₀: j = fi (n + 1) (1 - ((↑n:NNReal) + 1)⁻¹) := by rfl
  have hi₁: f₀ n i = (1 - (↑n)⁻¹) := by exact (hf₇ n i (1 - (↑n:NNReal)⁻¹) (by linarith)).mpr hi₀.symm
  have hj₁: f₀ (n + 1) j = (1 - ((↑n:NNReal) + 1)⁻¹) := by
    exact (hf₇ (n + 1) j _ (by linarith)).mpr hj₀.symm
  have hj₂: (1 - ((↑n:NNReal) + 1)⁻¹) = (1 - ((n:ℝ) + 1)⁻¹).toNNReal := by
    exact rfl
  have hn₂: f₀ (n + 1) i < f₀ (n + 1) j := by
    rw [hj₁, hj₂, hf₂ (n + 1) _ (by linarith), h₁ n i (by linarith)]
    rw [hf₁ n i (by linarith), hi₁]
    refine (Real.toNNReal_lt_toNNReal_iff ?_).mpr ?_
    . refine sub_pos.mpr ?_
      refine inv_lt_one_of_one_lt₀ ?_
      norm_cast
      exact Nat.lt_add_right 1 hn₀
    . have g₀: (↑n:NNReal)⁻¹ ≤ 1 := by exact Nat.cast_inv_le_one n
      rw [NNReal.coe_sub g₀, NNReal.coe_inv]
      simp
      refine inv_strictAnti₀ ?_ ?_
      . norm_cast
        exact Nat.zero_lt_of_lt hn₀
      . norm_cast
        exact lt_add_one n
  refine (StrictMono.lt_iff_lt ?_).mp hn₂
  exact hmo₂ (n + 1) (by linarith)

lemma imo_1985_p6_9_17
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (hf₇ : ∀ (n : ℕ) (x y : NNReal), 0 < n → (f₀ n x = y ↔ fi n y = x))
  (n : ℕ)
  (hn₀ : 2 ≤ n) :
   fi n (1 - (↑n)⁻¹) < fi (n + 1) (1 - (↑n + 1:NNReal)⁻¹) := by
  let i := fi n (1 - (↑n)⁻¹)
  let j := fi (n + 1) (1 - ((↑n:NNReal) + 1)⁻¹)
  have hi₀: i = fi n (1 - (↑n)⁻¹) := by rfl
  have hj₀: j = fi (n + 1) (1 - ((↑n:NNReal) + 1)⁻¹) := by rfl
  have hi₁: f₀ n i = (1 - (↑n)⁻¹) := by exact (hf₇ n i (1 - (↑n:NNReal)⁻¹) (by linarith)).mpr hi₀.symm
  have hj₁: f₀ (n + 1) j = (1 - ((↑n:NNReal) + 1)⁻¹) := by
    exact (hf₇ (n + 1) j _ (by linarith)).mpr hj₀.symm
  have hj₂: (1 - ((↑n:NNReal) + 1)⁻¹) = (1 - ((n:ℝ) + 1)⁻¹).toNNReal := by
    exact rfl
  have hn₂: f₀ (n + 1) i < f₀ (n + 1) j := by
    rw [hj₁, hj₂, hf₂ (n + 1) _ (by linarith), h₁ n i (by linarith)]
    rw [hf₁ n i (by linarith), hi₁]
    refine (Real.toNNReal_lt_toNNReal_iff ?_).mpr ?_
    . refine sub_pos.mpr ?_
      refine inv_lt_one_of_one_lt₀ ?_
      norm_cast
      exact Nat.lt_add_right 1 hn₀
    . have g₀: (↑n:NNReal)⁻¹ ≤ 1 := by exact Nat.cast_inv_le_one n
      rw [NNReal.coe_sub g₀, NNReal.coe_inv]
      simp
      refine inv_strictAnti₀ ?_ ?_
      . norm_cast
        exact Nat.zero_lt_of_lt hn₀
      . norm_cast
        exact lt_add_one n
  refine (StrictMono.lt_iff_lt ?_).mp hn₂
  exact hmo₂ (n + 1) (by linarith)


lemma imo_1985_p6_9_18
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (n : ℕ)
  (hn₀ : 2 ≤ n)
  (i : NNReal := fi n (1 - (↑n)⁻¹))
  (j : NNReal := fi (n + 1) (1 - (↑n + 1:NNReal)⁻¹))
  (hi₀ : i = fi n (1 - (↑n)⁻¹))
  (hj₀ : j = fi (n + 1) (1 - (↑n + 1:NNReal)⁻¹))
  (hi₁ : f₀ n i = 1 - (↑n)⁻¹)
  (hj₁ : f₀ (n + 1) j = 1 - (↑n + 1:NNReal)⁻¹)
  (hj₂ : (1 - ((↑n:NNReal) + 1)⁻¹) = (1 - ((n:ℝ) + 1)⁻¹).toNNReal):
  fi n (1 - (↑n)⁻¹) < fi (n + 1) (1 - (↑n + 1:NNReal)⁻¹) := by
  have hn₂: f₀ (n + 1) i < f₀ (n + 1) j := by
    rw [hj₁, hj₂, hf₂ (n + 1) _ (by linarith), h₁ n i (by linarith)]
    rw [hf₁ n i (by linarith), hi₁]
    refine (Real.toNNReal_lt_toNNReal_iff ?_).mpr ?_
    . refine sub_pos.mpr ?_
      refine inv_lt_one_of_one_lt₀ ?_
      norm_cast
      exact Nat.lt_add_right 1 hn₀
    . have g₀: (↑n:NNReal)⁻¹ ≤ 1 := by exact Nat.cast_inv_le_one n
      rw [NNReal.coe_sub g₀, NNReal.coe_inv]
      simp
      refine inv_strictAnti₀ ?_ ?_
      . norm_cast
        exact Nat.zero_lt_of_lt hn₀
      . norm_cast
        exact lt_add_one n
  rw [← hi₀, ← hj₀]
  refine (StrictMono.lt_iff_lt ?_).mp hn₂
  exact hmo₂ (n + 1) (by linarith)

lemma imo_1985_p6_9_19
  (f : ℕ → NNReal → ℝ)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (n : ℕ)
  (hn₀ : 2 ≤ n)
  (i j: NNReal)
  (hi₁ : f₀ n i = 1 - (↑n)⁻¹)
  (hj₁ : f₀ (n + 1) j = 1 - (↑n + 1:NNReal)⁻¹)
  (hj₂ : (1 - ((↑n:NNReal) + 1)⁻¹) = (1 - ((n:ℝ) + 1)⁻¹).toNNReal):
   f₀ (n + 1) i < f₀ (n + 1) j := by
  rw [hj₁, hj₂, hf₂ (n + 1) _ (by linarith), h₁ n i (by linarith)]
  rw [hf₁ n i (by linarith), hi₁]
  refine (Real.toNNReal_lt_toNNReal_iff ?_).mpr ?_
  . refine sub_pos.mpr ?_
    refine inv_lt_one_of_one_lt₀ ?_
    norm_cast
    exact Nat.lt_add_right 1 hn₀
  . have g₀: (↑n:NNReal)⁻¹ ≤ 1 := by exact Nat.cast_inv_le_one n
    rw [NNReal.coe_sub g₀, NNReal.coe_inv]
    simp
    refine inv_strictAnti₀ ?_ ?_
    . norm_cast
      exact Nat.zero_lt_of_lt hn₀
    . norm_cast
      exact lt_add_one n

lemma imo_1985_p6_9_20
  (f : ℕ → NNReal → ℝ)
  (f₀ : ℕ → NNReal → NNReal)
  (hf₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f n x = ↑(f₀ n x))
  (n : ℕ)
  (hn₀ : 2 ≤ n)
  (i : NNReal)
  (hi₁ : f₀ n i = 1 - (↑n)⁻¹):
   (f n i * (f n i + 1 / ↑n)).toNNReal < (1 - (↑n + 1:ℝ)⁻¹).toNNReal := by
  rw [hf₁ n i (by linarith), hi₁]
  refine (Real.toNNReal_lt_toNNReal_iff ?_).mpr ?_
  . refine sub_pos.mpr ?_
    refine inv_lt_one_of_one_lt₀ ?_
    norm_cast
    exact Nat.lt_add_right 1 hn₀
  . have g₀: (↑n:NNReal)⁻¹ ≤ 1 := by exact Nat.cast_inv_le_one n
    rw [NNReal.coe_sub g₀, NNReal.coe_inv]
    simp
    refine inv_strictAnti₀ ?_ ?_
    . norm_cast
      exact Nat.zero_lt_of_lt hn₀
    . norm_cast
      exact lt_add_one n


lemma imo_1985_p6_9_21
  (n : ℕ)
  (hn₀ : 2 ≤ n):
   (↑((1:NNReal) - (↑n)⁻¹) * (↑((1:NNReal) - (↑n)⁻¹) + (1:ℝ) / ↑n)).toNNReal < (1 - (↑n + 1:ℝ)⁻¹).toNNReal := by
  refine (Real.toNNReal_lt_toNNReal_iff ?_).mpr ?_
  . refine sub_pos.mpr ?_
    refine inv_lt_one_of_one_lt₀ ?_
    norm_cast
    exact Nat.lt_add_right 1 hn₀
  . have g₀: (↑n:NNReal)⁻¹ ≤ 1 := by exact Nat.cast_inv_le_one n
    rw [NNReal.coe_sub g₀, NNReal.coe_inv]
    simp
    refine inv_strictAnti₀ ?_ ?_
    . norm_cast
      exact Nat.zero_lt_of_lt hn₀
    . norm_cast
      exact lt_add_one n


lemma imo_1985_p6_9_22
  (f₀ : ℕ → NNReal → NNReal)
  (hmo₂ : ∀ (n : ℕ), 0 < n → StrictMono (f₀ n))
  (fi : ℕ → NNReal → NNReal)
  (n : ℕ)
  (hn₀ : 2 ≤ n)
  (i j: NNReal)
  (hi₀ : i = fi n (1 - (↑n)⁻¹))
  (hj₀ : j = fi (n + 1) (1 - (↑n + 1:NNReal)⁻¹))
  (hn₂ : f₀ (n + 1) i < f₀ (n + 1) j):
   fi n (1 - (↑n)⁻¹) < fi (n + 1) (1 - (↑n + 1:NNReal)⁻¹) := by
  rw [← hi₀, ← hj₀]
  refine (StrictMono.lt_iff_lt ?_).mp hn₂
  exact hmo₂ (n + 1) (by linarith)

lemma imo_1985_p6_9_23
  (n : ℕ)
  (hn₀ : 2 ≤ n):
   0 < 1 - (↑n + (1:ℝ))⁻¹ := by
  refine sub_pos.mpr ?_
  refine inv_lt_one_of_one_lt₀ ?_
  norm_cast
  exact Nat.lt_add_right 1 hn₀

lemma imo_1985_p6_9_24
  (n : ℕ)
  (hn₀ : 2 ≤ n):
  (↑n + 1:ℝ)⁻¹ < (1:ℝ) := by
  refine inv_lt_one_of_one_lt₀ ?_
  norm_cast
  exact Nat.lt_add_right 1 hn₀

lemma imo_1985_p6_9_25
  (n : ℕ)
  (hn₀ : 2 ≤ n):
   ↑((1:NNReal) - (↑n)⁻¹) * (↑((1:NNReal) - (↑n)⁻¹) + 1 / ↑n) < (1:ℝ) - (↑n + (1:ℝ))⁻¹ := by
  have g₀: (↑n:NNReal)⁻¹ ≤ 1 := by exact Nat.cast_inv_le_one n
  rw [NNReal.coe_sub g₀, NNReal.coe_inv]
  simp
  refine inv_strictAnti₀ ?_ ?_
  . norm_cast
    exact Nat.zero_lt_of_lt hn₀
  . norm_cast
    exact lt_add_one n

lemma imo_1985_p6_9_26
  (n : ℕ)
  (hn₀ : 2 ≤ n)
  (g₀ : (↑n:NNReal)⁻¹ ≤ 1):
  ↑((1:NNReal) - (↑n)⁻¹) * (↑((1:NNReal) - (↑n)⁻¹) + 1 / ↑n) < (1:ℝ) - (↑n + (1:ℝ))⁻¹ := by
  rw [NNReal.coe_sub g₀, NNReal.coe_inv]
  simp
  refine inv_strictAnti₀ ?_ ?_
  . norm_cast
    exact Nat.zero_lt_of_lt hn₀
  . norm_cast
    exact lt_add_one n


lemma imo_1985_p6_9_27
  (n : ℕ)
  (hn₀ : 2 ≤ n):
   (↑n + 1:ℝ)⁻¹ < (↑n)⁻¹ := by
  refine inv_strictAnti₀ ?_ ?_
  . norm_cast
    exact Nat.zero_lt_of_lt hn₀
  . norm_cast
    exact lt_add_one n

lemma imo_1985_p6_10_1
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₀ : fb = fun (n : ↑sn) => fi (↑n) (1 - 1 / ↑↑n))
  (hnb₀ : 2 ∈ sn)
  (nb : ↑sn)
  (hnb : nb = ⟨2, hnb₀⟩):
   0 < fb nb := by
  have g₁: (2:NNReal).IsConjExponent (2:NNReal) := by
    refine (NNReal.isConjExponent_iff_eq_conjExponent ?_).mpr ?_
    . exact one_lt_two
    . norm_cast
      simp
  rw [hfb₀]
  simp
  have hnb₁: nb.val = 2 := by simp_all only [one_div]
  rw [hnb₁]
  norm_cast
  rw [NNReal.IsConjExponent.one_sub_inv g₁]
  let x := fi 2 2⁻¹
  have hx₀: x = fi 2 2⁻¹ := by rfl
  have hx₁: f₀ 2 x = 2⁻¹ := by
    rw [hx₀]
    have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
    exact g₃ 2⁻¹
  rw [← hx₀]
  contrapose! hx₁
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₁)


lemma imo_1985_p6_10_2
  (fi : ℕ → NNReal → NNReal)
  (sn : Set ℕ)
  (nb : ↑sn)
  (hnb₀ : 2 ∈ sn)
  (hnb : nb = ⟨2, hnb₀⟩):
   NNReal.IsConjExponent 2 2 := by
  refine (NNReal.isConjExponent_iff_eq_conjExponent ?_).mpr ?_
  . exact one_lt_two
  . norm_cast
    simp


lemma imo_1985_p6_10_3
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (sn : Set ℕ)
  (hnb₀ : 2 ∈ sn)
  (nb : ↑sn)
  (hnb : nb = ⟨2, hnb₀⟩)
  (g₁ : NNReal.IsConjExponent 2 2):
   0 < fi (↑nb) (1 - (↑↑nb)⁻¹) := by
  have hnb₁: nb.val = 2 := by simp_all only [one_div]
  rw [hnb₁]
  norm_cast
  rw [NNReal.IsConjExponent.one_sub_inv g₁]
  let x := fi 2 2⁻¹
  have hx₀: x = fi 2 2⁻¹ := by rfl
  have hx₁: f₀ 2 x = 2⁻¹ := by
    rw [hx₀]
    have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
    exact g₃ 2⁻¹
  rw [← hx₀]
  contrapose! hx₁
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₁)


lemma imo_1985_p6_10_4
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (g₁ : NNReal.IsConjExponent 2 2):
   0 < fi 2 (1 - 2⁻¹) := by
  rw [NNReal.IsConjExponent.one_sub_inv g₁]
  let x := fi 2 2⁻¹
  have hx₀: x = fi 2 2⁻¹ := by rfl
  have hx₁: f₀ 2 x = 2⁻¹ := by
    rw [hx₀]
    have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
    exact g₃ 2⁻¹
  rw [← hx₀]
  contrapose! hx₁
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₁)


lemma imo_1985_p6_10_5
  (fi : ℕ → NNReal → NNReal)
  (sn : Set ℕ)
  (fb : ↑sn → NNReal)
  (hfb₀ : fb = fun (n : ↑sn) => fi (↑n) (1 - 1 / ↑↑n))
  (hnb₀ : 2 ∈ sn)
  (nb : ↑sn)
  (hnb : nb = ⟨2, hnb₀⟩)
  (g₂ : 0 < fi 2 (1 - 2⁻¹)):
   0 < fb nb := by
  rw [hfb₀]
  simp
  have hnb₁: nb.val = 2 := by simp_all only [one_div]
  rw [hnb₁]
  norm_cast



lemma imo_1985_p6_10_6
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (g₁ : NNReal.IsConjExponent 2 2):
   0 < fi 2 2⁻¹ := by
  let x := fi 2 2⁻¹
  have hx₀: x = fi 2 2⁻¹ := by rfl
  have hx₁: f₀ 2 x = 2⁻¹ := by
    rw [hx₀]
    have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
    exact g₃ 2⁻¹
  rw [← hx₀]
  contrapose! hx₁
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₁)


lemma imo_1985_p6_10_7
  (f₀ : ℕ → NNReal → NNReal)
  (fi : ℕ → NNReal → NNReal)
  (hmo₇ : ∀ (n : ℕ), 0 < n → Function.RightInverse (fi n) (f₀ n))
  (x : NNReal := fi 2 2⁻¹)
  (hx₀ : x = fi 2 2⁻¹):
   f₀ 2 x = 2⁻¹ := by
  rw [hx₀]
  have g₃: Function.RightInverse (fi 2) (f₀ 2) := by exact hmo₇ 2 (by linarith)
  exact g₃ 2⁻¹


lemma imo_1985_p6_10_8
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (g₁ : NNReal.IsConjExponent 2 2)
  (x : NNReal := fi 2 2⁻¹)
  (hx₀ : x = fi 2 2⁻¹)
  (hx₁ : f₀ 2 x = 2⁻¹):
   0 < fi 2 2⁻¹ := by
  rw [← hx₀]
  contrapose! hx₁
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₁)


lemma imo_1985_p6_10_9
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (g₁ : NNReal.IsConjExponent 2 2)
  (x : NNReal := fi 2 2⁻¹)
  (hx₁ : x ≤ 0):
   f₀ 2 x ≠ 2⁻¹ := by
  have hc₁: x = 0 := by exact nonpos_iff_eq_zero.mp hx₁
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₁)



lemma imo_1985_p6_10_10
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (g₁ : NNReal.IsConjExponent 2 2)
  (x : NNReal := fi 2 2⁻¹)
  (hc₁ : x = 0):
   f₀ 2 x ≠ 2⁻¹ := by
  have hc₃: f₀ 2 x = 0 := by
    rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
    norm_cast
    rw [zero_mul]
    exact Real.toNNReal_zero
  rw [hc₃]
  exact Ne.symm (NNReal.IsConjExponent.inv_ne_zero g₁)


lemma imo_1985_p6_10_11
  (f : ℕ → NNReal → ℝ)
  (h₀ : ∀ (x : NNReal), f 1 x = ↑x)
  (h₁ : ∀ (n : ℕ) (x : NNReal), 0 < n → f (n + 1) x = f n x * (f n x + 1 / ↑n))
  (f₀ : ℕ → NNReal → NNReal)
  (hf₂ : ∀ (n : ℕ) (x : NNReal), 0 < n → f₀ n x = (f n x).toNNReal)
  (fi : ℕ → NNReal → NNReal)
  (x : NNReal := fi 2 2⁻¹)
  (hc₁ : x = 0):
   f₀ 2 x = 0 := by
  rw [hc₁, hf₂ 2 0 (by linarith), h₁ 1 0 (by linarith), h₀ 0]
  norm_cast
  rw [zero_mul]
  exact Real.toNNReal_zero


lemma imo_1985_p6_10_12
  (sn : Set ℕ)
  (sb : Set NNReal)
  (fb : ↑sn → NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x => ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (br : ℝ)
  (hbr₀ : IsLUB sbr br)
  (nb : ↑sn)
  (g₀ : 0 < fb nb):
   0 < br := by
  have g₁: ∃ x, 0 < x ∧ x ∈ sbr := by
    use (fb nb).toReal
    constructor
    . exact g₀
    . rw [hsbr]
      simp
      use fb ↑nb
      constructor
      . rw [hsb₀]
        exact Set.mem_range_self nb
      . exact congrFun hfr (fb ↑nb)
  obtain ⟨x, hx₀, hx₁⟩ := g₁
  have hx₂: br ∈ upperBounds sbr := by
    refine (isLUB_le_iff hbr₀).mp ?_
    exact Preorder.le_refl br
  exact gt_of_ge_of_gt (hx₂ hx₁) hx₀


lemma imo_1985_p6_10_13
  (sn : Set ℕ)
  (sb : Set NNReal)
  (fb : ↑sn → NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x => ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (nb : ↑sn)
  (g₀ : 0 < fb nb):
   ∃ x, 0 < x ∧ x ∈ sbr := by
  use (fb nb).toReal
  constructor
  . exact g₀
  . rw [hsbr]
    simp
    use fb ↑nb
    constructor
    . rw [hsb₀]
      exact Set.mem_range_self nb
    . exact congrFun hfr (fb ↑nb)

lemma imo_1985_p6_10_14
  (sn : Set ℕ)
  (sb : Set NNReal)
  (fb : ↑sn → NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x => ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (nb : ↑sn)
  (g₀ : 0 < fb nb):
   0 < ↑(fb nb) ∧ ↑(fb nb) ∈ sbr := by
  constructor
  . exact g₀
  . rw [hsbr]
    simp
    use fb ↑nb
    constructor
    . rw [hsb₀]
      exact Set.mem_range_self nb
    . exact congrFun hfr (fb ↑nb)


lemma imo_1985_p6_10_15
  (sn : Set ℕ)
  (sb : Set NNReal)
  (fb : ↑sn → NNReal)
  (hsb₀ : sb = Set.range fb)
  (fr : NNReal → ℝ)
  (hfr : fr = fun x => ↑x)
  (sbr : Set ℝ)
  (hsbr : sbr = fr '' sb)
  (nb : ↑sn):
   ↑(fb nb) ∈ sbr := by
  rw [hsbr]
  simp
  use fb ↑nb
  constructor
  . rw [hsb₀]
    exact Set.mem_range_self nb
  . exact congrFun hfr (fb ↑nb)
