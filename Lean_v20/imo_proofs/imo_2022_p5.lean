import Mathlib
set_option linter.unusedVariables.analyzeTactics true

open Nat


lemma mylemma_1
  (b p: ℕ)
  (h₀: 0 < b)
  (hbp: b < p) :
  (1 + (b * p + b ^ p) ≤ (1 + b) ^ p) := by
  refine Nat.le_induction ?_ ?_ p hbp
  . rw [add_pow 1 b b.succ]
    rw [Finset.sum_range_succ _ b.succ]
    simp
    rw [Finset.sum_range_succ _ b]
    simp
    rw [add_comm _ (b * (b + 1))]
    have gb: b = b - 1 + 1 := by exact (Nat.sub_eq_iff_eq_add h₀).mp rfl
    nth_rewrite 7 [gb]
    rw [Finset.sum_range_succ' _ (b-1)]
    simp
    omega
  . intros n _ h₂
    nth_rewrite 2 [pow_add]
    rw [pow_one]
    have h₃: (1 + (b * n + b ^ n)) * (1 + b) ≤ ((1 + b) ^ n) * (1 + b) := by
      exact mul_le_mul_right' h₂ (1 + b)
    have h₄: 1 + (b * (n + 1) + b ^ (n + 1)) ≤ (1 + (b * n + b ^ n)) * (1 + b) := by
      ring_nf
      rw [Nat.add_assoc _ (b ^ 2 * n) (b ^ n)]
      exact Nat.le_add_right (1 + b + b * b ^ n + b * n) (b ^ 2 * n + b ^ n)
    exact le_trans h₄ h₃


lemma mylemma_2
  (b: ℕ) :
  (b.factorial ≤ b ^ b) := by
  exact factorial_le_pow b


lemma mylemma_3
  (a b p: ℕ)
  (hp: Nat.Prime p)
  (h₁: a ^ p = b.factorial + p)
  (hbp: p ≤ b) :
  (p ∣ a) := by
  have h₂: p ∣ b.factorial := by exact Nat.dvd_factorial (Nat.Prime.pos hp) hbp
  have h₃: p ∣ b.factorial + p := by exact Nat.dvd_add_self_right.mpr h₂
  have h₄: p ∣ a^p := by
    rw [h₁]
    exact h₃
  exact Nat.Prime.dvd_of_dvd_pow hp h₄


lemma mylemma_42
  (a b : ℕ)
  (h₀: 2 ≤ a)
  (h₁: a < b) :
  (a + b < a * b ) := by
  have h₂: a + b < b + b := by exact add_lt_add_right h₁ b
  have h₃: b + b ≤ a * b := by
    rw [← two_mul]
    exact mul_le_mul_right' h₀ b
  exact gt_of_ge_of_gt h₃ h₂


lemma mylemma_43
  (p: ℕ) :
  (Finset.Ico p (2 * p - 1)).prod (fun x => x + 1)
    = (Finset.range (p - 1)).prod (fun x => p + (x + 1)) := by
  rw [Finset.prod_Ico_eq_prod_range _ (p) (2 * p - 1)]
  have h₀: 2 * p - 1 - p = p - 1 := by omega
  rw [h₀]
  exact rfl


lemma mylemma_44
  (p: ℕ)
  (hp: 2 ≤ p) :
  (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1)
      = (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x + 1)) := by
  refine Nat.le_induction ?_ ?_ p hp
  . norm_num
  . intros n hn2 h₀
    simp at *
    have hn₀ : n ≠ 0 := by bound
    have hn₁: 0 < n := by exact lt_of_succ_lt hn2
    rw [← Nat.mul_factorial_pred hn₀, h₀]
    let f: (ℕ → ℕ) := fun (x : ℕ) => n - x
    have h₁: (Finset.range n).prod f =
        (Finset.range 1).prod f * (Finset.Ico 1 n).prod f := by
      exact (Finset.prod_range_mul_prod_Ico (fun k => n - k) hn₁).symm
    rw [h₁]
    have h₂: (Finset.range 1).prod f = n := by
      exact Finset.prod_range_one fun k => n - k
    rw [h₂]
    simp
    left
    rw [Finset.prod_Ico_eq_prod_range f 1 n]
    ring_nf
    exact rfl


lemma mylemma_41
  (b p: ℕ)
  -- (h₀: 0 < b)
  (hp: Nat.Prime p)
  (hb2p: b < 2 * p) :
  b.factorial + p < p ^ (2 * p) := by
  have h₁: b.factorial ≤ (2*p - 1).factorial := by
    refine factorial_le ?_
    exact le_pred_of_lt hb2p
  have gp: 2 ≤ p := by exact Prime.two_le hp
  have gp1: (p - 1) + 1 = p := by
    refine Nat.sub_add_cancel ?_
    exact one_le_of_lt gp
  let f: (ℕ → ℕ) := (fun (x : ℕ) => x + 1)
  have h₂: (Finset.range (2 * p - 1)).prod f =
      (Finset.range (p - 1)).prod (fun (x : ℕ) => p^2 - (x+1)^2) * p := by
    -- break the prod into three segments rang(p-1) + p + (p+1) until 2p-1
    have g₀: (Finset.range (2 * p - 1)).prod f = (Finset.range ((p - 1) + 1)).prod f
           * (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod f := by
      symm
      refine Finset.prod_range_mul_prod_Ico f ?_
      rw [gp1]
      have gg₀: p + 2 - 1 ≤ 2 * p - 1 := by
        refine Nat.sub_le_sub_right ?_ 1
        rw [add_comm]
        exact add_le_mul (by norm_num) gp
      exact le_of_lt gg₀
    have g₁: (Finset.range ((p - 1) + 1)).prod (fun (x : ℕ) => x + 1) =
       (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1) * ((p - 1) + 1) := by
      exact Finset.prod_range_succ _ (p - 1)
    rw [g₁] at g₀
    nth_rewrite 2 [mul_comm] at g₀
    rw [← mul_assoc] at g₀
    rw [gp1] at g₀ g₁
    have g₂: (Finset.Ico ((p - 1) + 1) (2 * p - 1)).prod (fun (x : ℕ) => x + 1)
              = (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1)) := by
      rw [gp1]
      exact mylemma_43 p
    have g₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => x + 1)
              = (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1)) := by
      exact mylemma_44 p gp
    rw [gp1] at g₂
    rw [g₂,g₃] at g₀
    have g₄: (Finset.range (p - 1)).prod (fun (x : ℕ) => p + (x+1))
      * (Finset.range (p - 1)).prod (fun (x : ℕ) => p - (x+1))
            = (Finset.range (p - 1)).prod (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
      symm
      exact Finset.prod_mul_distrib
    have g₅: (fun (x : ℕ) => p ^ 2 - (x+1) ^ 2) = (fun (x : ℕ) => (p + (x+1)) * (p - (x+1))) := by
      ext1 x
      exact Nat.sq_sub_sq p (x + 1)
    rw [g₄,← g₅] at g₀
    exact g₀
  have h₃: (Finset.range (p - 1)).prod (fun (x : ℕ) => p^2 - (x+1)^2) * p
      ≤ (p^2)^(Finset.range (p - 1)).card * p := by
    refine Nat.mul_le_mul_right ?_ ?_
    refine Finset.prod_le_pow_card (Finset.range (p - 1)) ?_ (p^2) ?_
    intros x _
    exact (p ^ 2).sub_le ((x + 1) ^ 2)
  simp at *
  have h₄: b.factorial + p ≤ (p ^ 2) ^ (p - 1) * p + p := by
    refine add_le_add_right ?_ p
    refine le_trans ?_ h₃
    rw [← h₂]
    rw [Finset.prod_range_add_one_eq_factorial]
    exact h₁
  have h₅: b.factorial + p < (p ^ 2) ^ (p - 1) * p * p := by
    refine lt_of_le_of_lt h₄ ?_
    rw [add_comm]
    nth_rewrite 2 [mul_comm]
    refine mylemma_42 p ((p ^ 2) ^ (p - 1) * p) gp ?_
    refine lt_mul_left (by linarith) ?_
    rw [← pow_mul]
    refine Nat.one_lt_pow ?_ (Nat.lt_of_succ_le gp)
    refine Nat.mul_ne_zero (by norm_num) ?_
    exact Nat.sub_ne_zero_iff_lt.mpr gp
  rw [mul_assoc _ p p, ← pow_two p] at h₅
  rw [← Nat.pow_succ, succ_eq_add_one, gp1] at h₅
  rw [Nat.pow_mul]
  exact h₅


lemma mylemma_4
  (a b p: ℕ)
  (h₀: 0 < a ∧ 0 < b)
  (hp: Nat.Prime p)
  (h₁: a ^ p = b.factorial + p)
  (hbp: p ≤ b)
  (h₂: p ∣ a)
  (hb2p: b < 2 * p) :
  (a = p) := by
  have gp: p ≤ a := by exact Nat.le_of_dvd h₀.1 h₂
  cases' lt_or_eq_of_le gp with h₃ h₃
  . exfalso
    cases' h₂ with c h₂
    have gc: 0 < c := by
      by_contra! hc0
      interval_cases c
      simp at *
      linarith
    by_cases hc: c < p
    . have g₁: c ∣ c^p := by exact dvd_pow_self c (by linarith)
      have h₄: c ∣ a^p := by
        rw [h₂, mul_pow]
        exact dvd_mul_of_dvd_right g₁ (p ^ p)
      have h₅: c ∣ b.factorial := by exact Nat.dvd_factorial gc (by linarith)
      have g₂: p = a ^ p - b.factorial := by
        symm
        rw [add_comm] at h₁
        refine (Nat.sub_eq_iff_eq_add ?_).mpr h₁
        rw [add_comm] at h₁
        exact le.intro (h₁.symm)
      have h₆: c ∣ p := by
        rw [g₂]
        exact dvd_sub h₄ h₅
      have h₇: c = 1 ∨ c = p := by exact (dvd_prime hp).mp h₆
      cases' h₇ with h₇₀ h₇₁
      . rw [h₇₀, mul_one] at h₂
        rw [h₂] at h₃
        linarith [h₃]
      . rw [h₇₁] at hc
        simp at hc
    . push_neg at hc
      have g₃: p^2 ≤ a := by
        rw [h₂, pow_two]
        exact mul_le_mul_left' hc p
      have h₃: p^(2*p) ≤ a^p := by
        rw [pow_mul]
        exact pow_left_mono p g₃
      have h₇: b.factorial + p < p^(2*p) := by exact mylemma_41 b p hp hb2p
      rw [←h₁] at h₇
      linarith
  exact h₃.symm


lemma mylemma_53
  (p: ℕ)
  (hp5: 5 ≤ p) :
  ((↑p:ℤ) ^ p ≡ ↑p * (↑p + 1) * (-1) ^ (p - 1) + (-1) ^ p [ZMOD (↑p + 1) ^ 2]) := by
  have h₀: (↑p:ℤ) = (↑p + 1) - 1 := by simp
  have h₁: ↑p ^ p ≡ ((↑p + 1) - 1) ^ p [ZMOD (↑p + 1) ^ 2] := by rw [← h₀]
  have h₂: (((↑p:ℤ) + 1) - 1) ^ p = (↑p * (↑p + 1) * (-1:ℤ) ^ (p - 1) + (-1) ^ p)
           + (Finset.Ico 2 (p + 1)).sum (fun (k : ℕ) =>
           (↑p + 1) ^ k * (-1:ℤ) ^ (p - k) * ↑(p.choose k)) := by
    rw [sub_eq_add_neg]
    rw [add_pow ((↑p:ℤ) + 1) (-1:ℤ)]
    have g₀: 2 ≤ p + 1 := by
      have gg₀: 5 + 1 ≤ p + 1 := by exact add_le_add_right hp5 1
      refine le_trans ?_ gg₀
      norm_num
    have g₁: 1 ≤ 2 := by norm_num
    rw [← Finset.sum_range_add_sum_Ico _ g₀]
    rw [← Finset.sum_range_add_sum_Ico _ g₁]
    simp
    rw [add_comm]
    simp
    rw [mul_comm]
    rw [mul_assoc]
  have h₃: 0 ≡ (Finset.Ico 2 (p + 1)).sum (fun (k : ℕ) => (↑p + 1) ^ k * (-1) ^ (p - k) * ↑(p.choose k))
                [ZMOD (↑p + 1) ^ 2] := by
    refine Int.modEq_of_dvd ?_
    simp
    refine Finset.dvd_sum ?_
    intros x g₀
    have gx: 2 ≤ x := by exact (Finset.mem_Ico.mp g₀).left
    rw [mul_assoc]
    refine dvd_mul_of_dvd_left ?_ ((-1:ℤ) ^ (p - x) * ↑(p.choose x))
    refine pow_dvd_pow ((↑p:ℤ) + 1) gx
  rw [h₂] at h₁
  rw [← add_zero ((↑p:ℤ) ^ p)] at h₁
  exact Int.ModEq.add_right_cancel h₃ h₁


lemma mylemma_52
  (p: ℕ)
  (hp: Nat.Prime p)
  (hp5: 5 ≤ p)
  (h₀: (p + 1) ^ 2 ∣ p ^ p - p) :
  False := by
  have h₁: ((↑p^p - ↑p):ℤ) ≡ (↑(p.choose 1) * ↑(p + 1) * (-1:ℤ)^(p-1) + (-1:ℤ)^p) - ↑p
      [ZMOD ↑(p+1)^2] := by
    refine Int.ModEq.sub_right (↑p) ?_
    simp
    exact mylemma_53 p hp5
  have gpo: Odd p := by
    refine Nat.Prime.odd_of_ne_two hp ?_
    linarith [hp5]
  have gpe: Even (p - 1) := by
    refine hp.even_sub_one ?_
    linarith [hp5]
  have g₁: (-1:ℤ) ^ (p - 1) = 1 := by exact Even.neg_one_pow gpe
  have g₂: (-1:ℤ) ^ (p) = -1 := by exact Odd.neg_one_pow gpo
  rw [g₁,g₂] at h₁
  simp at h₁
  have h₂: (p ^ p - p) ≡ (p * (p + 1)) - 1 - p [MOD ((p + 1) ^ 2)] := by
    refine Int.natCast_modEq_iff.mp ?_
    have g₃: p ≤ p^p := by
      refine Nat.le_self_pow (by linarith) _
    rw [Nat.cast_sub g₃]
    have g₄: p ≤ p * (p + 1) - 1 := by
      rw [mul_add]
      simp
      rw [add_comm, Nat.add_sub_assoc]
      . simp
      . rw [← pow_two]
        refine Nat.one_le_pow 2 p (by linarith)
    rw [Nat.cast_sub g₄]
    have g₅: 1 ≤ p * (p + 1) := by
      rw [← mul_one (p * (p + 1))]
      refine Nat.le_mul_of_pos_left ?_ ?_
      refine Nat.mul_pos (by linarith) (by linarith)
    rw [Nat.cast_sub g₅]
    rw [← sub_eq_add_neg] at h₁
    norm_cast
    norm_cast at h₁
  have h₃: p * (p + 1) - 1 - p = p^2 - 1 := by
    rw [Nat.sub_sub, mul_add]
    simp
    rw [← pow_two]
    exact Nat.add_sub_add_right (p^2) p 1
  rw [h₃] at h₂
  clear h₃ gpo gpe g₁ g₂
  -- now derive a line of contradictions from h₀
  have hc₁: (p ^ p - p) ≡ 0 [MOD (p+1)^2] := by exact modEq_zero_iff_dvd.mpr h₀
  -- mix the contradiction with what we had in h₂
  have h₄: p ^ 2 - 1 ≡ 0 [MOD (p+1)^2] := by
    apply Nat.ModEq.symm at h₂
    exact Nat.ModEq.trans h₂ hc₁
  have h₅: p - 1 ≡ 0 [MOD (p+1)] := by
    rw [pow_two] at h₄
    have g₀: p^2 - 1^2 = (p-1) * (p+1) := by
      rw [mul_comm]
      exact Nat.sq_sub_sq p 1
    simp at g₀
    rw [g₀] at h₄
    have g₁: p + 1 ≠ 0 := by linarith
    refine Nat.ModEq.mul_right_cancel' g₁ ?_
    rw [zero_mul]
    exact h₄
  have h₆: p - 1 ≤ 0 := by
    refine Nat.ModEq.le_of_lt_add h₅ ?_
    simp
    rw [← succ_eq_add_one]
    refine Nat.sub_lt_succ p 1
  have h₇: 0 < p - 1 := by
    simp
    linarith
  linarith [h₆,h₇]


lemma mylemma_51
  (p: ℕ)
  (hpl: 5 ≤ p) :
  (p + p.factorial < p ^ p) := by
  -- we use induction
  refine Nat.le_induction ?_ ?_ p (hpl)
  . exact Nat.lt_of_sub_eq_succ rfl
  . intros n hn h₁
    have h₂: n + 1 + (n + 1).factorial = (n.factorial + 1) * (n + 1) := by
      rw[add_mul, one_mul, Nat.factorial_succ]
      rw [add_comm (n + 1)]
      rw [mul_comm (n + 1)]
    rw [h₂, pow_add, pow_one ]
    refine Nat.mul_lt_mul_of_pos_right ?_ (by linarith)
    have h₅: n ^ n < (n + 1) ^ n := by
      refine Nat.pow_lt_pow_left ?_ ?_
      . exact lt_add_one n
      . refine Nat.ne_of_gt ?_
        linarith
    linarith


lemma mylemma_5
  (b p: ℕ)
  (hp: Nat.Prime p)
  (hbp: p ≤ b)
  (h₁: p ^ p = b.factorial + p)
  (hp5: 5 ≤ p) :
  (False) := by
  -- first prove that b = p cannot be
  by_cases h₄: b = p
  . have h₅: p + p.factorial < p^p := by exact mylemma_51 p hp5
    rw [h₄] at h₁
    linarith
  . have hpb: p < b := by exact lt_of_le_of_ne' hbp h₄
    clear hbp h₄
    have h₂: (p + 1) ^ 2 ∣ b.factorial := by
      have g₁: p + 1 ≤ b := by exact succ_le_iff.mpr hpb
      have g₂: 2 ∣ (p + 1) := by
        have gg₁: Odd p := by
          refine hp.odd_of_ne_two ?_
          linarith
        have gg₂: Even (p + 1) := by
          refine gg₁.add_odd ?_
          norm_num
        exact even_iff_two_dvd.mp gg₂
      have g₃: 2 * ((p+1)/2) * (p + 1) ∣ b.factorial := by
        have gg₁: (p + 1).factorial ∣ b.factorial := by exact Nat.factorial_dvd_factorial g₁
        have gg₂: (p + 1).factorial = (p + 1) * p.factorial := by exact factorial_succ p
        rw [mul_comm] at gg₂
        have gg₃: 6/2 ≤ (p + 1)/2 := by
          refine Nat.div_le_div_right ?_
          linarith
        norm_num at gg₃
        have gg₄: 2 + (p+1)/2 ≤ p := by -- strong induction
          refine Nat.le_induction ?_ ?_ p (hp5)
          . norm_num
          . intros n _ h₂
            ring_nf
            have ggg₁: (n / 2).succ ≤ (n + 1) / 2 + 1 := by
              rw [← succ_eq_add_one]
              refine Nat.succ_le_succ ?_
              refine Nat.div_le_div_right ?_
              linarith
            simp
            nth_rewrite 1 [← mul_one 2]
            rw [Nat.two_mul 1, add_assoc]
            refine Nat.add_le_add_left ?_ 1
            refine le_trans ?_ h₂
            rw [add_comm 2 _]
            nth_rewrite 3 [← mul_one 2]
            rw [Nat.two_mul 1, ← add_assoc, add_comm 1]
            exact Nat.add_le_add_right ggg₁ 1
        have gg₅: (2+(p+1)/2).factorial ∣ p.factorial := by
          exact factorial_dvd_factorial gg₄
        have gg₆: (2:ℕ).factorial * ((p+1)/2).factorial ∣ p.factorial := by
          refine dvd_trans ?_ gg₅
          exact (2:ℕ).factorial_mul_factorial_dvd_factorial_add ((p + 1) / 2)
        have gg₇: 2 * ((p+1)/2) ∣ p.factorial := by
          refine dvd_trans ?_ gg₆
          simp
          refine mul_dvd_mul_left 2 ?_
          refine Nat.dvd_factorial (by linarith[gg₃]) (by linarith)
        have gg₈: 2 * ((p+1)/2) * (p + 1) ∣ p.factorial * (p + 1) := by
          refine mul_dvd_mul_right ?_ (p + 1)
          exact gg₇
        rw [gg₂] at gg₁
        exact dvd_trans gg₈ gg₁
      have g₄: 2 * ((p+1)/2) = (p + 1) := by
        exact Nat.mul_div_cancel' g₂
      rw [g₄] at g₃
      ring_nf at *
      exact g₃
    have h₃: b.factorial = p ^ p - p := by exact eq_tsub_of_add_eq (h₁.symm)
    rw [h₃] at h₂
    exact mylemma_52 p hp hp5 h₂


lemma mylemma_6
  (a b p: ℕ)
  (hp: Nat.Prime p)
  (h₂: p ∣ a)
  (hb2p: 2 * p ≤ b) :
  (p ^ 2 ∣ a ^ p - b.factorial) := by
  have g₁: p^p ∣ a^p := by exact pow_dvd_pow_of_dvd h₂ p
  have g₂: 2 ≤ p := by exact Prime.two_le hp
  have h₃: p^2 ∣ a^p := by exact pow_dvd_of_le_of_pow_dvd g₂ g₁
  have g₃: (2*p).factorial ∣ b.factorial := by exact factorial_dvd_factorial hb2p
  have g₄: p.factorial * p.factorial ∣ (p+p).factorial := by
    exact factorial_mul_factorial_dvd_factorial_add p p
  rw [← pow_two, ← two_mul] at g₄
  have g₅: p ∣ p.factorial := by exact Nat.dvd_factorial (by linarith) (by linarith)
  have h₄: p ^ 2 ∣ p.factorial ^ 2 := by exact pow_dvd_pow_of_dvd g₅ 2
  have g₆: p ^ 2 ∣ (2 * p).factorial := by exact dvd_trans h₄ g₄
  have h₅: p^2 ∣ b.factorial := by exact dvd_trans g₆ g₃
  exact dvd_sub h₃ h₅


theorem imo_2022_p5
  (a b p : ℕ)
  (h₀: 0 < a ∧ 0 < b)
  (hp: Nat.Prime p)
  (h₁: a^p = Nat.factorial b + p) :
  (a, b, p) = (2, 2, 2) ∨ (a, b, p) = (3, 4, 3) := by
  by_cases hbp: b < p -- no solution
  . exfalso
    by_cases hab: a ≤ b
    . have h₂: a ∣ b.factorial := by exact Nat.dvd_factorial h₀.1 hab
      have g₃: a ∣ b.factorial + p := by
        rw [← h₁]
        refine dvd_pow_self a ?_
        exact Nat.Prime.ne_zero hp
      have h₃: a ∣ p := by exact (Nat.dvd_add_right h₂).mp g₃
      have h₄: a = 1 := by
        have g₄: a = 1 ∨ a = p := by
          exact (Nat.dvd_prime hp).mp h₃
        cases' g₄ with g₄₀ g₄₁
        . exact g₄₀
        . exfalso
          rw [← g₄₁] at hbp
          linarith[hbp,hab]
      rw [h₄] at h₁
      simp at h₁
      have h₅: 2 ≤ p := by exact Nat.Prime.two_le hp
      have g₆: 0 < b.factorial := by exact Nat.factorial_pos b
      have h₇: 1+2 ≤ b.factorial + p := by exact Nat.add_le_add g₆ h₅
      rw [← h₁] at h₇
      linarith
    . push_neg at hab
      have h₂: (b+1)^p ≤ a^p := by
        refine (Nat.pow_le_pow_iff_left ?_).mpr hab
        exact Nat.Prime.ne_zero hp
      have h₃: b^p + p*b + 1 ≤ (b+1)^p := by
        ring_nf
        rw [add_assoc]
        exact mylemma_1 b p h₀.2 hbp
      have g₄: p * 1 ≤ p * b := by
        refine mul_le_mul ?_ ?_ ?_ ?_
        . exact rfl.ge
        . exact h₀.2
        . norm_num
        . exact Nat.zero_le p
      have g₄: b.factorial ≤ b^b := by exact Nat.factorial_le_pow b
      have g₅: b^b ≤ b^p := by
        refine Nat.pow_le_pow_right h₀.2 ?_
        exact le_of_lt hbp
      linarith
  . push_neg at hbp
    have h₂: p ∣ a := by exact mylemma_3 a b p hp h₁ hbp
    by_cases hb2p: b < 2*p
    . have h₃: a = p := by exact mylemma_4 a b p h₀ hp h₁ hbp h₂ hb2p
      rw [h₃] at h₁
      by_cases hp5: p < 5
      . have h₄: 2 ≤ p := by exact Prime.two_le hp
        interval_cases p
        . left
          norm_num at h₁
          have h₄: b.factorial = 2 := by linarith
          have g₅: (2:ℕ).factorial = 2 := by norm_num
          rw [← g₅] at h₄
          have h₅: b = 2 := by
            refine (Nat.factorial_inj ?_).mp h₄
            linarith
          rw [h₃,h₅]
        . right
          norm_num at h₁
          rw [h₃]
          have h₄: b.factorial = 24 := by linarith
          have g₅: (4:ℕ).factorial = 24 := by exact rfl
          rw [← g₅] at h₄
          have h₅: b = 4 := by
            refine (Nat.factorial_inj ?_).mp h₄
            linarith
          rw [h₅]
        . exfalso
          contradiction
      . push_neg at hp5
        exfalso -- lifting the exponent
        exact mylemma_5 b p hp hbp h₁ hp5
    . push_neg at hb2p
      exfalso
      have h₃: p^2 ∣ a^p - b.factorial := by exact mylemma_6 a b p hp h₂ hb2p
      have g₃: b.factorial ≤ a^p := by exact le.intro (h₁.symm)
      have g₄: a^p - b.factorial = p := by
        rw [add_comm] at h₁
        exact (Nat.sub_eq_iff_eq_add g₃).mpr h₁
      have h₄: p^2 ∣ p := by
        rw [g₄] at h₃
        exact h₃
      have gp: 0 < p := by exact Prime.pos hp
      have h₅: p^2 ≤ p := by exact Nat.le_of_dvd gp h₄
      have g₆: 1 < p := by exact Prime.one_lt hp
      have h₆: p^1 < p^2 := by exact Nat.pow_lt_pow_succ g₆
      linarith
