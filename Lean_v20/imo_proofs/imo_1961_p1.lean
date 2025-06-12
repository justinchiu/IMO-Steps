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




open Real


/- Solve the system of equations:\n
$\n\\begin{matrix}\n\\quad x + y + z \\!\\!\\! &= a \\; \\, \\\\\nx^2 +y^2+z^2 \\!\\!\\! &=b^2 \\\\\n\\qquad \\qquad xy \\!\\!\\!  &= z^2\n\\end{matrix}\n$\n</center>\n\nwhere $a $ and $b $ are constants.  Give the conditions that $a $ and $b $ must satisfy so that $x, y, z $ (the solutions of the system) are distinct positive numbers.
Prove the following three conditions must hold:
1. a must be positive
2. b ^ 2 < a ^ 2
3. a^2 < 3 * b^2 -/

theorem imo_1961_p1
  (x y z a b : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x ≠ y)
  (h₂ : y ≠ z)
  (h₃ : z ≠ x)
  (h₄ : x + y + z = a)
  (h₅ : x^2 + y^2 + z^2 = b^2)
  (h₆ : x * y = z^2) :
  0 < a ∧ b^2 < a^2 ∧ a^2 < 3 * b^2 := by
  have ha: 0 < a := by linarith
  constructor
  . linarith
  . have h₇: (x + y + z) * (x + y - z) = b ^ 2 := by
      rw [← sq_sub_sq, ← h₆, add_sq]
      linarith
    have h₈: (x + y - z) = b ^ 2 / a := by
      rw [h₄] at h₇
      refine (eq_div_iff ?_).mpr ?_
      . exact Ne.symm (ne_of_lt ha)
      . rw [mul_comm] at h₇
        exact h₇
    have h₉: z = (a ^ 2 - b ^ 2) / (2 * a) := by
      have g₀: x + y = (a + b ^ 2 / a) / 2 := by linarith
      rw [g₀, add_div, div_div] at h₄
      rw [sub_div, mul_comm 2 a, ← div_div, pow_two, mul_self_div_self]
      linarith
    have h₁₀: b ^ 2 < a ^ 2 := by
      apply and_assoc.mpr at h₀
      cases' h₀ with h₀ hz
      rw [h₉] at hz
      apply div_pos_iff.mp at hz
      refine lt_of_sub_pos ?_
      cases' hz with hzc hzf
      . exact hzc.1
      . exfalso
        linarith
    have h₁₁: y ^ 2 + (-(a ^ 2 + b ^ 2) / (2 * a)) * y + ((a ^ 2 - b ^ 2) / (2 * a)) ^ 2 = 0 := by
      have g₀: x + y = (a + b ^ 2 / a) / 2 := by linarith
      rw [add_div, div_div] at g₀
      have g₁: x = a / 2 + b ^ 2 / (a * 2) - y := by linarith
      rw [g₁, h₉, sub_mul, add_mul, ← pow_two y] at h₆
      rw [neg_add', sub_div, neg_div, pow_two a, mul_div_mul_right a 2 (by linarith), sub_mul, neg_mul]
      rw [add_sub_assoc', ← sub_eq_add_neg, add_comm]
      refine add_eq_of_eq_sub ?_
      rw [zero_sub, ← pow_two a, ← h₆]
      ring_nf
    let aq : ℝ := 1
    let bq : ℝ := (-(a ^ 2 + b ^ 2) / (2 * a))
    let cq : ℝ := ((a ^ 2 - b ^ 2) / (2 * a)) ^ 2
    have haq : aq = 1 := by rfl
    have hbq : bq = (-(a ^ 2 + b ^ 2) / (2 * a)) := by rfl
    have hcq : cq = ((a ^ 2 - b ^ 2) / (2 * a)) ^ 2 := by rfl
    have h₁₂: aq * y ^ 2 + bq * y + cq = 0 := by
      rw [one_mul]
      exact h₁₁
    rw [pow_two] at h₁₂
    have h₁₃: (2 * aq * y + bq) ^ 2 = bq ^ 2 - 4 * aq * cq := by
      rw [add_sq]
      have g₀: (2 * aq * y) ^ 2 + 2 * (2 * aq * y) * bq = 4 * aq * (y ^ 2 + bq * y) := by
        rw [haq, hbq]
        ring_nf
      have g₁: aq = 1 := by rfl
      have g₂: y ^ 2 + bq * y = - cq := by
        rw [← one_mul (y ^ 2), ← g₁]
        linarith
      rw [g₀, g₂]
      linarith
    let s : ℝ := ((3 * a ^ 2 - b ^ 2) * (3 * b ^ 2 - a ^ 2)) / (4 * a ^ 2)
    have hs : s = ((3 * a ^ 2 - b ^ 2) * (3 * b ^ 2 - a ^ 2)) / (4 * a ^ 2) := by rfl
    have h₁₄: discrim aq bq cq = s := by
      have g₀: aq ≠ 0 := by exact Ne.symm (zero_ne_one' ℝ)
      apply (quadratic_eq_zero_iff_discrim_eq_sq g₀ y).mp at h₁₂
      rw [h₁₂, h₁₃]
      rw [haq, hbq, hcq, hs]
      ring_nf
    rw [← one_mul (y ^ 2), pow_two] at h₁₁
    apply (quadratic_eq_zero_iff_discrim_eq_sq (by linarith) y).mp at h₁₁
    constructor
    . exact h₁₀
    . by_contra! hc
      have hc₀: (3 * b ^ 2 - a ^ 2) ≤ 0 := by linarith
      have hc₁: 0 < (3 * a ^ 2 - b ^ 2) := by
        refine sub_pos_of_lt ?_
        refine lt_trans h₁₀ ?_
        refine lt_mul_left ?_ (by linarith)
        exact sq_pos_of_pos ha
      have hc₂: (3 * a ^ 2 - b ^ 2) * (3 * b ^ 2 - a ^ 2) ≤ 0 := by
        exact Linarith.mul_nonpos hc₀ hc₁
      have hc₃: s ≤ 0 := by
        refine div_nonpos_iff.mpr ?_
        right
        constructor
        . exact hc₂
        . refine mul_nonneg (by linarith) ?_
          exact sq_nonneg a
      rw [← h₁₄] at hc₃
      have h₁₅: aq ≠ 0 := by exact Ne.symm (zero_ne_one' ℝ)
      by_cases hc₄: s < 0
      . have hc₅: ∀ d:ℝ , discrim aq bq cq ≠ d ^ 2 := by
          intro d
          rw [h₁₄]
          have hc₆: 0 ≤ d ^ 2 := by exact sq_nonneg d
          linarith
        exfalso
        exact hc₅ ((2 : ℝ) * (1 : ℝ) * y + -(a ^ (2 : ℕ) + b ^ (2 : ℕ)) / ((2 : ℝ) * a)) h₁₁
      . have hc₅: s = 0 := by linarith
        rw [← h₁₄] at hc₅
        have h₁₆: y = -bq / (2 * aq) := by
          exact (quadratic_eq_zero_iff_of_discrim_eq_zero h₁₅ hc₅ y).mp h₁₂
        have h₁₇: y = (a ^ 2 + b ^ 2) / (2 * a) / 2 := by
          rw [h₁₆, haq, hbq]
          ring_nf
        have h₁₈: x = (a ^ 2 + b ^ 2) / (2 * a) - y := by
          rw [mul_comm, ← div_div, add_div, pow_two a, mul_self_div_self]
          linarith
        have h₁₉: x = y := by linarith
        exfalso
        exact h₁ h₁₉
