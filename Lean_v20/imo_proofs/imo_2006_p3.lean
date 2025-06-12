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


/- Show that for any real numbers $a$, $b$, and $c$,
  we have $(ab(a^2 - b^2)) + (bc(b^2 - c^2)) + (ca(c^2 - a^2)) \\leq \\frac{9\\sqrt{2}}{32}(a^2 + b^2 + c^2)^2$.-/


open Real



theorem imo_2006_p3
  (a b c : ℝ) :
  abs ((a * b * (a^2 - b^2)) + (b * c * (b^2 - c^2)) + (c * a * (c^2 - a^2)))
    ≤ (9 * Real.sqrt 2) / 32 * (a^2 + b^2 + c^2) ^ 2 := by
  have h₀: (a * b * (a^2 - b^2)) + (b * c * (b^2 - c^2)) + (c * a * (c^2 - a^2)) =
    (a - b) * (b - c) * (a - c) * (a + b + c) := by
    ring_nf
  have h₃: 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2 := by
    refine add_nonneg ?_ ?_
    . refine add_nonneg ?_ ?_
      . exact sq_nonneg (a - b)
      . exact sq_nonneg (b - c)
    . exact sq_nonneg (a - c)
  have h₄: abs ((a - b) * (b - c) * (a - c) * (a + b + c)) ≤ (1:ℝ) / 4 * 2 ^ ((3:ℝ)/2) *
    ((((a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2)/ 3) ^ ((3:ℝ)/4) * ((a + b + c) ^ (2)) ^ ((1:ℝ)/4) ) ^ (2)  := by
    rw [mul_pow, ]
    have h₄₀: ((((a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2) / 3) ^ ((3:ℝ) / 4)) ^ 2 =
      (((a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2) / 3) ^ ((3:ℝ) / 2) := by
      rw [← rpow_natCast, ← rpow_mul (by linarith)]
      norm_num
    have h₄₁ : (((a + b + c) ^ 2) ^ ((1:ℝ) / 4)) ^ 2 = abs (a + b + c) := by
      rw [← sqrt_sq_eq_abs, ← rpow_natCast (((a + b + c) ^ 2) ^ ((1:ℝ) / 4)), ← rpow_mul ?_]
      . rw [one_div_mul_eq_div, sqrt_eq_rpow]
        norm_num
      . exact sq_nonneg (a + b + c)
    by_cases he₀: a ≠ b ∧ a ≠ c ∧ b ≠ c
    . let s : Finset ℝ := {a, b, c}
      have hs₀: s.Nonempty := by exact Finset.insert_nonempty a {b, c}
      have hs₁: s = {a, b, c} := by rfl
      have hs₂: ∀ i ∈ s, i = a ∨ i = b ∨ i = c := by
        rw [hs₁]
        intros i hi
        simp_all only [Finset.mem_insert, Finset.mem_singleton]
      have hs₃: s.card = 3 := by
        refine Finset.card_eq_three.mpr ?_
        use a
        use b
        use c
        constructor
        . exact he₀.1
        constructor
        . exact he₀.2.1
        constructor
        . exact he₀.2.2
        . exact hs₁
      let z : ℝ := s.min' hs₀
      let x : ℝ := s.max' hs₀
      let sy : Finset ℝ := s \ {x,z}
      have hsy₀: sy.Nonempty := by
        have g₀: s = s ∪ ({x,z}:Finset ℝ) := by
          refine Finset.left_eq_union.mpr ?_
          intros d hd₀
          have hd₁: d = x ∨ d = z := by simp_all only [Finset.mem_insert, Finset.mem_singleton]
          cases' hd₁ with hd₁ hd₁
          . rw [hd₁]
            exact Finset.max'_mem s hs₀
          . rw [hd₁]
            exact Finset.min'_mem s hs₀
        have g₁: ({x,z}:Finset ℝ).card = 2 := by
          refine Finset.card_eq_two.mpr ?_
          use x
          use z
          constructor
          . by_contra hc₀
            have hc₁: s.min' ?_ < s.max' ?_ := by
              refine Finset.min'_lt_max'_of_card s ?_
              rw [hs₃]
              decide
            linarith
          . exact rfl
        have g₂: sy = s \ {x,z} := by rfl
        have g₃: sy.card + ({x,z}:Finset ℝ).card = s.card := by
          rw [g₀, g₂]
          exact Finset.card_sdiff_add_card s ({x,z}:Finset ℝ)
        rw [hs₃, g₁] at g₃
        simp at g₃
        refine Finset.one_le_card.mp ?_
        exact Nat.le_of_eq (id (Eq.symm g₃))
      let y : ℝ := (s \ {x,z}).min' hsy₀
      have hy: y ∈ s := by
        have hsy₁: sy ⊆ s := by exact Finset.sdiff_subset
        refine Finset.mem_of_subset hsy₁ ?_
        exact Finset.min'_mem sy hsy₀
      have hx: x ∈ s := by exact Finset.max'_mem s hs₀
      have hz: z ∈ s := by exact Finset.min'_mem s hs₀
      have hxz: x ≠ z := by
        refine ne_of_gt ?_
        refine Finset.min'_lt_max'_of_card s ?_
        rw [hs₃]
        decide
      have hxy: x ≠ y := by
        by_contra hc₀
        have hc₁: ({y, z}:Finset ℝ) = {y} ∪ {z} := by rfl
        have hc₂: sy = s \ {x, z} := by rfl
        rw [hc₀] at hc₂
        have hc₃: y ∉ sy := by
          rw [hc₂]
          refine Finset.not_mem_sdiff_of_mem_right ?_
          rw [hc₁]
          simp_all only [Finset.mem_union, Finset.mem_singleton, true_or]
        have hc₄: y ∈ sy := by exact Finset.min'_mem sy hsy₀
        exact hc₃ hc₄
      have hyz: z ≠ y := by
        by_contra hc₀
        have hc₁: ({x, y}:Finset ℝ) = {x} ∪ {y} := by rfl
        have hc₂: sy = s \ {x, z} := by rfl
        rw [hc₀] at hc₂
        have hc₃: y ∉ sy := by
          rw [hc₂]
          refine Finset.not_mem_sdiff_of_mem_right ?_
          rw [hc₁]
          simp_all only [Finset.mem_union, Finset.mem_singleton, or_true]
        have hc₄: y ∈ sy := by exact Finset.min'_mem sy hsy₀
        exact hc₃ hc₄
      have hs₄: (x = a ∧ y = b ∧ z = c) ∨ (x = a ∧ y = c ∧ z = b) ∨ (x = b ∧ y = a ∧ z = c)
        ∨ (x = b ∧ y = c ∧ z = a) ∨ (x = c ∧ y = a ∧ z = b) ∨ (x = c ∧ y = b ∧ z = a) := by
        clear h₀ h₄₀ h₄₁ hs₃ h₃ he₀ hs₁
        cases' hs₂ x hx with gx gx
        . cases' hs₂ y hy with gy gy
          . exfalso
            rw [gx, gy] at hxy
            apply hxy
            rfl
          . cases' gy with gy gy
            . left
              cases' hs₂ z hz with gz gz
              . exfalso
                rw [gx, gz] at hxz
                apply hxz
                rfl
              . cases' gz with gz gz
                . exfalso
                  rw [gy, gz] at hyz
                  apply hyz
                  rfl
                . constructor
                  . exact gx
                  . exact ⟨gy, gz⟩
            . right
              left
              cases' hs₂ z hz with gz gz
              . exfalso
                rw [gx, gz] at hxz
                apply hxz
                rfl
              . cases' gz with gz gz
                . constructor
                  . exact gx
                  . exact ⟨gy, gz⟩
                . exfalso
                  rw [gy, gz] at hyz
                  apply hyz
                  rfl
        . right
          right
          cases' gx with gx gx
          . cases' hs₂ y hy with gy gy
            . cases' hs₂ z hz with gz gz
              . exfalso
                rw [gy, gz] at hyz
                apply hyz
                rfl
              . cases' gz with gz gz
                . exfalso
                  rw [gx, gz] at hxz
                  apply hxz
                  rfl
                . left
                  constructor
                  . exact gx
                  . exact ⟨gy, gz⟩
            . cases' gy with gy gy
              . exfalso
                rw [gx, gy] at hxy
                apply hxy
                rfl
              . right
                left
                cases' hs₂ z hz with gz gz
                . constructor
                  . exact gx
                  . exact ⟨gy, gz⟩
                . exfalso
                  cases' gz with gz gz
                  . rw [gx, gz] at hxz
                    apply hxz
                    rfl
                  . rw [gy, gz] at hyz
                    apply hyz
                    rfl
          . right
            right
            cases' hs₂ y hy with gy gy
            . left
              cases' hs₂ z hz with gz gz
              . exfalso
                rw [gy, gz] at hyz
                apply hyz
                rfl
              . cases' gz with gz gz
                . constructor
                  . exact gx
                  . exact ⟨gy, gz⟩
                . exfalso
                  rw [gx, gz] at hxz
                  apply hxz
                  rfl
            . cases' gy with gy gy
              . cases' hs₂ z hz with gz gz
                . right
                  constructor
                  . exact gx
                  . exact ⟨gy, gz⟩
                . exfalso
                  cases' gz with gz gz
                  . rw [gy, gz] at hyz
                    apply hyz
                    rfl
                  . rw [gx, gz] at hxz
                    apply hxz
                    rfl
              . exfalso
                rw [gx, gy] at hxy
                apply hxy
                rfl
      have h₄₂: (abs (x - z)) ^ 3 ≤ (2 * ((a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2) / 3) ^ ((3:ℝ)/2) := by
        have h₄₃: |x - z| ^ 3 = ((abs (x - z)) ^ 2) ^ ((3:ℝ)/2) := by
          rw [← rpow_natCast _ 2, ← rpow_mul ?_]
          . simp
            rw [← mul_div_assoc]
            norm_num
            norm_cast
          . exact abs_nonneg (x - z)
        rw [h₄₃]
        refine rpow_le_rpow ?_ ?_ ?_
        . exact sq_nonneg |x - z|
        . refine (le_div_iff₀ (by linarith)).mpr ?_
          rw [mul_comm _ 3, sq_abs]
          have h₄₄: ((a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2) = ((x - y) ^ 2 + (y - z) ^ 2 + (x - z) ^ 2) := by
            cases' hs₄ with g₀ g₀
            . rw [g₀.1, g₀.2.1, g₀.2.2]
            cases' g₀ with g₀ g₀
            . rw [g₀.1, g₀.2.1, g₀.2.2]
              linarith
            cases' g₀ with g₀ g₀
            . rw [g₀.1, g₀.2.1, g₀.2.2]
              linarith
            cases' g₀ with g₀ g₀
            . rw [g₀.1, g₀.2.1, g₀.2.2]
              linarith
            cases' g₀ with g₀ g₀
            . rw [g₀.1, g₀.2.1, g₀.2.2]
              linarith
            . rw [g₀.1, g₀.2.1, g₀.2.2]
              linarith
          rw [h₄₄]
          have h₄₅: ((x - y) + (y - z)) ^ 2 ≤ 2 * ((x - y) ^ 2 + (y - z) ^ 2) := by
            exact add_sq_le
          simp at h₄₅
          linarith
        . linarith
      have h₄₃: abs ((a - b) * (b - c) * (a - c)) ≤ ((1:ℝ) / 4) * (abs (x - z)) ^ 3 := by
        have hxyp: 0 ≤ x - y := by
          refine sub_nonneg_of_le ?_
          exact Finset.le_max' s y hy
        have hyzp: 0 ≤ y - z := by
          refine sub_nonneg_of_le ?_
          exact Finset.min'_le s y hy
        have h₄₄: abs ((a - b) * (b - c) * (a - c)) = abs ((x - y) * (y - z) * (x - z)) := by
          repeat rw [abs_mul]
          cases' hs₄ with g₀ g₀
          . rw [g₀.1, g₀.2.1, g₀.2.2]
          cases' g₀ with g₀ g₀
          . rw [g₀.1, g₀.2.1, g₀.2.2]
            rw [abs_sub_comm c b]
            linarith
          cases' g₀ with g₀ g₀
          . rw [g₀.1, g₀.2.1, g₀.2.2]
            rw [abs_sub_comm b a]
            linarith
          cases' g₀ with g₀ g₀
          . rw [g₀.1, g₀.2.1, g₀.2.2]
            rw [abs_sub_comm b a, abs_sub_comm c a]
            linarith
          cases' g₀ with g₀ g₀
          . rw [g₀.1, g₀.2.1, g₀.2.2]
            rw [abs_sub_comm c b, abs_sub_comm c a]
            linarith
          . rw [g₀.1, g₀.2.1, g₀.2.2]
            rw [abs_sub_comm c b, abs_sub_comm b a, abs_sub_comm c a]
            linarith
        rw [h₄₄, abs_mul, pow_succ, ← mul_assoc]
        refine mul_le_mul ?_ ?_ ?_ ?_
        . rw [one_div_mul_eq_div]
          refine (le_div_iff₀ (by linarith)).mpr ?_
          rw [mul_comm _ 4,abs_mul, ← mul_assoc]
          have h₄₅: 4 * |x - y| * |y - z| ≤ (|x - y| + |y - z|) ^ 2 := by
            exact four_mul_le_sq_add |x - y| |y - z|
          refine le_trans h₄₅ ?_
          refine sq_le_sq.mpr ?_
          rw [abs_abs, abs_of_nonneg hxyp, abs_of_nonneg hyzp, sub_add_sub_cancel]
        . rw [abs_sub_comm]
        . exact abs_nonneg (x - z)
        . refine mul_nonneg (by linarith) ?_
          exact sq_nonneg |x - z|
      rw [h₄₀, h₄₁, ← mul_assoc, mul_assoc (1/4), abs_mul, ← mul_rpow]
      refine mul_le_mul ?_ ?_ ?_ ?_
      all_goals try linarith
      . refine le_trans h₄₃ ?_
        refine (mul_le_mul_left (by linarith)).mpr ?_
        rw [← mul_div_assoc ]
        exact h₄₂
      . exact abs_nonneg (a + b + c)
      . refine mul_nonneg (by linarith) ?_
        refine rpow_nonneg ?_ ((3:ℝ)/2)
        refine mul_nonneg (by linarith) ?_
        refine div_nonneg h₃ (by linarith)
    . push_neg at he₀
      have h₄₂: 0 ≤
        (1:ℝ) / 4 * 2 ^ ((3:ℝ) / 2) *
        (((((a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2) / 3) ^ ((3:ℝ) / 4)) ^ 2 * (((a + b + c) ^ 2) ^ ((1:ℝ) / 4)) ^ 2) := by
        refine mul_nonneg ?_ ?_
        . refine mul_nonneg ?_ ?_
          . linarith
          . refine rpow_nonneg (by linarith) ((3:ℝ)/2)
        . rw [← mul_pow]
          refine pow_nonneg ?_ 2
          refine mul_nonneg ?_ ?_
          . refine rpow_nonneg (by linarith) ((3:ℝ)/4)
          . refine rpow_nonneg ?_ ((1:ℝ)/4)
            exact sq_nonneg (a + b + c)
      by_cases he₁: a ≠ b ∧ a ≠ c
      . have he₂: b = c := by exact he₀ he₁.1 he₁.2
        refine le_of_eq_of_le ?_ h₄₂
        rw [he₂, sub_self, mul_zero, zero_mul, zero_mul, abs_of_nonneg (by linarith)]
      . push_neg at he₁
        by_cases he₂: a ≠ b
        . have he₃: a = c := by exact he₁ he₂
          refine le_of_eq_of_le ?_ h₄₂
          rw [he₃, sub_self, mul_zero, zero_mul, abs_of_nonneg (by linarith)]
        . refine le_of_eq_of_le ?_ h₄₂
          push_neg at he₂
          rw [he₂, sub_self, zero_mul, zero_mul, zero_mul, abs_of_nonneg (by linarith)]
  have h₅: (((a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2)/ 3) ^ ((3:ℝ)/4) * ((a + b + c) ^ (2)) ^ ((1:ℝ)/4) ≤
    (3/4) * (((a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2)/ 3) + ((1:ℝ)/4) * (a + b + c) ^ (2) := by
    refine geom_mean_le_arith_mean2_weighted ?_ ?_ ?_ ?_ ?_
    all_goals try linarith
    exact sq_nonneg (a + b + c)
  rw [div_mul_div_comm, mul_comm 4 3, ← div_mul_div_comm, div_self (by linarith), one_mul, one_div_mul_eq_div, ← add_div] at h₅
  have h₆: (a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2 + (a + b + c) ^ 2 = 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    ring_nf
  rw [h₆] at h₅
  have h₇: abs ((a - b) * (b - c) * (a - c) * (a + b + c)) ≤ (1:ℝ) / 4 * 2 ^ ((3:ℝ)/2) * (3 * (a ^ 2 + b ^ 2 + c ^ 2) / 4) ^ 2 := by
    refine le_trans h₄ ?_
    refine (mul_le_mul_left ?_).mpr ?_
    . simp
      refine rpow_pos_of_pos ?_ (3/2)
      linarith
    . refine pow_le_pow_left₀ ?_ h₅ 2
      refine mul_nonneg ?_ ?_
      . refine rpow_nonneg ?_ (3/4)
        refine div_nonneg h₃ (by linarith)
      . refine rpow_nonneg ?_ (1/4)
        exact sq_nonneg (a + b + c)
  rw [h₀]
  refine le_of_le_of_eq h₇ ?_
  rw [div_pow, mul_pow]
  simp
  have h₈: 2 ^ ((3:ℝ) / 2) = 2 * Real.sqrt 2 := by
    have h₈₀: (3:ℝ) = 2 + 1 := by linarith
    rw [h₈₀, add_div, rpow_add, sqrt_eq_rpow]
    simp
    linarith
  rw [h₈, mul_div_right_comm, ← mul_assoc]
  refine mul_eq_mul_right_iff.mpr ?_
  left
  ring_nf
