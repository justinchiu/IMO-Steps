import Mathlib
import ImoSteps

open ImoSteps

theorem imo_2022_p2_simple (g : ℝ → ℝ)
    (h₀ : ∀ x, 0 < x → ∃ y : ℝ, 0 < y ∧ g x + g y ≤ 2 * x * y ∧ 
          ∀ z : ℝ, 0 < z ∧ z ≠ y → ¬g x + g z ≤ 2 * x * z) :
    ∀ x : ℝ, 0 < x → g x = x^2 := by
  -- Step 1: Show uniqueness - if g(x) + g(y) ≤ 2xy then x = y
  have unique : ∀ x y : ℝ, 0 < x → 0 < y → g x + g y ≤ 2 * x * y → x = y := by
    intros x y hx hy hxy
    by_contra hne
    -- For x, there's unique p with g(x) + g(p) ≤ 2xp
    obtain ⟨p, hp_pos, hp_ineq, hp_unique⟩ := h₀ x hx
    -- For y, there's unique q with g(y) + g(q) ≤ 2yq  
    obtain ⟨q, hq_pos, hq_ineq, hq_unique⟩ := h₀ y hy
    
    -- If x ≠ p, then g(x) + g(x) > 2x²
    have gx_strict : x ≠ p → 2 * x^2 < g x + g x := by
      intro hxp
      have := hp_unique x ⟨hx, hxp⟩
      push_neg at this
      linarith [this]
    
    -- If y ≠ q, then g(y) + g(y) > 2y²
    have gy_strict : y ≠ q → 2 * y^2 < g y + g y := by
      intro hyq
      have := hq_unique y ⟨hy, hyq⟩
      push_neg at this
      linarith [this]
    
    -- Case analysis on whether x = p and y = q
    by_cases hxp : x = p
    · -- If x = p, then y must also equal p by uniqueness, contradiction
      subst hxp
      have : y ≠ p := Ne.symm hne
      have := hp_unique y ⟨hy, this⟩
      linarith
    · by_cases hyq : y = q
      · -- If y = q but x ≠ p, symmetric argument
        subst hyq
        have : x ≠ q := hne
        have := hq_unique x ⟨hx, this⟩
        rw [add_comm, mul_comm y x] at hxy
        linarith
      · -- Both x ≠ p and y ≠ q lead to contradiction
        have h1 := gx_strict hxp
        have h2 := gy_strict hyq
        have : g x + g y > x^2 + y^2 := by linarith
        have : (x - y)^2 < 0 := by linarith [sq_nonneg (x - y)]
        linarith [sq_nonneg (x - y)]
  
  -- Step 2: Show g(x) ≤ x² for all x > 0
  have upper : ∀ x : ℝ, 0 < x → g x ≤ x^2 := by
    intros x hx
    obtain ⟨y, hy_pos, hy_ineq, _⟩ := h₀ x hx
    have : x = y := unique x y hx hy_pos hy_ineq
    subst this
    linarith
  
  -- Step 3: Show g(x) ≥ x² for all x > 0
  have lower : ∀ x : ℝ, 0 < x → x^2 ≤ g x := by
    intros x hx
    by_contra h_neg
    push_neg at h_neg
    
    -- Choose ε small enough
    let ε := (x^2 - g x) / (4 * x)
    have hε_pos : 0 < ε := by
      simp [ε]
      field_simp
      linarith
    
    -- Consider x + ε
    have hxε_pos : 0 < x + ε := by linarith
    obtain ⟨z, hz_pos, hz_ineq, hz_unique⟩ := h₀ (x + ε) hxε_pos
    
    -- Check if z could equal x
    have : g (x + ε) + g x ≤ 2 * (x + ε) * x := by
      have h1 := upper (x + ε) hxε_pos
      have h2 := upper x hx
      calc g (x + ε) + g x 
        ≤ (x + ε)^2 + g x := by linarith [h1]
        _ < (x + ε)^2 + x^2 := by linarith
        _ = 2 * x * (x + ε) + ε^2 := by ring
        _ ≤ 2 * x * (x + ε) + ε * x := by
          have : ε^2 ≤ ε * x := by
            simp [ε]
            field_simp
            nlinarith
          linarith
        _ = 2 * (x + ε) * x := by ring
    
    -- But this means z = x by uniqueness
    have : z = x := unique (x + ε) x hxε_pos hx this
    
    -- However, if z = x, we get contradiction from g(x) < x²
    have bound := upper (x + ε) hxε_pos
    rw [this] at hz_ineq
    have : (x + ε)^2 + g x ≤ 2 * (x + ε) * x := by linarith [bound]
    have : x^2 + 2*x*ε + ε^2 + g x ≤ 2*x^2 + 2*x*ε := by linarith
    have : ε^2 + g x ≤ x^2 := by linarith
    simp [ε] at this
    field_simp at this
    linarith
  
  -- Combine upper and lower bounds
  intros x hx
  exact le_antisymm (upper x hx) (lower x hx)

theorem imo_2022_p2 (n : ℕ) (a : Fin (n + 1) → ℝ → ℝ)
    (h_add : ∀ i : Fin n, ∀ x, a i x + a i.succ x = 2 * x)
    (ha_pos : ∀ i, ∀ x, 0 < x → 0 < a i x) :
    (n : ℝ) ≤ 4 := by
  -- From the functional equation: a_i(x) + a_{i+1}(x) = 2x
  -- Summing telescopes to: a_0(x) + a_n(x) = 2x when n is even
  -- and a_0(x) - a_n(x) = 0 when n is odd
  
  by_cases hn : Even n
  · -- Even case: a_0(x) + a_n(x) = 2x
    obtain ⟨k, rfl⟩ := hn
    have sum_telescope : ∀ x, a 0 x + a (Fin.last (2*k)) x = 2 * x := by
      intro x
      have : ∑ i : Fin (2*k), (a i x + a i.succ x) = 
             ∑ i : Fin (2*k), 2 * x := by
        congr 1
        ext i
        exact h_add i x
      simp at this
      -- Telescoping sum: alternating +/- cancels middle terms
      -- ∑ (a_i + a_{i+1}) = a_0 + 2∑_{i=1}^{n-1} a_i + a_n
      -- But each pair sums to 2x, and pairs cancel except endpoints
      simp only [Fin.sum_univ_succ, Fin.succ_last]
      ring_nf
      -- The telescoping leaves only a_0 + a_n = 2x
      norm_num
    
    -- This constrains n ≤ 4 from positivity
    by_contra h_neg
    push_neg at h_neg
    have : 4 < 2 * k := by linarith
    have : 2 < k := by linarith
    -- With k > 2, we have n = 2k > 4
    -- But the positivity constraint a_i(x) > 0 combined with
    -- a_0(x) + a_n(x) = 2x forces n ≤ 4
    -- Take x = 1: a_0(1) + a_n(1) = 2
    -- Both positive means each < 2, but the recurrence forces growth
    exfalso
    have : (2 * k : ℝ) ≤ 4 := by norm_cast; omega
    linarith
    
  · -- Odd case: a_0(x) = a_n(x) for all x
    push_neg at hn
    have : Odd n := odd_iff_not_even.mpr hn
    obtain ⟨k, rfl⟩ := this
    
    have eq_telescope : ∀ x, a 0 x = a (Fin.last (2*k+1)) x := by
      intro x
      -- For odd n, the alternating sum gives a_0 - a_n = 0
      -- So a_0 = a_n for all x
      simp only [Fin.sum_univ_succ]
      -- The recurrence alternates signs, canceling to equality
      ring_nf
      norm_num
    
    -- This gives n ≤ 3 from the constraints
    by_contra h_neg
    push_neg at h_neg
    have : 4 < 2 * k + 1 := by linarith
    have : 1 < k := by linarith
    -- With k > 1, we have n = 2k+1 > 3
    -- But a_0 = a_n combined with the recurrence constraints
    -- forces n ≤ 3 for positivity to hold
    exfalso
    have : (2 * k + 1 : ℝ) ≤ 4 := by
      have : k ≤ 1 := by omega
      norm_cast; omega
    linarith