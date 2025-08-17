import Mathlib

open Int Rat

-- Helper for bounding the ratio
lemma product_ratio_bound (p q r : ℤ) (hp : 1 < p) (hq : p < q) (hr : q < r) :
    (p * q * r : ℚ) / ((p - 1) * (q - 1) * (r - 1)) < 2 := by
  have hp' : 2 ≤ p := hp
  have hq' : p + 1 ≤ q := by omega
  have hr' : q + 1 ≤ r := by omega
  
  -- Key observation: the ratio decreases as p,q,r increase
  -- Maximum is at p=2, q=3, r=4
  calc (p * q * r : ℚ) / ((p - 1) * (q - 1) * (r - 1))
    ≤ (p : ℚ) / (p - 1) * (q : ℚ) / (q - 1) * (r : ℚ) / (r - 1) := by
      field_simp; ring_nf
    _ ≤ 2 / 1 * (q : ℚ) / (q - 1) * (r : ℚ) / (r - 1) := by
      gcongr; norm_cast; omega
    _ ≤ 2 * 3 / 2 * (r : ℚ) / (r - 1) := by
      gcongr; norm_cast; omega
    _ ≤ 2 * 3 / 2 * 4 / 3 := by
      gcongr; norm_cast; omega
    _ = 2 := by norm_num

theorem imo_1992_p1 (p q r : ℤ)
    (h₀ : 1 < p ∧ p < q ∧ q < r)
    (h₁ : (p - 1) * (q - 1) * (r - 1) ∣ (p * q * r - 1)) :
    (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  obtain ⟨k, hk⟩ := h₁
  
  -- k must be positive
  have hk_pos : 0 < k := by
    have : 0 < p * q * r - 1 := by omega
    have : 0 < (p - 1) * (q - 1) * (r - 1) := by omega
    rw [← hk] at this
    exact pos_of_mul_pos_left this (by omega)
  
  -- Upper bound on k
  have hk_upper : k < 2 := by
    have : (k : ℚ) = (p * q * r - 1 : ℚ) / ((p - 1) * (q - 1) * (r - 1)) := by
      field_simp; norm_cast; rw [mul_comm]; exact hk
    calc (k : ℚ) = (p * q * r - 1 : ℚ) / ((p - 1) * (q - 1) * (r - 1)) := this
      _ < (p * q * r : ℚ) / ((p - 1) * (q - 1) * (r - 1)) := by
        apply div_lt_div_of_pos_right
        · norm_cast; omega
        · norm_cast; omega
      _ < 2 := product_ratio_bound p q r h₀.1 h₀.2.1 h₀.2.2
  
  -- So k = 1
  have : k = 1 := by omega
  rw [this, mul_one] at hk
  
  -- Now we have (p-1)(q-1)(r-1) = pqr - 1
  -- Expanding: pqr - pq - pr - qr + p + q + r - 1 = pqr - 1
  -- So: pq + pr + qr = p + q + r
  
  have key_eq : p * q + p * r + q * r = p + q + r := by
    have : (p - 1) * (q - 1) * (r - 1) = p * q * r - 1 := hk
    ring_nf at this ⊢
    linarith
  
  -- Case analysis on p (we know p ≥ 2)
  have hp_bound : p ≤ 3 := by
    by_contra
    have : 4 ≤ p := by omega
    -- If p ≥ 4, q ≥ 5, r ≥ 6, then the equation has no solution
    have : 5 ≤ q := by omega
    have : 6 ≤ r := by omega
    -- The ratio p*q + p*r + q*r over p + q + r is too large
    have : p + q + r < p * q + p * r + q * r := by nlinarith
    linarith [key_eq]
  
  interval_cases p
  · -- p = 2
    have : q * r = 2 * (q + r) := by simp at key_eq; linarith
    have : (q - 2) * (r - 2) = 4 := by linarith
    -- Since q > 2 and r > q, we need positive factors of 4
    have hq2 : 0 < q - 2 := by omega
    have hr2 : q - 2 ≤ r - 2 := by omega
    -- Factors of 4: (1,4) or (2,2)
    have : (q - 2 = 1 ∧ r - 2 = 4) ∨ (q - 2 = 2 ∧ r - 2 = 2) := by
      have : q - 2 ∣ 4 := ⟨r - 2, by linarith⟩
      interval_cases (q - 2) <;> simp_all
    cases this with
    | inl h => 
      -- q = 3, r = 6, but we need to check if this works
      have hq : q = 3 := by omega
      have hr : r = 6 := by omega
      -- Check: 2*3 + 2*6 + 3*6 = 6 + 12 + 18 = 36
      --        2 + 3 + 6 = 11, but 36 ≠ 11
      rw [hq, hr] at key_eq
      norm_num at key_eq -- This shows 36 = 11 which is false
    | inr h =>
      -- q = 4, r = 4, but we need q < r so this is impossible
      have : q = 4 ∧ r = 4 := by omega
      have : q < r := h₀.2.2.1
      omega -- Contradiction since q = r = 4
      
  · -- p = 3
    have : 2 * q * r = 3 * (q + r) := by simp at key_eq; linarith
    have : (2 * q - 3) * (2 * r - 3) = 9 := by linarith
    -- Since q > 3 and r > q, we have 2q - 3 > 3 and 2r - 3 > 2q - 3
    have : 3 < 2 * q - 3 := by omega
    have : 2 * q - 3 ≤ 2 * r - 3 := by omega
    -- Only factor of 9 with first factor > 3 is impossible
    -- Actually, if q = 5, then 2*5 - 3 = 7, which doesn't divide 9
    -- Let's reconsider: q ≥ 4
    have : 4 ≤ q := by omega
    have : 5 ≤ 2 * q - 3 := by omega
    -- But 9 = 1*9 = 3*3, and we need first factor ≥ 5
    -- This is impossible
    have : 2 * q - 3 ∣ 9 := ⟨2 * r - 3, by linarith⟩
    have : 2 * q - 3 ∈ ({1, 3, 9} : Finset ℤ) := by
      simp [Finset.mem_insert, Finset.mem_singleton]
      -- Show that divisors of 9 are exactly {1, 3, 9}
      have div9 : 2 * q - 3 ∣ 9 := this
      have pos : 0 < 2 * q - 3 := by omega
      -- If d | 9 and d > 0, then d ∈ {1,3,9}
      have h9 : 2 * q - 3 ≤ 9 := by
        apply Nat.le_of_dvd
        · norm_num
        · exact Int.coe_nat_dvd.mp div9
      have hge5 : 5 ≤ 2 * q - 3 := by omega
      -- But we have 5 ≤ 2q - 3 ≤ 9, so 2q - 3 ∈ {5,6,7,8,9}
      -- Only 9 divides 9 from this set
      interval_cases (2 * q - 3) using hge5, h9
      · norm_num at div9 -- 5 doesn't divide 9
      · norm_num at div9 -- 6 doesn't divide 9  
      · norm_num at div9 -- 7 doesn't divide 9
      · norm_num at div9 -- 8 doesn't divide 9
      · left; right; right; rfl -- 9 = 9
    simp at this
    cases this with
    | inl h => omega -- 2q - 3 = 1 means q = 2, contradiction
    | inr h => 
      cases h with
      | inl h => 
        -- 2q - 3 = 3 means q = 3, contradiction with p < q
        omega
      | inr h =>
        -- 2q - 3 = 9 means q = 6, then 2r - 3 = 1 means r = 2
        -- But we need q < r, contradiction
        have : q = 6 := by linarith
        have : 2 * r - 3 = 1 := by linarith
        have : r = 2 := by linarith
        omega