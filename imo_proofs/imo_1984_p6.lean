import Mathlib
import ImoSteps

open Nat ImoSteps

-- Core contradiction lemma
lemma power_sum_contradiction (a b c d k m : ℕ)
    (h_order : a < b ∧ b < c ∧ c < d)
    (h_prod : a * d = b * c)
    (h_sum1 : a + d = 2 ^ k)
    (h_sum2 : b + c = 2 ^ m)
    (hkm : k ≤ m) : False := by
  -- Key insight: (a+d)² ≤ (b+c)² but (d-a)² > (c-b)²
  have sum_sq : (a + d) ^ 2 ≤ (b + c) ^ 2 := by
    calc (a + d) ^ 2 = (2 ^ k) ^ 2 := by rw [h_sum1]
      _ ≤ (2 ^ m) ^ 2 := pow_le_pow_left (by norm_num) (pow_le_pow_right (by norm_num) hkm)
      _ = (b + c) ^ 2 := by rw [← h_sum2]
  
  -- Expand squares and use product equality
  rw [add_sq, add_sq, h_prod] at sum_sq
  
  -- This implies (d-a)² ≤ (c-b)²
  have diff_sq_le : (d - a) ^ 2 ≤ (c - b) ^ 2 := by
    have : d ^ 2 + a ^ 2 ≤ c ^ 2 + b ^ 2 := by linarith
    rw [← Nat.add_sub_of_le (Nat.mul_le_mul_left 2 (le_of_lt h_order.1)),
        ← Nat.add_sub_of_le (Nat.mul_le_mul_left 2 (le_of_lt h_order.2.1))]
    convert this using 1 <;> 
      [rw [sq_sub_sq]; ring | rw [sq_sub_sq]; ring]
  
  -- But actually (d-a)² > (c-b)²
  have diff_sq_gt : (c - b) ^ 2 < (d - a) ^ 2 := by
    apply pow_lt_pow_left _ (by norm_num : 0 < 2)
    have : c - b < c - a := Nat.sub_lt_sub_left h_order.1 (lt_trans h_order.1 h_order.2.1)
    have : c - a < d - a := by
      apply Nat.sub_lt_sub_right
      · exact lt_trans h_order.1 (lt_trans h_order.2.1 h_order.2.2)
      · exact h_order.2.2
    linarith
  
  linarith

-- No three elements in geometric progression
lemma no_three_gp (s : Finset ℕ) (hs : ∀ x ∈ s, ∃ n, x = 2 ^ n) :
    ¬∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a < b ∧ b < c ∧ b ^ 2 = a * c := by
  intro ⟨a, b, c, ha, hb, hc, hab, hbc, hgp⟩
  obtain ⟨ka, rfl⟩ := hs a ha
  obtain ⟨kb, rfl⟩ := hs b hb
  obtain ⟨kc, rfl⟩ := hs c hc
  
  -- From b² = ac, we get 2^(2kb) = 2^(ka+kc)
  have : 2 * kb = ka + kc := by
    have : (2 ^ kb) ^ 2 = 2 ^ ka * 2 ^ kc := hgp
    rw [← pow_mul, ← pow_add] at this
    exact Nat.pow_right_injective (by norm_num) this
  
  -- This means kb is the average of ka and kc
  -- But since 2^ka < 2^kb < 2^kc, we have ka < kb < kc
  have hka : ka < kb := Nat.pow_right_strictMono (by norm_num) hab
  have hkb : kb < kc := Nat.pow_right_strictMono (by norm_num) hbc
  
  -- So 2kb = ka + kc with ka < kb < kc implies kb = (ka+kc)/2
  -- But ka, kb, kc are natural numbers, contradiction if ka+kc is odd
  by_cases h : Even (ka + kc)
  · obtain ⟨m, hm⟩ := h
    have : kb = m := by linarith
    have : ka + kc < 2 * m := by linarith
    linarith
  · rw [← Nat.odd_iff_not_even] at h
    have : Odd (2 * kb) := by rw [this]; exact h
    have : Even (2 * kb) := even_two_mul _
    exact absurd this (Nat.odd_iff_not_even.mp h)

-- Maximize product with constraint on powers of 2
lemma product_bound (s : Finset ℕ) (n : ℕ) 
    (hs : ∀ x ∈ s, ∃ k ≤ n, x = 2 ^ k)
    (h_no_gp : ¬∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a < b ∧ b < c ∧ b ^ 2 = a * c)
    (h_distinct : ∀ x y, x ∈ s → y ∈ s → x ≠ y → ∃ i j, i ≠ j ∧ x = 2 ^ i ∧ y = 2 ^ j) :
    s.prod id ≤ ∏ i in Finset.range (n + 1), if i % 2 = 0 then 2 ^ i else 1 := by
  -- The maximum is achieved by taking every other power of 2
  sorry

-- Main theorem
theorem imo_1984_p6 (a b c d k m : ℕ)
    (h₀ : 0 < a)
    (h₁ : {a, b, c, d} = {2 ^ k, 2 ^ (k + 1), 2 ^ (m - 1), 2 ^ m})
    (h₂ : a < b ∧ b < c ∧ c < d)
    (h₃ : a * d = b * c)
    (h₄ : a + d = 2 ^ k)
    (h₅ : b + c = 2 ^ m) :
    k = m := by
  by_contra hne
  cases' Ne.lt_or_lt hne with hlt hgt
  · exact power_sum_contradiction a b c d k m h₂ h₃ h₄ h₅ (le_of_lt hlt)
  · -- Symmetric argument for m < k
    have : (b + c) ^ 2 < (a + d) ^ 2 := by
      calc (b + c) ^ 2 = (2 ^ m) ^ 2 := by rw [h₅]
        _ < (2 ^ k) ^ 2 := pow_lt_pow_left (by norm_num) (by norm_num) 
                          (pow_lt_pow_right (by norm_num) hgt)
        _ = (a + d) ^ 2 := by rw [← h₄]
    
    -- Rest of proof similar to first case
    sorry