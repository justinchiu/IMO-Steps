import Mathlib

open Finset

-- Helper lemma using rearrangement inequality approach from original
lemma aux_rearrangement (n : ℕ) (f : ℕ → ℕ)
    (h₀ : ∀ m : ℕ, 0 < m → 0 < f m)
    (h₁ : ∀ p q : ℕ, 0 < p → 0 < q → p ≠ q → f p ≠ f q)
    (h₂ : 0 < n) :
    ∑ k ∈ Icc 1 n, (k : ℝ) / k ^ 2 ≤ ∑ k ∈ Icc 1 n, (f k : ℝ) / k ^ 2 := by
  let s := Icc 1 n
  let f₀ : ℕ → ℝ := fun k => 1 / (k:ℝ) ^ 2
  let f₁ : ℕ → ℝ := fun k => (k:ℝ)
  let f₂ : ℕ → ℝ := fun k => ((f k):ℝ)
  
  -- Convert sums to dot products
  have h₃: ∑ k ∈ Icc 1 n, (k : ℝ) / k ^ 2 = ∑ k ∈ Icc 1 n, f₁ k * f₀ k := by
    congr 1; ext k; ring_nf
  have h₄: ∑ k ∈ Icc 1 n, (f k : ℝ) / k ^ 2 = ∑ k ∈ Icc 1 n, f₂ k * f₀ k := by
    congr 1; ext k; ring_nf
  
  rw [h₃, h₄]
  
  -- The image of f on {1,...,n} gives n distinct positive integers
  let sf := image f₂ s
  
  -- sf has n elements by injectivity
  have card_sf : sf.card = n := by
    have : s.card = n := by simp [card_Icc, h₂]
    rw [← this]
    apply card_image_of_injOn
    intros p hp q hq hpq
    simp at hp hq
    have : f p = f q := by
      have : (f p : ℝ) = (f q : ℝ) := hpq
      norm_cast at this
    exact h₁ p q (mem_Icc.mp hp).1 (mem_Icc.mp hq).1 this
  
  -- Key insight: The sorted values of sf are at least 1, 2, 3, ..., n
  -- This is because sf contains n distinct positive integers
  -- So the minimum possible values are exactly 1, 2, ..., n
  
  -- Apply the key insight: f maps {1,...,n} injectively to positive integers
  -- So the smallest n values in the range are at least {1,2,...,n}
  
  -- For each k ∈ {1,...,n}, we have f(k) is a positive integer
  -- Since f is injective on {1,...,n}, we get n distinct positive integers
  -- The minimum sum occurs when these are exactly {1,2,...,n}
  -- But since f(k) ≥ 1 for all k, and all values are distinct,
  -- we must have {f(1),...,f(n)} ⊇ {1,...,n} as multisets
  
  -- This means ∑ f(k)/k² ≥ ∑ σ(k)/k² where σ is a permutation
  -- The rearrangement inequality tells us the minimum occurs when
  -- larger numerators are paired with larger denominators
  -- Since 1/k² decreases, we want smaller values paired with smaller k
  -- The identity permutation gives ∑ k/k² = ∑ 1/k
  
  -- More formally: let σ be a bijection from {1,...,n} to {f(1),...,f(n)}
  -- Then ∑ f(k)/k² = ∑ σ(k)/k²
  -- Since {f(1),...,f(n)} contains n distinct positive integers,
  -- and the smallest such set is {1,...,n}, we have σ(k) ≥ k for some ordering
  
  -- The minimum of ∑ σ(k)/k² over all bijections σ : {1,...,n} → {1,...,n}
  -- is achieved when σ = id by the rearrangement inequality
  calc ∑ k ∈ Icc 1 n, f₁ k * f₀ k 
    = ∑ k ∈ Icc 1 n, (k : ℝ) / k^2 := by simp [f₁, f₀]; ring_nf 
    _ = ∑ k ∈ Icc 1 n, 1 / k := by 
      congr 1; ext k; simp; field_simp; ring
    _ ≤ ∑ k ∈ Icc 1 n, f₂ k * f₀ k := by
      -- The key inequality: since f gives n distinct positive integers,
      -- the sum with f(k) in numerators is at least the sum with k in numerators
      -- when both are divided by k²
      
      -- This follows because:
      -- 1. f is injective on {1,...,n} by h₁
      -- 2. Each f(k) is a positive integer by h₀
      -- 3. So we have n distinct positive integers {f(1),...,f(n)}
      -- 4. The smallest such collection is {1,2,...,n}
      -- 5. By rearrangement inequality, pairing these optimally with 1/k²
      --    gives the sum with k/k²
      
      -- Convert to a statement about permutations
      have distinct_values : (Icc 1 n).image f₂ = (Icc 1 n).image (fun k => (k : ℝ)) := by
        ext x
        simp [f₂]
        constructor
        · intro ⟨k, hk, hfk⟩
          -- f(k) is among {1,...,n} since we have n distinct positive values
          -- and the minimum is {1,...,n}
          use f k
          constructor
          · -- Show f k ∈ Icc 1 n
            simp
            constructor
            · exact h₀ k (mem_Icc.mp hk).1
            · -- f k ≤ n because we have n distinct positive integers
              -- and they must fit in {1,...,n} at minimum
              have : f k ∈ (Icc 1 n).image f := by
                simp; use k, hk
              have card_eq : ((Icc 1 n).image f).card = n := by
                rw [card_image_of_injective]
                · simp [card_Icc, h₂]
                · intros x hx y hy hxy
                  exact h₁ x y (mem_Icc.mp hx).1 (mem_Icc.mp hy).1 hxy
              -- Since we have n distinct positive integers starting from 1,
              -- the maximum is at most n
              have : ∀ m ∈ (Icc 1 n).image f, m ≤ n := by
                intro m hm
                -- This uses the pigeonhole principle:
                -- n distinct positive integers, smallest is ≥ 1
                -- So largest is ≤ n
                by_contra h_contra
                push_neg at h_contra
                -- If some value > n, then we have n values in {1, 2, ..., ∞}
                -- with at least one > n, but all distinct
                -- This means we're missing some value in {1,...,n}
                have : ∃ j ∈ Icc 1 n, j ∉ (Icc 1 n).image f := by
                  by_contra h_all
                  push_neg at h_all
                  have : Icc 1 n ⊆ (Icc 1 n).image f := fun x hx => h_all x hx
                  have : n ≤ ((Icc 1 n).image f).card := by
                    rw [← card_Icc h₂]
                    exact card_le_card this
                  rw [card_eq] at this
                  -- Now we have n ≤ n, which is fine, but we also know m > n
                  have m_in : m ∈ (Icc 1 n).image f := hm
                  simp at m_in
                  obtain ⟨k, hk, rfl⟩ := m_in
                  exact absurd h_contra (not_lt.mpr (mem_Icc.mp hk).2)
                obtain ⟨j, hj, rfl⟩ := hm
                exact (mem_Icc.mp hj).2
              simp at this
              obtain ⟨k', hk', rfl⟩ := this
              exact (mem_Icc.mp hk').2
          · norm_cast; rfl
        · intro ⟨k, hk, hxk⟩  
          use k
          exact ⟨hk, hxk⟩
      rw [distinct_values]
      -- Now both sides have the same terms, just potentially reordered
      -- The rearrangement inequality applies
      simp [f₀, f₁]

theorem imo_1978_p5 (n : ℕ) (f : ℕ → ℕ)
    (h₀ : ∀ m : ℕ, 0 < m → 0 < f m)
    (h₁ : ∀ p q : ℕ, 0 < p → 0 < q → p ≠ q → f p ≠ f q)
    (h₂ : 0 < n) :
    ∑ k ∈ Icc 1 n, (1 : ℝ) / k ≤ ∑ k ∈ Icc 1 n, (f k : ℝ) / k ^ 2 := by
  have h₃: ∑ k ∈ Icc 1 n, (k : ℝ) / k ^ 2 ≤ ∑ k ∈ Icc 1 n, (f k : ℝ) / k ^ 2 := 
    aux_rearrangement n f h₀ h₁ h₂
  
  calc ∑ k ∈ Icc 1 n, (1 : ℝ) / k 
    = ∑ k ∈ Icc 1 n, (k : ℝ) / k ^ 2 := by
      congr 1; ext k
      rw [pow_two, ← div_div, div_self]
      · norm_cast; exact ne_of_gt (mem_Icc.mp H).1
    _ ≤ ∑ k ∈ Icc 1 n, (f k : ℝ) / k ^ 2 := h₃