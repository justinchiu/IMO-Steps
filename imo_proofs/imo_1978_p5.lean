import Mathlib
import ImoSteps

open Finset ImoSteps

-- Core lemma: rearrangement inequality for specific functions
lemma rearrangement_inequality (n : ℕ) (f : ℕ → ℕ)
    (h₀ : ∀ m : ℕ, 0 < m → 0 < f m)
    (h₁ : ∀ p q : ℕ, 0 < p → 0 < q → p ≠ q → f p ≠ f q)
    (h₂ : 0 < n) :
    ∑ k ∈ Icc 1 n, (k : ℝ) / k ^ 2 ≤ ∑ k ∈ Icc 1 n, (f k : ℝ) / k ^ 2 := by
  -- Define the sorted image of f on [1,n]
  let s := Icc 1 n
  let sf := image (fun k => (f k : ℝ)) s
  let sf_sorted := (sort (· ≤ ·) sf).getD
  
  -- f is injective on s, so |image f s| = n
  have card_sf : sf.card = n := by
    rw [← card_Icc, ← @card_image_of_injOn _ _ s f]
    · simp [card_Icc, h₂]
    · intros p hp q hq hpq
      exact h₁ p q (mem_Icc.mp hp).1 (mem_Icc.mp hq).1 hpq
  
  -- The sorted list has length n
  have len_sorted : (sort (· ≤ ·) sf).length = n := by
    rw [← card_sf]
    exact length_sort _
  
  -- All values in sorted list are ≥ 1
  have sorted_ge_one : ∀ k ∈ s, 1 ≤ sf_sorted (k - 1) 0 := by
    intros k hk
    have hk_range : k - 1 < (sort (· ≤ ·) sf).length := by
      rw [len_sorted]
      exact Nat.sub_one_lt_of_le (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
    rw [List.getD_eq_getElem _ _ hk_range]
    have : (sort (· ≤ ·) sf)[k - 1] ∈ sort (· ≤ ·) sf := List.getElem_mem hk_range
    rw [mem_sort] at this
    simp [sf] at this
    obtain ⟨m, hm, rfl⟩ := this
    exact Nat.one_le_cast.mpr (h₀ m (mem_Icc.mp hm).1)
  
  -- Sorted values are increasing by at least 1
  have sorted_inc : ∀ a b ∈ s, a < b → sf_sorted (a - 1) 0 + 1 ≤ sf_sorted (b - 1) 0 := by
    intros a ha b hb hab
    have ha_range : a - 1 < (sort (· ≤ ·) sf).length := by
      rw [len_sorted]
      exact Nat.sub_one_lt_of_le (mem_Icc.mp ha).1 (mem_Icc.mp ha).2
    have hb_range : b - 1 < (sort (· ≤ ·) sf).length := by
      rw [len_sorted]
      exact Nat.sub_one_lt_of_le (mem_Icc.mp hb).1 (mem_Icc.mp hb).2
    
    -- Since f is injective and takes integer values, sorted values differ by at least 1
    have hab' : a - 1 < b - 1 := Nat.sub_mono_right (by linarith : 1 ≤ a) hab
    have : (sort (· ≤ ·) sf)[a - 1] < (sort (· ≤ ·) sf)[b - 1] := by
      apply List.sorted_le_getElem_lt_getElem
      · exact List.sorted_sort _
      · exact hab'
    
    -- Extract integer values
    rw [List.getD_eq_getElem _ _ ha_range, List.getD_eq_getElem _ _ hb_range]
    have ha_mem : (sort (· ≤ ·) sf)[a - 1] ∈ sf := by
      rw [mem_sort]; exact List.getElem_mem _
    have hb_mem : (sort (· ≤ ·) sf)[b - 1] ∈ sf := by
      rw [mem_sort]; exact List.getElem_mem _
    simp [sf] at ha_mem hb_mem
    obtain ⟨ma, hma, rfl⟩ := ha_mem
    obtain ⟨mb, hmb, rfl⟩ := hb_mem
    norm_cast at this ⊢
    omega
  
  -- Apply rearrangement inequality
  calc ∑ k ∈ s, (k : ℝ) / k ^ 2 
    = ∑ k ∈ s, 1 / k ^ 2 * k := by
      congr 1; ext k; ring
    _ ≤ ∑ k ∈ s, 1 / k ^ 2 * sf_sorted (k - 1) 0 := by
      apply sum_le_sum
      intros k hk
      gcongr
      -- Show k ≤ sf_sorted (k - 1) 0 by induction
      induction' k using Nat.strong_induction_on with k ih
      cases' k with k'
      · simp at hk
      cases' k' with k''
      · simp [sorted_ge_one 1 (by simp [h₂] : 1 ∈ s)]
      · -- k = k'' + 2
        have hk' : k'' + 1 ∈ s := by
          simp [Icc.mem] at hk ⊢; omega
        have : k'' + 1 ≤ sf_sorted k'' 0 := by
          cases' k'' with k'''
          · simp [sorted_ge_one 1 (by simp [h₂] : 1 ∈ s)]
          · exact ih (k''' + 2) (by omega) (by simp [Icc.mem] at hk ⊢; omega)
        calc k'' + 2 = (k'' + 1) + 1 := by ring
          _ ≤ sf_sorted k'' 0 + 1 := by linarith
          _ ≤ sf_sorted (k'' + 1) 0 := sorted_inc _ hk' _ hk (by omega)
    _ = ∑ k ∈ s, (f k : ℝ) / k ^ 2 := by
      -- The sorted values are exactly the values of f, just rearranged
      sorry -- This requires showing the bijection between sorted list and f values

theorem imo_1978_p5 (n : ℕ) (f : ℕ → ℕ)
    (h₀ : ∀ m : ℕ, 0 < m → 0 < f m)
    (h₁ : ∀ p q : ℕ, 0 < p → 0 < q → p ≠ q → f p ≠ f q)
    (h₂ : 0 < n) :
    ∑ k ∈ Icc 1 n, (1 : ℝ) / k ≤ ∑ k ∈ Icc 1 n, (f k : ℝ) / k ^ 2 := by
  calc ∑ k ∈ Icc 1 n, (1 : ℝ) / k
    = ∑ k ∈ Icc 1 n, (k : ℝ) / k ^ 2 := by
      congr 1; ext k; field_simp; ring
    _ ≤ ∑ k ∈ Icc 1 n, (f k : ℝ) / k ^ 2 := 
      rearrangement_inequality n f h₀ h₁ h₂