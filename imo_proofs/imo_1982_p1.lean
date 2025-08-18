import Mathlib
import ImoSteps

open Nat ImoSteps

theorem imo_1982_p1 (f : ℕ → ℤ)
    (h₀ : ∀ m n, 0 < m → 0 < n → f (m + n) - f m - f n ∈ ({0, 1} : Set ℤ))
    (h₁ : f 2 = 0)
    (h₂ : 0 < f 3)
    (h₃ : f 9999 = 3333) :
    f 1982 = 660 := by
  -- Use library lemmas for key properties
  have subadditive := subadditive_of_delta h₀
  have mult_bound := mult_bound_of_subadditive subadditive
  
  -- Determine f(3) = 1 from f(9999) = 3333
  have f3_eq : f 3 = 1 := by
    have : 3333 * f 3 ≤ f 9999 := mult_bound 3 3333 (by norm_num) (by norm_num)
    linarith [h₂, h₃]
  
  -- Find f(1980) = 660
  have f1980_eq : f 1980 = 660 := by
    have upper : f 1980 ≤ 660 := by
      have : f (5 * 1980) + f 99 ≤ f 9999 := 
        subadditive (5 * 1980) 99 (by norm_num) (by norm_num)
      have h1 : 5 * f 1980 ≤ f (5 * 1980) := 
        mult_bound 1980 5 (by norm_num) (by norm_num)
      have h2 : 33 * f 3 ≤ f 99 := 
        mult_bound 3 33 (by norm_num) (by norm_num)
      linarith [h₃, f3_eq]
    have lower : 660 ≤ f 1980 := by
      have : 660 * f 3 ≤ f 1980 := mult_bound 3 660 (by norm_num) (by norm_num)
      linarith [f3_eq]
    linarith
  
  -- Use f(1982) = f(1980) + f(2) + δ where δ ∈ {0,1}
  have : f 1982 - f 1980 - f 2 ∈ ({0, 1} : Set ℤ) := 
    h₀ 1980 2 (by norm_num) (by norm_num)
  
  -- Check that δ = 0 is the only possibility
  by_contra h_ne
  have : f 1982 - f 1980 - f 2 = 1 := by
    cases' this with h h <;> [exfalso; exact h]; linarith [f1980_eq, h₁]
  have f1982_eq : f 1982 = 661 := by linarith [f1980_eq, h₁, this]
  
  -- But f(1982) = 661 leads to contradiction
  have : 5 * f 1982 ≤ 3333 - 29 := by
    have h1 : f (5 * 1982) + f 89 ≤ f 9999 := 
      subadditive (5 * 1982) 89 (by norm_num) (by norm_num)
    have h2 : 5 * f 1982 ≤ f (5 * 1982) := 
      mult_bound 1982 5 (by norm_num) (by norm_num)
    have h3 : 29 * f 3 ≤ f 87 := 
      mult_bound 3 29 (by norm_num) (by norm_num)
    have h4 : f 87 + f 2 ≤ f 89 := 
      subadditive 87 2 (by norm_num) (by norm_num)
    linarith [h₁, h₃, f3_eq]
  
  linarith [f1982_eq]