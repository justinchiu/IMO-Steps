import Mathlib
import ImoSteps

open Nat ImoSteps

-- Core inequalities
lemma binomial_power_bound (b p : ℕ) (hb : 0 < b) (hbp : b < p) :
    1 + b * p + b ^ p ≤ (1 + b) ^ p := by
  induction' p, hbp using Nat.le_induction with n _ ih
  · rw [add_pow]
    calc 1 + b * b.succ + b ^ b.succ
      ≤ ∑ k in Finset.range (b.succ + 1), (b.succ).choose k * 1^k * b^(b.succ - k) := by
        simp [Finset.sum_range_succ]
        omega
      _ = (1 + b) ^ b.succ := by rw [← add_pow]
  · calc 1 + b * (n + 1) + b ^ (n + 1)
      ≤ 1 + b * n + b ^ n + b + b * b ^ n := by ring_nf; omega
      _ ≤ (1 + b) ^ n * (1 + b) := by
        apply mul_le_mul_right
        exact ih
      _ = (1 + b) ^ (n + 1) := by ring

lemma prime_divides_factorial_sum (a b p : ℕ) (hp : Prime p) 
    (h : a ^ p = b.factorial + p) (hbp : p ≤ b) : p ∣ a := by
  have : p ∣ a ^ p := by
    rw [h]
    exact dvd_add_self_right.mpr (dvd_factorial (Prime.pos hp) hbp)
  exact Prime.dvd_of_dvd_pow hp this


-- Product identities for factorials
lemma factorial_product_identity (p : ℕ) :
    (Finset.Ico p (2 * p - 1)).prod (· + 1) = 
    (Finset.range (p - 1)).prod (p + · + 1) := by
  rw [Finset.prod_Ico_eq_prod_range]
  congr 1
  omega

lemma factorial_reflection (p : ℕ) (hp : 2 ≤ p) :
    (Finset.range (p - 1)).prod (· + 1) = 
    (Finset.range (p - 1)).prod (p - · - 1) := by
  -- The products are (p-1)! in both cases
  have left : (Finset.range (p - 1)).prod (· + 1) = (p - 1).factorial := by
    rw [← Finset.prod_range_add_one]
    simp
  have right : (Finset.range (p - 1)).prod (p - · - 1) = (p - 1).factorial := by
    -- The right side also equals (p-1)!
    -- Since we map i ↦ p - i - 1 for i ∈ [0, p-2]
    -- This gives us p-1, p-2, ..., 1
    -- Which is the same product as 1, 2, ..., p-1
    rw [← Finset.prod_bij 
      (fun i _ => ⟨p - 2 - i, by omega⟩) 
      (by intros; simp; omega)
      (by intros; simp; omega)
      (by intros a b _ _ h; simp at h; omega)
      (by intros; use p - 2 - b; simp; omega)]
    simp [Finset.prod_range_add_one]
  rw [left, right]

-- Main divisibility lemma
lemma divisibility_constraint (a b p : ℕ) (hp : Prime p) (ha : 1 < a)
    (h_eq : a ^ p = b.factorial + p) (h_div : p ∣ a) : 
    a = p ∧ b < p := by
  obtain ⟨k, rfl⟩ := h_div
  have hk : 0 < k := by
    by_contra h0
    simp at h0
    subst h0
    simp at ha
  
  -- From (kp)^p = b! + p
  have : (k * p) ^ p = b.factorial + p := h_eq
  rw [mul_pow] at this
  
  -- If k > 1, then k^p * p^p > b! + p for large enough p
  by_cases hk1 : k = 1
  · subst hk1
    simp at this ⊢
    constructor; rfl
    by_contra hbp
    push_neg at hbp
    have : p ∣ b.factorial := dvd_factorial hp.pos hbp
    have : p ^ p ∣ b.factorial + p := by
      rw [← this]
      exact dvd_pow_self p (ne_of_gt hp.pos)
    have : p ^ p ≤ b.factorial + p := Nat.le_of_dvd (by omega) this
    have : p ^ p ≤ b.factorial + p := by
      calc p ^ p ≤ p * b.factorial := by
        -- Use factorial growth bounds
        apply mul_le_mul_left
        exact factorial_le_pow _
      _ ≤ b.factorial + p := by omega
    -- This contradicts our equation
    omega
  · have : 2 ≤ k := by omega
    -- For k ≥ 2, k^p * p^p grows too fast
    exfalso
    have : k ^ p * p ^ p > b.factorial + p := by
      -- For k ≥ 2 and p prime ≥ 2, we have k^p * p^p ≥ 2^2 * 2^2 = 16
      -- And since b! + p is at most b! + b + 1, we need to show this is small
      -- But from our equation, k^p * p^p = b! + p, contradiction
      -- Actually, we need a more careful analysis
      -- Since k ≥ 2, we have (kp)^p ≥ (2p)^p ≥ 2^p * p^p
      -- For p ≥ 5, this grows much faster than b!
      by_cases hp5 : p < 5
      · -- For small primes p < 5
        interval_cases p
        · omega  -- p = 0 contradicts Prime p
        · omega  -- p = 1 contradicts Prime p
        · -- p = 2
          have : k ^ 2 * 2 ^ 2 ≥ 2 ^ 2 * 2 ^ 2 := by
            apply Nat.mul_le_mul_right
            apply Nat.pow_le_pow_left this
          simp at this ⊢
          -- k^2 * 4 ≥ 16
          -- So b! < 16 - 2 = 14, thus b ≤ 4
          have : b.factorial < 14 := by omega
          interval_cases b <;> norm_num [factorial] at this ⊢
        · -- p = 3
          have : k ^ 3 * 3 ^ 3 ≥ 2 ^ 3 * 3 ^ 3 := by
            apply Nat.mul_le_mul_right
            apply Nat.pow_le_pow_left this
          simp at this ⊢
          -- k^3 * 27 ≥ 216
          have : b.factorial < 213 := by omega
          interval_cases b <;> (norm_num [factorial] at this ⊢ <;> try omega)
        · omega  -- p = 4 contradicts Prime p
      · -- For p ≥ 5
        push_neg at hp5
        have : k ^ p * p ^ p ≥ 2 ^ p * p ^ p := by
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_left this
        have : 2 ^ p * p ^ p = (2 * p) ^ p := by ring
        have : (2 * p) ^ p ≥ 10 ^ p := by
          apply Nat.pow_le_pow_left
          omega
        have : 10 ^ p ≥ 10 ^ 5 := by
          apply Nat.pow_le_pow_left; omega; exact hp5
        have : 10 ^ 5 = 100000 := by norm_num
        -- So k^p * p^p ≥ 100000
        -- But b! + p < 100000 only if b is small
        have : b.factorial < 100000 - p := by omega
        have : b < 9 := by
          by_contra h; push_neg at h
          have : b.factorial ≥ 9.factorial := by
            apply Nat.factorial_le; exact h
          have : 9.factorial = 362880 := by norm_num [factorial]
          omega
        -- But for b < 9 and p ≥ 5, we can check directly
        interval_cases b <;> (norm_num [factorial] at this ⊢ <;> try omega)
    linarith [this]

-- Solution characterization
lemma solution_structure (a b p : ℕ) (hp : Prime p) (ha : 1 < a)
    (h : a ^ p = b.factorial + p) :
    (a = p ∧ b = p - 1) ∨ (p = 2 ∧ a = 3 ∧ b = 4) := by
  by_cases h_div : p ∣ a
  · obtain ⟨rfl, hb⟩ := divisibility_constraint a b p hp ha h h_div
    left
    constructor; rfl
    -- Show b = p - 1 from p^p = b! + p and b < p
    interval_cases b <;> norm_num at h ⊢
    · norm_num at hb
  · -- Case where p ∤ a requires special analysis
    right
    -- Only p = 2, a = 3, b = 4 works
    -- We need to show that if p ∤ a, then p = 2, a = 3, b = 4
    -- First, if p ∤ a, then a and p are coprime
    -- From a^p = b! + p, we have a^p ≡ p (mod p)
    -- By Fermat's Little Theorem: a^p ≡ a (mod p) when gcd(a,p) = 1
    -- So a ≡ p ≡ 0 (mod p), contradiction unless p | a
    -- This means we need a different approach
    
    -- Actually, from a^p = b! + p with p ∤ a:
    -- If b ≥ p, then p | b!, so p | a^p, so p | a, contradiction
    -- So b < p
    
    have hb_lt : b < p := by
      by_contra h_neg
      push_neg at h_neg
      have : p ∣ b.factorial := dvd_factorial hp.pos h_neg
      have : p ∣ a ^ p := by
        rw [h]
        exact dvd_add_self_right.mpr this
      have : p ∣ a := Prime.dvd_of_dvd_pow hp this
      exact h_div this
    
    -- For small b and prime p, check all possibilities
    -- Since a > 1 and a^p = b! + p, we need b! + p to be a perfect p-th power
    interval_cases p
    · omega  -- p = 0 contradicts Prime p
    · omega  -- p = 1 contradicts Prime p
    · -- p = 2
      -- Need a^2 = b! + 2 with b < 2, so b = 0 or b = 1
      interval_cases b
      · -- b = 0: a^2 = 0! + 2 = 3, impossible
        simp [factorial] at h
        have : ∃ k, k * k = 3 := ⟨a, h⟩
        omega
      · -- b = 1: a^2 = 1! + 2 = 3, impossible  
        simp [factorial] at h
        have : ∃ k, k * k = 3 := ⟨a, h⟩
        omega
      · omega  -- b ≥ 2 contradicts b < p = 2
    · -- p = 3
      -- Need a^3 = b! + 3 with b < 3
      interval_cases b
      · -- b = 0: a^3 = 0! + 3 = 4, impossible (4 is not a perfect cube)
        simp [factorial] at h
        interval_cases a <;> (norm_num at h <;> try omega)
      · -- b = 1: a^3 = 1! + 3 = 4, impossible
        simp [factorial] at h
        interval_cases a <;> (norm_num at h <;> try omega)
      · -- b = 2: a^3 = 2! + 3 = 5, impossible
        simp [factorial] at h
        interval_cases a <;> (norm_num at h <;> try omega)
    · omega  -- p = 4 contradicts Prime p
    · -- p = 5
      -- Need a^5 = b! + 5 with b < 5
      interval_cases b <;> 
        (simp [factorial] at h; 
         interval_cases a <;> (norm_num at h <;> try omega))
    · -- p ≥ 6: similar analysis shows no solutions
      -- For larger primes, the gap between consecutive p-th powers grows
      -- and b! + p cannot be a perfect p-th power for small b
      exfalso
      have : b < 6 := by omega
      interval_cases b <;>
        (simp [factorial] at h;
         -- For each b, check if b! + p can be a perfect p-th power
         -- This requires checking a bounded range of a values
         have : a < 4 := by
           by_contra h_neg; push_neg at h_neg
           have : a ^ p ≥ 4 ^ p := Nat.pow_le_pow_left h_neg _
           have : 4 ^ p ≥ 4 ^ 6 := Nat.pow_le_pow_left (by omega) (by omega : 6 ≤ p)
           have : 4 ^ 6 = 4096 := by norm_num
           omega;
         interval_cases a <;> (try omega; norm_num at h; 
           have : p ≤ 200 := by omega;  -- Reasonable bound for contradiction
           interval_cases p <;> (norm_num at h <;> try omega)))

theorem imo_2022_p5 (a b p : ℕ) (hp : Prime p) (ha : 1 < a) (hb : 0 < b)
    (h : a ^ p = b.factorial + p) :
    p = 2 ∨ p = 3 := by
  obtain (⟨rfl, rfl⟩ | ⟨hp2, ha3, hb4⟩) := solution_structure a b p hp ha h
  · -- Case a = p, b = p - 1
    -- Check small primes
    interval_cases p <;> (norm_num at h ⊢ <;> try norm_num)
    -- For p ≥ 5, show p^p > (p-1)! + p
    exfalso
    have : p ^ p > (p - 1).factorial + p := by
      -- Direct verification for small primes
      match p with
      | 5 => norm_num [factorial]
      | 6 => norm_num [factorial]
      | 7 => norm_num [factorial]
      | n + 8 =>
        -- For p ≥ 8: p^p > p! > (p-1)! + p
        have : n + 8 ≥ 8 := by omega
        have : 8 ^ 8 > 7.factorial + 8 := by norm_num [factorial]
        have : (n + 8) ^ (n + 8) ≥ 8 ^ 8 := by
          apply Nat.pow_le_pow_of_le_left; omega
        have : 7.factorial ≥ (n + 7).factorial := by
          apply Nat.factorial_le; omega
        omega
    linarith [h]
  · -- Case p = 2, a = 3, b = 4
    left; exact hp2