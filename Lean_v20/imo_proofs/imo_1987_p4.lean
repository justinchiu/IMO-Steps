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


/- Prove that there is no function $f $ from the set of non-negative  integers into itself such that $f(f(n)) = n + 1987 $ for every $n $.-/


open Nat Finset



lemma aux_2
  (s : Finset ℕ)
  (fs : ℕ → Finset ℕ)
  (hu₁ : ∀ a ∈ s, #(fs a) = 2)
  (hu₃ : ∀ (x y : ℕ), x ∈ s → y ∈ s → fs x = fs y ∨ Disjoint (fs x) (fs y)) :
  Even (s.biUnion fs).card := by
  have hi: ∀ si:Finset ℕ , (∀ (x y : ℕ), x ∈ si → y ∈ si → fs x = fs y ∨ Disjoint (fs x) (fs y)) →
    (∀ x ∈ si, (fs x).card = 2) → Even (si.biUnion fs).card := by
    intros si
    refine Finset.induction ?_ ?_ si
    . simp
    . intros a s₁ _ ha₁ ha₂ ha₃
      have ha₄: Even #(s₁.biUnion fs) := by
        refine ha₁ ?_ ?_
        . intros x y hx₀ hy₀
          have hx₁: x ∈ insert a s₁ := by exact mem_insert_of_mem hx₀
          have hy₁: y ∈ insert a s₁ := by exact mem_insert_of_mem hy₀
          exact ha₂ x y hx₁ hy₁
        . intros x hx₀
          have hx₁: x ∈ insert a s₁ := by exact mem_insert_of_mem hx₀
          exact ha₃ x hx₁
      have ha₅: a ∈ insert a s₁ := by exact mem_insert_self a s₁
      have ha₆: fs a ⊆ s₁.biUnion fs ∨ Disjoint (fs a) (s₁.biUnion fs) := by
        by_cases ha₇: ∀ x ∈ s₁, Disjoint (fs x) (fs a)
        . right
          symm
          exact (disjoint_biUnion_left s₁ fs (fs a)).mpr ha₇
        . left
          push_neg at ha₇
          obtain ⟨b, hb₀, hb₁⟩ := ha₇
          have hb₂: fs b = fs a ∨ Disjoint (fs b) (fs a) := by
            refine ha₂ b a ?_ ?_
            . exact mem_insert_of_mem hb₀
            . exact ha₅
          cases' hb₂ with hb₂ hb₂
          . rw [← hb₂]
            exact subset_biUnion_of_mem fs hb₀
          . exact False.elim (hb₁ hb₂)
      simp
      cases' ha₆ with ha₆ ha₆
      . rw [union_eq_right.mpr ha₆]
        exact ha₄
      . rw [card_union_of_disjoint ha₆, ha₃ a ha₅]
        refine Even.add ?_ ha₄
        decide
  refine hi s ?_ ?_
  . exact fun x y a a_1 => hu₃ x y a a_1
  . exact fun x a => hu₁ x a


lemma aux_1
  (f₀: ℕ → ℕ)
  (s : Finset ℕ)
  (hf₁ : ∀ x ∈ s, f₀ x ∈ s)
  (fs : ℕ → Finset ℕ)
  (hu₀ : ∀ (x : ℕ), fs x = {x, f₀ x})
  (hu₂ : ∀ (x y : ℕ), x ∈ fs y → x = y ∨ x = f₀ y) :
  s.biUnion fs = s := by
  refine Finset.ext ?_
  intro a
  constructor
  . intro ha₀
    apply Finset.mem_biUnion.mp at ha₀
    contrapose! ha₀
    intro b hb₀
    contrapose! ha₀
    apply hu₂ a b at ha₀
    cases' ha₀ with ha₀ ha₀
    . rw [ha₀]
      exact hb₀
    . rw [ha₀]
      exact hf₁ b hb₀
  . intro ha₀
    refine Finset.mem_biUnion.mpr ?_
    use a
    constructor
    . exact ha₀
    . rw [hu₀]
      exact mem_insert_self a {f₀ a}


theorem imo_1987_p4 :
  ¬ ∃ (f : ℕ → ℕ), ∀ n, f (f n) = n + 1987 := by
  push_neg
  intro f
  let t : ℕ := 1987
  have ht₀: t = 1987 := by rfl
  rw [← ht₀]
  by_contra! h₀
  have h₁: ∀ n, f (n + t) = f (n) + t := by
    have h₁₀: ∀ n, f (f (f n)) = f (n + 1987) := by
      intro n
      exact congrArg f (h₀ n)
    intro n
    exact (rfl.congr (h₀ (f n))).mp (Eq.symm (h₁₀ n))
  have h₂: ∀ n k, f (n + t * k) = f n + t * k := by
    intros n k
    induction' k with d hd
    . exact rfl
    . rw [mul_add, mul_one, ← add_assoc, h₁ (n + t * d), hd, add_assoc]
  let s : Finset ℕ := Finset.range t
  have hs₀: s = range t := by exact rfl
  let f₀: ℕ → ℕ := fun x => (f (x % t)) % t
  have hf₀: ∀ x, f₀ x = f (x % t) % t := by exact fun x => rfl
  have hf₁: ∀ x ∈ s, (f₀ x) ∈ s := by
    intros x _
    refine Finset.mem_range.mpr ?_
    rw [hf₀]
    refine Nat.mod_lt (f (x % t)) ?_
    linarith
  have hf₂: ∀ x ∈ s, x % t = x := by
    intros x hx₀
    apply Finset.mem_range.mp at hx₀
    exact mod_eq_of_lt hx₀
  have hf₃: ∀ x ∈ s, f₀ (f₀ x) = x := by
    intros x hx₀
    rw [hf₀, hf₀, Nat.mod_mod, hf₂ x hx₀,]
    by_cases hx₁: f x < t
    . have hx₂: f x % t = f x := by exact mod_eq_of_lt hx₁
      rw [hx₂, h₀, add_mod_right]
      exact hf₂ x hx₀
    . push_neg at hx₁
      let k := (f x) / t
      let l := (f x) % t
      have hx₂: f x = l + t * k := by exact Eq.symm (mod_add_div (f x) t)
      have hx₃: f l + t * k = x + t := by rw [← h₀ x, hx₂, h₂ l k]
      have hl₀: l % t = l := by exact mod_mod (f x) t
      have hk₀: k < 2 := by
        by_contra! hc₀
        have hc₁: x + t < 2 * t := by
          rw [two_mul]
          simp
          refine Finset.mem_range.mp ?_
          exact hx₀
        have hc₂: 0 + t * 2 ≤ f l + t * k := by
          refine Nat.add_le_add ?_ ?_
          . exact Nat.zero_le (f l)
          . exact Nat.mul_le_mul_left t hc₀
        rw [zero_add, hx₃] at hc₂
        linarith
      interval_cases k
      . simp at hx₂ hx₃
        rw [hx₂, hl₀, hx₃, add_mod_right, hf₂ x hx₀]
      . rw [mul_one] at hx₂ hx₃
        simp at hx₃
        rw [hx₂, add_mod_right, hl₀, hx₃, hf₂ x hx₀]
  have hf₄: ∀ x y, x ∈ s → y ∈ s → f₀ x = f₀ y → x = y := by
    intros x y hx₀ hy₀ hxy
    rw [← hf₃ x hx₀, ← hf₃ y hy₀]
    exact congrArg f₀ (hxy)
  have hf₇: ∃ a ∈ s, f₀ a = a := by
    by_contra! hc₀
    clear h₀ h₁ h₂ hf₀ hf₂
    let fs : ℕ → Finset ℕ := fun x => {x, f₀ x}
    have hu₀: ∀ x, fs x = {x, f₀ x} := by exact fun x => rfl
    have hu₁: ∀ a ∈ s, (fs a).card = 2 := by
      exact fun a a_1 => card_pair fun a_2 => hc₀ a a_1 (id (Eq.symm a_2))
    have hu₂: ∀ x y : ℕ , x ∈ fs y → x = y ∨ x = f₀ y := by
      intros x y hx₀
      have hy₀: ({y, f₀ y}:Finset ℕ) = {y} ∪ {f₀ y} := by exact hu₀ y
      rw [hu₀ y, hy₀] at hx₀
      simp_all only [mem_union, mem_singleton,]
    have hu₃: ∀ x y, x ∈ s → y ∈ s → fs x = fs y ∨ Disjoint (fs x) (fs y) := by
      intros x y hx₀ hy₀
      by_cases hx₁: x = f₀ y
      . left
        rw [hu₀, hu₀, hx₁, hf₃ y hy₀]
        exact pair_comm (f₀ y) y
      . have hx₂: x ≠ f₀ x := by exact fun a => hc₀ x hx₀ (id (Eq.symm a))
        by_cases hx₃: x = y
        . left
          rw [hx₃]
        . right
          refine Finset.disjoint_iff_ne.mpr ?_
          intros a ha₀ b hb₀
          have ha₂: a = x ∨ a = f₀ x := by exact hu₂ a x ha₀
          have hb₂: b = y ∨ b = f₀ y := by exact hu₂ b y hb₀
          cases' ha₂ with ha₂ ha₂
          . omega
          . cases' hb₂ with hb₂ hb₂
            . rw [ha₂, hb₂]
              contrapose! hx₁
              rw [← hf₃ x hx₀]
              exact congrArg f₀ (hx₁)
            . rw [ha₂, hb₂]
              contrapose! hx₃
              exact hf₄ x y hx₀ hy₀ hx₃
    have hu₄: Finset.biUnion s fs = s := by
      exact aux_1 f₀ s hf₁ fs hu₀ hu₂
    have hu₅: Even (Finset.biUnion s fs).card := by
      exact aux_2 s fs hu₁ hu₃
    have hc₁: Even s.card := by
      rw [hu₄] at hu₅
      exact hu₅
    have hc₂: Odd s.card := by
      rw [hs₀, Finset.card_range, ht₀]
      decide
    apply Nat.not_even_iff_odd.mpr at hc₂
    exact hc₂ hc₁
  obtain ⟨a, ha₀, ha₁⟩ := hf₇
  have ha₂: ∃ k, f a = a + t * k := by
    rw [hf₀ a, hf₂ a ha₀, Nat.mod_def] at ha₁
    use ((f a) / t)
    refine Nat.eq_add_of_sub_eq ?_ ha₁
    rw [mul_comm]
    exact Nat.div_mul_le_self (f a) t
  obtain ⟨k, ha₃⟩ := ha₂
  have ha₄: f (f a) = a + t := by exact h₀ a
  have ha₅: f (f a) = a + 2 * t * k := by
    rw [ha₃, h₂ a k, ha₃]
    linarith
  omega
