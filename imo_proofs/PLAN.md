# Refactoring Plan for IMO Proofs Library

## 1. Objective

The primary goal is to refactor the existing Lean proofs of IMO problems into a shared library. This will reduce code duplication and minimize the total lines of code across the project, while ensuring each part of the library is general enough to be used in multiple solutions.

## 2. Analysis of Existing Proofs

After reviewing the `imo_*.lean` files, the following common mathematical areas and patterns have been identified:

*   **Number Theory:** Many problems use fundamental concepts like divisibility, modular arithmetic, prime numbers, and the greatest common divisor (GCD).
    *   `imo_1959_p1`: GCD properties.
    *   `imo_1974_p3`: Modular arithmetic, specifically quadratic residues modulo 5.
    *   `imo_1992_p1`: Divisibility rules and prime factorization.
    *   `imo_1984_p6`: Properties of odd/even numbers and powers of two.
*   **Algebra:** A significant number of problems are based on algebraic inequalities and manipulations.
    *   `imo_1964_p2`: A specific inequality `(a + b - c) * (a + c - b) ≤ a ^ 2`.
    *   `imo_1983_p6`: Custom lemmas for rearranging terms in an inequality.
    *   `imo_1960_p2`, `imo_1962_p2`: Manipulation of `Real.sqrt`.
*   **Trigonometry:** Some problems rely on trigonometric identities.
    *   `imo_1963_p5`: The product-to-sum identity for `sin_mul_cos`.
*   **Calculus/Real Analysis:** Several problems involve properties of real-valued functions, sequences, and series.
    *   `imo_1985_p6`: Properties of recursively defined sequences.
    *   `imo_2007_p6`: Use of Cauchy-Schwarz inequality (`sum_mul_sq_le_sq_mul_sq`).

## 3. Proposed Library Structure

A new file, `ImoSteps/Common.lean`, will be created to house the shared library. This file will be organized into namespaces corresponding to the mathematical areas identified above.

```lean
-- ImoSteps/Common.lean

import Mathlib

namespace ImoSteps.Common

-- General purpose lemmas that don't fit in a specific category.

-- ==============
-- Number Theory
-- ==============
namespace NumberTheory

lemma dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := sorry
lemma even_of_even_sq {n : ℕ} (h : Even (n^2)) : Even n := sorry
lemma not_sq_mod_5 (a : ℕ) : ¬ a ^ 2 ≡ 2 [MOD 5] ∧ ¬ a ^ 2 ≡ 3 [MOD 5] := sorry

end NumberTheory

-- ==============
-- Algebra
-- ==============
namespace Algebra

lemma le_sq_of_sub_mul_sub (a b c : ℝ) : (a + b - c) * (a + c - b) ≤ a ^ 2 := sorry
lemma am_gm_two_vars (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 2 * sqrt (a * b) ≤ a + b := sorry

end Algebra

-- ==============
-- Trigonometry
-- ==============
namespace Trigonometry

lemma sin_mul_cos (x y : ℝ) : Real.sin x * Real.cos y = (Real.sin (x + y) + Real.sin (x - y)) / 2 := by
  rw [Real.sin_add, Real.sin_sub]
  ring

end Trigonometry

end ImoSteps.Common
```

## 4. Refactoring Process

The refactoring will be executed as follows:

1.  **Create `ImoSteps/Common.lean`:** The new library file will be created with the structure defined above.
2.  **Populate the Library:** General lemmas identified from the individual proof files will be moved into the appropriate namespace in `ImoSteps/Common.lean`. Each lemma will be generalized to be reusable.
3.  **Update `ImoSteps.lean`:** The main library file will be updated to import `ImoSteps.Common`.
4.  **Refactor Problem Files:** Each `imo_*.lean` file will be modified to:
    *   Remove the local definitions of lemmas that are now in the shared library.
    *   Add `import ImoSteps.Common` at the beginning.
    *   Replace calls to local lemmas with calls to the new library lemmas (e.g., `ImoSteps.Common.Algebra.le_sq_of_sub_mul_sub`).
5.  **Verify Changes:** After each significant change, the project will be rebuilt to ensure all proofs remain valid.

## 5. Testing and Verification Strategy

The success of the refactoring will be verified through two main steps:

1.  **Compilation Check:** The entire project will be compiled using the existing `verify_compilation.sh` script, which internally runs `lake build`. A successful compilation ensures that all proofs are still logically sound and that the new library is correctly integrated.
2.  **Line Count Reduction:** The total number of lines of code (LOC) in all `*.lean` files will be measured before and after the refactoring using `wc -l`. The goal is to achieve a noticeable reduction in the total LOC.

## 6. Next Steps

If you approve this plan, I will proceed with the following actions:
1. Create the `ImoSteps/Common.lean` file.
2. Add the `ImoSteps.Common` import to `ImoSteps.lean`.
3. Begin refactoring the first few IMO problems as a proof of concept.
