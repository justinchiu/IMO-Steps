# Code Compression

Refactor and compress the Lean sources as much as possible while keeping all proofs valid.

## Goal
- Preserve the theorems defined in each `imo_*.lean` exactly.
- Minimize the total number of lines of code across the repo.
- Allow redesigning proofs, lemmas, and internal structure to reduce size.

## Constraints
- Keep the project building successfully (use `lake build` to verify).
- Do not edit the lakefile.
- Do not alter the names or statements of the theorems in each file.
- No `sorry` statements allowed - all proofs must be complete.
- Everything else (internal lemmas, helpers, modules, imports, notations, tactic usage, file layout) is fair game.

## Success Criteria
- Build passes with unchanged theorem interfaces.
- Aggregate `wc -l imo_*.lean` strictly decreases.

## Shared Library
- You may create or expand a common library in `ImoSteps.lean` for reusable utilities to reduce duplication.
- `imo_*.lean` files may import `ImoSteps` as needed without changing their exposed theorems.
- Each lemma in `ImoSteps.lean` should document which problems it has been used in (e.g., with a comment listing the problem files).

## Recommended Approach
- **Focus on abstracting shared lemmas** rather than naive tactic rewriting or formatting changes.
- Analyze the proofs one-by-one to identify common mathematical patterns and proof techniques.
- Extract reusable lemmas to `ImoSteps.lean` that capture these patterns.
- After analyzing each proof, check for lemmas that can be extracted and shared with previously analyzed proofs.
- Replace duplicated proof logic with calls to shared lemmas from `ImoSteps.lean`.
- Continuously verify that `lake build` works after each change.
- Ensure all `sorry` statements are removed before moving on to the next file.
- Revisit all previous proofs to check if more shared lemmas can be abstracted.

## Important Note
- **Avoid naive tactic rewriting** - Simply reformatting tactics or combining lines without semantic abstraction does not achieve meaningful compression.
- The goal is to identify and extract the mathematical patterns and lemmas that are genuinely shared across problems.
