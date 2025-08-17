# Code Compression

Refactor and compress the Lean sources as much as possible while keeping all proofs valid.

## Goal
- Preserve the theorems defined in each `imo_*.lean` exactly.
- Minimize the total number of lines of code across the repo.
- Allow redesigning proofs, lemmas, and internal structure to reduce size.

## Constraints
- Keep the project building successfully.
- Do not alter the names or statements of the theorems in each file.
- No `sorry` statements allowed - all proofs must be complete.
- Everything else (internal lemmas, helpers, modules, imports, notations, tactic usage, file layout) is fair game.

## Success Criteria
- Build passes with unchanged theorem interfaces.
- Aggregate `wc -l imo_*.lean` strictly decreases.

## Shared Library
- You may create or expand a common library in `ImoSteps.lean` for reusable utilities to reduce duplication.
- `imo_*.lean` files may import `ImoSteps` as needed without changing their exposed theorems.
