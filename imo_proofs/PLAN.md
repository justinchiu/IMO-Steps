# IMO Proofs Refactoring Plan

## Objective
Shorten IMO proof files by extracting common lemmas into a shared library, reducing code duplication and improving maintainability.

## Analysis Summary
- **22 IMO proof files** analyzed (1959-2023)
- **~5,800 lines of Lean code** total
- Estimated **30-40% reduction** possible through lemma extraction
- Common patterns identified across number theory, algebra, inequalities, and combinatorics

## Library Structure

```
imo_proofs/
├── ImoSteps/
│   ├── Common/
│   │   ├── NumberTheory.lean     # GCD, modular arithmetic, primes, factorials
│   │   ├── Algebra.lean          # Algebraic identities, factorizations, square manipulations
│   │   ├── Inequalities.lean     # Real inequalities, AM-GM, rearrangement, positivity
│   │   ├── Combinatorics.lean    # Finset operations, sums, products, binomial coefficients
│   │   ├── Trigonometry.lean     # Trig identities, product-to-sum formulas
│   │   └── Tactics.lean          # Custom tactics and automation helpers
│   └── Basic.lean                # Re-exports all common modules
├── ImoSteps.lean                  # Root module (imports ImoSteps.Basic)
└── [individual IMO files...]      # Refactored to use shared lemmas
```

## Key Lemmas to Extract

### Number Theory (NumberTheory.lean)
- GCD manipulation patterns (used in 8+ files)
- Modular arithmetic helpers with `decide` automation
- Factorial bounds and divisibility lemmas
- Prime number properties and divisibility patterns
- Common number theory inequalities

### Algebra (Algebra.lean)
- Square completion and manipulation lemmas
- Difference of squares and other factorizations
- Polynomial identities (sum of cubes, etc.)
- Algebraic rearrangement patterns
- Sign analysis helpers

### Inequalities (Inequalities.lean)
- Rearrangement inequality and variants
- AM-GM for 2, 3, and n variables
- Cauchy-Schwarz applications
- Square root manipulation lemmas
- Positivity reasoning patterns
- Triangle inequality variants

### Combinatorics (Combinatorics.lean)
- Finset sum/product splitting lemmas
- Binomial coefficient identities
- Sum manipulation patterns
- Range and interval operations
- Pigeonhole principle applications

### Tactics (Tactics.lean)
- Custom tactics for inequality chains
- Positivity automation
- Contradiction patterns
- Case analysis helpers
- Simplification sets

## Refactoring Strategy

### Phase 1: Create Library Infrastructure
1. Create `ImoSteps/Common/` directory structure
2. Implement core lemmas in each module
3. Create `ImoSteps.Basic` that imports all common modules
4. Update `ImoSteps.lean` to use the new structure

### Phase 2: Extract Common Lemmas
For each category:
1. Identify lemmas used in 3+ files
2. Generalize lemmas to be maximally reusable
3. Add appropriate docstrings
4. Include simp lemmas where appropriate

### Phase 3: Refactor Individual Files
For each IMO problem file:
1. Add `import ImoSteps`
2. Remove duplicate lemma definitions
3. Replace with calls to shared lemmas
4. Simplify proofs using new tactics
5. Verify compilation

### Phase 4: Optimization
1. Identify remaining duplication
2. Create problem-specific helper modules if needed
3. Add custom simp sets for common patterns
4. Document best practices

## Expected Impact

### Quantitative
- **Lines of code**: ~5,800 → ~3,500-4,000 (30-40% reduction)
- **Compilation time**: Slight improvement due to shared compiled modules
- **Proof length**: Individual files reduced by 20-60%

### Qualitative
- **Maintainability**: Easier to update common patterns
- **Readability**: Cleaner, more focused proofs
- **Extensibility**: New problems can leverage existing library
- **Learning curve**: Easier to understand proof patterns

## Files with Greatest Reduction Potential

1. **imo_1985_p6.lean**: 1,310 lines → ~500 lines (60% reduction)
2. **imo_2022_p5.lean**: 640 lines → ~300 lines (53% reduction)
3. **imo_1992_p1.lean**: 480 lines → ~200 lines (58% reduction)
4. **imo_1997_p5.lean**: 390 lines → ~180 lines (54% reduction)
5. **imo_1984_p6.lean**: 380 lines → ~180 lines (53% reduction)

## Verification Script

```bash
#!/bin/bash
# verify_compilation.sh

echo "IMO Proofs Compilation Verification"
echo "===================================="

cd /home/justinchiu/code/lean/IMO-Steps/imo_proofs

# Clean build
echo "Cleaning previous build..."
lake clean

# Update dependencies
echo "Updating dependencies..."
lake update

# Build the project
echo "Building all proofs..."
if lake build; then
    echo "✓ Build successful"
else
    echo "✗ Build failed"
    exit 1
fi

# Test individual files
echo -e "\nTesting individual IMO files..."
failed_files=()

for file in imo_*.lean; do
    echo -n "Testing $file... "
    if lake env lean "$file" 2>/dev/null | grep -q "error"; then
        echo "✗ FAILED"
        failed_files+=("$file")
    else
        echo "✓ OK"
    fi
done

# Summary
echo -e "\n===================================="
if [ ${#failed_files[@]} -eq 0 ]; then
    echo "✓ All IMO proofs compile successfully!"
    exit 0
else
    echo "✗ The following files failed to compile:"
    for file in "${failed_files[@]}"; do
        echo "  - $file"
    done
    exit 1
fi
```

## Implementation Timeline

1. **Hour 1-2**: Create library structure and core modules
2. **Hour 2-4**: Implement common lemmas in each category
3. **Hour 4-8**: Refactor individual IMO files
4. **Hour 8-9**: Testing and verification
5. **Hour 9-10**: Documentation and optimization

## Success Metrics

- [ ] All IMO files compile without errors
- [ ] At least 30% reduction in total lines of code
- [ ] No increase in compilation time
- [ ] All proofs remain valid and complete
- [ ] Clear documentation of shared lemmas

## Risk Mitigation

- **Version control**: All changes on separate branch
- **Incremental refactoring**: Test after each file change
- **Rollback plan**: Original files preserved in git history
- **Verification script**: Automated testing of all proofs

## Next Steps

1. Create the library directory structure
2. Implement core lemmas starting with NumberTheory
3. Refactor files with highest reduction potential first
4. Run verification script after each major change
5. Document any unexpected issues or patterns discovered