#!/bin/bash
# verify_compilation.sh - Verify all IMO proofs compile successfully

echo "IMO Proofs Compilation Verification"
echo "===================================="

# Navigate to the imo_proofs directory
cd "$(dirname "$0")" || exit 1

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
success_count=0
total_count=0

for file in imo_*.lean; do
    if [ -f "$file" ]; then
        total_count=$((total_count + 1))
        echo -n "Testing $file... "
        
        # Try to compile the file and check for errors
        if lake env lean "$file" 2>&1 | grep -q "error"; then
            echo "✗ FAILED"
            failed_files+=("$file")
        else
            echo "✓ OK"
            success_count=$((success_count + 1))
        fi
    fi
done

# Summary
echo -e "\n===================================="
echo "Results: $success_count/$total_count files compiled successfully"

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