#!/bin/bash
# Test script to verify that the Agda code generator outputs exactly the Rust code

set -e

REPO_ROOT="/home/runner/work/proving-philosophers/proving-philosophers"
GENERATED_FILE="/tmp/generated_main.rs"
ACTUAL_FILE="$REPO_ROOT/src/main.rs"

echo "Generating Rust code from Agda AST..."
python3 "$REPO_ROOT/agda/generate_rust.py" > "$GENERATED_FILE"

echo "Comparing generated code with actual Rust code..."
if diff -u "$ACTUAL_FILE" "$GENERATED_FILE"; then
    echo "✓ SUCCESS: Generated code matches actual Rust code exactly!"
    exit 0
else
    echo "✗ FAILURE: Generated code does not match actual Rust code"
    exit 1
fi
