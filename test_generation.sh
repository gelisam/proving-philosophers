#!/bin/bash
# Test script to verify that the Agda code generator outputs exactly the Rust code

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GENERATED_FILE="/tmp/generated_main.rs"
ACTUAL_FILE="$REPO_ROOT/rust/main.rs"

echo "Generating Rust code from Agda AST..."
"$REPO_ROOT/agda-build/Main" > "$GENERATED_FILE"

echo "Comparing generated code with actual Rust code..."
if diff -u "$ACTUAL_FILE" "$GENERATED_FILE"; then
    echo "✓ SUCCESS: Generated code matches actual Rust code exactly!"
    exit 0
else
    echo "✗ FAILURE: Generated code does not match actual Rust code"
    exit 1
fi
