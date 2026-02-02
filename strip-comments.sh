#!/bin/bash
# Script to strip comments and blank lines from Rust code
# Usage: ./strip-comments.sh input.rs output.rs

if [ "$#" -ne 2 ]; then
    echo "Usage: $0 input.rs output.rs"
    exit 1
fi

INPUT=$1
OUTPUT=$2

# Remove comments and blank lines:
# 1. Remove line comments (lines starting with //)
# 2. Remove blank lines (lines with only whitespace)
sed -e '/^[[:space:]]*\/\//d' -e '/^[[:space:]]*$/d' "$INPUT" > "$OUTPUT"
