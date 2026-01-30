# Proving Philosophers

A Rust + Agda project demonstrating the dining philosophers problem with code generation from an abstract syntax tree.

## Requirements

- Rust (edition 2021 or later)
- Agda 2.6.3 or later (with standard library v1.7.3)
- GHC (Haskell compiler, required for compiling Agda code)
  - **Required: GHC 9.0 or earlier** (GHC 9.2+ is not compatible with Agda-generated Haskell code)
  - **Recommended: GHC 8.10.7** (tested in CI)

## Testing

Run `make test-agda` to verify that the Rust implementation of the dining philosophers never causes any philosophers to starve (it doesn't do that yet but that's the intention), then check that the simplified model which the proof uses does match the Rust code which would be used in production.