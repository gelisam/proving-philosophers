# Proving Philosophers

Demonstrating one way in which we can prove Rust programs correct using the Agda proof assistant.

The dining philosophers is a classic concurrency setup where naive implementations can lead to starvation. We implement a classic solution to the problem in Rust, and then we formally verify that our implementation does not lead to starvation. Our approach is as follows:

1. Implement the dining philosophers setup in Rust.
2. Implement an idealized subset of the Rust language in Agda, and reimplement our Rust program in that subset.
3. Implement an idealized runtime for that subset where all possible interleavings of concurrent operations are modeled as an inifinite tree of possible executions.
4. Write an Agda proof that in every branch of that infinite tree, each philosopher eventually gets to eat an infinite number of times. Run `make build-agda` to machine-verify this proof.
5. Generate Rust code corresponding to the verified program. Run `make run-agda` to generate this code.
6. Verify that the generated Rust code is identical to our original Rust implementation in (1). Run `make test-agda` to perform this check.
7. Run the Rust implementation to see it in action. Run `make run-rust` to execute the Rust program.

(work in progress; the above description is aspirational)

## Requirements

- Rust (edition 2021 or later)
- Agda 2.6.3 or later (with standard library v1.7.3)
- GHC (Haskell compiler, required for compiling Agda code)
  - **Required: GHC 9.0 or earlier** (GHC 9.2+ is not compatible with Agda-generated Haskell code)
  - **Recommended: GHC 8.10.7** (tested in CI)