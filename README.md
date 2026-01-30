# Proving Philosophers

A Rust + Agda project demonstrating the dining philosophers problem with code generation from an abstract syntax tree.

## Overview

This project implements the dining philosophers problem where:
- **Rust code** (`src/main.rs`): Implements the solution using ordered forks to prevent deadlock
- **Agda code** (`agda/DiningPhilosophers.agda`): Defines an abstract syntax tree (AST) for simplified Rust operations and compiles to an executable that generates the exact Rust code

## Key Concepts

The Agda AST simplifies common Rust patterns into single operations:
- `Lock` → `.lock().unwrap()`
- `Sleep` → `thread::sleep(std::time::Duration::from_millis(100))`

This abstraction allows for easier reasoning about the algorithm while maintaining the ability to generate correct, idiomatic Rust code.

## Dining Philosophers Solution

The implementation uses the **ordered resource hierarchy** solution:
1. Five forks are numbered 0-4
2. Each philosopher sits between two forks
3. Philosophers always pick up the lower-numbered fork first, except the last philosopher
4. This ordering prevents circular wait conditions and thus prevents deadlock

## Project Structure

```
.
├── src/
│   └── main.rs                  # Rust implementation of dining philosophers
├── agda/
│   ├── DiningPhilosophers.agda  # Agda AST definition and code generator
│   └── DiningPhilosophers       # Compiled Agda executable (generated)
├── test_generation.sh           # Test that generated code matches actual code
├── Cargo.toml                   # Rust project configuration
└── README.md                    # This file
```

## Building and Running

### Quick Start

The project includes a Makefile for convenience:

```bash
# Run all tests
make test

# Build the Rust code
make build

# Run the dining philosophers
make run

# Run all quality checks (format, lint, test)
make check
```

### Rust Code

```bash
# Build the Rust code
cargo build

# Run the dining philosophers
cargo run
```

### Agda Code

To compile the Agda code generator:

```bash
cd agda
agda --compile --guardedness --ghc-flag=-Wwarn DiningPhilosophers.agda
```

This will create the `DiningPhilosophers` executable. To generate Rust code:

```bash
./agda/DiningPhilosophers > output.rs
```

### Testing Code Generation

```bash
# Test that the Agda generator produces exactly the Rust code
./test_generation.sh
```

This will:
1. Run the Agda executable to generate Rust code
2. Compare it with the actual `src/main.rs`
3. Report success if they match exactly

## AST Examples

The following AST nodes demonstrate the simplification:

```agda
-- Lock operation: expands to .lock().unwrap()
Lock "first_fork" "_guard1"
  generates: let _guard1 = first_fork.lock().unwrap();

-- Sleep operation: expands to thread::sleep with Duration
Sleep 100
  generates: thread::sleep(std::time::Duration::from_millis(100));
```

## Requirements

- Rust (edition 2021 or later)
- Agda 2.6.3 or later (with standard library)
- GHC (Haskell compiler, required for compiling Agda code)

## Testing

The project includes a test script that verifies the code generation works correctly:

```bash
./test_generation.sh
```

This ensures that running the Agda-compiled executable outputs exactly the Rust code in `src/main.rs`.