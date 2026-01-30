# Proving Philosophers

A Rust + Agda project demonstrating the dining philosophers problem with formally verified code generation.

## Overview

This project implements the dining philosophers problem where:
- **Rust code** (`src/main.rs`): Implements the solution using ordered forks to prevent deadlock
- **Agda code** (`agda/DiningPhilosophers.agda`): Defines an abstract syntax tree (AST) for simplified Rust operations
- **Code Generator** (`agda/generate_rust.py`): Demonstrates the AST concept by generating the exact Rust code

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
│   └── main.rs              # Rust implementation of dining philosophers
├── agda/
│   ├── DiningPhilosophers.agda  # Agda AST definition
│   └── generate_rust.py     # Python implementation demonstrating AST concept
├── test_generation.sh       # Test that generated code matches actual code
├── Cargo.toml              # Rust project configuration
└── README.md               # This file
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

### Testing Code Generation

```bash
# Test that the generator produces exactly the Rust code
./test_generation.sh
```

This will:
1. Run the code generator to produce Rust code
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
- Python 3 (for the code generator demonstration)
- Agda (optional, for working with the formal AST definition)

## Testing

The project includes a test script that verifies the code generation works correctly:

```bash
./test_generation.sh
```

This ensures that running the Agda code (or its Python equivalent) outputs exactly the Rust code in `src/main.rs`.