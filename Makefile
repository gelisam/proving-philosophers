.PHONY: all build test run clean check-format lint

all: test

# Build the Rust code
build:
	cargo build

# Run all tests
test: test-generation test-rust

# Test that the Agda code generator produces the correct Rust code
test-generation:
	@echo "Testing code generation..."
	./test_generation.sh

# Run Rust tests (if any)
test-rust:
	@echo "Running Rust tests..."
	cargo test

# Run the dining philosophers program
run:
	cargo run

# Check Rust code formatting
check-format:
	cargo fmt --check

# Run Rust linter
lint:
	cargo clippy -- -D warnings

# Clean build artifacts
clean:
	cargo clean
	rm -f /tmp/generated_main.rs

# Run all quality checks
check: check-format lint test
	@echo "All checks passed!"
