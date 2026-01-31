# Reusable Workflow for Dependency Setup

This directory contains a reusable workflow (`copilot-setup-steps.yml`) that sets up all dependencies required for the proving-philosophers project.

## Purpose

The `copilot-setup-steps.yml` workflow was created to avoid repeating dependency installation steps for each Copilot task or other workflow that needs to run tests or build the project.

## What It Does

The reusable workflow:
1. Checks out the repository
2. Installs Rust (latest stable)
3. Sets up 5 different caches for performance:
   - Cargo registry (crate metadata)
   - Cargo index (crates.io index)
   - Cargo build output (compiled artifacts)
   - Agda Standard Library (v1.7.3)
   - GHC installation (8.10.7)
4. Installs Agda 2.6.3
5. Installs GHC 8.10.7 via ghcup (required for compatibility)
6. Installs and configures Agda Standard Library v1.7.3
7. Runs the test suite (`make all`)

## How to Use

To use this reusable workflow in another workflow, simply call it using the `uses` keyword:

```yaml
name: My Custom Workflow

on:
  # Your trigger events here
  push:
    branches: [main]

jobs:
  my-job:
    uses: ./.github/workflows/copilot-setup-steps.yml
```

This will execute all the setup steps and tests in a single job.

## Example: Separate Setup and Custom Steps

If you need to perform custom steps after setup without running tests immediately, you can create a modified version:

```yaml
name: Custom Task

on:
  workflow_dispatch:

jobs:
  setup-and-custom:
    runs-on: ubuntu-latest
    permissions:
      contents: read
    env:
      AGDA_STDLIB_VERSION: v1.7.3

    steps:
      # Checkout
      - uses: actions/checkout@v3

      # You could extract just the setup steps here
      # and add your custom steps after
```

## Benefits

- **DRY (Don't Repeat Yourself)**: Setup code is in one place
- **Consistency**: All workflows use the same setup
- **Maintainability**: Changes to setup only need to be made once
- **Performance**: All caches are properly configured
- **Copilot Integration**: Makes it easy to create new Copilot tasks without duplicating setup

## Current Usage

This workflow is currently used by:
- `.github/workflows/test.yml` - Main test workflow for pushes and PRs
