# CI Caching Strategy

This document explains the caching strategy used in the GitHub Actions CI workflow for the proving-philosophers project.

## Overview

The CI workflow uses 5 different caches to speed up build times:

1. **Cargo Registry Cache** - Downloaded crate metadata
2. **Cargo Index Cache** - Index of available crates
3. **Cargo Build Cache** - Compiled Rust artifacts
4. **Agda Standard Library Cache** - Cloned agda-stdlib repository
5. **GHC Cache** - GHC compiler installation

## Cache Details

### 1. Cargo Registry Cache

**Path:** `~/.cargo/registry`

**Purpose:** Stores downloaded crate metadata from crates.io. This avoids re-downloading package information on every build.

**Cache Key:** `${{ runner.os }}-cargo-registry-${{ hashFiles('**/Cargo.toml') }}`

**Invalidated When:**
- Any `Cargo.toml` file in the repository changes
- Dependencies are added, removed, or their versions are updated
- The operating system changes (unlikely in CI)

**Restore Keys:** `${{ runner.os }}-cargo-registry-`
- If no exact match is found, uses the most recent cache with this prefix
- This is useful when dependencies are updated but most remain the same

**Example:**
- Key: `Linux-cargo-registry-abc123def456` (where `abc123def456` is the hash of Cargo.toml)
- If Cargo.toml changes, the hash changes, creating a new cache entry

### 2. Cargo Index Cache

**Path:** `~/.cargo/git`

**Purpose:** Contains the index of all available crates from crates.io. This is essentially a local mirror of the crates.io registry index.

**Cache Key:** `${{ runner.os }}-cargo-git-${{ hashFiles('**/Cargo.toml') }}`

**Invalidated When:**
- Any `Cargo.toml` file changes
- Dependencies are added, removed, or their versions are updated
- The operating system changes

**Restore Keys:** `${{ runner.os }}-cargo-git-`
- Falls back to the most recent index cache if no exact match

**Why Separate from Registry?**
- The git index and registry serve different purposes in Cargo's dependency resolution
- Caching them separately provides more granular control and better cache hit rates

### 3. Cargo Build Cache

**Path:** `target`

**Purpose:** Stores compiled Rust artifacts including:
- Compiled dependencies (in `target/debug/deps` or `target/release/deps`)
- Compiled project code
- Incremental compilation metadata

**Cache Key:** `${{ runner.os }}-cargo-build-${{ hashFiles('**/Cargo.toml') }}`

**Invalidated When:**
- Any `Cargo.toml` file changes
- Dependencies are added, removed, or their versions are updated
- The operating system changes

**Restore Keys:** `${{ runner.os }}-cargo-build-`
- Uses partial matches to reuse build artifacts when possible

**Important Notes:**
- Source code changes do NOT invalidate this cache
- Cargo's incremental compilation automatically rebuilds only changed files
- This is the largest cache and provides the biggest speed improvement
- The cache key is based on Cargo.toml, not source code, to maximize reuse

### 4. Agda Standard Library Cache

**Path:** `~/.agda-stdlib`

**Purpose:** Stores the cloned Agda standard library repository at version v1.7.3.

**Cache Key:** `${{ runner.os }}-agda-stdlib-${{ env.AGDA_STDLIB_VERSION }}`

**Invalidated When:**
- The `AGDA_STDLIB_VERSION` environment variable changes (currently `v1.7.3`)
- The operating system changes
- Manual cache clearing in GitHub Actions

**Restore Keys:** None
- No fallback keys because version compatibility is critical
- Either we have the exact version or we clone it fresh

**Why Cache This?**
- The standard library is ~150MB and doesn't change often
- Cloning from GitHub takes time and uses bandwidth
- Version is pinned, so cache is stable

**Version Compatibility:**
- Agda 2.6.3 requires agda-stdlib v1.7.3
- Mismatched versions cause compilation errors
- That's why we don't use restore keys here

### 5. GHC Cache

**Path:** `~/.ghcup`

**Purpose:** Stores the GHC 8.10.7 Haskell compiler installation managed by ghcup.

**Cache Key:** `${{ runner.os }}-ghcup-ghc-8.10.7`

**Invalidated When:**
- The GHC version in the key changes (hardcoded to `8.10.7`)
- The operating system changes
- Manual cache clearing

**Restore Keys:** None
- Exact version match required for compilation compatibility
- Different GHC versions can produce incompatible code

**Why GHC 8.10.7?**
- Agda 2.6.3 generates Haskell code
- GHC 9.4.7 (the default in Ubuntu) has deprecated the `*` type operator
- GHC 8.10.7 is compatible with Agda 2.6.3 and doesn't have this deprecation
- Compiling from scratch via ghcup takes several minutes

## Cache Strategy Summary

| Cache | Size | Invalidation Trigger | Has Restore Keys? |
|-------|------|---------------------|-------------------|
| Cargo Registry | ~10-50MB | Cargo.toml changes | Yes |
| Cargo Index | ~200MB | Cargo.toml changes | Yes |
| Cargo Build | ~100MB-1GB | Cargo.toml changes | Yes |
| Agda Stdlib | ~150MB | Version change | No |
| GHC | ~500MB | Version change | No |

## Cache Hit Scenarios

### Scenario 1: No Changes
If no files have changed since the last CI run:
- ✅ All 5 caches hit exactly
- Build completes in ~1-2 minutes

### Scenario 2: Only Source Code Changes
If only `.rs` or `.agda` files changed:
- ✅ All 5 caches hit exactly
- Cargo rebuilds only changed files incrementally
- Build completes in ~2-3 minutes

### Scenario 3: Dependency Changes
If `Cargo.toml` changes (new dependency or version update):
- ⚠️ Cargo caches invalidated, but restore keys used
- ✅ Agda and GHC caches still hit
- Most dependencies still cached via restore keys
- Only new/changed dependencies downloaded and compiled
- Build completes in ~3-5 minutes

### Scenario 4: Version Upgrades
If `AGDA_STDLIB_VERSION` changes or GHC version changes:
- ⚠️ Affected cache invalidated completely
- Other caches unaffected
- Build completes in ~5-10 minutes

### Scenario 5: Cold Start
If all caches are empty (first run or manual clear):
- ❌ No cache hits
- Everything downloaded and compiled from scratch
- Build completes in ~10-15 minutes

## Best Practices

1. **Don't update Cargo.toml frequently** - Batch dependency updates when possible
2. **Version pins are intentional** - Don't change AGDA_STDLIB_VERSION or GHC version unless necessary
3. **Restore keys are strategic** - They provide partial cache hits when exact matches fail
4. **Cache invalidation is conservative** - Better to rebuild than use incompatible cached artifacts

## Troubleshooting

### Cache Not Being Used
- Check if the cache key has changed unexpectedly
- Verify that the paths being cached exist after the installation steps
- GitHub Actions has a 10GB cache size limit per repository

### Build Failures After Caching
- Try clearing caches manually in GitHub Actions settings
- Check if version incompatibilities have been introduced
- Verify that cache paths are correct for your installation

### Slow Builds Despite Caching
- Check cache hit rates in the workflow logs
- Look for "Cache hit" vs "Cache miss" messages
- Consider if cache overhead exceeds benefit for small projects

## Future Improvements

Potential optimizations for the caching strategy:

1. Add `Cargo.lock` to cache keys for more precise invalidation
2. Implement cache sharding for large build artifacts
3. Add pre-warming caches on a schedule for faster cold starts
4. Consider using GitHub Actions cache versioning for easier management
