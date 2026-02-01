# CI Caching Strategy

This document describes the caching strategy used in the GitHub Actions workflow to speed up builds and reduce CI times.

## Overview

The workflow uses 6 separate caches to optimize different aspects of the build process. Each cache is strategically designed to minimize redundant work while ensuring correctness.

## Cache Layers

### Cache 1: Cargo Registry
**Path:** `~/.cargo/registry`  
**Purpose:** Stores downloaded crate metadata from crates.io  
**Invalidation:** When `Cargo.toml` changes (new dependencies or version updates)  
**Restore keys:** Falls back to any previous cargo registry cache if exact match not found  
**Benefit:** Avoids re-downloading crate metadata on each build

### Cache 2: Cargo Index
**Path:** `~/.cargo/git`  
**Purpose:** Stores the index of available crates from crates.io  
**Invalidation:** When `Cargo.toml` changes (new dependencies or version updates)  
**Restore keys:** Falls back to any previous cargo index cache if exact match not found  
**Benefit:** Avoids re-fetching the crates.io index

### Cache 3: Cargo Build Output
**Path:** `target`  
**Purpose:** Stores compiled Rust artifacts (dependencies and project code)  
**Invalidation:** When `Cargo.toml` changes (new dependencies or version updates)  
**Restore keys:** Falls back to any previous build cache if exact match not found  
**Note:** Source code changes don't invalidate cache; incremental compilation reuses artifacts  
**Benefit:** Significantly speeds up Rust compilation by reusing compiled dependencies

### Cache 4: Agda Standard Library
**Path:** `~/.agda-stdlib`  
**Purpose:** Stores the cloned agda-stdlib repository (v1.7.3) including any compiled `.agdai` files  
**Invalidation:** When `AGDA_STDLIB_VERSION` environment variable changes  
**Restore keys:** None (exact version match required for compatibility)  
**Benefit:** Avoids re-cloning the standard library repository and preserves compiled library modules

### Cache 5: GHC Installation
**Path:** `~/.ghcup`  
**Purpose:** Stores the GHC 8.10.7 compiler installed via ghcup  
**Invalidation:** When GHC version changes (hardcoded to 8.10.7)  
**Restore keys:** None (exact version match required for compilation compatibility)  
**Benefit:** Avoids re-installing GHC 8.10.7, which takes several minutes

### Cache 6: Compiled Agda Artifacts
**Path:** `~/.agda`  
**Purpose:** Stores compiled Agda interface files (`.agdai`) and configuration files  
**Invalidation:** When `AGDA_STDLIB_VERSION` changes (different stdlib version)  
**Restore keys:** None (exact version match required for compatibility)  
**Benefit:** Preserves compiled artifacts from standard library usage, saving 2-5 minutes per build  
**Key files cached:**
- `.agdai` files (compiled Agda interface files)
- `libraries` (Agda library registry)
- `defaults` (default libraries configuration)

## Performance Impact

Without caching:
- Agda standard library clone: ~30 seconds
- GHC installation: ~3-5 minutes
- Agda library compilation (first time): ~2-5 minutes
- Rust dependency compilation: ~1-2 minutes
- **Total: ~7-13 minutes**

With full cache hits:
- Agda library compilation (cached): ~10 seconds
- Rust dependency compilation (cached): ~10 seconds
- **Total: ~1-2 minutes**

## Cache Key Strategy

The caches use different strategies for cache keys:

1. **Content-based keys** (Cargo caches): Use `hashFiles('**/Cargo.toml')` to invalidate when dependencies change
2. **Version-based keys** (Agda, GHC): Use hardcoded version numbers to ensure exact version matches
3. **Restore keys**: Only used for Cargo caches to allow partial cache hits

## Maintenance

### Updating Agda Standard Library

To update to a new version of agda-stdlib:
1. Update `AGDA_STDLIB_VERSION` in `.github/workflows/copilot-setup-steps.yml`
2. This will automatically invalidate Cache 4 and Cache 6
3. The next build will clone and compile the new version

### Updating GHC

To update to a new version of GHC:
1. Update the version number in the "Install Agda" step
2. Update the cache key in Cache 5
3. The next build will install and cache the new version

## Troubleshooting

### Cache not being restored

Check the GitHub Actions logs for:
- Cache hit/miss messages
- Ensure cache key matches expectations
- Verify paths are correct

### Stale cache causing issues

If a cache becomes corrupted or stale:
1. Update the cache key in the workflow file
2. Or manually delete the cache from GitHub Settings → Actions → Caches

### Cache size limits

GitHub Actions cache has a 10 GB limit per repository. Monitor cache sizes:
- Individual cache entries are typically 100-500 MB
- Oldest caches are automatically evicted when limit is reached
