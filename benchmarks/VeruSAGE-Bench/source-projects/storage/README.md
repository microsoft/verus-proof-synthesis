# Verified Storage (ST)

**Source**: [Verified Storage](https://github.com/microsoft/verified-storage)

## Overview

A verified persistent storage system by Microsoft Research. Tasks focus on log implementation, invariant proofs, and persistent memory utilities.

## Tasks

| Category | Tasks |
|----------|-------|
| **ST** (Storage) | 63 |

## Source Components

- `storage_node/` - Main verified storage component
- `deps_hack/` - Required dependencies

## Task Categories

- `append_*.rs` - Log append operations
- `inv_*.rs` - Invariant proofs
- `layout_*.rs` - Layout specifications
- `logimpl_*.rs` - Log implementation
- `pmemutil_*.rs` - Persistent memory utilities
- `subregion_*.rs` - Memory subregion operations

## Prerequisites: Build Dependencies First

⚠️ **Important**: Before running any Storage tasks, you must build the dependencies crate.

### Step 1: Clone and Checkout

```bash
git clone https://github.com/microsoft/verified-storage.git
cd verified-storage
git checkout f49f053ab6b28b54b9443503621abd476a58839a
```

### Step 2: Apply Patch

Apply `storage.patch` to update the toolchain version:

```bash
git apply /path/to/VeruSAGE-Bench/source-projects/verified-storage/storage.patch
```

### Step 3: Build Dependencies

```bash
cd deps_hack
cargo build
```

This creates the required `libdeps_hack.rlib` in `deps_hack/target/debug/`.

### Step 4: Verify a Task

```bash
verus -L dependency=deps_hack/target/debug/deps \
      --extern deps_hack=deps_hack/target/debug/libdeps_hack.rlib \
      <task_file>.rs
```

## Extraction Notes

- Dependency build required before verification
- Tasks that involve Ghost/Tracked arguments went through some special refactoring: we replaced the exact Ghost/Tracked expression with place-holder expressions, and leveraged `proof_from_false` and `arbitrary` to make sure the unverified task file is compilable.
- Broadcast use statements removed in the unverified task files

## Acknowledgement

Many thanks to the authors of Verified Storage; we got a ton of support from them!
