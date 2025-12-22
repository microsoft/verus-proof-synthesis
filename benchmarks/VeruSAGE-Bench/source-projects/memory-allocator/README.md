# Memory Allocator (MA)

**Source**: [Verified Memory Allocator](https://github.com/verus-lang/verified-memory-allocator)

## Overview

A formally verified memory allocator. Tasks focus on bin sizes, commit masks, layout calculations, and pigeonhole proofs.

## Tasks

| Category | Tasks |
|----------|-------|
| **MA** (Memory Allocator) | 89 |

## Source Files

Tasks extracted from:
- `bin_sizes.rs` - Bin size calculations
- `commit_mask.rs` - Memory commit tracking
- `layout.rs` - Memory layout proofs
- `pigeonhole.rs` - Pigeonhole principle proofs

## Extraction Notes

- Downloaded from main branch on 6/13/2025
- Files with tracked pointers excluded (complex Verus feature)
- Some `by(compute_only)` assertions replaced with assumes
- `Metadata::Thin` replaced with `()` for latest Verus compatibility
