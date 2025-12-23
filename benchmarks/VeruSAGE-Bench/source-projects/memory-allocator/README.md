# Memory Allocator (MA)

**Source**: [Verified Memory Allocator](https://github.com/verus-lang/verified-memory-allocator)

## Overview

A formally verified memory allocator. Tasks focus on bin sizes, commit masks, layout calculations, and pigeonhole proofs.

## Tasks

| Category | Tasks |
|----------|-------|
| **MA** (Memory Allocator) | 89 |

## Source Files

Tasks extracted from the following files in [verus-mimalloc](https://github.com/verus-lang/verified-memory-allocator/tree/main/verus-mimalloc)
- `bin_sizes.rs` - Bin size calculations
- `commit_mask.rs` - Memory commit tracking
- `layout.rs` - Memory layout proofs
- `pigeonhole.rs` - Pigeonhole principle proofs
- `config.rs`


## Extraction Notes

- Downloaded from main branch on 6/13/2025
- Tasks that involve complicated tracked pointers excluded (complex Verus feature)
- Tasks that involve `tokenized_state_machine!` excluded (complex Verus feature)
- All other tasks that require proof annotations in [verus-mimalloc](https://github.com/verus-lang/verified-memory-allocator/tree/main/verus-mimalloc) are extracted and put here (note, quite some functions that used to require proof annotations no longer do under the later versions of Verus)
- `Metadata::Thin` replaced with `()` for latest Verus compatibility
