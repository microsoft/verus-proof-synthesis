# NRKernel (NR)

**Source**: [Verified NRKernel](https://github.com/matthias-brun/verified-nrkernel)

## Overview

A verified kernel with page table verification. Tasks focus on MMU operations, page table walks, OS refinement proofs, and memory management.

## Tasks

| Category | Tasks |
|----------|-------|
| **NR** (NRKernel) | 204 |

## Source Modules

Key modules with extracted tasks:
- `spec_t/mmu/` - MMU specification and proofs
- `spec_t/hlspec.rs` - High-level specification
- `spec_t/os_invariant.rs` - OS invariants
- `impl_u/l1.rs`, `impl_u/l2_impl.rs` - Page table implementation
- `impl_u/os_refinement.rs` - OS refinement proofs
- `impl_u/wrapped_token.rs` - Token management

## Extraction Notes

- All 204 non-trivial proof/exec functions extracted
- Uses `--cfg feature="impl"` for verification
- Most functions from `spec_t::mmu::rl3` excluded (log-all issues)
