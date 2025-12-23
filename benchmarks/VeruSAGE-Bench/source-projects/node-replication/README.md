# Node Replication (NO)

**Source**: [Verified Node Replication](https://github.com/verus-lang/verified-node-replication)

## Overview

A verified node replication library for concurrent data structures. Tasks focus on cyclic buffers, linearization proofs, and unbounded log verification.

## Tasks

| Category | Tasks |
|----------|-------|
| **NO** (Node Replication) | 29 |

## Source Modules

Many `Node Replication` functions' proof involves complicated Verus features and hence are excluded.

As a result, most of the extracted tasks come from files in the [spec](https://github.com/verus-lang/verified-node-replication/tree/main/verified-node-replication/src/spec) folder of Node Replication.

- `spec/cyclicbuffer.rs` - Cyclic buffer specifications
- `spec/linearization.rs` - Linearization proofs
- `spec/unbounded_log.rs` - Unbounded log verification
- `spec/unbounded_log_refines_simplelog.rs`
- `spec/utils.rs` - Utility functions

And, a couple of tasks extracted from [exec/utils](https://github.com/verus-lang/verified-node-replication/blob/main/verified-node-replication/src/exec/utils.rs)

## Extraction Notes

- All non-trivial proof/exec functions with ensures clauses extracted
- State machine/tokenized state machine functions excluded
- `exec/rwlock.rs` excluded (concurrency)
- Only simple state machine field access included

## Acknowledgement

Many thanks to the original authros of Node Replication.
