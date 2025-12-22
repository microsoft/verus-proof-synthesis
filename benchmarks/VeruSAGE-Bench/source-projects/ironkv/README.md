# IronKV (IR)

**Source**: [Verified IronKV](https://github.com/verus-lang/verified-ironkv)

## Overview

IronKV is a verified distributed key-value store. Tasks involve delegation maps, marshalling, network protocols, and single-delivery message semantics.

## Tasks

| Category | Tasks |
|----------|-------|
| **IR** (IronKV) | 118 |

## Source Files

Tasks extracted from `ironsht/src/`:
- `delegation_map_v.rs` - Key delegation logic
- `marshal_v.rs` - Serialization/deserialization
- `net_sht_v.rs` - Network protocols
- `single_delivery_*.rs` - Message delivery semantics
- `verus_extra/` - Utility functions

## Extraction Notes

- Downloaded June 14th, 2025
- All executable/proof functions from delegation_map_v extracted
- Manual cleanup required for some edge cases
