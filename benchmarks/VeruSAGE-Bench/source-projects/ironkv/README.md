# IronKV (IR)

**Source**: [Verified IronKV](https://github.com/verus-lang/verified-ironkv)

## Overview

IronKV is a verified distributed key-value store. Tasks involve delegation maps, marshalling, network protocols, and single-delivery message semantics.

## Tasks

| Category | Tasks |
|----------|-------|
| **IR** (IronKV) | 118 |

## Source Files

Tasks extracted from [ironsht/src/](https://github.com/verus-lang/verified-ironkv/tree/main/ironsht/src):
- `delegation_map_v.rs` - Key delegation logic
- `marshal_v.rs` - Serialization/deserialization
- `net_sht_v.rs` - Network protocols
- `single_delivery_*.rs` - Message delivery semantics
- `verus_extra/` - Utility functions

## Extraction Notes

- Downloaded June 14th, 2025
- All executable/proof functions that require proof annotations from `ironsht/src` are extracted
- Quite some functions that used to require proof annotations no long do with the latest version of Verus, and hence are excluded from our benchmark suite

## Acknowledgement

Many thanks to the IronKV authors.
