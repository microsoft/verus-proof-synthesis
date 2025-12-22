# Vest (VE)

**Source**: [Vest Project](https://github.com/secure-foundations/vest)

## Overview

Vest is a verified serialization/deserialization combinator library. Tasks focus on parser/serializer correctness proofs and format specifications.

## Tasks

| Category | Tasks |
|----------|-------|
| **VE** (Vest) | 22 |

## Source Modules

- `properties/` - Combinator property proofs
- `regular/leb128/` - LEB128 encoding proofs
- `regular/repetition/` - Repetition combinator proofs
- `regular/uints/` - Unsigned integer proofs
- `utils/` - Utility function proofs

## Task Types

- `SecureSpecBombinator` - Security specification proofs
- `lemma_parse_*` - Parser correctness lemmas
- `lemma_serialize_*` - Serializer correctness lemmas
- `theorem_*_roundtrip` - Roundtrip property proofs

## Extraction Notes

- 22 non-trivial proof/exec functions extracted
- Trait implementation proofs excluded (repetitive)
- Some trait-related lemmas kept in context
