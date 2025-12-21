# Anvil (AL & AC)

**Source**: [Anvil Project](https://github.com/anvil-verifier/anvil)

## Overview

Anvil is a framework for building formally verified Kubernetes controllers. The extracted tasks come from temporal logic proofs and controller verification.

## Tasks

| Category | Tasks | Source Directory |
|----------|-------|------------------|
| **AL** (Anvil) | 104 | `vstd_ext/` and `temporal_logic/` |
| **AC** (Anvil-Advanced) | 63 | `vreplicaset_controller/` |
| **Total** | **167** | |

### AL Tasks (vstd_ext + temporal_logic)
- 29 functions from `anvil/src/vstd_ext`
- 75 functions from `anvil/src/temporal_logic`
- Standard verification tasks

### AC Tasks (vreplicaset_controller)
- 63 functions from `anvil/src/controller/vreplicaset_controller`
- More complex tasks with external dependencies
- Recommended by Anvil authors as focus area

## Extraction Notes

- All non-trivial proof functions extracted
- AC tasks require dependency compilation (see deps_hack)
- Some AC files are 4000+ lines (complex verification)
