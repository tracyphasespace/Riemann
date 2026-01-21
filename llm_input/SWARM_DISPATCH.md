# Swarm Dispatch: Ready Tasks

## Job Files Ready for Distribution

| Job | File | Priority | Sorries |
|-----|------|----------|---------|
| Job 2 | `job2_rayleigh_identity.lean` | HIGH | 4 |
| Job 3 | `job3_zero_kernel_bridge.lean` | HIGH | 5 |
| Job 4 | `job4_chirality_assembly.lean` | HIGH | 3 |
| Job 5 | `job5_bivector_lemmas.lean` | MEDIUM | 5 |

## Completed Jobs
- **Job 1**: Linear Independence - DONE by Agent #001
  - File: `DiophantineGeometry.lean`
  - Theorem: `fta_all_exponents_zero`

## How to Claim

1. Select ONE job file
2. State: "I am Agent #XXX claiming Job N"
3. Complete ALL sorries in that file
4. Return the complete file with NO sorries
5. Include brief proof strategy notes

## Expected Output Format

```lean
/-!
# Job N Complete
# Agent: #XXX
# Status: ✅ All sorries resolved
-/

-- [Complete lean code with proofs]
```

## Dependencies

- Job 4 depends on Job 2 (Rayleigh identity)
- Job 3 is independent
- Job 5 is a prerequisite for Job 2

Recommended order: Job 5 → Job 2 → Job 4, Job 3 (parallel)

## Context Files (Read-Only Reference)

Agents may reference these existing files for context:
- `Riemann/ProofEngine/DiophantineGeometry.lean` - Proven FTA
- `Riemann/ProofEngine/BridgeObligations.lean` - Axiom structure
- `Riemann/ProofEngine/AnalyticBridge.lean` - Full spectral theory
- `Riemann/ProofEngine/STATUS.md` - Current proof status
