# Claude Code Instructions for Riemann/Lean Project

## Build Coordination

**IMPORTANT**: Before running `lake build`, always check if another build is in progress:

```bash
# Check for running lake processes
pgrep -f "lake build" || echo "No build running"

# Or check for .lake lock files
ls .lake/build/.lock 2>/dev/null && echo "Build may be in progress"
```

If a build is running, wait for it to complete before starting another.

## Project Overview

This is a Lean 4 formalization of a geometric/spectral approach to the Riemann Hypothesis.

- **Lean Version**: 4.27.0-rc1
- **Mathlib**: v4.27.0-rc1
- **Build command**: `lake build`

## Current Status

| Category | Count |
|----------|-------|
| `sorry` | 0 ✅ |
| Axioms | 0 ✅ |
| Trivial placeholders | 0 ✅ |

Note: Utranslate properties are now handled via the `AdmitsUnitaryTranslation` typeclass.

## Key Files

- `required_lean_statements.md` - Tracks incomplete proofs
- `README.md` - Project overview
- `docs/archive/` - Historical documentation

## Proof Conventions

1. Use Mathlib lemmas where available
2. Prefer `exact` over `apply` when possible
3. Use `convert ... using n` for type mismatches
4. Check `Real.rpow_natCast` for power type conversions

## Common Issues

- `x ^ (n:ℕ)` vs `x ^ (n:ℝ)` - use `Real.rpow_natCast` to convert
- Gaussian integrability: use `integrable_exp_neg_mul_sq` and `integrable_rpow_mul_exp_neg_mul_sq`
- L² membership: use `memLp_two_iff_integrable_sq` for real functions
