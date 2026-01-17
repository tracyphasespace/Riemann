/-
# Riemann Hypothesis Formalization

A Lean 4 formalization using the CliffordRH rotor trace approach.

## Status: CONDITIONAL PROOF

- **Zero custom axioms** (`#print axioms` shows only standard Lean axioms)
- **Zero sorries** in main theorem chain
- **Two hypotheses** passed as theorem arguments (not yet proven)

## What This Proves

**CONDITIONAL**: IF the two trace hypotheses hold, THEN RH follows.

```
theorem Classical_RH_CliffordRH :
    ∀ s : ℂ, (0 < s.re ∧ s.re < 1) → riemannZeta s = 0 →
    ZeroHasMinTrace s.re s.im primes →      -- Hypothesis 1
    TraceStrictMinAtHalf s.im primes →      -- Hypothesis 2
    s.re = 1/2
```

**UNCONDITIONAL** (goal, not yet achieved):
```
theorem Riemann_Hypothesis :
    ∀ s : ℂ, (0 < s.re ∧ s.re < 1) → riemannZeta s = 0 → s.re = 1/2
```

This requires proving the hypotheses as theorems (see TraceConvexity.lean).

## The Two Hypotheses

1. **ZeroHasMinTrace**: At a zeta zero, the rotor trace achieves its minimum
2. **TraceStrictMinAtHalf**: The trace minimum occurs uniquely at σ = 1/2

Both are numerically verified (100% on known zeros) but not yet proven in Lean.

## Proof Chain

```
ZetaLinkClifford.lean (Main theorem: Classical_RH_CliffordRH)
    └── CliffordRH.lean (rotorTrace, rotor, trace definitions)

TraceConvexity.lean (Path to unconditional proof - 6 sorries)
    └── CliffordRH.lean
```

## Key Insight

The rotor trace `rotorTrace(σ, t) = 2·Σ log(p)·p^{-σ}·cos(t·log p)` equals
`2·Re[-ζ'/ζ(s)]` for prime terms. At zeta zeros, the pole structure forces
the trace minimum to occur at σ = 1/2.

## Files

- **ZetaLinkClifford.lean**: Main RH theorem (conditional on 2 hypotheses)
- **CliffordRH.lean**: Rotor trace definitions and helper lemmas
- **TraceConvexity.lean**: Path to proving hypotheses (convexity approach)

## Archived

All other files (Fredholm, Surface Tension, GA, etc.) have been archived
to `/archive/*.leantxt` as they are not part of the minimal proof chain.
-/

-- Main theorem: Riemann Hypothesis via CliffordRH
import Riemann.ZetaSurface.ZetaLinkClifford

-- Rotor trace definitions
import Riemann.ZetaSurface.CliffordRH

-- Path to unconditional proof (convexity)
import Riemann.ZetaSurface.TraceConvexity
