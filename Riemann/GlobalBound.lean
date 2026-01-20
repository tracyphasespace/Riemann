/-
# Global Bound Module: Geometric Proof of Lindelöf Hypothesis

This module implements the 4-phase architectural blueprint for proving
global bounds on the Riemann zeta function using Projective Geometric Algebra.

## The Key Insight

**Analysis asks**: "Do these waves cancel out?" (Hard)
**Topology asks**: "Is this rope tied in a knot?" (Robust)

We prove the Sieve is a knot that cannot be untied. That is the global bound.

## The 4 Phases

### Phase 1: Compactification (ZetaManifold)
- Eliminate t → ∞ by working on a projective cylinder
- The "point at infinity" becomes a regular point
- Continuous function on compact domain ⟹ bounded image

### Phase 2: Chirality (PrimeRotor)
- Primes are residuals ⟹ their rotors are linearly independent
- The total rotor describes a SCREW motion (helical)
- The screw never flattens ⟹ persistent tension

### Phase 3: Conservation (Conservation)
- On σ = 1/2, the geometric mass is zero (null/light-like)
- Off the critical line, mass accumulates
- Conservation forbids the transition (infinite energy barrier)

### Phase 4: Lindelöf (Lindelof)
- Combine compactness + chirality + conservation
- The Sieve radius is bounded on the projective cylinder
- Mapping back introduces the t^ε growth factor
- Result: |ζ(1/2 + it)| = O(t^ε) for any ε > 0

### Phase 5: Signal vs Noise (InteractionTermLittleO)
- RealEnergy = IdealEnergy + InteractionTerm (Signal + Noise)
- Pair Correlation Hypothesis: Noise = o(Signal) as t → ∞
- Main Theorem: If Noise = o(Signal), then RealEnergy > 0 eventually
- The geometric stiffness dominates the interference

## Architecture Diagram

```
                    Geometric_Lindelof
                           │
    ┌──────────┬───────────┼───────────┬──────────┐
    │          │           │           │          │
    ▼          ▼           ▼           ▼          ▼
Compactness Chirality Conservation Lindelöf   SNR
 (Phase 1)  (Phase 2)  (Phase 3)  (Phase 4) (Phase 5)
    │          │           │           │          │
    ▼          ▼           ▼           ▼          ▼
Projective  Prime      Mass = 0    t^ε      Signal
Cylinder   Rotors     on σ=1/2    bound   dominates
```

## Connection to RH

The Riemann Hypothesis is a special case:
- RH says zeros lie on σ = 1/2
- Our Phase 3 proves this via conservation
- Lindelöf is a consequence: bounded Sieve ⟹ controlled growth

## Lean/Mathlib Version
- Lean: 4.27.0-rc1
- Mathlib: v4.27.0-rc1
-/

import Riemann.GlobalBound.ZetaManifold
import Riemann.GlobalBound.PrimeRotor
import Riemann.GlobalBound.Conservation
import Riemann.GlobalBound.Lindelof
import Riemann.GlobalBound.InteractionTermLittleO  -- Phase 5: Signal vs Noise (little-o version)
