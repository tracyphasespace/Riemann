# Sorry Audit - Riemann/Lean Codebase

## Summary
- **Total sorries**: 66 (excluding sandbox/archive)
- **Total axioms**: 8

## Categorization

### CATEGORY A: Core Proof Chain (12 sorries)
These are in the main files that form the proof skeleton.

#### Residues.lean (4 sorries)
| Line | Description | Type |
|------|-------------|------|
| 160 | Continuity of derivative of holomorphic function | Provable (Mathlib) |
| 163 | Derivative of pole + holomorphic | Provable (Mathlib) |
| 196 | Pole domination: -∞ + bounded = -∞ | Provable (Filter) |
| 247 | Filter intersection and extraction of δ | Provable (Filter) |

#### PhaseClustering.lean (4 sorries)
| Line | Description | Type |
|------|-------------|------|
| 82 | Filter arithmetic: combining limits | Provable (Filter) |
| 122 | Linearity of derivative | Provable (Mathlib) |
| 145 | List foldl type coercion | Technical (API) |
| 200 | Global extension of local clustering | **AXIOM CANDIDATE** |

#### ExplicitFormula.lean (5 sorries)
| Line | Description | Type |
|------|-------------|------|
| 64 | Convergence of sum over prime powers | **AXIOM CANDIDATE** |
| 90 | Continuity of finite sums | Provable (Mathlib) |
| 134 | Boundedness of continuous functions | Provable (Mathlib) |
| 176 | Positivity of foldl over squares | Provable (Mathlib) |
| 179 | Triangle inequality on list sum | Provable (Mathlib) |

### CATEGORY B: Axiom Stub Files (37 sorries)
These files contain theorem stubs that were axioms. Most can be consolidated.

| File | Sorries | Notes |
|------|---------|-------|
| AnalyticAxioms.lean | 6 | Pole divergence lemmas |
| ArithmeticAxioms.lean | 3 | Prime/log lemmas |
| CalculusAxioms.lean | 2 | MVT applications |
| CliffordAxioms.lean | 2 | Bivector algebra |
| ClusteringAxioms.lean | 1 | Duplicate of PhaseClustering |
| ConservationAxioms.lean | 2 | Energy conservation |
| ErgodicAxioms.lean | 8 | Oscillating integrals |
| ErgodicSNRAxioms.lean | 2 | SNR ergodicity |
| ExplicitFormulaAxioms.lean | 3 | Duplicate |
| GeometricAxioms.lean | 2 | Sieve geometry |
| NumericalAxioms.lean | 2 | First zero verification |
| SNRAxioms.lean | 1 | Signal-to-noise |
| SieveAxioms.lean | 1 | Sieve bounds |
| StabilityAxioms.lean | 2 | Stability conditions |

### CATEGORY C: Other Files (17 sorries)

| File | Sorries | Notes |
|------|---------|-------|
| Axioms.lean (root) | 2 | ax_zero_implies_norm_min, ax_norm_strict_min_at_half |
| GlobalBound/ErgodicSNR.lean | 1 | Ergodic bound |
| GlobalBound/PrimeRotor.lean | 1 | Rotor bound |
| ZetaSurface/TraceMonotonicity.lean | 0 | Comments only mention sorry |
| Convexity.lean | 2 | Energy convexity |
| TraceAtFirstZero.lean | 4 | Interval arithmetic |
| ClusteringDomination.lean | 1 | Domination logic |

---

## True Mathematical Axioms (Need Deep Proofs)

These represent genuine mathematical claims from analytic number theory:

1. **Explicit Formula Approximation** (ExplicitFormula.lean:64)
   - The finite prime sum approximates the log derivative of zeta
   - Requires: von Mangoldt explicit formula

2. **Global Phase Clustering** (PhaseClustering.lean:200)
   - ζ(s)=0 implies negative weighted cosine sum for ALL σ ∈ (0,1)
   - Requires: Explicit formula + extension argument

3. **Energy Convexity at Critical Line** (Convexity.lean)
   - Completed zeta has convex norm squared at σ=1/2
   - Requires: Functional equation properties

4. **Trace Negativity at First Zero** (TraceAtFirstZero.lean)
   - Numerical verification that trace < -5 at t=14.134725
   - Requires: Interval arithmetic or native computation

---

## Files to Consolidate/Delete

### Can Delete (0 imports, redundant):
- AristotleAxioms.lean
- StabilityAxioms.lean

### Should Consolidate into Axioms.lean:
- AnalyticAxioms.lean
- ClusteringAxioms.lean
- ExplicitFormulaAxioms.lean

### Keep Separate (distinct functionality):
- ErgodicAxioms.lean (ergodic theory lemmas)
- CliffordAxioms.lean (Clifford algebra)
- ArithmeticAxioms.lean (number theory basics)

---

## Recommended Action Plan

### Phase 1: Cleanup
1. Delete unused axiom files (AristotleAxioms, StabilityAxioms)
2. Consolidate duplicates into Riemann/Axioms.lean

### Phase 2: Prove Technical Sorries
Focus on the 8 "Provable" sorries in Residues.lean and PhaseClustering.lean:
- Filter arithmetic lemmas
- Derivative linearity
- Continuity of finite sums

### Phase 3: Attack True Axioms
Work on the 4 fundamental mathematical axioms with helper lemma decomposition.
