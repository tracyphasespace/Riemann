/-
# ProofEngine.Axioms - Assumption Documentation for RH Proof

## Status (2026-02-13)
**0 axioms, 0 sorry** — all former axioms eliminated.

### Eliminated Axioms (Historical)
1. `rotorTrace_first1000_lt_bound_axiom` — Proved via LeanCert interval arithmetic
   (see RotorTraceComputation.lean)
2. `completedRiemannZeta₀_conj_axiom` — Proved via Schwarz reflection
   (see AristotleContributions.lean)
3. `ax_global_phase_clustering` — Deleted as dead code (result was unused in main theorem)
4. `energy_convex_at_half` — Deleted as dead code (hypothesis passed but unused)

### Remaining Hypotheses (not axioms — passed as theorem parameters)

**Clean analytic version** (`Clifford_RH_Analytic`, 3 hypotheses):
- `h_zero : riemannZeta s = 0`
- `h_strip : 0 < s.re ∧ s.re < 1`
- `h_min : AnalyticStrictMinAtHalf s.im` — |ξ(σ+it)|² minimized at σ=1/2

**Strict convexity version** (`Clifford_RH_StrictConvex`, 3 hypotheses):
- Same `h_zero`, `h_strip`
- `h_conv : EnergyStrictlyConvexOnStrip s.im` — |ξ(σ+it)|² strictly convex on (0,1)
  (derives minimum from convexity + proved symmetry E(σ)=E(1-σ))

**Clifford orthogonal bridge version** (`Clifford_RH_from_Bridge`, 3 hypotheses):
- Same `h_zero`, `h_strip`
- `h_bridge : CliffordOrthogonalBridge s.im` — Clifford strict convexity transfers
  to analytic energy (the orthogonal decoupling principle)
  The antecedent (Clifford energy IS strictly convex) is PROVED with no special
  hypotheses, establishing the bridge is non-vacuous. The implication itself
  (that Clifford convexity transfers to analytic convexity) is the sole
  non-machine-verified step.

**Original discrete version** (`Clifford_RH_Derived`, 11 hypotheses):
- `h_norm_min : NormStrictMinAtHalf s.im primes` (discrete rotor sum)
- `h_zero_norm : ZeroHasMinNorm s.re s.im primes` (discrete rotor sum)
- Plus 9 other hypotheses (all unused with underscore prefix)

### Proved With No Special Hypotheses (GeometricBridge.lean)

1. `orthogonal_generators_no_cross_terms` — Clifford energy = Σ p^{-2σ} (definitional)
2. `geometric_velocity_strictly_positive` — d²/dσ²[p^{-2σ}] = 4·log²(p)·p^{-2σ} > 0
3. `strictConvexOn_cliffordTerm` — Each p^{-2σ} is strictly convex on (0,1)
4. `clifford_global_strict_convexity` — Σ p^{-2σ} is strictly convex on (0,1)
5. `clifford_bridge_antecedent_holds` — The Clifford energy IS strictly convex (witness: [2])

All are explicit hypotheses, making the theorems honestly conditional.
-/
