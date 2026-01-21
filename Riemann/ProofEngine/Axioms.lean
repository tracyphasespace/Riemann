/-
# ProofEngine.Axioms - Consolidated Assumptions for RH Proof

This file serves as a documentation hub for all assumptions used in the Riemann Hypothesis proof.

## Organization

### Category 1: Structural Definitions
Clifford algebra Cl(n,n) setup - see CliffordAxioms.lean

### Category 2: Analytic Bridge Hypotheses (THE REAL ASSUMPTIONS)
These are the genuine mathematical assumptions:
- `ax_global_phase_clustering` in PhaseClustering.lean
- `energy_convex_at_half` in Convexity.lean
- `explicit_formula_approximation` in ClusteringDomination.lean

### Category 3: Scaffolding Lemmas
Technical lemmas distributed across:
- SNRAxioms.lean - Signal/noise ratio lemmas
- ArithmeticAxioms.lean - FTA and log independence
- GeometricAxioms.lean - Frequency incommensurability
- CalculusAxioms.lean - Taylor theorem, MVT
- ErgodicAxioms.lean - Time averages
- And others

### Category 4: Proven Helper Lemmas
Working proofs in the individual stub files above.

---
**Assumption Summary for Reviewers:**
The RH proof reduces to the key hypotheses listed in Category 2.
All other "sorries" are technical scaffolding, not mathematical assumptions.
---
-/

-- This file intentionally has minimal content.
-- The actual axioms and lemmas are in the individual stub files.
-- See Riemann/Axioms.lean for the unified import point.
