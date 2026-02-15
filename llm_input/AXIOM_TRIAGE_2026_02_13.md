# Axiom Triage — 2026-02-13

**Pre-triage total**: 28 axioms (in compiled .lean files)
**Post-triage**: 25 axioms (2 deleted, 1 proved) — **3 live**, 22 dead (archived)
**Archived**: 44 dead .lean files moved to archive/ as .leantxt (2026-02-13)

---

## TIER 1: ELIMINATE NOW (4 axioms + 1 sorry)

### 1. `kernel_implies_zero_axiom` — DELETE
- **File**: `CliffordZetaMasterKey.lean:946`
- **Status**: Dead code
- **Reason**: Comment says "NOT needed for the RH proof (which only uses the forward direction)."
- **Action**: Delete axiom. Delete `zero_iff_kernel` ↔ theorem. Keep `zero_implies_kernel_axiom` (forward direction).

### 2. `scalarPart` — DEFINE
- **File**: `CliffordFoundation.lean:60`
- **Status**: Dead code
- **Reason**: `ClElement n` is now defined as `CliffordAlgebra (real_split_form n)` in `CliffordAxioms.lean`. The scalar part can be defined via `algebraMap` retraction: grade-0 component.
- **Action**: Define `scalarPart` using `CliffordAlgebra.ι` null-check or grade decomposition.

### 3. `prime_logs_linear_independent_axiom` — BRIDGE
- **File**: `Ergodicity.lean:51`
- **Status**: Dead code
- **Reason**: Core theorem ALREADY PROVED in `LinearIndependenceSolved.lean` as `LinearIndependent ℚ (fun (p : {x : ℕ // x.Prime}) => Real.log (p : ℕ))`. The axiom is a List-based interface needing a bridge.
- **Action**: Write bridge lemma converting subtype-based proof to List-based statement.

### 4. `sandbox/Test.lean` sorry — DELETE
- **File**: `sandbox/Test.lean:7`
- **Status**: Test file
- **Reason**: Contains `starRingEnd ℂ (riemannZeta s) = riemannZeta (starRingEnd ℂ s)` with sorry. Not needed; Mathlib lacks this lemma.
- **Action**: Delete the file (it's a sandbox test).

---

## TIER 2: KEEP AS AXIOMS — Live Build Path (4 axioms)

### `ax_global_phase_clustering` (PhaseClustering.lean:100) — KEEP
- **On path**: Riemann.lean → ProofEngine → PhaseClustering
- **Content**: Von Mangoldt Explicit Formula: ζ(s)=0 → negative phase clustering globally
- **Why keep**: Requires full explicit formula infrastructure (contour integration, residue calculus)

### `energy_convex_at_half` (Convexity.lean:207) — KEEP
- **On path**: Riemann.lean → ProofEngine → Convexity
- **Content**: |Λ(1/2+it)|² is convex for |t| ≥ 1
- **Why keep**: Requires second-derivative analysis of completed zeta

### `completedRiemannZeta₀_conj_axiom` (AristotleContributions.lean:114) — **ELIMINATED 2026-02-13**
- **On path**: Riemann.lean → ProofEngine → AristotleContributions
- **Content**: Schwarz reflection: Λ₀(conj s) = conj(Λ₀(s))
- **Proof**: Mellin conjugation for real-valued kernels (`GammaIntegral_conj` pattern).
  `hurwitzEvenFEPair 0` has `f = ofReal ∘ evenKernel 0` (real-valued), so `f_modif` is real,
  and `mellin f_modif (conj s) = conj(mellin f_modif s)` by `integral_conj` + `cpow_def_of_ne_zero`.

### `rotorTrace_first1000_lt_bound_axiom` (NumericalAxioms.lean:35) — KEEP
- **On path**: Riemann.lean → ProofEngine → TraceAtFirstZero → NumericalAxioms
- **Content**: Wolfram-verified bound: trace at first zero < -5
- **Why keep**: Requires native interval arithmetic (certified computation)

---

## TIER 3: KEEP AS AXIOMS — Dead Code, now ARCHIVED (22 axioms)

### Mathlib427Compat.lean (5 axioms) — ARCHIVED
These were initially classified as "live" but import-chain tracing shows they are
only used by other dead files (ErgodicSNR, ArithmeticAxioms, ExplicitFormula).

| Axiom | Notes |
|-------|-------|
| `vonMangoldt_geometric_sieve_diff_bounded` | Prime power summability |
| `zipWith_log_sum_eq_finset_sum` | List↔Finset bridge |
| `dirichlet_polynomial_ergodic_regularity` | Ergodic pointwise bounds |
| `signal_positive_for_prime_phases` | Phase positivity |
| `dirichlet_polynomial_noise_power_bound` | Noise power bound |

### BridgeObligations.lean (8 axioms) — ALL ARCHIVED
These represent the M1-M5 bridge obligations connecting abstract Hilbert space to ζ(s). They are the honest mathematical debt. Each has a documented discharge strategy.

| Axiom | Bridge | Notes |
|-------|--------|-------|
| `bivector_squares_to_neg_id` | M1 | B²=-Id as operator (CliffordAxioms proves B²=+1 as algebra element — different!) |
| `bivectors_commute` | M2a | Already proved in CliffordAxioms for CliffordAlgebra type |
| `cross_terms_vanish` | M2b | Requires connecting orthogonality to inner product |
| `scalar_bridge_matches_zeta` | M3 | Deep: Euler product = ζ(s) via Mathlib |
| `zeta_zero_implies_kernel` | M4 | Core spectral bridge |
| `rayleigh_forcing` | M5a | The forcing identity |
| `Q_pos` | M5b | Sum-of-squares positivity |
| `Omega_zero_right` | M5c | Trivial once Omega defined concretely |

### CliffordZetaMasterKey.lean (2 axioms after deletion) — ARCHIVED
| Axiom | Notes |
|-------|-------|
| `rayleigh_Phi_pos` | Positivity of Φ for charged states |
| `zero_implies_symmetric_kernel` | Core: ζ(s)=0 → symmetric kernel with nonzero charge |

### SpectralBridge.lean (1 axiom) — ARCHIVED
| Axiom | Notes |
|-------|-------|
| `zeta_zero_implies_eigenvalue_zero` | Refined M4 (purely arithmetic) |

### Other dead axioms (3) — ARCHIVED
| Axiom | File | Notes |
|-------|------|-------|
| `finite_sum_approx_analytic_axiom` | ExplicitFormulaAxioms | Explicit formula approximation |
| `rayleigh_decomposition_axiom` | AnalyticBridge | DFinsupp/Finset.sum interaction |
| `universal_monotonicity_from_orthogonality_axiom` | UniversalStiffness | Monotonicity from orthogonality |

---

## Summary

| Action | Count | Axioms |
|--------|-------|--------|
| **DELETED** | 2 | `kernel_implies_zero_axiom`, `scalarPart` |
| **BRIDGE** | 1 | `prime_logs_linear_independent_axiom` (core proved, List↔Finset gap) |
| **LIVE** | 4 | `ax_global_phase_clustering`, `energy_convex_at_half`, `completedRiemannZeta₀_conj_axiom`, `rotorTrace_first1000_lt_bound_axiom` |
| **ARCHIVED** | 22 | Bridge obligations + Mathlib427Compat shims + analysis |
| **Pre-triage total** | 28 | |

After triage: **4 live axioms** on the build path, 22 archived as .leantxt.
44 dead .lean files archived total (reducing live files from 72 to 28).

**Correction**: The 5 Mathlib427Compat axioms were initially classified as "live"
but import-chain tracing confirmed they are only used by other dead files
(ErgodicSNR, ArithmeticAxioms, ExplicitFormula — all archived).
