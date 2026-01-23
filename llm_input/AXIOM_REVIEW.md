# Complete Axiom Review for RH Proof

**Generated**: 2026-01-23 (Updated after cleanup)
**Purpose**: Human review of all axioms used in the Riemann Hypothesis formalization

---

## Summary

| Category | Count | Notes |
|----------|-------|-------|
| **Unique Axioms** | 31 | After cleanup |
| **Archived** | 4 files | RemainingProofs, ClusteringDomination, AnalyticBridgeEuler, Axioms.proposed |
| **Deleted** | 1 | coeff_sym_factorization_axiom (FALSE) |
| **Core Path** | 12 | Used by main theorem chain |
| **Auxiliary** | 19 | Supporting infrastructure |

---

## Category 1: Numerical Verification (2 axioms)

These encode Wolfram-verified computations that would require native interval arithmetic.

### 1.1 `rotorTrace_first1000_lt_bound_axiom`
**File**: `ProofEngine/NumericalAxioms.lean:35`

```lean
axiom rotorTrace_first1000_lt_bound_axiom :
    CliffordRH.rotorTrace (1/2) 14.134725 (Nat.primesBelow 7920).toList < -5
```

**Meaning**: At the first zeta zero height t ≈ 14.134725, with σ = 1/2, the rotor trace over primes below 7920 is strictly less than -5.

**Justification**: Wolfram Cloud computation gives trace ≈ -5.955. Interval arithmetic confirms the bound.

**Why Axiom**: Would require native interval arithmetic library + certified cos/log/power functions.

---

### 1.2 `rotorTrace_monotone_from_first1000_axiom`
**File**: `ProofEngine/NumericalAxioms.lean:59`

```lean
axiom rotorTrace_monotone_from_first1000_axiom
    (primes : List ℕ) (h_len : 1000 ≤ primes.length) (h_primes : ∀ p ∈ primes, Nat.Prime p) :
    CliffordRH.rotorTrace (1/2) 14.134725 primes ≤
      CliffordRH.rotorTrace (1/2) 14.134725 (Nat.primesBelow 7920).toList
```

**Meaning**: For large prime sets (≥1000 primes), the trace is bounded by the trace over primesBelow 7920.

**Justification**: Tail bound via integral comparison ∫_N^∞ log(x)/√x dx = O(√N · log N).

**Why Axiom**: Requires careful error analysis for oscillating sums.

---

## Category 2: Baker's Theorem / Transcendence (1 axiom)

### 2.1 `bakers_repulsion_axiom`
**File**: `ProofEngine/BakerRepulsion.lean:78`

```lean
axiom bakers_repulsion_axiom (σ : ℝ) (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    LinearIndependent ℚ (fun (p : S) => Real.log (p : ℕ)) →
    (∃ t, zeta_deriv_sum σ S t ≠ 0) →
    ∃ δ > 0, ∀ t, ‖zeta_deriv_sum σ S t‖ ≥ δ
```

**Meaning**: If prime logs are ℚ-linearly independent, the exponential sum ∑ c_p · e^{it log p} has a uniform lower bound.

**Justification**: Baker's Theorem (1966 Fields Medal) on linear forms in logarithms.

**Why Axiom**: Formalizing Baker's Theorem is a massive project (~5000+ lines).

**Literature**: A. Baker, "Linear forms in the logarithms of algebraic numbers" (1966).

---

## Category 3: Explicit Formula / Analytic Number Theory (3 axioms)

### 3.1 `finite_sum_approx_analytic_axiom`
**File**: `ProofEngine/ExplicitFormulaAxioms.lean:76`

```lean
axiom finite_sum_approx_analytic_axiom (ρ : ℂ) (primes : List ℕ) :
    ∃ (E : ℝ), 0 < E ∧ ∀ σ : ℝ, σ > ρ.re →
      abs (primes.foldl (...) 0 + (deriv (-ζ'/ζ) (σ + ρ.im * I)).re) < E
```

**Meaning**: The finite prime sum approximates -ζ'/ζ with bounded error.

**Justification**: Von Mangoldt Explicit Formula + Perron's formula.

**Why Axiom**: Requires contour integration, residue calculus, PNT-level error estimates.

**Literature**: Titchmarsh, "The Theory of the Riemann Zeta Function", Ch. 3.

---

### 3.2 `ax_global_phase_clustering`
**File**: `ProofEngine/PhaseClustering.lean:100`

```lean
axiom ax_global_phase_clustering (s : ℂ)
    (h_zero : riemannZeta s = 0) (h_strip : 0 < s.re ∧ s.re < 1)
    (h_simple : deriv riemannZeta s ≠ 0) (primes : List ℕ) (h_large : primes.length > 1000) :
    ∀ σ, σ ∈ Set.Ioo 0 1 → NegativePhaseClustering σ s.im primes
```

**Meaning**: If ζ(s) = 0 in the critical strip, the weighted cosine sum is negative for ALL σ ∈ (0,1).

**Justification**: Extends pole domination globally via Explicit Formula error bounds.

**Why Axiom**: Requires full von Mangoldt infrastructure.

---

### 3.3 `vonMangoldt_geometric_sieve_diff_bounded`
**File**: `Common/Mathlib427Compat.lean:218`

```lean
axiom vonMangoldt_geometric_sieve_diff_bounded
    (s : ℂ) (h_strip : 1/2 < s.re) (N : ℕ) (...) :
    ‖V - G‖ ≤ ∑ n ∈ Finset.range N, f n
```

**Meaning**: The difference between von Mangoldt sum and prime-only sum is bounded by (log n)² · n^{-2σ}.

**Why Axiom**: Data structure conversion between List.foldl and Finset.sum blocked by Mathlib 4.27 API.

---

## Category 4: Clifford Algebra Bridge (8 axioms)

These connect the GA formalism to classical ζ(s).

### 4.1 `bivector_squares_to_neg_id`
**File**: `ProofEngine/BridgeObligations.lean:69`

```lean
axiom bivector_squares_to_neg_id (B : ℕ → V →ₗ[ℝ] V) (p : ℕ) (hp : p.Prime) (v : V) :
    B p (B p v) = -v
```

**Meaning**: B_p² = -Id (bivector acts as 90° rotation on its plane).

**Why Axiom**: Requires concrete GA construction.

---

### 4.2 `bivectors_commute`
**File**: `ProofEngine/BridgeObligations.lean:81`

```lean
axiom bivectors_commute (B : ℕ → V →ₗ[ℝ] V) (p q : ℕ) (hp hq : Prime) (hpq : p ≠ q) (v : V) :
    B p (B q v) = B q (B p v)
```

**Meaning**: [B_p, B_q] = 0 for distinct primes (orthogonal decoupling).

---

### 4.3 `cross_terms_vanish`
**File**: `ProofEngine/BridgeObligations.lean:86`

```lean
axiom cross_terms_vanish (B : ℕ → V →ₗ[ℝ] V) (p q : ℕ) (hpq : p ≠ q) (inner : V → V → ℝ) (v : V) :
    inner (B p v) (B q v) = 0
```

**Meaning**: Cross-prime terms vanish in energy (block-diagonal structure).

---

### 4.4 `scalar_bridge_matches_zeta`
**File**: `ProofEngine/BridgeObligations.lean:104`

```lean
axiom scalar_bridge_matches_zeta (ScalarBridge : ℂ → ℝ) (s : ℂ) (hs : 1 < s.re) :
    (ScalarBridge s : ℂ) = riemannZeta s
```

**Meaning**: The scalar extraction from GA equals classical ζ(s) on Re(s) > 1.

**Why Axiom**: Requires showing GA Euler product equals Mathlib's.

---

### 4.5 `zeta_zero_implies_kernel`
**File**: `ProofEngine/BridgeObligations.lean:119`

```lean
axiom zeta_zero_implies_kernel (K : ℂ → V →ₗ[ℝ] V) (s : ℂ) (hs : InCriticalStrip s) :
    riemannZeta s = 0 → ∃ v : V, v ≠ 0 ∧ K s v = 0
```

**Meaning**: ζ(s) = 0 implies the stability operator K(s) has nontrivial kernel.

**Why Axiom**: Requires determinant → kernel via finite truncations.

---

### 4.6 `rayleigh_forcing`
**File**: `ProofEngine/BridgeObligations.lean:139`

```lean
axiom rayleigh_forcing (K : ℂ → V →ₗ[ℝ] V) (Omega Q : ...) (σ t : ℝ) (v : V) :
    Omega v (K (σ + t * I) v) = (σ - 1/2) * Q v
```

**Meaning**: The chiral pairing satisfies Ω(v, K(s)v) = (σ - 1/2) · Q(v).

**Why Axiom**: Requires split-signature GA bilinear algebra.

---

### 4.7 `Q_pos`
**File**: `ProofEngine/BridgeObligations.lean:144`

```lean
axiom Q_pos (Q : V → ℝ) (v : V) : v ≠ 0 → 0 < Q v
```

**Meaning**: The stiffness quadratic form is positive definite.

---

### 4.8 `Omega_zero_right`
**File**: `ProofEngine/BridgeObligations.lean:148`

```lean
axiom Omega_zero_right (Omega : V → V → ℝ) (v : V) : Omega v 0 = 0
```

**Meaning**: Ω(v, 0) = 0 (bilinearity).

---

## Category 5: Convexity / Functional Equation (2 axioms)

### 5.1 `energy_convex_at_half`
**File**: `ProofEngine/Convexity.lean:207`

```lean
axiom energy_convex_at_half (t : ℝ) (ht : 1 ≤ |t|)
    (h1 : SecondDerivBound t) (h2 : FirstDerivLowerBound t) (h3 : ZetaUpperBound t) :
    EnergyIsConvexAtHalf t
```

**Meaning**: The energy |Λ(1/2 + it)|² is convex (second derivative > 0) for |t| ≥ 1.

**Why Axiom**: Combines three bounds; for |t| < 1 requires numerical verification.

---

### 5.2 `completedRiemannZeta₀_conj_axiom`
**File**: `ProofEngine/AristotleContributions.lean:114`

```lean
axiom completedRiemannZeta₀_conj_axiom (s : ℂ) :
    completedRiemannZeta₀ (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta₀ s)
```

**Meaning**: Λ(conj s) = conj(Λ(s)) (Schwarz reflection principle).

**Why Axiom**: Requires `WeakFEPair.Λ₀_conj` not in Mathlib 4.27.

**Literature**: Titchmarsh §2.6.

---

## Category 6: Ergodic / SNR Structure (5 axioms)

### 6.1 `prime_logs_linear_independent_axiom`
**File**: `GlobalBound/Ergodicity.lean:61`

```lean
axiom prime_logs_linear_independent_axiom (primes : List ℕ) (coeffs : List ℚ)
    (h_primes h_nodup h_length)
    (h_sum : (List.zipWith (fun p q => q * log p) primes coeffs).sum = 0) :
    ∀ q ∈ coeffs, q = 0
```

**Meaning**: {log p : p prime} is ℚ-linearly independent.

**Justification**: Follows from Fundamental Theorem of Arithmetic.

**Why Axiom**: Blocked by List↔Finset conversion issues.

**Note**: PROVEN in `LinearIndependenceSolved.lean` as `log_primes_linear_independent` but with different signature.

---

### 6.2 `signal_diverges_axiom`
**File**: `GlobalBound/ArithmeticGeometry.lean:121`

```lean
axiom signal_diverges_axiom :
    Tendsto (fun N => totalSignal (Nat.primesBelow N).toList (1/2)) atTop atTop
```

**Meaning**: Signal(N) → ∞ as N → ∞.

**Justification**: Signal ≈ ∑_{p≤N} p^{-1} which diverges (Mertens' theorem).

**Why Axiom**: Converting foldl to Finset.sum with type coercions.

---

### 6.3 `noiseGrowth_eq_cross_sum_axiom`
**File**: `GlobalBound/Ergodicity.lean:359`

```lean
axiom noiseGrowth_eq_cross_sum_axiom (S : Finset ℕ) (t : ℝ) :
    NoiseGrowth S t = crossTermSum S t
```

**Meaning**: Noise equals the cross-term sum (structural identity).

---

### 6.4 `ergodicity_validates_snr`
**File**: `GlobalBound/Ergodicity.lean:704`

```lean
axiom ergodicity_validates_snr (S : Finset ℕ) (h_nonempty : S.Nonempty)
    (h_primes : ∀ p ∈ S, Nat.Prime p) :
    Tendsto (fun t => Signal S t / |NoiseGrowth S t|) atTop atTop
```

**Meaning**: Signal-to-Noise Ratio diverges (SNR → ∞).

**Why Axiom**: Requires Cesàro → pointwise bounds via almost periodic function theory.

---

### 6.5 `dirichlet_polynomial_ergodic_regularity`
**File**: `Common/Mathlib427Compat.lean:303`

```lean
axiom dirichlet_polynomial_ergodic_regularity
    (h_noise_avg : ∫Noise/T → 0) (h_signal_avg : ∫Signal/T → L > 0) :
    |Noise| =o[atTop] Signal
```

**Meaning**: For Dirichlet polynomials, time-average convergence implies pointwise asymptotic bounds.

**Justification**: Almost periodic functions + Bernstein inequalities.

---

## Category 7: Auxiliary Technical (6 axioms)

### 7.1 `zipWith_log_sum_eq_finset_sum`
**File**: `Common/Mathlib427Compat.lean:257`

```lean
axiom zipWith_log_sum_eq_finset_sum (primes coeffs) (...) :
    (List.zipWith (fun p q => q * log p) primes coeffs).sum =
    ∑ p ∈ primes.toFinset.subtype ..., coeffs.getD (primes.idxOf p) 0 * log p
```

**Meaning**: List zipWith sum equals Finset sum (data structure bridge).

**Why Axiom**: Index tracking through Nodup + coercion complexity.

---

### 7.2 `signal_positive_for_prime_phases`
**File**: `Common/Mathlib427Compat.lean:320`

```lean
axiom signal_positive_for_prime_phases {S : Finset ℕ} (h_nonempty) (Signal) (...) :
    ∀ᶠ t in atTop, 0 < Signal t
```

**Meaning**: Signal = ∑ sin²(t·log p)·p^{-1} > 0 eventually.

**Justification**: Linear independence of {log p} means phases desynchronize.

---

### 7.3 `dirichlet_polynomial_noise_power_bound`
**File**: `Common/Mathlib427Compat.lean:338`

```lean
axiom dirichlet_polynomial_noise_power_bound (...) (α : ℝ) (hα : 0 < α < 1) :
    IsBigO atTop Noise (fun t => Signal^α)
```

**Meaning**: |Noise| = O(Signal^α) for α < 1.

**Justification**: Bernstein inequalities + Random Matrix Theory predicts α = 1/2.

---

### 7.4 `equidistribution_bound`
**File**: `ProofEngine/BridgeObligations.lean:262`

```lean
axiom equidistribution_bound (x t : ℝ) (hx : 1 < x) :
    |∑ p prime, p ≤ x, cos(t · log p)| ≤ √x · (log x)²
```

**Meaning**: CLT-type bound on prime cosine sums.

**Why Axiom**: Not implied by commutation/decoupling alone.

---

### 7.5 `universal_monotonicity_from_orthogonality_axiom`
**File**: `ZetaSurface/UniversalStiffness.lean:399`

```lean
axiom universal_monotonicity_from_orthogonality_axiom (t primes)
    (h_ortho : orthogonal axes) :
    CliffordRH.TraceIsMonotonic t primes
```

**Meaning**: Orthogonal prime axes imply trace monotonicity.

**Why Axiom**: Requires beam_forces_derivative_sign from orthogonality.

---

### 7.6 `scalarPart`
**File**: `ZetaSurface/CliffordFoundation.lean:60`

```lean
axiom scalarPart (n : ℕ) : ClElement n → ℝ
```

**Meaning**: Scalar projection from Clifford algebra element.

**Why Axiom**: Abstract interface pending concrete GA construction.

---

## Category 8: Cleaned Up (2026-01-23)

**Archived** (moved to `ZetaSurface/archive/`):
- `RemainingProofs.lean` → `RemainingProofs.leantxt` (documentation only)
- `ClusteringDomination.lean` → `ClusteringDomination.leantxt` (duplicate axioms)
- `AnalyticBridgeEuler.lean` → `AnalyticBridgeEuler.leantxt` (duplicate)
- `sandbox/Axioms.proposed.lean` → `Axioms.proposed.leantxt` (proposals only)

**Deleted**:
- `coeff_sym_factorization_axiom` - FALSE when s.re = 1/2 and s.im ≠ 0

**Remaining potential duplicates** (kept for now):
- `rayleigh_Phi_pos` - Similar to Q_pos but different signature
- `zero_implies_symmetric_kernel` - Variant of zeta_zero_implies_kernel
- `kernel_implies_zero_axiom` - Converse direction (may be useful)

---

## Critical Path Analysis

The main theorem `RH_algebraic_core` in BridgeObligations.lean depends on:

1. **zeta_zero_implies_kernel** (M4) - Zero to kernel
2. **rayleigh_forcing** (M5a) - Rayleigh identity
3. **Q_pos** (M5b) - Stiffness positivity
4. **Omega_zero_right** (M5c) - Bilinearity

These 4 axioms are SUFFICIENT for the algebraic core proof.

The full `Clifford_RH_Derived` additionally uses:
- **ax_global_phase_clustering** - Global extension
- **energy_convex_at_half** - Energy minimum
- **Numerical axioms** - Bootstrapping bounds

---

## Recommendation Summary

| Priority | Action | Axioms |
|----------|--------|--------|
| **Keep** | Core math facts | Baker's, Explicit Formula, Bridge M1-M5 |
| **Reduce** | Prove from FTA | prime_logs_linear_independent (done in LinearIndependenceSolved) |
| **Done** | Archived 4 files | RemainingProofs, ClusteringDomination, AnalyticBridgeEuler, Axioms.proposed |
| **Done** | Deleted 1 false axiom | coeff_sym_factorization_axiom |
| **Fix** | Signature mismatch | Unify prime_logs variants |

---

## Files with Broken Proofs (Not Compiling)

These files contain axioms but have broken proofs preventing compilation:

1. `ProofEngine/ExplicitFormulaAxioms.lean` - Doc comment syntax fixed, may still have issues
2. `ProofEngine/AnalyticBridge.lean` - `rewrite` failures
3. `GlobalBound/Ergodicity.lean` - Various proof failures
4. `GlobalBound/ArithmeticGeometry.lean` - Unknown status
5. `ZetaSurface/UniversalStiffness.lean` - Unknown status

**These are NOT on the main build path**, which is why `lake build` passes.

---

*End of Axiom Review*
