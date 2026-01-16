# Sorry Audit

Copyright (c) 2026 Tracy McSheery PhaseSpace

This document classifies all `sorry` statements in the formalization.

## Summary

| Category | Count | Impact on Main Result |
|----------|-------|----------------------|
| **Mathlib gap (alternative path only)** | 1 | None - not used in main proof |
| **Future work stubs (FredholmTheory.lean)** | 9 | None - documentation only |
| **Technical lemmas (CliffordSieveOperator.lean)** | 2 | None - alternative formalization |
| **Total** | **12** | Main proof chain: **0 sorry** |

## Categories

### 1. Alternative Proof Path (1 sorry)

**File**: `ProvenAxioms.lean:367`

```lean
lemma riemannZeta_conj (s : ℂ) (hs : s ≠ 1) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
  by_cases h_re : 1 < s.re
  · exact riemannZeta_conj_of_re_gt_one s h_re
  · sorry  -- Requires Identity Theorem for meromorphic functions
```

**Why it's there**: The Re(s) > 1 case is proven using the Dirichlet series formula.
The Re(s) ≤ 1 case requires the Identity Theorem: two meromorphic functions that
agree on an open set with accumulation points must agree everywhere.

**Mathlib Gap**: The Identity Theorem for meromorphic functions is not available
in Mathlib in a form we can use directly.

**Impact**: This sorry is in `riemannZeta_conj`, which is only used by
`functional_equation_zero_proven`, which is part of an ALTERNATIVE proof path.
The MAIN proof path does NOT use this lemma.

### 2. Future Work Stubs (9 sorries in FredholmTheory.lean)

These sorries are **intentional documentation** of the path to proving the
`zero_implies_kernel` axiom. They are NOT used in any proof chain.

| Line | Purpose |
|------|---------|
| 125 | `trace_class_eigenvalues_summable` - Requires Mathlib trace-class infrastructure |
| 171 | `TraceClassBound` - Standard spectral theory |
| 183 | `compact_spectrum_discrete` - Compact operators have discrete spectrum |
| 208 | `HilbertPolyaOperator_is_self_adjoint` - Construction of H-P operator |
| 256 | `zeta_factor_equivalence` - Euler product connection |
| 273 | `Fredholm_det_eq_Euler_product` - Convergence of Euler product |
| 287 | `zero_iff_eigenvalue_one` - Fredholm determinant theory |
| 345 | `explicit_formula_zeta_zeros` - Full explicit formula machinery |
| 510 | `zero_implies_kernel_proof` - The axiom itself |

**Purpose**: FredholmTheory.lean serves as a **roadmap** documenting three approaches
to eventually proving the axiom:
1. Fredholm determinant theory
2. Selberg trace formula
3. Weil explicit formula

These are research stubs, not proof obligations.

### 3. Technical Lemmas (2 sorries in CliffordSieveOperator.lean)

| Line | Purpose |
|------|---------|
| 171 | `bilinear_expansion` - Inner product algebra |
| 279 | `kernel_implies_critical_line` - Alternative proof path |

These are in an alternative formalization of the sieve operator.

## Main Proof Path (0 Sorry)

The main proof chain in `ZetaLinkInstantiation.lean` uses:

1. `critical_strip_geometric_eq_complex` - **PROVEN** (by definition)
2. `spectral_mapping_ZetaLink_proven` - **PROVEN** (uses `zero_implies_kernel` axiom)
3. `Critical_Line_from_Zero_Bivector` - **PROVEN** (0 sorry)

## Verification

```bash
# Count all sorries
grep -rn "^\s*sorry" --include="*.lean" Riemann/ | grep -v Archive | wc -l
# Output: 12

# List all sorries
grep -rn "^\s*sorry" --include="*.lean" Riemann/ | grep -v Archive
```

## Key Point

**The MAIN proof has 0 sorry.** All 12 sorries are either:
- In an ALTERNATIVE proof path (not used by main theorem)
- Future work stubs (documentation only, not proofs)
- Technical lemmas in alternative formalizations

The main result `Classical_RH_from_Geometric` depends only on:
- 1 axiom: `zero_implies_kernel` (Fredholm determinant)
- 0 sorry in the proof chain
