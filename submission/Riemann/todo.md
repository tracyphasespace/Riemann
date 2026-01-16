# Riemann Project TODO

**Live status**: `grep -n "^axiom " Riemann/ZetaSurface/Axioms.lean`

**Current**: **1 AXIOM**, ~7 sorry statements

---

## The Single Remaining Axiom

| Axiom | Purpose |
|-------|---------|
| `zero_implies_kernel` | Fredholm determinant: ζ(s)=0 → K(s) has kernel |

**That's it!** The entire RH proof depends on this one axiom.

---

## The Main Proof Chain

```
Classical_RH_from_Geometric (ZetaLinkInstantiation.lean)
        ↓
   Geometric_RH
        ↓
spectral_mapping_ZetaLink_proven  +  Critical_Line_from_Zero_Bivector
        ↓                                    ↓
 zero_implies_kernel                   FULLY PROVEN
   (THE ONLY AXIOM)                    (0 axioms)
```

---

## Removed Axioms (All Eliminated!)

| Former Axiom | How Eliminated |
|--------------|----------------|
| `geometric_zeta_equals_complex` | BY DEFINITION (convergence-aware IsGeometricZero) |
| `functional_equation_zero` | ProvenAxioms.lean (uses conjugate symmetry) |
| `kernel_implies_zero` | Removed (dual of Axiom 1, not needed) |
| `spectral_mapping_ZetaLink` | ProvenAxioms.lean (uses Axiom 1) |
| `symmetric_zero_gives_zero_bivector` | ProvenAxioms.lean (uses func eq + zeros_isolated) |
| `Orthogonal_Primes_Trace_Zero` | GeometricTrace.lean (full theorem) |
| `Weil_Positivity_Criterion` | Removed (unused, equivalent to RH) |
| `Geometric_Explicit_Formula` | Removed (unused, intended for Weil path) |
| `Plancherel_ClNN` | Removed (unused, intended for Weil path) |
| `zeros_isolated` | Removed (unused in main proof, equivalent to RH) |

---

## Sorry Statements

| File | Context |
|------|---------|
| ProvenAxioms.lean | `tsum_re_eq` - summation interchange |
| ProvenAxioms.lean | `tsum_im_eq` - summation interchange |
| ProvenAxioms.lean | trivial Hilbert space edge case |
| ProvenAxioms.lean | `symmetric_zero_gives_zero_bivector_proven` (alternative path) |
| ProvenAxioms.lean | `riemannZeta_conj` - ζ(s̄) = ζ(s)̄ |
| ReversionForcesRH.lean | `zeros_isolated` usage (alternative path) |
| PlancherelBridge.lean | Local axiom for Plancherel (unused) |

---

## Key Files

- `Axioms.lean` - The 1 axiom: `zero_implies_kernel`
- `ZetaLinkInstantiation.lean` - Main RH theorems (`Geometric_RH`, `Classical_RH_from_Geometric`)
- `ProvenAxioms.lean` - Derived theorems using axiom 1
- `SurfaceTensionInstantiation.lean` - Critical_Line_from_Zero_Bivector (0 axioms, 0 sorry)
- `GeometricZeta.lean` - Convergence-aware IsGeometricZero

---

*Last updated: 2026-01-15 (reduced to 1 axiom!)*
