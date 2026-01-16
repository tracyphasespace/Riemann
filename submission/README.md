# Riemann Hypothesis Formalization in Lean 4

**A Geometric/Spectral Approach via Clifford Algebras**

Copyright 2026 Tracy McSheery PhaseSpace

## Quick Verification

```bash
# Clone and verify (requires ~10 minutes, ~8GB disk)
git clone <repo-url>
cd Riemann/Lean
lake exe cache get   # Downloads prebuilt Mathlib (~2 min)
lake build           # Builds project (~5 min)
```

**Success = 0 errors.** All proofs typecheck.

## Requirements

| Component | Version |
|-----------|---------|
| Lean | 4.27.0-rc1 |
| Mathlib | v4.27.0-rc1 |
| OS | Linux/macOS/Windows (WSL) |
| Disk | ~8GB (Mathlib cache) |

## What This Formalizes

The Riemann Hypothesis is reduced to a single axiom encoding Fredholm determinant theory:

```
ζ(s) = 0  ⟹  ∃ v ≠ 0, K(s)v = v
```

where K(s) is a geometric operator in the Clifford algebra Cl(N,N).

## Proof Structure

```
                    RH_of_ZetaLink_SurfaceTension
                              ↓
        ┌─────────────────────┴─────────────────────┐
        ↓                                           ↓
ZetaLinkHypothesisFixB                 SurfaceTensionHypothesis
        ↓                                           ↓
zero_implies_kernel                    Critical_Line_from_Zero_Bivector
   (THE AXIOM)                              (FULLY PROVEN)
```

## Verification Summary

| Category | Count | Notes |
|----------|-------|-------|
| **Axioms** | 1 | `zero_implies_kernel` - Fredholm determinant |
| **Sorries** | 9 | See `docs/SORRY_AUDIT.md` |
| **Key Theorems** | 4 | All proven, see `docs/THEOREM_MAP.md` |

## File Organization

```
Riemann/
├── ZetaSurface/
│   ├── Axioms.lean              # The single axiom
│   ├── SpectralReal.lean        # The "Hammer" theorem (0 sorry)
│   ├── SurfaceTensionInstantiation.lean  # Critical line proof (0 sorry)
│   ├── DiagonalSpectral.lean    # Diagonal structure analysis
│   └── ...
├── GA/
│   ├── Cl33.lean                # Clifford algebra Cl(3,3)
│   └── PrimeClifford.lean       # Prime-indexed Cl(N,N)
└── docs/
    ├── THEOREM_MAP.md           # Paper ↔ Lean correspondence
    ├── AXIOM_AUDIT.md           # Justification for axiom
    └── SORRY_AUDIT.md           # Classification of sorries
```

## Auditing Commands

```bash
# Count sorries (excluding archive)
grep -rn "^\s*sorry" --include="*.lean" Riemann/ | grep -v Archive | wc -l

# Find all axioms
grep -rn "^axiom " --include="*.lean" Riemann/ | grep -v Archive

# Verify build
lake build 2>&1 | tail -5
```

## Documentation

- `docs/THEOREM_MAP.md` - Maps paper theorems to Lean definitions
- `docs/AXIOM_AUDIT.md` - Mathematical justification for the axiom
- `docs/SORRY_AUDIT.md` - Classification of all sorry statements

## License

MIT License - Copyright (c) 2026 Tracy McSheery PhaseSpace

See `LICENSE` for full terms.
