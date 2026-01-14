# Riemann Hypothesis Lean 4 Formalization

A formal verification of the geometric/spectral approach to the Riemann Hypothesis.

## Build Status

**Status**: Building
**Lean**: 4.27.0-rc1
**Mathlib**: v4.27.0-rc1

### Current Tally

| Category | Count | Notes |
|----------|-------|-------|
| Theorems with `sorry` | 1 | HR_nonempty in SurfaceTension.lean |
| Axioms | 4 | Utranslate properties (measure completion) |
| Trivial placeholders | 12 | Future work items |

## Quick Start

```bash
# Install Lean 4 via elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build the project
cd Lean
lake build
```

## Project Structure

```
Riemann/
├── GA/                              # Geometric Algebra foundations
│   ├── Cl33.lean                   # Clifford algebra Cl(3,3)
│   └── Cl33Ops.lean                # Operations and spinors
├── ZetaSurface/                     # Main development
│   ├── CompletionCore.lean         # Abstract operator interface
│   ├── CompletionKernelModel.lean  # Concrete L² model
│   ├── CompletionMeasure.lean      # Weighted measure model
│   ├── Compression.lean            # Finite-dimensional compression
│   ├── CompressionRicker.lean      # Wavelet compression
│   ├── SpectralReal.lean           # Spectral reality proofs
│   ├── SpectralZeta.lean           # Spectral zeta functions
│   ├── TransferOperator.lean       # K(s) operator definition
│   ├── ZetaLinkFinite.lean         # Euler product connection
│   ├── AdapterQFD_Ricker.lean      # Ricker wavelet L² proofs
│   └── ...
└── Riemann.lean                     # Main entry point
```

## Core Mathematical Results

### Proven Theorems

1. **Adjoint Symmetry**: `K(s)† = K(1 - conj(s))`
   - File: `CompletionCore.lean`, `CompletionKernelModel.lean`

2. **Self-Adjoint on Critical Line**: `K(1/2 + it)† = K(1/2 + it)`
   - File: `SpectralReal.lean`, `CompletionMeasureModel.lean`

3. **Wavelet L² Membership**: Ricker wavelets and atoms are in L²
   - File: `AdapterQFD_Ricker.lean`

4. **Determinant-Eigenvalue Link**: `det(I - A) = 0 ⟹ 1 ∈ spectrum(A)`
   - File: `SpectralZeta.lean`

### Key Insight

The critical line Re(s) = 1/2 emerges as the unique fixed point of the involution s ↦ 1 - conj(s). On this line, the sieve operator K(s) is self-adjoint, hence has real spectrum. Off the critical line, K(s) is not self-adjoint.

## Documentation

- `required_lean_statements.md` - Tracks incomplete proofs for external contributors
- `docs/archive/` - Historical development documents

## Contributing

See `required_lean_statements.md` for proof requests. Contributions should:

1. Use Lean 4 with Mathlib v4.27.0-rc1
2. Follow Mathlib conventions
3. Avoid simp linter warnings
4. Include documentation

## License

MIT

## References

- Mathlib Documentation: https://leanprover-community.github.io/mathlib4_docs/
- Lean 4 Documentation: https://leanprover.github.io/lean4/doc/
