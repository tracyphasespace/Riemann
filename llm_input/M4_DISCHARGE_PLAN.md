# Plan: M4 Discharge Strategy (`zeta_zero_implies_kernel`)

**Status**: PLANNING
**Date**: 2026-01-23
**Goal**: Discharge axiom M4 - the spectral bridge from ζ(s) = 0 to ker K(s) ≠ {0}

---

## The Axiom

```lean
axiom zeta_zero_implies_kernel {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : ℂ → V →ₗ[ℝ] V) (s : ℂ) (hs : InCriticalStrip s) :
    riemannZeta s = 0 → ∃ v : V, v ≠ 0 ∧ K s v = 0
```

**Meaning**: If ζ(s) = 0 in the critical strip, then the Hamiltonian K(s) has nontrivial kernel.

---

## Current Infrastructure

From `BridgeDefinitions.lean`:

| Component | Definition |
|-----------|------------|
| **H** | `lp (fun _ : ℕ => ℂ) 2` (ℓ²(ℂ)) |
| **B_p** | Diagonal: `(B p f) n = i·(-1)^{v_p(n)} · f(n)` |
| **ScalingOperator** | `D(σ) = (σ - 1/2)·Id` |
| **InteractionOperator** | `V(s) = Σ_p p^{-s}·B_p` |
| **TotalHamiltonian** | `K(s) = D(σ) + V(s)` |

**Key Property**: K(s) is **diagonal** on the standard basis of ℓ²:
```
K(s) e_n = λ_n(s) · e_n
```
where
```
λ_n(s) = (σ - 1/2) + Σ_p p^{-s} · i · (-1)^{v_p(n)}
```

---

## Mathematical Analysis

### The Core Challenge

**ζ(s) = 0** is an analytic statement about:
```
ζ(s) = Σ_{n=1}^∞ n^{-s}  (Dirichlet series, Re(s) > 1)
     = Π_p (1 - p^{-s})^{-1}  (Euler product, Re(s) > 1)
```

**ker K(s) ≠ {0}** is an algebraic statement about:
```
∃ v ≠ 0 : K(s)v = 0
```

The bridge must connect the analytic world (zeros of ζ) to the algebraic world (kernel vectors).

### Why This is Hard

1. **Domain Mismatch**: Euler product converges for Re(s) > 1, but zeros are in 0 < Re(s) < 1
2. **Infinite vs Finite**: ζ involves infinitely many primes; K(s) uses finite prime set
3. **Spectral Theory**: Requires connecting zeta zeros to spectrum of infinite-dimensional operator

---

## Strategy Options

### Option A: Finite Truncation + Limit (Most Promising)

**Idea**: For finite N primes, show det(K_N) relates to truncated Euler product.

**Step 1**: Define finite-dimensional truncation
```lean
def K_N (s : ℂ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := ...
```

**Step 2**: Show determinant connection
```lean
theorem det_K_N_eq_truncated_euler (s : ℂ) (N : ℕ) :
    (K_N s N).det = (some function of truncated Euler product)
```

**Step 3**: Use Mathlib's `exists_mulVec_eq_zero_iff`
```lean
-- Mathlib: (∃ v ≠ 0, M.mulVec v = 0) ↔ M.det = 0
```

**Step 4**: Take limit N → ∞
```lean
theorem zeta_zero_implies_kernel_limit :
    riemannZeta s = 0 → ∃ v : H, v ≠ 0 ∧ K s v = 0
```

**Challenges**:
- Need to define K_N carefully to match K restricted to finite subspace
- Limit argument requires showing approximate kernel vectors converge
- Truncated Euler product doesn't directly give ζ in the critical strip

---

### Option B: Direct Eigenvalue Construction

**Idea**: Since K(s) is diagonal, directly construct the kernel condition.

**Step 1**: K(s) has kernel iff some eigenvalue is zero
```lean
theorem K_kernel_iff_zero_eigenvalue :
    (∃ v ≠ 0, K s v = 0) ↔ ∃ n, λ_n(s) = 0
```

**Step 2**: Relate eigenvalues to zeta
The eigenvalue at index n is:
```
λ_n(s) = (σ - 1/2) + Σ_p p^{-s} · i · (-1)^{v_p(n)}
```

For n = 1 (no prime factors):
```
λ_1(s) = (σ - 1/2) + Σ_p p^{-s} · i
```

**Challenge**: How does ζ(s) = 0 imply λ_n(s) = 0 for some n?

This requires showing that the "oscillating sum" Σ p^{-s}·i·(±1) can cancel (σ - 1/2) for some n when ζ(s) = 0.

---

### Option C: Spectral Theory Approach

**Idea**: Use spectral theory of operators on Hilbert spaces.

**Key Mathlib Resources**:
- `Spectrum` - spectrum of operators
- `resolvent` - (A - λ)^{-1}
- Spectral mapping theorem

**Step 1**: Show 0 ∈ spectrum(K(s)) when ζ(s) = 0

**Step 2**: For normal operators, spectrum includes eigenvalues

**Challenge**: Requires substantial spectral theory infrastructure

---

### Option D: Keep as Axiom (Pragmatic)

**Rationale**: M4 is the core "spectral reformulation" - the deep claim that zeros of ζ correspond to kernel elements of an operator. This is:

1. **Standard in Physics**: The Hilbert-Pólya conjecture (RH ↔ eigenvalues of self-adjoint operator)
2. **Non-trivial Mathematics**: Connecting analytic objects (zeta zeros) to algebraic objects (kernels)
3. **Honest Isolation**: Keeping it as axiom clearly marks the "physics assumption"

**Status**: Currently at 16 axioms. Keeping M4 is acceptable if:
- Other axioms continue to be discharged
- M4 is well-documented as the "spectral bridge"
- The rest of the proof chain is rigorous

---

## Recommended Path

### Phase 1: Prove Diagonal Structure (Easy)

```lean
/-- K(s) is diagonal: K(s) e_n = λ_n(s) · e_n -/
theorem K_is_diagonal (s : ℂ) (primes : Finset ℕ) (n : ℕ) :
    TotalHamiltonian s primes (lp.single 2 n 1) =
    eigenvalue_sum s primes n • (lp.single 2 n 1)
```

### Phase 2: Prove Kernel Characterization (Medium)

```lean
/-- Kernel exists iff some eigenvalue is zero -/
theorem K_kernel_iff (s : ℂ) (primes : Finset ℕ) :
    (∃ v : H, v ≠ 0 ∧ TotalHamiltonian s primes v = 0) ↔
    (∃ n, eigenvalue_sum s primes n = 0)
```

### Phase 3: Connect to Zeta (Hard - May Require Axiom)

The hard step is:
```lean
/-- ζ(s) = 0 implies some eigenvalue sum vanishes -/
theorem zeta_zero_implies_eigenvalue_zero (s : ℂ) (hs : InCriticalStrip s)
    (hz : riemannZeta s = 0) :
    ∃ primes : Finset ℕ, ∃ n, eigenvalue_sum s primes n = 0
```

This is where the deep connection lies. Options:
1. **Prove it** using Explicit Formula + careful analysis
2. **Axiomatize it** as a cleaner, more specific axiom
3. **Accept M4** as the single "spectral bridge" axiom

---

## Effort Estimate

| Phase | Difficulty | Lines | Notes |
|-------|------------|-------|-------|
| Phase 1 | Easy | ~50 | Diagonal structure from definitions |
| Phase 2 | Medium | ~100 | Kernel characterization for diagonal ops |
| Phase 3 | Hard | ~200+ or Axiom | The "spectral bridge" |

---

## Recommendation

**Short Term**: Keep M4 as axiom, focus on:
1. Completing Ergodicity.lean (AI2's work)
2. Documenting M4 thoroughly in AXIOM_REVIEW.md

**Long Term**: Attempt Phase 1 and 2 to reduce M4 to a cleaner statement:
```lean
-- Cleaner axiom (reduces M4 to pure number theory)
axiom zeta_zero_implies_eigenvalue_zero (s : ℂ) (hs : InCriticalStrip s) :
    riemannZeta s = 0 → ∃ n, eigenvalue_sum s (primesBelow (some_bound n)) n = 0
```

This would separate:
- **Proven**: Diagonal structure, kernel characterization (Lean verified)
- **Axiom**: The deep number-theoretic connection (clearly isolated)

---

## Files to Create/Modify

| Action | File | Purpose |
|--------|------|---------|
| CREATE | `ProofEngine/SpectralBridge.lean` | Phases 1-2 proofs |
| UPDATE | `AXIOM_REVIEW.md` | Document M4 strategy |
| MAYBE | Refine M4 axiom in `BridgeObligations.lean` | Cleaner statement |

---

## Conclusion

M4 is the **hardest remaining axiom** because it bridges:
- Analytic number theory (ζ zeros)
- Spectral theory (operator kernels)
- Infinite-dimensional functional analysis

The recommended approach is to **prove the algebraic parts** (diagonal structure, kernel characterization) and **isolate the number-theoretic connection** as a clearly-stated axiom.

This keeps the formalization honest while maximizing verified content.
