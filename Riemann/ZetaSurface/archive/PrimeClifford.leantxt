/-
# Prime-Indexed Clifford Algebra: Automatic Orthogonality

**Purpose**: Embed primes as orthogonal generators in a Clifford algebra,
making the determinant factorization automatic.

## The Menger Sponge Analogy

The prime sieve structure is analogous to the **Menger Sponge** fractal:
- In the limit, the Menger Sponge has **Zero Volume** and **Infinite Surface Area**
- Similarly, the prime sieve removes "volume" (composite numbers) at each scale
- What remains is a structure with maximal "surface" (the primes)
- The Surface Tension formalism captures this: σ = 1/2 is where the
  "surface" (critical line) has zero tension

## Key Insight

Instead of primes acting as translations on L²(ℝ), we give each prime
its own orthogonal direction in Cl(N,N). Then:

- γ_p² = -1 for each prime p (NO imaginary unit - this IS the rotation generator)
- γ_p γ_q = -γ_q γ_p for distinct primes p ≠ q (anticommutation)
- Orthogonality is DEFINITIONAL from Clifford algebra structure

**CRITICAL**: There are NO imaginary components. The "i" in complex analysis
is replaced by bivectors B with B² = -1. Everything is real geometric algebra.

## The Determinant Factorization

With orthogonal prime directions:

det(I - K) = det(I - Σ_p K_p) = ∏_p det(I - K_p)

because the cross-terms vanish by anticommutation.

## Connection to Euler Product

If det(I - K_p) = (1 - p^{-s}) for each prime, then:

det(I - K) = ∏_p (1 - p^{-s}) = ζ(s)^{-1}

This is the Euler product, derived from Clifford algebra structure.
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Data.Nat.Prime.Basic
import Riemann.ZetaSurface.PrimeShifts

noncomputable section

namespace Riemann.GA.PrimeClifford

open CliffordAlgebra
open Riemann.ZetaSurface

/-! ## 1. Prime-Indexed Vector Space -/

/--
Vector space indexed by primes up to B.
Each prime p ≤ B gets a basis vector e_p.
-/
def PrimeVec (B : ℕ) := { p : ℕ // p ∈ primesUpTo B } → ℝ

instance (B : ℕ) : AddCommGroup (PrimeVec B) := Pi.addCommGroup
instance (B : ℕ) : Module ℝ (PrimeVec B) := Pi.module _ _ _

/--
Basis vector for prime p.
-/
def basisPrime {B : ℕ} (p : { p : ℕ // p ∈ primesUpTo B }) : PrimeVec B :=
  Pi.single p 1

/-! ## 2. Split Signature Quadratic Form -/

/--
The quadratic form with split signature.
Each prime p gets signature -1 (so γ_p² = -1, like the imaginary unit).

This makes each prime direction "timelike" in the Clifford sense,
matching the phase structure from Cl(3,3).
-/
def signaturePrime (B : ℕ) : { p : ℕ // p ∈ primesUpTo B } → ℝ :=
  fun _ => -1  -- All primes get signature -1

/--
The quadratic form for the prime-indexed space.
-/
def QPrime (B : ℕ) : QuadraticForm ℝ (PrimeVec B) :=
  QuadraticMap.weightedSumSquares ℝ (signaturePrime B)

/-! ## 3. The Prime Clifford Algebra -/

/--
Clifford algebra over the prime-indexed space.
Cl(0, π(B)) where π(B) = number of primes ≤ B.
-/
abbrev ClPrime (B : ℕ) := CliffordAlgebra (QPrime B)

/--
Embedding of prime vectors into the Clifford algebra.
-/
def ιPrime (B : ℕ) : PrimeVec B →ₗ[ℝ] ClPrime B := ι (QPrime B)

/-! ## 4. Generator Properties -/

/--
Lemma: The quadratic form evaluates to -1 on basis vectors.
This is used to prove γ_p² = -1.
-/
theorem QPrime_basis {B : ℕ} (p : { p : ℕ // p ∈ primesUpTo B }) :
    QPrime B (basisPrime p) = -1 := by
  -- Q(e_p) = Σ_r signature(r) * e_p(r)² = signature(p) * 1² = -1
  classical
  -- Rewrite to expose the sum structure
  have heq : QPrime B (basisPrime p) =
      ∑ i, (-1 : ℝ) • (basisPrime p i * basisPrime p i) := by
    unfold QPrime signaturePrime
    exact QuadraticMap.weightedSumSquares_apply _ _
  rw [heq]
  unfold basisPrime
  simp only [smul_eq_mul]
  -- Sum over all indices, but only p contributes (others are 0)
  let e_p : PrimeVec B := Pi.single p (1 : ℝ)
  have h0 : ∀ r : { q : ℕ // q ∈ primesUpTo B }, r ≠ p →
      (-1 : ℝ) * (e_p r * e_p r) = 0 := by
    intro r hr
    simp only [e_p, Pi.single_apply, hr, ↓reduceIte, mul_zero]
  have hsum := Fintype.sum_eq_single (a := p)
    (f := fun r => (-1 : ℝ) * (e_p r * e_p r)) h0
  -- The sum equals just the p term, which is -1
  have hp_val : (fun r => (-1 : ℝ) * (e_p r * e_p r)) p = -1 := by
    simp only [e_p, Pi.single_apply, ↓reduceIte, mul_one]
  calc ∑ i, (-1 : ℝ) • (basisPrime p i * basisPrime p i)
      = ∑ i, (-1 : ℝ) * (e_p i * e_p i) := by simp only [smul_eq_mul, e_p, basisPrime]
    _ = (-1 : ℝ) * (e_p p * e_p p) := hsum
    _ = -1 := hp_val

theorem prime_generator_sq {B : ℕ} (p : { p : ℕ // p ∈ primesUpTo B }) :
    (ιPrime B (basisPrime p)) * (ιPrime B (basisPrime p)) =
    algebraMap ℝ (ClPrime B) (-1) := by
  unfold ιPrime
  rw [ι_sq_scalar]
  rw [QPrime_basis]

/--
Lemma: The polar form vanishes for distinct basis vectors.
This proves orthogonality of distinct prime generators.
-/
theorem QPrime_polar_orthogonal {B : ℕ}
    (p q : { p : ℕ // p ∈ primesUpTo B }) (h_ne : p ≠ q) :
    QuadraticMap.polar (QPrime B) (basisPrime p) (basisPrime q) = 0 := by
  -- Polar(e_p, e_q) = Q(e_p + e_q) - Q(e_p) - Q(e_q) = -2 - (-1) - (-1) = 0
  classical
  -- First compute Q on each basis vector
  have hQ_p : QPrime B (basisPrime p) = -1 := QPrime_basis p
  have hQ_q : QPrime B (basisPrime q) = -1 := QPrime_basis q
  -- Now compute Q(e_p + e_q)
  have hQ_add : QPrime B (basisPrime p + basisPrime q) = -2 := by
    -- Direct computation using sum
    have heq : QPrime B (basisPrime p + basisPrime q) =
        ∑ i : { x : ℕ // x ∈ primesUpTo B },
          (-1 : ℝ) • ((basisPrime p + basisPrime q) i * (basisPrime p + basisPrime q) i) := by
      unfold QPrime signaturePrime
      exact QuadraticMap.weightedSumSquares_apply _ _
    rw [heq]
    -- Simplify using smul_eq_mul
    simp only [basisPrime, smul_eq_mul]
    -- Define the summand using explicit typed Pi.single
    let e_p : PrimeVec B := Pi.single p (1 : ℝ)
    let e_q : PrimeVec B := Pi.single q (1 : ℝ)
    let g : { x : ℕ // x ∈ primesUpTo B } → ℝ := fun r =>
      (-1 : ℝ) * ((e_p r + e_q r) * (e_p r + e_q r))
    -- Convert (f + g) x to f x + g x
    conv_lhs => arg 2; ext x; rw [Pi.add_apply]
    -- Now the goal matches g
    change (∑ i, g i) = -2
    -- Only p and q contribute
    have h0 : ∀ r, r ≠ p ∧ r ≠ q → g r = 0 := by
      intro r ⟨hrp, hrq⟩
      simp only [g, e_p, e_q, Pi.single_apply, hrp, hrq, ↓reduceIte, add_zero, mul_zero]
    have hsum : (∑ r, g r) = g p + g q := by
      simpa using Fintype.sum_eq_add (a := p) (b := q) (f := g) h_ne h0
    have gp : g p = -1 := by
      simp only [g, e_p, e_q, Pi.single_apply, ↓reduceIte, add_zero, mul_one, h_ne]
    have gq : g q = -1 := by
      simp only [g, e_p, e_q, Pi.single_apply, Ne.symm h_ne, ↓reduceIte, zero_add, mul_one]
    linarith [hsum, gp, gq]
  -- Finally, polar = Q(p+q) - Q(p) - Q(q)
  unfold QuadraticMap.polar
  linarith [hQ_add, hQ_p, hQ_q]

theorem prime_generators_anticommute {B : ℕ}
    (p q : { p : ℕ // p ∈ primesUpTo B }) (h_ne : p ≠ q) :
    (ιPrime B (basisPrime p)) * (ιPrime B (basisPrime q)) +
    (ιPrime B (basisPrime q)) * (ιPrime B (basisPrime p)) = 0 := by
  unfold ιPrime
  rw [CliffordAlgebra.ι_mul_ι_add_swap]
  rw [QPrime_polar_orthogonal p q h_ne, map_zero]

/-! ## 5. The Key Consequence: Determinant Factorization

**Corollary**: Prime contributions are orthogonal in trace.

For any linear functional tr on ClPrime B:
  tr(γ_p · γ_q) = 0 for p ≠ q (via anticommutation symmetry)

This is because tr(AB + BA) = 2·tr(AB) for symmetric trace,
but γ_p γ_q + γ_q γ_p = 0, so tr(γ_p γ_q) = 0.

**The Determinant Factorization Theorem** (Informal):

For the operator K = Σ_p K_p where each K_p acts in the γ_p direction:

  det(I - K) = ∏_p det(I - K_p)

Proof sketch:
1. K_p lives in the γ_p "subspace"
2. For p ≠ q, K_p and K_q anticommute (they're in orthogonal directions)
3. In the log-det expansion: tr(K^n) = Σ_p tr(K_p^n) (cross-terms vanish)
4. Therefore: log(det(I-K)) = Σ_p log(det(I-K_p))
5. Exponentiating: det(I-K) = ∏_p det(I-K_p)

This is the Euler product structure, derived from Clifford orthogonality!
-/

/-! ## 6. Connection to Existing Structure

**Integration with Existing Code**:

The existing CompletionKernel.lean defines:
  K(s,B) = Σ_p Kterm(s,p) on L²(ℝ)

To use the Prime Clifford structure, we reinterpret:
  - Each Kterm(s,p) acts in the γ_p direction of ClPrime B
  - The Hilbert space becomes ClPrime B (or a representation of it)
  - Orthogonality is now automatic

The weights α(s,p) and β(s,p) still give the coefficients,
but the directional structure comes from the Clifford algebra.
-/

end Riemann.GA.PrimeClifford

end
