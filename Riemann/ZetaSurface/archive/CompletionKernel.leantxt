/-
# Kernel Completion: Weights in the Operator

**Purpose**: Complete the transfer operator by adding backward shifts with
algebraically-chosen weights, achieving adjoint symmetry.

## Strategy

We work on H := L²(ℝ, du; ℂ) (standard Hilbert space) or HR := L²(ℝ, du; ℝ)
for the Cl33 version.

The completed operator includes both forward and backward prime shifts:
  K(s) = Σ_p [ α(s,p) · T_p + β(s,p) · T_p⁻¹ ]

where:
  α(s, p) = p^{-s}           (forward weight)
  β(s, p) = conj(α(1 - conj(s), p))  (backward weight, "completion knob")

## Key Result

  K(s)† = K(1 - conj(s))

This mirrors the functional equation of the completed zeta function.

## Architecture Note (Cl33 Refactoring)

In the Cl33 version:
- `conj(s)` becomes `reverse(s.toCl33)` where `reverse` is Clifford reversal
- For `s = σ + B·t`, `reverse(s) = σ - B·t` (since `reverse(B) = -B`)
- This is exactly complex conjugation in the Span{1, B} ≅ ℂ subalgebra

## Why This Works

Taking adjoint:
- Swaps T_p ↔ T_p⁻¹ (since (T_p)† = T_p⁻¹)
- Conjugates weights (since (c·U)† = conj(c)·U†)

The choice of β is designed so that this swap matches K(1 - conj(s)).

## References

- TransferOperator.lean (basic operator)
- PrimeShifts.lean (prime shift operators)
- Riemann/GA/Cl33Ops.lean (Clifford algebra weights)
-/

import Riemann.ZetaSurface.TransferOperator

noncomputable section
open scoped Real ComplexConjugate
open MeasureTheory
open Riemann.GA
open Riemann.GA.Ops
open Complex

namespace Riemann.ZetaSurface.CompletionKernel

/-! ## 1. Completion Weights (Cl33 - Primary) -/

/--
Backward weight components for Cl33.
For s = σ + B·t, β(s,p) = reverse(α(1 - conj(s), p)) = reverse(α(1 - σ + B·t, p))
-/
def βCos (s : SpectralParam) (p : ℕ) : ℝ :=
  αCos s.funcEq p

def βSin (s : SpectralParam) (p : ℕ) : ℝ :=
  -αSin s.funcEq p  -- Negated because reversal negates B coefficient

/--
On the critical line (σ = 1/2), funcEq is the identity on sigma.
s.funcEq = {sigma := 1 - s.sigma, t := s.t}
For s.sigma = 1/2: s.funcEq.sigma = 1 - 1/2 = 1/2
-/
theorem funcEq_sigma_half (t : ℝ) :
    (criticalLine t).funcEq.sigma = 1/2 := by
  unfold criticalLine SpectralParam.funcEq
  norm_num

/--
At real s = 1/2 (t = 0), β = α (self-adjoint weights).
-/
theorem α_β_match_half_real (p : ℕ) :
    αCos (criticalLine 0) p = βCos (criticalLine 0) p ∧
    αSin (criticalLine 0) p = 0 := by
  -- At t = 0, criticalLine 0 = {sigma := 1/2, t := 0}
  -- αCos = p^{-1/2} * cos(0) = p^{-1/2}
  -- βCos = αCos(funcEq(criticalLine 0)) = αCos({sigma := 1/2, t := 0}) = p^{-1/2}
  -- αSin = p^{-1/2} * sin(0) = 0
  constructor
  · -- αCos = βCos
    -- βCos s = αCos s.funcEq
    -- criticalLine 0 = {sigma := 1/2, t := 0}
    -- (criticalLine 0).funcEq = {sigma := 1 - 1/2, t := 0} = {sigma := 1/2, t := 0}
    -- So βCos (criticalLine 0) = αCos {sigma := 1/2, t := 0} = αCos (criticalLine 0)
    unfold βCos criticalLine SpectralParam.funcEq
    -- Need to show αCos {1/2, 0} p = αCos {1 - 1/2, 0} p
    -- These are equal because 1/2 = 1 - 1/2
    congr 1
    simp only [SpectralParam.mk.injEq]
    constructor <;> norm_num
  · -- αSin = 0
    unfold αSin criticalLine
    simp only [zero_mul, Real.sin_zero, mul_zero]

/-! ## 2. Completion Weights (Complex - Legacy) -/

/--
Forward weight (same as in TransferOperator).
α(s, p) = p^{-s}
-/
def α (s : ℂ) (p : ℕ) : ℂ :=
  (p : ℂ) ^ (-s)

/--
Backward weight: the "completion knob".
β(s, p) = conj(α(1 - conj(s), p))

This definition is chosen so that K(s)† = K(1 - conj(s)).
-/
def β (s : ℂ) (p : ℕ) : ℂ :=
  conj (α (1 - conj s) p)

/--
Key identity: β expressed in terms of power.
-/
theorem β_eq (s : ℂ) (p : ℕ) (hp : 1 < p) :
    β s p = (p : ℂ) ^ (-(1 - s)) := by
  unfold β α
  -- conj(p^{-(1-conj(s))}) = p^{-(1-s)}
  -- For natural p, arg(p : ℂ) = 0 ≠ π
  have hp_arg : (p : ℂ).arg ≠ Real.pi := by
    have h1 : (p : ℂ) = ((p : ℝ) : ℂ) := by norm_cast
    rw [h1, Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ p)]
    exact Real.pi_ne_zero.symm
  -- Use conj_cpow: conj x ^ n = conj (x ^ conj n)
  -- For p real positive: conj p = p, so p ^ n = conj (p ^ conj n)
  have h_conj_nat : (starRingEnd ℂ) (p : ℂ) = (p : ℂ) := Complex.conj_natCast p
  -- conj_cpow gives: conj(p) ^ n = conj(p ^ conj(n))
  -- With conj(p) = p: p ^ n = conj(p ^ conj(n))
  -- Taking conj: conj(p ^ n) = p ^ conj(n)
  -- Actually we use: conj(p ^ (-(1 - conj s))) = p ^ conj(-(1 - conj s)) = p ^ (-(1-s))
  have h1 := Complex.conj_cpow (p : ℂ) (-(1 - conj s)) hp_arg
  rw [h_conj_nat] at h1
  -- h1: p ^ (-(1 - conj s)) = conj(p ^ conj(-(1 - conj s)))
  -- conj(-(1 - conj s)) = -(1 - conj(conj s)) = -(1 - s)
  simp only [map_neg, map_sub, map_one, conj_conj] at h1
  -- h1: p ^ (-(1 - conj s)) = conj(p ^ (-(1 - s)))
  -- So: conj(p ^ (-(1 - conj s))) = conj(conj(p ^ (-(1 - s)))) = p ^ (-(1-s))
  rw [h1]
  simp only [conj_conj]

/--
At s = 1/2 (real), the weights are related by conjugation.
-/
theorem α_β_half (p : ℕ) :
    β (1/2 : ℂ) p = conj (α (1/2 : ℂ) p) := by
  unfold β
  -- β(1/2) = conj(α(1 - conj(1/2))) = conj(α(1/2)) since conj(1/2) = 1/2 for real
  congr 1
  -- Goal: α(1 - conj(1/2)) p = α(1/2) p
  congr 1
  -- Goal: 1 - conj(1/2) = 1/2
  simp only [map_div₀, map_one, map_ofNat]
  ring

/-! ## 2. Completed Single-Prime Term -/

/--
One completed summand for a single prime p:
  K_p(s) = α(s,p) · T_p + β(s,p) · T_p⁻¹
-/
def Kterm (s : ℂ) (p : ℕ) : H →L[ℂ] H :=
  (α s p) • (Tprime p).toContinuousLinearMap +
  (β s p) • (TprimeInv p).toContinuousLinearMap

/-! ## 3. Adjoint Lemmas -/

/--
Adjoint of scalar multiplication: (c · U)† = conj(c) · U†
-/
theorem adjoint_smul (c : ℂ) (U : H →L[ℂ] H) :
    (c • U).adjoint = conj c • U.adjoint := by
  exact map_smulₛₗ ContinuousLinearMap.adjoint c U

/--
Adjoint distributes over addition.
-/
theorem adjoint_add' (U V : H →L[ℂ] H) :
    (U + V).adjoint = U.adjoint + V.adjoint := by
  exact map_add ContinuousLinearMap.adjoint U V

/--
Adjoint of a Finset sum.
-/
theorem adjoint_finset_sum {ι : Type*} (S : Finset ι) (F : ι → H →L[ℂ] H) :
    (S.sum F).adjoint = S.sum (fun i => (F i).adjoint) := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact map_zero ContinuousLinearMap.adjoint
  | insert a S' ha ih =>
    simp only [Finset.sum_insert ha]
    rw [adjoint_add', ih]

/-! ## 4. Adjoint of Single-Prime Term -/

/--
**Key Lemma**: Adjoint of Kterm swaps α ↔ β and T_p ↔ T_p⁻¹.
-/
theorem Kterm_adjoint (s : ℂ) (p : ℕ) :
    (Kterm s p).adjoint = Kterm (1 - conj s) p := by
  -- Proof: (α·T_p + β·T_p⁻¹)† = conj(α)·T_p⁻¹ + conj(β)·T_p
  unfold Kterm
  rw [adjoint_add', adjoint_smul, adjoint_smul]
  rw [Tprime_adjoint, TprimeInv_adjoint]
  -- Now we have: conj(α s p) • TprimeInv + conj(β s p) • Tprime
  -- Need to match: α(1 - conj s) • Tprime + β(1 - conj s) • TprimeInv
  rw [add_comm]
  congr 1
  -- First term: conj(β s p) = α(1 - conj s, p)
  · unfold β
    simp only [conj_conj]
  -- Second term: conj(α s p) = β(1 - conj s, p)
  · unfold β α
    -- Goal: conj(p^{-s}) = conj(p^{-(1 - conj(1 - conj s))})
    -- Simplify: 1 - conj(1 - conj s) = 1 - (1 - conj(conj s)) = 1 - (1 - s) = s
    congr 1
    congr 1
    simp only [map_sub, map_one, conj_conj, sub_sub_cancel]

/-! ## 5. Completed Operator -/

/--
Completed finite operator over primes up to B.
K(s, B) = Σ_{p ≤ B prime} Kterm(s, p)
-/
def K (s : ℂ) (B : ℕ) : H →L[ℂ] H := by
  classical
  exact (primesUpTo B).sum (fun p => Kterm s p)

/-! ## 6. Main Adjoint Symmetry Theorem -/

/--
**Main Theorem (Kernel Completion)**: The completed operator satisfies
the adjoint relation mirroring the functional equation.

  K(s)† = K(1 - conj(s))

This is the operator-theoretic analog of ξ(s) = ξ(1-s).
-/
theorem K_adjoint_symm (s : ℂ) (B : ℕ) :
    (K s B).adjoint = K (1 - conj s) B := by
  classical
  unfold K
  rw [adjoint_finset_sum]
  congr 1
  funext p
  exact Kterm_adjoint s p

/-! ## 7. Unitarity on the Critical Line -/

/--
On the critical line s = 1/2 + it, the operator is self-adjoint:
  K(1/2 + it)† = K(1/2 + it)

Proof:
- conj(1/2 + it) = 1/2 - it
- 1 - (1/2 - it) = 1/2 + it
- So K(1/2 + it)† = K(1 - conj(1/2 + it)) = K(1/2 + it)
-/
theorem K_adjoint_critical (t : ℝ) (B : ℕ) :
    (K (1/2 + t * I) B).adjoint = K (1/2 + t * I) B := by
  rw [K_adjoint_symm]
  congr 1
  -- 1 - conj(1/2 + t*I) = 1 - (1/2 - t*I) = 1/2 + t*I
  simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, conj_ofReal, conj_I]
  ring

/--
At real s = 1/2, the operator is self-adjoint.
  K(1/2)† = K(1/2)
-/
theorem K_selfadjoint_half (B : ℕ) :
    (K (1/2 : ℂ) B).adjoint = K (1/2 : ℂ) B := by
  rw [K_adjoint_symm]
  congr 1
  -- 1 - conj(1/2) = 1 - 1/2 = 1/2 ✓
  simp only [map_div₀, map_one, map_ofNat]
  ring

/-! ## Physical Summary

Kernel completion achieves the functional equation symmetry algebraically:

1. **Forward + backward shifts**: K(s) uses both T_p and T_p⁻¹
2. **Designed weights**: β is chosen so adjoint swaps correctly
3. **Adjoint symmetry**: K(s)† = K(1 - conj(s))
4. **Critical line**: Self-adjoint at s = 1/2

The proof is essentially algebraic, using only:
- Adjoint of isometry = inverse
- Adjoint of scalar multiplication conjugates the scalar
- Adjoint distributes over sums

This is the "first winner" approach: minimal analysis, maximal algebra.
-/

end Riemann.ZetaSurface.CompletionKernel

end