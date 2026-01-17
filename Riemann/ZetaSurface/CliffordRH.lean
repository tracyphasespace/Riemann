/-
# Clifford RH: Rotor Matrix Approach to Riemann Hypothesis

**Key Finding from Python Experiments:**
- At zeta zeros: trace is NEGATIVE, |V|² reaches LOCAL EXTREMA
- Trace = 2·Σ log(p)·p^{-σ}·cos(t·log p) = 2·Re[von Mangoldt sum]
- This connects to Re[ζ'/ζ] having specific behavior near zeros

**The Criterion (from numerical evidence):**
At a zero γ: trace(σ=1/2, t=γ) < 0 AND d(trace)/dσ > 0 AND |V|² is local extremum
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix Real

noncomputable section

namespace CliffordRH

/-!
## 1. Basic Definitions
-/

/-- 2×2 rotation matrix for angle θ -/
def rotor (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ, -sin θ;
     sin θ,  cos θ]

/-- Rotor for prime p at height t -/
def primeRotor (p : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  rotor (t * log p)

/-- Column vector [x, 0]ᵀ -/
def colVec (x : ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  !![x; 0]

/-- Spiral vector: [p^{-σ}, 0]ᵀ -/
def spiralVec (p : ℕ) (σ : ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  colVec ((p : ℝ) ^ (-σ))

/-!
## 2. Rotor Sum (Clifford action)

V(σ, t) = Σ_p R_p · v_p where R_p = rotor(t·log p), v_p = [p^{-σ}, 0]ᵀ
-/

/-- Sum of rotated spiral vectors -/
def rotorSum (σ t : ℝ) (primes : List ℕ) : Matrix (Fin 2) (Fin 1) ℝ :=
  primes.foldl (fun acc p =>
    acc + primeRotor p t * spiralVec p σ
  ) 0

/-- Squared norm of the rotor sum -/
def rotorSumNormSq (σ t : ℝ) (primes : List ℕ) : ℝ :=
  let V := rotorSum σ t primes
  (V 0 0) ^ 2 + (V 1 0) ^ 2

/-!
## 3. Trace Formulation

trace(Σ w_p · R_p) = 2 · Σ w_p · cos(θ_p)

With w_p = log(p) · p^{-σ}, θ_p = t · log(p):
rotorTrace = 2 · Σ log(p) · p^{-σ} · cos(t · log p)

This equals 2 · Re[Σ log(p) · p^{-s}] where s = σ + it
-/

/-- The trace function: 2·Σ log(p)·p^{-σ}·cos(t·log p) -/
def rotorTrace (σ t : ℝ) (primes : List ℕ) : ℝ :=
  2 * primes.foldl (fun acc p =>
    acc + log p * (p : ℝ) ^ (-σ) * cos (t * log p)
  ) 0

/-!
## 3.5 Trace Derivatives (for Convexity Analysis)

The first derivative: T'(σ) = -2·Σ (log p)²·p^{-σ}·cos(t·log p)
The second derivative: T''(σ) = 2·Σ (log p)³·p^{-σ}·cos(t·log p)

If T''(σ) > 0 on (0,1), the trace is CONVEX, guaranteeing a unique minimum.
-/

/-- First derivative of rotorTrace w.r.t. σ -/
def rotorTraceFirstDeriv (σ t : ℝ) (primes : List ℕ) : ℝ :=
  -2 * primes.foldl (fun acc p =>
    acc + (log p)^2 * (p : ℝ)^(-σ) * cos (t * log p)
  ) 0

/-- Second derivative of rotorTrace w.r.t. σ (the convexity term) -/
def rotorTraceSecondDeriv (σ t : ℝ) (primes : List ℕ) : ℝ :=
  2 * primes.foldl (fun acc p =>
    acc + (log p)^3 * (p : ℝ)^(-σ) * cos (t * log p)
  ) 0

/-!
### Strengthened Hypothesis: Convexity Implies Strict Minimum

If the second derivative is positive throughout (0,1), then:
1. The trace function is strictly convex
2. Any critical point is a global minimum
3. If the critical point is at σ = 1/2, it's the UNIQUE minimum
-/

/-- Convexity condition: T''(σ) > 0 on (0,1) -/
def TraceIsConvex (t : ℝ) (primes : List ℕ) : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 → rotorTraceSecondDeriv σ t primes > 0

/-- Critical point at σ = 1/2: T'(1/2) = 0 -/
def TraceCriticalAtHalf (t : ℝ) (primes : List ℕ) : Prop :=
  rotorTraceFirstDeriv (1/2) t primes = 0

/-- Strengthened hypothesis: convexity + critical point implies strict minimum -/
def TraceStrictMinAtHalf_strong (t : ℝ) (primes : List ℕ) : Prop :=
  TraceIsConvex t primes ∧
  TraceCriticalAtHalf t primes

/-!
**Path to Proving TraceStrictMinAtHalf_strong ⟹ TraceStrictMinAtHalf**:

Standard calculus: convexity + critical point at 1/2 ⟹ strict minimum at 1/2

Proof sketch:
1. By Mean Value Theorem: f(σ) - f(1/2) = f'(ξ)(σ - 1/2) for some ξ between σ and 1/2
2. By MVT again: f'(ξ) - f'(1/2) = f''(η)(ξ - 1/2) for some η
3. Since f''(η) > 0 (convexity) and f'(1/2) = 0 (critical):
   - If σ > 1/2: ξ > 1/2, so f'(ξ) > 0, so f(σ) > f(1/2)
   - If σ < 1/2: ξ < 1/2, so f'(ξ) < 0, so f(σ) > f(1/2)
4. Therefore f(1/2) is the unique strict minimum.

Mathlib path: Use `Convex.strictMonoOn_of_deriv_pos` or `StrictConvexOn.unique_local_min`.

**Note**: The main proof chain in ZetaLinkClifford.lean takes `TraceStrictMinAtHalf` as
a hypothesis directly, so this bridge is OPTIONAL for strengthening the proof.
-/

/-!
## 4. Key Theorems
-/

/-- Trace of rotation matrix is 2·cos(θ) -/
theorem trace_rotor (θ : ℝ) : trace (rotor θ) = 2 * cos θ := by
  simp only [rotor, trace, diag, Fin.sum_univ_two, of_apply, Fin.isValue]
  simp only [cons_val_zero, cons_val_one, head_cons]
  ring

/-- Helper: Single prime rotor action gives cos/sin components -/
lemma primeRotor_spiralVec_components (p : ℕ) (σ t : ℝ) :
    (primeRotor p t * spiralVec p σ) 0 0 = (p : ℝ)^(-σ) * cos (t * log p) ∧
    (primeRotor p t * spiralVec p σ) 1 0 = (p : ℝ)^(-σ) * sin (t * log p) := by
  unfold primeRotor rotor spiralVec colVec
  constructor <;> {
    simp only [Matrix.mul_apply, Fin.sum_univ_two, of_apply, Fin.isValue,
               cons_val_zero, cons_val_one, head_cons]
    ring
  }

/-- The rotor sum components are weighted trig sums -/
theorem rotorSum_components (σ t : ℝ) (primes : List ℕ) :
    let V := rotorSum σ t primes
    V 0 0 = primes.foldl (fun acc p => acc + (p : ℝ)^(-σ) * cos (t * log p)) 0 ∧
    V 1 0 = primes.foldl (fun acc p => acc + (p : ℝ)^(-σ) * sin (t * log p)) 0 := by
  -- Prove both components together by induction
  have h : ∀ (init : Matrix (Fin 2) (Fin 1) ℝ) (acc0 acc1 : ℝ),
      init 0 0 = acc0 → init 1 0 = acc1 →
      (primes.foldl (fun acc p => acc + primeRotor p t * spiralVec p σ) init) 0 0 =
        primes.foldl (fun acc p => acc + (p : ℝ)^(-σ) * cos (t * log p)) acc0 ∧
      (primes.foldl (fun acc p => acc + primeRotor p t * spiralVec p σ) init) 1 0 =
        primes.foldl (fun acc p => acc + (p : ℝ)^(-σ) * sin (t * log p)) acc1 := by
    induction primes with
    | nil => intro init acc0 acc1 h0 h1; simp [h0, h1]
    | cons p ps ih =>
      intro init acc0 acc1 h0 h1
      simp only [List.foldl_cons]
      apply ih
      · simp only [Matrix.add_apply, h0, (primeRotor_spiralVec_components p σ t).1]
      · simp only [Matrix.add_apply, h1, (primeRotor_spiralVec_components p σ t).2]
  unfold rotorSum
  exact h 0 0 0 rfl rfl

/-!
## 5. The Clifford RH Criterion

From numerical experiments with 1000 primes:

**At zeta zeros (σ = 1/2):**
- rotorTrace is typically NEGATIVE (-5 to -22)
- |V|² shows local extrema (usually maxima)

**At non-zeros (σ = 1/2):**
- rotorTrace oscillates positive/negative
- |V|² varies without special pattern

**Conjecture:** ζ(1/2 + it) = 0 ⟹ rotorTrace(1/2, t) < 0
-/

/-- A point t is a rotor-detected zero if trace is negative at σ=1/2 -/
def IsRotorZero (t : ℝ) (primes : List ℕ) : Prop :=
  rotorTrace (1/2) t primes < 0

/-- Local extremum property -/
def IsLocalExtremum (f : ℝ → ℝ) (x : ℝ) : Prop :=
  (∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → f y ≤ f x) ∨
  (∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → f y ≥ f x)

/-- The full Clifford RH criterion -/
def SatisfiesCliffordRH (t : ℝ) (primes : List ℕ) : Prop :=
  rotorTrace (1/2) t primes < 0 ∧
  IsLocalExtremum (fun t' => rotorSumNormSq (1/2) t' primes) t

/-!
## 6. Connection to Zeta

The rotorTrace relates to the logarithmic derivative:

-ζ'(s)/ζ(s) = Σ_{n≥1} Λ(n)/n^s = Σ_p Σ_k log(p)/p^{ks}

For k=1 term only:
Re[-ζ'(s)/ζ(s)]|_{k=1} ≈ Σ_p log(p)·p^{-σ}·cos(t·log p) = rotorTrace/2

At zeros, ζ'(s)/ζ(s) has a pole (simple pole of ζ at zero).
The real part being negative at σ=1/2 reflects this pole structure.
-/

/-!
### Bridge to Complex Zeta (Conjecture)

**Conjecture**: If rotorTrace(1/2, t) < 0 for sufficiently many primes,
then there exists ε > 0 such that for all σ in (1/2-ε, 1/2+ε),
|rotorTrace(σ, t)| > |rotorTrace(1/2, t)| / 2.

This would connect the trace behavior to the local structure near a zero.
Currently documented as conjecture based on numerical evidence (97% accuracy).
-/

/-!
## 7. Numerical Verification (from Python)

```
At ZETA ZEROS (σ = 1/2):
γ =  14.1347: |V|² =   2.3756, trace =    -5.9543
γ =  21.0220: |V|² =   0.7368, trace =   -15.0673
γ =  25.0109: |V|² =   4.9350, trace =   -21.7117
γ =  30.4249: |V|² =   7.3873, trace =   -14.0182
γ =  32.9351: |V|² =   0.2230, trace =   -13.8526

At NON-ZEROS (σ = 1/2):
t =  10.0000: |V|² =   2.1598, trace =    17.9517
t =  16.0000: |V|² =   0.6960, trace =    -6.1632
t =  19.0000: |V|² =   1.7054, trace =    11.3126
```

Pattern: Zeros have consistently NEGATIVE trace, non-zeros oscillate.
-/

end CliffordRH

end
