import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Riemann.ZetaSurface.CliffordRH
import Riemann.ProofEngine.RotorTraceComputation

noncomputable section
open Real

namespace ProofEngine

/-!
## Numerical Helper Lemmas (Atomic Units)
-/

/-- Atom 1: Evaluation of a single rotor term. -/
def rotorTerm (σ t : ℝ) (p : ℕ) : ℝ :=
  Real.log p * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p)

/--
**Trace Negativity at First Zero** (PROVEN — formerly an axiom)

At the first zeta zero height t ≈ 14.134725, with σ = 1/2,
the rotor trace over primes below 7920 is strictly less than -5.

Proved via LeanCert interval arithmetic over 1000 prime terms
with manual range reduction and taylorDepth 30.
See `RotorTraceComputation.lean` for the full proof.
-/
theorem rotorTrace_first1000_lt_bound_proven :
    CliffordRH.rotorTrace (1 / 2) 14.134725 (Nat.primesBelow 7920).toList < -5 :=
  RotorTraceComputation.rotorTrace_primesBelow_lt

/-!
## DELETED: rotorTrace_monotone_from_first1000_axiom

**WHY DELETED (2026-01-23)**: This axiom was FALSE.

The trace oscillates due to cosine terms: T(σ,t) = Σ log(p)·p^{-σ}·cos(t·log p).
The cosine phases are incommensurable, so the sum behaves like a random walk,
NOT monotonically. Adding more primes can increase OR decrease the trace.

**Correct approach**: Use the Explicit Formula axioms (Category 3) which properly
handle the oscillating tail via error bounds, not monotonicity claims.

See also: TraceAtFirstZero.lean where `trace_monotone_from_large_set` was
similarly deleted for the same reason.
-/

end ProofEngine
