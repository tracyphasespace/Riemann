/-
# Test: Manual range reduction using Expr.pi

Key insight: cosComputableReduced uses crude π bounds (6 digits) for range reduction,
causing O(0.003) width per period shift. By doing range reduction in the Expr itself
using Expr.pi (16-digit piInterval), we get O(1e-16) width per period shift.
-/
import LeanCert

open LeanCert.Core LeanCert.Validity LeanCert.Engine

-- One rotorTrace term with manual range reduction
-- cos(t*log(p)) = sign * cos(t*log(p) - k*π) where reduced arg ∈ [0, π]
def mkRotorTermReduced (p : ℚ) (k : ℤ) (negSign : Bool) : Expr :=
  let cosArg := .add (.mul (.const (565389/40000)) (.log (.const p)))
                     (.neg (.mul (.const k) .pi))
  let cosTerm := .cos cosArg
  let signedCos := if negSign then .neg cosTerm else cosTerm
  .mul (.mul (.log (.const p))
             (.exp (.neg (.mul (.log (.const p)) (.const (1/2))))))
       signedCos

-- Per-term interval with manual reduction
def termIntervalReduced (p : ℕ) (k : ℤ) (negSign : Bool) (cfg : EvalConfig) : IntervalRat :=
  evalIntervalCore1 (mkRotorTermReduced p k negSign) ⟨0, 0, le_refl _⟩ cfg

-- Cumulative check with manual reduction
-- Each (p, k, negSign) triple from Python computation
def rotorTraceCheckReduced
    (terms : List (ℕ × ℤ × Bool)) (bound : ℚ) (cfg : EvalConfig) : Bool :=
  let hiSum := terms.foldl (fun acc (p, k, neg) =>
    acc + (termIntervalReduced p k neg cfg).hi) (0 : ℚ)
  decide (2 * hiSum < bound)

-- Test data: first 10 primes with their k and sign values
def test10terms : List (ℕ × ℤ × Bool) := [
  (2, 3, true),     -- sign=-1 → negSign=true
  (3, 4, false),    -- sign=+1
  (5, 7, true),
  (7, 8, false),
  (11, 10, false),
  (13, 11, true),
  (17, 12, false),
  (19, 13, true),
  (23, 14, false),
  (29, 15, true)
]

-- The key test: does the reduced version pass?
#eval rotorTraceCheckReduced test10terms (-7) { taylorDepth := 30 }

-- Diagnostic: what's the actual hiSum?
#eval do
  let cfg : EvalConfig := { taylorDepth := 30 }
  let hiSum := test10terms.foldl (fun acc (p, k, neg) =>
    acc + (termIntervalReduced p k neg cfg).hi) (0 : ℚ)
  let approx := (2 * hiSum).num * 1000000 / (2 * hiSum).den
  IO.println s!"2*hiSum ≈ {approx}/1000000"
  IO.println s!"actual = -7028123/1000000"
