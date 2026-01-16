import Riemann.ZetaSurface.DirichletTermProof
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic

open Complex
open Riemann.ZetaSurface.DirichletTermProof
open Riemann.ZetaSurface.GeometricZeta

noncomputable section

/-!
# Test: Dirichlet Term Bridge to Clifford Algebra
This test checks that the real and imaginary parts of complex powers
match the scalar and bivector parts of the real Clifford algebra expression.
-/

-- Spectral parameter encoding
example : spectralParam 2 3 = ⟨2, 3⟩ := rfl

-- Clifford decomposition: test scalar and bivector parts separately
example : (cliffordPower 5 2 3).1 = (5 : ℝ) ^ (-(2:ℝ)) * Real.cos (3 * Real.log 5) := rfl
example : (cliffordPower 5 2 3).2 = -(5 : ℝ) ^ (-(2:ℝ)) * Real.sin (3 * Real.log 5) := rfl

-- Matches GeometricZeta components
example : (cliffordPower 5 2 3).1 = ScalarTerm 5 2 3 := rfl
example : (cliffordPower 5 2 3).2 = BivectorTerm 5 2 3 := rfl

-- Complex version matches real-Clifford version (via theorems)
example : ((5 : ℂ) ^ (-spectralParam 2 3)).re = ScalarTerm 5 2 3 :=
  dirichlet_term_re 5 (by norm_num) 2 3

example : ((5 : ℂ) ^ (-spectralParam 2 3)).im = BivectorTerm 5 2 3 :=
  dirichlet_term_im 5 (by norm_num) 2 3

-- This confirms the Cl(N,N) ↔ ℂ bridge works for actual numeric values.

end
