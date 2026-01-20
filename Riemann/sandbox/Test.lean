import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex

example (s : ℂ) : starRingEnd ℂ (riemannZeta s) = riemannZeta (starRingEnd ℂ s) := by
  sorry