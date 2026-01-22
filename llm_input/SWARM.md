# AI2 Direct Work Guide

**Mode**: DIRECT (no agents - they cause lockups)
**Build System**: Lean 4.27.0-rc1 / Mathlib v4.27.0-rc1
**Current Sorries**: 15

---

## CRITICAL RULES

1. **DO NOT spawn agents** - causes lockups
2. **DO NOT run `lake build`** - AI1 handles builds
3. Work on ONE sorry at a time
4. Document blockers, move to next if stuck
5. Commit progress periodically

---

## Priority Queue

### Ready to attempt:
1. **CalculusAxioms:21** - taylor_second_order (structure done)
2. **EnergySymmetry:263** - local_min (second derivative test)
3. **CalculusAxioms:55** - effective_convex (uses #1)

### Need axioms first:
4. **EnergySymmetry:101,109** - Xi↔Zeta (need completedRiemannZeta₀_eq)
5. **ClusterBound:83,102** - (need c2_stability_transfer helper)

### Lower priority:
6. TraceAtFirstZero:77,143,153
7. EnergySymmetry:305
8. Others (AnalyticAxioms, NumericalAxioms, etc.)

---

## Rosetta Stone: Key Mathlib Lemmas

```lean
-- Taylor expansion
taylor_mean_remainder_lagrange_iteratedDeriv
iteratedDeriv_succ : iteratedDeriv (n+1) f = deriv (iteratedDeriv n f)

-- Strict monotonicity from positive derivative
strictMonoOn_of_deriv_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, 0 < deriv f x) :
    StrictMonoOn f D

-- Symmetry → zero derivative
deriv_comp_const_sub f a x : deriv (fun y => f (a - y)) x = -deriv f (a - x)

-- Pole limits
tendsto_inv_nhdsGT_zero : Tendsto (·⁻¹) (𝓝[>] 0) atTop

-- normSq differentiability (decompose to re² + im²)
Complex.normSq_apply : normSq z = z.re * z.re + z.im * z.im
```

---

## Session History

| Batch | Sorries Before | After | Method |
|-------|----------------|-------|--------|
| 1-5 | 96 | 52 | Agents |
| C-D | 17 | 15 | Agents (lockups) |
| Current | 15 | ? | Direct |

---

*Work directly. No agents. Document blockers.*
