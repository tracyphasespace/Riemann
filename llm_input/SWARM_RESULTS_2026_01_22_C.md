# Swarm Results - 2026-01-22 Batch C

## Agent ES-1: riemannXi_zero_iff_zeta_zero - NEEDS_WORK

**STATUS:** NEEDS_WORK
**FILE:** Riemann/ProofEngine/EnergySymmetry.lean
**LINE:** 87 → split into two sorries at lines 101, 109
**AGENT ID:** a81edfd

### Edit Made
Split single sorry into two smaller sorries with documented proof strategy:
- Line 101: `ξ(s) = 0 → ζ(s) = 0` direction
- Line 109: `ζ(s) = 0 → ξ(s) = 0` direction

### Proof Strategy
The relationship: `completedRiemannZeta₀ s = completedRiemannZeta s + 1/s + 1/(1-s)`
And: `completedRiemannZeta s = π^(-s/2) * Γ(s/2) * ζ(s)` (for s ≠ 0, 1)

In the strip (0 < s.re < 1):
- s(1-s) ≠ 0
- π^(-s/2) ≠ 0
- Γ(s/2) ≠ 0 (s/2 not a non-positive integer)

### Blocker
Needs Mathlib API:
- `completedRiemannZeta₀_eq_completedRiemannZeta_add_poles`
- `Complex.Gamma_ne_zero` for the strip
- `Complex.cpow_ne_zero`

### Sources
- [Mathlib.NumberTheory.LSeries.RiemannZeta](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html)

---

## Agent ES-2: energy_deriv_zero_at_half - NEEDS_WORK

**STATUS:** NEEDS_WORK
**FILE:** Riemann/ProofEngine/EnergySymmetry.lean
**LINE:** 193
**AGENT ID:** aee7b89

### Edit Made
None - file conflict prevented edit (other agents modifying same file)

### Proof Ready (not applied)
```lean
theorem energy_deriv_zero_at_half (t : ℝ) :
    deriv (fun σ => ZetaEnergy t σ) (1/2) = 0 := by
  apply deriv_zero_of_symmetric
  · -- Differentiability of ZetaEnergy
    have h_line : Differentiable ℝ (fun σ : ℝ => (σ : ℂ) + t * I) := by
      apply Differentiable.add
      · exact Complex.ofRealCLM.differentiable
      · exact differentiable_const _
    have h_xi : Differentiable ℂ riemannXi := by
      unfold riemannXi
      apply Differentiable.sub
      · apply Differentiable.mul
        · apply Differentiable.mul
          · exact differentiable_id
          · exact differentiable_const 1 |>.sub differentiable_id
        · exact differentiable_completedRiemannZeta₀
      · exact differentiable_const _
    have h_comp : Differentiable ℝ (fun σ : ℝ => riemannXi ((σ : ℂ) + t * I)) :=
      (h_xi.restrictScalars ℝ).comp h_line
    have h_re : Differentiable ℝ (fun σ => (riemannXi ((σ : ℂ) + t * I)).re) :=
      Complex.reCLM.differentiable.comp h_comp
    have h_im : Differentiable ℝ (fun σ => (riemannXi ((σ : ℂ) + t * I)).im) :=
      Complex.imCLM.differentiable.comp h_comp
    have h_eq : (fun σ => ZetaEnergy t σ) = (fun σ => (riemannXi ((σ : ℂ) + t * I)).re ^ 2 +
        (riemannXi ((σ : ℂ) + t * I)).im ^ 2) := by
      ext σ; simp only [ZetaEnergy, Complex.normSq_apply]
    rw [h_eq]
    exact (h_re.pow 2).add (h_im.pow 2)
  · intro σ; exact zeta_energy_symmetric t σ
```

### Blocker
File conflict - multiple agents editing EnergySymmetry.lean simultaneously

---

## Agent ES-3: symmetry_and_convexity_imply_local_min - NEEDS_WORK

**STATUS:** NEEDS_WORK
**FILE:** Riemann/ProofEngine/EnergySymmetry.lean
**LINE:** 223 → 243
**AGENT ID:** a3e4156

### Edit Made
Restructured proof with cleaner documentation:
- Added `use 1/4` for δ with `norm_num`
- Documented second derivative test argument
- Added detailed MVT explanation

### Blocker
Requires C² differentiability of `ZetaEnergy`, which depends on:
1. Line 193: `energy_deriv_zero_at_half` has sorry for differentiability
2. Composition `normSq ∘ riemannXi ∘ (σ ↦ σ + t*I)` needs to be shown C²

---

## Agent CA-1: taylor_case_2/3 - NEEDS_WORK

**STATUS:** NEEDS_WORK
**FILE:** Riemann/ProofEngine/CalculusAxioms.lean
**LINE:** 63 (taylor_second_order lemma) → sorry at line 128
**AGENT ID:** a7ae90f

### Edit Made
Added detailed documentation in Case 3 (x < x₀) explaining:
- Reflection argument: define `g(y) = f(x₀ - y + x)`
- Transform Taylor expansion from left endpoint to right endpoint
- Mathematical proof strategy

### Blocker
1. **Primary:** `contDiff_two_of_differentiable_deriv` at line 28 has sorry
   - Statement too weak: needs continuity of second derivative, not just differentiability
2. **Secondary:** Mathlib's Taylor only expands at left endpoint

### Proof Strategy
Define `g(y) = f(x₀ - y + x)` on `[0, x₀ - x]`:
- `g(0) = f(x₀)`, `g(x₀ - x) = f(x)`
- `g'(y) = -f'(x₀ - y + x)`, `g''(y) = f''(x₀ - y + x)`
- Apply Taylor, transform back to get `f(x)` expanded at `x₀`

---

## Agent AA-1: finite_sum_approx_analytic_proven - NEEDS_WORK

**STATUS:** NEEDS_WORK
**FILE:** Riemann/ProofEngine/AnalyticAxioms.lean
**LINE:** 320 (sorry at 336)
**AGENT ID:** ae48185

### Edit Made
Added detailed documentation explaining the mathematical content and why this theorem requires the Explicit Formula infrastructure.

### Mathematical Content
The theorem requires von Mangoldt's Explicit Formula:
```
-ζ'/ζ(s) = Σ_ρ 1/(s-ρ) + Σ_p log(p)·p^{-s} + (regular terms)
```
Differentiating gives:
```
d/ds(-ζ'/ζ) = -Σ_ρ 1/(s-ρ)² + Σ_p log²(p)·p^{-s} + ...
```
The finite sum approximates the prime contribution with bounded error.

### Blocker
Requires deep analytic number theory not in Mathlib:
1. Contour integration infrastructure
2. Zero-sum formulas for Riemann zeta function
3. Truncation error analysis for prime sums

This is one of the 2 remaining axioms (`ax_finite_sum_approx_analytic`).

---

*Generated by AI2 Swarm Coordinator - Batch C*
