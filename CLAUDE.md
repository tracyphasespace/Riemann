# Claude Code Instructions for Riemann/Lean Project

## Table of Contents

1. [Quick Start](#quick-start)
2. [Mandatory Workflow](#mandatory-plan-first-workflow)
3. [Project Overview](#project-overview)
4. [Proof Architecture](#proof-architecture)
5. [Real vs Complex Architecture](#real-vs-complex-architecture)
6. [Cl(3,3) Geometric Framework](#the-cl33-geometric-framework)
7. [Mathlib 4.27 API Reference](#mathlib-4-api-reference-critical)
8. [Mathlib 4.27 API Patterns](#mathlib-427-api-patterns)
9. [Taylor's Theorem & Calculus API](#taylors-theorem--calculus-api)
10. [Proof Search Tactics](#proof-search-tactics-lean-427)
11. [Sorry Verification Protocol](#sorry-verification-protocol-critical)
12. [Using Aristotle](#using-aristotle-harmonics-lean-424-agent)

---

## Quick Start

```bash
# Verify the proof
cd /home/tracy/development/Riemann/Lean
lake build

# Check for running builds FIRST (prevents OOM)
pgrep -x lake || echo "No lake process running"
```

**Current status, build locks, and coordination**: See `llm_input/Communications.md`

---

## Mandatory Plan-First Workflow

**THE #1 CAUSE OF WASTED TIME**: Jumping into proofs without planning.

**SYMPTOMS OF THRASHING**:
- Trying random tactics hoping something works
- Deleting and rewriting the same proof multiple times
- Guessing Mathlib API names that don't exist
- Writing 50+ line proofs that fail on line 3

### STEP 0: PLAN FIRST (REQUIRED)

Before touching ANY .lean file:

1. **State the goal in plain English**
2. **Ask: Is this theorem mathematically TRUE?** (We wasted days on false theorems)
3. **Search Mathlib FIRST**:
   - Loogle: `https://loogle.lean-lang.org/?q=<type signature>`
   - Local grep: `grep -rn "lemma_name" .lake/packages/mathlib/`
4. **Decompose into atomic lemmas** (1-3 lines each, ONE Mathlib lemma per helper)
5. **Write a table BEFORE coding**:

| Helper Lemma | Mathlib API | Signature | Status |
|--------------|-------------|-----------|--------|
| `log_sum_ne_zero` | `add_pos`, `Real.log_pos` | `1 < p → 1 < q → log p + log q ≠ 0` | TODO |

### STEP 1: SEARCH (Before Writing Anything)

```lean
-- TRY THESE FIRST (in order):
example : goal := by exact?   -- Often finds the exact lemma
example : goal := by apply?   -- Suggests applicable lemmas
example : goal := by aesop    -- For logic/sets/basic algebra
example : goal := by simp?    -- Shows what simp would use
```

### STEP 2: WRITE ATOMIC HELPERS

**Each helper lemma must be:**
- 1-3 lines maximum
- Use exactly ONE main Mathlib lemma
- Have a clear type signature

```lean
-- GOOD: Atomic, uses one lemma
private lemma log_sum_ne_zero {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    Real.log p + Real.log q ≠ 0 :=
  ne_of_gt (add_pos (Real.log_pos (by exact_mod_cast hp)) (Real.log_pos (by exact_mod_cast hq)))

-- BAD: Monolithic, impossible to debug
theorem big_theorem := by
  [50 lines of tactics that fail somewhere in the middle]
```

### STEP 3: VERIFY

```lean
#print axioms MyTheorem  -- Must NOT show sorryAx
```

### STEP 4: IF STUCK - STOP AND DOCUMENT

```lean
theorem stuck_theorem : goal := by
  -- TRIED: exact Foo.bar (2026-01-23)
  -- FAILED: type mismatch, expected ℤ got ℕ
  -- TRIED: apply?
  -- FAILED: no applicable lemmas
  -- BLOCKER: Need Mathlib lemma for X, doesn't exist in 4.27
  sorry
```

**Then move on.** Don't spend hours on one sorry.

---

## Project Overview

This is a Lean 4 formalization of the Riemann Hypothesis using the CliffordRH Cl(3,3) rotor dynamics approach.

- **Lean Version**: 4.27.0-rc1
- **Mathlib**: v4.27.0-rc1
- **Build command**: `lake build`

### The Master Key: ProofEngine.lean

The main theorem `Clifford_RH_Derived` in `ProofEngine.lean` combines all modules:

```lean
theorem Clifford_RH_Derived (s : ℂ) (h_zero : riemannZeta s = 0)
    (h_strip : 0 < s.re ∧ s.re < 1)
    (h_simple : deriv riemannZeta s ≠ 0)
    (primes : List ℕ)
    (h_large : primes.length > 1000)
    (h_primes : ∀ p ∈ primes, 0 < (p : ℝ))
    (h_approx : AdmissiblePrimeApproximation s primes)
    (h_convex : EnergyIsConvexAtHalf s.im)
    (h_C2 : ContDiff ℝ 2 (ZetaEnergy s.im))
    (h_norm_min : NormStrictMinAtHalf s.im primes)
    (h_zero_norm : ZeroHasMinNorm s.re s.im primes) :
    s.re = 1 / 2
```

---

## Proof Architecture

```
                    Clifford_RH_Derived
                           │
        ┌──────────────────┼──────────────────┐
        │                  │                  │
        ▼                  ▼                  ▼
  derived_monotonicity  derived_energy_min  zero_implies_norm_min
        │                  │                  │
        ▼                  ▼                  ▼
  PhaseClustering     EnergySymmetry    (Approximation)
        │                  │
        ▼                  ▼
  Pole of ζ'/ζ        Functional Eq.
  (Hadamard)          ξ(s) = ξ(1-s)
```

### Key Theorem Locations

| Theorem | File |
|---------|------|
| `Clifford_RH_Derived` | ProofEngine.lean |
| `derived_monotonicity` | ProofEngine.lean |
| `derived_energy_min` | ProofEngine.lean |
| `Classical_RH_CliffordRH` | ZetaLinkClifford.lean |
| `convexity_implies_norm_strict_min` | EnergySymmetry.lean |

---

## Real vs Complex Architecture

**IMPORTANT**: The CliffordRH Cl(3,3) framework is purely REAL. Complex values appear only in "bridge" modules connecting standard zeta function theory to CliffordRH.

### Layer 1: Pure Real Cl(3,3) (No Complex)
```
CliffordRH.lean         - rotorTrace, rotorSumNormSq : ℝ → ℝ → List ℕ → ℝ
TraceMonotonicity.lean  - Real analysis on traces (derivatives, monotonicity)
```

### Layer 2: Bridge (Uses ℂ to connect to zeta)
```
ZetaLinkClifford.lean   - Takes s : ℂ, extracts s.re and s.im for CliffordRH
```

### Layer 3: Complex Analysis (Derives bridge properties)
```
PhaseClustering.lean    - Pole structure of ζ'/ζ (complex analysis)
Convexity.lean          - Energy convexity via completedRiemannZeta₀
EnergySymmetry.lean     - Functional equation ξ(s) = ξ(1-s)
Residues.lean           - Horizontal approach: pole dominates as σ → ρ⁺
```

---

## The Cl(3,3) Geometric Framework

| Complex RH Language        | CliffordRH Language              |
|----------------------------|----------------------------------|
| ζ(s) = 0                   | Rotor Phase-Locking              |
| Pole at s = 1              | Bivector Torque Source           |
| Logarithmic Derivative     | Rotor Force Field                |
| Monotonicity of ζ'/ζ       | Geometric Gradient (Trace ↑)     |
| Critical Line σ = 1/2      | Energy Equilibrium of Rotor Norm |

### Key Definitions (CliffordRH.lean)

```lean
-- The Scalar Projection of the Rotor Force Field (the "Force")
def rotorTrace (σ t : ℝ) (primes : List ℕ) : ℝ :=
  2 * primes.foldl (fun acc p =>
    acc + Real.log p * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p)) 0

-- The Chiral Rotor Sum Norm Squared (the "Energy")
def rotorSumNormSq (σ t : ℝ) (primes : List ℕ) : ℝ :=
  let sum_cos := primes.foldl (fun acc p => acc + (p : ℝ)^(-σ) * Real.cos (t * Real.log p)) 0
  let sum_sin := primes.foldl (fun acc p => acc + (p : ℝ)^(-σ) * Real.sin (t * Real.log p)) 0
  sum_cos ^ 2 + sum_sin ^ 2
```

### Cl(3,3) Proof Toolbox

**Tool 1: Topological Pole Limit**
```lean
Tendsto (fun σ => (σ - ρ.re)⁻¹) (𝓝[>] ρ.re) atTop
-- Method: Compose tendsto_inv_nhdsGT_zero with translation
```

**Tool 2: Complex → Real Reduction**
```lean
((σ : ℂ) + ρ.im * I - ρ)⁻¹.re = (σ - ρ.re)⁻¹
-- Method: Prove s - ρ is purely real when s.im = ρ.im via Complex.ext
```

**Tool 3: Symmetry Derivative**
```lean
f(x) = f(1-x) ⟹ f'(1/2) = 0
-- Method: Chain rule gives f'(x) = -f'(1-x), so at x=1/2: linarith
```

**Tool 4: Strict Monotonicity**
```lean
(∀ x ∈ (a,b), f'(x) > 0) ⟹ StrictMonoOn f (a,b)
-- Method: Apply strictMonoOn_of_deriv_pos
```

**Tool 5: Domination Inequality**
```lean
Analytic > M ∧ |Finite + Analytic| < E ∧ M > E ⟹ Finite < 0
-- Method: linarith
```

---

## Mathlib 4 API Reference (CRITICAL)

### Complex Norms
```lean
-- Use ‖·‖ (norm), NOT Complex.abs
-- ‖(p:ℂ)^(-s)‖ = p^(-s.re) for p > 0
Complex.norm_cpow_eq_rpow_re_of_pos
```

### Limit Theorems
```lean
tendsto_inv_nhdsGT_zero : Tendsto (·⁻¹) (𝓝[>] 0) atTop  -- 1/x → +∞ as x → 0⁺
tendsto_neg_atTop_atBot : Tendsto (-·) atTop atBot       -- -y → -∞ as y → +∞
tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within  -- Restrict to nhdsWithin
```

### Filter Pattern (for nhdsWithin proofs)
```lean
filter_upwards [self_mem_nhdsWithin] with σ hσ
simp only [Set.mem_Ioi] at hσ ⊢
linarith
```

### Continuity
```lean
continuous_sub_right x₀  -- σ ↦ σ - x₀ is continuous
```

### Summability
```lean
Real.summable_nat_rpow              -- Σ n^(-x) converges iff x > 1
Summable.of_nonneg_of_le            -- Comparison test
Summable.of_norm_bounded_eventually -- Eventually bounded comparison
```

### Asymptotics
```lean
isLittleO_log_rpow_atTop : (hr : 0 < r) → log =o[atTop] (·^r)  -- log(x) = o(x^r)
IsLittleO.bound : (f =o[l] g) → (0 < c) → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖
```

---

## Mathlib 4.27 API Patterns

### Finset Products
```lean
-- WRONG: Finset.prod_ne_zero does not exist
-- RIGHT: Use Finset.prod_pos + Nat.pos_iff_ne_zero
private lemma prod_prime_pow_ne_zero {S : Finset ℕ} (h_primes : ∀ p ∈ S, Nat.Prime p)
    (e : ℕ → ℕ) : S.prod (fun p => p ^ e p) ≠ 0 := by
  have h_pos : 0 < S.prod (fun p => p ^ e p) := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (h_primes p hp).pos (e p)
  exact Nat.pos_iff_ne_zero.mp h_pos
```

### Power Positivity
```lean
-- WRONG: Nat.pos_pow_of_pos does not exist
-- RIGHT: Use pow_pos directly
pow_pos (h_primes p hp).pos (e p)  -- Works for any ordered semiring
```

### Prime Factorization
```lean
-- (p^e).factorization p = e
private lemma prime_pow_factorization_self {p e : ℕ} (hp : p.Prime) :
    (p ^ e).factorization p = e := by
  rw [hp.factorization_pow, Finsupp.single_eq_same]

-- (q^e).factorization p = 0 for p ≠ q
private lemma prime_pow_factorization_other {p q e : ℕ} (hq : q.Prime) (hne : p ≠ q) :
    (q ^ e).factorization p = 0 := by
  rw [hq.factorization_pow, Finsupp.single_eq_of_ne hne]
```

### Asymptotic API (IsBigO / Tendsto)
```lean
-- IMPORTANT: IsBigO uses norms internally
-- WRONG: IsBigO l (fun x => |f x|) g
-- RIGHT: IsBigO l f g  -- norms handled internally

-- Key lemmas:
tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) : Tendsto (·^y) atTop atTop
isBigO_iff : f =O[l] g ↔ ∃ C, ∀ᶠ x in l, ‖f x‖ ≤ C * ‖g x‖
tendsto_atTop_mono' : (∀ᶠ x in l, f x ≤ g x) → Tendsto g l atTop → Tendsto f l atTop
```

### Dependency Cycle Resolution
```lean
-- WRONG: File A imports File B, File B imports File A
-- RIGHT: Extract shared lemmas to Common/ shim file
-- Example: Use Riemann/Common/Mathlib427Compat.lean for shared utilities
```

### Sum Splitting (Three-Way Partition)
```lean
-- Split sum into positive, negative, zero parts using filter
have h1 := Finset.sum_filter_add_sum_filter_not s (fun p => 0 < z p) f
have h2 : s.filter (¬(0 < z ·)) = s.filter (z · < 0) ∪ s.filter (z · = 0) := by
  ext p; simp [not_lt]; constructor <;> (intro; cases' ‹_›.lt_or_eq with h h <;> simp [*])
have h_disj : Disjoint (s.filter (z · < 0)) (s.filter (z · = 0)) := by
  rw [Finset.disjoint_filter]; intro p _ hz_neg hz_eq; linarith
rw [h2, Finset.sum_union h_disj]
```

### Complex Derivative Patterns
```lean
-- Derivative of star/conj composition
theorem deriv_star_comp {f : ℝ → ℂ} (x : ℝ) (hf : DifferentiableAt ℝ f x) :
    deriv (star ∘ f) x = star (deriv f x) := hf.hasDerivAt.star.deriv

-- For norm squared: d/dx ‖f(x)‖² = 2 * Re(f'(x) * conj(f(x)))
have h := hf.hasDerivAt.norm_sq
rw [h.deriv, inner_eq_re_mul_conj]
```

### Unique Factorization for Disjoint Prime Products
```lean
-- If ∏_{S} p^{e(p)} = ∏_{T} q^{f(q)} over disjoint primes S, T, then all exponents = 0
lemma disjoint_exp_zero {S T : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    (h_disj : Disjoint S T) (e f : ℕ → ℕ)
    (h_eq : S.prod (fun p => p ^ e p) = T.prod (fun p => p ^ f p))
    (q : ℕ) (hq : q ∈ S) : e q = 0 := by
  -- Use factorization comparison
  have h1 := factorization_prod_prime_pow' hS e q; rw [if_pos hq] at h1
  have h2 := factorization_prod_prime_pow' hT f q
  simp only [Finset.disjoint_left.mp h_disj hq, ↓reduceIte] at h2
  rw [h_eq] at h1; linarith
```

---

## Taylor's Theorem & Calculus API

### Taylor's Theorem with Lagrange Remainder
```lean
-- USE THIS (weaker requirements):
taylor_mean_remainder_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
    (hx : x₀ < x)
    (hf : ContDiffOn ℝ n f (Icc x₀ x))  -- NOTE: n, not n+1!
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) :
    ∃ x' ∈ Ioo x₀ x, f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)!

-- NOT THIS (requires n+1 smoothness):
taylor_mean_remainder_lagrange_iteratedDeriv
```

### Building ContDiff from Differentiable
```lean
contDiff_one_iff_deriv : ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous (deriv f)

-- Usage:
have h : ContDiff ℝ 1 f := contDiff_one_iff_deriv.mpr ⟨hf, hf'.continuous⟩
```

### derivWithin ↔ deriv Conversion
```lean
DifferentiableAt.derivWithin : DifferentiableAt 𝕜 f x → UniqueDiffWithinAt 𝕜 s x →
    derivWithin f s x = deriv f x

uniqueDiffOn_Icc {a b : ℝ} (hab : a < b) : UniqueDiffOn ℝ (Icc a b)
```

### iteratedDerivWithin Patterns
```lean
-- WRONG: iteratedDeriv_two does not exist!
-- RIGHT: Use simp with succ/zero:
simp only [iteratedDeriv_succ, iteratedDeriv_zero]  -- gives deriv (deriv f)

-- Expand iteratedDerivWithin 2:
rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ, iteratedDerivWithin_one]
```

### Derivative Composition (from Deriv.Shift)
```lean
-- IMPORT: Mathlib.Analysis.Calculus.Deriv.Shift
deriv_comp_const_sub : deriv (fun x => f (a - x)) x = -deriv f (a - x)
deriv.neg : deriv (-f) x = -deriv f x
```

---

## Proof Search Tactics (Lean 4.27)

### Priority Order
1. `exact?` / `apply?` - fastest, often instant solution
2. `aesop` - good for logic, set theory, basic algebra
3. `simp` with explicit lemmas - when you know the direction
4. Manual proof - only after automation fails

### `exact?` - Find exact lemma match
```lean
example : 2 + 3 = 5 := by exact?  -- Finds: exact rfl
example : a + b = b + a := by exact?  -- Finds: exact add_comm a b
```

### `apply?` - Find applicable lemmas
```lean
example (h : 0 < x) : 0 < x^2 := by apply?  -- Suggests: apply sq_pos_of_pos h
```

### `aesop` - Automated proof search
```lean
-- Logic and basic algebra
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by aesop

-- Set theory
example (h : x ∈ A ∩ B) : x ∈ A := by aesop

-- Use aesop? to generate proof script for faster compilation
```

### `rw?` - Find rewrite lemmas
```lean
example : (a + b) + c = a + (b + c) := by rw?  -- Suggests: rw [add_assoc]
```

---

## Sorry Verification Protocol (CRITICAL)

### Step 1: Check the theorem
```lean
#print axioms MyTheorem
```
- If `sorryAx` appears → proof is INCOMPLETE
- If only `propext`, `Classical.choice`, `Quot.sound` → proof is COMPLETE

### Step 2: Check upstream dependencies
```lean
-- If MyTheorem uses HelperLemma, also check:
#print axioms HelperLemma
```

### Step 3: Force evaluation (optional)
```lean
#eval! myComputableDef  -- Forces runtime check
#guard_msgs in #check myTheorem  -- Verify no warnings
```

---

## Using Aristotle (Harmonic's Lean 4.24 Agent)

**Workflow**: Send Lean files to Aristotle for proof attempts. Aristotle runs on Lean 4.24/Mathlib, while this project uses Lean 4.27.

### Process:
1. **Send** a file or lemma with clear task description
2. **Review** output - Aristotle marks what was proved vs failed
3. **Extract** useful snippets (proofs, strategies, counterexamples)
4. **Adapt** for Lean 4.27 API differences
5. **Integrate** as working proofs or documented strategies

### Common 4.24 → 4.27 Adaptations:
- `exact?` → replace with actual lemma reference
- `simp_all +decide` → may need explicit simp lemmas
- `grind` tactic → use `nlinarith` or `omega`
- List API differences (foldl, reverseRecOn patterns)

---

## Lessons Learned

### What Causes Churn
- **Guessing APIs**: Trying `Finset.prod_ne_zero` when it doesn't exist
- **Skipping planning**: Jumping into proofs without decomposing
- **Ignoring type coercions**: foldl on `List ℕ` but uses `(p : ℝ)` inside
- **Proving impossible theorems**: Check mathematical truth FIRST

### What Works
- **Atomic lemma decomposition**: Break into 1-3 line helpers
- **Loogle/exact? first**: Search before writing manual proofs
- **Compatibility shim**: Use `Riemann/Common/Mathlib427Compat.lean`
- **Check mathematical correctness**: Is the theorem even TRUE?

### The Golden Rule
**PLAN BEFORE LEAN**: Create a written plan with atomic lemmas BEFORE touching any .lean file.

---

*Updated 2026-01-23 | Status & coordination: see llm_input/Communications.md*
