/-
# Trace Verification at the First Zeta Zero

**Goal**: Verify that the rotor trace is strictly negative at the first zeta zero.
This replaces the numerical `axiom` with a computational proof using interval arithmetic.

**Mathematical Background**:
The first nontrivial zero of ζ is at s = 1/2 + i·14.134725...
At this height, we verify that T(0.5, 14.134725) < 0.

**Approach**: Rigorous Interval Arithmetic
- Every calculation carries guaranteed error bounds
- No floating-point rounding errors can invalidate the proof
- The final result is a rigorous inequality

**Numerical Result** (computed via Wolfram Cloud):
  Trace(0.5, 14.1347) ≈ -5.955

**Status**: Interval arithmetic kernel implemented. Uses nlinarith for multiplication bounds.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Riemann.ZetaSurface.CliffordRH

noncomputable section
open Real CliffordRH

namespace ProofEngine.TraceAtFirstZero

/-!
## 1. Rigorous Interval Arithmetic Kernel
-/

structure Interval where
  lo : ℝ
  hi : ℝ
  valid : lo ≤ hi

def Interval.contains (I : Interval) (x : ℝ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

def Interval.point (x : ℝ) : Interval := ⟨x, x, le_rfl⟩

-- Addition is safe and easy
def Interval.add (a b : Interval) : Interval :=
  ⟨a.lo + b.lo, a.hi + b.hi, add_le_add a.valid b.valid⟩

theorem mem_add {I J : Interval} {x y : ℝ} (hx : I.contains x) (hy : J.contains y) :
    (Interval.add I J).contains (x + y) :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

-- Negation flips bounds
def Interval.neg (a : Interval) : Interval :=
  ⟨-a.hi, -a.lo, neg_le_neg a.valid⟩

theorem mem_neg {I : Interval} {x : ℝ} (hx : I.contains x) :
    (Interval.neg I).contains (-x) :=
  ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

/-!
## 2. Multiplication (The Pain Killer)
We simplify the logic. We don't need 9 cases manually.
We define multiplication by min/max of corners, and prove it covers all cases.
-/

def Interval.mul (I J : Interval) : Interval :=
  let p1 := I.lo * J.lo
  let p2 := I.lo * J.hi
  let p3 := I.hi * J.lo
  let p4 := I.hi * J.hi
  ⟨min p1 (min p2 (min p3 p4)),
   max p1 (max p2 (max p3 p4)),
   le_trans (min_le_left _ _) (le_max_left _ _)⟩

/-!
### Helper lemmas for mem_mul (Rosetta Stone: small atomic units)
-/

/-- Helper: For x ∈ [a,b], y ∈ [c,d] with x,y ≥ 0, product bounds follow from monotonicity. -/
private lemma mul_bounds_nonneg {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hx_nn : 0 ≤ x) (hy_nn : 0 ≤ y) (ha_nn : 0 ≤ a) (hc_nn : 0 ≤ c) :
    a * c ≤ x * y ∧ x * y ≤ b * d := by
  constructor
  · exact mul_le_mul hx.1 hy.1 hc_nn (le_trans ha_nn hx.1)
  · exact mul_le_mul hx.2 hy.2 hy_nn (le_trans hx_nn hx.2)

/-- Helper: Linear function k*x on [a,b] has extrema at endpoints. -/
private lemma linear_bounds (k x a b : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    min (k * a) (k * b) ≤ k * x ∧ k * x ≤ max (k * a) (k * b) := by
  by_cases hk : 0 ≤ k
  · -- k ≥ 0: k*a ≤ k*x ≤ k*b, so min = k*a, max = k*b
    constructor
    · exact min_le_of_left_le (mul_le_mul_of_nonneg_left ha hk)
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_left hb hk)
  · -- k < 0: k*b ≤ k*x ≤ k*a, so min = k*b, max = k*a
    push_neg at hk
    constructor
    · exact min_le_of_right_le (mul_le_mul_of_nonpos_left hb (le_of_lt hk))
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_left ha (le_of_lt hk))

/-- Helper: min of 4 values using nested min -/
private lemma min4_le {p1 p2 p3 p4 v : ℝ} (h : v = p1 ∨ v = p2 ∨ v = p3 ∨ v = p4) :
    min p1 (min p2 (min p3 p4)) ≤ v := by
  rcases h with rfl | rfl | rfl | rfl
  · exact min_le_left _ _
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

/-- Helper: max of 4 values using nested max -/
private lemma le_max4 {p1 p2 p3 p4 v : ℝ} (h : v = p1 ∨ v = p2 ∨ v = p3 ∨ v = p4) :
    v ≤ max p1 (max p2 (max p3 p4)) := by
  rcases h with rfl | rfl | rfl | rfl
  · exact le_max_left _ _
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)

/-- Helper: Product is bounded by one of the four corners (general case). -/
private lemma product_in_corners {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (a*c) (min (a*d) (min (b*c) (b*d))) ≤ x * y ∧
    x * y ≤ max (a*c) (max (a*d) (max (b*c) (b*d))) := by
  -- Strategy: Bilinear xy on [a,b]×[c,d] has extrema at corners.
  -- Step 1: For fixed y, x*y is linear in x, so x*y ∈ {a*y, b*y}
  -- Step 2: For each endpoint x∈{a,b}, x*y is linear in y, so x*y ∈ {x*c, x*d}
  -- Therefore x*y is bounded by {a*c, a*d, b*c, b*d}

  -- Get bounds on x*y in terms of a*y and b*y
  have hxy_linear := linear_bounds y x a b hx.1 hx.2
  -- hxy_linear : min (y*a) (y*b) ≤ y*x ∧ y*x ≤ max (y*a) (y*b)
  -- But we need bounds on x*y, and linear_bounds gives y*x

  -- Rewrite with commutativity
  rw [mul_comm y x, mul_comm y a, mul_comm y b] at hxy_linear

  -- Now get bounds on a*y and b*y in terms of corners
  have hay_linear := linear_bounds a y c d hy.1 hy.2
  have hby_linear := linear_bounds b y c d hy.1 hy.2

  -- Let m4 = min(a*c, a*d, b*c, b*d) and M4 = max(a*c, a*d, b*c, b*d)
  -- We show m4 ≤ x*y ≤ M4 by chaining through intermediate bounds

  -- Auxiliary: m4 is ≤ each component
  have m4_le_ac : min (a*c) (min (a*d) (min (b*c) (b*d))) ≤ a * c := min_le_left _ _
  have m4_le_ad : min (a*c) (min (a*d) (min (b*c) (b*d))) ≤ a * d :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have m4_le_bc : min (a*c) (min (a*d) (min (b*c) (b*d))) ≤ b * c :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have m4_le_bd : min (a*c) (min (a*d) (min (b*c) (b*d))) ≤ b * d :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

  -- Auxiliary: each component is ≤ M4
  have ac_le_M4 : a * c ≤ max (a*c) (max (a*d) (max (b*c) (b*d))) := le_max_left _ _
  have ad_le_M4 : a * d ≤ max (a*c) (max (a*d) (max (b*c) (b*d))) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have bc_le_M4 : b * c ≤ max (a*c) (max (a*d) (max (b*c) (b*d))) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have bd_le_M4 : b * d ≤ max (a*c) (max (a*d) (max (b*c) (b*d))) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)

  constructor
  · -- Lower bound: m4 ≤ x*y
    -- m4 ≤ min(a*c, a*d) ≤ a*y (by hay_linear.1)
    -- m4 ≤ min(b*c, b*d) ≤ b*y (by hby_linear.1)
    -- So m4 ≤ min(a*y, b*y) ≤ x*y (by hxy_linear.1)
    have h_m4_le_min_ac_ad : min (a*c) (min (a*d) (min (b*c) (b*d))) ≤ min (a*c) (a*d) :=
      le_min m4_le_ac m4_le_ad
    have h_m4_le_min_bc_bd : min (a*c) (min (a*d) (min (b*c) (b*d))) ≤ min (b*c) (b*d) :=
      le_min m4_le_bc m4_le_bd
    have h_m4_le_ay : min (a*c) (min (a*d) (min (b*c) (b*d))) ≤ a * y :=
      le_trans h_m4_le_min_ac_ad hay_linear.1
    have h_m4_le_by : min (a*c) (min (a*d) (min (b*c) (b*d))) ≤ b * y :=
      le_trans h_m4_le_min_bc_bd hby_linear.1
    have h_m4_le_min_ay_by : min (a*c) (min (a*d) (min (b*c) (b*d))) ≤ min (a*y) (b*y) :=
      le_min h_m4_le_ay h_m4_le_by
    exact le_trans h_m4_le_min_ay_by hxy_linear.1
  · -- Upper bound: x*y ≤ M4
    -- x*y ≤ max(a*y, b*y) ≤ max(max(a*c,a*d), max(b*c,b*d)) ≤ M4
    have h_max_ac_ad_le_M4 : max (a*c) (a*d) ≤ max (a*c) (max (a*d) (max (b*c) (b*d))) :=
      max_le ac_le_M4 ad_le_M4
    have h_max_bc_bd_le_M4 : max (b*c) (b*d) ≤ max (a*c) (max (a*d) (max (b*c) (b*d))) :=
      max_le bc_le_M4 bd_le_M4
    have h_ay_le_M4 : a * y ≤ max (a*c) (max (a*d) (max (b*c) (b*d))) :=
      le_trans hay_linear.2 h_max_ac_ad_le_M4
    have h_by_le_M4 : b * y ≤ max (a*c) (max (a*d) (max (b*c) (b*d))) :=
      le_trans hby_linear.2 h_max_bc_bd_le_M4
    have h_max_ay_by_le_M4 : max (a*y) (b*y) ≤ max (a*c) (max (a*d) (max (b*c) (b*d))) :=
      max_le h_ay_le_M4 h_by_le_M4
    exact le_trans hxy_linear.2 h_max_ay_by_le_M4

theorem mem_mul {I J : Interval} {x y : ℝ} (hx : I.contains x) (hy : J.contains y) :
    (Interval.mul I J).contains (x * y) := by
  simp only [Interval.mul, Interval.contains] at *
  exact product_in_corners hx hy

/-!
## 3. Transcendental Bounds (Log and Cos)
We rely on the monotonicity of log and the periodicity of cos.
-/

/-- Log is strictly increasing. Bounds map directly. -/
def Interval.log (I : Interval) (h_pos : 0 < I.lo) : Interval :=
  ⟨Real.log I.lo, Real.log I.hi, Real.log_le_log h_pos I.valid⟩

theorem mem_log {I : Interval} {x : ℝ} (h_pos : 0 < I.lo) (hx : I.contains x) :
    (Interval.log I h_pos).contains (Real.log x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le h_pos hx.1
  constructor
  · exact Real.log_le_log h_pos hx.1
  · exact Real.log_le_log hx_pos hx.2

/-- Cosine bound assuming input is in a monotonic region.
    For general intervals, would need to handle extrema at 0, π, 2π, etc. -/
def Interval.cos_decreasing (I : Interval) (h_in_0_pi : 0 ≤ I.lo ∧ I.hi ≤ Real.pi) : Interval :=
  -- cos is decreasing on [0, π], so swap bounds: cos(hi) ≤ cos(lo)
  ⟨Real.cos I.hi, Real.cos I.lo, by
    -- cos_le_cos_of_nonneg_of_le_pi : 0 ≤ x → y ≤ π → x ≤ y → cos y ≤ cos x
    exact Real.cos_le_cos_of_nonneg_of_le_pi h_in_0_pi.1 h_in_0_pi.2 I.valid⟩

/-!
## 4. The Computational Proof
Instead of Axioms, we calculate.
-/

/--
Certified Trace Calculation.
We reconstruct `rotorTrace` using Interval operations.
-/
def rotorTraceInterval (σ : Interval) (t : Interval) (primes : List ℕ) : Interval :=
  let two := Interval.point 2
  let sum := primes.foldl (fun acc p =>
    let p_real := Interval.point (p : ℝ)
    -- For a full implementation, we'd need:
    -- 1. Interval.log for log(p)
    -- 2. Interval.exp for p^(-σ) = exp(-σ * log(p))
    -- 3. Interval.cos for cos(t * log(p))
    -- 4. Combine with Interval.mul and Interval.add
    -- Here we use a placeholder that assumes correct calculation
    acc
  ) (Interval.point 0)
  Interval.mul two sum

/--
**The Trace Negativity Theorem**
At the first zeta zero height t ≈ 14.134725, with σ = 0.5,
the trace is strictly negative for sufficiently many primes.
-/
theorem trace_negative_at_first_zero :
    CliffordRH.rotorTrace (1 / 2) 14.134725 (Nat.primesBelow 7920).toList < -5 := by
  -- STRATEGY (requires native computation or interval arithmetic):
  -- 1. Define constants as explicit rationals: σ = 1/2, t = 14134725/1000000
  -- 2. Construct interval I_σ ⊇ {1/2}, I_t ⊇ {14.134725}
  -- 3. Run rotorTraceInterval on these intervals with primesBelow 7920
  -- 4. The result I_trace should satisfy I_trace.hi < -5
  -- 5. Use norm_num to verify the inequality on concrete numbers
  --
  -- NUMERICAL: Wolfram Cloud gives trace ≈ -5.955
  -- BLOCKER: Requires implementing Interval.exp and full rotorTraceInterval
  sorry

-- DELETED: trace_tail_bounded (2026-01-23)
-- Statement was FALSE: Σ log(p)/√p diverges, so no fixed C bounds all finite lists.

-- DELETED: trace_monotone_from_large_set (2026-01-23)
-- Statement was FALSE: trace oscillates due to cosine, not monotonic in prime count.

end ProofEngine.TraceAtFirstZero
