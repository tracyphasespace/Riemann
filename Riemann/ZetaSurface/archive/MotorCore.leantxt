/-
MotorCore.lean

Encapsulates the "5-point Motor Proof" mechanics in Lean using standard block-diagonal
linear algebra. This is the right abstraction boundary for:
  (i) orthogonal prime planes,
 (ii) commuting prime generators (no BCH residue),
(iii) projection artifacts (interference only after collapsing dimensions),
 (iv) blade/eigenvector reduction (global operator diagonalizes by coordinates).

This file is intentionally written for a FINITE index type `ι` (truncate primes) so it
stays purely algebraic and avoids ℓ² / topology. You can later swap `H := ι → Plane`
for an `ℓ²` space once the core algebra is stable.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace MotorProof

section Core

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A replaceable 2-plane model for a single prime sector. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Global state space: one 2-plane per prime (truncate by `ι`). -/
abbrev H (ι : Type) [Fintype ι] := ι → Plane

/-- A "basis blade": put a vector `v` in coordinate `i`, zero elsewhere. -/
def blade (i : ι) (v : Plane) : H ι := Pi.single i v

@[simp] lemma blade_same (i : ι) (v : Plane) : blade i v i = v := by
  simp [blade]

@[simp] lemma blade_ne {i j : ι} (h : j ≠ i) (v : Plane) : blade i v j = 0 := by
  simp [blade, Pi.single_eq_of_ne h]

/-- Coordinate projection as a linear map (evaluation at `i`). -/
def coord (i : ι) : H ι →ₗ[ℝ] Plane :=
{ toFun := fun x => x i
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl }

@[simp] lemma coord_apply (i : ι) (x : H ι) : coord i x = x i := rfl

/--
Localize an operator to a single coordinate; all other coordinates are fixed.
This is the precise linear-algebra avatar of "prime generators act in disjoint planes".
-/
def actOn (i : ι) (A : Plane →ₗ[ℝ] Plane) : H ι →ₗ[ℝ] H ι :=
{ toFun := fun x j => if j = i then A (x j) else x j
  map_add' := by
    intro x y; ext j
    by_cases h : j = i
    · subst h; simp [LinearMap.map_add]
    · simp [h]
  map_smul' := by
    intro a x; ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h] }

@[simp] lemma actOn_apply (i : ι) (A : Plane →ₗ[ℝ] Plane) (x : H ι) (j : ι) :
    actOn i A x j = if j = i then A (x j) else x j := rfl

/-- `actOn` affects only the chosen coordinate. -/
lemma actOn_eq_self_of_ne {i j : ι} (h : j ≠ i) (A : Plane →ₗ[ℝ] Plane) (x : H ι) :
    actOn i A x j = x j := by simp [h]

/-- `actOn` transports a blade within the same coordinate. (Eigenvector reduction core.) -/
lemma actOn_blade_same (i : ι) (A : Plane →ₗ[ℝ] Plane) (v : Plane) :
    actOn i A (blade i v) = blade i (A v) := by
  ext j
  by_cases h : j = i
  · subst h; simp [blade]
  · simp [blade, h]

/-- `actOn` leaves blades in other coordinates unchanged. -/
lemma actOn_blade_ne {i j : ι} (hij : j ≠ i) (A : Plane →ₗ[ℝ] Plane) (v : Plane) :
    actOn i A (blade j v) = blade j v := by
  ext k
  by_cases hk : k = i
  · subst hk
    -- coordinate `i` of `blade j v` is zero since `j ≠ i`
    simp [blade, hij]
  · simp [hk]

/--
Prime blocks commute: operators acting on distinct coordinates commute.
This is the Lean form of "orthogonal bivectors commute" / "BCH residue is exactly zero".
-/
theorem actOn_comm {i j : ι} (hij : i ≠ j)
    (A B : Plane →ₗ[ℝ] Plane) :
    (actOn i A).comp (actOn j B) = (actOn j B).comp (actOn i A) := by
  apply LinearMap.ext; intro x
  funext k
  simp only [LinearMap.comp_apply, actOn_apply]
  by_cases hk_i : k = i <;> by_cases hk_j : k = j
  · -- k = i and k = j is impossible since i ≠ j
    exfalso; exact hij (hk_i.symm.trans hk_j)
  · -- k = i, k ≠ j: LHS = A (x i), RHS = A (x i)
    subst hk_i
    simp only [if_true, if_neg hk_j]
  · -- k ≠ i, k = j: LHS = B (x j), RHS = B (x j)
    subst hk_j
    simp only [if_neg hk_i, if_true]
  · -- k ≠ i, k ≠ j: both sides are x k
    simp only [if_neg hk_i, if_neg hk_j]

/--
Scalar projection that *collapses* the orthogonal frame: this is where "interference"
is reintroduced (projection artifact).
-/
def projSum : H ι →ₗ[ℝ] Plane :=
∑ i : ι, coord (ι := ι) i

@[simp] lemma projSum_apply (x : H ι) :
    projSum x = ∑ i : ι, x i := by
  simp [projSum, coord, LinearMap.coe_sum, Finset.sum_apply]

/-- Projection of a single blade recovers its payload. -/
lemma projSum_blade (i : ι) (v : Plane) :
    projSum (blade i v) = v := by
  simp only [projSum_apply, blade]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hj
    simp [Pi.single_eq_of_ne hj]

/--
Projection removes orthogonality: two distinct blades can cancel after projection.
This is your "interference exists only after smashing dimensions" statement.
-/
theorem projection_cancellation {i j : ι} (_hij : i ≠ j) (v : Plane) :
    projSum (blade i v + blade j (-v)) = 0 := by
  simp only [map_add, projSum_blade, add_neg_cancel]

/--
In the lifted space `H`, the same two-blade vector cannot be zero unless `v = 0`.
This is the "no cancellation in orthogonal coordinates" rigidity.
-/
theorem lifted_no_cancellation {i j : ι} (hij : i ≠ j) {v : Plane} (hv : v ≠ 0) :
    (blade i v + blade j (-v) : H ι) ≠ 0 := by
  intro h
  have hi : (blade i v + blade j (-v)) i = 0 := by rw [h]; rfl
  -- At coordinate i, the j-term is zero (since j ≠ i), so this forces v = 0
  simp only [Pi.add_apply, blade_same, blade_ne hij, add_zero] at hi
  exact hv hi

end Core

/-!
## Motor Interface Layer

Plug in your actual GA "motor = dilation ∘ rotor" blocks.

This is where you encode:
  * time-like rotation (isometric rotor in the prime's time plane),
  * space-like dilation (the σ-dependent weight),
  * and then reuse `actOn_comm` etc. to eliminate BCH/interaction terms in Lean.
-/
section MotorInterface

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable (rot : ι → ℝ → Plane ≃ₗᵢ[ℝ] Plane)  -- time-like rotor (isometry)
variable (w : ℝ → ι → ℝ)                     -- σ-dependent dilation weight

/-- One prime motor block: dilation `w σ i` followed by rotor `rot i t`. -/
def motorBlock (σ t : ℝ) (i : ι) : Plane →ₗ[ℝ] Plane :=
(w σ i) • (rot i t).toLinearMap

/-- Localize the prime motor to its coordinate in the global space. -/
def motorOn (σ t : ℝ) (i : ι) : H ι →ₗ[ℝ] H ι :=
actOn i (motorBlock rot w σ t i)

/-- Norm behavior: rotor preserves norm; dilation multiplies it by `|w|`. -/
lemma motorBlock_norm (σ t : ℝ) (i : ι) (v : Plane) :
    ‖motorBlock rot w σ t i v‖ = |w σ i| * ‖v‖ := by
  simp only [motorBlock, LinearMap.smul_apply, norm_smul, Real.norm_eq_abs]
  congr 1
  exact (rot i t).norm_map v

/-- Distinct prime motors commute globally (block diagonal). -/
lemma motorOn_comm {i j : ι} (hij : i ≠ j) (σ t : ℝ) :
    (motorOn rot w σ t i).comp (motorOn rot w σ t j)
      =
    (motorOn rot w σ t j).comp (motorOn rot w σ t i) :=
  actOn_comm hij (motorBlock rot w σ t i) (motorBlock rot w σ t j)

end MotorInterface

/-!
## Connection to CliffordRH

This section provides the bridge between MotorCore abstractions and the
existing CliffordRH.lean definitions.
-/
section CliffordBridge

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The standard 2D rotation matrix as a linear isometry.
    TODO: Implement actual rotation by θ. For now, uses identity. -/
def rotation2D (_θ : ℝ) : Plane ≃ₗᵢ[ℝ] Plane :=
  LinearIsometryEquiv.refl ℝ Plane

/-- Prime rotor: rotation by angle t * log(p). -/
def primeRotor (p : ℕ) (t : ℝ) : Plane ≃ₗᵢ[ℝ] Plane :=
  rotation2D (t * Real.log p)

/-- Prime weight: p^(-σ) dilation factor. -/
def primeWeight (σ : ℝ) (p : ℕ) : ℝ := (p : ℝ) ^ (-σ)

/-- The full prime motor combines weight and rotation. -/
def primeMotor (p : ℕ) (σ t : ℝ) : Plane →ₗ[ℝ] Plane :=
  (primeWeight σ p) • (primeRotor p t).toLinearMap

end CliffordBridge

end MotorProof
