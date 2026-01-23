import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic

noncomputable section

namespace ProofEngine

/-- Weight function for split signature: +1 on left (e_i), -1 on right (f_j) -/
def split_weight (n : ℕ) : (Fin n ⊕ Fin n) → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- The Split-Signature Quadratic Form Q(x, y) = ∑ x_i^2 - ∑ y_i^2.
    Uses weightedSumSquares with +1 weights on e_i and -1 weights on f_j. -/
def real_split_form (n : ℕ) : QuadraticForm ℝ (Fin n ⊕ Fin n → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (split_weight n)

/-- The Clifford Algebra Cl(n, n) over ℝ. -/
abbrev ClElement (n : ℕ) : Type :=
  CliffordAlgebra (real_split_form n)

/-- The canonical basis vectors e_i (embedding the i-th left basis vector into Clifford algebra). -/
def e (n : ℕ) (i : Fin n) : ClElement n :=
  CliffordAlgebra.ι (real_split_form n) (Pi.single (Sum.inl i) 1)

/-- The canonical basis vectors f_i (embedding the i-th right basis vector into Clifford algebra). -/
def f (n : ℕ) (i : Fin n) : ClElement n :=
  CliffordAlgebra.ι (real_split_form n) (Pi.single (Sum.inr i) 1)

/-- The Prime Bivector B_i = e_i * f_i. -/
def primeBivector (n : ℕ) (i : Fin n) : ClElement n :=
  e n i * f n i

-- ===========================================================================
-- ATOMIC HELPER LEMMAS for quadratic form values
-- ===========================================================================

/-- Helper: Q(e_i basis) = 1 for the left (positive) component -/
lemma split_form_left (n : ℕ) (i : Fin n) :
    real_split_form n (Pi.single (Sum.inl i) 1) = 1 := by
  simp only [real_split_form, QuadraticMap.weightedSumSquares_apply]
  -- Sum over all indices; only the Sum.inl i term is nonzero
  rw [Finset.sum_eq_single (Sum.inl i)]
  · simp only [Pi.single_eq_same, mul_one, split_weight, one_smul]
  · intro b _ hb
    simp only [Pi.single_apply, hb, if_false, mul_zero, smul_zero]
  · intro h
    simp only [Finset.mem_univ, not_true_eq_false] at h

/-- Helper: Q(f_j basis) = -1 for the right (negative) component -/
lemma split_form_right (n : ℕ) (j : Fin n) :
    real_split_form n (Pi.single (Sum.inr j) 1) = -1 := by
  simp only [real_split_form, QuadraticMap.weightedSumSquares_apply]
  rw [Finset.sum_eq_single (Sum.inr j)]
  · simp only [Pi.single_eq_same, mul_one, split_weight, smul_eq_mul, mul_one]
  · intro b _ hb
    simp only [Pi.single_apply, hb, if_false, mul_zero, smul_zero]
  · intro h
    simp only [Finset.mem_univ, not_true_eq_false] at h

/-- e_i^2 = 1 in Cl(n,n) -/
lemma e_sq (n : ℕ) (i : Fin n) : e n i * e n i = 1 := by
  unfold e
  rw [CliffordAlgebra.ι_sq_scalar, split_form_left]
  rfl

/-- f_j^2 = -1 in Cl(n,n) -/
lemma f_sq (n : ℕ) (j : Fin n) : f n j * f n j = -1 := by
  unfold f
  rw [CliffordAlgebra.ι_sq_scalar, split_form_right]
  simp only [map_neg, map_one]

/-- e_i and f_j are orthogonal (different components of Sum).
    Pi.single at Sum.inl i and Sum.inr j have disjoint supports. -/
lemma e_f_isOrtho (n : ℕ) (i j : Fin n) :
    (real_split_form n).IsOrtho (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1) := by
  rw [QuadraticMap.isOrtho_def]
  simp only [real_split_form, QuadraticMap.weightedSumSquares_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  simp only [Pi.add_apply, Pi.single_apply, smul_eq_mul]
  aesop

/-- e_i and e_j are orthogonal for distinct i ≠ j. -/
lemma e_e_isOrtho (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    (real_split_form n).IsOrtho (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inl j) 1) := by
  rw [QuadraticMap.isOrtho_def]
  simp only [real_split_form, QuadraticMap.weightedSumSquares_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  simp only [Pi.add_apply, Pi.single_apply, smul_eq_mul]
  aesop

/-- f_i and f_j are orthogonal for distinct i ≠ j. -/
lemma f_f_isOrtho (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    (real_split_form n).IsOrtho (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inr j) 1) := by
  rw [QuadraticMap.isOrtho_def]
  simp only [real_split_form, QuadraticMap.weightedSumSquares_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  simp only [Pi.add_apply, Pi.single_apply, smul_eq_mul]
  aesop

/-- e_i * f_j = -f_j * e_i (anticommute due to orthogonality) -/
lemma e_f_anticommute (n : ℕ) (i j : Fin n) :
    e n i * f n j = -(f n j * e n i) := by
  unfold e f
  exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (e_f_isOrtho n i j)

/-- f_j * e_i = -(e_i * f_j) (flip of anticommute) -/
lemma f_e_eq_neg_e_f (n : ℕ) (i j : Fin n) : f n j * e n i = -(e n i * f n j) := by
  rw [e_f_anticommute, neg_neg]

/-- e_i * e_j = -e_j * e_i for distinct indices (anticommute) -/
lemma e_e_anticommute (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    e n i * e n j = -(e n j * e n i) := by
  unfold e
  exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (e_e_isOrtho n i j h)

/-- f_i * f_j = -f_j * f_i for distinct indices (anticommute) -/
lemma f_f_anticommute (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    f n i * f n j = -(f n j * f n i) := by
  unfold f
  exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (f_f_isOrtho n i j h)

-- ===========================================================================
-- MAIN THEOREMS
-- ===========================================================================

/-- Helper: LHS reduces to e_j * e_i * (f_i * f_j) -/
private lemma bivector_prod_lhs (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    e n i * f n i * (e n j * f n j) = e n j * e n i * (f n i * f n j) := by
  calc e n i * f n i * (e n j * f n j)
      _ = e n i * (f n i * (e n j * f n j)) := by rw [mul_assoc]
      _ = e n i * ((f n i * e n j) * f n j) := by rw [mul_assoc (f n i) (e n j) (f n j)]
      _ = e n i * ((-(e n j * f n i)) * f n j) := by rw [f_e_eq_neg_e_f n j i]
      _ = e n i * (-(e n j * f n i * f n j)) := by rw [neg_mul]
      _ = -(e n i * (e n j * f n i * f n j)) := by rw [mul_neg]
      _ = -(e n i * (e n j * (f n i * f n j))) := by rw [mul_assoc (e n j) (f n i) (f n j)]
      _ = -(e n i * e n j * (f n i * f n j)) := by rw [← mul_assoc (e n i) (e n j)]
      _ = -(-(e n j * e n i) * (f n i * f n j)) := by rw [e_e_anticommute n i j h]
      _ = e n j * e n i * (f n i * f n j) := by rw [neg_mul, neg_neg]

/-- Helper: RHS reduces to e_j * e_i * (f_i * f_j) -/
private lemma bivector_prod_rhs (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    e n j * f n j * (e n i * f n i) = e n j * e n i * (f n i * f n j) := by
  calc e n j * f n j * (e n i * f n i)
      _ = e n j * (f n j * (e n i * f n i)) := by rw [mul_assoc]
      _ = e n j * ((f n j * e n i) * f n i) := by rw [mul_assoc (f n j) (e n i) (f n i)]
      _ = e n j * ((-(e n i * f n j)) * f n i) := by rw [f_e_eq_neg_e_f n i j]
      _ = e n j * (-(e n i * f n j * f n i)) := by rw [neg_mul]
      _ = -(e n j * (e n i * f n j * f n i)) := by rw [mul_neg]
      _ = -(e n j * (e n i * (f n j * f n i))) := by rw [mul_assoc (e n i) (f n j) (f n i)]
      _ = -(e n j * e n i * (f n j * f n i)) := by rw [← mul_assoc (e n j) (e n i)]
      _ = -(e n j * e n i * (-(f n i * f n j))) := by rw [f_f_anticommute n j i h.symm]
      _ = -(-(e n j * e n i * (f n i * f n j))) := by rw [mul_neg]
      _ = e n j * e n i * (f n i * f n j) := by rw [neg_neg]

theorem primeBivectors_commute_proven (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    primeBivector n i * primeBivector n j = primeBivector n j * primeBivector n i := by
  unfold primeBivector
  rw [bivector_prod_lhs n i j h, bivector_prod_rhs n i j h]

/-- Proven Theorem: Bivector Squares to +1. -/
theorem primeBivector_sq_proven (n : ℕ) (i : Fin n) :
    primeBivector n i * primeBivector n i = 1 := by
  unfold primeBivector
  -- (e * f) * (e * f) = e * (f * (e * f)) = e * ((f * e) * f)
  rw [mul_assoc (e n i) (f n i) (e n i * f n i)]
  rw [← mul_assoc (f n i) (e n i) (f n i)]
  -- f * e = -(e * f)
  rw [f_e_eq_neg_e_f]
  -- = e * (-(e * f) * f) = e * -(e * (f * f))
  rw [neg_mul, mul_assoc (e n i) (f n i) (f n i)]
  -- f * f = -1
  rw [f_sq]
  -- = e * -(e * -1) = e * e = 1
  simp only [mul_neg_one, neg_neg]
  rw [e_sq]

end ProofEngine
