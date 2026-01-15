# Audit Signatures - Riemann Project

All definitions, theorems, structures, and classes.
Proof bodies omitted for reviewability.

---

## GA/Cl33.lean

```lean
def signature33 : Fin 6 → ℝ
  | 0 => 1   -- γ₁: spacelike
  | 1 => 1   -- γ₂: spacelike
  | 2 => 1   -- γ₃: spacelike
  | 3 => -1  -- γ₄: timelike
  | 4 => -1  -- γ₅: timelike (internal)
  | 5 => -1  -- γ₆: timelike (internal)
```

```lean
def Q33 : QuadraticForm ℝ (Fin 6 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ signature33
```

```lean
abbrev Cl33 := CliffordAlgebra Q33
```

```lean
def ι33 : (Fin 6 → ℝ) →ₗ[ℝ] Cl33 := ι Q33
```

```lean
def basis_vector (i : Fin 6) : Fin 6 → ℝ := Pi.single i (1:ℝ)
```

```lean
theorem generator_squares_to_signature (i : Fin 6) :
    (ι33 (basis_vector i)) * (ι33 (basis_vector i)) =
    algebraMap ℝ Cl33 (signature33 i) := by ...
```

```lean
theorem generators_anticommute (i j : Fin 6) (h_ne : i ≠ j) :
    (ι33 (basis_vector i)) * (ι33 (basis_vector j)) +
    (ι33 (basis_vector j)) * (ι33 (basis_vector i)) = 0 := by ...
```

```lean
def B_internal : Cl33 := ι33 (basis_vector 4) * ι33 (basis_vector 5)
```

```lean
theorem B_internal_sq : B_internal * B_internal = -1 := by
  unfold B_internal
  -- B² = (γ₄ γ₅)² = γ₄ γ₅ γ₄ γ₅ = -γ₄² γ₅² = -(-1)(-1) = -1
  let γ₄ := ι33 (basis_vector 4)
  let γ₅ := ι33 (basis_vector 5)
  -- Get anticommutation: γ₅ γ₄ + γ₄ γ₅ = 0, so γ₅ γ₄ = -(γ₄ γ₅)
  have h_anti : γ₅ * γ₄ + γ₄ * γ₅ = 0 := ...
```

```lean
theorem reverse_B_internal : reverse B_internal = -B_internal := by
  unfold B_internal
  let γ₄ := ι33 (basis_vector 4)
  let γ₅ := ι33 (basis_vector 5)
  -- reverse(γ₄ * γ₅) = reverse(γ₅) * reverse(γ₄) = γ₅ * γ₄
  have h1 : reverse (γ₄ * γ₅) = reverse γ₅ * reverse γ₄ := reverse.map_mul γ₄ γ₅
  -- reverse(γᵢ) = γᵢ for single vectors
  have h2 : reverse γ₄ = γ₄ := by ...
```

```lean
def Cl33Complex (a b : ℝ) : Cl33 :=
  algebraMap ℝ Cl33 a + b • B_internal
```

```lean
theorem reverse_Cl33Complex (a b : ℝ) :
    reverse (Cl33Complex a b) = Cl33Complex a (-b) := by ...
```

```lean
theorem Cl33Complex_mul (a b c d : ℝ) :
    Cl33Complex a b * Cl33Complex c d = Cl33Complex (a*c - b*d) (a*d + b*c) := by ...
```

## GA/Cl33Ops.lean

```lean
structure SpectralParam where
  sigma : ℝ  -- Real part
  t : ℝ      -- Imaginary part (coefficient of B)
```

```lean
def SpectralParam.toCl33 (s : SpectralParam) : Cl33 :=
  Cl33Complex s.sigma s.t
```

```lean
def criticalLine (t : ℝ) : SpectralParam :=
  { sigma := 1/2, t := t }
```

```lean
def SpectralParam.conj (s : SpectralParam) : SpectralParam :=
  { sigma := s.sigma, t := -s.t }
```

```lean
theorem SpectralParam.conj_toCl33 (s : SpectralParam) :
    reverse s.toCl33 = s.conj.toCl33 := by ...
```

```lean
def SpectralParam.funcEq (s : SpectralParam) : SpectralParam :=
  { sigma := 1 - s.sigma, t := s.t }
```

```lean
def exp_B (θ : ℝ) : Cl33 :=
  Cl33Complex (Real.cos θ) (Real.sin θ)
```

```lean
theorem exp_B_zero : exp_B 0 = 1 := by
  unfold exp_B Cl33Complex
  simp only [Real.cos_zero, Real.sin_zero, zero_smul, add_zero]
  rfl
```

```lean
theorem exp_B_add (a b : ℝ) : exp_B (a + b) = exp_B a * exp_B b := by
  unfold exp_B
  -- Use the multiplication rule for Cl33Complex:
  -- Cl33Complex a' b' * Cl33Complex c' d' = Cl33Complex (a'*c' - b'*d') (a'*d' + b'*c')
  rw [Cl33Complex_mul]
  -- Goal: Cl33Complex (cos(a+b)) (sin(a+b)) = Cl33Complex (cos a * cos b - sin a * sin b) (cos a * sin b + sin a * cos b)
  -- This is exactly the angle addition formulas
  congr 1
  · exact Real.cos_add a b
  · -- sin(a+b) = sin a * cos b + cos a * sin b, but we have cos a * sin b + sin a * cos b
    rw [Real.sin_add, add_comm]
```

```lean
theorem exp_B_neg (θ : ℝ) : exp_B (-θ) = reverse (exp_B θ) := by
  unfold exp_B
  simp [Real.cos_neg, Real.sin_neg]
  exact (reverse_Cl33Complex (Real.cos θ) (Real.sin θ)).symm
```

```lean
def exp_cl33 (s : SpectralParam) : Cl33 :=
  Real.exp s.sigma • exp_B s.t
```

```lean
def normSq_cl33 (a b : ℝ) : ℝ := a^2 + b^2
```

```lean
def norm_cl33 (a b : ℝ) : ℝ := Real.sqrt (normSq_cl33 a b)
```

```lean
theorem exp_B_normSq (θ : ℝ) : normSq_cl33 (Real.cos θ) (Real.sin θ) = 1 := by
  unfold normSq_cl33
  rw [Real.cos_sq_add_sin_sq]
```

```lean
theorem exp_B_norm (θ : ℝ) : norm_cl33 (Real.cos θ) (Real.sin θ) = 1 := by
  unfold norm_cl33
  rw [exp_B_normSq]
  exact Real.sqrt_one
```

```lean
def alpha_cl (s : SpectralParam) (p : ℕ) : Cl33 :=
  let logp := Real.log (p : ℝ)
  let scale := (p : ℝ) ^ (-s.sigma)  -- p^{-σ}
  scale • Cl33Complex (Real.cos (s.t * logp)) (-Real.sin (s.t * logp))
```

```lean
def beta_cl (s : SpectralParam) (p : ℕ) : Cl33 :=
  reverse (alpha_cl s.funcEq p)
```

```lean
theorem alpha_beta_half (t : ℝ) (p : ℕ) :
    beta_cl (criticalLine t) p = reverse (alpha_cl (criticalLine t) p) := by ...
```

```lean
theorem alpha_cl_normSq (s : SpectralParam) (p : ℕ) (_hp : 2 ≤ p) :
    normSq_cl33
      ((p : ℝ) ^ (-s.sigma) * Real.cos (s.t * Real.log p))
      ((p : ℝ) ^ (-s.sigma) * (-Real.sin (s.t * Real.log p))) =
    (p : ℝ) ^ (-2 * s.sigma) := by ...
```

```lean
def α_cl33 (s : SpectralParam) (p : ℕ) : Cl33 :=
  let scale := (p : ℝ) ^ (-s.sigma)
  let θ := s.t * Real.log p
  -- p⁻ˢ = p⁻ᵟ (cos(t log p) - B sin(t log p))
  scale • Cl33Complex (Real.cos θ) (-Real.sin θ)
```

```lean
theorem α_cl33_eq_alpha_cl (s : SpectralParam) (p : ℕ) :
    α_cl33 s p = alpha_cl s p := by ...
```

```lean
theorem α_cl33_normSq (s : SpectralParam) (p : ℕ) (hp : 2 ≤ p) :
    let θ := s.t * Real.log p
    normSq_cl33
      ((p : ℝ) ^ (-s.sigma) * Real.cos θ)
      ((p : ℝ) ^ (-s.sigma) * (-Real.sin θ)) =
    (p : ℝ) ^ (-2 * s.sigma) := by ...
```

```lean
theorem α_cl33_norm_critical (p : ℕ) (hp : 2 ≤ p) (t : ℝ) :
    let s := criticalLine t
    let θ := s.t * Real.log p
    norm_cl33
      ((p : ℝ) ^ (-s.sigma) * Real.cos θ)
      ((p : ℝ) ^ (-s.sigma) * (-Real.sin θ)) =
    (p : ℝ) ^ (-(1/2 : ℝ)) := by ...
```

## ZetaSurface/AdapterQFD_Ricker.lean

```lean
def rickerReal (x : ℝ) : ℝ :=
  (1 - x^2) * Real.exp (-(x^2) / 2)
```

```lean
def ricker (x : ℝ) : ℂ := (rickerReal x : ℂ)
```

```lean
theorem rickerReal_measurable : Measurable rickerReal := by
  unfold rickerReal
  exact (measurable_const.sub (measurable_id.pow_const 2)).mul
    (measurable_id.pow_const 2 |>.neg.div_const 2 |>.exp)
```

```lean
theorem ricker_measurable : Measurable ricker :=
  Complex.measurable_ofReal.comp rickerReal_measurable
```

```lean
theorem rickerReal_aestronglyMeasurable : AEStronglyMeasurable rickerReal volume :=
  rickerReal_measurable.aestronglyMeasurable
```

```lean
theorem ricker_aestronglyMeasurable : AEStronglyMeasurable ricker volume :=
  ricker_measurable.aestronglyMeasurable
```

```lean
theorem rickerReal_memLp2 : MemLp rickerReal 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq rickerReal_aestronglyMeasurable]
  unfold rickerReal
  -- |rickerReal x|² = (1-x²)² * exp(-x²)
  have h_sq : ∀ x : ℝ, ((1 - x ^ 2) * Real.exp (-(x ^ 2) / 2)) ^ 2 =
      (1 - x ^ 2) ^ 2 * Real.exp (-1 * (x ^ 2)) := by ...
```

```lean
theorem ricker_memLp2 : MemLp ricker 2 (volume : Measure ℝ) := by
  unfold ricker
  exact MemLp.ofReal rickerReal_memLp2
```

```lean
def rickerVec : Lp ℂ 2 (volume : Measure ℝ) :=
  ricker_memLp2.toLp ricker
```

```lean
def atomReal (a b : ℝ) (_hb : 0 < b) : ℝ → ℝ :=
  fun u => Real.sqrt b * rickerReal (b * u - a)
```

```lean
def atom (a b : ℝ) (_hb : 0 < b) : ℝ → ℂ :=
  fun u => (Real.sqrt b : ℂ) * ricker (b * u - a)
```

```lean
theorem atom_measurable (a b : ℝ) (hb : 0 < b) : Measurable (atom a b hb) := by
  unfold atom
  exact measurable_const.mul
    (ricker_measurable.comp ((measurable_const.mul measurable_id).sub_const a))
```

```lean
theorem atom_aestronglyMeasurable (a b : ℝ) (hb : 0 < b) :
    AEStronglyMeasurable (atom a b hb) volume := ...
```

```lean
theorem atom_memLp2 (a b : ℝ) (hb : 0 < b) :
    MemLp (atom a b hb) 2 (volume : Measure ℝ) := by ...
```

```lean
def atomVec (a b : ℝ) (hb : 0 < b) : Lp ℂ 2 (volume : Measure ℝ) :=
  (atom_memLp2 a b hb).toLp (atom a b hb)
```

```lean
theorem atom_inner_bounded (a₁ b₁ a₂ b₂ : ℝ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    ‖@inner ℂ _ _ (atomVec a₁ b₁ hb₁) (atomVec a₂ b₂ hb₂)‖ ≤
    ‖atomVec a₁ b₁ hb₁‖ * ‖atomVec a₂ b₂ hb₂‖ := ...
```

## ZetaSurface/CompletionCore.lean

```lean
theorem critical_fixed (t : ℝ) :
    (1 : ℂ) - conj ((1/2 : ℂ) + (t : ℂ) * Complex.I)
      =
    ((1/2 : ℂ) + (t : ℂ) * Complex.I) := by ...
```

```lean
theorem critical_fixed' (t : ℝ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * Complex.I
    (1 : ℂ) - conj s = s := critical_fixed t
```

```lean
structure CompletedModel where
  /-- Underlying Hilbert space. -/
  H : Type

  /-- Normed group structure on H. -/
  instNormedAddCommGroup : NormedAddCommGroup H

  /-- Inner product space structure on H. -/
  instInner : InnerProductSpace ℂ H

  /-- Completeness of H. -/
  instComplete : CompleteSpace H

  /-- Completed finite operator at spectral parameter s and cutoff B. -/
  Op : ℂ → ℕ → (H →L[ℂ] H)

  /-- Functional-equation shadow: adjoint symmetry. -/
  adjoint_symm :
    ∀ (s : ℂ) (B : ℕ),
      (Op s B).adjoint = Op (1 - conj s) B

  /--
  Critical-line normality: Op(s) commutes with its adjoint when s is on the critical line.

  This is a weaker condition than unitarity but sufficient for spectral structure.
  On the critical line, self-adjointness (from adjoint_symm + critical_fixed) implies normality.
  -/
  normal_on_critical :
    ∀ (t : ℝ) (B : ℕ),
      let s : ℂ := (1/2 : ℂ) + (t : ℂ) * Complex.I
      (Op s B).adjoint * Op s B = Op s B * (Op s B).adjoint
```

```lean
class CompletedOpFamily (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ℂ → ℕ → H →L[ℂ] H) : Prop where
  adjoint_symm : ∀ s B, (K s B).adjoint = K (1 - conj s) B
  normal_on_critical : ∀ (t : ℝ) (B : ℕ),
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * Complex.I
    (K s B).adjoint * K s B = K s B * (K s B).adjoint
```

```lean
theorem selfadjoint_half (B : ℕ) :
    (M.Op (1/2 : ℂ) B).adjoint = M.Op (1/2 : ℂ) B := by ...
```

```lean
theorem selfadjoint_critical (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * Complex.I
    (M.Op s B).adjoint = M.Op s B := by ...
```

```lean
theorem adjoint_off_critical (σ t : ℝ) (B : ℕ) :
    (M.Op ((σ : ℂ) + (t : ℂ) * I) B).adjoint =
    M.Op (((1 - σ) : ℂ) + (t : ℂ) * I) B := by ...
```

```lean
theorem functional_eq_symmetry (s : ℂ) (B : ℕ) :
    (M.Op s B).adjoint = M.Op (1 - conj s) B := ...
```

```lean
theorem selfadjoint_half_tc {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ℂ → ℕ → H →L[ℂ] H) [CompletedOpFamily H K] (B : ℕ) :
    (K (1/2 : ℂ) B).adjoint = K (1/2 : ℂ) B := by ...
```

```lean
theorem adjoint_off_critical_tc {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ℂ → ℕ → H →L[ℂ] H) [CompletedOpFamily H K] (σ t : ℝ) (B : ℕ) :
    (K ((σ : ℂ) + (t : ℂ) * I) B).adjoint =
    K (((1 - σ) : ℂ) + (t : ℂ) * I) B := by ...
```

```lean
theorem functional_eq_symmetry_tc {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ℂ → ℕ → H →L[ℂ] H) [CompletedOpFamily H K] (s : ℂ) (B : ℕ) :
    (K s B).adjoint = K (1 - conj s) B := ...
```

## ZetaSurface/CompletionKernel.lean

```lean
def βCos (s : SpectralParam) (p : ℕ) : ℝ :=
  αCos s.funcEq p
```

```lean
def βSin (s : SpectralParam) (p : ℕ) : ℝ :=
  -αSin s.funcEq p  -- Negated because reversal negates B coefficient
```

```lean
theorem funcEq_sigma_half (t : ℝ) :
    (criticalLine t).funcEq.sigma = 1/2 := by ...
```

```lean
theorem α_β_match_half_real (p : ℕ) :
    αCos (criticalLine 0) p = βCos (criticalLine 0) p ∧
    αSin (criticalLine 0) p = 0 := by ...
```

```lean
def α (s : ℂ) (p : ℕ) : ℂ :=
  (p : ℂ) ^ (-s)
```

```lean
def β (s : ℂ) (p : ℕ) : ℂ :=
  conj (α (1 - conj s) p)
```

```lean
theorem β_eq (s : ℂ) (p : ℕ) (hp : 1 < p) :
    β s p = (p : ℂ) ^ (-(1 - s)) := by ...
```

```lean
theorem α_β_half (p : ℕ) :
    β (1/2 : ℂ) p = conj (α (1/2 : ℂ) p) := by ...
```

```lean
def Kterm (s : ℂ) (p : ℕ) : H →L[ℂ] H :=
  (α s p) • (Tprime p).toContinuousLinearMap +
  (β s p) • (TprimeInv p).toContinuousLinearMap
```

```lean
theorem adjoint_smul (c : ℂ) (U : H →L[ℂ] H) :
    (c • U).adjoint = conj c • U.adjoint := by ...
```

```lean
theorem adjoint_add' (U V : H →L[ℂ] H) :
    (U + V).adjoint = U.adjoint + V.adjoint := by ...
```

```lean
theorem adjoint_finset_sum {ι : Type*} (S : Finset ι) (F : ι → H →L[ℂ] H) :
    (S.sum F).adjoint = S.sum (fun i => (F i).adjoint) := by ...
```

```lean
theorem Kterm_adjoint (s : ℂ) (p : ℕ) :
    (Kterm s p).adjoint = Kterm (1 - conj s) p := by ...
```

```lean
def K (s : ℂ) (B : ℕ) : H →L[ℂ] H := by
  classical
  exact (primesUpTo B).sum (fun p => Kterm s p)
```

```lean
theorem K_adjoint_symm (s : ℂ) (B : ℕ) :
    (K s B).adjoint = K (1 - conj s) B := by ...
```

```lean
theorem K_adjoint_critical (t : ℝ) (B : ℕ) :
    (K (1/2 + t * I) B).adjoint = K (1/2 + t * I) B := by ...
```

```lean
theorem K_selfadjoint_half (B : ℕ) :
    (K (1/2 : ℂ) B).adjoint = K (1/2 : ℂ) B := by ...
```

## ZetaSurface/CompletionKernelModel.lean

```lean
theorem one_minus_conj_critical (t : ℝ) :
    (1 : ℂ) - conj ((1/2 : ℂ) + (t : ℂ) * I) = (1/2 : ℂ) + (t : ℂ) * I := by ...
```

```lean
def KernelModel : CompletedModel where
  H := H  -- L²(ℝ, volume; ℂ) from CompletionKernel

  instNormedAddCommGroup := inferInstance
  instInner := inferInstance
  instComplete := inferInstance

  Op := fun s B => CompletionKernel.K s B

  adjoint_symm := by ...
```

```lean
instance KernelCompletedOpFamily : CompletedOpFamily H CompletionKernel.K where
  adjoint_symm := CompletionKernel.K_adjoint_symm
  normal_on_critical := by ...
```

```lean
theorem kernel_selfadjoint_critical (t : ℝ) (B : ℕ) :
    (CompletionKernel.K ((1/2 : ℂ) + (t : ℂ) * I) B).adjoint =
    CompletionKernel.K ((1/2 : ℂ) + (t : ℂ) * I) B := by ...
```

```lean
theorem kernel_selfadjoint_half (B : ℕ) :
    (CompletionKernel.K (1/2 : ℂ) B).adjoint = CompletionKernel.K (1/2 : ℂ) B := by ...
```

```lean
theorem kernel_normal_critical (t : ℝ) (B : ℕ) :
    (CompletionKernel.K ((1/2 : ℂ) + (t : ℂ) * I) B).adjoint *
    CompletionKernel.K ((1/2 : ℂ) + (t : ℂ) * I) B =
    CompletionKernel.K ((1/2 : ℂ) + (t : ℂ) * I) B *
    (CompletionKernel.K ((1/2 : ℂ) + (t : ℂ) * I) B).adjoint := by ...
```

## ZetaSurface/CompletionMeasure.lean

```lean
abbrev Weight := ℝ → ℝ≥0∞
```

```lean
def μw (w : Weight) : Measure ℝ :=
  (volume : Measure ℝ).withDensity w
```

```lean
abbrev Hw (w : Weight) := Lp ℂ 2 (μw w)
```

```lean
def tau (a : ℝ) : ℝ → ℝ := fun u => u + a
```

```lean
theorem tau_inv (a : ℝ) : tau (-a) ∘ tau a = id := by
  ext u
  simp [tau]
```

```lean
structure QuasiInvariant (w : Weight) : Prop where
  measurable_w : Measurable w
  ae_pos : ∀ᵐ u ∂volume, (0 : ℝ≥0∞) < w u
  ac_fwd : ∀ a : ℝ, (μw w).map (tau a) ≪ μw w
  ac_bwd : ∀ a : ℝ, μw w ≪ (μw w).map (tau a)
```

```lean
def RN_deriv (w : Weight) (a : ℝ) : ℝ → ℝ≥0∞ :=
  fun u => w u / w (u - a)
```

```lean
theorem RN_deriv_explicit (w : Weight) (a : ℝ)
    (_hw : QuasiInvariant w) (u : ℝ) :
    RN_deriv w a u = w u / w (u - a) := rfl
```

```lean
def correctionFactor (w : Weight) (a : ℝ) (u : ℝ) : ℂ :=
  (Real.sqrt (ENNReal.toReal (RN_deriv w a u)) : ℂ)
```

```lean
def UtranslateAux (w : Weight) (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun u => correctionFactor w a u * f (u + a)
```

```lean
theorem RN_deriv_zero (w : Weight) (u : ℝ) (hw : w u ≠ 0) (hw_top : w u ≠ ⊤) :
    RN_deriv w 0 u = 1 := by ...
```

```lean
theorem correctionFactor_zero (w : Weight) (u : ℝ) (hw : w u ≠ 0) (hw_top : w u ≠ ⊤) :
    correctionFactor w 0 u = 1 := by ...
```

```lean
structure TranslationCompatible (w : Weight) : Prop where
  rn_mul_ae : ∀ a b : ℝ, ∀ᵐ u ∂volume,
    RN_deriv w a u * RN_deriv w b (u + a) = RN_deriv w (a + b) u
```

```lean
theorem RN_deriv_exp (c : ℝ) (a u : ℝ) :
    let w : Weight := fun x => ENNReal.ofReal (Real.exp (c * x))
    RN_deriv w a u = ENNReal.ofReal (Real.exp (c * a)) := by ...
```

```lean
theorem exp_weight_translation_compatible (c : ℝ) :
    let w : Weight := fun x => ENNReal.ofReal (Real.exp (c * x))
    TranslationCompatible w := by ...
```

```lean
theorem UtranslateAux_zero (w : Weight) (f : ℝ → ℂ) (u : ℝ)
    (hw : w u ≠ 0) (hw' : w u ≠ ⊤) :
    UtranslateAux w 0 f u = f u := by ...
```

```lean
class AdmitsUnitaryTranslation (w : Weight) where
  /-- The unitary translation operator for shift a -/
  U : ℝ → (Hw w →ₗᵢ[ℂ] Hw w)
  /-- U_a acts as √RN · (f ∘ τ_a) almost everywhere -/
  spec : ∀ a : ℝ, ∀ f : Hw w, ∀ᵐ u ∂(μw w),
    (U a f : ℝ → ℂ) u = correctionFactor w a u * (f : ℝ → ℂ) (u + a)
  /-- U_0 is the identity -/
  zero : U 0 = LinearIsometry.id
  /-- U_a ∘ U_b = U_{a+b} -/
  add : ∀ a b : ℝ, (U a).comp (U b) = U (a + b)
  /-- (U_a)† = U_{-a} -/
  adjoint : ∀ a : ℝ, (U a).toContinuousLinearMap.adjoint = (U (-a)).toContinuousLinearMap
```

```lean
theorem Utranslate_spec (w : Weight) [hw : AdmitsUnitaryTranslation w] (a : ℝ) :
    ∀ f : Hw w, ∀ᵐ u ∂(μw w),
      (Utranslate w a f : ℝ → ℂ) u =
      (Real.sqrt (ENNReal.toReal (RN_deriv w a u)) : ℂ) * (f : ℝ → ℂ) (u + a) := by ...
```

```lean
theorem Utranslate_adjoint (w : Weight) [hw : AdmitsUnitaryTranslation w] (a : ℝ) :
    (Utranslate w a).toContinuousLinearMap.adjoint =
    (Utranslate w (-a)).toContinuousLinearMap := ...
```

```lean
theorem Utranslate_add (w : Weight) [hw : AdmitsUnitaryTranslation w] (a b : ℝ) :
    (Utranslate w a).comp (Utranslate w b) = Utranslate w (a + b) := ...
```

```lean
theorem Utranslate_zero (w : Weight) [hw : AdmitsUnitaryTranslation w] :
    Utranslate w 0 = LinearIsometry.id := ...
```

```lean
def Twprime (w : Weight) [AdmitsUnitaryTranslation w] (p : ℕ) : Hw w →ₗᵢ[ℂ] Hw w :=
  Utranslate w (logShift p)
```

```lean
def TwprimeInv (w : Weight) [AdmitsUnitaryTranslation w] (p : ℕ) : Hw w →ₗᵢ[ℂ] Hw w :=
  Utranslate w (-logShift p)
```

```lean
theorem Twprime_adjoint (w : Weight) [AdmitsUnitaryTranslation w] (p : ℕ) :
    (Twprime w p).toContinuousLinearMap.adjoint =
    (TwprimeInv w p).toContinuousLinearMap := by ...
```

```lean
def α (s : ℂ) (p : ℕ) : ℂ := (p : ℂ) ^ (-s)
```

```lean
def β (s : ℂ) (p : ℕ) : ℂ := conj (α (1 - conj s) p)
```

```lean
def Kwterm (w : Weight) [AdmitsUnitaryTranslation w] (s : ℂ) (p : ℕ) : Hw w →L[ℂ] Hw w :=
  (α s p) • (Twprime w p).toContinuousLinearMap +
  (β s p) • (TwprimeInv w p).toContinuousLinearMap
```

```lean
def Kw (w : Weight) [AdmitsUnitaryTranslation w] (s : ℂ) (B : ℕ) : Hw w →L[ℂ] Hw w := by
  classical
  exact (primesUpTo B).sum (fun p => Kwterm w s p)
```

```lean
theorem adjoint_smul_w (w : Weight) (c : ℂ) (U : Hw w →L[ℂ] Hw w) :
    (c • U).adjoint = conj c • U.adjoint := ...
```

```lean
theorem adjoint_add_w (w : Weight) (U V : Hw w →L[ℂ] Hw w) :
    (U + V).adjoint = U.adjoint + V.adjoint := by ...
```

```lean
theorem beta_conj_eq_alpha_symm (s : ℂ) (p : ℕ) :
    conj (β s p) = α (1 - conj s) p := by ...
```

```lean
theorem alpha_conj_eq_beta_symm (s : ℂ) (p : ℕ) :
    conj (α s p) = β (1 - conj s) p := by ...
```

```lean
theorem Kwterm_adjoint (w : Weight) [AdmitsUnitaryTranslation w] (s : ℂ) (p : ℕ) :
    (Kwterm w s p).adjoint = Kwterm w (1 - conj s) p := by ...
```

```lean
theorem Kw_adjoint_symm (w : Weight) [AdmitsUnitaryTranslation w] (s : ℂ) (B : ℕ) :
    (Kw w s B).adjoint = Kw w (1 - conj s) B := by ...
```

```lean
theorem Kw_selfadjoint_half (w : Weight) [AdmitsUnitaryTranslation w] (B : ℕ) :
    (Kw w (1/2 : ℂ) B).adjoint = Kw w (1/2 : ℂ) B := by ...
```

```lean
def trivialWeight : Weight := fun _ => 1
```

```lean
def gammaWeight (σ : ℝ) : Weight :=
  fun u => ENNReal.ofReal (Real.exp (σ * u))
```

## ZetaSurface/CompletionMeasureModel.lean

```lean
theorem one_minus_conj_critical' (t : ℝ) :
    (1 : ℂ) - conj ((1/2 : ℂ) + (t : ℂ) * I) = (1/2 : ℂ) + (t : ℂ) * I := by ...
```

```lean
def MeasureModel (w : CompletionMeasure.Weight)
    [CompletionMeasure.AdmitsUnitaryTranslation w] : CompletedModel where
  H := CompletionMeasure.Hw w

  instNormedAddCommGroup := inferInstance
  instInner := inferInstance
  instComplete := inferInstance

  Op := fun s B => CompletionMeasure.Kw w s B

  adjoint_symm := by ...
```

```lean
def trivialWeight : CompletionMeasure.Weight := fun _ => 1
```

```lean
def expWeight (σ₀ : ℝ) : CompletionMeasure.Weight :=
  fun u => ENNReal.ofReal (Real.exp (σ₀ * u))
```

```lean
theorem measure_selfadjoint_critical (w : CompletionMeasure.Weight)
    [CompletionMeasure.AdmitsUnitaryTranslation w] (t : ℝ) (B : ℕ) :
    (CompletionMeasure.Kw w ((1/2 : ℂ) + (t : ℂ) * I) B).adjoint =
    CompletionMeasure.Kw w ((1/2 : ℂ) + (t : ℂ) * I) B := by ...
```

```lean
theorem measure_selfadjoint_half (w : CompletionMeasure.Weight)
    [CompletionMeasure.AdmitsUnitaryTranslation w] (B : ℕ) :
    (CompletionMeasure.Kw w (1/2 : ℂ) B).adjoint = CompletionMeasure.Kw w (1/2 : ℂ) B := by ...
```

```lean
theorem measure_normal_critical (w : CompletionMeasure.Weight)
    [CompletionMeasure.AdmitsUnitaryTranslation w] (t : ℝ) (B : ℕ) :
    let s := (1/2 : ℂ) + (t : ℂ) * I
    (CompletionMeasure.Kw w s B).adjoint * CompletionMeasure.Kw w s B =
    CompletionMeasure.Kw w s B * (CompletionMeasure.Kw w s B).adjoint := by ...
```

## ZetaSurface/Compression.lean

```lean
structure CompressionData (M : CompletedModel) where
  /-- The finite-dimensional subspace to compress onto. -/
  W : Submodule ℂ M.H

  /-- Proof that W is finite-dimensional. -/
  finiteDim : FiniteDimensional ℂ W

  /-- Index type for the basis. -/
  ι : Type

  /-- ι is a finite type. -/
  instFintype : Fintype ι

  /-- ι has decidable equality. -/
  instDecEq : DecidableEq ι

  /-- Orthonormal basis of W indexed by ι. -/
  e : OrthonormalBasis ι ℂ W
```

```lean
instance instCompleteSpace : CompleteSpace C.W := FiniteDimensional.complete ℂ C.W
```

```lean
def projToW : M.H →L[ℂ] C.W :=
  C.W.orthogonalProjection
```

```lean
def incl : C.W →L[ℂ] M.H :=
  C.W.subtypeL
```

```lean
def projOnH : M.H →L[ℂ] M.H :=
  (incl C).comp (projToW C)
```

```lean
def OpW (s : ℂ) (B : ℕ) : M.H →L[ℂ] M.H :=
  (projOnH C).comp ((M.Op s B).comp (projOnH C))
```

```lean
def phi (i : C.ι) : M.H :=
  (incl C) (C.e i)
```

```lean
theorem phi_orthonormal : Orthonormal ℂ (phi C) := by
  -- The inclusion preserves inner products, and e is orthonormal in W.
  -- Orthonormal = (∀ i, ‖v i‖ = 1) ∧ Pairwise (⟪v i, v j⟫ = 0)
  constructor
  · -- ∀ i, ‖φ_i‖ = 1
    intro i
    unfold phi incl
    -- ‖(e i : M.H)‖ = ‖e i‖ in W = 1
    have h := C.e.orthonormal.1 i
    rw [← h]
    rfl
  · -- Pairwise: ⟨φ_i, φ_j⟩ = 0 for i ≠ j
    intro i j hij
    unfold phi incl
    -- ⟨(e i : M.H), (e j : M.H)⟩ = ⟨e i, e j⟩ in W = 0
    have h := C.e.orthonormal.2 hij
    rw [← h]
    rfl
```

```lean
def mat (s : ℂ) (B : ℕ) : Matrix C.ι C.ι ℂ :=
  fun i j => @inner ℂ _ _ (phi C i) ((OpW C s B) (phi C j))
```

```lean
def charMat (s : ℂ) (B : ℕ) : Matrix C.ι C.ι ℂ :=
  (1 : Matrix C.ι C.ι ℂ) - mat C s B
```

```lean
def detLike (s : ℂ) (B : ℕ) : ℂ :=
  Matrix.det (charMat C s B)
```

```lean
theorem detLike_eq (s : ℂ) (B : ℕ) :
    detLike C s B = Matrix.det ((1 : Matrix C.ι C.ι ℂ) - mat C s B) := rfl
```

```lean
theorem OpW_range (s : ℂ) (B : ℕ) :
    ∀ v : M.H, OpW C s B v ∈ (LinearMap.range (incl C).toLinearMap) := by ...
```

```lean
theorem projOnH_selfadjoint : (projOnH C).adjoint = projOnH C := by
  unfold projOnH projToW incl
  -- (incl ∘ proj)† = proj† ∘ incl†
  rw [ContinuousLinearMap.adjoint_comp]
  -- proj† = incl and incl† = proj by Mathlib lemmas
  rw [Submodule.adjoint_orthogonalProjection]
  rw [Submodule.adjoint_subtypeL]
```

```lean
theorem OpW_selfadjoint_critical (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * I
    (OpW C s B).adjoint = OpW C s B := by ...
```

```lean
theorem mat_hermitian_critical (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * I
    Matrix.conjTranspose (mat C s B) = mat C s B := by ...
```

```lean
theorem charMat_hermitian_critical (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * I
    Matrix.conjTranspose (charMat C s B) = charMat C s B := by ...
```

```lean
theorem det_real_of_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : Matrix.conjTranspose A = A) :
    (Matrix.det A).im = 0 := by ...
```

```lean
theorem detLike_real_critical (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * I
    (detLike C s B).im = 0 := by ...
```

## ZetaSurface/CompressionRicker.lean

```lean
structure AtomParam where
  a : ℝ  -- translation
  b : ℝ  -- scale
  hb : 0 < b
```

```lean
def AtomParam.toVec (p : AtomParam) : Lp ℂ 2 (volume : Measure ℝ) :=
  atomVec p.a p.b p.hb
```

```lean
abbrev CompressionWindow := Finset AtomParam
```

```lean
def windowAtoms (W : CompressionWindow) : Finset (Lp ℂ 2 (volume : Measure ℝ)) :=
  open Classical in W.image AtomParam.toVec
```

```lean
def atomsFrom (window : CompressionWindow) : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  { v | ∃ p ∈ window, v = p.toVec }
```

```lean
theorem atomsFrom_finite (window : CompressionWindow) : (atomsFrom window).Finite := by
  classical
  apply Set.Finite.subset (Finset.finite_toSet (windowAtoms window))
  intro v hv
  obtain ⟨p, hp, hvp⟩ := hv
  rw [Finset.mem_coe, windowAtoms, Finset.mem_image]
  exact ⟨p, hp, hvp.symm⟩
```

```lean
def rickerSubspace (window : CompressionWindow) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) := ...
```

```lean
theorem rickerSubspace_finiteDim (window : CompressionWindow) :
    FiniteDimensional ℂ (rickerSubspace window) := ...
```

```lean
def dyadicWindow (n_trans n_scale : ℕ) (δ b₀ : ℝ) (_hδ : 0 < δ) (hb₀ : 0 < b₀) :
    CompressionWindow := by ...
```

```lean
def uniformWindow (n : ℕ) (δ b : ℝ) (_hδ : 0 < δ) (hb : 0 < b) :
    CompressionWindow := by ...
```

```lean
def rickerCompressionData (window : CompressionWindow) :
    CompressionData KernelModel := by ...
```

```lean
def rickerDetLike (window : CompressionWindow) (s : ℂ) (B : ℕ) : ℂ :=
  CompressionData.detLike (rickerCompressionData window) s B
```

```lean
def uniformRickerDetLike (n : ℕ) (δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b)
    (s : ℂ) (B : ℕ) : ℂ := ...
```

```lean
theorem rickerSubspace_dim_le (window : CompressionWindow) :
    Module.finrank ℂ (rickerSubspace window) ≤ window.card := by ...
```

```lean
theorem rickerSubspace_dim_eq (window : CompressionWindow)
    (hli : LinearIndependent ℂ (fun p : window => (p.1.toVec : Lp ℂ 2 (volume : Measure ℝ)))) :
    Module.finrank ℂ (rickerSubspace window) = window.card := by ...
```

## ZetaSurface/Hamiltonian.lean

```lean
def B : Cl33 := B_internal
```

```lean
theorem B_sq : B * B = -1 := B_internal_sq
```

```lean
theorem B_rev : CliffordAlgebra.reverse B = -B := reverse_B_internal
```

```lean
def expB (θ : ℝ) : Cl33 := exp_B θ
```

```lean
theorem expB_mul (θ₁ θ₂ : ℝ) : expB θ₁ * expB θ₂ = expB (θ₁ + θ₂) :=
  (exp_B_add θ₁ θ₂).symm
```

```lean
def epsilon : ℝ := 1e-9
```

```lean
theorem epsilon_pos : 0 < epsilon := by norm_num [epsilon]
```

```lean
def BaseGenerator : HR →L[ℝ] HR :=
  let T_plus := (L2TranslateR epsilon).toContinuousLinearMap
  let T_minus := (L2TranslateR (-epsilon)).toContinuousLinearMap
  (1 / (2 * epsilon)) • (T_plus - T_minus)
```

```lean
def Hamiltonian (n : ℕ) : HR →L[ℝ] HR :=
  (Real.log n) • BaseGenerator
```

```lean
theorem Hamiltonian_additivity (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Hamiltonian (a * b) = Hamiltonian a + Hamiltonian b := by ...
```

```lean
def PrimeFlow (n : ℕ) : HR →ₗᵢ[ℝ] HR :=
  TprimeR n
```

```lean
theorem Flow_recursion (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (PrimeFlow a).comp (PrimeFlow b) = PrimeFlow (a * b) := by ...
```

```lean
theorem Flow_comm (a b : ℕ) :
    (PrimeFlow a).comp (PrimeFlow b) = (PrimeFlow b).comp (PrimeFlow a) := by ...
```

```lean
def IsStableGenerator (H : HR →L[ℝ] HR) : Prop :=
  H.adjoint = -H
```

```lean
theorem BaseGenerator_stable : IsStableGenerator BaseGenerator := by
  unfold IsStableGenerator BaseGenerator
  -- Adjoint of scalar • A is conj(scalar) • A†
  rw [map_smulₛₗ ContinuousLinearMap.adjoint]
  simp only [starRingEnd_apply, star_trivial]
  -- Adjoint of (T_plus - T_minus) is (T_plus† - T_minus†)
  rw [map_sub]
  -- Use L2TranslateR_adjoint: T_a† = T_{-a}
  rw [L2TranslateR_adjoint epsilon]
  rw [L2TranslateR_adjoint (-epsilon)]
  simp only [neg_neg]
  -- We have k • (T_minus - T_plus)
  -- We want -k • (T_plus - T_minus)
  rw [← neg_sub]
  rw [smul_neg]
```

```lean
theorem Stability_scalar (r : ℝ) (H : HR →L[ℝ] HR) (h_stable : IsStableGenerator H) :
    IsStableGenerator (r • H) := by ...
```

```lean
theorem Surface_Stability_Universal (n : ℕ) (_hn : 0 < n) :
    IsStableGenerator (Hamiltonian n) := by ...
```

```lean
def SurfaceEnergy (n : ℕ) (f : HR) : ℝ :=
  @inner ℝ HR _ f (Hamiltonian n f)
```

```lean
theorem StableState_EigenCondition (n : ℕ) (f : HR) (E : ℝ)
    (h_eigen : Hamiltonian n f = E • f) (h_norm : ‖f‖ = 1) :
    SurfaceEnergy n f = E := by ...
```

```lean
def primeWeight (σ t : ℝ) (p : ℕ) : Cl33 :=
  (p : ℝ) ^ (-σ) • expB (-t * Real.log p)
```

```lean
def SpectralElement (σ t : ℝ) : Cl33 :=
  algebraMap ℝ Cl33 σ + t • B_internal
```

```lean
theorem SpectralElement_critical (t : ℝ) :
    SpectralElement (1/2) t = algebraMap ℝ Cl33 (1/2) + t • B_internal := ...
```

## ZetaSurface/PrimeShifts.lean

```lean
def logShift (n : ℕ) : ℝ := Real.log n
```

```lean
theorem logShift_pos {n : ℕ} (hn : 2 ≤ n) : 0 < logShift n := by
  unfold logShift
  apply Real.log_pos
  exact mod_cast hn
```

```lean
theorem logShift_prime_pos {p : ℕ} (hp : Nat.Prime p) : 0 < logShift p := by
  apply logShift_pos
  exact hp.two_le
```

```lean
theorem logShift_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    logShift (m * n) = logShift m + logShift n := by ...
```

```lean
def TprimeR (p : ℕ) : HR →ₗᵢ[ℝ] HR :=
  L2TranslateR (logShift p)
```

```lean
def TprimeInvR (p : ℕ) : HR →ₗᵢ[ℝ] HR :=
  L2TranslateR (-logShift p)
```

```lean
theorem TprimeR_TprimeInvR (p : ℕ) :
    (TprimeR p).comp (TprimeInvR p) = LinearIsometry.id := by ...
```

```lean
theorem TprimeInvR_TprimeR (p : ℕ) :
    (TprimeInvR p).comp (TprimeR p) = LinearIsometry.id := by ...
```

```lean
theorem TprimeR_adjoint (p : ℕ) :
    (TprimeR p).toContinuousLinearMap.adjoint = (TprimeInvR p).toContinuousLinearMap := by ...
```

```lean
def Tprime (p : ℕ) : H →ₗᵢ[ℂ] H :=
  L2Translate (logShift p)
```

```lean
def TprimeInv (p : ℕ) : H →ₗᵢ[ℂ] H :=
  L2Translate (-logShift p)
```

```lean
theorem Tprime_TprimeInv (p : ℕ) :
    (Tprime p).comp (TprimeInv p) = LinearIsometry.id := by ...
```

```lean
theorem TprimeInv_Tprime (p : ℕ) :
    (TprimeInv p).comp (Tprime p) = LinearIsometry.id := by ...
```

```lean
theorem Tprime_adjoint (p : ℕ) :
    (Tprime p).toContinuousLinearMap.adjoint = (TprimeInv p).toContinuousLinearMap := by ...
```

```lean
theorem TprimeInv_adjoint (p : ℕ) :
    (TprimeInv p).toContinuousLinearMap.adjoint = (Tprime p).toContinuousLinearMap := by ...
```

```lean
def primesUpTo (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter Nat.Prime
```

```lean
theorem mem_primesUpTo_prime {p B : ℕ} (hp : p ∈ primesUpTo B) : Nat.Prime p := by
  simp [primesUpTo] at hp
  exact hp.2
```

```lean
theorem mem_primesUpTo_le {p B : ℕ} (hp : p ∈ primesUpTo B) : p ≤ B := by
  simp [primesUpTo] at hp
  omega
```

```lean
theorem primesUpTo_mono {B₁ B₂ : ℕ} (h : B₁ ≤ B₂) :
    primesUpTo B₁ ⊆ primesUpTo B₂ := by ...
```

```lean
theorem Tprime_comp_R {p q : ℕ} (_hp : 0 < p) (_hq : 0 < q) :
    (TprimeR p).comp (TprimeR q) = L2TranslateR (logShift p + logShift q) := by ...
```

```lean
theorem Tprime_comp_mul_R {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (TprimeR p).comp (TprimeR q) = TprimeR (p * q) := by ...
```

```lean
theorem TprimeR_comm (p q : ℕ) :
    (TprimeR p).comp (TprimeR q) = (TprimeR q).comp (TprimeR p) := by ...
```

```lean
theorem Tprime_comp {p q : ℕ} (_hp : 0 < p) (_hq : 0 < q) :
    (Tprime p).comp (Tprime q) = L2Translate (logShift p + logShift q) := by ...
```

```lean
theorem Tprime_comm (p q : ℕ) :
    (Tprime p).comp (Tprime q) = (Tprime q).comp (Tprime p) := by ...
```

## ZetaSurface/SpectralReal.lean

```lean
def CriticalOp (M : CompletedModel) (B : ℕ) : M.H →L[ℂ] M.H :=
  M.Op (1/2 : ℂ) B
```

```lean
theorem CriticalOp_selfadjoint (M : CompletedModel) (B : ℕ) :
    (CriticalOp M B).adjoint = CriticalOp M B := by ...
```

```lean
def IsRealComplex (z : ℂ) : Prop := z.im = 0
```

```lean
theorem Eigenvalue_Real_of_SelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Op : H →L[ℂ] H)
    (h_sa : Op.adjoint = Op)
    (ev : ℂ) (v : H) (hv : v ≠ 0)
    (h_eigen : Op v = ev • v) :
    IsRealComplex ev := by ...
```

```lean
theorem Critical_Eigenvalue_Real (M : CompletedModel) (B : ℕ)
    (ev : ℂ) (v : M.H) (hv : v ≠ 0)
    (h_eigen : CriticalOp M B v = ev • v) :
    IsRealComplex ev := ...
```

```lean
theorem NonSelfAdjoint_Off_Critical (M : CompletedModel) (s : ℂ) (B : ℕ)
    (h_off : s.re ≠ 1 / 2)
    (h_inj : ∀ s₁ s₂, M.Op s₁ B = M.Op s₂ B → s₁ = s₂) :
    (M.Op s B).adjoint ≠ M.Op s B := by ...
```

```lean
theorem param_eq_conj_iff_critical (s : ℂ) : s = 1 - conj s ↔ s.re = 1 / 2 := by
  constructor
  · -- Forward: s = 1 - conj(s) implies s.re = 1/2
    intro h
    have h_re : s.re = (1 - conj s).re := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h_re
    -- h_re : s.re = 1 - s.re
    linarith
  · -- Backward: s.re = 1/2 implies s = 1 - conj(s)
    intro h_half
    apply Complex.ext
    · -- Real part: s.re = (1 - conj s).re
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · -- Imaginary part: s.im = (1 - conj s).im
      simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring
```

```lean
theorem Defect_Zero_Iff_Critical (M : CompletedModel) (s : ℂ) (B : ℕ)
    (h_inj : ∀ s₁ s₂, M.Op s₁ B = M.Op s₂ B → s₁ = s₂) :
    AdjointDefect M s B = 0 ↔ s.re = 1 / 2 := by ...
```

```lean
theorem Defect_Zero_On_Critical (M : CompletedModel) (t : ℝ) (B : ℕ) :
    AdjointDefect M ((1 / 2 : ℂ) + (t : ℂ) * I) B = 0 := by ...
```

```lean
theorem SkewAdjoint_to_SelfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E)
    (h_skew : A.adjoint = -A) :
    (Complex.I • A).adjoint = Complex.I • A := by ...
```

```lean
theorem Spectral_Rigidity (M : CompletedModel) (B : ℕ) :
    ∀ ev v, v ≠ 0 → CriticalOp M B v = ev • v → IsRealComplex ev := ...
```

```lean
structure SurfaceTensionHypothesis (M : CompletedModel) where
  /-- The positive-definite quadratic form Q_B(v) -/
  quadraticForm : ℕ → M.H → ℝ
  /-- Positivity: Q_B(v) > 0 for nonzero v when B ≥ 2 (Fix B domain) -/
  quadraticForm_pos : ∀ B : ℕ, 2 ≤ B → ∀ v : M.H, v ≠ 0 → 0 < quadraticForm B v
  /-- The Rayleigh-quotient identity:
      Im⟨v, K(s)v⟩ = (Re(s) - 1/2) · Q_B(v) -/
  rayleigh_imaginary_part :
    ∀ s : ℂ, ∀ B : ℕ, ∀ v : M.H,
    (@inner ℂ M.H _ v (M.Op s B v)).im = (s.re - 1/2) * quadraticForm B v
```

```lean
theorem Real_Eigenvalue_Implies_Critical_of_SurfaceTension
    (M : CompletedModel) (ST : SurfaceTensionHypothesis M)
    (s : ℂ) (B : ℕ) (hB : 2 ≤ B) (ev : ℝ) (v : M.H) (hv : v ≠ 0)
    (h_eigen : M.Op s B v = (ev : ℂ) • v) :
    s.re = 1 / 2 := by ...
```

```lean
structure SpectralExclusionHypothesis (M : CompletedModel) where
  /--
  **The Exclusion Property**: If 1 is an eigenvalue of K(s) with s in the
  critical strip, then s must lie on the critical line.

  This captures the content of Theorem 1.1(ii) from the paper:
  Real eigenvalues (specifically eigenvalue 1) force criticality.
  -/
  eigenvalue_one_implies_critical :
    ∀ s : ℂ, (0 < s.re ∧ s.re < 1) →
    (∃ v : M.H, v ≠ 0 ∧ M.Op s 0 v = (1 : ℂ) • v) →
    s.re = 1 / 2

  /--
  **Generalization**: Any real eigenvalue ev forces criticality.
  -/
  real_eigenvalue_implies_critical :
    ∀ s : ℂ, (0 < s.re ∧ s.re < 1) →
    ∀ (ev : ℝ), (∃ v : M.H, v ≠ 0 ∧ M.Op s 0 v = (ev : ℂ) • v) →
    s.re = 1 / 2
```

```lean
theorem inner_product_consistency
    (M : CompletedModel) (s : ℂ) (B : ℕ)
    (ev : ℝ) (v : M.H) (hv : v ≠ 0)
    (h_eigen : M.Op s B v = (ev : ℂ) • v) :
    @inner ℂ M.H _ v (M.Op s B v) = @inner ℂ M.H _ v (M.Op (1 - conj s) B v) := by ...
```

```lean
theorem adjoint_defect_inner_zero
    (M : CompletedModel) (s : ℂ) (B : ℕ)
    (ev : ℝ) (v : M.H) (hv : v ≠ 0)
    (h_eigen : M.Op s B v = (ev : ℂ) • v) :
    @inner ℂ M.H _ v (AdjointDefect M s B v) = 0 := by ...
```

```lean
def RiemannHypothesis : Prop :=
  ∀ s : ℂ, 0 < s.re ∧ s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2
```

```lean
structure ZetaLinkHypothesis (M : CompletedModel) where
  zeta_zero_iff_eigenvalue_one :
    ∀ s : ℂ, (0 < s.re ∧ s.re < 1) →
    (riemannZeta s = 0 ↔ ∃ B : ℕ, ∃ (v : M.H), v ≠ 0 ∧ M.Op s B v = (1 : ℂ) • v)
```

```lean
structure ZetaLinkHypothesisFixB (M : CompletedModel) where
  zeta_zero_iff_eigenvalue_one :
    ∀ s : ℂ, (0 < s.re ∧ s.re < 1) →
    (riemannZeta s = 0 ↔ ∃ B : ℕ, 2 ≤ B ∧ ∃ (v : M.H), v ≠ 0 ∧ M.Op s B v = (1 : ℂ) • v)
```

```lean
def ZetaLinkHypothesisFixB.ofZetaLink (M : CompletedModel)
    (ZL : ZetaLinkHypothesis M)
    (h_bound : ∀ s : ℂ, (0 < s.re ∧ s.re < 1) → riemannZeta s = 0 →
      ∃ B : ℕ, 2 ≤ B ∧ ∃ (v : M.H), v ≠ 0 ∧ M.Op s B v = (1 : ℂ) • v) :
    ZetaLinkHypothesisFixB M where
  zeta_zero_iff_eigenvalue_one := fun s h_strip => by
    constructor
    · exact h_bound s h_strip
    · intro ⟨B, _, v, hv, h_eigen⟩
      exact (ZL.zeta_zero_iff_eigenvalue_one s h_strip).mpr ⟨B, v, hv, h_eigen⟩
```

```lean
theorem RH_of_ZetaLink_SurfaceTension
    (M : CompletedModel)
    (ZL : ZetaLinkHypothesisFixB M)
    (ST : SurfaceTensionHypothesis M) :
    RiemannHypothesis := by ...
```

```lean
theorem RH_of_ZetaLink_SurfaceTension_alt
    (M : CompletedModel)
    (ZL : ZetaLinkHypothesis M)
    (ST : SurfaceTensionHypothesis M)
    (h_bound : ∀ s : ℂ, (0 < s.re ∧ s.re < 1) → riemannZeta s = 0 →
      ∃ B : ℕ, 2 ≤ B ∧ ∃ (v : M.H), v ≠ 0 ∧ M.Op s B v = (1 : ℂ) • v) :
    RiemannHypothesis := ...
```

## ZetaSurface/SpectralZeta.lean

```lean
def reflect (s : ℂ) : ℂ := (1 : ℂ) - conj s
```

```lean
theorem reflect_criticalLine (t : ℝ) : reflect (criticalLine t) = criticalLine t := by
  simpa [reflect, criticalLine, s_param] using (critical_fixed t)
```

```lean
def CharacteristicEq (s : ℂ) (B : ℕ) : Prop :=
  ∃ v : M.H, v ≠ 0 ∧ M.Op s B v = v
```

```lean
def HasEigenvalueOne (s : ℂ) (B : ℕ) : Prop :=
  ∃ v : M.H, v ≠ 0 ∧ M.Op s B v = (1 : ℂ) • v
```

```lean
theorem CharacteristicEq_iff_EigenvalueOne (s : ℂ) (B : ℕ) :
    CharacteristicEq M s B ↔ HasEigenvalueOne M s B := by ...
```

```lean
theorem critical_selfadjoint (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * I
    (M.Op s B).adjoint = M.Op s B := ...
```

```lean
theorem not_selfadjoint_off_critical (σ t : ℝ) (B : ℕ) (hσ : σ ≠ 1 / 2)
    (h_inj : ∀ s₁ s₂, M.Op s₁ B = M.Op s₂ B → s₁ = s₂) :
    (M.Op ((σ : ℂ) + (t : ℂ) * I) B).adjoint ≠ M.Op ((σ : ℂ) + (t : ℂ) * I) B := by ...
```

```lean
theorem RH_Spectral_Version (s : ℂ) (B : ℕ)
    (_h_char : CharacteristicEq M s B)
    (h_stable : (M.Op s B).adjoint = M.Op s B)
    (h_inj : ∀ s₁ s₂, M.Op s₁ B = M.Op s₂ B → s₁ = s₂) :
    s.re = 1/2 := by ...
```

```lean
def zetaInvC (s : ℂ) (B : ℕ) : ℂ :=
  CompressionData.detLike C s B
```

```lean
def zetaC (s : ℂ) (B : ℕ) : ℂ := (zetaInvC C s B)⁻¹
```

```lean
def zeroSet (B : ℕ) : Set ℂ := { s | zetaInvC C s B = 0 }
```

```lean
theorem zetaInvC_real_on_critical (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * I
    (zetaInvC C s B).im = 0 := by ...
```

```lean
def DetSymm : Prop :=
  ∀ (s : ℂ) (B : ℕ),
    conj (zetaInvC C s B) = zetaInvC C (reflect s) B
```

```lean
theorem zeroSet_reflect_of_DetSymm {B : ℕ} (h : DetSymm C) {s : ℂ}
    (hs : s ∈ zeroSet C B) :
    reflect s ∈ zeroSet C B := by ...
```

```lean
def BridgeToEuler : Prop :=
  ∀ (s : ℂ) (B : ℕ), zetaInvC C s B = ZInv B s
```

```lean
theorem zeroSet_subset_ZInv_zeros {B : ℕ} (h : BridgeToEuler C) :
    zeroSet C B ⊆ { s | ZInv B s = 0 } := by ...
```

```lean
def FiniteRH (B : ℕ) : Prop :=
  ∀ (s : ℂ), zetaInvC C s B = 0 → s.re = (1/2 : ℝ)
```

```lean
theorem zeroSet_subset_criticalLine {B : ℕ} (h : FiniteRH C B) :
    zeroSet C B ⊆ { s | s.re = (1/2 : ℝ) } := by ...
```

```lean
def hasEigOne (s : ℂ) (B : ℕ) : Prop :=
  ∃ v : C.ι → ℂ, v ≠ 0 ∧ (CompressionData.mat C s B).mulVec v = v
```

```lean
theorem detLike_zero_implies_hasEigOne (s : ℂ) (B : ℕ) :
    zetaInvC C s B = 0 → hasEigOne C s B := by ...
```

```lean
theorem spectrum_real_on_critical (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * I
    Matrix.conjTranspose (CompressionData.mat C s B) = CompressionData.mat C s B := ...
```

## ZetaSurface/SurfaceTension.lean

```lean
def SurfaceEnergyNorm (n : ℕ) (f : HR) : ℝ :=
  @inner ℝ HR _ (Hamiltonian n f) (Hamiltonian n f)
```

```lean
theorem Energy_nonneg (n : ℕ) (f : HR) : 0 ≤ SurfaceEnergyNorm n f := by
  unfold SurfaceEnergyNorm
  exact real_inner_self_nonneg
```

```lean
theorem Energy_zero_iff (n : ℕ) (f : HR) :
    SurfaceEnergyNorm n f = 0 ↔ Hamiltonian n f = 0 := by ...
```

```lean
def TensionOp (σ : ℝ) : HR →L[ℝ] HR :=
  (σ - 1/2) • ContinuousLinearMap.id ℝ HR
```

```lean
theorem Equilibrium_Condition (σ : ℝ) (f : HR) (hf : f ≠ 0) :
    TensionOp σ f = 0 ↔ σ = 1/2 := by ...
```

```lean
def StabilityFunctional (σ : ℝ) : ℝ := (σ - 1/2)^2
```

```lean
theorem StabilityFunctional_nonneg (σ : ℝ) : 0 ≤ StabilityFunctional σ := by
  unfold StabilityFunctional
  exact sq_nonneg _
```

```lean
theorem StabilityFunctional_zero_iff (σ : ℝ) :
    StabilityFunctional σ = 0 ↔ σ = 1/2 := by ...
```

```lean
theorem Stability_Cost (σ : ℝ) :
    StabilityFunctional σ = 0 ↔ σ = 1/2 := ...
```

```lean
theorem Tension_Scale_Invariant (σ : ℝ) (m n : ℕ) :
    TensionOp σ = TensionOp σ := rfl
```

```lean
theorem Critical_Surface_Unique :
    ∀ σ : ℝ, (∀ f : HR, f ≠ 0 → TensionOp σ f = 0) ↔ σ = 1/2 := by ...
```

```lean
theorem Stable_Energy_Zero (n : ℕ)
    (h_stable : IsStableGenerator (Hamiltonian n)) (f : HR) :
    SurfaceEnergy n f = 0 := by ...
```

## ZetaSurface/SurfaceTensionInstantiation.lean

```lean
def KernelQuadraticForm (B : ℕ) (v : H) : ℝ :=
  (primesUpTo B).sum (fun p => Real.log p * ‖v‖^2)
```

```lean
theorem KernelQuadraticForm_pos (B : ℕ) (hB : 2 ≤ B) (v : H) (hv : v ≠ 0) :
    0 < KernelQuadraticForm B v := by ...
```

```lean
axiom rayleigh_identity_kernel :
  ∀ (s : ℂ) (B : ℕ) (v : H),
    (@inner ℂ H _ v (K s B v)).im =
    (s.re - 1/2) * KernelQuadraticForm B v
```

```lean
def KernelModelSurfaceTension : SurfaceTensionHypothesis KernelModel where
  quadraticForm := fun B v => KernelQuadraticForm B v

  quadraticForm_pos := fun B hB v hv => KernelQuadraticForm_pos B hB v hv

  rayleigh_imaginary_part := fun s B v => rayleigh_identity_kernel s B v
```

```lean
theorem KernelModel_Hammer_Unconditional
    (s : ℂ) (B : ℕ) (hB : 2 ≤ B) (ev : ℝ) (v : H) (hv : v ≠ 0)
    (h_eigen : K s B v = (ev : ℂ) • v) :
    s.re = 1 / 2 := ...
```

```lean
theorem RH_for_KernelModel
    (ZL : ZetaLinkHypothesisFixB KernelModel) :
    Spectral.RiemannHypothesis := ...
```

## ZetaSurface/SurfaceTensionMeasure.lean

```lean
def logWeight (p : ℕ) : ℝ := Real.log p
```

```lean
def KwTensionTerm (s : ℂ) (p : ℕ) : Hw w →L[ℂ] Hw w :=
  let logp := (Real.log p : ℂ)
  -- T_p = log(p) · (α(s,p) · T_p - β(s,p) · T_p^{-1})
  (logp * α s p) • (Twprime w p).toContinuousLinearMap -
  (logp * β s p) • (TwprimeInv w p).toContinuousLinearMap
```

```lean
def KwTension (s : ℂ) (B : ℕ) : Hw w →L[ℂ] Hw w := by
  classical
  exact (primesUpTo B).sum (fun p => KwTensionTerm s p)
```

```lean
structure of p^{-s} with respect to σ.
```

```lean
def KwQuadraticForm (B : ℕ) (v : Hw w) : ℝ := by
  classical
  exact (primesUpTo B).sum (fun p => logWeight p * ‖(Twprime w p) v‖^2)
```

```lean
theorem logWeight_pos (p : ℕ) (hp : Nat.Prime p) : 0 < logWeight p := by
  unfold logWeight
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 1 < (p : ℝ) := by ...
```

```lean
theorem KwQuadraticForm_pos (B : ℕ) (hB : 2 ≤ B) (v : Hw w) (hv : v ≠ 0) :
    0 < KwQuadraticForm B v := by ...
```

```lean
structure RayleighIdentity (w : Weight) [AdmitsUnitaryTranslation w] where
  /-- The identity holds for all s, B, v -/
  identity : ∀ (s : ℂ) (B : ℕ) (v : Hw w),
    (@inner ℂ (Hw w) _ v (Kw w s B v)).im =
    (s.re - 1/2) * KwQuadraticForm B v
```

```lean
theorem Real_Eigenvalue_Implies_Critical_of_Rayleigh
    (RI : RayleighIdentity w)
    (hQ_pos : ∀ B : ℕ, 2 ≤ B → ∀ v : Hw w, v ≠ 0 → 0 < KwQuadraticForm B v)
    (s : ℂ) (B : ℕ) (hB : 2 ≤ B) (ev : ℝ) (v : Hw w) (hv : v ≠ 0)
    (h_eigen : Kw w s B v = (ev : ℂ) • v) :
    s.re = 1 / 2 := by ...
```

```lean
structure QuadraticFormPositivity (w : Weight) [AdmitsUnitaryTranslation w] where
  pos : ∀ B : ℕ, 2 ≤ B → ∀ v : Hw w, v ≠ 0 → 0 < KwQuadraticForm B v
```

```lean
theorem Real_Eigenvalue_Implies_Critical_Proved
    (RI : RayleighIdentity w)
    (s : ℂ) (B : ℕ) (hB : 2 ≤ B) (ev : ℝ) (v : Hw w) (hv : v ≠ 0)
    (h_eigen : Kw w s B v = (ev : ℂ) • v) :
    s.re = 1 / 2 := by ...
```

```lean
def MeasureModel (w : Weight) [AdmitsUnitaryTranslation w] : CompletedModel where
  H := Hw w
  instNormedAddCommGroup := inferInstance
  instInner := inferInstance
  instComplete := inferInstance
  Op := fun s B => Kw w s B
  adjoint_symm := fun s B => Kw_adjoint_symm w s B
  normal_on_critical := by ...
```

```lean
def MeasureModelSurfaceTension
    (RI : RayleighIdentity w) :
    SurfaceTensionHypothesis (MeasureModel w) where

  quadraticForm := fun B v => KwQuadraticForm B v

  quadraticForm_pos := fun B hB v hv => KwQuadraticForm_pos B hB v hv

  rayleigh_imaginary_part := fun s B v => RI.identity s B v
```

```lean
theorem MeasureModel_Hammer
    (RI : RayleighIdentity w)
    (s : ℂ) (B : ℕ) (hB : 2 ≤ B) (ev : ℝ) (v : Hw w) (hv : v ≠ 0)
    (h_eigen : Kw w s B v = (ev : ℂ) • v) :
    s.re = 1 / 2 := ...
```

## ZetaSurface/TransferOperator.lean

```lean
def αCos (s : SpectralParam) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-s.sigma) * Real.cos (s.t * Real.log p)
```

```lean
def αSin (s : SpectralParam) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-s.sigma) * Real.sin (s.t * Real.log p)
```

```lean
def AtermCos (s : SpectralParam) (p : ℕ) : HR →L[ℝ] HR :=
  (αCos s p) • (TprimeR p).toContinuousLinearMap
```

```lean
def AtermSin (s : SpectralParam) (p : ℕ) : HR →L[ℝ] HR :=
  (αSin s p) • (TprimeR p).toContinuousLinearMap
```

```lean
def α (s : ℂ) (p : ℕ) : ℂ :=
  (p : ℂ) ^ (-s)
```

```lean
theorem α_modulus_critical (p : ℕ) (hp : Nat.Prime p) (t : ℝ) :
    ‖α (1/2 + t * I) p‖ = Real.rpow p (-1/2 : ℝ) := by ...
```

```lean
theorem α_decomposition_critical (p : ℕ) (hp : Nat.Prime p) (t : ℝ) :
    α (1/2 + t * I) p =
    (Real.rpow p (-1/2 : ℝ) : ℂ) * Complex.exp (-I * t * Real.log p) := by ...
```

```lean
def Aterm (s : ℂ) (p : ℕ) : H →L[ℂ] H :=
  (α s p) • (Tprime p).toContinuousLinearMap
```

```lean
def A (s : ℂ) (B : ℕ) : H →L[ℂ] H := by
  classical
  exact (primesUpTo B).sum (fun p => Aterm s p)
```

```lean
theorem Aterm_adjoint (s : ℂ) (p : ℕ) :
    (Aterm s p).adjoint =
    (conj (α s p)) • (TprimeInv p).toContinuousLinearMap := by ...
```

```lean
theorem weights_uniform_modulus (t : ℝ) (p : ℕ) (hp : Nat.Prime p) :
    ‖α (1/2 + t * I) p‖ = Real.rpow p (-1/2 : ℝ) := by ...
```

```lean
theorem weights_phase_critical (t : ℝ) (p : ℕ) (hp : Nat.Prime p)
    (ht : -t * Real.log p ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.arg (α (1/2 + t * I) p) = -t * Real.log p := by ...
```

## ZetaSurface/Translations.lean

```lean
abbrev HR := Lp ℝ 2 (volume : Measure ℝ)
```

```lean
theorem measurePreserving_translate (a : ℝ) :
    MeasurePreserving (fun u => u + a) (volume : Measure ℝ) volume := ...
```

```lean
def L2TranslateR (a : ℝ) : HR →ₗᵢ[ℝ] HR :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun u => u + a) (measurePreserving_translate a)
```

```lean
theorem L2TranslateR_zero : L2TranslateR 0 = LinearIsometry.id := by
  apply LinearIsometry.ext
  intro f
  apply Lp.ext
  have h := Lp.coeFn_compMeasurePreserving f (measurePreserving_translate 0)
  refine h.trans ?_
  filter_upwards with x
  simp only [Function.comp_apply, add_zero, LinearIsometry.id_apply]
```

```lean
theorem L2TranslateR_add (a b : ℝ) :
    (L2TranslateR a).comp (L2TranslateR b) = L2TranslateR (a + b) := by ...
```

```lean
theorem L2TranslateR_comm (a b : ℝ) :
    (L2TranslateR a).comp (L2TranslateR b) = (L2TranslateR b).comp (L2TranslateR a) := by ...
```

```lean
def L2TranslateREquiv (a : ℝ) : HR ≃ₗᵢ[ℝ] HR where
  toLinearEquiv := {
    toFun := L2TranslateR a
    map_add' := (L2TranslateR a).map_add
    map_smul' := (L2TranslateR a).map_smul
    invFun := L2TranslateR (-a)
    left_inv := fun f => by
      have h : (L2TranslateR (-a)).comp (L2TranslateR a) = LinearIsometry.id := by ...
```

```lean
theorem L2TranslateREquiv_symm (a : ℝ) :
    (L2TranslateREquiv a).symm = L2TranslateREquiv (-a) := by ...
```

```lean
theorem L2TranslateR_adjoint (a : ℝ) :
    (L2TranslateR a).toContinuousLinearMap.adjoint =
    (L2TranslateR (-a)).toContinuousLinearMap := by ...
```

```lean
theorem L2TranslateR_unitary (a : ℝ) :
    (L2TranslateR a).toContinuousLinearMap.adjoint ∘L
    (L2TranslateR a).toContinuousLinearMap =
    ContinuousLinearMap.id ℝ HR := by ...
```

```lean
abbrev H := Lp ℂ 2 (volume : Measure ℝ)
```

```lean
def L2Translate (a : ℝ) : H →ₗᵢ[ℂ] H :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun u => u + a) (measurePreserving_translate a)
```

```lean
theorem L2Translate_zero : L2Translate 0 = LinearIsometry.id := by
  apply LinearIsometry.ext
  intro f
  apply Lp.ext
  have h := Lp.coeFn_compMeasurePreserving f (measurePreserving_translate 0)
  refine h.trans ?_
  filter_upwards with x
  simp only [Function.comp_apply, add_zero, LinearIsometry.id_apply]
```

```lean
theorem L2Translate_add (a b : ℝ) :
    (L2Translate a).comp (L2Translate b) = L2Translate (a + b) := by ...
```

```lean
theorem L2Translate_comm (a b : ℝ) :
    (L2Translate a).comp (L2Translate b) = (L2Translate b).comp (L2Translate a) := by ...
```

```lean
def L2TranslateEquiv (a : ℝ) : H ≃ₗᵢ[ℂ] H where
  toLinearEquiv := {
    toFun := L2Translate a
    map_add' := (L2Translate a).map_add
    map_smul' := (L2Translate a).map_smul
    invFun := L2Translate (-a)
    left_inv := fun f => by
      have h : (L2Translate (-a)).comp (L2Translate a) = LinearIsometry.id := by ...
```

```lean
theorem L2Translate_adjoint (a : ℝ) :
    (L2Translate a).toContinuousLinearMap.adjoint =
    (L2Translate (-a)).toContinuousLinearMap := by ...
```

## ZetaSurface/ZetaLinkFinite.lean

```lean
def Z (B : ℕ) (s : ℂ) : ℂ :=
  (primesUpTo B).prod (fun p => (1 - (p : ℂ) ^ (-s))⁻¹)
```

```lean
def ZInv (B : ℕ) (s : ℂ) : ℂ :=
  (primesUpTo B).prod (fun p => 1 - (p : ℂ) ^ (-s))
```

```lean
theorem Z_ZInv_inv (B : ℕ) (s : ℂ) (hZ : Z B s ≠ 0) :
    Z B s * ZInv B s = 1 := by ...
```

```lean
def logEulerTrunc (B M : ℕ) (s : ℂ) : ℂ :=
  (primesUpTo B).sum (fun p =>
    (Finset.Icc 1 M).sum (fun m =>
      ((p : ℂ) ^ (-(m : ℂ) * s)) / (m : ℂ)
    )
  )
```

```lean
def logEulerFirstOrder (B : ℕ) (s : ℂ) : ℂ :=
  (primesUpTo B).sum (fun p => (p : ℂ) ^ (-s))
```

```lean
theorem logEulerFirstOrder_eq (B : ℕ) (s : ℂ) :
    logEulerFirstOrder B s = logEulerTrunc B 1 s := by ...
```

```lean
def detLikeCompressed {M : CompletedModel} (C : CompressionData M) (s : ℂ) (B : ℕ) : ℂ :=
  CompressionData.detLike C s B
```

```lean
def defaultWindow : CompressionWindow :=
  uniformWindow 10 1.0 1.0 (by norm_num) (by norm_num)
```

```lean
def detLikeRicker (s : ℂ) (B : ℕ) : ℂ :=
  rickerDetLike defaultWindow s B
```

```lean
def Op (s : ℂ) (B : ℕ) : (M.H →L[ℂ] M.H) := M.Op s B
```

```lean
def charOp (s : ℂ) (B : ℕ) : (M.H →L[ℂ] M.H) :=
  (1 : M.H →L[ℂ] M.H) - Op M s B
```

```lean
theorem critical_line_det_real (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * I
    (detLikeCompressed C s B).im = 0 := by ...
```

```lean
def traceCompressed {M : CompletedModel} (C : CompressionData M) (s : ℂ) (B : ℕ) : ℂ :=
  (Finset.univ : Finset C.ι).sum (fun i => (CompressionData.mat C s B) i i)
```

```lean
structure TraceLogDetLink {M : CompletedModel} (C : CompressionData M) where
  /-- Predicate for when the trace power sum converges -/
  converges : ℂ → ℕ → Prop
  /-- The trace power sum is summable when converges holds -/
  trace_sum_summable :
    ∀ s : ℂ, ∀ B : ℕ, converges s B →
    Summable (fun n : ℕ => (CompressionData.mat C s B ^ n).trace / (n : ℂ))
  /-- The identity linking log-det to trace sum -/
  log_det_eq_neg_trace_sum :
    ∀ s : ℂ, ∀ B : ℕ, converges s B →
    Complex.log (Matrix.det (1 - CompressionData.mat C s B)) =
    - ∑' n : ℕ, (CompressionData.mat C s B ^ n).trace / (n : ℂ)
```

```lean
theorem log_detLike_of_link {M : CompletedModel} (C : CompressionData M)
    (Link : TraceLogDetLink C) (s : ℂ) (B : ℕ) (h : Link.converges s B) :
    Complex.log (CompressionData.detLike C s B) =
    - ∑' n : ℕ, (CompressionData.mat C s B ^ n).trace / (n : ℂ) := by ...
```

```lean
structure TraceSeriesConvergence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) where
  /-- Bound constant (typically rank of the finite-dimensional space) -/
  boundConst : ℝ
  /-- Positivity of the bound constant -/
  boundConst_pos : 0 < boundConst
  /-- Contraction rate (typically operator norm of A) -/
  contractionRate : ℝ
  /-- The contraction rate is non-negative -/
  contractionRate_nonneg : 0 ≤ contractionRate
  /-- The contraction rate is strictly less than 1 (geometric decay) -/
  contractionRate_lt_one : contractionRate < 1
  /-- The trace norm bound: ‖tr(A^n)‖ ≤ C · r^n -/
  trace_bound : ∀ n : ℕ, ‖(A ^ n).trace‖ ≤ boundConst * contractionRate ^ n
  /-- The Dirichlet series is summable for Re(s) ≥ 0 -/
  series_summable : ∀ s : ℂ, 0 ≤ s.re →
    Summable (fun n : ℕ => (A ^ (n + 1)).trace / ((n + 1 : ℂ) ^ s))
```

```lean
def spectralZetaOfConvergence {M : CompletedModel} (C : CompressionData M)
    (s : ℂ) (B : ℕ)
    (TSC : TraceSeriesConvergence (CompressionData.mat C s B))
    (hs : 0 ≤ s.re) : ℂ := ...
```

```lean
theorem spectralZeta_summable {M : CompletedModel} (C : CompressionData M)
    (s : ℂ) (B : ℕ)
    (TSC : TraceSeriesConvergence (CompressionData.mat C s B))
    (hs : 0 ≤ s.re) :
    Summable (fun n : ℕ => (CompressionData.mat C s B ^ (n + 1)).trace / ((n + 1 : ℂ) ^ s)) := ...
```

## ZetaSurface.lean

```lean
def logCoord (x : ℝ) : ℝ := Real.log x
```

```lean
def s_param (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
```

```lean
def criticalLine (t : ℝ) : ℂ := s_param (1/2) t
```

```lean
theorem mellin_kernel_factorization
    (x σ t : ℝ) (hx : 0 < x) :
    Complex.exp (((s_param σ t) - (1/2 : ℂ)) * Complex.log x)
      =
    Complex.exp (((σ - 1/2 : ℝ) : ℂ) * (Real.log x))
      *
    Complex.exp (Complex.I * ((t : ℂ) * (Real.log x))) := by ...
```

```lean
theorem critical_line_no_envelope (x : ℝ) (hx : 0 < x) :
    Complex.exp ((((1:ℝ)/2 - 1/2 : ℝ) : ℂ) * (Real.log x)) = 1 := by ...
```

```lean
theorem kernel_modulus_one_on_critical_line
    (x t : ℝ) (hx : 0 < x) :
    ‖Complex.exp (((criticalLine t) - (1/2 : ℂ)) * Complex.log x)‖ = 1 := by ...
```

```lean
theorem kernel_modulus_not_one_off_critical
    (x σ t : ℝ) (hx : 0 < x) (hx_ne_one : x ≠ 1) (hσ : σ ≠ 1/2) :
    ‖Complex.exp (((s_param σ t) - (1/2 : ℂ)) * Complex.log x)‖ ≠ 1 := by ...
```

```lean
def phase (t : ℝ) (u : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t : ℂ) * (u : ℂ)))
```

```lean
theorem abs_phase_one (t u : ℝ) : ‖phase t u‖ = 1 := by
  unfold phase
  rw [norm_exp]
  -- re(i·t·u) = 0 since i has zero real part
  simp [Complex.I_re, Complex.I_im]
```

```lean
theorem phase_mul_preserves_inner_product :
    ∀ (t : ℝ), ∀ (u : ℝ), phase t u * conj (phase t u) = 1 := by ...
```

---

**Total signatures extracted: 342**
