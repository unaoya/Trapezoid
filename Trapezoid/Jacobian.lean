import Trapezoid.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Metric Real

noncomputable section

lemma ContinuousLinearMap.det_comp (E : Type) [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] (f g : E →L[ℝ] E) :
    (f.comp g).det = f.det * g.det := by
  have (h : E →L[ℝ] E) : h.det = (h : E →ₗ[ℝ] E).det := rfl
  repeat rw [this]
  rw [← LinearMap.det_comp]
  exact rfl

lemma phi_decomp :
    φ = (arcsin ∘ (fun x => 2 / x) ∘ (fun r => (r ^ 2))) := rfl

lemma differentiable_2_div_x (x : ℝ) (h₀ : x ≠ 0) :
    DifferentiableAt ℝ (fun x => 2 / x) x := by
  refine DifferentiableAt.div ?_ ?_ h₀
  · exact differentiableAt_const 2
  · exact differentiableAt_id'

lemma differentiable_phi (r : ℝ) (h₀ : r ≠ 0)
    (h₁ : ¬2 / r ^ 2 = -1) (h₂ : ¬2 / r ^ 2 = 1) :
    DifferentiableAt ℝ φ r := by
  rw [phi_decomp]
  apply DifferentiableAt.comp
  · exact Real.differentiableAt_arcsin.mpr ⟨h₁, h₂⟩
  · apply DifferentiableAt.comp
    · apply differentiable_2_div_x
      exact pow_ne_zero 2 h₀
    · exact differentiableAt_pow 2

def deriv_phi (r : ℝ) : ℝ :=
  (√(1 - (2 / r ^ 2) ^ 2))⁻¹ * (-2 / (r ^ 2) ^ 2 * (2 * r))

lemma deriv_phi_eq (r : ℝ) (h₀ : r ≠ 0)
    (h₁ : ¬2 / r ^ 2 = -1) (h₂ : ¬2 / r ^ 2 = 1) :
    deriv φ r = deriv_phi r := by
  rw [phi_decomp, deriv_comp, deriv_comp]
  rw [deriv_arcsin, deriv_pow, deriv_div]
  simp
  rfl
  · exact differentiableAt_const 2
  · exact differentiableAt_id'
  · exact pow_ne_zero 2 h₀
  · apply differentiable_2_div_x
    exact pow_ne_zero 2 h₀
  · exact differentiableAt_pow 2
  · exact Real.differentiableAt_arcsin.mpr ⟨h₁, h₂⟩
  · apply DifferentiableAt.comp
    · apply differentiable_2_div_x
      exact pow_ne_zero 2 h₀
    · exact differentiableAt_pow 2

lemma g_diffble (p : ℝ²) (h₀ : p.1 ≠ 0)
    (h₁ : ¬2 / p.1 ^ 2 = -1) (h₂ : ¬2 / p.1 ^ 2 = 1) :
    DifferentiableAt ℝ g p := by
  apply DifferentiableAt.prod
  · exact differentiableAt_fst
  · refine DifferentiableAt.add ?_ ?_
    · exact differentiableAt_snd
    · have : (fun (x : ℝ²) ↦ φ x.1) = ((fun x => φ x) ∘ (fun x => x.1)) := rfl
      rw [this]
      apply DifferentiableAt.comp
      · exact differentiable_phi _ h₀ h₁ h₂
      · exact differentiableAt_fst

def fderiv_g (p : ℝ²) :=
  LinearMap.toContinuousLinearMap
    (
      (Matrix.toLin
        (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ))
      !![1, 0; deriv_phi p.1, 1]
    )

lemma fderiv_g_det (p : ℝ²) :
    (fderiv_g p).det = 1 := by simp [fderiv_g]

def g₁ (p : ℝ²) : ℝ := p.1

def Basis.One : Basis (Fin 1) ℝ ℝ :=
  Basis.ofEquivFun (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm

def fderiv_g₁ (_ : ℝ²) :=
  LinearMap.toContinuousLinearMap
    (
      (Matrix.toLin
        (Basis.finTwoProd ℝ) (Basis.One))
      !![1, 0]
    )

def fderiv_g₁' := ContinuousLinearMap.fst ℝ ℝ ℝ

lemma fderiv_g₁_rw (p : ℝ²) :
  fderiv_g₁ p = fderiv_g₁' := by
  ext
  simp [fderiv_g₁', fderiv_g₁, Matrix.toLin_apply, Basis.One]
  simp [fderiv_g₁', fderiv_g₁, Matrix.toLin_apply, Basis.One]

lemma hasfderiv_g₁ (p : ℝ²) : HasFDerivAt g₁ (fderiv_g₁ p) p := by
  have : g₁ = Prod.fst := by rfl
  rw [this, fderiv_g₁_rw]
  apply hasFDerivAt_fst

def g₂ (p : ℝ²) : ℝ := p.2 + φ p.1

lemma g₂_decomp :
    g₂ = (fun p => Prod.snd p + (φ ∘ Prod.fst) p) := rfl

def fderiv_g₂ (p : ℝ²) :=
  LinearMap.toContinuousLinearMap
    (
      (Matrix.toLin
        (Basis.finTwoProd ℝ) (Basis.One))
      !![deriv_phi p.1, 1]
    )

def fderiv_g₂₁ := ContinuousLinearMap.snd ℝ ℝ ℝ

def fderiv_g₂₂ (p : ℝ) :=
  (ContinuousLinearMap.lsmul ℝ ℝ (deriv_phi p)).comp
    (ContinuousLinearMap.fst ℝ ℝ ℝ)

lemma frediv_g₂_rw (p : ℝ²) :
    fderiv_g₂ p = fderiv_g₂₁ + fderiv_g₂₂ p.fst := by
  ext
  simp [fderiv_g₂₁, fderiv_g₂₂, fderiv_g₂, Matrix.toLin_apply, Basis.One]
  simp [fderiv_g₂₁, fderiv_g₂₂, fderiv_g₂, Matrix.toLin_apply, Basis.One]

lemma hasfderiv_g₂ (p : ℝ²) (h₀ : p.1 ≠ 0) (h₁ : ¬2 / p.1 ^ 2 = -1)
    (h₂ : ¬2 / p.1 ^ 2 = 1) : HasFDerivAt g₂ (fderiv_g₂ p) p := by
  rw [g₂_decomp, frediv_g₂_rw]
  apply HasFDerivAt.add
  · exact hasFDerivAt_snd
  · apply HasFDerivAt.comp
    · have := deriv_phi_eq p.1 h₀ h₁ h₂
      simp [← this, hasFDerivAt_iff_hasDerivAt]
      exact differentiable_phi _ h₀ h₁ h₂
    · exact hasFDerivAt_fst

lemma hasfderiv_g (p : ℝ²) (h₀ : p.1 ≠ 0) (h₁ : ¬2 / p.1 ^ 2 = -1)
    (h₂ : ¬2 / p.1 ^ 2 = 1) : HasFDerivAt g (fderiv_g p) p := by
  apply HasFDerivAt.prod (f₁' := fderiv_g₁ p) (f₂' := fderiv_g₂ p)
  exact hasfderiv_g₁ p
  exact hasfderiv_g₂ p h₀ h₁ h₂

lemma fderiv_g_eq (p : ℝ²) (h₀ : p.1 ≠ 0) (h₁ : ¬2 / p.1 ^ 2 = -1)
    (h₂ : ¬2 / p.1 ^ 2 = 1) : fderiv ℝ g p = fderiv_g p :=
  HasFDerivAt.fderiv (hasfderiv_g p h₀ h₁ h₂)

lemma g_deriv_det (p : ℝ²) (h₀ : p.1 ≠ 0) (h₁ : ¬2 / p.1 ^ 2 = -1)
    (h₂ : ¬2 / p.1 ^ 2 = 1) : (fderiv ℝ g p).det = 1 := by
  rw [fderiv_g_eq p h₀ h₁ h₂]
  exact fderiv_g_det p

lemma polarCoord_symm_deriv_det (p : ℝ²) :
    (fderiv ℝ polarCoord.symm p).det = p.1 := by
  rw [HasFDerivAt.fderiv (hasFDerivAt_polarCoord_symm p)]
  apply det_fderivPolarCoordSymm

lemma polarCoord_symm_diffble (p : ℝ²) :
    DifferentiableAt ℝ polarCoord.symm p :=
  HasFDerivAt.differentiableAt (hasFDerivAt_polarCoord_symm p)

def matrixPolarCoordSymm (p : ℝ²) :=
  !![cos p.2, -p.1 * sin p.2; sin p.2, p.1 * cos p.2]

lemma matrixPolarCoordSymm_det (p : ℝ²) :
    (matrixPolarCoordSymm p).det = p.1 := by
  rw [matrixPolarCoordSymm, Matrix.det_fin_two_of]
  calc
    cos p.2 * (p.1 * cos p.2) - (-p.1 * sin p.2) * sin p.2
        = p.1 * (cos p.2 ^ 2 + sin p.2 ^ 2) := by ring
    _ = p.1 := by simp

def fderivPolarCoordSymmEquiv' (p : ℝ²) (h₀ : p.1 ≠ 0) :
    ℝ² ≃ₗ[ℝ] ℝ² := by
  apply LinearEquiv.ofIsUnitDet (v := (Basis.finTwoProd ℝ))
    (v' := (Basis.finTwoProd ℝ))
    (f := (Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
      (matrixPolarCoordSymm p)))
  simp [matrixPolarCoordSymm_det]
  exact h₀

lemma fderivPolarCoordSymmEquiv'_det (p : ℝ²) (h₀ : p.1 ≠ 0) :
    (fderivPolarCoordSymmEquiv' p h₀).det = p.1 := by
  simp [fderivPolarCoordSymmEquiv']
  exact matrixPolarCoordSymm_det p

def fderivPolarCoordSymmEquiv (p : ℝ²) (h₀ : p.1 ≠ 0) :=
  LinearEquiv.toContinuousLinearEquiv (fderivPolarCoordSymmEquiv' p h₀)

lemma fderivPolarCoordSymmEquiv_det (p : ℝ²) (h₀ : p.1 ≠ 0) :
  (fderivPolarCoordSymmEquiv p h₀).det = p.1 := by
  simp [fderivPolarCoordSymmEquiv, fderivPolarCoordSymmEquiv']
  exact matrixPolarCoordSymm_det p

lemma hasFDerivAt_polarCoord (x : ℝ²) (h₀ : (polarCoord x).1 ≠ 0)
    (hx : x ∈ polarCoord.symm.target) :
  HasFDerivAt (𝕜 := ℝ) polarCoord
    (fderivPolarCoordSymmEquiv (polarCoord x) h₀).symm x := by
  apply PartialHomeomorph.hasFDerivAt_symm polarCoord.symm hx
  exact hasFDerivAt_polarCoord_symm (polarCoord x)

lemma fderivAt_polarCoord (x : ℝ²) (hx : x ∈ polarCoord.symm.target)
    (h₀ : (polarCoord x).1 ≠ 0) :
  fderiv ℝ polarCoord x = (fderivPolarCoordSymmEquiv (polarCoord x) h₀).symm := by
  apply HasFDerivAt.fderiv
  apply hasFDerivAt_polarCoord
  exact hx

lemma aux₀ (f : ℝ² ≃L[ℝ] ℝ²) :
    ContinuousLinearMap.det f.toContinuousLinearMap =
      LinearMap.det (f.toContinuousLinearMap.toLinearMap) := rfl

lemma aux₁ (f : ℝ² ≃L[ℝ] ℝ²) :
    LinearEquiv.det (f.toLinearEquiv) =
      LinearMap.det (f.toLinearEquiv.toLinearMap) := by
  exact LinearEquiv.coe_det f.toLinearEquiv

lemma aux (f : ℝ² ≃L[ℝ] ℝ²) :
    ContinuousLinearMap.det f.toContinuousLinearMap =
      LinearEquiv.det (f.toLinearEquiv) := by
  have : f.toContinuousLinearMap.toLinearMap = f.toLinearEquiv.toLinearMap := by rfl
  rw [aux₀, aux₁, this]

lemma polarCoord_deriv_det (x : ℝ²) (hx : x ∈ polarCoord.symm.target)
    (h₀ : (polarCoord x).1 ≠ 0) :
    (fderiv ℝ polarCoord x).det = (polarCoord x).1⁻¹ := by
  rw [fderivAt_polarCoord x hx h₀]
  rw [fderivPolarCoordSymmEquiv]
  rw [ContinuousLinearEquiv.det_coe_symm]
  rw [aux]
  rw [LinearEquiv.toLinearEquiv_toContinuousLinearEquiv]
  rw [fderivPolarCoordSymmEquiv'_det]

lemma polarCoord_diffble (p : ℝ²) (hp : p ∈ polarCoord.symm.target)
    (h : (polarCoord p).1 ≠ 0) : DifferentiableAt ℝ polarCoord p := by
  apply HasFDerivAt.differentiableAt
  apply PartialHomeomorph.hasFDerivAt_symm polarCoord.symm hp
      (f' := (fderivPolarCoordSymmEquiv (polarCoord p) h))
  apply hasFDerivAt_polarCoord_symm (polarCoord p)

lemma jf_eq_1 (p : ℝ²) (h₀ : (polarCoord p).1 ≠ 0)
    (h₁ : ¬2 / (polarCoord p).1 ^ 2 = -1) (h₂ : ¬2 / (polarCoord p).1 ^ 2 = 1)
    (hp : p ∈ polarCoord.symm.target) : (fderiv ℝ f p).det = 1 := by
  rw [f]
  repeat rw [fderiv_comp]
  repeat rw [ContinuousLinearMap.det_comp]
  rw [g_deriv_det _ h₀ h₁ h₂, polarCoord_deriv_det _ hp h₀, polarCoord_symm_deriv_det]
  dsimp [g]
  simp
  exact CommGroupWithZero.mul_inv_cancel _ h₀
  exact g_diffble _ h₀ h₁ h₂
  exact polarCoord_diffble _ hp h₀
  exact polarCoord_symm_diffble _
  refine DifferentiableAt.comp p ?_ ?_
  exact g_diffble _ h₀ h₁ h₂
  exact polarCoord_diffble _ hp h₀
