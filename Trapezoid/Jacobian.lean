import Trapezoid.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

open Metric Real

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E₁ E₂ E₃ E₄ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
    [NormedAddCommGroup E₄] [NormedSpace 𝕜 E₄]
    {f : E₁ → E₂} (x : E₁) {g : E₂ → E₃} {h : E₃ → E₄}

lemma DifferentiableAt.comp₂ (hh : DifferentiableAt 𝕜 h (g (f x)))
    (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (h ∘ g ∘ f) x := by
  apply DifferentiableAt.comp
  exact hh
  exact DifferentiableAt.comp _ hg hf

lemma fderiv_comp₂ (hh : DifferentiableAt 𝕜 h (g (f x)))
    (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (h ∘ g ∘ f) x =
      (fderiv 𝕜 h (g (f x))).comp ((fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x)) := by
  rw [fderiv_comp _ _ _, fderiv_comp _ hg hf]
  rfl
  exact hh
  exact DifferentiableAt.comp _ hg hf

lemma deriv_comp₂ (x : 𝕜) {f g h : 𝕜 → 𝕜}
    (hf : DifferentiableAt 𝕜 f (g (h x)))
    (hg : DifferentiableAt 𝕜 g (h x))
    (hh : DifferentiableAt 𝕜 h x) :
    deriv (f ∘ g ∘ h) x =
      deriv f (g (h x)) * deriv g (h x) * deriv h x := by
  rw [deriv_comp _ _ _, deriv_comp _ hg hh]
  simp
  ring_nf
  exact hf
  exact DifferentiableAt.comp x hg hh

end

noncomputable section

lemma ContinuousLinearMap.det_comp (E₁ : Type) [TopologicalSpace E₁]
    [AddCommGroup E₁] [Module ℝ E₁] (f g : E₁ →L[ℝ] E₁) :
    (f.comp g).det = f.det * g.det := by
  rw [← LinearMap.det_comp]
  rfl

def Basis.One : Basis (Fin 1) ℝ ℝ := Basis.ofEquivFun (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm

lemma aux (f : ℝ² ≃L[ℝ] ℝ²) :
    (f.toContinuousLinearMap).det = (f.toLinearEquiv).det := by
  have h₀ : f.toContinuousLinearMap.det =
      f.toContinuousLinearMap.toLinearMap.det := rfl
  have h₁ : f.toLinearEquiv.det = f.toLinearEquiv.toLinearMap.det :=
    LinearEquiv.coe_det f.toLinearEquiv
  rw [h₀, h₁]
  rfl

end

noncomputable section

lemma phi_decomp : φ = (arcsin ∘ (fun x => 2 / x) ∘ (fun r => (r ^ 2))) := rfl

@[simp]
lemma differentiable_2_div_x {x : ℝ} (h₀ : x ≠ 0) :
    DifferentiableAt ℝ (fun x => 2 / x) (x ^ 2) := by
  apply DifferentiableAt.div <;> simp [h₀]

lemma differentiable_phi (r : ℝ) (h₀ : r ≠ 0)
    (h₁ : ¬2 / r ^ 2 = -1) (h₂ : ¬2 / r ^ 2 = 1) :
    DifferentiableAt ℝ φ r := by
  rw [phi_decomp]
  apply DifferentiableAt.comp₂
  · exact Real.differentiableAt_arcsin.mpr ⟨h₁, h₂⟩
  · simp [h₀]
  · simp

def deriv_phi (r : ℝ) : ℝ :=
  (√(1 - (2 / r ^ 2) ^ 2))⁻¹ * (-2 / (r ^ 2) ^ 2) * (2 * r)

lemma deriv_phi_eq (r : ℝ) (h₀ : r ≠ 0)
    (h₁ : ¬2 / r ^ 2 = -1) (h₂ : ¬2 / r ^ 2 = 1) :
    deriv φ r = deriv_phi r := by
  rw [phi_decomp, deriv_comp₂, deriv_arcsin, deriv_pow, deriv_div]
  simp
  any_goals simp [h₀]
  · rfl
  · exact Real.differentiableAt_arcsin.mpr ⟨h₁, h₂⟩

open ContinuousLinearMap

def g₁ : ℝ² → ℝ := Prod.fst

def g₂ : ℝ² → ℝ := Prod.snd + φ.comp Prod.fst

def fderiv_g₂ (p : ℝ²) :=
  snd ℝ ℝ ℝ + (lsmul ℝ ℝ (deriv_phi p.fst)).comp (fst ℝ ℝ ℝ)

lemma hasfderiv_g₂ (p : ℝ²) (h₀ : p.1 ≠ 0) (h₁ : ¬2 / p.1 ^ 2 = -1)
    (h₂ : ¬2 / p.1 ^ 2 = 1) : HasFDerivAt g₂ (fderiv_g₂ p) p := by
  apply HasFDerivAt.add
  · exact hasFDerivAt_snd
  · apply HasFDerivAt.comp
    · have := deriv_phi_eq _ h₀ h₁ h₂
      simp [← this, hasFDerivAt_iff_hasDerivAt]
      exact differentiable_phi _ h₀ h₁ h₂
    · exact hasFDerivAt_fst

lemma g_diffble (p : ℝ²) (h₀ : p.1 ≠ 0)
    (h₁ : ¬2 / p.1 ^ 2 = -1) (h₂ : ¬2 / p.1 ^ 2 = 1) :
    DifferentiableAt ℝ g p := by
  apply DifferentiableAt.prod
  · simp
  · refine DifferentiableAt.add ?_ ?_
    · exact differentiableAt_snd
    · have : (fun (x : ℝ²) ↦ φ x.1) = ((fun x => φ x) ∘ (fun x => x.1)) := rfl
      rw [this]
      apply DifferentiableAt.comp
      · exact differentiable_phi _ h₀ h₁ h₂
      · simp

def fderiv_g (p : ℝ²) := (fst ℝ ℝ ℝ).prod (fderiv_g₂ p)

lemma fderiv_g_det : (fderiv_g p).det = 1 := by
  have : (fderiv_g p) =
    LinearMap.toContinuousLinearMap
      (
        (Matrix.toLin
          (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ))
        !![1, 0; deriv_phi p.1, 1]
      ) := by ext <;> simp [fderiv_g, fderiv_g₂]
  simp [this]

lemma hasfderiv_g (p : ℝ²) (h₀ : p.1 ≠ 0) (h₁ : ¬2 / p.1 ^ 2 = -1)
    (h₂ : ¬2 / p.1 ^ 2 = 1) : HasFDerivAt g (fderiv_g p) p := by
  apply HasFDerivAt.prod
  exact hasFDerivAt_fst
  exact hasfderiv_g₂ _ h₀ h₁ h₂

lemma g_deriv_det (p : ℝ²) (h₀ : p.1 ≠ 0) (h₁ : ¬2 / p.1 ^ 2 = -1)
    (h₂ : ¬2 / p.1 ^ 2 = 1) : (fderiv ℝ g p).det = 1 := by
  rw [HasFDerivAt.fderiv (hasfderiv_g _ h₀ h₁ h₂)]
  apply fderiv_g_det

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
  exact matrixPolarCoordSymm_det _

def fderivPolarCoordSymmEquiv (p : ℝ²) (h₀ : p.1 ≠ 0) :=
  LinearEquiv.toContinuousLinearEquiv (fderivPolarCoordSymmEquiv' _ h₀)

lemma fderivPolarCoordSymmEquiv_det (p : ℝ²) (h₀ : p.1 ≠ 0) :
  (fderivPolarCoordSymmEquiv p h₀).det = p.1 := by
  simp [fderivPolarCoordSymmEquiv, fderivPolarCoordSymmEquiv']
  exact matrixPolarCoordSymm_det _

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
  exact hasFDerivAt_polarCoord _ _ hx

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
  rw [f, fderiv_comp₂]
  repeat rw [ContinuousLinearMap.det_comp]
  rw [g_deriv_det _ h₀ h₁ h₂, polarCoord_deriv_det _ hp h₀, polarCoord_symm_deriv_det]
  simp
  exact CommGroupWithZero.mul_inv_cancel _ h₀
  exact polarCoord_symm_diffble _
  exact g_diffble _ h₀ h₁ h₂
  exact polarCoord_diffble _ hp h₀
