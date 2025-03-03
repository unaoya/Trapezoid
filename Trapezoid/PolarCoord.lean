import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Trapezoid.Defs
import Trapezoid.LA

noncomputable section

open Real

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

#check fderivPiPolarCoordSymm
#check hasFDerivAt_pi_polarCoord_symm
