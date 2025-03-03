import Trapezoid.Defs
import Mathlib.Topology.Algebra.Module.Equiv

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
