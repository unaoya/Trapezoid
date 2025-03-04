import Trapezoid.Defs
import Mathlib.Topology.Algebra.Module.Equiv

noncomputable section

lemma ContinuousLinearMap.det_comp (E₁ : Type) [TopologicalSpace E₁]
    [AddCommGroup E₁] [Module ℝ E₁] (f g : E₁ →L[ℝ] E₁) :
    (f.comp g).det = f.det * g.det := by
  rw [← LinearMap.det_comp]
  rfl

end
