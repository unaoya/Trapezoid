import Trapezoid.Defs
import Trapezoid.Square
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

structure Triangle where
  A : E
  B : E
  C : E

namespace Triangle

variable (T : Triangle)

def contained (S : Set E) : Prop :=
  {T.A, T.B, T.C} ⊆ S

def translate (v : E) : Triangle :=
  ⟨T.A + v, T.B + v, T.C + v⟩

def isIsosceles : Prop :=
  dist T.A T.B = dist T.A T.C ∨
  dist T.A T.B = dist T.B T.C ∨
  dist T.A T.C = dist T.B T.C

noncomputable
def area : ℝ :=
  (μ (convexHull ℝ {T.A, T.B, T.C})).toReal

#check Real.volume_preserving_transvectionStruct
#check Set.Finite.convexHull_eq_image

lemma area_translate_eq (v : E) :
    area (T.translate v) = T.area := by
  rw [area, area]
  rw [translate]
  simp
  sorry

lemma area_std :
    (Triangle.mk ![0, 0] ![1, 0] ![0, 1]).area = 1 / 2 := by
  sorry

def vec_to_matrix (a b : ℝ²) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a.1, a.2; b.1, b.2]

def vec_to_map (a b : ℝ²) : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ :=
  Matrix.mulVecLin (vec_to_matrix a b)

lemma vec_to_matrix_det (a b : ℝ²) :
    abs (a.1 * b.2 - a.2 * b.1) = abs (vec_to_matrix a b).det := by
  dsimp [vec_to_matrix]
  simp

def pair_to_fun (a b : E) : Fin 2 → E :=
  fun i =>
    match i with
    | 0 => a
    | 1 => b

example (a b : E) :
    (PiLp.basisFun 2 ℝ (Fin 2)).addHaar (parallelepiped (pair_to_fun a b)) =
      ENNReal.ofReal |(PiLp.basisFun 2 ℝ (Fin 2)).det (pair_to_fun a b)| := by
  apply MeasureTheory.Measure.addHaar_parallelepiped

lemma area_origin (a b : E) :
    (Triangle.mk O a b).area = abs (a 0 * b 1 - a 1 * b 0) * 1 / 2 := by
  sorry

#check mem_parallelepiped_iff
#check Finset.mem_convexHull
#check convexHull_basis_eq_stdSimplex
#check MeasureTheory.Measure.map_linearMap_addHaar_pi_eq_smul_addHaar
#check MeasureTheory.Measure.map
#check MeasureTheory.Measure.map_apply
#check Finset.mem_convexHull
#check Finset.centerMass_mem_convexHull

open InnerProductGeometry Real

/--
  面積の計算、(1/2)ab sinθ
-/
lemma area_sin (a b : E) :
    (Triangle.mk O a b).area =
      sin (angle a b) * (‖a‖ * ‖b‖) / 2 := by
  rw [area_origin]
  rw [sin_angle_mul_norm_mul_norm]
  simp
  congr
  symm
  rw [Real.sqrt_eq_iff_mul_self_eq]
  ring_nf
  rw [sq_abs]
  ring_nf
  ring_nf
  rw [add_comm, ← mul_pow, ← mul_pow, ← add_assoc, ← sub_eq_add_neg]
  have : a 0 * a 1 * b 0 * b 1 * 2 = 2 * (a 1 * b 0) * (a 0 * b 1) := by
    ring
  rw [this, ← sub_sq]
  exact sq_nonneg _
  simp

end Triangle
