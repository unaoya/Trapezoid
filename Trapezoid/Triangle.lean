import Trapezoid.Defs

notation "E²" => EuclideanSpace ℝ (Fin 2)

#check toEuclidean
#check toEuclidean.toFun
#check toEuclidean.invFun

structure Triangle where
  A : ℝ²
  B : ℝ²
  C : ℝ²

namespace Triangle

variable (T : Triangle)

def contained (S : Set ℝ²) : Prop :=
  {T.A, T.B, T.C} ⊆ S

noncomputable
def area : ENNReal :=
  μ (convexHull ℝ {T.A, T.B, T.C})

-- 面積の計算、(1/2)ab sinθ

def isosceles : Prop :=
  dist T.A T.B = dist T.A T.C ∨
  dist T.A T.B = dist T.B T.C ∨
  dist T.A T.C = dist T.B T.C

end Triangle
