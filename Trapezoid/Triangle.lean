import Mathlib.MeasureTheory.Measure.Haar.OfBasis

notation "ℝ²" => ℝ × ℝ
notation "μ" => MeasureTheory.volume

structure Triangle where
  A : ℝ²
  B : ℝ²
  C : ℝ²

namespace Triangle

def contained (T : Triangle) (S : Set ℝ²) :
    Prop :=
  {T.A, T.B, T.C} ⊆ S

noncomputable
def area (T : Triangle) : ENNReal :=
  μ (convexHull ℝ {T.A, T.B, T.C})

def isosceles (T : Triangle) : Prop :=
  dist T.A T.B = dist T.A T.C ∨
  dist T.A T.B = dist T.B T.C ∨
  dist T.A T.C = dist T.B T.C

end Triangle
