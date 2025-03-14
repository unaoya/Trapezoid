import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.PolarCoord

noncomputable section

open Metric Real

notation "ℝ²" => ℝ × ℝ
notation "μ" => MeasureTheory.volume
notation "E" => EuclideanSpace ℝ (Fin 2)

#check finTwoArrowEquiv
#check toEuclidean

def C : ℝ := 100

def O : E := ![0, 0]

def φ (r : ℝ) : ℝ := arcsin (2 / (r ^ 2))

def g : ℝ² → ℝ² := fun ⟨r, θ⟩ => ⟨r, θ + φ r⟩

def polarCoord' := polarCoord ∘ finTwoArrowEquiv ℝ

def f := polarCoord.symm ∘ g ∘ polarCoord

def f' := polarCoord.symm ∘ g ∘ polarCoord'

def f'' := (finTwoArrowEquiv ℝ).symm ∘ polarCoord.symm ∘ g ∘ polarCoord'
