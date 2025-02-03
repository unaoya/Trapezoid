import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.PolarCoord

noncomputable section

open Metric Real

notation "ℝ²" => ℝ × ℝ
notation "μ" => MeasureTheory.volume

def C : ℝ := 100

def O : ℝ² := (0,0)

def φ (r : ℝ) : ℝ := arcsin (2 / (r ^ 2))

def g : ℝ² → ℝ² := fun ⟨r, θ⟩ => ⟨r, θ + φ r⟩

def f := polarCoord.symm ∘ g ∘ polarCoord

instance : Dist ℝ² where
  dist p q := Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2)

@[simp]
lemma euc_dist_eq (p : ℝ²) :
  dist (0,0) p = Real.sqrt (p.1^2 + p.2^2) := by
  simp [dist]
