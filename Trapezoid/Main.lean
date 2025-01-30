import Trapezoid.Basic
import Mathlib.Topology.Bornology.Basic

open Bornology Metric Real

def IsUnbounded (S : Set ℝ²) : Prop :=
  ¬IsBounded S

theorem main (S : Set ℝ²)
    (unb : IsUnbounded S) (pos : 0 < μ S) :
    ∃ T : Triangle, T.contained S
    ∧ T.area = 1 ∧ T.isosceles
   := sorry

lemma Lebesgue' (S : Set ℝ²) :
    ∃ A ∈ S, ∃ ε ∈ Set.Ioo (0 : ℝ) 1,
    μ (ball A ε ∩ S) > 0.9 * μ (ball A ε) :=
  sorry

lemma exists_O (S : Set ℝ²)
    (unb : IsUnbounded S)
    (A : ℝ²) (hA : A ∈ S) (M : ℝ) :
    ∃ O ∈ S, dist O A > M :=
  sorry
