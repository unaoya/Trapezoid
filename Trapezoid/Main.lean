import Trapezoid.Basic
import Mathlib.Topology.Bornology.Basic

open Bornology Metric Real

section
variable (S : Set ℝ²)

def Set.IsUnbounded : Prop :=
  ¬IsBounded S

lemma Set.exists_O (unb : S.IsUnbounded)
    (A : ℝ²) (hA : A ∈ S) (M : ℝ) :
    ∃ O ∈ S, dist O A > M :=
  sorry

end

section
variable (S : Set ℝ²) (pos : 0 < μ S)

lemma Lebesgue' : ∃ A ∈ S, ∃ ε ∈ Set.Ioo (0 : ℝ) 1,
    μ (ball A ε ∩ S) > 0.9 * μ (ball A ε) :=
  sorry

theorem main (unb : S.IsUnbounded) :
    ∃ T : Triangle, T.contained S
    ∧ T.area = 1 ∧ T.isosceles :=
  sorry

end
