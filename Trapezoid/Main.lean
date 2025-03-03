import Trapezoid.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem

open Bornology Metric Real

section

variable (S : Set E)

def Set.IsUnbounded : Prop := ¬IsBounded S

lemma Set.exists_O (unb : S.IsUnbounded) (A : E) (hA : A ∈ S) (M : ℝ) :
    ∃ O ∈ S, dist O A > M := sorry

end

section

variable (S : Set E) (pos : 0 < μ S)

#check IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ S 1

def p a := ∀ {ι : Type} {l : Filter ι} (w : ι → E) (δ : ι → ℝ),
    Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
      (∀ᶠ (j : ι) in l, a ∈ closedBall (w j) (1 * δ j)) →
        Filter.Tendsto (fun j ↦ μ (S ∩ closedBall (w j) (δ j)) / μ (closedBall (w j) (δ j))) l (nhds 1)

open MeasureTheory.Measure

example : ∃ a, p S a := by
  have := IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ S 1
  have : ∀ᵐ x ∂(restrict μ S), p S x := by apply this
  rw [MeasureTheory.ae_iff] at this
  have : (restrict μ S) {a | ¬p S a}ᶜ > 0 := by
    sorry
  simp at this
  sorry

lemma Lebesgue' : ∃ A ∈ S, ∃ ε ∈ Set.Ioo (0 : ℝ) 1,
    μ (ball A ε ∩ S) > 0.9 * μ (ball A ε) := sorry

theorem main (unb : S.IsUnbounded) :
    ∃ T : Triangle, T.contained S ∧ T.area = 1 ∧ T.isIsosceles :=
  sorry

end
