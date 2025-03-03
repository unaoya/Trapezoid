import Trapezoid.Triangle
import Trapezoid.Jacobian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Metric Real

noncomputable section

-- 与えられたSに対し、O=(0,0), A=(d,0)が条件を満たすように取れるとして証明
-- 上の場合に帰着できる。回転と平行移動不変なので

-- ここでは特別な場合の証明を行う。
-- 帰着の議論はmain.leanにある。

section

variable (p : E)

lemma dist_eq_r : dist O p = (polarCoord' p).1 := by
  unfold O
  rw [EuclideanSpace.dist_eq]
  simp
  rfl

lemma f_r (hp : g (polarCoord' p) ∈ polarCoord.target) :
    (polarCoord (f' p)).1 = (polarCoord' p).1 := by
  have : polarCoord (f' p) = g (polarCoord' p) := by
    apply polarCoord.right_inv'
    exact hp
  rw [this]
  rfl

lemma f_isom (hp : g (polarCoord' p) ∈ polarCoord.target) :
    dist O p = dist O (f'' p) := by
  repeat rw [dist_eq_r]
  exact (f_r p hp).symm

def Tf : Triangle where
  A := O
  B := p
  C := f'' p

lemma Tfp_isosceles (hp : g (polarCoord' p) ∈ polarCoord.target) :
    (Tf p).isIsosceles :=
  Or.symm (Or.inr (f_isom p hp))

lemma Tfp_area1 : (Tf p).area = 1 := by
  sorry

end

lemma sin_ineq (x : ℝ)
    (hx : x ∈ Set.Ioo 0 (π / 2)) :
    sin x < x ∧ x < (π / 2) * sin x := by
  constructor
  · exact Real.sin_lt (Set.mem_Ioo.mp hx).1
  · rw [← inv_mul_lt_iff₀]
    · simp
      apply Real.mul_lt_sin
      exact (Set.mem_Ioo.mp hx).1
      exact (Set.mem_Ioo.mp hx).2
    · simp [pi_pos]

section

variable (ε : ℝ) (d : ℝ)
  (hε : ε ∈ Set.Ioo 0 1)
  (hd : d > (C / ε) + ε)

def a : E := ![d, 0]
def b' := ball (a d) ε
def b'' := ball (a d) (ε / 2)
def DD := ball O C

lemma B_D_disj : Disjoint (b' ε d) DD := sorry

lemma dist_p_fp (p : E) (h : p ∈ (b'' ε d)) :
    dist p (f'' p) < ε / 2 :=
  let r := (polarCoord' p).1
  calc
    dist p (f'' p) = 2 * r * sin ((φ r) / 2) := sorry
    _ < r * φ r := sorry
    _ < r * π / 2 * sin (φ r) := sorry
    _ = π / r := sorry
    _ < π * ε / C := sorry
    _ < ε / 2 := sorry

lemma fB'_B : f'' '' (b'' ε d) ⊆ (b' ε d) := by
  intro p ⟨hp₀, hp₁, hp₂⟩
  have : dist p (a d) < ε := sorry
  sorry

section
variable (S : Set E)

lemma ineq (h : f'' '' ((b'' ε  d) ∩ S) ∩ S = ∅)
    (pos : 0 < μ S) :
    μ ((b' ε d) \ S) ≥ 0.125 * (μ (b' ε d)) :=
  have : 0 < μ S := pos
  sorry

lemma ineq_contra (pos : 0 < μ S)
    (Lebesgue : (a d) ∈ S ∧ μ (b' ε d ∩ S) > 0.9 * μ (b' ε d)) :
    (f'' '' ((b'' ε  d) ∩ S) ∩ S).Nonempty := by
  by_contra h
  have h₀ := Set.not_nonempty_iff_eq_empty.mp h
  have h₁ := ineq _ _ S h₀
  have : μ (b' ε d) > μ (b' ε d) := by
    calc
      μ (b' ε d) = μ (b' ε d ∩ S) + μ (b' ε d \ S) := sorry
      _ > 0.9 * μ (b' ε d) + 0.125 * μ (b' ε d) := sorry
      _ > μ (b' ε d) := sorry
  exact (lt_self_iff_false (μ (b' ε d))).mp this

lemma exists_p (pos : 0 < μ S)
  (Lebesgue : (a d) ∈ S ∧ μ (b' ε d ∩ S) > 0.9 * μ (b' ε d)) :
    ∃ p ∈ (b'' ε d) ∩ S, f'' p ∈ (b' ε d) ∩ S := by
    rcases (ineq_contra ε d S pos Lebesgue) with ⟨q, hq₀, hq₁⟩
    rcases hq₀ with ⟨p, hp₀, rfl⟩
    use p
    constructor
    · exact hp₀
    · constructor
      · apply fB'_B
        exact Set.mem_image_of_mem _ hp₀.1
      · exact hq₁

end

end

end
