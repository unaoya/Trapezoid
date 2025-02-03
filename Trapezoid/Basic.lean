import Trapezoid.Triangle
import Trapezoid.Jacobian

open Metric Real

noncomputable section

-- 与えられたSに対し、O=(0,0), A=(d,0)が条件を満たすように取れるとして証明
-- 上の場合に帰着できる。回転と平行移動不変なので

-- ここでは特別な場合の証明を行う。
-- 帰着の議論はmain.leanにある。

lemma f_r (p : ℝ²)
    (h : g (polarCoord p) ∈ polarCoord.target) :
    (polarCoord (f p)).1 = (polarCoord p).1 := by
  have : polarCoord (f p) = g (polarCoord p) := by
    apply polarCoord.right_inv' h
  rw [this]
  rfl

lemma dist_eq_r (p : ℝ²) :
    dist O p = (polarCoord p).1 := by
  rw [O, euc_dist_eq]
  rfl

lemma f_isom (p : ℝ²)
    (h : g (polarCoord p) ∈ polarCoord.target) :
    dist O p = dist O (f p) := by
  repeat rw [dist_eq_r]
  exact (f_r p h).symm

def Tf (p : ℝ²) : Triangle where
  A := O
  B := p
  C := f p

lemma Tfp_isosceles (p : ℝ²)
    (h : g (polarCoord p) ∈ polarCoord.target) :
    (Tf p).isosceles :=
  Or.symm (Or.inr (f_isom p h))

lemma Tfp_area1 (p : ℝ²) : (Tf p).area = 1 :=
  sorry

#loogle "convexHull", "image"

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

def A : ℝ² := (d,0)
def B := ball (A d) ε
def B' := ball (A d) (ε / 2)
def D := ball O C

lemma B_D_disj : Disjoint (B ε d) D := sorry

lemma dist_p_fp (p : ℝ²) (h : p ∈ (B' ε d)) :
    dist p (f p) < ε / 2 :=
  let r := (polarCoord p).1
  calc
    dist p (f p) = 2 * r * sin ((φ r) / 2) := sorry
    _ < r * φ r := sorry
    _ < r * π / 2 * sin (φ r) := sorry
    _ = π / r := sorry
    _ < π * ε / C := sorry
    _ < ε / 2 := sorry

lemma fB'_B : f '' (B' ε d) ⊆ (B ε d) := by
  intro p ⟨hp₀, hp₁, hp₂⟩
  have : dist p (A d) < ε := sorry
  sorry

#loogle "mem", Metric.ball

lemma ineq (S : Set ℝ²)
    (h : f '' ((B' ε  d) ∩ S) ∩ S = ∅) :
    μ ((B ε d) \ S) ≥ 0.125 * (μ (B ε d)) :=
  sorry

axiom Lebesgue (S : Set ℝ²) (pos : 0 < μ S) :
    (A d) ∈ S ∧ μ (B ε d ∩ S) > 0.9 * μ (B ε d)

lemma ineq_contra (S : Set ℝ²) (pos : 0 < μ S) :
    (f '' ((B' ε  d) ∩ S) ∩ S).Nonempty := by
  by_contra h
  have h₀ := Set.not_nonempty_iff_eq_empty.mp h
  have h₁ := ineq _ _ S h₀
  have h₂ := Lebesgue ε d S pos
  have : μ (B ε d) > μ (B ε d) := by
    calc
      μ (B ε d) = μ (B ε d ∩ S) + μ (B ε d \ S) := sorry
      _ > 0.9 * μ (B ε d) + 0.125 * μ (B ε d) := sorry
      _ = μ (B ε d) := sorry
  exact (lt_self_iff_false (μ (B ε d))).mp this


lemma exists_p (S : Set ℝ²) (pos : 0 < μ S) : ∃ p ∈ (B' ε d) ∩ S,
    f p ∈ (B ε d) ∩ S := by
    rcases (ineq_contra ε d S pos) with ⟨q, hq₀, hq₁⟩
    rcases hq₀ with ⟨p, hp₀, rfl⟩
    use p
    have : p ∈ (B' ε d) :=
      Set.mem_of_mem_inter_left hp₀
    have : f p ∈ (B ε d) :=
      fB'_B _ _ (Set.mem_image_of_mem _ this)
    exact ⟨hp₀, ⟨this, hq₁⟩⟩

end

end
