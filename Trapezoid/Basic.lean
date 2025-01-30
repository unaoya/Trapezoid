import Trapezoid.Triangle
import Mathlib.Analysis.SpecialFunctions.PolarCoord

open Metric Real

noncomputable section

variable (ε : ℝ) (d : ℝ)
  (hε : ε ∈ Set.Ioo 0 1)
  (hd : d > (C / ε) + ε)

def C : ℝ := 100
def O : ℝ² := (0,0)
def A : ℝ² := (d,0)
def B := ball (A d) ε
def B' := ball (A d) (ε / 2)
def D := ball O C

lemma B_D_disj : Disjoint (B ε d) D := sorry

def φ (r : ℝ) : ℝ := arcsin (2 / (r ^ 2))

def f (p : ℝ²) : ℝ² :=
  let ⟨r, θ⟩ := polarCoord p
  ⟨r * cos (θ + φ r), r * sin (θ + φ r)⟩

def jacobian (f : ℝ² → ℝ²) (p : ℝ²) : ℝ := sorry

lemma jf_eq_1 (p : ℝ²) : jacobian f p = 1 := sorry

def Tf (p : ℝ²) : Triangle where
  A := O
  B := p
  C := f p

lemma Tfp_isosceles (p : ℝ²) :
    (Tf p).isosceles := sorry

lemma Tfp_area1 (p : ℝ²) : (Tf p).area = 1 :=
  sorry

#loogle "convexHull", "image"

lemma sin_ineq (x : ℝ)
    (hx : x ∈ Set.Ioo 0 (π / 2)) :
    sin x < x ∧ x < (π / 2) * sin x :=
  sorry

#loogle Real.sin _ < _

lemma dist_p_fp (p : ℝ²) :
    dist p (f p) < ε / 2 := sorry

lemma fB'_B : f '' (B' ε d) ⊆ (B ε d) :=
  sorry

lemma ineq (S : Set ℝ²)
    (h : f '' ((B' ε  d) ∩ S) ∩ S = ∅) :
    μ ((B ε d) \ S) ≥ 0.125 * (μ (B ε d)) :=
  sorry

axiom Lebesgue (S : Set ℝ²) (pos : 0 < μ S) :
    (A d) ∈ S ∧ μ (B ε d ∩ S) > 0.9 * μ (B ε d)

lemma ineq_contra (S : Set ℝ²) :
    (f '' ((B' ε  d) ∩ S) ∩ S).Nonempty := sorry

lemma exists_p : ∃ p ∈ (B' ε d) ∩ S,
    f p ∈ (B ε d) ∩ S := by
    rcases (ineq_contra ε d S) with ⟨q, hq₀, hq₁⟩
    have : q ∈ (B ε d) :=
      fB'_B _ _ (Set.image_subset _ (Set.inter_subset_left) hq₀)
    rcases hq₀ with ⟨p, hp₀, hp₁⟩
    use p
    rw [hp₁]
    exact ⟨hp₀, ⟨this, hq₁⟩⟩

-- 与えられたSに対し、O=(0,0), A=(d,0)が条件を満たすように取れるとして証明
-- 上の場合に帰着できる。回転と平行移動不変なので
