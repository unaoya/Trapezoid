import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Analysis.Convex.Join
import Trapezoid.Subspace

universe u

lemma self_mem_innerDualCone {H : Type u} (p : H)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    p ∈ Set.innerDualCone {p} := by
  simp_all only [mem_innerDualCone, Set.mem_singleton_iff, forall_eq]
  exact real_inner_self_nonneg

noncomputable section

def A : E := !₂[1, 1]
def B : E := !₂[-1, 1]
def C' : E := !₂[-1, -1]
def D : E := !₂[1, -1]

lemma D_is_negB : D = -B := by
  ext i
  rw [B, D]
  fin_cases i <;> simp

lemma A_is_negC : A = -C' := by
  ext i
  rw [A, C']
  fin_cases i <;> simp

open RealInnerProductSpace

lemma A_is_orth_B : ⟪A, B⟫ = 0 := by simp [A, B]

def L := (Submodule.span ℝ {A})ᗮ

def Lᵣ := Set.innerDualCone {A}

def Lₗ := Set.innerDualCone {C'}

def diagonal := segment ℝ B D

def triangle_A := convexJoin ℝ diagonal {A}

def tirangle_C' := convexJoin ℝ diagonal {C'}

def square := convexHull ℝ {A, B, C', D}

instance : InnerProductSpace.Core ℝ E := InnerProductSpace.toCore

instance : Fact (Module.finrank ℝ E = 1 + 1) := by
  simp
  trivial

lemma A_neq_zero : A ≠ 0 := by
  by_contra h
  unfold A at h
  have := congrFun h 0
  simp at this

lemma B_neq_zero : B ≠ 0 := by
  by_contra h
  unfold B at h
  have := congrFun h 1
  simp at this

lemma rank_L_eq_one : Module.finrank ℝ L = 1 := by
  unfold L
  apply finrank_orthogonal_span_singleton
  apply A_neq_zero

lemma L_eq_span : L = Submodule.span ℝ {B} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_singleton_le_iff_mem]
    unfold L
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    apply A_is_orth_B
  · rw [rank_L_eq_one]
    apply finrank_span_singleton
    apply B_neq_zero

lemma mem_L (p : E) : p ∈ L ↔ ⟪A, p⟫ = 0 := by
  unfold L
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]

lemma mem_Lᵣ (p : E) : p ∈ Lᵣ ↔ ⟪A, p⟫ ≥ 0 := by
  unfold Lᵣ
  rw [mem_innerDualCone]
  simp

lemma mem_Lₗ (p : E) : p ∈ Lₗ ↔ ⟪C', p⟫ ≥ 0 := by
  unfold Lₗ
  rw [mem_innerDualCone]
  simp

lemma inner_eq_zero_iff (p : E) : ⟪A, p⟫ = 0 ↔ ⟪A, p⟫ ≥ 0 ∧ ⟪C', p⟫ ≥ 0 := by
  rw [A_is_negC, InnerProductSpace.Core.inner_neg_left]
  constructor <;> intro h
  · constructor <;> linarith
  · linarith

lemma mem_L_iff (p : E) : p ∈ L ↔ p ∈ Lᵣ ∧ p ∈ Lₗ := by
  rw [mem_L, mem_Lᵣ, mem_Lₗ]
  exact inner_eq_zero_iff p

lemma diagonal_sub_L (p : E) (hp : p ∈ diagonal) : p ∈ L := by
  unfold diagonal at hp
  rw [segment_eq_image] at hp
  rcases hp with ⟨t, ht, rfl⟩
  simp
  rw [mem_L_iff]
  constructor
  · rw [mem_Lᵣ]
    simp
    dsimp [A, B, D]
    ring_nf
    simp
  · rw [mem_Lₗ]
    simp
    dsimp [B, D, C']
    ring_nf
    simp

lemma segment_subset_r (p x : E) (hp : p ∈ L) (hx : x ∈ segment ℝ A p) : x ∈ Lᵣ := by
  have h₁ := ConvexCone.convex (Set.innerDualCone {A})
  rw [← convexHull_pair] at hx
  apply convexHull_min (s := {A, p}) _ h₁
  exact hx
  intro y hy
  rcases hy with rfl | rfl
  exact self_mem_innerDualCone A
  rw [mem_L_iff] at hp
  exact hp.1

lemma segment_subset_l (p x : E) (hp : p ∈ L) (hx : x ∈ segment ℝ C' p) : x ∈ Lₗ := by
  have h₁ := ConvexCone.convex (Set.innerDualCone {C'})
  rw [← convexHull_pair] at hx
  apply convexHull_min (s := {C', p}) _ h₁
  exact hx
  intro y hy
  rcases hy with rfl | rfl
  exact self_mem_innerDualCone C'
  rw [mem_L_iff] at hp
  exact hp.2

lemma triangle_A_sub_Lᵣ (p : E) (hp : p ∈ triangle_A) : p ∈ Lᵣ := by
  rw [triangle_A] at hp
  rw [mem_convexJoin] at hp
  rcases hp with ⟨p, hp, t, rfl, hx⟩
  apply segment_subset_r p
  exact diagonal_sub_L p hp
  rw [segment_symm]
  exact hx

lemma tirangle_C'_sub_Lₗ (p : E) (hp : p ∈ tirangle_C') : p ∈ Lₗ := by
  rw [tirangle_C'] at hp
  rw [mem_convexJoin] at hp
  rcases hp with ⟨p, hp, t, rfl, hx⟩
  apply segment_subset_l p
  exact diagonal_sub_L p hp
  rw [segment_symm]
  exact hx

lemma triangle_inter_sub_L' (p : E) (hp₁ : p ∈ triangle_A) (hp₂ : p ∈ tirangle_C') : p ∈ L := by
  rw [mem_L_iff]
  constructor
  · exact triangle_A_sub_Lᵣ p hp₁
  · exact tirangle_C'_sub_Lₗ p hp₂

lemma triangle_inter_sub_L : triangle_A ∩ tirangle_C' ⊆ L := by
  intro x ⟨hx₁, hx₂⟩
  apply triangle_inter_sub_L' x hx₁ hx₂

theorem triangle_inter_vol : μ (triangle_A ∩ tirangle_C') = 0 := by
  rw [← nonpos_iff_eq_zero]
  calc
    μ (triangle_A ∩ tirangle_C') ≤ μ L := MeasureTheory.measure_mono triangle_inter_sub_L
    _ = 0 := by rw [L_eq_span]; apply vectorspan_volume B

lemma zero_mem_segment : 0 ∈ segment ℝ B D := by
  rw [segment_eq_image]
  simp
  use 1 / 2
  simp
  constructor
  · norm_num
  · dsimp [B, D]
    ext i
    fin_cases i <;> simp; norm_num; ring_nf

lemma segment_decomp : segment ℝ C' A = segment ℝ C' 0 ∪ segment ℝ 0 A := by
  sorry

lemma segment_sub₁ : segment ℝ C' 0 ⊆ convexJoin ℝ (segment ℝ B D) {C', A} := by
  intro x hx
  rw [mem_convexJoin]
  use 0
  constructor
  · exact zero_mem_segment
  · use C'
    constructor
    . simp
    . rw [segment_symm]
      exact hx

lemma segment_sub₂ : segment ℝ 0 A ⊆ convexJoin ℝ (segment ℝ B D) {C', A} := by
  intro x hx
  rw [mem_convexJoin]
  use 0
  constructor
  · exact zero_mem_segment
  · use A
    constructor
    . simp
    . exact hx

lemma segment_sub : segment ℝ C' A ⊆ convexJoin ℝ (segment ℝ B D) {C', A} := by
  rw [segment_decomp]
  exact Set.union_subset segment_sub₁ segment_sub₂

lemma convexJoin_segment : convexJoin ℝ (segment ℝ B D) {C', A} =
    convexJoin ℝ (segment ℝ B D) (segment ℝ C' A) := by
  apply Set.Subset.antisymm
  · apply convexJoin_mono_right
    intro x hx
    rcases hx with rfl | rfl
    exact left_mem_segment ℝ C' A
    exact right_mem_segment ℝ C' A
  · calc
      convexJoin ℝ (segment ℝ B D) (segment ℝ C' A) ⊆
          convexJoin ℝ (segment ℝ B D) (convexJoin ℝ (segment ℝ B D) {C', A}) := by
        apply convexJoin_mono_right
        apply segment_sub
      _ = convexJoin ℝ (convexJoin ℝ (segment ℝ B D) (segment ℝ B D)) {C', A} := by
        exact Eq.symm (convexJoin_assoc (segment ℝ B D) (segment ℝ B D) {C', A})
      _ ⊆ convexJoin ℝ (segment ℝ B D) {C', A} := by
        rw [← convexJoin_singletons, convexJoin_convexJoin_convexJoin_comm]
        simp

lemma triangle_union' : triangle_A ∪ tirangle_C' = square := by
  rw [triangle_A, tirangle_C', ← convexJoin_union_right]
  simp
  rw [diagonal, convexJoin_segment, convexJoin_segments]
  rw [square]
  refine DFunLike.congr rfl ?_
  aesop

lemma union_eq_square : convexJoin ℝ (segment ℝ B D) {C', A} =
    convexHull ℝ {A, B, C', D} := by
  sorry

def EuclideanSpace.toProd (p : E) : ℝ × ℝ := (p 0, p 1)

@[simp]
lemma toProd_fst (p : E) : p.toProd.1 = p 0 := rfl

@[simp]
lemma toProd_snd (p : E) : p.toProd.2 = p 1 := rfl

lemma square_volume (a b : E) (h : a.toProd ≤ b.toProd) :
    μ (convexHull ℝ ((Set.univ).pi ![{a 0, b 0}, {a 1, b 1}])) =
      ENNReal.ofReal ((b 0 - a 0) * (b 1 - a 1)) := by
  have (s : Set (Fin 2)) :
    (convexHull ℝ) (s.pi ![{a 0, b 0}, {a 1, b 1}]) =
      s.pi fun i ↦ (convexHull ℝ) (![{a 0, b 0}, {a 1, b 1}] i) := by
      rw [convexHull_pi]
  rw [this]
  have : μ (Set.univ.pi fun i ↦ (convexHull ℝ) (![{a 0, b 0}, {a 1, b 1}] i)) =
      MeasureTheory.Measure.pi (fun _ => μ)
        (Set.univ.pi fun i ↦ (convexHull ℝ) (![{a 0, b 0}, {a 1, b 1}] i)) := by
    rfl
  rw [this]
  rw [MeasureTheory.Measure.pi_pi]
  simp
  rw [segment_eq_Icc]
  rw [segment_eq_Icc]
  rw [Real.volume_Icc]
  rw [Real.volume_Icc]
  rw [ENNReal.ofReal_mul]
  simp
  rw [← toProd_fst a, ← toProd_fst b]
  exact h.1
  exact h.2
  exact h.1

theorem triangle_union_vol :
    μ (convexJoin ℝ (segment ℝ B D) {A} ∪
      convexJoin ℝ (segment ℝ B D) {C'}) = 4 := by
  rw [triangle_union]
  rw [union_eq_square]
  -- apply square_volume
  sorry

-- Lによる鏡映で移す
theorem triangle_vol_eq :
    μ (convexJoin ℝ (segment ℝ B D) {A}) = μ (convexJoin ℝ (segment ℝ B D) {C'}) := by
  sorry

theorem triangle_vol_eq_2 :
    μ (convexJoin ℝ (segment ℝ B D) {A}) = 2 := by
  have : μ (convexJoin ℝ (segment ℝ B D) {A}) + μ (convexJoin ℝ (segment ℝ B D) {C'}) = 4 := by
    rw [← MeasureTheory.measure_union_add_inter₀]
    rw [triangle_union_vol]
    rw [triangle_inter_vol]
    simp
    apply Convex.nullMeasurableSet
    apply Convex.convexJoin
    exact convex_segment B D
    exact convex_singleton C'
  rw [← triangle_vol_eq] at this
  rw [← two_mul] at this
  rw [← ENNReal.eq_div_iff] at this
  rw [this]
  symm
  rw [ENNReal.eq_div_iff]
  ring
  simp
  simp
  simp
  simp
