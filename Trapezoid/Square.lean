import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Measure
import Mathlib.Topology.Algebra.ContinuousAffineMap
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

def triangle_C' := convexJoin ℝ diagonal {C'}

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

lemma tirangle_C'_sub_Lₗ (p : E) (hp : p ∈ triangle_C') : p ∈ Lₗ := by
  rw [triangle_C'] at hp
  rw [mem_convexJoin] at hp
  rcases hp with ⟨p, hp, t, rfl, hx⟩
  apply segment_subset_l p
  exact diagonal_sub_L p hp
  rw [segment_symm]
  exact hx

lemma triangle_inter_sub_L' (p : E) (hp₁ : p ∈ triangle_A) (hp₂ : p ∈ triangle_C') : p ∈ L := by
  rw [mem_L_iff]
  constructor
  · exact triangle_A_sub_Lᵣ p hp₁
  · exact tirangle_C'_sub_Lₗ p hp₂

lemma triangle_inter_sub_L : triangle_A ∩ triangle_C' ⊆ L := by
  intro x ⟨hx₁, hx₂⟩
  apply triangle_inter_sub_L' x hx₁ hx₂

theorem triangle_inter_vol : μ (triangle_A ∩ triangle_C') = 0 := by
  rw [← nonpos_iff_eq_zero]
  calc
    μ (triangle_A ∩ triangle_C') ≤ μ L := MeasureTheory.measure_mono triangle_inter_sub_L
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

lemma zero_mem_segment' : 0 ∈ segment ℝ C' A := by
  rw [segment_eq_image]
  simp
  use 1 / 2
  simp
  constructor
  · norm_num
  · dsimp [C', A]
    ext i
    fin_cases i <;> simp; norm_num; ring_nf

lemma segment_subset : segment ℝ C' 0 ⊆ segment ℝ C' A := by
  rw [← convexHull_pair]
  apply convexHull_min
  · intro x hx
    rcases hx with rfl | rfl
    exact left_mem_segment ℝ C' A
    exact zero_mem_segment'
  · exact convex_segment C' A

lemma segment_subset' : segment ℝ 0 A ⊆ segment ℝ C' A := by
  rw [← convexHull_pair]
  apply convexHull_min
  · intro x hx
    rcases hx with rfl | rfl
    exact zero_mem_segment'
    exact right_mem_segment ℝ C' A
  · exact convex_segment C' A

lemma segment_subset_union : segment ℝ C' 0 ∪ segment ℝ 0 A ⊆ segment ℝ C' A := by
  intro x hx
  rcases hx with hx | hx
  · exact segment_subset hx
  · exact segment_subset' hx

-- openSegment_subset_unionを拡張して証明できる。
-- 拡張をmathlibにpushしたい。
lemma segment_decomp : segment ℝ C' A = segment ℝ C' 0 ∪ segment ℝ 0 A := by
  apply Set.eq_of_subset_of_subset
  · rw [← insert_endpoints_openSegment]
    apply Set.insert_subset
    left
    exact left_mem_segment ℝ C' 0
    apply Set.insert_subset
    right
    exact right_mem_segment ℝ 0 A
    calc
      openSegment ℝ C' A ⊆ insert 0 (openSegment ℝ C' 0 ∪ openSegment ℝ 0 A) := by
        apply openSegment_subset_union
        use 1 / 2
        unfold C' A
        unfold AffineMap.lineMap
        simp
        ext i
        fin_cases i <;> simp; norm_num; ring_nf
      _ ⊆ segment ℝ C' 0 ∪ segment ℝ 0 A := by
        apply Set.insert_subset
        left
        exact right_mem_segment ℝ C' 0
        apply Set.union_subset_union
        apply openSegment_subset_segment
        apply openSegment_subset_segment
  · exact segment_subset_union

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

lemma triangle_union' : triangle_A ∪ triangle_C' = square := by
  rw [triangle_A, triangle_C', ← convexJoin_union_right]
  simp
  rw [diagonal, convexJoin_segment, convexJoin_segments]
  rw [square]
  refine DFunLike.congr rfl ?_
  aesop

instance : AddCommMonoid (Set E) := Set.addCommMonoid (α := E)

def T_A := AffineEquiv.constVAdd ℝ E A

lemma T_A_invfun : T_A.invFun = λ x => C' + x := by
  ext x i
  unfold T_A C' A
  fin_cases i <;> simp

lemma mu_T_A : μ square = μ (T_A.invFun ⁻¹' square) := by
  rw [← MeasureTheory.Measure.measure_preimage_of_map_eq_self]
  rw [T_A_invfun]
  rw [MeasureTheory.Measure.IsAddLeftInvariant.map_add_left_eq_self C']
  apply Convex.nullMeasurableSet
  exact convex_convexHull ℝ {A, B, C', D}

def b : Fin 2 → E := ![A + D, A + B]

lemma invfun_invimg_eq_fun_img : T_A.invFun ⁻¹' square = T_A.toAffineMap '' square := by
  simp

lemma pair_union {α : Type u} (s t : α) : ({s, t} : Set α) = {s} ∪ {t} := by
  simp
  exact Set.pair_comm s t

lemma T_A_sq_eq_conv : T_A.toAffineMap '' square = convexHull ℝ (∑ i : Fin 2, {0, b i}) := by
  unfold square
  rw [AffineMap.image_convexHull]
  congr
  simp
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_pair]
  rw [pair_union 0, Set.union_add, pair_union 0, Set.add_union, Set.add_union]
  simp
  unfold b T_A
  simp
  rw [A_is_negC, D_is_negB]
  simp
  rw [add_assoc, add_comm (-C') B, ← add_assoc _ B]
  simp
  aesop


lemma convexHull_eq_paralle : convexHull ℝ (∑ i : Fin 2, {0, b i}) = parallelepiped b :=
  (parallelepiped_eq_convexHull b).symm

lemma T_A_square : μ (T_A.invFun ⁻¹' square) = μ (parallelepiped b) := by
  rw [← convexHull_eq_paralle]
  rw [← T_A_sq_eq_conv]
  rw [invfun_invimg_eq_fun_img]

def S (a : ℝˣ) := DistribMulAction.toLinearEquiv ℝ E a

def S_2 := S (IsUnit.unit (by norm_num : IsUnit (2 : ℝ)))

lemma S_2_eq : S_2.toLinearMap = (2 : ℝ) • LinearMap.id := by
  simp [S_2, S]
  ext x i
  simp

lemma det_S_2 : S_2.toLinearMap.det = 4 := by
  rw [S_2_eq]
  rw [LinearMap.det_smul]
  simp
  norm_num

def onb : OrthonormalBasis (Fin 2) ℝ E :=
  {
    repr := LinearIsometryEquiv.refl ℝ E
  }

@[simp]
lemma onb_zero : onb 0 = ![1, 0] := by
  unfold onb
  simp
  ext i
  fin_cases i <;> simp <;> rfl

@[simp]
lemma onb_one : onb 1 = ![0, 1] := by
  unfold onb
  simp
  ext i
  fin_cases i <;> simp <;> rfl

lemma b_eq_scale_onb : b = onb.toBasis.map S_2 := by
  simp
  ext i j
  unfold b S_2 S A B D
  simp
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

lemma map_linearMap_volume_eq_smul_volume (f : E →ₗ[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |(f.det)| * μ s := by
  have (s : Set (Fin 2 → ℝ)) :
    (MeasureTheory.Measure.map (EuclideanSpace.measurableEquiv (Fin 2)) μ) s =
      μ ((EuclideanSpace.measurableEquiv (Fin 2)) ⁻¹' s) := by
    apply MeasurableEquiv.map_apply
  simp

lemma b_is_img : parallelepiped b = S_2.toLinearMap '' parallelepiped onb := by
  rw [image_parallelepiped]
  rw [b_eq_scale_onb]
  simp
  rw [Basis.coe_map]
  simp

lemma para_b_vol : μ (parallelepiped b) = 4 := by
  rw [b_is_img]
  rw [map_linearMap_volume_eq_smul_volume S_2.toLinearMap]
  rw [OrthonormalBasis.volume_parallelepiped]
  rw [det_S_2]
  simp

lemma square_vol : μ square = 4 := by
  rw [mu_T_A]
  rw [T_A_square]
  rw [para_b_vol]

theorem triangle_union_vol :
    μ (triangle_A ∪ triangle_C') = 4 := by
  rw [triangle_union']
  rw [square_vol]

def F : E →ₗ[ℝ] E := (-1 : ℝ) • LinearMap.id

lemma det_F : F.det = 1 := by
  unfold F
  rw [LinearMap.det_smul]
  simp

lemma triangle_A_hull : triangle_A = convexHull ℝ {A, B, D} := by
  unfold triangle_A diagonal
  have : segment ℝ A A = {A} := by simp
  rw [← this]
  rw [convexJoin_segments]
  simp
  have : {B, D, A} = ({A, B, D} : Set E) := by
    aesop
  rw [this]

lemma triangle_C'_hull : triangle_C' = convexHull ℝ {C', B, D} := by
  unfold triangle_C' diagonal
  have : segment ℝ C' C' = {C'} := by simp
  rw [← this]
  rw [convexJoin_segments]
  simp
  have : {B, D, C'} = ({C', B, D} : Set E) := by
    aesop
  rw [this]

lemma map_F_triangle : triangle_C' = F '' triangle_A := by
  rw [triangle_A_hull]
  rw [triangle_C'_hull]
  rw [LinearMap.image_convexHull]
  congr
  simp
  rw [Set.image_insert_eq, Set.image_pair]
  have : F A = C' := by
    unfold F A C'
    simp
    ext i
    fin_cases i <;> simp
  rw [this]
  have : F B = D := by
    unfold F B D
    simp
    ext i
    fin_cases i <;> simp
  rw [this]
  have : F D = B := by
    unfold F B D
    simp
    ext i
    fin_cases i <;> simp
  rw [this]
  aesop

theorem triangle_vol_eq : μ (triangle_A) = μ (triangle_C') := by
  rw [map_F_triangle]
  rw [map_linearMap_volume_eq_smul_volume F]
  rw [det_F]
  simp

theorem triangle_vol_eq_2 :
    μ (triangle_A) = 2 := by
  have : μ (triangle_A) + μ (triangle_C') = 4 := by
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
