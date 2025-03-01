import Trapezoid.Triangle

notation "E" => EuclideanSpace ℝ (Fin 2)
#check finTwoArrowEquiv

lemma subspace_volume_zero
    (S : AffineSubspace ℝ E) (h : S ≠ ⊤) :
    μ S.carrier = 0 :=
  MeasureTheory.Measure.addHaar_affineSubspace _ _ h

lemma finrank_fin_prod : Module.finrank ℝ E = 2 := by
  aesop

lemma rank_span_singleton_one (v : E) :
    Module.rank ℝ (Submodule.span ℝ {v}) ≤ 1 := by
  rw [rank_submodule_le_one_iff]
  use v
  simp
  exact Submodule.mem_span_singleton_self v

lemma finrank_span_singleton_one (v : E) :
    Module.finrank ℝ (Submodule.span ℝ {v}) ≤ 1 := by
  refine Module.finrank_le_of_rank_le ?_
  exact rank_span_singleton_one v

lemma vectorspan_singleton_ne_top (v : E) :
    Submodule.span ℝ {v} < ⊤ := by
  apply Submodule.lt_top_of_finrank_lt_finrank
  rw [finrank_fin_prod]
  have := finrank_span_singleton_one v
  linarith

lemma affinespan_pair_ne_top (a b : E) :
    affineSpan ℝ {a, b} < ⊤ := by
  by_contra h
  simp at h
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty] at h
  rw [vectorSpan_pair] at h
  have := vectorspan_singleton_ne_top (a -ᵥ b)
  rw [← h] at this
  aesop
  simp

lemma affinespan_volume (a b : E) :
    μ (affineSpan ℝ {a, b}).carrier = 0 := by
  apply MeasureTheory.Measure.addHaar_affineSubspace
  apply ne_top_of_lt (affinespan_pair_ne_top a b)
