import Trapezoid.Defs

lemma vectorspan_volume (v : E) : μ (Submodule.span ℝ {v}).carrier = 0 := by
  apply MeasureTheory.Measure.addHaar_submodule
  rw [← lt_top_iff_ne_top]
  apply span_lt_top_of_card_lt_finrank
  simp
