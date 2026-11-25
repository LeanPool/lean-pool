/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.BallSubmean
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.CompactDiscLocalization

/-!
# Uniform small discs for compact families of PSH germs

A Lebesgue number for an open cover by actual disc-PSH neighborhoods gives
one radius bound valid at all centers in a compact set. The chosen neighborhood
may depend on the center. No local-to-global assertion for arbitrary large
affine discs is used.
-/

@[expose] public section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {u : E → EReal} {U K : Set E}

/-- Ambient PSH germs are upper semicontinuous on their domain. -/
theorem PlurisubharmonicOn.upperSemicontinuousOn (hu : PlurisubharmonicOn u U) :
    UpperSemicontinuousOn u U := by
  intro x hx c hc
  exact nhdsWithin_le_nhds ((hu x hx).upperSemicontinuousAt c hc)

/-- A compact set of PSH germs has a nonnegative finite upper bound, including
when the compact set is empty or the potential is identically negative infinity. -/
theorem PlurisubharmonicOn.exists_nonnegative_compact_upper_bound
    (hu : PlurisubharmonicOn u U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, u x ≤ (C : EReal) := by
  by_cases hne : K.Nonempty
  · obtain ⟨y, hy, hmax⟩ :=
      (hu.upperSemicontinuousOn.mono hKU).exists_isMaxOn hne hK
    obtain ⟨B, hB, _⟩ := EReal.exists_rat_btwn_of_lt
      (lt_top_iff_ne_top.mpr ((hu y (hKU hy)).ne_top))
    refine ⟨Max.max (B : ℝ) 0, le_max_right _ _, ?_⟩
    intro x hx
    exact ((hmax hx).trans hB.le).trans
      (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  · exact ⟨0, le_rfl, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

/-- One positive radius works for all centers in a compact set, each inside
one of the original disc-PSH neighborhoods witnessing its germ. -/
theorem PlurisubharmonicOn.exists_uniform_disc_neighborhoods
    (hu : PlurisubharmonicOn u U) (hK : IsCompact K) (hKU : K ⊆ U) (v : E) :
    ∃ R > 0, ∀ x ∈ K, ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ DiscPshOn u W ∧
      ∀ r : ℝ, r ≤ R → affineClosedDisc x v r ⊆ W := by
  classical
  choose W hW hxW huW using fun x : K => hu x (hKU x.property)
  have hcover : K ⊆ ⋃ x : K, W x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  obtain ⟨δ, hδ, hballs⟩ := lebesgue_number_lemma_of_metric hK hW hcover
  let R : ℝ := δ / (2 * (‖v‖ + 1))
  have hden : 0 < 2 * (‖v‖ + 1) := by positivity
  have hR : 0 < R := div_pos hδ hden
  have hRmul : R * (2 * (‖v‖ + 1)) = δ := div_mul_cancel₀ δ (ne_of_gt hden)
  have hRδ : R * ‖v‖ < δ := by nlinarith [norm_nonneg v]
  refine ⟨R, hR, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hballs x hx
  refine ⟨W i, hW i, hi (mem_ball_self hδ), huW i, ?_⟩
  intro r hr y hy
  apply hi
  have hdist := mem_closedBall.mp (affineClosedDisc_subset_closedBall x v r hy)
  exact mem_ball.mpr (hdist.trans_lt
    ((mul_le_mul_of_nonneg_right hr (norm_nonneg v)).trans_lt hRδ))

/-- The original deficit criterion holds uniformly for sufficiently small
discs centered in a compact family of PSH germs, with any admissible majorant. -/
theorem PlurisubharmonicOn.exists_uniform_circleDeficit_bound
    (hu : PlurisubharmonicOn u U) (hK : IsCompact K) (hKU : K ⊆ U) (v : E) :
    ∃ R > 0, ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ R → ∀ C : ℝ,
      (∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal)) →
      circleDeficit u x v r C ≤
        ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - u x).toENNReal := by
  obtain ⟨R, hR, hlocal⟩ := hu.exists_uniform_disc_neighborhoods hK hKU v
  refine ⟨R, hR, ?_⟩
  intro x hx r hr hrR C hC
  obtain ⟨W, _, _, hW, hdisc⟩ := hlocal x hx
  exact hW.submean x v r hr (hdisc r hrR) C hC

variable [MeasurableSpace E] [BorelSpace E]

/-- Upper semicontinuity of PSH germs gives a measurable zero extension of
their deficit on any measurable subset of the germ domain. -/
theorem PlurisubharmonicOn.measurable_indicator_deficit (hu : PlurisubharmonicOn u U)
    (hK : MeasurableSet K) (hKU : K ⊆ U) (C : ℝ) :
    Measurable (K.indicator (fun x => ((C : EReal) - u x).toENNReal)) :=
  measurable_indicator_deficit_of_upperSemicontinuousOn hu.upperSemicontinuousOn hK hKU C

end SGPT.Foundations.Analysis
