/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Baire.BaireMeasurable

/-!
# `C¹` maps between spaces of the same dimension send meagre sets to meagre sets

Let `E` be a finite-dimensional real normed space and `f` a `C¹` map on an open set `A ⊆ E`, with
values in `E`. Then `f` sends meagre subsets of `A` to meagre sets: near a regular point `f` is a
local homeomorphism (inverse function theorem), and the image of the critical set is a countable
union of compact sets of Haar measure zero (Sard's lemma for equal dimensions).

## Main statements

* `ContDiffOn.isNowhereDense_image_inter_det_fderiv_eq_zero`: for a compact `C ⊆ A`, the image
  of the critical points lying in `C` is nowhere dense.
* `ContDiffOn.isMeagre_image_inter_det_fderiv_eq_zero`: the image of the critical set is meagre.
* `ContDiffOn.exists_mem_nhds_isMeagre_image`: near a regular point, `f` sends meagre sets to
  meagre sets.
* `ContDiffOn.isMeagre_image`: `f` sends meagre subsets of `A` to meagre sets.
-/

public section

open Set Filter Topology MeasureTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {A : Set E} {f : E → E}

/-- For a `C¹` map on an open set `A` and a compact `C ⊆ A`, the image of the critical points
lying in `C` is nowhere dense. -/
theorem ContDiffOn.isNowhereDense_image_inter_det_fderiv_eq_zero (hf : ContDiffOn ℝ 1 f A)
    (hA : IsOpen A) {C : Set E} (hC : IsCompact C) (hCA : C ⊆ A) :
    IsNowhereDense (f '' (C ∩ {x | (fderiv ℝ f x).det = 0})) := by
  borelize E
  have hdiff : ∀ x ∈ A, DifferentiableAt ℝ f x := fun x hx =>
    (hf.contDiffAt (hA.mem_nhds hx)).differentiableAt one_ne_zero
  have hdet : ContinuousOn (fun x => (fderiv ℝ f x).det) A :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hA le_rfl)
  have hclosed : IsClosed (C ∩ {x | (fderiv ℝ f x).det = 0}) :=
    (hdet.mono hCA).preimage_isClosed_of_isClosed hC.isClosed isClosed_singleton
  have hcpt : IsCompact (f '' (C ∩ {x | (fderiv ℝ f x).det = 0})) :=
    (hC.of_isClosed_subset hclosed inter_subset_left).image_of_continuousOn
      (hf.continuousOn.mono (inter_subset_left.trans hCA))
  have hnull : (Measure.addHaar : Measure E) (f '' (C ∩ {x | (fderiv ℝ f x).det = 0})) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero Measure.addHaar
      (fun x hx => (hdiff x (hCA hx.1)).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx.2)
  exact IsNowhereDense.of_isClosed_null (μ := Measure.addHaar) hcpt.isClosed hnull

/-- For a `C¹` map on an open set `A`, the image of the critical points in `A` is meagre. -/
theorem ContDiffOn.isMeagre_image_inter_det_fderiv_eq_zero (hf : ContDiffOn ℝ 1 f A)
    (hA : IsOpen A) :
    IsMeagre (f '' (A ∩ {x | (fderiv ℝ f x).det = 0})) := by
  have hball : ∀ x, ∃ r : ℝ, x ∈ A → 0 < r ∧ Metric.closedBall x r ⊆ A := by
    intro x
    by_cases hx : x ∈ A
    · obtain ⟨r, hr, hrA⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hA.mem_nhds hx)
      exact ⟨r, fun _ => ⟨hr, hrA⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose r hr using hball
  obtain ⟨t, htA, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := A) (f := fun x => Metric.closedBall x (r x))
    fun x hx => mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x (hr x hx).1)
  refine (isMeagre_biUnion htc fun x hx =>
    (hf.isNowhereDense_image_inter_det_fderiv_eq_zero hA (isCompact_closedBall x (r x))
      (hr x (htA hx)).2).isMeagre).mono ?_
  rintro _ ⟨y, ⟨hyA, hyc⟩, rfl⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hcover hyA)
  exact mem_iUnion₂.2 ⟨x, hx, y, ⟨hyx, hyc⟩, rfl⟩

/-- Near a regular point of a `C¹` map, the image of a meagre set is meagre. -/
theorem ContDiffOn.exists_mem_nhds_isMeagre_image (hf : ContDiffOn ℝ 1 f A) (hA : IsOpen A) {x : E}
    (hx : x ∈ A) (hreg : (fderiv ℝ f x).det ≠ 0) :
    ∃ U ∈ 𝓝 x, ∀ B : Set E, IsMeagre B → IsMeagre (f '' (B ∩ U)) := by
  set L := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hreg
  have hstrict : HasStrictFDerivAt f (L : E →L[ℝ] E) x := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hf.contDiffAt (hA.mem_nhds hx)).hasStrictFDerivAt_fderiv one_ne_zero
  set e := hstrict.toOpenPartialHomeomorph f
  refine ⟨e.source, e.open_source.mem_nhds hstrict.mem_toOpenPartialHomeomorph_source,
    fun B hB => ?_⟩
  have hB' : IsMeagre ((Subtype.val : e.source → E) ⁻¹' B) :=
    hB.preimage_of_isOpenMap continuous_subtype_val e.open_source.isOpenMap_subtype_val
  have himg := e.isOpenEmbedding_restrict.isInducing.isMeagre_image hB'
  convert himg using 1
  ext z
  constructor
  · rintro ⟨y, ⟨hyB, hys⟩, rfl⟩
    exact ⟨⟨y, hys⟩, hyB, rfl⟩
  · rintro ⟨⟨y, hys⟩, hyB, rfl⟩
    exact ⟨y, ⟨hyB, hys⟩, rfl⟩

/-- A `C¹` map from an open subset `A` of `E` to `E` sends meagre subsets of `A` to meagre
subsets of `E`. (Since `A` is open, a subset of `A` is meagre in `A` exactly when it is meagre in
`E`.) -/
theorem ContDiffOn.isMeagre_image (hf : ContDiffOn ℝ 1 f A) (hA : IsOpen A) {B : Set E}
    (hBA : B ⊆ A) (hB : IsMeagre B) : IsMeagre (f '' B) := by
  have hloc : ∀ x, ∃ U : Set E, x ∈ A → (fderiv ℝ f x).det ≠ 0 →
      U ∈ 𝓝 x ∧ IsMeagre (f '' (B ∩ U)) := by
    intro x
    by_cases h : x ∈ A ∧ (fderiv ℝ f x).det ≠ 0
    · obtain ⟨U, hU, hUB⟩ := hf.exists_mem_nhds_isMeagre_image hA h.1 h.2
      exact ⟨U, fun _ _ => ⟨hU, hUB B hB⟩⟩
    · exact ⟨univ, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose U hU using hloc
  set R := A \ {x | (fderiv ℝ f x).det = 0}
  obtain ⟨t, htR, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := R)
    (f := U) fun x hx => mem_nhdsWithin_of_mem_nhds (hU x hx.1 hx.2).1
  have hreg : IsMeagre (⋃ x ∈ t, f '' (B ∩ U x)) :=
    isMeagre_biUnion htc fun x hx => (hU x (htR hx).1 (htR hx).2).2
  refine ((hf.isMeagre_image_inter_det_fderiv_eq_zero hA).union hreg).mono ?_
  rintro _ ⟨y, hyB, rfl⟩
  by_cases hyc : y ∈ {x | (fderiv ℝ f x).det = 0}
  · exact Or.inl ⟨y, ⟨hBA hyB, hyc⟩, rfl⟩
  · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hcover ⟨hBA hyB, hyc⟩)
    exact Or.inr (mem_iUnion₂.2 ⟨x, hx, y, ⟨hyB, hyx⟩, rfl⟩)

end
