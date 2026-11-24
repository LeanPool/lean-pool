/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM12.Section4PathFacts
import LeanPool.GraphMinor.GM12.Section4DrawingControl
import LeanPool.GraphMinor.GM12.Section4BranchImage
import LeanPool.GraphMinor.GM12.Section4SpanSeparation
import LeanPool.GraphMinor.GM16.HypergraphImage
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Carrying a controlled drawing minor into its ambient graph

The embedded-graph form of XII (4.3), page 249, relabels each branch
and joining edge through the drawing embedding. The embedding
preserves all edge ends, so the images are subhypergraphs and the
loop condition is preserved. Pull back an ambient small separation.
The controlling-tangle condition puts this separation in the drawing
tangle, where the original branch cannot lie on its small side.
-/

public section

namespace GraphMinor.GM12

open Set Graph Surface Hypergraph GM10 GM11 GM14 GM15 GM16

private theorem span_image_hypergraph_le
    {S α β : Type*} [TopologicalSpace S] {G : Graph α β}
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (H : Drawing S) (η : SpanEmbedding H G) :
    imageHypergraph η.vMap η.eMap H.toHypergraph ≤ Hypergraph.ofGraph G hV hE := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact η.imageGraph_le.vertexSet_mono (η.bijOn_v.mapsTo hx)
  · rintro _ ⟨e, he, rfl⟩
    exact η.imageGraph_le.edgeSet_mono (η.bijOn_e.mapsTo he)
  · rintro _ ⟨e, he, rfl⟩
    ext x
    constructor
    · rintro ⟨y, hxy⟩
      have him : η.imageGraph.IsLink (η.eMap e) x y :=
        (η.imageGraph_le.isLink_iff (η.bijOn_e.mapsTo he)).mpr hxy
      obtain ⟨v, hv, hvx⟩ := η.bijOn_v.surjOn him.left_mem
      have hcl : v ∈ closure e := (η.inc_iff e he v hv).mp (hvx ▸ him.inc_left)
      exact ⟨e, v, ⟨he, hv, hcl⟩, rfl, hvx⟩
    · rintro ⟨f, v, hinc, hfe, hvx⟩
      have hfe' : f = e := η.bijOn_e.injOn hinc.1 he hfe
      subst f
      obtain ⟨w, hlink⟩ := (η.inc_iff e he v hinc.2.1).mpr hinc.2.2
      exact ⟨w, hvx ▸ (η.imageGraph_le.isLink_iff (η.bijOn_e.mapsTo he)).mp hlink⟩

/-- Carry connected disjoint subdrawings through a drawing embedding,
retaining their exact vertex images for the path attachment in XII
(4.4), page 252. -/
theorem exists_embedded_connecting_branches
    {S α β : Type*} [TopologicalSpace S] {G : Graph α β}
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) {H : Drawing S}
    (η : SpanEmbedding H G) {W : Type*} (D : W → Drawing S)
    (hD : ∀ v, (D v).IsSubdrawing H)
    (hne : ∀ v, (D v).V.Nonempty) (hconn : ∀ v, IsConnectedDrawing (D v))
    (hdisj : ∀ v w, v ≠ w → Disjoint (D v).V (D w).V) :
    ∃ A : W → Hypergraph α β,
      (∀ v, A v ≤ Hypergraph.ofGraph G hV hE ∧
        (A v).vertexSet.Nonempty ∧ IsConnectedSub (A v)) ∧
      (∀ v w, v ≠ w → Disjoint (A v).vertexSet (A w).vertexSet) ∧
      ∀ v, (A v).vertexSet = η.vMap '' (D v).V := by
  let A := fun v => imageHypergraph η.vMap η.eMap (D v).toHypergraph
  have hsub : ∀ v, (D v).toHypergraph ≤ H.toHypergraph :=
    fun v => subdrawing_toHypergraph_le (hD v)
  have hImage := span_image_hypergraph_le hV hE H η
  refine ⟨A, ?_, ?_, fun _ => rfl⟩
  · intro v
    refine ⟨(imageHypergraph_mono_on η.vMap η.eMap η.bijOn_e.injOn (hsub v)).trans hImage,
      (hne v).image η.vMap, ?_⟩
    exact isConnectedSub_imageHypergraph η.vMap η.eMap
      (η.bijOn_v.injOn.mono (hD v).1)
      (isConnectedSub_toHypergraph_of_connected_drawing (hconn v))
  · intro v w hvw
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, hxe⟩ ⟨y, hy, hye⟩
    have hxy := η.bijOn_v.injOn ((hD v).1 hx) ((hD w).1 hy) (hxe.trans hye.symm)
    exact Set.disjoint_left.mp (hdisj v w hvw) hx (hxy.symm ▸ hy)

/-- Transfer a controlled minor from a drawing tangle to the
ambient tangle controlling it through a drawing embedding. -/
theorem controlsMinor_of_controlling_drawing_tangle
    {S α β γ δ : Type*} [TopologicalSpace S] {G : Graph α β} {H : Drawing S}
    (η : SpanEmbedding H G) {θstar θ : ℕ}
    {Tstar : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hC : IsControllingTangle G H η θstar θ Tstar T) {L : Graph γ δ}
    (hc : ControlsMinor H.toHypergraph θ T L) :
    ControlsMinor (Hypergraph.ofGraph G hC.isTangle_star.finite_V hC.isTangle_star.finite_E)
      θstar Tstar L := by
  obtain ⟨a, b, ha, hdisj, hlink, hloop, hinj, hcard, hcontrol⟩ := hc
  let G' := Hypergraph.ofGraph G hC.isTangle_star.finite_V hC.isTangle_star.finite_E
  have hImage : imageHypergraph η.vMap η.eMap H.toHypergraph ≤ G' :=
    span_image_hypergraph_le hC.isTangle_star.finite_V hC.isTangle_star.finite_E H η
  have hbE : ∀ e ∈ L.edgeSet, b e ∈ H.E := by
    intro e he
    obtain ⟨v, w, hl⟩ := L.exists_isLink_of_mem_edgeSet he
    by_cases hvw : v = w
    · subst w
      exact (hloop e v hl).1
    · exact (hlink e v w hl hvw).1
  have hmapinc : ∀ e ∈ H.E, ∀ x, G'.Inc (η.eMap e) x ↔
      ∃ v, H.toHypergraph.Inc e v ∧ η.vMap v = x := by
    intro e he x
    have heImage : η.eMap e ∈ (imageHypergraph η.vMap η.eMap H.toHypergraph).edgeSet :=
      mem_image_of_mem η.eMap he
    constructor
    · intro hi
      have him := (inc_iff_of_le hImage heImage).mpr hi
      obtain ⟨f, v, hfv, hfe, hvx⟩ := him
      have hfe' := η.bijOn_e.injOn hfv.1 he hfe
      subst f
      exact ⟨v, hfv, hvx⟩
    · rintro ⟨v, hi, hvx⟩
      exact (inc_iff_of_le hImage heImage).mp ⟨e, v, hi, rfl, hvx⟩
  refine ⟨fun v => imageHypergraph η.vMap η.eMap (a v), fun e => η.eMap (b e),
    ?_, ?_, ?_, ?_, ?_, hcard.trans hC.theta_le, ?_⟩
  · intro v hv
    refine ⟨(imageHypergraph_mono_on η.vMap η.eMap η.bijOn_e.injOn (ha v hv).1).trans hImage,
      (ha v hv).2.1.image η.vMap, ?_⟩
    exact isConnectedSub_imageHypergraph η.vMap η.eMap
      (η.bijOn_v.injOn.mono (ha v hv).1.vertexSet_subset) (ha v hv).2.2
  · intro u hu v hv huv
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, hxe⟩ ⟨y, hy, hye⟩
    have hxy := η.bijOn_v.injOn ((ha u hu).1.vertexSet_subset hx)
      ((ha v hv).1.vertexSet_subset hy) (hxe.trans hye.symm)
    exact Set.disjoint_left.mp (hdisj u hu v hv huv) hx (hxy.symm ▸ hy)
  · intro e u v hl huv
    obtain ⟨he, hx, hy⟩ := hlink e u v hl huv
    obtain ⟨x, hx, hix⟩ := hx
    obtain ⟨y, hy, hiy⟩ := hy
    refine ⟨hImage.edgeSet_subset (mem_image_of_mem η.eMap he),
      ⟨η.vMap x, mem_image_of_mem η.vMap hx, (hmapinc _ he _).mpr ⟨x, hix, rfl⟩⟩,
      η.vMap y, mem_image_of_mem η.vMap hy, (hmapinc _ he _).mpr ⟨y, hiy, rfl⟩⟩
  · intro e v hl
    obtain ⟨he, hnot, hends⟩ := hloop e v hl
    refine ⟨hImage.edgeSet_subset (mem_image_of_mem η.eMap he), ?_, ?_⟩
    · rintro ⟨f, hf, hfe⟩
      have heq := η.bijOn_e.injOn ((ha v hl.left_mem).1.edgeSet_subset hf) he hfe
      exact hnot (heq ▸ hf)
    · intro x hix
      obtain ⟨y, hiy, hyx⟩ := (hmapinc _ he x).mp hix
      exact ⟨y, hends y hiy, hyx⟩
  · intro e he f hf hef heq
    exact hinj e he f hf hef (η.bijOn_e.injOn (hbE e he) (hbE f hf) heq)
  · intro A B hAB horder v hv hsmall
    have hsep := hC.isTangle_star.isTangle.isSeparation hAB
    obtain ⟨AH, BH, hRestr, hAV, _, _, _, horderH⟩ :=
      exists_span_restricted_separation hC.isTangle_star.finite_V hC.isTangle_star.finite_E H η hsep
    have hθorder : separationOrder A B < θ := horder.trans_le hcard
    have hmem : (AH, BH) ∈ T := (hC.controls hsep hθorder hRestr).mp hAB
    apply hcontrol AH BH hmem (horderH.trans_lt horder) v hv
    intro x hx
    rw [hAV]
    exact ⟨(ha v hv).1.vertexSet_subset hx, hsmall (mem_image_of_mem η.vMap hx)⟩

end GraphMinor.GM12
