/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.SegregationDrawing

/-!
# Replacing one member of a segregation

This is the first half of the proof of Claim (1) of (8.4) (page 41). We replace `(A, Ω)` by `(A',
Ω)`,
where `A'` is a smaller subgraph that holds `ΩBar` and `H ∩ A`, and that has an edge. All the
conditions
stay true, and the arrangement stays the same. As the paper says, the edge of `A'` keeps the new
society from already being in the segregation.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface GraphMinor.GM11

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- Two subgraphs with the same vertices and edges are equal. -/
theorem eq_of_le_le {G A B : Graph α β} (hA : A ≤ G) (hB : B ≤ G) (hV : V(A) = V(B))
    (hE : E(A) = E(B)) : A = B :=
  le_antisymm (le_of_subset_of_subset hA hB hV.subset hE.subset)
    (le_of_subset_of_subset hB hA hV.superset hE.superset)

private theorem replacing_smaller_society_decreases_size
    {α : Type u}
    {β : Type v}
    {G₁ : Graph α β}
    {S_seg : Set (Society α β)}
    (hVf : V(G₁).Finite)
    (hEf : E(G₁).Finite)
    {S₀ : Society α β}
    (hS₀ : S₀ ∈ S_seg)
    {A' : Graph α β}
    (hA' : A' ≤ S₀.G)
    (hbar : S₀.Ω.bar ⊆ V(A'))
    (hne : A' ≠ S₀.G)
    (hs : IsGraphSegregation G₁ S_seg)
    (hS₀G : S₀.G ≤ G₁)
    (G₁' : Graph α β)
    (hV' : V(G₁') = V(A') ∪ ⋃ S₁ ∈ S_seg \ {S₀}, V(S₁.G))
    (hE' : E(G₁') = E(A') ∪ ⋃ S₁ ∈ S_seg \ {S₀}, E(S₁.G))
    (hVsub : V(G₁') ⊆ V(G₁))
    (hEsub : E(G₁') ⊆ E(G₁))
    (hcount₁ : V(G₁').ncard ≤ V(G₁).ncard)
    (hcount₂ : E(G₁').ncard ≤ E(G₁).ncard) :
    V(G₁').ncard + E(G₁').ncard < V(G₁).ncard + E(G₁).ncard := by
  by_cases hV'eq : V(A') = V(S₀.G)
  · have hEne : E(A') ≠ E(S₀.G) := fun h => hne (eq_of_le_le hA' le_rfl hV'eq h)
    obtain ⟨e, heS, heA⟩ : ∃ e ∈ E(S₀.G), e ∉ E(A') := by
      by_contra hcon
      push Not at hcon
      exact hEne (Subset.antisymm hA'.edgeSet_mono hcon)
    have : e ∉ E(G₁') := by
      rw [hE']
      rintro (h | h)
      · exact heA h
      · obtain ⟨S₁, ⟨h₁, hn₁⟩, h⟩ := mem_iUnion₂.mp h
        exact disjoint_left.mp (hs.edge_disjoint S₀ hS₀ S₁ h₁ (Ne.symm hn₁)) heS h
    have hlt := ncard_lt_ncard (⟨hEsub, fun h => this (h (hS₀G.edgeSet_mono heS))⟩ :
      E(G₁') ⊂ E(G₁)) hEf
    omega
  · obtain ⟨x, hxS, hxA⟩ : ∃ x ∈ V(S₀.G), x ∉ V(A') := by
      by_contra hcon
      push Not at hcon
      exact hV'eq (Subset.antisymm hA'.vertexSet_mono hcon)
    have : x ∉ V(G₁') := by
      rw [hV']
      rintro (h | h)
      · exact hxA h
      · obtain ⟨S₁, ⟨h₁, hn₁⟩, h⟩ := mem_iUnion₂.mp h
        exact hxA (hbar (hs.vertex_inter_subset S₀ hS₀ S₁ h₁ (Ne.symm hn₁) ⟨hxS, h⟩).1)
    have hlt := ncard_lt_ncard (⟨hVsub, fun h => this (h (hS₀G.vertexSet_mono hxS))⟩ :
      V(G₁') ⊂ V(G₁)) hVf
    omega

/-- See the module docstring. -/
theorem exists_replacement {H : Drawing S} {G₁ : Graph α β} {η : SpanEmbedding H G₁}
    {S_seg : Set (Society α β)} {α_disc : Society α β → Set S} {α_pt : α → S}
    (hVf : V(G₁).Finite) (hEf : E(G₁).Finite)
    (hseg : IsThreeSegregation G₁ S_seg) (harr : IsSurfaceArrangement S_seg α_disc α_pt)
    (hcompat : IsCompatibleWith G₁ H η S_seg α_disc α_pt) {S₀ : Society α β} (hS₀ : S₀ ∈ S_seg)
    {A' : Graph α β} (hA' : A' ≤ S₀.G) (hbar : S₀.Ω.bar ⊆ V(A')) (hH : pieceGraph η S₀.G ≤ A')
    (hE : E(A').Nonempty) (hne : A' ≠ S₀.G) :
    ∃ (S_seg' : Set (Society α β)) (α_disc' : Society α β → Set S) (G₁' : Graph α β)
      (η' : SpanEmbedding H G₁'),
      G₁' ≤ G₁ ∧ IsThreeSegregation G₁' S_seg' ∧ IsSurfaceArrangement S_seg' α_disc' α_pt ∧
      IsCompatibleWith G₁' H η' S_seg' α_disc' α_pt ∧
      segregationVertices S_seg' = segregationVertices S_seg ∧
      η'.imageGraph = η.imageGraph ∧ η'.vMap = η.vMap ∧ η'.eMap = η.eMap ∧
      (∀ S' ∈ S_seg', ∃ S₁ ∈ S_seg, α_disc' S' = α_disc S₁) ∧
      V(G₁').ncard + E(G₁').ncard < V(G₁).ncard + E(G₁).ncard ∧
      V(G₁') = V(A') ∪ ⋃ S₁ ∈ S_seg \ {S₀}, V(S₁.G) ∧
      E(G₁') = E(A') ∪ ⋃ S₁ ∈ S_seg \ {S₀}, E(S₁.G) := by
  classical
  obtain ⟨hs, h3⟩ := hseg
  have hS₀G := hs.le S₀ hS₀
  have hVG : V(G₁) = ⋃ S₁ ∈ S_seg, V(S₁.G) := by
    conv_lhs => rw [← hs.union_eq]
    simp [vertexSet_subgraphSUnion]
  have hEG : E(G₁) = ⋃ S₁ ∈ S_seg, E(S₁.G) := by
    conv_lhs => rw [← hs.union_eq]
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨S₁, hS₁, rfl⟩; exact hs.le S₁ hS₁)]
    simp
  have hA'V : ∀ x ∈ V(A'), x ∈ V(G₁) := fun x hx => hS₀G.vertexSet_mono (hA'.vertexSet_mono hx)
  let S₀' : Society α β := ⟨A', S₀.Ω, S₀.finite_V.subset hA'.vertexSet_mono,
    S₀.finite_E.subset hA'.edgeSet_mono, hbar⟩
  have hS₀'S₀ : S₀' ≠ S₀ := fun h => hne (congrArg Society.G h)
  have hS₀'E : ∀ S₁ ∈ S_seg, S₁ ≠ S₀ → Disjoint E(A') E(S₁.G) := fun S₁ hS₁ h =>
    (hs.edge_disjoint S₀ hS₀ S₁ hS₁ (Ne.symm h)).mono_left hA'.edgeSet_mono
  have hS₀'not : S₀' ∉ S_seg := by
    intro hin
    obtain ⟨e, he⟩ := hE
    exact disjoint_left.mp (hS₀'E S₀' hin hS₀'S₀) he he
  let S_seg' : Set (Society α β) := insert S₀' (S_seg \ {S₀})
  let α_disc' : Society α β → Set S := Function.update α_disc S₀' (α_disc S₀)
  have hd₀ : α_disc' S₀' = α_disc S₀ := Function.update_self ..
  have hd₁ : ∀ S₁ ∈ S_seg, α_disc' S₁ = α_disc S₁ := fun S₁ hS₁ =>
    Function.update_of_ne (fun (h : S₁ = S₀') => hS₀'not (h ▸ hS₁)) ..
  -- The new graph.
  let G₁' : Graph α β := subgraphSUnion G₁ ((fun S₁ : Society α β => S₁.G) '' S_seg')
  have hpiece : ∀ T ∈ (fun S₁ : Society α β => S₁.G) '' S_seg', T ≤ G₁ := by
    rintro _ ⟨S₁, rfl | ⟨hS₁, -⟩, rfl⟩
    · exact hA'.trans hS₀G
    · exact hs.le S₁ hS₁
  have hG₁'le : G₁' ≤ G₁ := subgraphSUnion_le hpiece
  have hV' : V(G₁') = V(A') ∪ ⋃ S₁ ∈ S_seg \ {S₀}, V(S₁.G) := by
    simp only [G₁', vertexSet_subgraphSUnion, S_seg', biUnion_image, biUnion_insert]
    rfl
  have hE' : E(G₁') = E(A') ∪ ⋃ S₁ ∈ S_seg \ {S₀}, E(S₁.G) := by
    simp only [G₁']
    rw [edgeSet_subgraphSUnion hpiece]
    simp only [S_seg', biUnion_image, biUnion_insert]
    rfl
  have hle' : ∀ S' ∈ S_seg', S'.G ≤ G₁' := by
    rintro S' (rfl | ⟨hS₁, hne₁⟩)
    · refine le_of_subset_of_subset (hA'.trans hS₀G) hG₁'le ?_ ?_
      · rw [hV']
        exact subset_union_left
      · rw [hE']
        exact subset_union_left
    · refine le_of_subset_of_subset (hs.le S' hS₁) hG₁'le ?_ ?_
      · rw [hV']
        exact (subset_biUnion_of_mem (u := fun S₁ : Society α β => V(S₁.G))
          (show S' ∈ S_seg \ {S₀} from ⟨hS₁, hne₁⟩)).trans subset_union_right
      · rw [hE']
        exact (subset_biUnion_of_mem (u := fun S₁ : Society α β => E(S₁.G))
          (show S' ∈ S_seg \ {S₀} from ⟨hS₁, hne₁⟩)).trans subset_union_right
  have hseg' : IsThreeSegregation G₁' S_seg' := by
    refine ⟨⟨(hs.finite.subset sdiff_subset).insert _, hle', ?_, ?_, ?_⟩, ?_⟩
    · refine eq_of_le_le (subgraphSUnion_le ?_) le_rfl ?_ ?_
      · rintro _ ⟨S₁, hS₁, rfl⟩
        exact hle' S₁ hS₁
      · rfl
      · rw [edgeSet_subgraphSUnion]
        · simp only [G₁']
          rw [edgeSet_subgraphSUnion hpiece]
        · rintro _ ⟨S₁, hS₁, rfl⟩
          exact hle' S₁ hS₁
    · rintro S₁ (rfl | ⟨h₁, hn₁⟩) S₂ (rfl | ⟨h₂, hn₂⟩) hne₁₂
      · exact absurd rfl hne₁₂
      · have := hs.vertex_inter_subset S₀ hS₀ S₂ h₂ (Ne.symm hn₂)
        exact (inter_subset_inter_left _ hA'.vertexSet_mono).trans this
      · have := hs.vertex_inter_subset S₁ h₁ S₀ hS₀ hn₁
        exact (inter_subset_inter_right _ hA'.vertexSet_mono).trans this
      · exact hs.vertex_inter_subset S₁ h₁ S₂ h₂ hne₁₂
    · rintro S₁ (rfl | ⟨h₁, hn₁⟩) S₂ (rfl | ⟨h₂, hn₂⟩) hne₁₂
      · exact absurd rfl hne₁₂
      · exact hS₀'E S₂ h₂ hn₂
      · exact (hS₀'E S₁ h₁ hn₁).symm
      · exact hs.edge_disjoint S₁ h₁ S₂ h₂ hne₁₂
    · rintro S₁ (rfl | ⟨h₁, -⟩)
      · exact h3 S₀ hS₀
      · exact h3 S₁ h₁
  have hsegV : segregationVertices S_seg' = segregationVertices S_seg := by
    simp only [segregationVertices]
    ext x
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨S₁, rfl | ⟨h₁, -⟩, hx⟩
      · exact ⟨S₀, hS₀, hx⟩
      · exact ⟨S₁, h₁, hx⟩
    · rintro ⟨S₁, h₁, hx⟩
      by_cases h : S₁ = S₀
      · subst h
        exact ⟨S₀', Or.inl rfl, hx⟩
      · exact ⟨S₁, Or.inr ⟨h₁, h⟩, hx⟩
  -- The image of `H`.
  have hIV : ∀ v ∈ H.V, η.vMap v ∈ V(S₀.G) → η.vMap v ∈ V(A') := fun v hv h =>
    hH.vertexSet_mono ⟨η.bijOn_v.mapsTo hv, h⟩
  have hIE : ∀ e ∈ H.E, η.eMap e ∈ E(S₀.G) → η.eMap e ∈ E(A') := fun e he h =>
    hH.edgeSet_mono ((edgeSet_pieceGraph η hS₀G).superset ⟨η.bijOn_e.mapsTo he, h⟩)
  have hIle : η.imageGraph ≤ G₁' := by
    refine le_of_subset_of_subset η.imageGraph_le hG₁'le ?_ ?_
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := η.bijOn_v.surjOn hx
      have hxG := η.imageGraph_le.vertexSet_mono hx
      rw [hVG] at hxG
      obtain ⟨S₁, hS₁, hxS⟩ := mem_iUnion₂.mp hxG
      rw [hV']
      by_cases h : S₁ = S₀
      · subst h
        exact Or.inl (hIV v hv hxS)
      · exact Or.inr (mem_iUnion₂.mpr ⟨S₁, ⟨hS₁, h⟩, hxS⟩)
    · intro x hx
      obtain ⟨e, he, rfl⟩ := η.bijOn_e.surjOn hx
      have hxG := η.imageGraph_le.edgeSet_mono hx
      rw [hEG] at hxG
      obtain ⟨S₁, hS₁, hxS⟩ := mem_iUnion₂.mp hxG
      rw [hE']
      by_cases h : S₁ = S₀
      · subst h
        exact Or.inl (hIE e he hxS)
      · exact Or.inr (mem_iUnion₂.mpr ⟨S₁, ⟨hS₁, h⟩, hxS⟩)
  let η' : SpanEmbedding H G₁' :=
    ⟨η.imageGraph, η.vMap, η.eMap, hIle, η.bijOn_v, η.bijOn_e, η.inc_iff⟩
  -- The arrangement.
  have harr' : IsSurfaceArrangement S_seg' α_disc' α_pt := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro S₁ (rfl | ⟨h₁, -⟩)
      · rw [hd₀]
        exact harr.isClosedDisc S₀ hS₀
      · rw [hd₁ S₁ h₁]
        exact harr.isClosedDisc S₁ h₁
    · rintro S₁ (rfl | ⟨h₁, hn₁⟩) S₂ (rfl | ⟨h₂, hn₂⟩) hne₁₂
      · exact absurd rfl hne₁₂
      · rw [hd₀, hd₁ S₂ h₂]
        exact harr.inter_discs S₀ hS₀ S₂ h₂ (Ne.symm hn₂)
      · rw [hd₀, hd₁ S₁ h₁]
        exact harr.inter_discs S₁ h₁ S₀ hS₀ hn₁
      · rw [hd₁ S₁ h₁, hd₁ S₂ h₂]
        exact harr.inter_discs S₁ h₁ S₂ h₂ hne₁₂
    · rintro S₁ (rfl | ⟨h₁, -⟩)
      · rw [hd₀]
        exact harr.inter_bd S₀ hS₀
      · rw [hd₁ S₁ h₁]
        exact harr.inter_bd S₁ h₁
    · rw [hsegV]
      exact harr.injOn_pts
    · rintro S₁ (rfl | ⟨h₁, -⟩)
      · rw [hd₀]
        exact harr.natural_order S₀ hS₀
      · rw [hd₁ S₁ h₁]
        exact harr.natural_order S₁ h₁
  have hcompat' : IsCompatibleWith G₁' H η' S_seg' α_disc' α_pt := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv h
      rw [hsegV] at h
      exact hcompat.pt_eq v hv h
    · rintro S₁ (rfl | ⟨h₁, -⟩)
      · rw [hd₀]
        exact hcompat.bd_inter_eq S₀ hS₀
      · rw [hd₁ S₁ h₁]
        exact hcompat.bd_inter_eq S₁ h₁
    · rintro S₁ (rfl | ⟨h₁, -⟩) v hv
      · rw [hd₀, hcompat.inter_V_iff S₀ hS₀ v hv]
        exact ⟨hIV v hv, fun h => hA'.vertexSet_mono h⟩
      · rw [hd₁ S₁ h₁]
        exact hcompat.inter_V_iff S₁ h₁ v hv
    · rintro S₁ (rfl | ⟨h₁, -⟩) e he
      · rw [hd₀, hcompat.inter_E_iff S₀ hS₀ e he]
        exact ⟨hIE e he, fun h => hA'.edgeSet_mono h⟩
      · rw [hd₁ S₁ h₁]
        exact hcompat.inter_E_iff S₁ h₁ e he
  -- The size drops.
  have hVsub : V(G₁') ⊆ V(G₁) := hG₁'le.vertexSet_mono
  have hEsub : E(G₁') ⊆ E(G₁) := hG₁'le.edgeSet_mono
  have hcount₁ := ncard_le_ncard hVsub hVf
  have hcount₂ := ncard_le_ncard hEsub hEf
  have hdrop : V(G₁').ncard + E(G₁').ncard < V(G₁).ncard + E(G₁).ncard := by
    exact replacing_smaller_society_decreases_size (α := α) (β := β) (G₁ := G₁) (S_seg := S_seg)
      hVf hEf (S₀ := S₀) hS₀ (A' := A') hA' hbar hne hs hS₀G G₁' hV' hE' hVsub hEsub hcount₁
      hcount₂
  refine ⟨S_seg', α_disc', G₁', η', hG₁'le, hseg', harr', hcompat', hsegV, rfl, rfl, rfl, ?_, hdrop,
    hV', hE'⟩
  rintro S₁ (rfl | ⟨h₁, -⟩)
  · exact ⟨S₀, hS₀, hd₀⟩
  · exact ⟨S₁, h₁, hd₁ S₁ h₁⟩

end GraphMinor.GM14
