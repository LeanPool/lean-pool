/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.PieceDrawing
public import LeanPool.GraphMinor.GM14.RigidThread

/-!
# From drawings of the members of a segregation to a drawing of the graph

"It follows that we may assume, to simplify notation, that $G_1$ is a drawing in $\Sigma$" (Graph
Minors
XIV, proof of (8.4), page 42). If each member of a segregation is drawn in its disc, then the
drawings meet only in the common vertices, and they glue to a drawing of the whole graph.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface GraphMinor.GM11

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]

/-- The drawings `Γs` of the members of a segregation of `G` have a common vertex map `ν`, and their
union is a drawing of `G`. -/
theorem exists_glued_drawing {G : Graph α β} {S_seg : Set (Society α β)}
    (hseg : IsGraphSegregation G S_seg) {ν : α → S} (hinj : InjOn ν V(G))
    (Γs : ∀ S₀ ∈ S_seg, GraphDrawing S₀.G S)
    (hν : ∀ S₀ (h : S₀ ∈ S_seg), ∀ v : V(S₀.G), ((Γs S₀ h).iso.vertexEquiv v).1 = ν v.1)
    (hmeet : ∀ S₁ (h₁ : S₁ ∈ S_seg), ∀ S₂ (h₂ : S₂ ∈ S_seg), S₁ ≠ S₂ →
      (Γs S₁ h₁).drawing.U ∩ (Γs S₂ h₂).drawing.U ⊆ ν '' (V(S₁.G) ∩ V(S₂.G))) :
    ∃ Γ : GraphDrawing G S, Γ.drawing.U = ⋃ (S₀) (h : S₀ ∈ S_seg), (Γs S₀ h).drawing.U ∧
      (∀ v : V(G), (Γ.iso.vertexEquiv v).1 = ν v.1) ∧
      ∀ S₀ (h : S₀ ∈ S_seg), ∀ e ∈ E(S₀.G),
        graphDrawingEdgeSet Γ e = graphDrawingEdgeSet (Γs S₀ h) e := by
  classical
  let Us : Society α β → Set S := fun S₀ => if h : S₀ ∈ S_seg then (Γs S₀ h).drawing.U else ∅
  have hUs : ∀ S₀ (h : S₀ ∈ S_seg), Us S₀ = (Γs S₀ h).drawing.U := fun S₀ h => by
    simp only [Us, h, dite_true]
  let Es : Society α β → β → Set S := fun S₀ e =>
    if h : S₀ ∈ S_seg then graphDrawingEdgeSet (Γs S₀ h) e else ∅
  have hEs : ∀ S₀ (h : S₀ ∈ S_seg) e, Es S₀ e = graphDrawingEdgeSet (Γs S₀ h) e := fun S₀ h e => by
    simp only [Es, h, dite_true]
  let part (T : Set (Society α β)) : Graph α β :=
    subgraphSUnion G ((fun S₀ : Society α β => S₀.G) '' T)
  have hle : ∀ T ⊆ S_seg, part T ≤ G := fun T hT =>
    subgraphSUnion_le (by rintro _ ⟨S₀, hS₀, rfl⟩; exact hseg.le S₀ (hT hS₀))
  have hV : ∀ T ⊆ S_seg, V(part T) = ⋃ S₀ ∈ T, V(S₀.G) := fun T hT => by
    simp [part, vertexSet_subgraphSUnion]
  have hE : ∀ T ⊆ S_seg, E(part T) = ⋃ S₀ ∈ T, E(S₀.G) := fun T hT => by
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨S₀, hS₀, rfl⟩; exact hseg.le S₀ (hT hS₀))]
    simp
  have key : ∀ T : Set (Society α β), T.Finite → T ⊆ S_seg → ∃ Γ : GraphDrawing (part T) S,
      Γ.drawing.U = (⋃ S₀ ∈ T, Us S₀) ∧
      (∀ v : V(part T), (Γ.iso.vertexEquiv v).1 = ν v.1) ∧
      ∀ S₀ ∈ T, ∀ e ∈ E(S₀.G), graphDrawingEdgeSet Γ e = Es S₀ e := by
    intro T hT
    induction T, hT using Set.Finite.induction_on with
    | empty =>
      intro _
      have hVe : V(part ∅) = ∅ := by simpa using hV ∅ (empty_subset _)
      have hEe : E(part ∅) = ∅ := by simpa using hE ∅ (empty_subset _)
      obtain ⟨Γ, hU, hv⟩ := GraphDrawing.of_edgeless (hVe ▸ finite_empty) hEe
        (ν := ν) (hVe ▸ injOn_empty ν)
      refine ⟨Γ, by rw [hU, hVe]; simp, hv, by simp⟩
    | @insert S₁ T hS₁ hT ih =>
      intro hsub
      have hT' : T ⊆ S_seg := (subset_insert _ _).trans hsub
      have hS₁' : S₁ ∈ S_seg := hsub (mem_insert _ _)
      obtain ⟨Γ, hU, hv, he⟩ := ih hT'
      have hl₁ : part T ≤ part (insert S₁ T) := by
        refine le_of_subset_of_subset (hle T hT') (hle _ hsub) ?_ ?_
        · rw [hV T hT', hV _ hsub]
          exact biUnion_subset_biUnion_left (subset_insert _ _)
        · rw [hE T hT', hE _ hsub]
          exact biUnion_subset_biUnion_left (subset_insert _ _)
      have hl₂ : S₁.G ≤ part (insert S₁ T) := by
        refine le_of_subset_of_subset (hseg.le S₁ hS₁') (hle _ hsub) ?_ ?_
        · rw [hV _ hsub]
          exact subset_biUnion_of_mem (u := fun S₀ : Society α β => V(S₀.G)) (mem_insert _ _)
        · rw [hE _ hsub]
          exact subset_biUnion_of_mem (u := fun S₀ : Society α β => E(S₀.G)) (mem_insert _ _)
      have hne : ∀ S₀ ∈ T, S₀ ≠ S₁ := fun S₀ h => by
        rintro rfl
        exact hS₁ h
      obtain ⟨Γ', hU', hv', he'⟩ := GraphDrawing.glue_edges hl₁ hl₂
        (by rw [hV T hT', hV _ hsub, biUnion_insert, union_comm])
        (by rw [hE T hT', hE _ hsub, biUnion_insert, union_comm])
        (by
          rw [hE T hT']
          refine disjoint_iUnion₂_left.mpr fun S₀ hS₀ => ?_
          exact hseg.edge_disjoint S₀ (hT' hS₀) S₁ hS₁' (hne S₀ hS₀))
        (hinj.mono (hle _ hsub).vertexSet_mono) Γ (Γs S₁ hS₁') hv (hν S₁ hS₁')
        (by
          rintro x ⟨hx₁, hx₂⟩
          rw [hU] at hx₁
          obtain ⟨S₀, hS₀, hx₁⟩ := mem_iUnion₂.mp hx₁
          rw [hUs S₀ (hT' hS₀)] at hx₁
          obtain ⟨y, ⟨hy₁, hy₂⟩, rfl⟩ := hmeet S₀ (hT' hS₀) S₁ hS₁' (hne S₀ hS₀) ⟨hx₁, hx₂⟩
          refine ⟨y, ⟨?_, hy₂⟩, rfl⟩
          rw [hV T hT']
          exact mem_iUnion₂.mpr ⟨S₀, hS₀, hy₁⟩)
      refine ⟨Γ', ?_, hv', ?_⟩
      · rw [hU', hU, biUnion_insert, union_comm, hUs S₁ hS₁']
      · intro S₀ hS₀ e heS₀
        rw [he' e]
        rcases hS₀ with rfl | hS₀
        · have hn : e ∉ E(part T) := by
            rw [hE T hT']
            intro h
            obtain ⟨S₂, hS₂, h⟩ := mem_iUnion₂.mp h
            exact disjoint_left.mp (hseg.edge_disjoint S₂ (hT' hS₂) S₀ hS₁' (hne S₂ hS₂)) h heS₀
          have : graphDrawingEdgeSet Γ e = ∅ := by
            ext x
            simp [graphDrawingEdgeSet, hn]
          rw [this, empty_union, hEs S₀ hS₁']
        · have hn : e ∉ E(S₁.G) := disjoint_left.mp
            (hseg.edge_disjoint S₀ (hT' hS₀) S₁ hS₁' (hne S₀ hS₀)) heS₀
          have : graphDrawingEdgeSet (Γs S₁ hS₁') e = ∅ := by
            ext x
            simp [graphDrawingEdgeSet, hn]
          rw [this, union_empty, he S₀ hS₀ e heS₀]
  obtain ⟨Γ, hU, hv, he⟩ := key S_seg hseg.finite Subset.rfl
  have hpart : part S_seg = G := hseg.union_eq
  have hU₀ : (⋃ S₀ ∈ S_seg, Us S₀) = ⋃ (S₀) (h : S₀ ∈ S_seg), (Γs S₀ h).drawing.U :=
    iUnion₂_congr hUs
  have : ∀ G' : Graph α β, G' = G → ∀ Γ : GraphDrawing G' S,
      Γ.drawing.U = (⋃ S₀ ∈ S_seg, Us S₀) →
      (∀ v : V(G'), (Γ.iso.vertexEquiv v).1 = ν v.1) →
      (∀ S₀ ∈ S_seg, ∀ e ∈ E(S₀.G), graphDrawingEdgeSet Γ e = Es S₀ e) →
      ∃ Γ : GraphDrawing G S, Γ.drawing.U = (⋃ (S₀) (h : S₀ ∈ S_seg), (Γs S₀ h).drawing.U) ∧
        (∀ v : V(G), (Γ.iso.vertexEquiv v).1 = ν v.1) ∧
        ∀ S₀ (h : S₀ ∈ S_seg), ∀ e ∈ E(S₀.G),
          graphDrawingEdgeSet Γ e = graphDrawingEdgeSet (Γs S₀ h) e := by
    rintro _ rfl Γ h₁ h₂ h₃
    exact ⟨Γ, h₁.trans hU₀, h₂, fun S₀ h e he => (h₃ S₀ h e he).trans (hEs S₀ h e)⟩
  exact this _ hpart Γ hU hv he

/-- The subgraph `H ∩ A` of `A`, for a subgraph `H = η(H)` of `G`. -/
def pieceGraph {H : Drawing S} {G : Graph α β} (η : SpanEmbedding H G) (A : Graph α β) :
    Graph α β :=
  (η.imageGraph.induce (V(η.imageGraph) ∩ V(A))).restrict E(A)

omit [T2Space S] in
theorem vertexSet_pieceGraph {H : Drawing S} {G : Graph α β} (η : SpanEmbedding H G)
    (A : Graph α β) : V(pieceGraph η A) = V(η.imageGraph) ∩ V(A) := rfl

omit [T2Space S] in
theorem pieceGraph_le_image {H : Drawing S} {G : Graph α β} (η : SpanEmbedding H G)
    (A : Graph α β) : pieceGraph η A ≤ η.imageGraph :=
  restrict_le.trans (η.imageGraph.induce_le inter_subset_left)

omit [T2Space S] in
theorem edgeSet_pieceGraph {H : Drawing S} {G : Graph α β} (η : SpanEmbedding H G)
    {A : Graph α β} (hA : A ≤ G) : E(pieceGraph η A) = E(η.imageGraph) ∩ E(A) := by
  ext e
  constructor
  · intro he
    exact ⟨(pieceGraph_le_image η A).edgeSet_mono he, (edgeSet_restrict _ _ ▸ he).2⟩
  · rintro ⟨he, heA⟩
    obtain ⟨x, y, hl⟩ := η.imageGraph.exists_isLink_of_mem_edgeSet he
    have hlG := hl.mono η.imageGraph_le
    have hlA := (hA.isLink_iff heA).mpr hlG
    refine (edgeSet_restrict _ _ ▸ ⟨?_, heA⟩ : e ∈ E(pieceGraph η A))
    exact (show (η.imageGraph.induce (V(η.imageGraph) ∩ V(A))).IsLink e x y from
      ⟨hl, ⟨hl.left_mem, hlA.left_mem⟩, ⟨hl.right_mem, hlA.right_mem⟩⟩).edge_mem

omit [T2Space S] in
theorem pieceGraph_le {H : Drawing S} {G : Graph α β} (η : SpanEmbedding H G)
    {A : Graph α β} (hA : A ≤ G) : pieceGraph η A ≤ A := by
  refine le_of_subset_of_subset ((pieceGraph_le_image η A).trans η.imageGraph_le) hA ?_ ?_
  · exact inter_subset_right
  · rw [edgeSet_pieceGraph η hA]
    exact inter_subset_right

/-- `H ∩ α(A, Ω)` is the subgraph `H ∩ A` of `A`, by compatibility. -/
theorem exists_pieceEmbedding {H : Drawing S} {G : Graph α β} (η : SpanEmbedding H G)
    {A : Graph α β} (hA : A ≤ G) {D : Set S} (hD : IsClosed D) (hbd : subBd D ∩ H.U ⊆ H.V)
    (hV : ∀ v ∈ H.V, v ∈ D ↔ η.vMap v ∈ V(A)) (hE : ∀ e ∈ H.E, e ⊆ D ↔ η.eMap e ∈ E(A)) :
    ∃ η₁ : SpanEmbedding (H.interSet D) A, η₁.imageGraph = pieceGraph η A ∧
      η₁.vMap = η.vMap ∧ η₁.eMap = η.eMap := by
  have hIV := (interSet_V_and_U hD hbd).1
  have hIE : (H.interSet D).E = {e | e ∈ H.E ∧ e ⊆ D} := by
    ext g
    exact Whitney.mem_interSet_E
  have hEP := edgeSet_pieceGraph η hA
  refine ⟨⟨pieceGraph η A, η.vMap, η.eMap, pieceGraph_le η hA, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩,
    rfl, rfl, rfl⟩
  · rw [hIV]
    intro v hv
    exact ⟨η.bijOn_v.mapsTo hv.1, (hV v hv.1).mp hv.2⟩
  · rw [hIV]
    exact η.bijOn_v.injOn.mono inter_subset_left
  · rw [hIV]
    rintro a ⟨ha, haA⟩
    obtain ⟨v, hv, rfl⟩ := η.bijOn_v.surjOn ha
    exact ⟨v, ⟨hv, (hV v hv).mpr haA⟩, rfl⟩
  · rw [hIE, hEP]
    intro e he
    exact ⟨η.bijOn_e.mapsTo he.1, (hE e he.1).mp he.2⟩
  · rw [hIE]
    exact η.bijOn_e.injOn.mono fun e he => he.1
  · rw [hIE, hEP]
    rintro a ⟨ha, haA⟩
    obtain ⟨e, he, rfl⟩ := η.bijOn_e.surjOn ha
    exact ⟨e, ⟨he, (hE e he).mpr haA⟩, rfl⟩
  · intro e he v hv
    have he' : e ∈ H.E := (hIE.subset he).1
    have hv' : v ∈ H.V := by rw [hIV] at hv; exact hv.1
    rw [← η.inc_iff e he' v hv']
    constructor
    · exact fun ⟨z, hz⟩ => ⟨z, hz.mono (pieceGraph_le_image η A)⟩
    · rintro ⟨z, hz⟩
      have hm : η.eMap e ∈ E(pieceGraph η A) := by
        rw [hEP]
        exact ⟨η.bijOn_e.mapsTo he', (hE e he').mp (hIE.subset he).2⟩
      exact ⟨z, ((pieceGraph_le_image η A).isLink_iff hm).mpr hz⟩

end GraphMinor.GM14
