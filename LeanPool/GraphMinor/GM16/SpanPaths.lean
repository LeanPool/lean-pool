/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.GM11.Section5b
import LeanPool.GraphMinor.GM11.NiceStatements
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section3c

/-!
# Paths under a span embedding

The vertex and edge bijections of a span preserve links and hence walks.
Their images stay in the image subgraph. These facts let the path arguments
for XVI (8.3) pass between a drawing and its copy in the ambient graph.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}

/-- A span embedding preserves the two ends of an edge, including a loop. -/
theorem spanEmbedding_map_isLink {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) {e : Set S} {x y : S} (he : H.toGraph.IsLink e x y) :
    η.imageGraph.IsLink (η.eMap e) (η.vMap x) (η.vMap y) := by
  have hx : x ∈ closure e := (he.2.2.2 ▸ mem_insert x {y}).1
  have hy : y ∈ closure e := (he.2.2.2 ▸ mem_insert_of_mem x (mem_singleton y)).1
  rw [Graph.isLink_iff_inc]
  refine ⟨(η.inc_iff e he.1 x he.2.1).mpr hx,
    (η.inc_iff e he.1 y he.2.2.1).mpr hy, ?_⟩
  intro z hz
  obtain ⟨a, ha, rfl⟩ := η.bijOn_v.surjOn (hz.vertex_mem)
  have haz := (η.inc_iff e he.1 a ha).mp hz
  have haa : a ∈ ({x, y} : Set S) := he.2.2.2 ▸ ⟨haz, ha⟩
  rcases haa with rfl | haa
  · exact Or.inl rfl
  · exact Or.inr (congrArg η.vMap (mem_singleton_iff.mp haa))

/-- Map a drawing walk to the image graph of a span embedding. -/
def mapSpanWalk {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) {x y : S} (W : GraphWalk H.toGraph x y) :
    GraphWalk η.imageGraph (η.vMap x) (η.vMap y) :=
  match W with
  | .nil hx => .nil (η.bijOn_v.mapsTo hx)
  | .cons he W => .cons (spanEmbedding_map_isLink η he) (mapSpanWalk η W)

/-- The mapped walk has exactly the mapped vertices of the original walk. -/
theorem mapSpanWalk_support {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) {x y : S} (W : GraphWalk H.toGraph x y) :
    (mapSpanWalk η W).support = W.support.map η.vMap := by
  induction W with
  | nil _ => rfl
  | cons he W ih =>
    change _ :: (mapSpanWalk η W).support = _ :: W.support.map η.vMap
    rw [ih]

/-- The mapped walk has exactly the mapped edges of the original walk. -/
theorem mapSpanWalk_edges {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) {x y : S} (W : GraphWalk H.toGraph x y) :
    (mapSpanWalk η W).edges = W.edges.map η.eMap := by
  induction W with
  | nil _ => rfl
  | cons he W ih =>
    change _ :: (mapSpanWalk η W).edges = _ :: W.edges.map η.eMap
    rw [ih]

/-- Two paths from the old graph to a common point outside it contain an
old-graph path between their distinct old ends. The paths may intersect
away from that common point. -/
theorem exists_hPath_of_two_paths {G H P Q : Graph α β} {a w b : α}
    (hHG : H ≤ G) (hP : GM09.IsGraphPathWithEnds G P a w)
    (hQ : GM09.IsGraphPathWithEnds G Q w b)
    (ha : a ∈ V(H)) (hb : b ∈ V(H)) (hab : a ≠ b)
    (hPH : V(P) ∩ V(H) ⊆ {a}) (hQH : V(Q) ∩ V(H) ⊆ {b}) :
    ∃ L : Graph α β, L ≤ GM09.subgraphUnion G P Q ∧ IsHPathWithEnds G H L a b := by
  let U := GM09.subgraphUnion G P Q
  have hPU : P ≤ U := GM09.le_subgraphUnion_left hP.1 hQ.1
  have hQU : Q ≤ U := GM09.le_subgraphUnion_right hP.1 hQ.1
  obtain ⟨WP, _, _, _⟩ := hP.2
  obtain ⟨WQ, _, _, _⟩ := hQ.2
  obtain ⟨WP', _, _⟩ := GM09.exists_walk_up_of_le hPU WP
  obtain ⟨WQ', _, _⟩ := GM09.exists_walk_up_of_le hQU WQ
  obtain ⟨L, hL, _, _⟩ := GM09.exists_isGraphPathWithEnds_of_walk (WP'.append WQ')
  have hUG : U ≤ G := GM09.subgraphUnion_le hP.1 hQ.1
  have hLG : GM09.IsGraphPathWithEnds G L a b := hL.mono hUG
  have hLsub : L ≤ U := hL.1
  have hPE := GM09.disjoint_edgeSet_of_inter_singleton hP hHG hPH
  have hQE := GM09.disjoint_edgeSet_of_inter_singleton hQ hHG hQH
  refine ⟨L, hLsub, hHG, hLG, hab, ha, hb, ?_, ?_⟩
  · apply subset_antisymm
    · rintro x ⟨hxL, hxH⟩
      have hxU := hLsub.vertexSet_mono hxL
      change x ∈ V(P) ∪ V(Q) at hxU
      rcases hxU with hxP | hxQ
      · exact mem_insert_iff.mpr (Or.inl (mem_singleton_iff.mp (hPH ⟨hxP, hxH⟩)))
      · exact mem_insert_of_mem a (hQH ⟨hxQ, hxH⟩)
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨hLG.left_mem, ha⟩
      · rw [mem_singleton_iff] at hx
        subst x
        exact ⟨hLG.right_mem, hb⟩
  · apply disjoint_left.mpr
    intro e heL heH
    have heU := hLsub.edgeSet_mono heL
    rw [GM09.edgeSet_subgraphUnion hP.1 hQ.1] at heU
    rcases heU with heP | heQ
    · exact hPE.notMem_of_mem_left heP heH
    · exact hQE.notMem_of_mem_left heQ heH

/-- The ends of an image edge are at metric distance at most two.
Both ends lie on a common region of the original drawing. The two radial
spokes to its hub, each traversed twice, give a closed walk of length four. -/
theorem metric_le_two_of_image_link [T2Space S] (hS : IsClosedSurface S)
    {H : Drawing S} {G : Graph α β} (η : SpanEmbedding H G)
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric H θ T d)
    {x y : S} (hx : x ∈ H.V) (hy : y ∈ H.V) {e : β}
    (he : e ∈ E(η.imageGraph)) (hlink : G.IsLink e (η.vMap x) (η.vMap y)) :
    d {x} {y} ≤ 2 := by
  let : ConnectedSpace S := hm.1.1.1
  have hl := (η.imageGraph_le.isLink_iff he).mpr hlink
  obtain ⟨f, hf, hfe⟩ := η.bijOn_e.surjOn he
  have hix : η.imageGraph.Inc (η.eMap f) (η.vMap x) := by rw [hfe]; exact ⟨η.vMap y, hl⟩
  have hiy : η.imageGraph.Inc (η.eMap f) (η.vMap y) := by rw [hfe]; exact ⟨η.vMap x, hl.symm⟩
  have hxf := (η.inc_iff f hf x hx).mp hix
  have hyf := (η.inc_iff f hf y hy).mp hiy
  obtain ⟨r, hr, hfr⟩ := exists_region_incident hS hf
  have hxr := (closure_minimal hfr isClosed_closure) hxf
  have hyr := (closure_minimal hfr isClosed_closure) hyf
  obtain ⟨K, ins, hrad, _, hd⟩ := hm.2
  have hp := hrad.2.1
  have hxK := hp.2.1 hx
  have hyK := hp.2.1 hy
  have hxA : ({x} : Set S) ∈ H.A := Or.inl (Or.inl ⟨x, hx, rfl⟩)
  have hyA : ({y} : Set S) ∈ H.A := Or.inl (Or.inl ⟨y, hy, rfl⟩)
  rw [hd _ hxA _ hyA]
  by_cases hθ : θ ≤ 2
  · exact (tangleMetric_le_order hp _ _).trans hθ
  obtain ⟨c, ⟨hcr, hcK⟩, _⟩ := hp.2.2.1 r hr
  obtain ⟨a, ha, hac⟩ := exists_spoke_at ⟨hrad.1, hp⟩ hrad.2.2 hS ⟨f, hf⟩ hr hcr hcK hx hxr
  obtain ⟨b, hb, hbc⟩ := exists_spoke_at ⟨hrad.1, hp⟩ hrad.2.2 hS ⟨f, hf⟩ hr hcr hcK hy hyr
  have la : K.toGraph.IsLink a x c := ⟨ha, hxK, hcK, hac⟩
  have lb : K.toGraph.IsLink b y c := ⟨hb, hyK, hcK, hbc⟩
  let W : GraphWalk K.toGraph x x := .cons la (.cons lb.symm (.cons lb (.cons la.symm (.nil hxK))))
  have hu : ∀ z ∈ W.support, z ∈ insWalk ins K W := fun z hz =>
    Or.inl ((mem_walkDrawing_U K W).mpr (Or.inl hz))
  apply tangleMetric_le
  refine ⟨x, W, {x}, {y}, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · exact ⟨hxA, Or.inl (Or.inl ⟨x, hxK, rfl⟩), Or.inl ⟨x, hx, rfl, rfl⟩⟩
  · exact ⟨hyA, Or.inl (Or.inl ⟨y, hyK, rfl⟩), Or.inl ⟨y, hy, rfl, rfl⟩⟩
  · change 4 < 2 * θ
    omega
  · rintro z rfl
    exact hu _ (by simp [W, GraphWalk.support])
  · rintro z rfl
    exact hu _ (by simp [W, GraphWalk.support])

/-- A path meeting a span just in its ends is a span path when the ends are
at distance at least three. That bound rules out a shared edge. -/
theorem isHPath_of_far_ends [T2Space S] (hS : IsClosedSurface S) {H : Drawing S} {G P : Graph α β}
    (η : SpanEmbedding H G) {d : Set S → Set S → ℕ}
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hm : HasTangleMetric H θ T d)
    {x y : S} (hx : x ∈ H.V) (hy : y ∈ H.V)
    (hP : GM09.IsGraphPathWithEnds G P (η.vMap x) (η.vMap y))
    (hne : η.vMap x ≠ η.vMap y)
    (hinter : V(P) ∩ V(η.imageGraph) = {η.vMap x, η.vMap y})
    (hdist : 3 ≤ d {x} {y}) : IsHPathWithEnds G η.imageGraph P (η.vMap x) (η.vMap y) := by
  refine ⟨η.imageGraph_le, hP, hne, η.bijOn_v.mapsTo hx, η.bijOn_v.mapsTo hy, hinter, ?_⟩
  apply disjoint_left.mpr
  intro e heP heH
  obtain ⟨r, s, hlinkP⟩ := P.exists_isLink_of_mem_edgeSet heP
  have hlinkG := (hP.1.isLink_iff heP).mp hlinkP
  have hlinkH := (η.imageGraph_le.isLink_iff heH).mpr hlinkG
  have hr : r ∈ ({η.vMap x, η.vMap y} : Set α) := hinter ▸ ⟨hlinkP.left_mem, hlinkH.left_mem⟩
  have hs : s ∈ ({η.vMap x, η.vMap y} : Set α) := hinter ▸ ⟨hlinkP.right_mem, hlinkH.right_mem⟩
  have hbad : G.IsLink e (η.vMap x) (η.vMap y) → False := by
    intro hl
    have hb := metric_le_two_of_image_link hS η hm hx hy heH hl
    omega
  rcases hr with rfl | hr <;> rcases hs with rfl | hs
  · exact hP.not_isLoopAt heP _ hlinkG
  · rw [mem_singleton_iff] at hs
    exact hbad (hs ▸ hlinkG)
  · rw [mem_singleton_iff] at hr
    exact hbad (hr ▸ hlinkG.symm)
  · rw [mem_singleton_iff] at hr hs
    exact hP.not_isLoopAt heP _ (hr ▸ hs ▸ hlinkG)

/-- A path with distinct ends has an edge at its last end, and the other
end of that edge is different. -/
theorem path_edge_at_end {G P : Graph α β} {a b : α}
    (hP : GM09.IsGraphPathWithEnds G P a b) (hab : a ≠ b) :
    ∃ (e : β) (u : α), P.IsLink e u b ∧ u ≠ b := by
  obtain ⟨_, W, hsimple, _, _⟩ := GM09.IsGraphPathWithEnds.symm hP
  cases W with
  | nil _ => exact (hab rfl).elim
  | @cons b u a e hl R =>
    refine ⟨e, u, hl.symm, ?_⟩
    intro heq
    exact (List.nodup_cons.mp hsimple).1 (heq ▸ R.start_mem_support)

end GraphMinor.GM16
