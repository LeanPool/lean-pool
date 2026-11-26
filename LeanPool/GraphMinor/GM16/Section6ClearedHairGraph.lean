/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6HairFamily
import LeanPool.GraphMinor.GM16.Section6ZoneWalks
import LeanPool.GraphMinor.GM16.Section6HairUnion
import LeanPool.GraphMinor.GM16.SpanPaths
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Walks

/-!
# The connected graph after clearing a zone in XVI (6.3)

Join the full hair paths to the part of the old drawing in the closed
smaller zone. That part is connected and contains the far ends, rather
than `Y₄` as printed on page 60. The union is connected, avoids the horn
vertices, and meets the cleared drawing precisely at the near ends.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}

omit [T2Space S] in
private theorem span_image_connected {G : Graph α β} {H : Drawing S}
    (η : SpanEmbedding H G) (hH : H.IsConnected) : IsGraphConnected η.imageGraph := by
  constructor
  · obtain ⟨a, ha⟩ := hH.1
    exact ⟨η.vMap a, η.bijOn_v.mapsTo ha⟩
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := η.bijOn_v.surjOn hx
    obtain ⟨b, hb, rfl⟩ := η.bijOn_v.surjOn hy
    obtain ⟨W⟩ := hH.2 a ha b hb
    exact ⟨mapSpanWalk η W⟩

private theorem disjoint_edges_of_disjoint_vertices {G C H : Graph α β}
    (hCG : C ≤ G) (hHG : H ≤ G) (hd : Disjoint V(C) V(H)) : Disjoint E(C) E(H) := by
  apply Set.disjoint_left.mpr
  intro e heC heH
  obtain ⟨a, b, he⟩ := C.exists_isLink_of_mem_edgeSet heC
  have heH' := (hHG.isLink_iff heH).mpr (he.mono hCG)
  exact (Set.disjoint_left.mp hd) he.left_mem heH'.left_mem

/-- A drawing vertex in the open zone is absent from the cleared
embedded graph. -/
theorem cleared_image_vertex_not_mem
    {G : Graph α β} {H : Drawing S} (η : SpanEmbedding H G) {Λ : Set S}
    (hΛ : IsOpen Λ) {y : S} (hy : y ∈ H.V) (hyΛ : y ∈ Λ) :
    η.vMap y ∉ V((restrictCleared η Λ).imageGraph) := by
  intro hyIm
  obtain ⟨z, hz, heq⟩ := (restrictCleared η Λ).bijOn_v.surjOn hyIm
  have hz' : z ∈ H.V ∧ z ∈ univ \ Λ :=
    (mem_interSet_V_iff (Γ := H) (by simpa only [← compl_eq_univ_sdiff] using
      hΛ.isClosed_compl)).mp hz
  have hzy : z = y := η.bijOn_v.injOn hz'.1 hy heq
  exact hz'.2.2 (hzy.symm ▸ hyΛ)

/-- Construct `G₂` in XVI (6.3), pages 60–61, and prove the properties
needed for the second application of (5.3). Its connected core contains
the far ends in the closed smaller zone, correcting the printed `Y₄`. -/
theorem exists_connected_cleared_hair_graph
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {d : Set S → Set S → ℕ} {X : Set α} {Y Y₄ : Set S} {θ lam : ℕ}
    (F : HairFamily G H η d X Y θ) (hY : Y ⊆ H.V)
    (hX : X ⊆ V(G) \ V(η.imageGraph))
    (hH : (PaintingOrDrawing.drawing H).IsTwoCell)
    {z Λ₁ Λ : Set S} (hZone : IsLambdaZoneAround H d lam z Λ₁)
    (hΛ : IsOpen Λ) (hnest : closure Λ₁ ⊆ Λ) (hY₄ : Y₄ ⊆ Y)
    (hfar : ∀ y ∈ Y₄, F.far y ∈ closure Λ₁)
    (hnear : ∀ y ∈ Y₄, y ∉ Λ) :
    ∃ K : Graph α β, K ≤ G ∧ IsGraphConnected K ∧ Disjoint X V(K) ∧
      Disjoint E(K) E((restrictCleared η Λ).imageGraph) ∧
      V(K) ∩ V((restrictCleared η Λ).imageGraph) = (restrictCleared η Λ).vMap '' Y₄ ∧
      ∀ x ∈ V((restrictCleared η Λ).imageGraph), {y | K.Adj x y}.Subsingleton := by
  classical
  let D := H.interSet (closure Λ₁)
  let ηD := restrictSpan η (H.V ∩ closure Λ₁) {e | e ∈ H.E ∧ e ⊆ closure Λ₁}
  let C := ηD.imageGraph
  let η' := restrictCleared η Λ
  let paths : Y₄ → Graph α β := fun y => F.path y.val
  let K := subgraphSUnion G ({C} ∪ range paths)
  have hC : IsGraphConnected C := span_image_connected ηD (zone_interSet_connected hS hH hZone)
  have hCG : C ≤ G := ηD.imageGraph_le
  have hCold : C ≤ η.imageGraph := by
    apply Graph.restrict_le.trans
    apply Graph.induce_le
    rintro x ⟨y, hy, rfl⟩
    exact η.bijOn_v.mapsTo (H.spanV_subset _ _ hy)
  have hCΛ : ∀ x ∈ V(C), ∃ y ∈ H.V, y ∈ Λ ∧ η.vMap y = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := ηD.bijOn_v.surjOn hx
    have hyH := (Drawing.span_isSubdrawing H _ _).1 hy
    have hycl : y ∈ closure Λ₁ := interSet_U_subset isClosed_closure (D.V_subset_U hy)
    exact ⟨y, hyH, hnest hycl, rfl⟩
  have hCdisj : Disjoint V(C) V(η'.imageGraph) := by
    apply Set.disjoint_left.mpr
    intro x hxC hx'
    obtain ⟨y, hy, hyΛ, rfl⟩ := hCΛ x hxC
    exact cleared_image_vertex_not_mem η hΛ hy hyΛ hx'
  have hfarC : ∀ y ∈ Y₄, η.vMap (F.far y) ∈ V(C) := by
    intro y hy
    apply ηD.bijOn_v.mapsTo
    exact Or.inl ⟨⟨F.far_mem y (hY₄ hy), hfar y hy⟩, F.far_mem y (hY₄ hy)⟩
  have hPG : ∀ y : Y₄, paths y ≤ G := fun y => (F.is_hPath y.val (hY₄ y.property)).2.1.le
  have hKG : K ≤ G := subgraphSUnion_le (by
    rintro R (hR | ⟨y, rfl⟩)
    · exact (mem_singleton_iff.mp hR) ▸ hCG
    · exact hPG y)
  have hConn : IsGraphConnected K := connected_union_of_core hCG hC hPG
    (fun y => graphPath_isGraphConnected (F.is_hPath y.val (hY₄ y.property)).2.1)
    (fun y => ⟨η.vMap (F.far y.val), hfarC y.val y.property,
      (F.is_hPath y.val (hY₄ y.property)).2.1.right_mem⟩)
  have hfamily : ∀ R ∈ ({C} : Set (Graph α β)) ∪ range paths, R ≤ G := by
    rintro R (hR | ⟨y, rfl⟩)
    · exact (mem_singleton_iff.mp hR) ▸ hCG
    · exact hPG y
  have hPinter : ∀ y : Y₄, V(paths y) ∩ V(η'.imageGraph) = {η.vMap y.val} := by
    intro y
    apply Set.Subset.antisymm
    · rintro x ⟨hxP, hxH'⟩
      have hxH := (restrictCleared_imageGraph_le η Λ).vertexSet_mono hxH'
      have hx : x ∈ ({η.vMap y.val, η.vMap (F.far y.val)} : Set α) :=
        (F.is_hPath y.val (hY₄ y.property)).2.2.2.2.2.1 ▸ ⟨hxP, hxH⟩
      rcases hx with hx | hx
      · exact hx
      · have heq := mem_singleton_iff.mp hx
        have hfarNot := cleared_image_vertex_not_mem η hΛ (F.far_mem y.val (hY₄ y.property))
          (hnest (hfar y.val y.property))
        exact False.elim (hfarNot (heq ▸ hxH'))
    · rintro x rfl
      exact ⟨(F.is_hPath y.val (hY₄ y.property)).2.1.left_mem,
        η'.bijOn_v.mapsTo (mem_clearedSubdrawing_V (hY (hY₄ y.property)) (hnear y.val y.property))⟩
  have hinter : V(K) ∩ V(η'.imageGraph) = η'.vMap '' Y₄ := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxK, hxH'⟩
      obtain ⟨R, hR, hxR⟩ := mem_iUnion₂.mp hxK
      rcases hR with hR | ⟨y, rfl⟩
      · have hRC := mem_singleton_iff.mp hR
        exact False.elim ((Set.disjoint_left.mp hCdisj) (hRC ▸ hxR) hxH')
      · have hxy := mem_singleton_iff.mp ((hPinter y).subset ⟨hxR, hxH'⟩)
        exact ⟨y.val, y.property, hxy.symm⟩
    · rintro x ⟨y, hy, rfl⟩
      have hPnear : η.vMap y ∈ V(paths ⟨y, hy⟩) := (F.is_hPath y (hY₄ hy)).2.1.left_mem
      exact ⟨(le_subgraphSUnion hfamily (Or.inr ⟨⟨y, hy⟩, rfl⟩)).vertexSet_mono hPnear,
        η'.bijOn_v.mapsTo (mem_clearedSubdrawing_V (hY (hY₄ hy)) (hnear y hy))⟩
  refine ⟨K, hKG, hConn, ?_, ?_, hinter, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hxX hxK
    obtain ⟨R, hR, hxR⟩ := mem_iUnion₂.mp hxK
    rcases hR with hR | ⟨y, rfl⟩
    · have hRC := mem_singleton_iff.mp hR
      exact (hX hxX).2 (hCold.vertexSet_mono (hRC ▸ hxR))
    · exact (Set.disjoint_left.mp (F.avoids_horns y.val (hY₄ y.property))) hxX hxR
  · apply Set.disjoint_left.mpr
    intro e heK heH'
    rw [edgeSet_subgraphSUnion hfamily] at heK
    obtain ⟨R, hR, heR⟩ := mem_iUnion₂.mp heK
    rcases hR with hR | ⟨y, rfl⟩
    · have hRC := mem_singleton_iff.mp hR
      exact (Set.disjoint_left.mp (disjoint_edges_of_disjoint_vertices hCG η'.imageGraph_le hCdisj))
        (hRC ▸ heR) heH'
    · exact (Set.disjoint_left.mp (F.is_hPath y.val (hY₄ y.property)).2.2.2.2.2.2) heR
        ((restrictCleared_imageGraph_le η Λ).edgeSet_mono heH')
  · intro x hxH'
    have hleaf : {z | (subgraphSUnion G (range paths)).Adj x z}.Subsingleton := by
      apply hair_union_old_neighbors_subsingleton
        (P := paths) (a := fun y : Y₄ => η.vMap y.val)
        (b := fun y : Y₄ => η.vMap (F.far y.val))
        (fun y => (F.is_hPath y.val (hY₄ y.property)).2.1)
        (fun _ => le_rfl) hPinter ?_ hxH'
      intro y z heq
      exact Subtype.ext (η.bijOn_v.injOn (hY (hY₄ y.property)) (hY (hY₄ z.property)) heq)
    have hsub : {z | K.Adj x z} ⊆ {z | (subgraphSUnion G (range paths)).Adj x z} := by
      intro z hz
      obtain ⟨R, hR, hAdj⟩ := (subgraphSUnion_adj_iff hfamily).mp hz
      rcases hR with hR | hR
      · have hRC := mem_singleton_iff.mp hR
        obtain ⟨e, he⟩ := hAdj
        exact False.elim ((Set.disjoint_left.mp hCdisj) (hRC ▸ he.left_mem) hxH')
      · apply (subgraphSUnion_adj_iff (fun R hR => hfamily R (Or.inr hR))).mpr
        exact ⟨R, hR, hAdj⟩
    intro a ha b hb
    exact hleaf (hsub ha) (hsub hb)

end GraphMinor.GM16
