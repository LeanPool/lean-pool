/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.SubDataSep
public import LeanPool.GraphMinor.GM12.Section4MetricExistence
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM11.Theorem66
import LeanPool.GraphMinor.GM11.FlatCover

/-!
# Graph Minors XIV – Section 10 Translation (Part 1: Rigidity, 2-Cell, Tangle, and Metric)

This file proves the first two steps of the translation from the hypotheses of Graph Minors XIV,
(1.1) (pages 24–25) to the hypotheses of (4.1) (pages 30–31):
- `isTwoCell_of_subdivision_and_representative`: a drawing `H` of representativity `≥ 1` on a
  connected closed non-spherical surface `S` whose graph is a subdivision of a simple 3-connected
  graph is a 2-cell drawing (`H.IsTwoCell`).
- `exists_respectful_tangle_and_metric`: such a drawing `H` admits a respectful tangle `T` of
  order `209` and a tangle metric `d` (`IsRespectfulDrawingTangle H 209 T ∧ HasTangleMetric H 209 T
  d`).
- `isRigid_of_subdivision_and_respectful_tangle`: such a drawing `H` is rigid (`IsRigid H`).
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14.Whitney

universe u v w

/-! ## 1. Tangle Orientation of Path Separations -/

section TanglePathSep

variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- Left side of the canonical hypergraph separation of `Γ.toHypergraph` induced by an edge set
`E₀ ⊆ Γ.E`. -/
noncomputable def drawingEdgeSepA (Γ : Drawing S) (E₀ : Set (Set S)) : Hypergraph S (Set S) where
  vertexSet := verts Γ.toGraph E₀
  edgeSet := E₀ ∩ Γ.E
  Inc e v := Γ.toHypergraph.Inc e v ∧ e ∈ E₀
  vertex_mem_of_inc e _ h := ⟨e, h.2, inc_of_mem_closure h.1.1 h.1.2.2 h.1.2.1⟩
  edge_mem_of_inc _ _ h := ⟨h.2, h.1.1⟩
  vertexSet_finite := Γ.finite_V.subset (fun _ ⟨_, _, _, hl⟩ => hl.left_mem)
  edgeSet_finite := Γ.finite_edges.subset inter_subset_right

/-- Right side of the canonical hypergraph separation of `Γ.toHypergraph` induced by an edge set
`E₀ ⊆ Γ.E`. -/
noncomputable def drawingEdgeSepB (Γ : Drawing S) (E₀ : Set (Set S)) : Hypergraph S (Set S) where
  vertexSet := (Γ.V \ verts Γ.toGraph E₀) ∪ verts Γ.toGraph (Γ.E \ E₀)
  edgeSet := Γ.E \ E₀
  Inc e v := Γ.toHypergraph.Inc e v ∧ e ∉ E₀
  vertex_mem_of_inc e _ h :=
    Or.inr ⟨e, ⟨h.1.1, h.2⟩, inc_of_mem_closure h.1.1 h.1.2.2 h.1.2.1⟩
  edge_mem_of_inc _ _ h := ⟨h.1.1, h.2⟩
  vertexSet_finite :=
    Γ.finite_V.subset (union_subset sdiff_subset (fun _ ⟨_, _, _, hl⟩ => hl.left_mem))
  edgeSet_finite := Γ.finite_edges.subset sdiff_subset

omit [T2Space S] in
theorem drawingEdgeSepA_le (Γ : Drawing S) (E₀ : Set (Set S)) :
    drawingEdgeSepA Γ E₀ ≤ Γ.toHypergraph where
  vertexSet_subset := fun _ ⟨_, _, _, hl⟩ => hl.left_mem
  edgeSet_subset := inter_subset_right
  ends_eq e he := by
    ext v
    exact ⟨fun h => ⟨h, he.1⟩, fun h => h.1⟩

omit [T2Space S] in
theorem drawingEdgeSepB_le (Γ : Drawing S) (E₀ : Set (Set S)) :
    drawingEdgeSepB Γ E₀ ≤ Γ.toHypergraph where
  vertexSet_subset := union_subset sdiff_subset (fun _ ⟨_, _, _, hl⟩ => hl.left_mem)
  edgeSet_subset := sdiff_subset
  ends_eq e he := by
    ext v
    exact ⟨fun h => ⟨h, he.2⟩, fun h => h.1⟩

omit [T2Space S] in
theorem isSeparation_drawingEdgeSep (Γ : Drawing S) (E₀ : Set (Set S)) :
    Γ.toHypergraph.IsSeparation (drawingEdgeSepA Γ E₀) (drawingEdgeSepB Γ E₀) := by
  rw [isSeparation_iff_of_le (drawingEdgeSepA_le Γ E₀) (drawingEdgeSepB_le Γ E₀)]
  refine ⟨?_, ?_, ?_⟩
  · change verts Γ.toGraph E₀ ∪ ((Γ.V \ verts Γ.toGraph E₀) ∪ verts Γ.toGraph (Γ.E \ E₀)) = Γ.V
    have hs1 : verts Γ.toGraph E₀ ⊆ Γ.V := fun _ ⟨_, _, _, hl⟩ => hl.left_mem
    have hs2 : verts Γ.toGraph (Γ.E \ E₀) ⊆ Γ.V := fun _ ⟨_, _, _, hl⟩ => hl.left_mem
    rw [← Set.union_assoc, union_sdiff_self, union_eq_self_of_subset_left hs1,
      union_eq_self_of_subset_right hs2]
  · change (E₀ ∩ Γ.E) ∪ (Γ.E \ E₀) = Γ.E
    rw [Set.inter_comm, inter_union_sdiff]
  · change (E₀ ∩ Γ.E) ∩ (Γ.E \ E₀) = ∅
    ext e
    simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false, not_and]
    exact fun h1 _ h2 => h2 h1.1

omit [T2Space S] in
theorem inter_vertexSet_drawingEdgeSep (Γ : Drawing S) (E₀ : Set (Set S)) :
    (drawingEdgeSepA Γ E₀ ∩ drawingEdgeSepB Γ E₀).vertexSet = bdry Γ.toGraph E₀ := by
  change verts Γ.toGraph E₀ ∩ ((Γ.V \ verts Γ.toGraph E₀) ∪ verts Γ.toGraph (Γ.E \ E₀)) =
    verts Γ.toGraph E₀ ∩ verts Γ.toGraph (Γ.E \ E₀)
  ext x
  simp only [mem_inter_iff, mem_union, mem_sdiff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.resolve_left (fun h => h.2 h1)⟩,
    fun ⟨h1, h2⟩ => ⟨h1, Or.inr h2⟩⟩

omit [T2Space S] in
theorem suffix_bdry_subset {Γ : Drawing S} {x u y : S}
    (W₁ : GraphWalk Γ.toGraph x u) (W₂ : GraphWalk Γ.toGraph u y)
    (hs : (W₁.append W₂).IsSimple)
    (hbd : bdry Γ.toGraph {g | g ∈ (W₁.append W₂).edges} ⊆ {x, y}) :
    bdry Γ.toGraph {g | g ∈ W₂.edges} ⊆ {u, y} := by
  have hnd : (W₁.support ++ W₂.support.tail).Nodup := by
    have h1 : (W₁.append W₂).support.Nodup := hs
    rwa [GraphWalk.support_append] at h1
  have hd := List.nodup_append.mp hnd
  intro z ⟨⟨g₁, hg₁, hig₁⟩, g₂, ⟨hg₂E, hg₂_not⟩, hig₂⟩
  have hzW₂ : z ∈ W₂.support := inc_mem_support W₂ hg₁ hig₁
  by_contra hz_not
  have hzu : z ≠ u := fun h => hz_not (Or.inl h)
  have hzy : z ≠ y := fun h => hz_not (Or.inr h)
  have hz_tail : z ∈ W₂.support.tail := by
    rw [W₂.support_eq_cons] at hzW₂
    exact (List.mem_cons.mp hzW₂).resolve_left hzu
  have hg₂_not₁ : g₂ ∉ W₁.edges := by
    intro hg₂_1
    have hzW₁ : z ∈ W₁.support := inc_mem_support W₁ hg₂_1 hig₂
    exact hd.2.2 z hzW₁ z hz_tail rfl
  have hg₁_full : g₁ ∈ (W₁.append W₂).edges := by
    rw [GraphWalk.edges_append]
    exact List.mem_append_right _ hg₁
  have hg₂_not_full : g₂ ∉ (W₁.append W₂).edges := by
    rw [GraphWalk.edges_append]
    exact fun h => (List.mem_append.mp h).elim hg₂_not₁ hg₂_not
  have hz_xy : z ∈ ({x, y} : Set S) :=
    hbd ⟨⟨g₁, hg₁_full, hig₁⟩, g₂, ⟨hg₂E, hg₂_not_full⟩, hig₂⟩
  rcases hz_xy with rfl | rfl
  · exact hd.2.2 z W₁.start_mem_support z hz_tail rfl
  · exact hzy rfl

omit [T2Space S] in
theorem walk_edgeSep_mem_tangle {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph ord T) (hord : 4 ≤ ord)
    {u y : S} (W : GraphWalk Γ.toGraph u y)
    (hsuff : ∀ ⦃w : S⦄ (W_a : GraphWalk Γ.toGraph u w) (W_b : GraphWalk Γ.toGraph w y),
      W = W_a.append W_b → bdry Γ.toGraph {g | g ∈ W_b.edges} ⊆ {w, y}) :
    (drawingEdgeSepA Γ {g | g ∈ W.edges}, drawingEdgeSepB Γ {g | g ∈ W.edges}) ∈ T := by
  induction W with
  | @nil u hu =>
    have hemp : {g : Set S | g ∈ (GraphWalk.nil hu : GraphWalk Γ.toGraph u u).edges} = ∅ := by
      ext g; simp [GraphWalk.edges]
    rw [hemp]
    have hsep := isSeparation_drawingEdgeSep Γ ∅
    have hbd_emp : bdry Γ.toGraph ∅ = ∅ := by
      ext z; simp [bdry, verts]
    have hord0 : separationOrder (drawingEdgeSepA Γ ∅) (drawingEdgeSepB Γ ∅) < ord := by
      rw [separationOrder, inter_vertexSet_drawingEdgeSep, hbd_emp, Set.ncard_empty]
      omega
    rcases hT.axiom1 hsep hord0 with h | h
    · exact h
    · exfalso
      refine hT.axiom3 h ?_
      change (Γ.V \ verts Γ.toGraph ∅) ∪ verts Γ.toGraph (Γ.E \ ∅) = Γ.V
      have hv0 : verts Γ.toGraph ∅ = ∅ := by ext z; simp [verts]
      have hsub : verts Γ.toGraph (Γ.E \ ∅) ⊆ Γ.V := fun _ ⟨_, _, _, hl⟩ => hl.left_mem
      rw [hv0, sdiff_empty, union_eq_self_of_subset_right hsub]
  | @cons u v y e hlink rest ih =>
    have hrest_mem : (drawingEdgeSepA Γ {g | g ∈ rest.edges},
        drawingEdgeSepB Γ {g | g ∈ rest.edges}) ∈ T :=
      ih fun w W_a W_b h_eq =>
        hsuff (GraphWalk.cons hlink W_a) W_b (by rw [h_eq]; rfl)
    have hends_sub : Γ.toHypergraph.ends e ⊆ {u, v} := by
      intro z hz
      have hinc : Γ.toGraph.Inc e z := inc_of_mem_closure hz.1 hz.2.2 hz.2.1
      obtain ⟨w, hlk⟩ := hinc
      exact Γ.toGraph.eq_or_eq_of_isLink_of_isLink hlk hlink
    have he_size : edgeSize Γ.toHypergraph e < ord := by
      have hle : (Γ.toHypergraph.ends e).ncard ≤ 2 :=
        (Set.ncard_le_ncard hends_sub (Set.toFinite _)).trans
          (Set.ncard_insert_le u {v} |>.trans (by simp))
      unfold edgeSize
      omega
    have hKe_mem : (edgeHypergraph Γ.toHypergraph e, Γ.toHypergraph.deleteEdges {e}) ∈ T :=
      (GM10.theorem_2_7_proof (by omega) hT.isSeparation hT.order_lt hT.axiom1 hT.axiom2).mp
        hT e hlink.edge_mem he_size
    let A₀ := drawingEdgeSepA Γ {g | g ∈ rest.edges}
    let B₀ := drawingEdgeSepB Γ {g | g ∈ rest.edges}
    let Ke := edgeHypergraph Γ.toHypergraph e
    let De := Γ.toHypergraph.deleteEdges {e}
    have hbd_rest : bdry Γ.toGraph {g | g ∈ rest.edges} ⊆ {v, y} :=
      hsuff (GraphWalk.cons hlink (.nil hlink.right_mem)) rest rfl
    have hinter_sub : ((A₀ ∪ Ke) ∩ (B₀ ∩ De)).vertexSet ⊆ {u, v, y} := by
      intro z ⟨hzA, hzB, _⟩
      rcases hzA with hzA₀ | hzKe
      · have hz_bd : z ∈ bdry Γ.toGraph {g | g ∈ rest.edges} := by
          rw [← inter_vertexSet_drawingEdgeSep]
          exact ⟨hzA₀, hzB⟩
        rcases hbd_rest hz_bd with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · rcases hends_sub hzKe with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
    have hord_union : separationOrder (A₀ ∪ Ke) (B₀ ∩ De) < ord := by
      have hle : ((A₀ ∪ Ke) ∩ (B₀ ∩ De)).vertexSet.ncard ≤ 3 :=
        (Set.ncard_le_ncard hinter_sub (Set.toFinite _)).trans
          ((Set.ncard_insert_le u {v, y}).trans
            (Nat.add_le_add_right ((Set.ncard_insert_le v {y}).trans (by simp)) 1))
      unfold separationOrder
      omega
    have hunion_mem : (A₀ ∪ Ke, B₀ ∩ De) ∈ T :=
      GM10.theorem_2_2_proof hT hrest_mem hKe_mem hord_union
    let E₁ : Set (Set S) := {g | g ∈ (GraphWalk.cons hlink rest).edges}
    have hbd₁ : bdry Γ.toGraph E₁ ⊆ {u, y} :=
      hsuff (.nil hlink.left_mem) (GraphWalk.cons hlink rest) rfl
    have hord₁ : separationOrder (drawingEdgeSepA Γ E₁) (drawingEdgeSepB Γ E₁) < ord := by
      rw [separationOrder, inter_vertexSet_drawingEdgeSep]
      have hle : (bdry Γ.toGraph E₁).ncard ≤ 2 :=
        (Set.ncard_le_ncard hbd₁ (Set.toFinite _)).trans
          (Set.ncard_insert_le u {y} |>.trans (by simp))
      omega
    have hE₁_sub : (drawingEdgeSepA Γ E₁).edgeSet ⊆ (A₀ ∪ Ke).edgeSet := by
      rintro g ⟨hg, hgE⟩
      simp only [E₁, GraphWalk.edges, List.mem_cons, mem_ofPred_eq] at hg
      rcases hg with rfl | hg_rest
      · exact Or.inr (mem_singleton g)
      · exact Or.inl ⟨hg_rest, hgE⟩
    exact GM10.theorem_2_9_proof hT hunion_mem (isSeparation_drawingEdgeSep Γ E₁) hord₁
      (Or.inr (Or.inr ⟨by omega, hE₁_sub⟩))

omit [T2Space S] in
/-- Any separation `(A, B)` of `Γ.toHypergraph` of order `< ord` (`4 ≤ ord`) whose left-hand edge
set `A.edgeSet` is contained in the edge set `E(Q)` of a path `Q` (`IsGraphPathWithEnds Γ.toGraph Q
x y`)
with `bdry Γ.toGraph E(Q) ⊆ {x, y}` belongs to the tangle `T`. -/
theorem path_sep_mem_tangle {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph ord T) (hord : 4 ≤ ord)
    {x y : S} {Q : Graph S (Set S)} (hQ : IsGraphPathWithEnds Γ.toGraph Q x y)
    (hbd : bdry Γ.toGraph E(Q) ⊆ {x, y})
    {A B : Hypergraph S (Set S)} (hsep : Γ.toHypergraph.IsSeparation A B)
    (hAB_ord : separationOrder A B < ord) (hAE : A.edgeSet ⊆ E(Q)) :
    (A, B) ∈ T := by
  obtain ⟨hle, W, hs, _, hE⟩ := hQ
  obtain ⟨W_Γ, hsupp, hedges⟩ := W.exists_transfer (G' := Γ.toGraph)
    (fun _ _ _ _ hlk => hlk.mono hle)
    (fun z hz => hle.vertexSet_mono (W.mem_vertexSet_of_mem_support hz))
  have hs_Γ : W_Γ.IsSimple := by
    change W_Γ.support.Nodup
    rw [hsupp]
    exact hs
  have hEQ : E(Q) = {g | g ∈ W_Γ.edges} := by
    rw [hE, hedges]
  have hbd_W : bdry Γ.toGraph {g | g ∈ W_Γ.edges} ⊆ {x, y} := hEQ ▸ hbd
  have hmem_EQ : (drawingEdgeSepA Γ E(Q), drawingEdgeSepB Γ E(Q)) ∈ T := by
    rw [hEQ]
    exact walk_edgeSep_mem_tangle hT hord W_Γ fun w W_a W_b h_eq =>
      suffix_bdry_subset W_a W_b (h_eq ▸ hs_Γ) (h_eq ▸ hbd_W)
  have hA_sub : A.edgeSet ⊆ (drawingEdgeSepA Γ E(Q)).edgeSet :=
    fun e he => ⟨hAE he, hsep.left_le.edgeSet_subset he⟩
  exact GM10.theorem_2_9_proof hT hmem_EQ hsep hAB_ord (Or.inr (Or.inr ⟨by omega, hA_sub⟩))

/-- In a closed disc `Δ` with `subBd Δ = F` and `F ∩ Γ.U ⊆ Γ.V`, every vertex of `Γ` in `Δ \ F`
belongs to `verts Γ.toGraph {e ∈ Γ.E | e ⊆ Δ}` (when `SubData Γ.toGraph G₀ P`). -/
theorem mem_verts_inter_of_mem_diff_bd {Γ : Drawing S} {G₀ : Graph S (Set S)}
    {P : Set S → Graph S (Set S)} (hS : IsClosedSurface S)
    (hsd : SubData Γ.toGraph G₀ P) {Δ F : Set S} (hΔ : IsClosedDisc Δ)
    (hbd : subBd Δ = F) (hF_norm : F ∩ Γ.U ⊆ Γ.V) {v : S} (hvV : v ∈ Γ.V) (hvΔ : v ∈ Δ \ F) :
    v ∈ verts Γ.toGraph {e ∈ Γ.E | e ⊆ Δ} := by
  obtain ⟨g, hgE, hig⟩ := SubDataSepGeneral.exists_inc_of_mem_V hsd hvV
  have hvc : v ∈ closure g := mem_closure_of_inc hig
  have hOpen : IsOpen (Δ \ F) := hbd ▸ (IsClosedDisc.isOpenDisc_diff_subBd hS hΔ).1.1
  obtain ⟨y, hy_open, hyg⟩ := mem_closure_iff.mp hvc (Δ \ F) hOpen hvΔ
  have hgΔ : g ⊆ Δ :=
    edge_subset_of_inter_nonempty hΔ.isClosed (hbd ▸ hF_norm) hgE ⟨y, hyg, hy_open.1⟩
  exact ⟨g, ⟨hgE, hgΔ⟩, hig⟩

/-! ## 2. Proof of `H.IsTwoCell`, Respectful Tangle, Metric, and `IsRigid H` -/

/-- On a connected closed non-spherical surface `S`, a drawing `H` with `H.IsRepresentative θ`
(`1 ≤ θ`) cannot have `H.U` contained in a closed disc `Δ ⊆ S`. -/
theorem not_U_subset_closedDisc_of_representative [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) {H : Drawing S} {θ : ℕ}
    (hθ : 1 ≤ θ) (hrep : H.IsRepresentative θ) {Δ : Set S} (hΔ : IsClosedDisc Δ)
    (hU_sub : H.U ⊆ Δ) : False := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨Δ', hΔ', h₁, -⟩ := exists_disc_around hman hΔ (fun x _ => hS.2.2 x) isOpen_univ
    (subset_univ _)
  have hO := IsClosedDisc.isOArc_discBd hΔ'
  have hif : Δ' \ discBd Δ' = interior Δ' := by
    have := IsClosedDisc.frontier_eq_discBd hS hΔ'
    rw [← this, frontier, (IsClosedDisc.isCompact hΔ').isClosed.closure_eq]
    ext x
    constructor
    · rintro ⟨ha, hb⟩
      by_contra h
      exact hb ⟨ha, h⟩
    · exact fun h => ⟨interior_subset h, fun h' => h'.2 h⟩
  let Y : Set S := (interior Δ')ᶜ
  have hYc : IsClosed Y := isOpen_interior.isClosed_compl
  have hbY : discBd Δ' ⊆ Y := fun x hx hi => by
    rw [← hif] at hi
    exact hi.2 hx
  have hY_disj_Δ : Disjoint Y Δ := disjoint_left.mpr fun x hxY hxΔ =>
    hxY (hif ▸ h₁ hxΔ)
  obtain ⟨a, ha⟩ := (infinite_of_isOArc hO).nonempty
  obtain ⟨N, hNU, -⟩ := exists_drawing_on_oArc hO (finite_singleton a)
    (singleton_nonempty a) (singleton_subset_iff.mpr ha)
  have hYn : GM11.IsNice Y := ⟨N, isGammaNice_of_frontier (Drawing.IsSubdrawing.refl N) (hNU ▸ hbY)
    (by
    rw [hNU, frontier_compl, ← IsClosedDisc.frontier_eq_discBd hS hΔ']
    exact frontier_interior_subset)⟩
  have hu : Y ≠ univ := fun h => by
    obtain ⟨x, hx⟩ := (infinite_of_isOArc (IsClosedDisc.isOArc_discBd hΔ)).nonempty
    exact (h ▸ mem_univ x : x ∈ Y) (hif ▸ h₁ (Surface.discBd_subset Δ hx))
  obtain ⟨E, hE, -, hYE⟩ := GM11.theorem_7_5_proof hS hYc hYn hu finite_empty (disjoint_empty _)
    fun F hFY hF => by
      rw [sdiff_empty]
      have hF_disj : Disjoint F H.U :=
        disjoint_left.mpr fun x hxF hxU => disjoint_left.mp hY_disj_Δ (hFY hxF) (hU_sub hxU)
      have hF_norm : H.IsNormal F := fun x ⟨hxF, hxU⟩ => (disjoint_left.mp hF_disj hxF hxU).elim
      have hF_V : F ∩ H.V = ∅ := eq_empty_iff_forall_notMem.mpr fun x ⟨hxF, hxV⟩ =>
        disjoint_left.mp hF_disj hxF (H.V_subset_U hxV)
      have hcard : (F ∩ H.V).ncard < θ := by
        rw [hF_V, Set.ncard_empty]
        exact hθ
      exact hrep.2 F hF hF_norm hcard
  obtain ⟨D, ⟨hDE, hD, hb, -⟩, -⟩ := disc_oArc E (discBd Δ') hE (hbY.trans hYE) hO
  obtain rfl : D = Δ' := eq_of_discBd_eq (IsClosedSurface.isSurface hS) hns hD hΔ' hb
  have huE : E = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ interior D
    · exact hDE (interior_subset hx)
    · exact hYE hx
  have hfr := IsClosedDisc.frontier_eq_discBd hS hE
  rw [huE, frontier_univ] at hfr
  have hO' := IsClosedDisc.isOArc_discBd hE
  rw [huE, ← hfr] at hO'
  exact (infinite_of_isOArc hO').nonempty.ne_empty rfl

/-- When `SubData H.toGraph G₀ P` holds, `E(H.toGraph) \ {e ∈ H.E | e ⊆ Δ}` is nonempty for every
closed disc `Δ ⊆ S` with `subBd Δ ∩ H.U ⊆ H.V` on a non-spherical surface `S` where `H` is
`θ`-representative (`1 ≤ θ`). -/
theorem compl_disc_edges_nonempty [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) {H : Drawing S} {G₀ : Graph S (Set S)}
    {P : Set S → Graph S (Set S)} (hsd : SubData H.toGraph G₀ P) {θ : ℕ}
    (hθ : 1 ≤ θ) (hrep : H.IsRepresentative θ) {Δ : Set S} (hΔ : IsClosedDisc Δ) :
    (E(H.toGraph) \ {e ∈ H.E | e ⊆ Δ}).Nonempty := by
  by_contra hemp
  rw [not_nonempty_iff_eq_empty] at hemp
  have hE_sub : ∀ e ∈ H.E, e ⊆ Δ := by
    intro e he
    by_contra hnot
    have : e ∈ E(H.toGraph) \ {e ∈ H.E | e ⊆ Δ} := ⟨he, fun h => hnot h.2⟩
    rw [hemp] at this
    exact this
  have hV_sub : H.V ⊆ Δ := by
    intro v hv
    obtain ⟨g, hgE, hig⟩ := SubDataSepGeneral.exists_inc_of_mem_V hsd hv
    exact hΔ.isClosed.closure_subset_iff.mpr (hE_sub g hgE) (mem_closure_of_inc hig)
  have hU_sub : H.U ⊆ Δ := by
    intro x hxU
    by_cases hxV : x ∈ H.V
    · exact hV_sub hxV
    · obtain ⟨e, heE, hxe⟩ := H.exists_edge_of_mem hxU hxV
      exact hE_sub e heE hxe
  exact not_U_subset_closedDisc_of_representative hS hns hθ hrep hΔ hU_sub

/-- **Lemma 1a (`H.IsTwoCell`):** If `H` is a drawing of representativity `≥ 1` on a connected
closed non-spherical surface `S` whose graph is a subdivision of a simple 3-connected graph, then
`H.IsTwoCell`. -/
theorem isTwoCell_of_subdivision_and_representative [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) {H : Drawing S}
    (hsub : IsSubdivisionOfSimpleThreeConnected H.toGraph)
    {θ : ℕ} (hθ : 1 ≤ θ) (hrep : H.IsRepresentative θ) :
    H.IsTwoCell := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨G₀, P, hsd⟩ := exists_subData hsub
  have hU_ne : H.U.Nonempty := by
    have h4 := hsd.simple.2.1
    have hV₀_ne : V(G₀).Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Set.ncard_empty] at h4
      omega
    obtain ⟨v₀, hv₀⟩ := hV₀_ne
    exact ⟨v₀, H.V_subset_U (hsd.sub hv₀)⟩
  refine ⟨inferInstance, fun r hr => ?_⟩
  have h_od := open_disc S r hS ‹ConnectedSpace S›
    ⟨region_nonempty hr, region_isPreconnected hr⟩ (region_isOpen hr)
    (fun F hFr hF => by
      have hFU_emp : F ∩ H.U = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun x ⟨hxF, hxU⟩ => region_subset hr (hFr hxF) hxU
      have hF_norm : H.IsNormal F := by
        change F ∩ H.U ⊆ H.V
        rw [hFU_emp]
        exact empty_subset _
      have hFV_emp : F ∩ H.V = ∅ :=
        eq_empty_of_subset (inter_subset_inter_right F H.V_subset_U) hFU_emp
      have hcard : (F ∩ H.V).ncard < θ := by
        rw [hFV_emp, Set.ncard_empty]
        exact hθ
      have hnull := hrep.2 F hF hF_norm hcard
      have hbdS : Disjoint F (bd S) := disjoint_left.mpr fun x _ hx => hx (hS.2.2 x)
      obtain ⟨Δ, -, hΔ, hbΔ⟩ :=
        (epstein S univ F (IsClosedSurface.isSurface hS) inferInstance hF
          (subset_univ F) hbdS).1 hnull
      have hsbΔ : subBd Δ = F := (IsClosedDisc.subBd_eq_discBd hS hΔ).trans hbΔ
      let A_E : Set (Set S) := {e ∈ H.E | e ⊆ Δ}
      have hAE_emp : A_E = ∅ := by
        by_contra hAE_ne
        rw [← Ne, ← nonempty_iff_ne_empty] at hAE_ne
        have hcompl_ne := compl_disc_edges_nonempty hS hns hsd hθ hrep hΔ
        have hbd_sub : bdry H.toGraph A_E ⊆ F ∩ H.V := by
          rintro z ⟨⟨e₁, ⟨he₁E, he₁Δ⟩, hie₁⟩, e₂, ⟨he₂E, he₂_not⟩, hie₂⟩
          have hzV : z ∈ H.V := hie₁.vertex_mem
          have hzΔ : z ∈ Δ := hΔ.isClosed.closure_subset_iff.mpr he₁Δ (mem_closure_of_inc hie₁)
          have hzF : z ∈ F := by
            by_contra hz_not_F
            have hOpen : IsOpen (Δ \ F) :=
              hsbΔ ▸ (IsClosedDisc.isOpenDisc_diff_subBd hS hΔ).1.1
            obtain ⟨y, hy_open, hye₂⟩ :=
              mem_closure_iff.mp (mem_closure_of_inc hie₂) (Δ \ F) hOpen ⟨hzΔ, hz_not_F⟩
            have he₂Δ : e₂ ⊆ Δ :=
              edge_subset_of_inter_nonempty hΔ.isClosed (hsbΔ ▸ hF_norm) he₂E ⟨y, hye₂, hy_open.1⟩
            exact he₂_not ⟨he₂E, he₂Δ⟩
          exact ⟨hzF, hzV⟩
        rw [hFV_emp, subset_empty_iff] at hbd_sub
        have hbd_card : (bdry H.toGraph A_E).ncard ≤ 2 := by
          rw [hbd_sub, Set.ncard_empty]
          omega
        have hAE_sub : A_E ⊆ E(H.toGraph) := fun _ he => he.1
        obtain ⟨_, x, y, _, _, _, hbd_eq, _, _, _⟩ :=
          SubDataSepGeneral.sep_general hsd hAE_sub hbd_card hAE_ne hcompl_ne
        rw [hbd_sub] at hbd_eq
        exact (Set.insert_nonempty x {y}).ne_empty hbd_eq.symm
      have hΔ_disj : Disjoint Δ H.U := by
        refine disjoint_left.mpr fun z hzΔ hzU => ?_
        by_cases hzF : z ∈ F
        · exact (eq_empty_iff_forall_notMem.mp hFU_emp z) ⟨hzF, hzU⟩
        · by_cases hzV : z ∈ H.V
          · have hz_verts :=
              mem_verts_inter_of_mem_diff_bd hS hsd hΔ hsbΔ hF_norm hzV ⟨hzΔ, hzF⟩
            change z ∈ verts H.toGraph A_E at hz_verts
            rw [hAE_emp] at hz_verts
            rcases hz_verts with ⟨_, hg, _⟩
            exact hg
          · obtain ⟨g, hgE, hzg⟩ := H.exists_edge_of_mem hzU hzV
            have hgΔ : g ⊆ Δ :=
              edge_subset_of_inter_nonempty hΔ.isClosed (hsbΔ ▸ hF_norm) hgE ⟨z, hzg, hzΔ⟩
            have hg_AE : g ∈ A_E := ⟨hgE, hgΔ⟩
            rw [hAE_emp] at hg_AE
            exact hg_AE
      obtain ⟨φ⟩ := hF
      have hpF : (φ 1).1 ∈ F := (φ 1).2
      have hpΔ : (φ 1).1 ∈ Δ := Surface.discBd_subset Δ (hbΔ.symm ▸ hpF)
      have hΔr : Δ ⊆ r :=
        subset_region hr hΔ.isPathConnected.isConnected.isPreconnected hΔ_disj hpΔ (hFr hpF)
      exact ⟨Δ, hΔr, hΔ, hbΔ⟩)
  rcases h_od with ⟨_, hr_univ⟩ | hr_disc
  · exfalso
    obtain ⟨x, hx⟩ := hU_ne
    exact region_subset hr (hr_univ ▸ mem_univ x) hx
  · exact hr_disc

/-- **Lemma 2 (`IsRespectfulDrawingTangle` and `HasTangleMetric`):** From `H.IsTwoCell` and
`H.IsRepresentative θ` (`1 ≤ θ`) on a connected closed non-spherical surface `S`, constructs the
respectful tangle `T` of order `θ` and its metric `d`. -/
theorem exists_respectful_tangle_and_metric [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) {H : Drawing S} {θ : ℕ}
    (hθ : 1 ≤ θ) (h2cell : H.IsTwoCell) (hrep : H.IsRepresentative θ) :
    ∃ (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ),
      IsRespectfulDrawingTangle H θ T ∧ HasTangleMetric H θ T d := by
  obtain ⟨T, ⟨hT_tangle, hT_resp⟩, _⟩ :=
    GM11.theorem_4_1_proof (Γ := PaintingOrDrawing.drawing H) hS hns hθ h2cell hrep
  have hT : IsRespectfulDrawingTangle H θ T := ⟨h2cell, hT_tangle, hT_resp⟩
  obtain ⟨d, hd⟩ := GM12.exists_metric_of_respectful_drawing_tangle hS hT
  exact ⟨T, d, hT, hd⟩

/-- **Lemma 1b (`IsRigid H`):** If `H` is a drawing on a connected closed non-spherical surface `S`
whose graph is a subdivision of a simple 3-connected graph and `H` has a respectful tangle `T` of
order `θ ≥ 4` and is `θ`-representative, then `IsRigid H`. -/
theorem isRigid_of_subdivision_and_respectful_tangle [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) {H : Drawing S}
    (hsub : IsSubdivisionOfSimpleThreeConnected H.toGraph)
    {θ : ℕ} (hθ : 4 ≤ θ) (hrep : H.IsRepresentative θ)
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle H θ T) :
    IsRigid H := by
  obtain ⟨G₀, P, hsd⟩ := exists_subData hsub
  intro F hF_oarc hF_norm hF_card
  have hcard_lt : (F ∩ H.V).ncard < θ := by omega
  obtain ⟨Δ, hΔ, hsbΔ, hmem_in⟩ := hT.2.2.2 F hF_oarc hF_norm hcard_lt
  refine ⟨Δ, ⟨hΔ, hsbΔ, ?_⟩⟩
  let A_E : Set (Set S) := {e ∈ H.E | e ⊆ Δ}
  have hA_E_sub : A_E ⊆ E(H.toGraph) := fun _ he => he.1
  have hinter_E : (H.interSet Δ).E = A_E := by
    change (H.span _ _).E = _
    rw [H.span_E]
    ext e
    simp only [A_E, mem_inter_iff, mem_ofPred_eq]
    tauto
  obtain ⟨hinter_V, _⟩ := interSet_V_and_U hΔ.isClosed (hsbΔ ▸ hF_norm)
  by_cases hAE_ne : A_E.Nonempty
  · right
    have hcompl_ne : (E(H.toGraph) \ A_E).Nonempty :=
      compl_disc_edges_nonempty hS hns hsd (by omega) hrep hΔ
    have hbd_AE_sub : bdry H.toGraph A_E ⊆ F ∩ H.V := by
      rintro z ⟨⟨e₁, ⟨he₁E, he₁Δ⟩, hie₁⟩, e₂, ⟨he₂E, he₂_not⟩, hie₂⟩
      have hzV : z ∈ H.V := hie₁.vertex_mem
      have hzΔ : z ∈ Δ := hΔ.isClosed.closure_subset_iff.mpr he₁Δ (mem_closure_of_inc hie₁)
      have hzF : z ∈ F := by
        by_contra hz_not_F
        have hOpen : IsOpen (Δ \ F) :=
          hsbΔ ▸ (IsClosedDisc.isOpenDisc_diff_subBd hS hΔ).1.1
        obtain ⟨y, hy_open, hye₂⟩ :=
          mem_closure_iff.mp (mem_closure_of_inc hie₂) (Δ \ F) hOpen ⟨hzΔ, hz_not_F⟩
        have he₂Δ : e₂ ⊆ Δ :=
          edge_subset_of_inter_nonempty hΔ.isClosed (hsbΔ ▸ hF_norm) he₂E ⟨y, hye₂, hy_open.1⟩
        exact he₂_not ⟨he₂E, he₂Δ⟩
      exact ⟨hzF, hzV⟩
    have hbd_AE_card : (bdry H.toGraph A_E).ncard ≤ 2 :=
      (Set.ncard_le_ncard hbd_AE_sub (H.finite_V.subset inter_subset_right)).trans hF_card
    obtain ⟨_, x, y, Q, _, hxy, hbd_eq, _, hQ_path, hcases⟩ :=
      SubDataSepGeneral.sep_general hsd hA_E_sub hbd_AE_card hAE_ne hcompl_ne
    have hFV_eq : F ∩ H.V = {x, y} := by
      have hsub_xy : ({x, y} : Set S) ⊆ F ∩ H.V := hbd_eq ▸ hbd_AE_sub
      exact (Set.eq_of_subset_of_ncard_le hsub_xy
        (by rw [Set.ncard_pair hxy]; exact hF_card)
        (H.finite_V.subset inter_subset_right)).symm
    rcases hcases with ⟨hAE_eq, hAV_eq⟩ | ⟨hcompl_eq, _⟩
    · refine ⟨x, y, hxy, hFV_eq, ?_⟩
      obtain ⟨hle_Q, W_Q, hs_Q, hV_Q, hE_Q⟩ := hQ_path
      have hP_V : (H.interSet Δ).V = V(Q) := by
        rw [hinter_V, ← hAV_eq]
        ext z
        constructor
        · rintro ⟨hzV, hzΔ⟩
          by_cases hzF : z ∈ F
          · have hz_xy : z ∈ bdry H.toGraph A_E := by
              rw [hbd_eq, ← hFV_eq]
              exact ⟨hzF, hzV⟩
            exact hz_xy.1
          · exact mem_verts_inter_of_mem_diff_bd hS hsd hΔ hsbΔ hF_norm hzV ⟨hzΔ, hzF⟩
        · rintro ⟨g, ⟨hgE, hgΔ⟩, hig⟩
          exact ⟨hig.vertex_mem, hΔ.isClosed.closure_subset_iff.mpr hgΔ (mem_closure_of_inc hig)⟩
      have hP_E : (H.interSet Δ).E = E(Q) := hinter_E.trans hAE_eq
      have hP_sub : (H.interSet Δ).IsSubdrawing H := H.span_isSubdrawing _ _
      obtain ⟨W_P, hsupp_P, hedges_P⟩ := W_Q.exists_transfer (G' := (H.interSet Δ).toGraph)
        (fun _ _ _ _ hlk => (hP_sub.isLink_iff (hP_E.symm ▸ hlk.edge_mem)).mpr (hlk.mono hle_Q))
        (fun z hz => by
          change z ∈ (H.interSet Δ).V
          rw [hP_V, hV_Q]
          exact hz)
      have hs_P : W_P.IsSimple := by
        change W_P.support.Nodup
        rw [hsupp_P]
        exact hs_Q
      exact ⟨W_P, hs_P, by rw [hP_V, hV_Q, hsupp_P], by rw [hP_E, hE_Q, hedges_P]⟩
    · exfalso
      have hfrΔ : frontier Δ = F := by rw [← subBd_eq_frontier, hsbΔ]
      have hsep₁ : H.toHypergraph.IsSeparation
          ((PaintingOrDrawing.drawing H).inter Δ)
          ((PaintingOrDrawing.drawing H).interOutside Δ) :=
        GM11.isSeparation_inter (Γ := PaintingOrDrawing.drawing H) hΔ.isClosed
          (by rw [hfrΔ]; exact hF_norm)
      have hsep₂ : H.toHypergraph.IsSeparation
          ((PaintingOrDrawing.drawing H).interOutside Δ)
          ((PaintingOrDrawing.drawing H).inter Δ) :=
        hsep₁.symm
      have hinter_sub :
          ((PaintingOrDrawing.drawing H).interOutside Δ ∩
            (PaintingOrDrawing.drawing H).inter Δ).vertexSet ⊆ F ∩ H.V := by
        intro z ⟨hz_out, hz_in⟩
        rw [← hfrΔ]
        exact GM11.inter_outside_subset (Γ := PaintingOrDrawing.drawing H) ⟨hz_in, hz_out⟩
      have hord₂_le : separationOrder
          ((PaintingOrDrawing.drawing H).interOutside Δ)
          ((PaintingOrDrawing.drawing H).inter Δ) ≤ 2 :=
        (Set.ncard_le_ncard hinter_sub (H.finite_V.subset inter_subset_right)).trans hF_card
      have hE₂_sub : ((PaintingOrDrawing.drawing H).interOutside Δ).edgeSet ⊆ E(Q) := by
        rw [← hcompl_eq]
        rintro g ⟨hgE, hg_out⟩
        refine ⟨hgE, fun ⟨_, hgΔ⟩ => ?_⟩
        obtain ⟨z, hz⟩ := hgE.1
        have hzF : z ∈ F := by
          rw [← hfrΔ, frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
          exact ⟨subset_closure (hgΔ hz), hg_out hz⟩
        exact (hgE.2.1 hz).2 (hF_norm ⟨hzF, (hgE.2.1 hz).1⟩)
      have hbd_Q : bdry H.toGraph E(Q) ⊆ {x, y} := by
        rw [← hcompl_eq, bdry_compl hA_E_sub, hbd_eq]
      have hmem_out :
          ((PaintingOrDrawing.drawing H).interOutside Δ,
            (PaintingOrDrawing.drawing H).inter Δ) ∈ T :=
        path_sep_mem_tangle hT.2.1 hθ hQ_path hbd_Q hsep₂ (by omega) hE₂_sub
      exact hT.2.1.axiom2 hmem_in hmem_out hmem_out
        (by rw [GM10.union_assoc, GM10.union_self, hsep₁.union_eq])
  · left
    rw [not_nonempty_iff_eq_empty] at hAE_ne
    rintro z ⟨hzΔ, hzU⟩
    by_contra hz_not_F
    by_cases hzV : z ∈ H.V
    · have hz_verts :=
        mem_verts_inter_of_mem_diff_bd hS hsd hΔ hsbΔ hF_norm hzV ⟨hzΔ, hz_not_F⟩
      change z ∈ verts H.toGraph A_E at hz_verts
      rw [hAE_ne] at hz_verts
      rcases hz_verts with ⟨_, hg, _⟩
      exact hg
    · obtain ⟨g, hgE, hzg⟩ := H.exists_edge_of_mem hzU hzV
      have hgΔ : g ⊆ Δ :=
        edge_subset_of_inter_nonempty hΔ.isClosed (hsbΔ ▸ hF_norm) hgE ⟨z, hzg, hzΔ⟩
      have hg_AE : g ∈ A_E := ⟨hgE, hgΔ⟩
      rw [hAE_ne] at hg_AE
      exact hg_AE

/-- Combined first part of the Section 10 translation: under the hypotheses of (1.1), `H` is 2-cell
and rigid and admits a respectful tangle `T` of order `209` with tangle metric `d`. -/
theorem isRigid_and_isTwoCell_of_subdivision_and_representative
    [ConnectedSpace S] (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    {α : Type u} {β : Type v} {G : Graph α β} {H : Drawing S} (η : SpanEmbedding H G)
    (hH_subdiv : IsSubdivisionOfSimpleThreeConnected η.imageGraph)
    (hrep : H.IsRepresentative 209) :
    ∃ (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ),
      H.IsTwoCell ∧ IsRigid H ∧
      IsRespectfulDrawingTangle H 209 T ∧ HasTangleMetric H 209 T d := by
  have hsub_H : IsSubdivisionOfSimpleThreeConnected H.toGraph :=
    isSubdivision_toGraph_of_spanEmbedding η hH_subdiv
  have h2cell : H.IsTwoCell :=
    isTwoCell_of_subdivision_and_representative hS hns hsub_H (by omega) hrep
  obtain ⟨T, d, hT, hd⟩ :=
    exists_respectful_tangle_and_metric hS hns (by omega) h2cell hrep
  have hrigid : IsRigid H :=
    isRigid_of_subdivision_and_respectful_tangle hS hns hsub_H (by omega) hrep hT
  exact ⟨T, d, h2cell, hrigid, hT, hd⟩

end TanglePathSep

end GraphMinor.GM14
