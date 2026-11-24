/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section12c

/-!
# Moving a portrayal to another hypergraph on the same vertices

Let `π` be a portrayal of `H₁`, and let `H₂` be a hypergraph with the same vertices, each of whose
edges lies inside an edge of `H₁`, or has at most one end. Keep the painting, `β` and `γ`, and the
vertices of each cell. Put each edge of `H₂` into a cell that holds its ends, and in which any two
of its ends are adjacent. The result is a portrayal of `H₂`, and its warps do not go up, because the
1-skeleton of each cell does not grow.

Graph Minors XVII does this silently in three places: in the proof of (12.6), to pass between `G ∪
G*`, `G` and `G*`; in the proof of (13.3), to pass between `G \ Z` and `G / Z`; and in the proof of
(14.2). We use it for all of them.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

universe u v w

variable {α : Type u} {β₁ : Type v} {β₂ : Type w}

/-- Each edge of `H₂` lies inside an edge of `H₁`, or has at most one end. -/
@[expose] def EdgesCovered (H₂ : Hypergraph α β₂) (H₁ : Hypergraph α β₁) : Prop :=
  ∀ e ∈ H₂.edgeSet, (∃ e₁ ∈ H₁.edgeSet, H₂.ends e ⊆ H₁.ends e₁) ∨ (H₂.ends e).Subsingleton

/-- A tangle needs a vertex: so a portrayal of a hypergraph with a tangle has a cell. -/
theorem Portrayal.cells_nonempty {β : Type v} {G : Hypergraph α β} {θ : ℕ} {𝒯 : Set
  (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G) : π.Γ.C.Nonempty := by
  by_cases hV : G.vertexSet.Nonempty
  · obtain ⟨v, hv⟩ := hV
    obtain ⟨c, hc, -⟩ := π.p1_vertex v hv
    exact ⟨c, hc⟩
  · exfalso
    have hV' : G.vertexSet = ∅ := not_nonempty_iff_eq_empty.1 hV
    have hs : G.IsSeparation G (G.deleteEdges G.edgeSet) :=
      isSeparation_deleteEdges le_rfl le_rfl (by simp) (by simp)
    have hord : separationOrder G (G.deleteEdges G.edgeSet) < θ := by
      have : separationOrder G (G.deleteEdges G.edgeSet) = 0 := by
        change (G.vertexSet ∩ G.vertexSet).ncard = 0
        simp [hV']
      have := h𝒯.one_le
      omega
    rcases h𝒯.axiom1 hs hord with h | h
    · exact h𝒯.axiom3 h rfl
    · exact h𝒯.axiom3 h rfl

/-- A cell for each edge of `H₂`, as in the head of this file. -/
theorem Portrayal.exists_cellChoice {H₁ : Hypergraph α β₁} (π : Portrayal H₁) {H₂ : Hypergraph α β₂}
    (hV : H₂.vertexSet = H₁.vertexSet) (hne : π.Γ.C.Nonempty) (hcov : EdgesCovered H₂ H₁) :
    ∃ f : β₂ → Set π.S, ∀ e ∈ H₂.edgeSet, f e ∈ π.Γ.C ∧ H₂.ends e ⊆ (π.cellGraph (f e)).vertexSet ∧
      ∀ x ∈ H₂.ends e, ∀ y ∈ H₂.ends e, x ≠ y → (π.cellGraph (f e)).skeleton.Adj x y := by
  have h : ∀ e, ∃ c : Set π.S, e ∈ H₂.edgeSet → c ∈ π.Γ.C ∧ H₂.ends e ⊆ (π.cellGraph c).vertexSet ∧
      ∀ x ∈ H₂.ends e, ∀ y ∈ H₂.ends e, x ≠ y → (π.cellGraph c).skeleton.Adj x y := by
    intro e
    by_cases he : e ∈ H₂.edgeSet
    · rcases hcov e he with ⟨e₁, he₁, hsub⟩ | hsub
      · obtain ⟨c, hc, hec⟩ := π.p1_edge e₁ he₁
        refine ⟨c, fun _ => ⟨hc, fun x hx => ?_, fun x hx y hy hxy => skeleton_adj_of_mem
          (π.cellGraph_le c hc) hec (hsub hx) (hsub hy) hxy⟩⟩
        have h1 : x ∈ (π.cellGraph c).ends e₁ := by
          rw [← (π.cellGraph_le c hc).ends_eq e₁ hec]
          exact hsub hx
        exact (π.cellGraph c).vertex_mem_of_inc h1
      · rcases (H₂.ends e).eq_empty_or_nonempty with h0 | ⟨v, hv⟩
        · obtain ⟨c, hc⟩ := hne
          exact ⟨c, fun _ => ⟨hc, by simp [h0], by simp [h0]⟩⟩
        · have hv' : v ∈ H₁.vertexSet := hV ▸ H₂.vertex_mem_of_inc hv
          obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv'
          refine ⟨c, fun _ => ⟨hc, fun x hx => ?_, fun x hx y hy hxy => absurd (hsub hx hy) hxy⟩⟩
          rw [hsub hx hv]
          exact hvc
    · exact ⟨∅, fun h => absurd h he⟩
  choose f hf using h
  exact ⟨f, fun e he => hf e he⟩

/-- The cell `c` of the moved portrayal: the vertices of `α(c)`, and the edges sent to `c`. -/
@[expose] def reEdgeCell {H₁ : Hypergraph α β₁} (π : Portrayal H₁) (H₂ : Hypergraph α β₂) (f : β₂
  → Set π.S)
    (hf : ∀ e ∈ H₂.edgeSet, H₂.ends e ⊆ (π.cellGraph (f e)).vertexSet)
      (c : Set π.S) : Hypergraph α β₂ where
  vertexSet := (π.cellGraph c).vertexSet
  edgeSet := {e ∈ H₂.edgeSet | f e = c}
  Inc e v := H₂.Inc e v ∧ f e = c
  vertex_mem_of_inc := by
    rintro e v ⟨h, rfl⟩
    exact hf e (H₂.edge_mem_of_inc h) h
  edge_mem_of_inc := fun _ _ h => ⟨H₂.edge_mem_of_inc h.1, h.2⟩
  vertexSet_finite := (π.cellGraph c).vertexSet_finite
  edgeSet_finite := H₂.edgeSet_finite.subset (sep_subset _ _)

/-- The moved portrayal. Every condition (P2) to (P7) speaks only of the vertices of cells, of `β`
and of `γ`, which do not change. -/
@[expose] noncomputable def Portrayal.reEdge {H₁ : Hypergraph α β₁} (π : Portrayal H₁)
  (H₂ : Hypergraph α β₂)
    (hV : H₂.vertexSet = H₁.vertexSet) (f : β₂ → Set π.S)
    (hC : ∀ e ∈ H₂.edgeSet, f e ∈ π.Γ.C)
    (hf : ∀ e ∈ H₂.edgeSet, H₂.ends e ⊆ (π.cellGraph (f e)).vertexSet) : Portrayal H₂ where
  S := π.S
  isSurface := π.isSurface
  connected := π.connected
  Γ := π.Γ
  cellGraph := reEdgeCell π H₂ f hf
  borderSet := π.borderSet
  domγ := π.domγ
  nodeVertex := π.nodeVertex
  cellGraph_le := fun c hc => ⟨hV ▸ (π.cellGraph_le c hc).vertexSet_subset, sep_subset _ _, fun e
    he => by
    ext v
    exact ⟨fun h => ⟨h, he.2⟩, fun h => h.1⟩⟩
  borderSet_subset := fun n hn => hV ▸ π.borderSet_subset n hn
  domγ_subset := π.domγ_subset
  nodeVertex_mem := fun n hn => hV ▸ π.nodeVertex_mem n hn
  nodeVertex_injOn := π.nodeVertex_injOn
  p1_vertex := fun v hv => π.p1_vertex v (hV ▸ hv)
  p1_edge := fun e he => ⟨f e, hC e he, he, rfl⟩
  p1_disjoint := fun c _ c' _ hne => Set.disjoint_left.2 fun e h h' => hne (h.2.symm.trans h'.2)
  p2 := π.p2
  p3_notMem := π.p3_notMem
  p3_subset := π.p3_subset
  p4_disjoint := π.p4_disjoint
  p4_notMem := π.p4_notMem
  p5 := π.p5
  p6 := π.p6
  p7 := π.p7

/-- A linkage statement passes to a subgraph, which has fewer linkages. -/
theorem linkagePairs_mono {K₁ K₂ : SimpleGraph α} (h : K₂ ≤ K₁) {X Y : Set α} {k : ℕ} {x y : α}
    (hL : Portrayal.LinkagePairs K₁ X Y k x y) : Portrayal.LinkagePairs K₂ X Y k x y := by
  intro P hP
  let Q : Fin k → PathFromTo K₁ X Y := fun i =>
    ⟨(P i).first, (P i).last, (P i).walk.mapLe h, (SimpleGraph.Walk.isPath_mapLe h).2 (P i).isPath,
      (P i).first_mem, (P i).last_mem⟩
  have hQ : ∀ i, (Q i).walk.support = (P i).walk.support := fun i =>
    SimpleGraph.Walk.support_mapLe_eq_support h (P i).walk
  obtain ⟨i, h1, h2⟩ := hL Q (fun i j hij => by
    change Disjoint {z | z ∈ (Q i).walk.support} {z | z ∈ (Q j).walk.support}
    rw [hQ i, hQ j]
    exact hP hij)
  exact ⟨i, h1, h2⟩

/-- `π₁` has warp at most that of `π₂` at each cuff, over a homeomorphism of their surfaces. -/
@[expose] def Portrayal.WarpLE {α₁ α₂ b₁ b₂ : Type*} {G₁ : Hypergraph α₁ b₁} {G₂ : Hypergraph α₂
  b₂} (π₁ : Portrayal G₁) (π₂ : Portrayal G₂) : Prop :=
  ∃ ψ : π₁.S ≃ₜ π₂.S, ∀ Θ ∈ cuffs π₁.S, π₁.warpAt Θ ≤ π₂.warpAt (ψ '' Θ)

section WarpLE

variable {a₀ a₁ a₂ b₀ b₁ b₂ : Type*} {G₀ : Hypergraph a₀ b₀} {G₁ : Hypergraph a₁ b₁} {G₂ :
  Hypergraph a₂ b₂}
  {π₀ : Portrayal G₀} {π₁ : Portrayal G₁} {π₂ : Portrayal G₂}

theorem Portrayal.Resembles.warpLE (h : π₁.Resembles π₂) : π₁.WarpLE π₂ := by
  obtain ⟨ψ, hψ⟩ := h
  exact ⟨ψ, fun Θ hΘ => (hψ Θ hΘ).le⟩

theorem Portrayal.WarpLE.trans (h : π₀.WarpLE π₁) (h' : π₁.WarpLE π₂) : π₀.WarpLE π₂ := by
  obtain ⟨ψ, hψ⟩ := h
  obtain ⟨ψ', hψ'⟩ := h'
  refine ⟨ψ.trans ψ', fun Θ hΘ => ?_⟩
  have h1 := hψ Θ hΘ
  have h2 := hψ' (ψ '' Θ) (image_cuff_mem_cuffs ψ hΘ)
  have e : (ψ.trans ψ') '' Θ = ψ' '' (ψ '' Θ) := by
    change (ψ' ∘ ψ) '' Θ = _
    rw [image_comp]
  rw [e]
  exact h1.trans h2

theorem Portrayal.WarpLE.warp_le (h : π₁.WarpLE π₂) : π₁.warp ≤ π₂.warp := by
  classical
  obtain ⟨ψ, hψ⟩ := h
  unfold Portrayal.warp
  by_cases hne : (cuffs π₁.S).Nonempty
  · have hne₂ : (cuffs π₂.S).Nonempty := by
      obtain ⟨Θ, hΘ⟩ := hne
      exact ⟨ψ '' Θ, image_cuff_mem_cuffs ψ hΘ⟩
    rw [ite_eq_left hne, ite_eq_left hne₂]
    refine max_le_max le_rfl (csSup_le ?_ ?_)
    · obtain ⟨Θ, hΘ⟩ := hne
      exact ⟨_, Θ, hΘ, rfl⟩
    · rintro _ ⟨Θ, hΘ, rfl⟩
      have h3 := π₂.warpAt_le_warp (image_cuff_mem_cuffs ψ hΘ)
      unfold Portrayal.warp at h3
      rw [ite_eq_left hne₂] at h3
      refine (hψ Θ hΘ).trans ?_
      refine le_csSup ?_ ⟨_, image_cuff_mem_cuffs ψ hΘ, rfl⟩
      refine ⟨max 1 (sSup {p | ∃ Θ ∈ cuffs π₂.S, p = π₂.warpAt Θ}), ?_⟩
      rintro _ ⟨Θ', hΘ', rfl⟩
      have h4 := π₂.warpAt_le_warp hΘ'
      unfold Portrayal.warp at h4
      rw [ite_eq_left hne₂] at h4
      exact h4
  · rw [ite_eq_right hne]
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl

/-- "Simpler than" for surfaces does not see a homeomorphism on the left. -/
theorem isSimplerThan_congr_left {X X' Y : Type} [TopologicalSpace X] [TopologicalSpace X']
  [TopologicalSpace Y]
    (e : X ≃ₜ X') (h : IsSimplerThan X' Y) : IsSimplerThan X Y := by
  obtain ⟨a, b, c, a', b', c', ⟨f⟩, hY, h'⟩ := h
  exact ⟨a, b, c, a', b', c', ⟨e.trans f⟩, hY, h'⟩

/-- "Simpler than" for surfaces does not see a homeomorphism on the right. -/
theorem isSimplerThan_congr_right {X Y Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Y']
    (e : Y ≃ₜ Y') (h : IsSimplerThan X Y') : IsSimplerThan X Y := by
  obtain ⟨a, b, c, a', b', c', hX, ⟨f⟩, h'⟩ := h
  exact ⟨a, b, c, a', b', c', hX, ⟨e.trans f⟩, h'⟩

/-- A simpler portrayal stays simpler when the right side has warps no smaller. -/
theorem Portrayal.IsSimpler.trans_warpLE (h : π₀.IsSimpler π₁) (h' : π₁.WarpLE π₂) : π₀.IsSimpler
  π₂ := by
  have hw := h'.warp_le
  obtain ⟨ψ', hψ'⟩ := h'
  rcases h with ⟨hs, hle⟩ | ⟨ψ, hle, Θ, hΘ, hlt⟩
  · exact .inl ⟨isSimplerThan_congr_right ψ'.symm hs, hle.trans hw⟩
  · have e : ∀ Θ : Set π₀.S, (ψ.trans ψ') '' Θ = ψ' '' (ψ '' Θ) := fun Θ => by
      change (ψ' ∘ ψ) '' Θ = _
      rw [image_comp]
    refine .inr ⟨ψ.trans ψ', fun Θ hΘ => ?_, Θ, hΘ, ?_⟩
    · rw [e]
      exact (hle Θ hΘ).trans (hψ' _ (image_cuff_mem_cuffs ψ hΘ))
    · rw [e]
      exact hlt.trans_le (hψ' _ (image_cuff_mem_cuffs ψ hΘ))

/-- A portrayal with warps no larger than a simpler portrayal is simpler. -/
theorem Portrayal.WarpLE.trans_isSimpler (h : π₀.WarpLE π₁) (h' : π₁.IsSimpler π₂) : π₀.IsSimpler
  π₂ := by
  have hw := h.warp_le
  obtain ⟨ψ, hψ⟩ := h
  rcases h' with ⟨hs, hle⟩ | ⟨ψ', hle, Θ, hΘ, hlt⟩
  · exact .inl ⟨isSimplerThan_congr_left ψ hs, hw.trans hle⟩
  · have e : ∀ Θ : Set π₀.S, (ψ.trans ψ') '' Θ = ψ' '' (ψ '' Θ) := fun Θ => by
      change (ψ' ∘ ψ) '' Θ = _
      rw [image_comp]
    have hΘ' : ψ.symm '' Θ ∈ cuffs π₀.S := image_cuff_mem_cuffs ψ.symm hΘ
    refine .inr ⟨ψ.trans ψ', fun Φ hΦ => ?_, ψ.symm '' Θ, hΘ', ?_⟩
    · rw [e]
      exact (hψ Φ hΦ).trans (hle _ (image_cuff_mem_cuffs ψ hΦ))
    · have hi : ψ '' (ψ.symm '' Θ) = Θ := by ext x; simp
      rw [e, hi]
      have h1 := hψ _ hΘ'
      rw [hi] at h1
      exact h1.trans_lt hlt

/-- A portrayal simpler than one of warp `≤ p` has warp `≤ p`. -/
theorem Portrayal.IsSimpler.warp_le (h : π₁.IsSimpler π₂) : π₁.warp ≤ π₂.warp := by
  rcases h with ⟨-, h⟩ | ⟨ψ, hle, -⟩
  · exact h
  · exact Portrayal.WarpLE.warp_le ⟨ψ, hle⟩

end WarpLE

/-- The moved portrayal has warps no larger, since each cell has no new adjacent pair. -/
theorem Portrayal.reEdge_warpLE {H₁ : Hypergraph α β₁} (π : Portrayal H₁) (H₂ : Hypergraph α β₂)
    (hV : H₂.vertexSet = H₁.vertexSet) (f : β₂ → Set π.S)
    (hC : ∀ e ∈ H₂.edgeSet, f e ∈ π.Γ.C)
    (hf : ∀ e ∈ H₂.edgeSet, H₂.ends e ⊆ (π.cellGraph (f e)).vertexSet)
    (hadj : ∀ e ∈ H₂.edgeSet, ∀ x ∈ H₂.ends e, ∀ y ∈ H₂.ends e, x ≠ y → (π.cellGraph
      (f e)).skeleton.Adj x y) :
    (π.reEdge H₂ hV f hC hf).WarpLE π := by
  have : T2Space π.S := π.isSurface.2.1
  refine ⟨Homeomorph.refl π.S, fun Θ hΘ => ?_⟩
  have himg : (Homeomorph.refl π.S : π.S → π.S) '' Θ = Θ := image_id Θ
  refine le_of_le_of_eq ?_ (congrArg π.warpAt himg.symm)
  refine ((π.reEdge H₂ hV f hC hf).warpAt_le_iff (Θ := Θ)).mpr fun c hc hcΘ => ?_
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x
  have hbd : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
  refine le_trans (Nat.sInf_le ?_) (π.cellWarp_le_warpAt hc hcΘ)
  have hsk : (reEdgeCell π H₂ f hf c).skeleton ≤ (π.cellGraph c).skeleton := by
    rintro x y ⟨hne, e, hx, hy⟩
    have hadj' := hadj e (H₂.edge_mem_of_inc hx.1) x hx.1 y hy.1 hne
    rwa [hx.2] at hadj'
  intro n₁ hn₁ n₂ hn₂ hne
  obtain ⟨h1, h2, h3⟩ := π.cellWarp_spec hc hbd n₁ hn₁ n₂ hn₂ hne
  exact ⟨h1, h2, fun a b => linkagePairs_mono hsk (h3 a b)⟩

/-- Moving a portrayal: if the tangle `𝒯₂` holds every separation `(A, D)` of `H₂` of small order on
the vertices of a cell, then the moved portrayal is `𝒯₂`-central. -/
theorem Portrayal.exists_moved {H₁ : Hypergraph α β₁} (π : Portrayal H₁) {H₂ : Hypergraph α β₂}
    (hV : H₂.vertexSet = H₁.vertexSet) (hne : π.Γ.C.Nonempty) (hcov : EdgesCovered H₂ H₁)
    {𝒯₂ : Set (Hypergraph α β₂ × Hypergraph α β₂)} {θ₂ : ℕ}
    (hord : ∀ c ∈ π.Γ.C, ((π.cellGraph c).vertexSet ∩ π.otherVertices c).ncard < θ₂)
    (hdom : ∀ c ∈ π.Γ.C, ∀ A D : Hypergraph α β₂, H₂.IsSeparation A D → separationOrder A D < θ₂ →
      A.vertexSet = (π.cellGraph c).vertexSet → (A, D) ∈ 𝒯₂) :
    ∃ π₂ : Portrayal H₂, π₂.IsCentral 𝒯₂ ∧ π₂.WarpLE π := by
  obtain ⟨f, hf⟩ := π.exists_cellChoice hV hne hcov
  have hC : ∀ e ∈ H₂.edgeSet, f e ∈ π.Γ.C := fun e he => (hf e he).1
  have hf' : ∀ e ∈ H₂.edgeSet, H₂.ends e ⊆ (π.cellGraph (f e)).vertexSet := fun e he =>
    (hf e he).2.1
  refine ⟨π.reEdge H₂ hV f hC hf', fun c hc => ?_, π.reEdge_warpLE H₂ hV f hC hf' fun e he =>
    (hf e he).2.2⟩
  let π₂ := π.reEdge H₂ hV f hC hf'
  have hle : π₂.cellGraph c ≤ H₂ := π₂.cellGraph_le c hc
  refine ⟨complSubhypergraph H₂ (π₂.cellGraph c), hdom c hc _ _ (isSeparation_complSubhypergraph
    hle) ?_ rfl⟩
  rw [separationOrder_complSubhypergraph]
  have hsub : attachments H₂ (π₂.cellGraph c) ⊆ (π.cellGraph c).vertexSet ∩ π.otherVertices c :=
    π₂.attachments_cellGraph_subset_otherVertices hc
  exact (ncard_le_ncard hsub ((π.cellGraph c).vertexSet_finite.inter_of_left _)).trans_lt
    (hord c hc)

/-- The edges of `H*` lie inside edges of `H`. -/
theorem edgesCovered_oneSkeleton {b : Type*} (H : Hypergraph α b) : EdgesCovered
  (oneSkeletonHypergraph H) H := by
  intro s hs
  induction s using Sym2.ind with
  | _ x y =>
    obtain ⟨hne, e, hx, hy⟩ := (SimpleGraph.mem_edgeSet _).1 hs
    refine .inl ⟨e, H.edge_mem_of_inc hx, ?_⟩
    rintro v ⟨-, hv⟩
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact hx
    · exact hy

/-- `H₂ / Z` keeps being covered by `H₁ / Z`. -/
theorem EdgesCovered.quotient {H₁ : Hypergraph α β₁} {H₂ : Hypergraph α β₂}
  (h : EdgesCovered H₂ H₁) (Z : Set α) :
    EdgesCovered (quotientVertices H₂ Z) (quotientVertices H₁ Z) := by
  intro e he
  rcases h e he with ⟨e₁, he₁, hs⟩ | hs
  · exact .inl ⟨e₁, he₁, fun x hx => ⟨hs hx.1, hx.2⟩⟩
  · exact .inr fun x hx y hy => hs hx.1 hy.1

/-- Redundancy passes from `π₂` to any `π₁` with warps no larger, when each quotient of `𝒯₁` lies
below a quotient of `𝒯₂`. Given a portrayal simpler than `π₁`, move it to `H₂ / Z`; it is simpler
than `π₂`. The bound on `θ₂` keeps the cells of the moved portrayal below the order of `𝒯₂ / Z`. -/
theorem Portrayal.IsRedundant.of_moved {H₁ : Hypergraph α β₁} {H₂ : Hypergraph α β₂}
    {𝒯₁ : Set (Hypergraph α β₁ × Hypergraph α β₁)} {𝒯₂ : Set (Hypergraph α β₂ × Hypergraph α β₂)}
    {θ₁ θ₂ z p : ℕ} (h𝒯₁ : IsTangle H₁ θ₁ 𝒯₁) (h𝒯₂ : IsTangle H₂ θ₂ 𝒯₂) (hθ₁ : z + max 3
      (2 * p + 2) < θ₁)
    (hV : H₂.vertexSet = H₁.vertexSet) (hcov : EdgesCovered H₂ H₁)
    (hθ₂ : z + max 3 (2 * p + 2) < θ₂)
    {π₁ : Portrayal H₁} {π₂ : Portrayal H₂} (hred : π₂.IsRedundant 𝒯₂ θ₂ z) (hwarp : π₂.warp ≤ p)
      (hle : π₁.WarpLE π₂)
    (hdom : ∀ Z ⊆ H₁.vertexSet, Z.ncard ≤ z → ∀ A B, (A, B) ∈ quotientTangle H₁ 𝒯₁ Z →
      separationOrder A B ≤ max 3 (2 * p + 2) →
      ∃ A' B', (A', B') ∈ quotientTangle H₂ 𝒯₂ Z ∧ A.vertexSet ⊆ A'.vertexSet) :
    π₁.IsRedundant 𝒯₁ θ₁ z := by
  refine ⟨by omega, fun Z hZ hcard π' hcen hsimp => ?_⟩
  have hZ₂ : Z ⊆ H₂.vertexSet := hV ▸ hZ
  have hZlt₁ : Z.ncard < θ₁ := by omega
  have hZlt₂ : Z.ncard < θ₂ := by omega
  have ht₁ := theorem_4_2_proof h𝒯₁ hZ hZlt₁
  have ht₂ := theorem_4_2_proof h𝒯₂ hZ₂ hZlt₂
  have hs₂ : π'.IsSimpler π₂ := hsimp.trans_warpLE hle
  have hw' : π'.warp ≤ p := hs₂.warp_le.trans hwarp
  obtain ⟨π'', hc'', hl''⟩ := π'.exists_moved (H₂ := quotientVertices H₂ Z)
    (by change H₂.vertexSet \ Z = H₁.vertexSet \ Z; rw [hV])
    (π'.cells_nonempty ht₁) (hcov.quotient Z) (θ₂ := θ₂ - Z.ncard) (𝒯₂ := quotientTangle H₂ 𝒯₂ Z)
    (fun c hc => by have := π'.ncard_cell_inter_other_le hw' hc; omega)
    (fun c hc A D hs ho hVA => by
      obtain ⟨B, hB⟩ := hcen c hc
      have hle := (π'.cellGraph_le c hc)
      have hsmall : ((π'.cellGraph c).vertexSet ∩ π'.otherVertices c).ncard ≤ max 3 (2 * p + 2)
        := π'.ncard_cell_inter_other_le hw' hc
      have ho₀ : separationOrder (π'.cellGraph c) (complSubhypergraph (quotientVertices H₁ Z)
        (π'.cellGraph c)) ≤ max 3 (2 * p + 2) := by
        rw [separationOrder_complSubhypergraph]
        exact (ncard_le_ncard (π'.attachments_cellGraph_subset_otherVertices hc)
          ((π'.cellGraph c).vertexSet_finite.inter_of_left _)).trans hsmall
      have hB' := GM10.theorem_2_9_proof ht₁ hB (isSeparation_complSubhypergraph hle) (by omega)
        (.inr (.inl subset_rfl))
      obtain ⟨A', B', hm, hsub⟩ := hdom Z hZ hcard _ _ hB' ho₀
      exact GM10.theorem_2_9_proof ht₂ hm hs ho (.inr (.inl (hVA ▸ hsub))))
  exact hred.2 Z hZ₂ hcard π'' hc'' (hl''.trans_isSimpler hs₂)

end GraphMinor.GM17
