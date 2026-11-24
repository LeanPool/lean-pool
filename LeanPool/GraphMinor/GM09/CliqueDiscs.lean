/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Park
public import LeanPool.GraphMinor.GM09.DiscPlacement
public import LeanPool.GraphMinor.GM09.Section11c

/-!
# The discs of the small cliques

The proof of (11.11) of Graph Minors IX chooses a closed disc for each clique of at most three
vertices of a rural neighborhood, so that two discs meet only at common vertices. The paper states
this in one sentence. Here is the argument.

We only need discs for a family of cliques in which no clique contains another. A triangle in the
family bounds a region of the drawing with nothing inside, and we put a smaller disc in that region
that touches the boundary only at the three vertices. Then we thicken the edges in the family to
thin discs, one after another. A vertex forming a clique by itself lies in no other clique of the
family, so a small disc next to it meets none of the others.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u

variable {α : Type u} {N : Neighborhood α (Sym2 α)}

/-- The facts about a presentation that the choice of discs uses: the drawing meets the boundary of
`Δ` and the disc `Δ₀` only in the vertices it should, and the graph is simple. -/
structure IsTidyPresentation (P : Presentation N) : Prop where
  bd_U : ∀ x ∈ P.Γ.drawing.U, x ∈ subBd P.Δ → ∃ v ∈ N.Ω.bar, x = vertexPt P.Γ v
  Δ₀_U : ∀ x ∈ P.Γ.drawing.U, x ∈ P.Δ₀ → ∃ v ∈ N.Ω₀.bar, x = vertexPt P.Γ v
  Δ₀_bd : P.Δ₀ ∩ subBd P.Δ ⊆ P.Γ.drawing.U
  simple : IsSimpleGraph N.G

/-- A closed disc whose boundary is in the drawing and whose interior misses the drawing and `Δ₀`,
with exactly the vertices of `K` on its boundary. -/
structure IsEmptyRegion (P : Presentation N) (K : Set α) (E : Set EuclideanPlane) : Prop where
  disc : IsClosedDisc E
  sub : E ⊆ P.Δ
  bd_U : discBd E ⊆ P.Γ.drawing.U
  bd_iff : ∀ v ∈ V(N.G), vertexPt P.Γ v ∈ discBd E ↔ v ∈ K
  int_U : Disjoint (interior E) P.Γ.drawing.U
  int_Δ₀ : Disjoint (interior E) P.Δ₀

/-- The family of cliques for which we want discs. -/
structure IsCliqueFamily (P : Presentation N) (F : Set (Set α)) : Prop where
  finite : F.Finite
  clique : ∀ K ∈ F, IsLeThreeClique N.G K
  nonempty : ∀ K ∈ F, K.Nonempty
  antichain : ∀ K ∈ F, ∀ K' ∈ F, K ⊆ K' → K = K'
  off₀ : ∀ v, {v} ∈ F → v ∉ N.Ω₀.bar
  region : ∀ K ∈ F, K.ncard = 3 → ∃ E, IsEmptyRegion P K E

/-- A closed disc for the clique `K`: it has the vertices of `K` on its boundary, and it meets `Δ₀`
and the boundary of `Δ` only in vertices of `K`. -/
structure IsCliqueDisc (P : Presentation N) (K : Set α) (B : Set EuclideanPlane) : Prop where
  disc : IsClosedDisc B
  sub : B ⊆ P.Δ
  bd : ∀ v ∈ K, vertexPt P.Γ v ∈ discBd B
  inter₀ : B ∩ P.Δ₀ ⊆ vertexPt P.Γ '' (N.Ω₀.bar ∩ K)
  inter_bd : B ∩ subBd P.Δ ⊆ vertexPt P.Γ '' (K ∩ N.Ω.bar)

theorem isClosed_Δ₀ (P : Presentation N) : IsClosed P.Δ₀ := by
  rcases P.agrees_Δ₀ with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
    exact isClosed_empty
  · exact h.isCompact.isClosed

namespace IsTidyPresentation

variable {P : Presentation N}

/-- A presentation of a simple rural neighborhood chosen by `Neighborhood.IsRural.exists_clean` is
tidy. -/
theorem of_clean (hs : IsSimpleGraph N.G)
    (h₁ : P.Γ.drawing.U ∩ subBd P.Δ = ⋃ v ∈ N.Ω.bar, graphDrawingVertexSet P.Γ v)
    (h₂ : P.Δ₀ ∩ subBd P.Δ ⊆ ⋃ v ∈ N.Ω.bar, graphDrawingVertexSet P.Γ v)
    (h₃ : P.Γ.drawing.U ∩ subBd P.Δ₀ ⊆ ⋃ v ∈ N.Ω₀.bar, graphDrawingVertexSet P.Γ v) :
    IsTidyPresentation P := by
  have hbar : ∀ {x : EuclideanPlane} {Ω : CyclicPerm α}, Ω.bar ⊆ V(N.G) →
      x ∈ (⋃ v ∈ Ω.bar, graphDrawingVertexSet P.Γ v) → ∃ v ∈ Ω.bar, x = vertexPt P.Γ v := by
    intro x Ω hs hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    exact ⟨v, hv, (mem_vertexSet_iff P.Γ (hs hv)).mp hxv⟩
  refine ⟨fun x hx hb => hbar N.bar_subset (h₁ ▸ ⟨hx, hb⟩), fun x hx h₀ => ?_, ?_, hs⟩
  · refine hbar N.bar₀_subset (h₃ ⟨hx, ?_⟩)
    rcases P.agrees_Δ₀ with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h] at h₀
      exact h₀.elim
    · have hni : x ∉ interior P.Δ₀ := (P.U_subset hx).2
      rw [interior_eq_discInt_plane h] at hni
      rw [subBd_eq_discBd_plane h]
      by_contra hb
      exact hni ⟨h₀, hb⟩
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hbar N.bar_subset (h₂ hx)
    exact vertexPt_mem_U P.Γ (N.bar_subset hv)

theorem mem_U {v : α} (hv : v ∈ V(N.G)) : vertexPt P.Γ v ∈ P.Γ.drawing.U :=
  P.Γ.drawing.V_subset_U (vertexPt_mem_V P.Γ hv)

/-- A vertex of `K` drawn in `Δ₀` is in `ΩBar₀`. -/
theorem pt_Δ₀ (T : IsTidyPresentation P) {K : Set α} (hK : K ⊆ V(N.G)) {x : EuclideanPlane}
    (hx : x ∈ vertexPt P.Γ '' K) (h : x ∈ P.Δ₀) : x ∈ vertexPt P.Γ '' (N.Ω₀.bar ∩ K) := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, he⟩ := T.Δ₀_U _ (mem_U (hK hv)) h
  have := vertexPt_injOn P.Γ (hK hv) (N.bar₀_subset hw) he
  subst this
  exact ⟨v, ⟨hw, hv⟩, rfl⟩

/-- A vertex of `K` drawn in the boundary of `Δ` is in `ΩBar`. -/
theorem pt_bd (T : IsTidyPresentation P) {K : Set α} (hK : K ⊆ V(N.G)) {x : EuclideanPlane}
    (hx : x ∈ vertexPt P.Γ '' K) (h : x ∈ subBd P.Δ) : x ∈ vertexPt P.Γ '' (K ∩ N.Ω.bar) := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, he⟩ := T.bd_U _ (mem_U (hK hv)) h
  have := vertexPt_injOn P.Γ (hK hv) (N.bar_subset hw) he
  subst this
  exact ⟨v, ⟨hv, hw⟩, rfl⟩

/-- A point drawn for a vertex of both `K` and `K'` is drawn for a common vertex. -/
theorem pt_inter {K K' : Set α} (hK : K ⊆ V(N.G)) (hK' : K' ⊆ V(N.G)) {x : EuclideanPlane}
    (hx : x ∈ vertexPt P.Γ '' K) (hx' : x ∈ vertexPt P.Γ '' K') :
    x ∈ vertexPt P.Γ '' (K ∩ K') := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, he⟩ := hx'
  have := vertexPt_injOn P.Γ (hK' hw) (hK hv) he
  subst this
  exact ⟨w, ⟨hv, hw⟩, rfl⟩

end IsTidyPresentation

namespace IsEmptyRegion

variable {P : Presentation N} {K K' : Set α} {E E' : Set EuclideanPlane}

theorem isPreconnected_interior (R : IsEmptyRegion P K E) : IsPreconnected (interior E) := by
  rw [interior_eq_discInt_plane R.disc]
  exact R.disc.isPreconnected_discInt

/-- A point of the region off its interior is on its boundary. -/
theorem mem_bd (R : IsEmptyRegion P K E) {x : EuclideanPlane} (hx : x ∈ E)
    (hi : x ∉ interior E) : x ∈ discBd E := by
  rw [interior_eq_discInt_plane R.disc] at hi
  by_contra hb
  exact hi ⟨hx, hb⟩

/-- Two regions of different cliques have disjoint interiors. -/
theorem interior_disjoint (R : IsEmptyRegion P K E) (R' : IsEmptyRegion P K' E')
    (hK : K ⊆ V(N.G)) (hK' : K' ⊆ V(N.G)) (hne : K ≠ K')
    (hbd : ∀ v ∈ K, vertexPt P.Γ v ∈ discBd E) (hbd' : ∀ v ∈ K', vertexPt P.Γ v ∈ discBd E') :
    Disjoint (interior E) (interior E') := by
  by_contra hmeet
  obtain ⟨x, hx, hx'⟩ := not_disjoint_iff.mp hmeet
  have h₁ : interior E ⊆ interior E' := by
    rcases subset_interior_or_compl R'.disc R.isPreconnected_interior
      (disjoint_of_subset_right R'.bd_U R.int_U) with h | h
    · exact h
    · exact (h hx (interior_subset hx')).elim
  have h₂ : interior E' ⊆ interior E := by
    rcases subset_interior_or_compl R.disc R'.isPreconnected_interior
      (disjoint_of_subset_right R.bd_U R'.int_U) with h | h
    · exact h
    · exact (h hx' (interior_subset hx)).elim
  have hEE : E = E' := by
    rw [← closure_interior_of_isClosedDisc R.disc, ← closure_interior_of_isClosedDisc R'.disc,
      Subset.antisymm h₁ h₂]
  subst hEE
  exact hne (Subset.antisymm (fun v hv => (R'.bd_iff v (hK hv)).mp (hbd v hv))
    (fun v hv => (R.bd_iff v (hK' hv)).mp (hbd' v hv)))

/-- A smaller disc in an empty region, which touches the boundary of the region only in the vertices
of the clique. Any point of the smaller disc off the interior of the region is one of them. -/
theorem exists_inscribed (R : IsEmptyRegion P K E) (hfin : K.Finite)
    (hbd : ∀ v ∈ K, vertexPt P.Γ v ∈ discBd E) :
    ∃ B ⊆ E, IsClosedDisc B ∧ (∀ v ∈ K, vertexPt P.Γ v ∈ discBd B) ∧
      ∀ x ∈ B, x ∉ interior E → x ∈ vertexPt P.Γ '' K := by
  obtain ⟨B, hB, hd, hb, ht⟩ := exists_inscribed_disc R.disc (hfin.image (vertexPt P.Γ))
    (by rintro _ ⟨v, hv, rfl⟩; exact hbd v hv)
  refine ⟨B, hB, hd, fun v hv => hb (mem_image_of_mem _ hv), fun x hx hi => ?_⟩
  rw [← ht]
  exact ⟨hx, R.mem_bd (hB hx) hi⟩

end IsEmptyRegion

variable {P : Presentation N}

/-- Discs for the triangles of the family. -/
theorem exists_triangle_discs (T : IsTidyPresentation P) {F : Set (Set α)}
    (C : IsCliqueFamily P F) :
    ∃ β : Set α → Set EuclideanPlane,
      (∀ K ∈ F, K.ncard = 3 → IsCliqueDisc P K (β K) ∧
        β K ∩ P.Γ.drawing.U ⊆ vertexPt P.Γ '' K) ∧
      ∀ K ∈ F, ∀ K' ∈ F, K.ncard = 3 → K'.ncard = 3 → K ≠ K' →
        β K ∩ β K' ⊆ vertexPt P.Γ '' (K ∩ K') := by
  classical
  have hKV : ∀ K ∈ F, K ⊆ V(N.G) := fun K hK => (C.clique K hK).1
  have hfin : ∀ K ∈ F, K.Finite := fun K hK => N.finite_V.subset (hKV K hK)
  choose! E hE using C.region
  have hbdE : ∀ K ∈ F, K.ncard = 3 → ∀ v ∈ K, vertexPt P.Γ v ∈ discBd (E K) :=
    fun K hK h3 v hv => ((hE K hK h3).bd_iff v (hKV K hK hv)).mpr hv
  choose! β hβ using fun K (hK : K ∈ F) (h3 : K.ncard = 3) =>
    (hE K hK h3).exists_inscribed (hfin K hK) (hbdE K hK h3)
  refine ⟨β, fun K hK h3 => ?_, fun K hK K' hK' h3 h3' hne x hx => ?_⟩
  · obtain ⟨hs, hd, hb, hp⟩ := hβ K hK h3
    have R := hE K hK h3
    refine ⟨⟨hd, hs.trans R.sub, hb, ?_, ?_⟩, ?_⟩
    · rintro x ⟨hx, h₀⟩
      exact T.pt_Δ₀ (hKV K hK) (hp x hx (disjoint_right.mp R.int_Δ₀ h₀)) h₀
    · rintro x ⟨hx, hbd⟩
      refine T.pt_bd (hKV K hK) (hp x hx fun hi => ?_) hbd
      exact disjoint_left.mp (disjoint_interior_subBd P.Δ) (interior_mono R.sub hi) hbd
    · rintro x ⟨hx, hU⟩
      exact hp x hx (disjoint_right.mp R.int_U hU)
  · have R := hE K hK h3
    have R' := hE K' hK' h3'
    obtain ⟨hs, -, -, hp⟩ := hβ K hK h3
    obtain ⟨hs', -, -, hp'⟩ := hβ K' hK' h3'
    have hdis := R.interior_disjoint R' (hKV K hK) (hKV K' hK') hne (hbdE K hK h3) (hbdE K' hK' h3')
    have hoff : ∀ {A A' : Set EuclideanPlane}, Disjoint (interior A) (interior A') →
        IsClosedDisc A' → ∀ {y : EuclideanPlane}, y ∈ A' → y ∉ interior A := by
      intro A A' hd hA y hy hi
      have hcl : y ∈ closure (interior A') := by
        rw [closure_interior_of_isClosedDisc hA]
        exact hy
      obtain ⟨z, hzo, hz⟩ := mem_closure_iff.mp hcl _ isOpen_interior hi
      exact disjoint_left.mp hd hzo hz
    exact IsTidyPresentation.pt_inter (hKV K hK) (hKV K' hK')
      (hp x hx.1 (hoff hdis R'.disc (hs' hx.2))) (hp' x hx.2 (hoff hdis.symm R.disc (hs hx.1)))

/-- Discs for the edges of the family, one after another. They meet the closed set `Y`, which meets
the drawing only in vertices, only in the ends of the edge. -/
theorem exists_edge_discs (T : IsTidyPresentation P) (I : Finset (Set α))
    (hI : ∀ K ∈ I, IsLeThreeClique N.G K ∧ K.ncard = 2) {Y : Set EuclideanPlane} (hY : IsClosed Y)
    (hYU : ∀ x ∈ Y, x ∈ P.Γ.drawing.U → x ∈ P.Γ.drawing.V) :
    ∃ D : Set α → Set EuclideanPlane,
      (∀ K ∈ I, IsCliqueDisc P K (D K) ∧ D K ∩ P.Γ.drawing.V ⊆ vertexPt P.Γ '' K ∧
        D K ∩ Y ⊆ vertexPt P.Γ '' K) ∧
      ∀ K ∈ I, ∀ K' ∈ I, K ≠ K' → D K ∩ D K' ⊆ vertexPt P.Γ '' (K ∩ K') := by
  classical
  have hpair : ∀ K ∈ I, ∃ a b, a ≠ b ∧ K = {a, b} := fun K hK => Set.ncard_eq_two.mp (hI K hK).2
  rcases isEmpty_or_nonempty α with hα | hα
  · refine ⟨fun _ => ∅, fun K hk => ?_, fun K hk => ?_⟩ <;>
    · obtain ⟨a, -⟩ := hpair K hk
      exact hα.elim a
  choose! a b hab hK using hpair
  have hmemK : ∀ K ∈ I, a K ∈ K ∧ b K ∈ K := fun K hk => by
    have h₁ : a K ∈ ({a K, b K} : Set α) := Or.inl rfl
    have h₂ : b K ∈ ({a K, b K} : Set α) := Or.inr rfl
    rw [← hK K hk] at h₁ h₂
    exact ⟨h₁, h₂⟩
  have hKV : ∀ K ∈ I, K ⊆ V(N.G) := fun K hk => (hI K hk).1.1
  have hlink : ∀ K ∈ I, N.G.IsLink s(a K, b K) (a K) (b K) := fun K hk =>
    (hI K hk).1.2.2 _ (hmemK K hk).1 _ (hmemK K hk).2 (hab K hk)
  let e : Set α → Sym2 α := fun K => s(a K, b K)
  let pa : Set α → EuclideanPlane := fun K => vertexPt P.Γ (a K)
  let pb : Set α → EuclideanPlane := fun K => vertexPt P.Γ (b K)
  let l : Set α → Set EuclideanPlane := fun K => closure (graphDrawingEdgeSet P.Γ (e K))
  let R : Set α → Set EuclideanPlane := fun K =>
    P.Δ₀ ∪ subBd P.Δ ∪ Y ∪ P.Γ.drawing.V ∪
      ⋃ f ∈ E(N.G) \ {e K}, closure (graphDrawingEdgeSet P.Γ f)
  have hline : ∀ K ∈ I, IsLineWithEnds (l K) (pa K) (pb K) := fun K hk =>
    isLine_closure_of_isLink P.Γ (hlink K hk) (hab K hk)
  have hpab : ∀ K ∈ I, pa K ≠ pb K := fun K hk h =>
    hab K hk (vertexPt_injOn P.Γ (hlink K hk).left_mem (hlink K hk).right_mem h)
  have hRc : ∀ K ∈ I, IsClosed (R K) := fun K _ => by
    refine ((((isClosed_Δ₀ P).union (isClosed_subBd P.Δ)).union hY).union
      P.Γ.drawing.finite_V.isClosed).union ?_
    exact (N.finite_E.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure
  have hopen : ∀ K ∈ I, ∀ x ∈ l K, x ∉ ({pa K, pb K} : Set EuclideanPlane) →
      x ∈ graphDrawingEdgeSet P.Γ (e K) ∧ x ∉ P.Γ.drawing.V := by
    intro K hk x hx hn
    obtain ⟨hmem, hcap⟩ := closure_inter_V_of_isLink P.Γ (hlink K hk)
    have hxV : x ∉ P.Γ.drawing.V := fun hV => by
      have hm : x ∈ l K ∩ P.Γ.drawing.V := ⟨hx, hV⟩
      rw [show l K = closure (graphDrawingEdgeSet P.Γ s(a K, b K)) from rfl, hcap] at hm
      exact hn hm
    refine ⟨?_, hxV⟩
    rw [← P.Γ.drawing.closure_diff_V hmem]
    exact ⟨hx, hxV⟩
  have hUe : ∀ K ∈ I, ∀ x ∈ graphDrawingEdgeSet P.Γ (e K), x ∈ P.Γ.drawing.U := fun K hk x hx =>
    ((graphDrawingEdgeSet_mem P.Γ (hlink K hk).edge_mem).2.1 hx).1
  have hmeet : ∀ K ∈ I, l K ∩ R K ⊆ {pa K, pb K} := by
    rintro K hk x ⟨hx, hxR⟩
    by_contra hn
    obtain ⟨hxe, hxV⟩ := hopen K hk x hx hn
    have hxU := hUe K hk x hxe
    rcases hxR with (((h | h) | h) | h) | h
    · obtain ⟨v, hv, rfl⟩ := T.Δ₀_U x hxU h
      exact hxV (vertexPt_mem_V P.Γ (N.bar₀_subset hv))
    · obtain ⟨v, hv, rfl⟩ := T.bd_U x hxU h
      exact hxV (vertexPt_mem_V P.Γ (N.bar_subset hv))
    · exact hxV (hYU x h hxU)
    · exact hxV h
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp h
      have hmem := graphDrawingEdgeSet_mem P.Γ hf.1
      have hxf' : x ∈ graphDrawingEdgeSet P.Γ f := by
        rw [← P.Γ.drawing.closure_diff_V hmem]
        exact ⟨hxf, hxV⟩
      exact hf.2 (eq_of_mem_edgeSet P.Γ hf.1 (hlink K hk).edge_mem hxf' hxe)
  have hene : ∀ K ∈ I, ∀ K' ∈ I, K ≠ K' → e K ≠ e K' := by
    intro K hk K' hk' hne he
    apply hne
    rw [hK K hk, hK K' hk']
    rcases Sym2.eq_iff.mp he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]
    · rw [h₁, h₂, pair_comm]
  have hcross : ∀ K ∈ I, ∀ K' ∈ I, K ≠ K' → l K ⊆ R K' := by
    intro K hk K' hk' hne x hx
    exact Or.inr (mem_iUnion₂.mpr ⟨e K, ⟨(hlink K hk).edge_mem, hene K hk K' hk' hne⟩, hx⟩)
  obtain ⟨D, hD, hp⟩ := exists_lenses I hline hpab hRc hmeet hcross
  have hends : ∀ K ∈ I, ({pa K, pb K} : Set EuclideanPlane) ⊆ vertexPt P.Γ '' K := by
    rintro K hk _ (rfl | rfl)
    · exact mem_image_of_mem _ (hmemK K hk).1
    · exact mem_image_of_mem _ (hmemK K hk).2
  have hRsub : ∀ K ∈ I, ∀ S, S ⊆ R K → D K ∩ S ⊆ vertexPt P.Γ '' K := fun K hk S hS x hx =>
    hends K hk ((hD K hk).2.2.1 ⟨hx.1, hS hx.2⟩)
  refine ⟨D, fun K hk => ?_, fun K hk K' hk' hne x hx => ?_⟩
  · obtain ⟨hdisc, hsub, -, hpa, hpb, hpc⟩ := hD K hk
    have hin : D K ⊆ P.Δ := by
      intro x hx
      by_cases hxe : x ∈ ({pa K, pb K} : Set EuclideanPlane)
      · rcases hxe with rfl | rfl
        · exact (P.U_subset (IsTidyPresentation.mem_U (hlink K hk).left_mem)).1
        · exact (P.U_subset (IsTidyPresentation.mem_U (hlink K hk).right_mem)).1
      · have hdj : Disjoint (D K \ {pa K, pb K}) (discBd P.Δ) := by
          rw [disjoint_left]
          rintro y ⟨hy, hyn⟩ hyb
          refine hyn ((hD K hk).2.2.1 ⟨hy, Or.inl (Or.inl (Or.inl (Or.inr ?_)))⟩)
          rw [subBd_eq_discBd_plane P.isClosedDisc_Δ]
          exact hyb
        rcases subset_interior_or_compl P.isClosedDisc_Δ hpc hdj with h | h
        · exact interior_subset (h ⟨hx, hxe⟩)
        · exfalso
          obtain ⟨y, hyl, hyn⟩ := (hline K hk).nonempty_sdiff
          have hye := (hopen K hk y hyl hyn).1
          exact h ⟨hsub hyl, hyn⟩ (P.U_subset (hUe K hk y hye)).1
    refine ⟨⟨hdisc, hin, fun v hv => ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hK K hk] at hv
      rcases hv with rfl | rfl
      · exact hpa
      · exact hpb
    · rintro x ⟨hx, h₀⟩
      exact T.pt_Δ₀ (hKV K hk)
        (hRsub K hk _ (fun y hy => Or.inl (Or.inl (Or.inl (Or.inl hy)))) ⟨hx, h₀⟩) h₀
    · rintro x ⟨hx, hb⟩
      exact T.pt_bd (hKV K hk)
        (hRsub K hk _ (fun y hy => Or.inl (Or.inl (Or.inl (Or.inr hy)))) ⟨hx, hb⟩) hb
    · exact hRsub K hk _ fun y hy => Or.inl (Or.inr hy)
    · exact hRsub K hk _ fun y hy => Or.inl (Or.inl (Or.inr hy))
  · have h := hp K hk K' hk' hne hx
    exact IsTidyPresentation.pt_inter (hKV K hk) (hKV K' hk') (hends K hk h.1) (hends K' hk' h.2)

/-- Discs for the vertices that form a clique by themselves. Each one is close to its vertex, so it
misses a closed set that misses the vertex. -/
theorem exists_vertex_discs (T : IsTidyPresentation P) {A : Set α} (hfin : A.Finite)
    (hAV : A ⊆ V(N.G)) (hA₀ : ∀ v ∈ A, v ∉ N.Ω₀.bar) {Z : Set EuclideanPlane} (hZ : IsClosed Z)
    (hAZ : ∀ v ∈ A, vertexPt P.Γ v ∉ Z) :
    ∃ s : α → Set EuclideanPlane, (∀ v ∈ A, IsCliqueDisc P {v} (s v) ∧ Disjoint (s v) Z) ∧
      ∀ v ∈ A, ∀ w ∈ A, v ≠ w → Disjoint (s v) (s w) := by
  classical
  obtain ⟨O, hO, hd⟩ := (hfin.image (vertexPt P.Γ)).t2_separation
  have hoff : ∀ v ∈ A, vertexPt P.Γ v ∉ P.Δ₀ := by
    intro v hv h
    obtain ⟨w, hw, he⟩ := T.Δ₀_U _ (IsTidyPresentation.mem_U (hAV hv)) h
    have := vertexPt_injOn P.Γ (hAV hv) (N.bar₀_subset hw) he
    exact hA₀ v hv (this ▸ hw)
  have hclosed : IsClosed (Z ∪ P.Δ₀) := hZ.union (isClosed_Δ₀ P)
  have hex : ∀ v ∈ A, ∃ K ⊆ P.Δ, K ⊆ O (vertexPt P.Γ v) ∩ (Z ∪ P.Δ₀)ᶜ ∧ IsClosedDisc K ∧
      vertexPt P.Γ v ∈ discBd K ∧ K ∩ discBd P.Δ ⊆ {vertexPt P.Γ v} := fun v hv =>
    exists_small_disc_at P.isClosedDisc_Δ (P.U_subset (IsTidyPresentation.mem_U (hAV hv))).1
      ((hO _).2.inter hclosed.isOpen_compl)
      ⟨(hO _).1, by rintro (h | h); exacts [hAZ v hv h, hoff v hv h]⟩
  rcases isEmpty_or_nonempty α with hα | hα
  · refine ⟨fun _ => ∅, fun v => ?_, fun v => ?_⟩ <;> exact hα.elim v
  choose! s hsub hW hdisc hb htouch using hex
  refine ⟨s, fun v hv => ⟨⟨hdisc v hv, hsub v hv, ?_, ?_, ?_⟩, ?_⟩, fun v hv w hw hne => ?_⟩
  · intro w hw
    rw [mem_singleton_iff.mp hw]
    exact hb v hv
  · rintro x ⟨hx, h₀⟩
    exact ((hW v hv hx).2 (Or.inr h₀)).elim
  · rintro x ⟨hx, hbd⟩
    have hx' : x ∈ ({vertexPt P.Γ v} : Set _) :=
      htouch v hv ⟨hx, by rwa [subBd_eq_discBd_plane P.isClosedDisc_Δ] at hbd⟩
    rw [mem_singleton_iff] at hx'
    subst hx'
    exact T.pt_bd (K := {v}) (singleton_subset_iff.mpr (hAV hv)) (mem_image_of_mem _ rfl) hbd
  · rw [disjoint_left]
    exact fun x hx h => (hW v hv hx).2 (Or.inl h)
  · have hne' : vertexPt P.Γ v ≠ vertexPt P.Γ w := fun h =>
      hne (vertexPt_injOn P.Γ (hAV hv) (hAV hw) h)
    have := hd (mem_image_of_mem _ hv) (mem_image_of_mem _ hw) hne'
    exact this.mono (fun x hx => (hW v hv hx).1) (fun x hx => (hW w hw hx).1)

/-- The discs of the family, as in the proof of (11.11) of Graph Minors IX, page 76. -/
theorem exists_clique_discs (T : IsTidyPresentation P) {F : Set (Set α)}
    (C : IsCliqueFamily P F) :
    ∃ β : Set α → Set EuclideanPlane, (∀ K ∈ F, IsCliqueDisc P K (β K)) ∧
      ∀ K ∈ F, ∀ K' ∈ F, K ≠ K' → β K ∩ β K' ⊆ vertexPt P.Γ '' (K ∩ K') := by
  classical
  have hKV : ∀ K ∈ F, K ⊆ V(N.G) := fun K hK => (C.clique K hK).1
  have hfin : ∀ K ∈ F, K.Finite := fun K hK => N.finite_V.subset (hKV K hK)
  obtain ⟨β₃, h₃, hp₃⟩ := exists_triangle_discs T C
  let Y : Set EuclideanPlane := ⋃ K ∈ {K ∈ F | K.ncard = 3}, β₃ K
  have hYc : IsClosed Y := (C.finite.subset (sep_subset _ _)).isClosed_biUnion
    fun K hK => (h₃ K hK.1 hK.2).1.disc.isCompact.isClosed
  have hYU : ∀ x ∈ Y, x ∈ P.Γ.drawing.U → x ∈ P.Γ.drawing.V := by
    intro x hx hU
    obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hx
    obtain ⟨v, hv, rfl⟩ := (h₃ K hK.1 hK.2).2 ⟨hxK, hU⟩
    exact vertexPt_mem_V P.Γ (hKV K hK.1 hv)
  let I : Finset (Set α) := C.finite.toFinset.filter (fun K => K.ncard = 2)
  have hI : ∀ {K}, K ∈ I ↔ K ∈ F ∧ K.ncard = 2 := by
    intro K
    simp [I]
  obtain ⟨D, h₂, hp₂⟩ := exists_edge_discs T I (fun K hK => ⟨C.clique K (hI.mp hK).1, (hI.mp hK).2⟩)
    hYc hYU
  let Z : Set EuclideanPlane := Y ∪ ⋃ K ∈ I, D K
  have hZc : IsClosed Z := hYc.union (I.finite_toSet.isClosed_biUnion
    fun K hK => (h₂ K hK).1.disc.isCompact.isClosed)
  let A : Set α := {v | {v} ∈ F}
  have hAfin : A.Finite := by
    refine (C.finite.biUnion hfin).subset fun v hv => mem_iUnion₂.mpr ⟨{v}, hv, rfl⟩
  have hAV : A ⊆ V(N.G) := fun v hv => hKV _ hv rfl
  have hnot : ∀ v ∈ A, ∀ K ∈ F, K.ncard ≠ 1 → vertexPt P.Γ v ∈ vertexPt P.Γ '' K → False := by
    intro v hv K hK hne hm
    obtain ⟨w, hw, he⟩ := hm
    have := vertexPt_injOn P.Γ (hKV K hK hw) (hAV hv) he
    subst this
    have hEq := C.antichain _ hv K hK (singleton_subset_iff.mpr hw)
    exact hne (hEq ▸ ncard_singleton w)
  have hAZ : ∀ v ∈ A, vertexPt P.Γ v ∉ Z := by
    rintro v hv (h | h)
    · obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp h
      exact hnot v hv K hK.1 (by rw [hK.2]; norm_num)
        ((h₃ K hK.1 hK.2).2 ⟨hxK, IsTidyPresentation.mem_U (hAV hv)⟩)
    · obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp h
      exact hnot v hv K (hI.mp hK).1 (by rw [(hI.mp hK).2]; norm_num)
        ((h₂ K hK).2.1 ⟨hxK, vertexPt_mem_V P.Γ (hAV hv)⟩)
  obtain ⟨s, h₁, hp₁⟩ := exists_vertex_discs T hAfin hAV (fun v hv => C.off₀ v hv) hZc hAZ
  have hcases : ∀ K ∈ F, K.ncard = 3 ∨ K.ncard = 2 ∨ ∃ v, K = {v} := by
    intro K hK
    have h3 := (C.clique K hK).2.1
    have h0 : K.ncard ≠ 0 := (ncard_ne_zero_of_mem (C.nonempty K hK).some_mem (hfin K hK))
    have : K.ncard = 3 ∨ K.ncard = 2 ∨ K.ncard = 1 := by omega
    rcases this with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (ncard_eq_one.mp h))
  let β : Set α → Set EuclideanPlane := fun K =>
    if K.ncard = 3 then β₃ K else if K.ncard = 2 then D K else
      if h : ∃ v, K = {v} then s h.choose else ∅
  have hβ₃ : ∀ {K : Set α}, K.ncard = 3 → β K = β₃ K := fun h => by simp [β, h]
  have hβ₂ : ∀ {K : Set α}, K.ncard = 2 → β K = D K := fun h => by simp [β, h]
  have hβ₁ : ∀ v : α, β {v} = s v := by
    intro v
    have h : ∃ w, ({v} : Set α) = {w} := ⟨v, rfl⟩
    have hc : h.choose = v := (singleton_injective h.choose_spec).symm
    simp only [β, ncard_singleton, OfNat.one_ne_ofNat, ↓reduceIte, h, ↓reduceDIte, hc]
  -- The discs of two different sizes meet as they should.
  have h32 : ∀ K ∈ F, ∀ K' ∈ F, K.ncard = 3 → K'.ncard = 2 →
      β₃ K ∩ D K' ⊆ vertexPt P.Γ '' (K ∩ K') := by
    rintro K hK K' hK' h3 h2 x ⟨hx, hx'⟩
    have hk' : K' ∈ I := hI.mpr ⟨hK', h2⟩
    have hxK' := (h₂ K' hk').2.2 ⟨hx', mem_iUnion₂.mpr ⟨K, ⟨hK, h3⟩, hx⟩⟩
    obtain ⟨w, hw, rfl⟩ := id hxK'
    exact IsTidyPresentation.pt_inter (hKV K hK) (hKV K' hK')
      ((h₃ K hK h3).2 ⟨hx, IsTidyPresentation.mem_U (hKV K' hK' hw)⟩) hxK'
  have h31 : ∀ K ∈ F, K.ncard = 3 → ∀ v ∈ A, Disjoint (β₃ K) (s v) := by
    intro K hK h3 v hv
    rw [disjoint_left]
    exact fun x hx hs => disjoint_left.mp (h₁ v hv).2 hs
      (Or.inl (mem_iUnion₂.mpr ⟨K, ⟨hK, h3⟩, hx⟩))
  have h21 : ∀ K ∈ F, K.ncard = 2 → ∀ v ∈ A, Disjoint (D K) (s v) := by
    intro K hK h2 v hv
    rw [disjoint_left]
    exact fun x hx hs => disjoint_left.mp (h₁ v hv).2 hs
      (Or.inr (mem_iUnion₂.mpr ⟨K, hI.mpr ⟨hK, h2⟩, hx⟩))
  refine ⟨β, fun K hK => ?_, fun K hK K' hK' hne x hx => ?_⟩
  · rcases hcases K hK with h | h | ⟨v, rfl⟩
    · rw [hβ₃ h]
      exact (h₃ K hK h).1
    · rw [hβ₂ h]
      exact (h₂ K (hI.mpr ⟨hK, h⟩)).1
    · rw [hβ₁]
      exact (h₁ v hK).1
  · rcases hcases K hK with h | h | ⟨v, rfl⟩ <;> rcases hcases K' hK' with h' | h' | ⟨w, rfl⟩
    · rw [hβ₃ h, hβ₃ h'] at hx
      exact hp₃ K hK K' hK' h h' hne hx
    · rw [hβ₃ h, hβ₂ h'] at hx
      exact h32 K hK K' hK' h h' hx
    · rw [hβ₃ h, hβ₁] at hx
      exact (disjoint_left.mp (h31 K hK h w hK') hx.1 hx.2).elim
    · rw [hβ₂ h, hβ₃ h'] at hx
      rw [inter_comm]
      exact h32 K' hK' K hK h' h ⟨hx.2, hx.1⟩
    · rw [hβ₂ h, hβ₂ h'] at hx
      exact hp₂ K (hI.mpr ⟨hK, h⟩) K' (hI.mpr ⟨hK', h'⟩) hne hx
    · rw [hβ₂ h, hβ₁] at hx
      exact (disjoint_left.mp (h21 K hK h w hK') hx.1 hx.2).elim
    · rw [hβ₁, hβ₃ h'] at hx
      exact (disjoint_left.mp (h31 K' hK' h' v hK) hx.2 hx.1).elim
    · rw [hβ₁, hβ₂ h'] at hx
      exact (disjoint_left.mp (h21 K' hK' h' v hK) hx.2 hx.1).elim
    · rw [hβ₁, hβ₁] at hx
      have hvw : v ≠ w := fun h => hne (by rw [h])
      exact (disjoint_left.mp (hp₁ v hK w hK' hvw) hx.1 hx.2).elim

end GraphMinor.GM09
