/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.ReEdge

/-!
# Graph Minors XVII, Section 12: from a portrayal of `G*` to a portrayal of `G`

This file proves (12.6) of Robertson and Seymour, *Graph Minors. XVII. Taming a Vortex*, J. Combin.
Theory Ser. B 77 (1999), 200.

- **(12.6)** (`theorem_12_6`, page 200).

The proof adds the edges of `G` to `G*` one at a time, by (12.4). The hypergraph `G ∪ G*` of the
paper is `mixGraph G E(G)`, whose edges are in `β ⊕ Sym2 α`.

At the end we delete the edges of `G*`. The paper says only that this gives a portrayal resembling
`π`, but a deletion can lower a warp. We show that it does not: `G*` can be put back by
`Portrayal.exists_moved`, so a lower warp would give a central portrayal of `G*` simpler than `π`.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- Hypergraphs with the same vertices and 1-skeleton have the same `G*`. -/
theorem oneSkeleton_eq_of_skeleton_eq {b₁ b₂ : Type*} {A : Hypergraph α b₁} {B : Hypergraph α b₂}
  (hV : A.vertexSet = B.vertexSet) (h : A.skeleton = B.skeleton) :
    oneSkeletonHypergraph A = oneSkeletonHypergraph B := by
  refine Hypergraph.ext hV (by change A.skeleton.edgeSet = B.skeleton.edgeSet; rw [h]) ?_
  funext s v
  apply propext
  change (s ∈ A.skeleton.edgeSet ∧ v ∈ s) ↔ (s ∈ B.skeleton.edgeSet ∧ v ∈ s)
  rw [h]

section Embodiment

variable {b : Type*} {H : Hypergraph α b} {R : Hypergraph α (Sym2 α)} {θ : ℕ}
  {𝒯s : Set (Hypergraph α (Sym2 α) × Hypergraph α (Sym2 α))}

theorem embodiment_isTangle (hH : oneSkeletonHypergraph H = R) (h𝒯 : IsTangle R θ 𝒯s) :
    IsTangle H θ (embodimentTangle H 𝒯s θ) :=
  theorem_12_5_proof (hH ▸ h𝒯)

/-- If `A*` is small, then the separation of `G*` made from `(A, B)` is in `𝒯*`. -/
theorem skeleton_mem_of_embodiment (hH : oneSkeletonHypergraph H = R)
  (h𝒯 : IsTangle R θ 𝒯s) {A B : Hypergraph α b}
    (h : (A, B) ∈ embodimentTangle H 𝒯s θ) :
    (oneSkeletonHypergraph A, (oneSkeletonHypergraph B).deleteEdges (oneSkeletonHypergraph
      A).edgeSet) ∈ 𝒯s := by
  subst hH
  obtain ⟨hs, ho, C, hC⟩ := h
  exact GM10.theorem_2_9_proof h𝒯 hC (isSeparation_oneSkeleton hs) ho (.inr (.inl subset_rfl))

/-- A separation of `H` of small order whose left side lies on the vertices of a member of `𝒯*` is
in the embodiment. -/
theorem embodiment_mem (hH : oneSkeletonHypergraph H = R) (h𝒯 : IsTangle R θ 𝒯s) {A D : Hypergraph
  α b}
    (hs : H.IsSeparation A D) (ho : separationOrder A D < θ) {A₀ B₀ : Hypergraph α (Sym2 α)} (hm :
      (A₀, B₀) ∈ 𝒯s)
    (hsub : A.vertexSet ⊆ A₀.vertexSet) : (A, D) ∈ embodimentTangle H 𝒯s θ := by
  subst hH
  exact ⟨hs, ho, _, GM10.theorem_2_9_proof h𝒯 hm (isSeparation_oneSkeleton hs) ho (.inr
    (.inl hsub))⟩

/-- A member of a quotient of the embodiment lies on the vertices of a member of the same quotient
of `𝒯*`. -/
theorem embodiment_quotient_dom (hH : oneSkeletonHypergraph H = R) (h𝒯 : IsTangle R θ 𝒯s) {Z : Set
  α} {A B : Hypergraph α b}
    (h : (A, B) ∈ quotientTangle H (embodimentTangle H 𝒯s θ) Z) :
    ∃ A' B', (A', B') ∈ quotientTangle R 𝒯s Z ∧ A.vertexSet ⊆ A'.vertexSet := by
  obtain ⟨-, ⟨A₀, B₀⟩, hm, hZ, h1, h2⟩ := h
  have hm' := skeleton_mem_of_embodiment hH h𝒯 hm
  have hs := h𝒯.isSeparation hm'
  dsimp only at h1 h2 hZ
  subst h1 h2
  exact ⟨_, _, ⟨GM10.IsSeparation.quotientVertices hs Z, _, hm', hZ, rfl, rfl⟩, subset_rfl⟩

end Embodiment

/-- The hypergraph `G_i` of the paper: the vertices of `G`, the edges of `X`, and the edges of `G*`.
-/
@[expose] def mixGraph (G : Hypergraph α β) (X : Set β) : Hypergraph α (β ⊕ Sym2 α) where
  vertexSet := G.vertexSet
  edgeSet := Sum.inl '' (X ∩ G.edgeSet) ∪ Sum.inr '' G.skeleton.edgeSet
  Inc e v := Sum.elim (fun e => e ∈ X ∧ G.Inc e v) (fun s => s ∈ G.skeleton.edgeSet ∧ v ∈ s) e
  vertex_mem_of_inc := by
    rintro (e | s) v h
    · exact G.vertex_mem_of_inc h.2
    · exact (oneSkeletonHypergraph G).vertex_mem_of_inc (e := s) h
  edge_mem_of_inc := by
    rintro (e | s) v h
    · exact .inl ⟨e, ⟨h.1, G.edge_mem_of_inc h.2⟩, rfl⟩
    · exact .inr ⟨s, h.1, rfl⟩
  vertexSet_finite := G.vertexSet_finite
  edgeSet_finite := ((G.edgeSet_finite.subset inter_subset_right).image _).union
    ((oneSkeletonHypergraph G).edgeSet_finite.image _)

theorem mixGraph_skeleton (G : Hypergraph α β) (X : Set β) : (mixGraph G X).skeleton = G.skeleton
  := by
  ext x y
  constructor
  · rintro ⟨hne, (e | s), hx, hy⟩
    · exact ⟨hne, e, hx.2, hy.2⟩
    · have hs : s = s(x, y) := ((Sym2.mem_and_mem_iff hne).1 ⟨hx.2, hy.2⟩)
      subst hs
      exact (SimpleGraph.mem_edgeSet _).1 hx.1
  · intro h
    have hm : s(x, y) ∈ G.skeleton.edgeSet := (SimpleGraph.mem_edgeSet _).2 h
    exact ⟨h.1, .inr s(x, y), ⟨hm, Sym2.mem_mk_left _ _⟩, ⟨hm, Sym2.mem_mk_right _ _⟩⟩

theorem mixGraph_oneSkeleton (G : Hypergraph α β) (X : Set β) :
    oneSkeletonHypergraph (mixGraph G X) = oneSkeletonHypergraph G :=
  oneSkeleton_eq_of_skeleton_eq rfl (mixGraph_skeleton G X)

/-- Deleting the new edge `x` from `G_{i}` gives `G_{i-1}`. -/
theorem mixGraph_deleteEdges (G : Hypergraph α β) {X : Set β} {x : β} (hx : x ∉ X) :
    (mixGraph G (insert x X)).deleteEdges {Sum.inl x} = mixGraph G X := by
  refine Hypergraph.ext rfl ?_ ?_
  · ext e
    constructor
    · rintro ⟨(⟨f, ⟨hf, hfE⟩, rfl⟩ | ⟨s, hs, rfl⟩), hne⟩
      · rcases hf with rfl | hf
        · exact absurd rfl hne
        · exact .inl ⟨f, ⟨hf, hfE⟩, rfl⟩
      · exact .inr ⟨s, hs, rfl⟩
    · rintro (⟨f, ⟨hf, hfE⟩, rfl⟩ | ⟨s, hs, rfl⟩)
      · refine ⟨.inl ⟨f, ⟨.inr hf, hfE⟩, rfl⟩, ?_⟩
        rintro h
        rw [mem_singleton_iff, Sum.inl_injective.eq_iff] at h
        exact hx (h ▸ hf)
      · exact ⟨.inr ⟨s, hs, rfl⟩, by simp⟩
  · funext e v
    apply propext
    rcases e with e | s
    · change ((e ∈ insert x X ∧ G.Inc e v) ∧ Sum.inl e ∉ ({Sum.inl x} : Set (β ⊕ Sym2 α))) ↔ (e ∈ X
        ∧ G.Inc e v)
      constructor
      · rintro ⟨⟨h1 | h1, h2⟩, h3⟩
        · exact absurd (by rw [h1]; rfl) h3
        · exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨.inr h1, h2⟩, ?_⟩
        rintro h
        rw [mem_singleton_iff, Sum.inl_injective.eq_iff] at h
        exact hx (h ▸ h1)
    · change ((s ∈ G.skeleton.edgeSet ∧ v ∈ s) ∧ Sum.inr s ∉ ({Sum.inl x} : Set (β ⊕ Sym2 α))) ↔
        (s ∈ G.skeleton.edgeSet ∧ v ∈ s)
      simp

/-- (12.4), with `G \ e` named `G₀`. -/
theorem theorem_12_4_of_eq {b : Type*} {H G₀ : Hypergraph α b} {e : b} (he : e ∈ H.edgeSet)
  (hG₀ : H.deleteEdges {e} = G₀)
    (hK : IsClique G₀ (H.ends e)) {𝒯 : Set (Hypergraph α b × Hypergraph α b)} {θ p : ℕ}
      (h𝒯 : IsTangle G₀ θ 𝒯)
    (hθ : 4 * p + 9 < θ) (π : Portrayal G₀) (hc : π.IsCentral 𝒯) (hred : π.IsRedundant 𝒯 θ
      (2 * p + 7)) (hwarp : π.warp ≤ p) :
    ∃ π' : Portrayal H, π'.IsCentral (inducedSubhypergraphTangle H G₀ 𝒯 θ) ∧ π'.Resembles π := by
  subst hG₀
  exact theorem_12_4_proof he hK h𝒯 hθ π hc hred hwarp

/-- A central portrayal of `H`, with warps at most those of a redundant `π` of `G*`, resembles `π`.
Otherwise, moving it to `G*` gives a central portrayal simpler than `π`. -/
theorem resembles_of_warpLE {b : Type*} {G : Hypergraph α β} {H : Hypergraph α b} {θ p : ℕ}
    {𝒯s : Set (Hypergraph α (Sym2 α) × Hypergraph α (Sym2 α))} (hH : oneSkeletonHypergraph H
      = oneSkeletonHypergraph G)
    (h𝒯 : IsTangle (oneSkeletonHypergraph G) θ 𝒯s) (hθ : max 3 (2 * p + 2) < θ) {π : Portrayal
      (oneSkeletonHypergraph G)}
    (hred : π.IsRedundant 𝒯s θ (2 * p + 7)) {π₁ : Portrayal H} (hc₁ : π₁.IsCentral
      (embodimentTangle H 𝒯s θ))
    (hw₁ : π₁.warp ≤ p) (hl : π₁.WarpLE π) : π₁.Resembles π := by
  obtain ⟨ψ, hψ⟩ := id hl
  rcases Portrayal.resembles_or_isSimpler_of_warpAt_le ψ hψ with h | h
  · exact h
  exfalso
  have hV : (oneSkeletonHypergraph G).vertexSet = H.vertexSet := (congrArg Hypergraph.vertexSet
    hH).symm
  obtain ⟨π₂, hc₂, hl₂⟩ := π₁.exists_moved (H₂ := oneSkeletonHypergraph G) hV
    (π₁.cells_nonempty (embodiment_isTangle hH h𝒯)) (hH ▸ edgesCovered_oneSkeleton H) (θ₂ := θ) (𝒯₂
      := 𝒯s)
    (fun c hc => by have := π₁.ncard_cell_inter_other_le hw₁ hc; omega)
    (fun c hc A D hs ho hVA => by
      obtain ⟨B, hB⟩ := hc₁ c hc
      exact GM10.theorem_2_9_proof h𝒯 (skeleton_mem_of_embodiment hH h𝒯 hB) hs ho (.inr
        (.inl hVA.subset)))
  exact hred.isZeroRedundant h𝒯 π₂ hc₂ (hl₂.trans_isSimpler h)

/-- **Graph Minors XVII, (12.6)** (page 200): "Let $G$ be a hypergraph, and let $\mathscr{T}^*$ be a
tangle in $G^*$ of order $>4p+9$. Let $\mathscr{T}$ be the embodiment of $\mathscr{T}^*$ in $G$. Let
$\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $(2p+7)$-redundant, $\mathscr{T}^*$-central
portrayal of $G^*$ with warp $\le p$. Then there is a $\mathscr{T}$-central portrayal of $G$
resembling $\pi$." -/
theorem theorem_12_6_proof {G : Hypergraph α β} {θ p : ℕ} {𝒯s : Set (Hypergraph α
  (Sym2 α) × Hypergraph α (Sym2 α))}
    (h𝒯 : IsTangle (oneSkeletonHypergraph G) θ 𝒯s) (hθ : 4 * p + 9 < θ) (π : Portrayal
      (oneSkeletonHypergraph G))
    (hc : π.IsCentral 𝒯s) (hred : π.IsRedundant 𝒯s θ (2 * p + 7)) (hwarp : π.warp ≤ p) :
    ∃ π' : Portrayal G, π'.IsCentral (embodimentTangle G 𝒯s θ) ∧ π'.Resembles π := by
  have hp : 1 ≤ p := π.one_le_warp.trans hwarp
  have hmax : max 3 (2 * p + 2) = 2 * p + 2 := by omega
  have hstage : ∀ X (π₁ : Portrayal (mixGraph G X)), π₁.Resembles π → π₁.IsRedundant
    (embodimentTangle (mixGraph G X) 𝒯s θ) θ (2 * p + 7) := by
    intro X π₁ hr
    refine Portrayal.IsRedundant.of_moved (embodiment_isTangle (mixGraph_oneSkeleton G X) h𝒯) h𝒯
      (by omega) rfl ?_ (by omega) hred hwarp hr.warpLE
      fun Z _ _ A B h _ => embodiment_quotient_dom (mixGraph_oneSkeleton G X) h𝒯 h
    exact mixGraph_oneSkeleton G X ▸ edgesCovered_oneSkeleton (mixGraph G X)
  have hmain : ∀ X : Set β, X.Finite → X ⊆ G.edgeSet → ∃ π₁ : Portrayal (mixGraph G X),
      π₁.IsCentral (embodimentTangle (mixGraph G X) 𝒯s θ) ∧ π₁.Resembles π := by
    intro X hX
    induction X, hX using Set.Finite.induction_on with
    | empty =>
      intro _
      obtain ⟨π₁, hc₁, hl₁⟩ := π.exists_moved (H₂ := mixGraph G ∅) (θ₂ := θ) rfl
        (π.cells_nonempty h𝒯)
        (by
          rintro _ (⟨f, ⟨hf, -⟩, rfl⟩ | ⟨s, hs, rfl⟩)
          · exact absurd hf (notMem_empty f)
          · exact .inl ⟨s, hs, fun v hv => hv⟩)
        (fun c hc' => by have := π.ncard_cell_inter_other_le hwarp hc'; omega)
        (fun c hc' A D hs ho hVA => by
          obtain ⟨B, hB⟩ := hc c hc'
          exact embodiment_mem (mixGraph_oneSkeleton G ∅) h𝒯 hs ho hB hVA.subset)
      exact ⟨π₁, hc₁, resembles_of_warpLE (p := p) (mixGraph_oneSkeleton G ∅) h𝒯
        (by omega) hred hc₁ (hl₁.warp_le.trans hwarp) hl₁⟩
    | @insert x X hxX _ ih =>
      intro hsub
      obtain ⟨π₀, hc₀, hr₀⟩ := ih ((subset_insert _ _).trans hsub)
      have he : (Sum.inl x : β ⊕ Sym2 α) ∈ (mixGraph G (insert x X)).edgeSet :=
        .inl ⟨x, ⟨mem_insert _ _, hsub (mem_insert _ _)⟩, rfl⟩
      have hK : IsClique (mixGraph G X) ((mixGraph G (insert x X)).ends (Sum.inl x)) :=
        ⟨fun v hv => G.vertex_mem_of_inc hv.2, fun u hu v hv hne => by
          rw [mixGraph_skeleton]
          exact ⟨hne, x, hu.2, hv.2⟩⟩
      obtain ⟨π', hc', hr'⟩ := theorem_12_4_of_eq he (mixGraph_deleteEdges G hxX) hK
        (embodiment_isTangle (mixGraph_oneSkeleton G X) h𝒯) hθ π₀ hc₀ (hstage X π₀ hr₀)
          (hr₀.warp_eq ▸ hwarp)
      refine ⟨π', fun c hcc => ?_, hr'.trans hr₀⟩
      obtain ⟨D, hs, ho, hm⟩ := hc' c hcc
      obtain ⟨C, hC⟩ := hm.2.2
      have hVsub : (π'.cellGraph c).vertexSet ⊆ (oneSkeletonHypergraph
        (π'.cellGraph c ∩ mixGraph G X)).vertexSet :=
        fun v hv => ⟨hv, (π'.cellGraph_le c hcc).vertexSet_subset hv⟩
      exact ⟨D, embodiment_mem (mixGraph_oneSkeleton G _) h𝒯 hs ho hC hVsub⟩
  obtain ⟨π₁, hc₁, hr₁⟩ := hmain _ G.edgeSet_finite subset_rfl
  have hw₁ : π₁.warp ≤ p := hr₁.warp_eq ▸ hwarp
  have hH := mixGraph_oneSkeleton G G.edgeSet
  obtain ⟨π', hc', hl'⟩ := π₁.exists_moved (H₂ := G) (θ₂ := θ) rfl (π₁.cells_nonempty
    (embodiment_isTangle hH h𝒯))
    (fun e he => .inl ⟨.inl e, .inl ⟨e, ⟨he, he⟩, rfl⟩, fun v hv => ⟨he, hv⟩⟩)
    (fun c hc' => by have := π₁.ncard_cell_inter_other_le hw₁ hc'; omega)
    (fun c hc' A D hs ho hVA => by
      obtain ⟨B, hB⟩ := hc₁ c hc'
      exact embodiment_mem rfl h𝒯 hs ho (skeleton_mem_of_embodiment hH h𝒯 hB) hVA.subset)
  have hl : π'.WarpLE π := hl'.trans hr₁.warpLE
  exact ⟨π', hc', resembles_of_warpLE (p := p) rfl h𝒯 (by omega) hred hc'
    (hl.warp_le.trans hwarp) hl⟩

end GraphMinor.GM17
