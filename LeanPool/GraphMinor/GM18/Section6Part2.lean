/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM18.Section6Part1

/-!
# Graph Minors XVIII, Section 6 (Part 2): Well-Quasi-Ordering of Rootless Patchworks (6.6)

This file formalizes (6.6) (pages 104–106) of Robertson and Seymour,
*Graph Minors. XVIII. Tree-decompositions and well-quasi-ordering*, J. Combin. Theory Ser. B 89
(2003), 77–108, together with its two claims `lemma_6_6_claim_1` and `lemma_6_6_claim_2`:

- `lemma_6_6_claim_1` (Claim (1), page 105): for every `t ∈ V(T)` in a rooted decomposition `(T, τ)`
  of `P` whose underlying tree-decomposition `(S, σ)` is proper and whose pieces all belong to `𝒞`,
  the subtree patchwork `P | (τ × T^t)` belongs to `enlargementClass (rootingClosure 𝒞) 𝒞_t`.
- `lemma_6_6_claim_2` (Claim (2), page 105): if the subtree patchworks at the out-neighbours of `X`
  are well-quasi-ordered by simulation, then so are the subtree patchworks at `X`.
- `sigmaTree`: the arborescences `Tᵢ` side by side in `Σ k, ι k`, as the tree `M` of the paper.

The rest of the proof of (6.6), through Graph Minors IV, (3.3), is in `Section6Stars.lean`.
-/

public section

namespace GraphMinor.GM18

open SimpleGraph Hypergraph

universe u v w

variable {α : Type u} {β : Type v} {Ω : Type w}

/-! ## Rooting closure, existence of fresh hearts, and bounded root lengths -/

/-- The union `𝒞* = 𝒞 ∪ 𝒞'` of a class `𝒞` of partial `Ω`-patchworks with the class `𝒞'` of all
rootings of rootless members of `𝒞` (Graph Minors XVIII, proof of (6.6), page 105). -/
@[expose] def rootingClosure (𝒞 : Set (PartialPatchwork Ω α β)) : Set (PartialPatchwork Ω α β) :=
  𝒞 ∪ {P' : PartialPatchwork Ω α β | ∃ P ∈ 𝒞, IsRooting P P'}

/-- If `𝒞` is well-behaved, then `rootingClosure 𝒞` is well-behaved (by (6.1), page 105). -/
theorem wellBehaved_rootingClosure [Preorder Ω] {𝒞 : Set (PartialPatchwork Ω α β)}
    (h𝒞 : WellBehaved 𝒞) : WellBehaved (rootingClosure 𝒞) :=
  h𝒞.union (theorem_6_1_proof h𝒞)

/-- When `β` is infinite, every rooted location `ℒ` in `P.G` has a fresh edge assignment
`newEdge : RootedHypergraph α β → β` injective on `ℒ` with `newEdge A ∉ P.G.edgeSet` for all
`A ∈ ℒ`, and hence a heart `Q` satisfying `IsPlaceHeart P ℒ newEdge Q`. -/
theorem exists_fresh_isPlaceHeart [Infinite β] (P : PartialPatchwork Ω α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation P.G ℒ) :
    ∃ (newEdge : RootedHypergraph α β → β) (Q : PartialPatchwork Ω α β),
      IsPlaceHeart P ℒ newEdge Q ∧ ∀ ⦃A⦄, A ∈ ℒ → newEdge A ∉ P.G.edgeSet := by
  classical
  have hcompl_inf : ((P.G.edgeSet)ᶜ : Set β).Infinite := by
    rw [Set.compl_eq_univ_sdiff]
    exact Set.infinite_univ.sdiff P.G.edgeSet_finite
  let _ : Infinite ((P.G.edgeSet)ᶜ : Set β) := hcompl_inf.to_subtype
  let _ : Fintype ℒ := hℒ.finite.fintype
  let eℒ : ℒ ≃ Fin (Fintype.card ℒ) := Fintype.equivFin ℒ
  let emb : ℕ ↪ ((P.G.edgeSet)ᶜ : Set β) := Infinite.natEmbedding ((P.G.edgeSet)ᶜ : Set β)
  let d₀ : β := (emb 0).1
  let newEdge : RootedHypergraph α β → β := fun A ↦
    if hA : A ∈ ℒ then (emb (eℒ ⟨A, hA⟩).1).1 else d₀
  have hinj : Set.InjOn newEdge ℒ := by
    intro A₁ hA₁ A₂ hA₂ hEq
    dsimp only [newEdge] at hEq
    rw [dite_eq_left hA₁, dite_eq_left hA₂] at hEq
    have hemb_eq : emb (eℒ ⟨A₁, hA₁⟩).1 = emb (eℒ ⟨A₂, hA₂⟩).1 := Subtype.ext hEq
    have hfin_eq : eℒ ⟨A₁, hA₁⟩ = eℒ ⟨A₂, hA₂⟩ := Fin.ext (emb.injective hemb_eq)
    exact congrArg Subtype.val (eℒ.injective hfin_eq)
  have hfresh : ∀ ⦃A⦄, A ∈ ℒ → newEdge A ∉ P.G.edgeSet := by
    intro A hA
    dsimp only [newEdge]
    rw [dite_eq_left hA]
    exact (emb (eℒ ⟨A, hA⟩).1).2
  have hnotMem : ∀ ⦃A⦄, A ∈ ℒ → newEdge A ∉ (rootedLocationCore P.G ℒ).edgeSet :=
    fun _ hA hc ↦ hfresh hA (mem_rootedLocationCore_edgeSet_iff.1 hc).1
  exact ⟨newEdge, mkPlaceHeart P hℒ newEdge hinj hnotMem,
    isPlaceHeart_mkPlaceHeart P hℒ newEdge hinj hnotMem, hfresh⟩

/-- In any well-behaved class `𝒞*` of partial `Ω`-patchworks (where `Ω` is well-quasi-ordered),
there is an integer `k ≥ 0` such that `|πBar(P)| ≤ k` for all `P ∈ 𝒞*`
(Graph Minors XVIII, proof of (6.6), page 106: "since $\mathscr{C}$ is well-behaved, there exists
$k \ge 0$ such that $|\bar{\pi}(G)| \le k$ for every $(G, \mu, \Delta, \phi) \in \mathscr{C}$",
applied to `𝒞* = rootingClosure 𝒞`). -/
theorem WellBehaved.exists_roots_length_le [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω)
    {𝒞_star : Set (PartialPatchwork Ω α β)} (h𝒞_star : WellBehaved 𝒞_star) :
    ∃ k : ℕ, ∀ P ∈ 𝒞_star, P.G.roots.length ≤ k := by
  classical
  by_contra! h_unbdd
  choose P_of hP_of_mem hP_of_gt using h_unbdd
  let idx_P : ℕ → PartialPatchwork Ω α β :=
    fun m ↦ Nat.rec (P_of 0) (fun _ prev ↦ P_of prev.G.roots.length) m
  have hidx_mem : ∀ m, idx_P m ∈ 𝒞_star := by
    intro m
    cases m with
    | zero => exact hP_of_mem 0
    | succ n => exact hP_of_mem (idx_P n).G.roots.length
  have hidx_strictMono : StrictMono (fun m ↦ (idx_P m).G.roots.length) :=
    strictMono_nat_of_lt_succ fun m ↦ hP_of_gt (idx_P m).G.roots.length
  let UnitType := PUnit.{max w (max u v) + 1}
  have hUnit_wqo : WellQuasiOrderedLE UnitType := Finite.to_wellQuasiOrderedLE
  let Ω' : Type (max w (max u v)) := DisjointUnionQuasiOrder Ω UnitType
  have hΩ'_wqo : WellQuasiOrderedLE Ω' := wellQuasiOrderedLE_disjointUnion hΩ hUnit_wqo
  let ι : Ω ↪o Ω' := DisjointUnionQuasiOrder.inlEmb Ω UnitType
  let Q : ℕ → GM04.Patchwork Ω' α β := fun m ↦
    { G := (idx_P m).G
      dom := (idx_P m).dom
      μ := (idx_P m).μ
      Δ := (idx_P m).Δ
      φ := fun e ↦
        match (idx_P m).φ e with
        | (ω : Ω) => Sum.inl ω
        | ⊥ => Sum.inr PUnit.unit
      dom_subset := (idx_P m).dom_subset
      μ_nodup := (idx_P m).μ_nodup
      μ_set := (idx_P m).μ_set
      Δ_verts := (idx_P m).Δ_verts
      Δ_free := (idx_P m).Δ_free }
  have hQ_comp : ∀ m, ∃ P ∈ 𝒞_star, IsCompletion ι P (Q m) := by
    intro m
    refine ⟨idx_P m, hidx_mem m, ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, ?_⟩⟩
    intro e _ ω hφ
    change (match (idx_P m).φ e with | (ω' : Ω) => Sum.inl ω' | ⊥ => Sum.inr PUnit.unit) = Sum.inl ω
    rw [hφ]
  obtain ⟨i, j, hij, _, _, hexp, _⟩ := h𝒞_star Ω' ι hΩ'_wqo Q hQ_comp
  have hlen_eq : (idx_P i).G.roots.length = (idx_P j).G.roots.length := hexp.roots_length
  exact ne_of_lt (hidx_strictMono hij) hlen_eq

/-! ## Claim (1) of (6.6): Subtree patchworks as enlargements -/

/-- Restricting `toPartialPatchwork P` to `G'` is definitionally `toPartialPatchwork (P.restrict
G')`. -/
theorem toPartialPatchwork_restrict (P : GM04.Patchwork Ω α β) (G' : RootedHypergraph α β) :
    (toPartialPatchwork P).restrict G' = toPartialPatchwork (P.restrict G') := rfl

/-- If `G₁ ≤ G₂ ≤ P.G`, then `(P.restrict G₂).restrict G₁` is equivalent (`PatchworkEquiv`) to
`P.restrict G₁`. -/
theorem Patchwork.restrict_restrict_equiv {P : GM04.Patchwork Ω α β}
    {G₁ G₂ : RootedHypergraph α β}
    (h₂ : G₂.toHypergraph ≤ P.G.toHypergraph)
    (h₁ : G₁.toHypergraph ≤ G₂.toHypergraph) :
    PatchworkEquiv ((P.restrict G₂).restrict G₁) (P.restrict G₁) where
  G_eq := rfl
  dom_eq := by
    rw [(P.restrict G₂).restrict_dom h₁, P.restrict_dom h₂, P.restrict_dom (h₁.trans h₂),
      Set.inter_assoc, Set.inter_eq_right.mpr h₁.edgeSet_subset]
  μ_eq _ _ := rfl
  Δ_eq e he := by
    rw [(P.restrict G₂).restrict_Δ h₁ he, P.restrict_Δ h₂ (h₁.edgeSet_subset he),
      P.restrict_Δ (h₁.trans h₂) he]
  φ_eq _ _ := rfl

/-- Closure of a class `𝒞` of partial `Ω`-patchworks under `PatchworkEquiv`. -/
@[expose] def equivClosure (𝒞 : Set (PartialPatchwork Ω α β)) : Set (PartialPatchwork Ω α β) :=
  {Q | ∃ P ∈ 𝒞, PatchworkEquiv Q P}

theorem IsCompletion.congr_left {Ω' : Type*} [Preorder Ω] [Preorder Ω']
    {ι : Ω ↪o Ω'} {P₁ P₂ : PartialPatchwork Ω α β} {Q : GM04.Patchwork Ω' α β}
    (hP : PatchworkEquiv P₁ P₂) (h : IsCompletion ι P₁ Q) :
    IsCompletion ι P₂ Q where
  G_eq := h.G_eq.trans hP.G_eq
  dom_eq := h.dom_eq.trans hP.dom_eq
  μ_eq _ he := (h.μ_eq (hP.dom_eq.symm ▸ he)).trans (hP.μ_eq (hP.dom_eq.symm ▸ he))
  Δ_eq _ he := (h.Δ_eq (hP.G_eq.symm ▸ he)).trans (hP.Δ_eq (hP.G_eq.symm ▸ he))
  φ_eq _ he _ hω := h.φ_eq (hP.G_eq.symm ▸ he) ((hP.φ_eq (hP.G_eq.symm ▸ he)).trans hω)

theorem wellBehaved_equivClosure [Preorder Ω] {𝒞 : Set (PartialPatchwork Ω α β)}
    (h𝒞 : WellBehaved 𝒞) : WellBehaved (equivClosure 𝒞) := by
  intro Ω' _ ι hΩ' Q hQ
  refine h𝒞 Ω' ι hΩ' Q fun i ↦ ?_
  obtain ⟨P', ⟨P, hP_mem, hP_equiv⟩, hcomp⟩ := hQ i
  exact ⟨P, hP_mem, hcomp.congr_left hP_equiv⟩

/-- If `P₁` and `P₂` are equivalent (`PatchworkEquiv P₁ P₂`) and `IsPlaceHeart P₁ ℒ newEdge Q`,
then `IsPlaceHeart P₂ ℒ newEdge Q`. -/
theorem IsPlaceHeart.congr_left {P₁ P₂ Q : PartialPatchwork Ω α β}
    {ℒ : Set (RootedHypergraph α β)} {newEdge : RootedHypergraph α β → β}
    (hP : PatchworkEquiv P₁ P₂) (hQ : IsPlaceHeart P₁ ℒ newEdge Q) :
    IsPlaceHeart P₂ ℒ newEdge Q where
  isRootedLocation := hP.G_eq ▸ hQ.isRootedLocation
  injOn_newEdge := hQ.injOn_newEdge
  newEdge_notMem_core := hP.G_eq ▸ hQ.newEdge_notMem_core
  vertexSet_eq := hP.G_eq ▸ hQ.vertexSet_eq
  edgeSet_eq := hP.G_eq ▸ hQ.edgeSet_eq
  roots_eq := hP.G_eq ▸ hQ.roots_eq
  ends_core := hP.G_eq ▸ hQ.ends_core
  ends_newEdge := hQ.ends_newEdge
  dom_eq := by
    rw [← hP.G_eq, ← hP.dom_eq]
    exact hQ.dom_eq
  μ_core f hf := by
    rw [← hP.G_eq, ← hP.dom_eq] at hf
    rw [hQ.μ_core hf, hP.μ_eq hf.2]
  μ_newEdge := hQ.μ_newEdge
  Δ_core f hf := by
    rw [← hP.G_eq] at hf
    have hfE : f ∈ P₁.G.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 hf).1
    rw [hQ.Δ_core hf, hP.Δ_eq hfE]
  Δ_newEdge A hA := by
    rw [hQ.Δ_newEdge hA]
    have hle₁ : A.toHypergraph ≤ P₁.G.toHypergraph := (hQ.isRootedLocation.isComplemented hA).le
    have hle₂ : A.toHypergraph ≤ P₂.G.toHypergraph := hP.G_eq ▸ hle₁
    have hfg : PatchworkEquiv (P₁.restrict A) (P₂.restrict A) :=
      { G_eq := rfl
        dom_eq := by rw [P₁.restrict_dom hle₁, P₂.restrict_dom hle₂, hP.dom_eq]
        μ_eq := fun e he ↦ by
          rw [P₁.restrict_dom hle₁] at he
          exact hP.μ_eq he.1
        Δ_eq := fun e he ↦ by
          rw [P₁.restrict_Δ hle₁ he, P₂.restrict_Δ hle₂ he]
          exact hP.Δ_eq (hle₁.edgeSet_subset he)
        φ_eq := fun e he ↦ hP.φ_eq (hle₁.edgeSet_subset he) }
    exact hfg.feasibleGroupings_eq
  φ_core f hf := by
    rw [← hP.G_eq] at hf
    have hfE : f ∈ P₁.G.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 hf).1
    rw [hQ.φ_core hf, hP.φ_eq hfE]
  φ_newEdge := hQ.φ_newEdge

/-- `P.restrict P.G` is equivalent (`PatchworkEquiv`) to `P`. -/
theorem patchworkEquiv_restrict_self (P : GM04.Patchwork Ω α β) :
    PatchworkEquiv (P.restrict P.G) P where
  G_eq := rfl
  dom_eq := by rw [P.restrict_dom le_rfl, Set.inter_eq_left.mpr P.dom_subset]
  μ_eq _ _ := rfl
  Δ_eq _ he := P.restrict_Δ le_rfl he
  φ_eq _ _ := rfl

/-- In an arborescence `T` with `T.verts = Finset.univ` and `S = arborescenceUnderlying T`, where
`(T, τ)` is a `GM04.IsTreeDecomposition` of `G` and `σ t = (τ t).toHypergraph`, for every
`g ∈ T.edges`, `(GM04.cross τ (T.subtreeAt g) g).toHypergraph = GM10.treeDecompSide S σ s(g,
T.parent g) g`
and `(GM04.cross τ (T.rootSide g) T.root).toHypergraph = GM10.treeDecompSide S σ s(g, T.parent g)
(T.parent g)`. -/
private theorem cross_subtreeAt_and_rootSide_eq_treeDecompSide {ι : Type*} [Fintype ι]
    {G : RootedHypergraph α β} {T : GM04.RootedTree ι} {τ : ι → RootedHypergraph α β}
    (htd : GM04.IsTreeDecomposition G T τ) (hT_verts : T.verts = Finset.univ)
    {S : SimpleGraph ι} {σ : ι → Hypergraph α β}
    (hT_S : arborescenceUnderlying T = S) (hσ : ∀ t, (τ t).toHypergraph = σ t)
    {g : ι} (hg : g ∈ T.edges) :
    (GM04.cross τ (T.subtreeAt g) g).toHypergraph =
      GM10.treeDecompSide S σ s(g, T.parent g) g ∧
    (GM04.cross τ (T.rootSide g) T.root).toHypergraph =
      GM10.treeDecompSide S σ s(g, T.parent g) (T.parent g) := by
  classical
  have hg_sub : g ∈ T.subtreeAt g := T.self_mem_subtreeAt (hT_verts ▸ Finset.mem_univ g)
  have hroot_mem : T.root ∈ T.rootSide g := T.root_mem_rootSide hg
  have hreach_sub : ∀ t : ι,
      (S.deleteEdges {s(g, T.parent g)}).Reachable g t ↔ t ∈ T.subtreeAt g := by
    intro t
    rw [← hT_S]
    exact reachable_deleteEdges_arborescenceUnderlying_iff T hT_verts hg t
  have hreach_rootSide : ∀ t : ι,
      (S.deleteEdges {s(g, T.parent g)}).Reachable (T.parent g) t ↔ t ∈ T.rootSide g := by
    intro t
    rw [← hT_S]
    exact reachable_parent_deleteEdges_arborescenceUnderlying_iff T hT_verts hg t
  have hle_σ : ∀ t : ι, σ t ≤ G.toHypergraph :=
    fun t ↦ hσ t ▸ htd.le t (hT_verts ▸ Finset.mem_univ t)
  refine ⟨?_, ?_⟩
  · refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (htd.cross_le (T.subtreeAt_subset_verts g) hg_sub)
      (biUnion_le fun t _ ↦ hle_σ t) ?_ ?_
    · rw [GM04.cross_toHypergraph_of_mem τ hg_sub]
      ext v
      simp only [GM10.treeDecompSide, biUnion_vertexSet, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and, hreach_sub, hσ]
    · rw [GM04.cross_toHypergraph_of_mem τ hg_sub]
      ext e
      simp only [GM10.treeDecompSide, biUnion_edgeSet, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and, hreach_sub, hσ]
  · refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (htd.cross_le (T.rootSide_subset_verts g) hroot_mem)
      (biUnion_le fun t _ ↦ hle_σ t) ?_ ?_
    · rw [GM04.cross_toHypergraph_of_mem τ hroot_mem]
      ext v
      simp only [GM10.treeDecompSide, biUnion_vertexSet, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and, hreach_rootSide, hσ]
    · rw [GM04.cross_toHypergraph_of_mem τ hroot_mem]
      ext e
      simp only [GM10.treeDecompSide, biUnion_edgeSet, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and, hreach_rootSide, hσ]

/-- Every edge `x` of `S = arborescenceUnderlying T` (where `T.verts = Finset.univ`) incident with
`t`
is either `s(y, t)` for some `y ∈ T.children t` or (when `t ≠ T.root`) `s(t, T.parent t)`. -/
private theorem vertexLocation_eq_children_or_parent {ι : Type*} [Fintype ι] [Preorder Ω]
    {P : GM04.Patchwork Ω α β} (hrootless : IsRootless P)
    {T : GM04.RootedTree ι} {τ : ι → RootedHypergraph α β}
    (hdec : IsRootedDecomposition P T τ) (hT_verts : T.verts = Finset.univ)
    {S : SimpleGraph ι} {σ : ι → Hypergraph α β}
    (hT_S : arborescenceUnderlying T = S) (hσ : ∀ u, (τ u).toHypergraph = σ u) (t : ι) :
    let ℒ : Set (RootedHypergraph α β) :=
      {A | ∃ y ∈ T.children t, A = GM04.cross τ (T.subtreeAt y) y}
    ((∀ ht : t ∈ T.edges,
      rootedLocationToLocation P.G
          (insert (rootedDecompRootSide hdec.isTreeDecomposition ht) ℒ) =
        vertexLocation S σ t) ∧
     (t ∉ T.edges →
      rootedLocationToLocation P.G ℒ = vertexLocation S σ t)) := by
  classical
  intro ℒ
  have hℒ_toLoc : ∀ y ∈ T.children t,
      let A := GM04.cross τ (T.subtreeAt y) y
      (A.toHypergraph, complementHypergraph P.G A) =
        (GM10.treeDecompSide S σ s(y, t) y, GM10.treeDecompSide S σ s(y, t) t) := by
    intro y hy A
    obtain ⟨hye, hpar_y⟩ := T.mem_children_iff.1 hy
    obtain ⟨hcomp_y, hcomp_y_eq⟩ := theorem_6_5_1 hdec hye
    have ⟨hsub_y, hroot_y⟩ :=
      cross_subtreeAt_and_rootSide_eq_treeDecompSide hdec.isTreeDecomposition hT_verts hT_S hσ hye
    rw [complementHypergraph_eq_of_isComplemented hcomp_y, hcomp_y_eq, hsub_y, hroot_y, hpar_y]
  refine ⟨fun ht ↦ ?_, fun ht ↦ ?_⟩
  · let G₀ := rootedDecompRootSide hdec.isTreeDecomposition ht
    have hG₀_toLoc : (G₀.toHypergraph, complementHypergraph P.G G₀) =
        (GM10.treeDecompSide S σ s(T.parent t, t) (T.parent t),
          GM10.treeDecompSide S σ s(T.parent t, t) t) := by
      obtain ⟨hcomp_t, hcomp_t_eq, _⟩ := theorem_6_5_2 hrootless hdec ht
      have ⟨hsub_t, hroot_t⟩ :=
        cross_subtreeAt_and_rootSide_eq_treeDecompSide hdec.isTreeDecomposition hT_verts hT_S hσ ht
      rw [complementHypergraph_eq_of_isComplemented hcomp_t, hcomp_t_eq]
      change ((GM04.cross τ (T.rootSide t) T.root).toHypergraph,
          (GM04.cross τ (T.subtreeAt t) t).toHypergraph) = _
      rw [hsub_t, hroot_t, Sym2.eq_swap]
    ext p
    simp only [rootedLocationToLocation, Set.mem_image, Set.mem_insert_iff, vertexLocation,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨A, rfl | ⟨y, hy, rfl⟩, rfl⟩
      · rw [hG₀_toLoc]
        refine ⟨T.parent t, ?_, rfl⟩
        rw [← hT_S]
        exact Or.inl ⟨ht, rfl⟩
      · rw [hℒ_toLoc y hy]
        obtain ⟨hye, hpar_y⟩ := T.mem_children_iff.1 hy
        refine ⟨y, ?_, rfl⟩
        rw [← hT_S]
        exact Or.inr ⟨hye, hpar_y⟩
    · rintro ⟨u, hadj, rfl⟩
      rw [← hT_S] at hadj
      rcases hadj with ⟨_, rfl⟩ | ⟨hue, hpar_u⟩
      · exact ⟨G₀, Or.inl rfl, hG₀_toLoc⟩
      · have huc : u ∈ T.children t := T.mem_children_iff.2 ⟨hue, hpar_u⟩
        exact ⟨GM04.cross τ (T.subtreeAt u) u, Or.inr ⟨u, huc, rfl⟩, hℒ_toLoc u huc⟩
  · ext p
    simp only [rootedLocationToLocation, Set.mem_image, vertexLocation, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨A, ⟨y, hy, rfl⟩, rfl⟩
      rw [hℒ_toLoc y hy]
      obtain ⟨hye, hpar_y⟩ := T.mem_children_iff.1 hy
      refine ⟨y, ?_, rfl⟩
      rw [← hT_S]
      exact Or.inr ⟨hye, hpar_y⟩
    · rintro ⟨u, hadj, rfl⟩
      rw [← hT_S] at hadj
      rcases hadj with ⟨hte, _⟩ | ⟨hue, hpar_u⟩
      · exact (ht hte).elim
      · have huc : u ∈ T.children t := T.mem_children_iff.2 ⟨hue, hpar_u⟩
        exact ⟨GM04.cross τ (T.subtreeAt u) u, ⟨u, huc, rfl⟩, hℒ_toLoc u huc⟩

private theorem cross_child_le_cross_parent
    {ι : Type*} {T : GM04.RootedTree ι} {τ : ι → RootedHypergraph α β}
    {G : RootedHypergraph α β} (htd : GM04.IsTreeDecomposition G T τ)
    {t y : ι} (htv : t ∈ T.verts) (hye : y ∈ T.edges) (hpar_y : T.parent y = t) :
    (GM04.cross τ (T.subtreeAt y) y).toHypergraph ≤
      (GM04.cross τ (T.subtreeAt t) t).toHypergraph :=
  htd.cross_le_cross
    (T.subtreeAt_mono (hpar_y ▸ T.reaches_parent (T.edges_subset_verts hye)))
    (T.subtreeAt_subset_verts t)
    (T.self_mem_subtreeAt (T.edges_subset_verts hye))
    (T.self_mem_subtreeAt htv)

/-- **Claim (1)** in the proof of Graph Minors XVIII, (6.6) (page 105):
"(1) *Let $t \in V(T)$ and let $N(t)$ be the set of all $y \in V(T)$ such that there is an edge of
$T$ with head $y$ and tail $t$. Then $P|\tau \times T^t$ is an enlargement of a member of
$\mathscr{C}^*$ by the set of $\Omega$-patchworks
$\mathscr{C}_t = \{P|\tau \times T^y \colon y \in N(t)\}$.*" -/
theorem lemma_6_6_claim_1 [Infinite β] [Preorder Ω] {ι : Type*} [Fintype ι]
    {𝒞 : Set (PartialPatchwork Ω α β)}
    {P : GM04.Patchwork Ω α β} (hrootless : IsRootless P)
    {S : SimpleGraph ι} {σ : ι → Hypergraph α β}
    (hprop : IsProper P.G.toHypergraph S σ)
    {T : GM04.RootedTree ι} (hT_verts : T.verts = Finset.univ)
    (hT_S : arborescenceUnderlying T = S)
    {τ : ι → RootedHypergraph α β}
    (hdec : IsRootedDecomposition P T τ)
    (hσ : ∀ u, (τ u).toHypergraph = σ u)
    (hpieces : ∀ u (Q : PartialPatchwork Ω α β),
      IsPiece (toPartialPatchwork P) S σ u Q → Q ∈ 𝒞)
    (t : ι) :
    let 𝒞_t : Set (PartialPatchwork Ω α β) :=
      {Q | ∃ y ∈ T.children t,
        PatchworkEquiv Q (toPartialPatchwork (P.restrict (GM04.cross τ (T.subtreeAt y) y)))}
    toPartialPatchwork (P.restrict (GM04.cross τ (T.subtreeAt t) t)) ∈
      enlargementClass (rootingClosure 𝒞) 𝒞_t := by
  classical
  intro 𝒞_t
  let P_part := toPartialPatchwork P
  have hP_part_total : P_part.IsTotal := fun e _ ↦ WithBot.coe_ne_bot
  have htv : t ∈ T.verts := hT_verts ▸ Finset.mem_univ t
  let B_H := GM04.cross τ (T.subtreeAt t) t
  have hle_B : B_H.toHypergraph ≤ P.G.toHypergraph :=
    hdec.isTreeDecomposition.cross_le (T.subtreeAt_subset_verts t) (T.self_mem_subtreeAt htv)
  let B := P_part.restrict B_H
  let ℒ : Set (RootedHypergraph α β) :=
    {A | ∃ y ∈ T.children t, A = GM04.cross τ (T.subtreeAt y) y}
  have hB_restrict_mem : ∀ A ∈ ℒ, B.restrict A ∈ 𝒞_t := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hye, hpar_y⟩ := T.mem_children_iff.1 hy
    exact ⟨y, hy, Patchwork.restrict_restrict_equiv hle_B
      (cross_child_le_cross_parent hdec.isTreeDecomposition htv hye hpar_y)⟩
  by_cases ht_edge : t ∈ T.edges
  · -- Case 2: `t ∈ T.edges` (`t ≠ T.root`).
    let G₀ := rootedDecompRootSide hdec.isTreeDecomposition ht_edge
    let ℒ_star : Set (RootedHypergraph α β) := insert G₀ ℒ
    obtain ⟨hℒ_B, hℒ_star, hcore_eq⟩ := theorem_6_5_3 hrootless hdec ht_edge
    -- Show `G₀ ∉ ℒ` using `hprop : IsProper P.G.toHypergraph S σ`.
    have hG₀_notMem_ℒ : G₀ ∉ ℒ := by
      rintro ⟨y, hy, hEq⟩
      obtain ⟨hye, hpar_y⟩ := T.mem_children_iff.1 hy
      have hclaim3 := (lemma_6_5_claim_3 hrootless hdec ht_edge hye hpar_y).2
      change G₀.toHypergraph ≤ _ at hclaim3
      rw [hEq, (theorem_6_5_1 hdec hye).choose_spec] at hclaim3
      have hsep_y := (hdec.isTreeDecomposition.isSeparation_edge hye).isSeparation
      have hunion_eq : (GM04.cross τ (T.rootSide y) T.root).toHypergraph = P.G.toHypergraph := by
        refine (GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hsep_y.right_le
          (GM10.union_le hsep_y.left_le hsep_y.right_le)
          (Set.union_eq_right.mpr hclaim3.vertexSet_subset).symm
          (Set.union_eq_right.mpr hclaim3.edgeSet_subset).symm).trans hsep_y.union_eq
      have ⟨hsub_y, hroot_y⟩ :=
        cross_subtreeAt_and_rootSide_eq_treeDecompSide hdec.isTreeDecomposition hT_verts hT_S hσ hye
      have hadj_y : S.Adj y (T.parent y) := by
        rw [← hT_S]; exact Or.inl ⟨hye, rfl⟩
      have hmakes_y : GM10.MakesSeparation S σ s(y, T.parent y)
          (GM04.cross τ (T.subtreeAt y) y).toHypergraph
          (GM04.cross τ (T.rootSide y) T.root).toHypergraph :=
        ⟨y, T.parent y, hadj_y, rfl, hsub_y, hroot_y⟩
      exact (hprop (S.mem_edgeSet.2 hadj_y) hmakes_y) hunion_eq
    -- Choose a fresh heart `Q_star` of `(P_part, ℒ_star)`.
    obtain ⟨newEdge, Q_star, hQ_star, _⟩ := exists_fresh_isPlaceHeart P_part hℒ_star
    -- `Q_star` is a piece of `P_part` at `t` under `(S, σ)`, hence `Q_star ∈ 𝒞`.
    have hloc_eq : rootedLocationToLocation P_part.G ℒ_star = vertexLocation S σ t :=
      (vertexLocation_eq_children_or_parent hrootless hdec hT_verts hT_S hσ t).1 ht_edge
    have hQ_star_piece : IsPiece P_part S σ t Q_star :=
      ⟨ℒ_star, ⟨hP_part_total, hℒ_star⟩, hloc_eq, ⟨newEdge, hQ_star⟩⟩
    have hQ_star_mem : Q_star ∈ 𝒞 := hpieces t Q_star hQ_star_piece
    -- Define `Q_mk = mkPlaceHeart B hℒ_B newEdge hinj_B hnotMem_B`, `G_Q = Q_mk.G`, and `Q =
    -- Q_star.restrict G_Q`.
    let e₀ := newEdge G₀
    have he₀_dom : e₀ ∈ Q_star.dom := by
      rw [hQ_star.dom_eq]
      exact Or.inr ⟨G₀, Or.inl rfl, rfl⟩
    have he₀_φ : Q_star.φ e₀ = ⊥ := hQ_star.φ_newEdge (Or.inl rfl)
    have hQ_star_rootless : IsRootless Q_star := by
      change Q_star.G.rootSet = ∅
      rw [RootedHypergraph.rootSet, hQ_star.roots_eq]
      exact hrootless
    have hinj_B : Set.InjOn newEdge ℒ := hQ_star.injOn_newEdge.mono (Set.subset_insert G₀ ℒ)
    have hnotMem_B : ∀ ⦃A⦄, A ∈ ℒ → newEdge A ∉ (rootedLocationCore B.G ℒ).edgeSet := by
      intro A hA
      rw [show B.G = B_H from rfl, hcore_eq]
      exact hQ_star.newEdge_notMem_core (Or.inr hA)
    have hQ_mk := isPlaceHeart_mkPlaceHeart B hℒ_B newEdge hinj_B hnotMem_B
    let G_Q := (mkPlaceHeart B hℒ_B newEdge hinj_B hnotMem_B).G
    have hG_Q_V : G_Q.vertexSet = Q_star.G.vertexSet := by
      change (mkPlaceHeart B hℒ_B newEdge hinj_B hnotMem_B).G.vertexSet = Q_star.G.vertexSet
      rw [hQ_mk.vertexSet_eq, hQ_star.vertexSet_eq]
      exact congrArg Hypergraph.vertexSet hcore_eq
    have hG_Q_E : G_Q.edgeSet = Q_star.G.edgeSet \ {e₀} := by
      change (mkPlaceHeart B hℒ_B newEdge hinj_B hnotMem_B).G.edgeSet =
        Q_star.G.edgeSet \ {newEdge G₀}
      rw [hQ_mk.edgeSet_eq, hQ_star.edgeSet_eq, show B.G = B_H from rfl, hcore_eq]
      ext e
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_image, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro (hc | ⟨A, hA, rfl⟩)
        · refine ⟨Or.inl hc, fun hEq ↦ ?_⟩
          rw [hEq] at hc
          exact hQ_star.newEdge_notMem_core (Or.inl rfl) hc
        · refine ⟨Or.inr ⟨A, Or.inr hA, rfl⟩, fun hEq ↦ ?_⟩
          have hAG₀ : A = G₀ := hQ_star.injOn_newEdge (Or.inr hA) (Or.inl rfl) hEq
          rw [hAG₀] at hA
          exact hG₀_notMem_ℒ hA
      · rintro ⟨hc | ⟨A, rfl | hA, rfl⟩, hne_e₀⟩
        · exact Or.inl hc
        · exact (hne_e₀ rfl).elim
        · exact Or.inr ⟨A, hA, rfl⟩
    have hG_Q_ends : ∀ e ∈ G_Q.edgeSet, G_Q.ends e = Q_star.G.ends e := by
      intro e he
      change e ∈ (mkPlaceHeart B hℒ_B newEdge hinj_B hnotMem_B).G.edgeSet at he
      rw [hQ_mk.edgeSet_eq, show B.G = B_H from rfl] at he
      rcases he with hc | ⟨A, hA, rfl⟩
      · have hc_star : e ∈ (rootedLocationCore P_part.G ℒ_star).edgeSet := hcore_eq ▸ hc
        rw [hQ_mk.ends_core hc, hQ_star.ends_core hc_star]
        have he_B : e ∈ B_H.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 hc).1
        exact (hle_B.ends_eq e he_B).symm
      · rw [hQ_mk.ends_newEdge hA, hQ_star.ends_newEdge (Or.inr hA)]
    have hG_Q_le : G_Q.toHypergraph ≤ Q_star.G.toHypergraph :=
      { vertexSet_subset := hG_Q_V.le
        edgeSet_subset := hG_Q_E.le.trans Set.sdiff_subset
        ends_eq := fun e he ↦ (hG_Q_ends e he).symm }
    have hdel_le : Q_star.G.toHypergraph.deleteEdges {e₀} ≤ Q_star.G.toHypergraph :=
      { vertexSet_subset := le_rfl
        edgeSet_subset := Set.sdiff_subset
        ends_eq := fun e he ↦ Set.ext fun v ↦ ⟨fun h ↦ ⟨h, he.2⟩, fun h ↦ h.1⟩ }
    have hG_Q_del : G_Q.toHypergraph = Q_star.G.toHypergraph.deleteEdges {e₀} :=
      GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hG_Q_le hdel_le hG_Q_V hG_Q_E
    have hG_Q_roots : G_Q.roots = Q_star.μ e₀ := by
      change (mkPlaceHeart B hℒ_B newEdge hinj_B hnotMem_B).G.roots = Q_star.μ e₀
      rw [hQ_mk.roots_eq, hQ_star.μ_newEdge (Or.inl rfl)]
      rfl
    let Q := Q_star.restrict G_Q
    have hQ_rooting : IsRooting Q_star Q :=
      ⟨hQ_star_rootless, e₀, he₀_dom, he₀_φ, hG_Q_le, hG_Q_del, hG_Q_roots, rfl⟩
    have hQ_mem : Q ∈ rootingClosure 𝒞 := Or.inr ⟨Q_star, hQ_star_mem, hQ_rooting⟩
    -- Now verify `IsPlaceHeart B ℒ newEdge Q`.
    have hQ_heart : IsPlaceHeart B ℒ newEdge Q :=
      { isRootedLocation := hℒ_B
        injOn_newEdge := hinj_B
        newEdge_notMem_core := hnotMem_B
        vertexSet_eq := rfl
        edgeSet_eq := rfl
        roots_eq := rfl
        ends_core := hQ_mk.ends_core
        ends_newEdge := hQ_mk.ends_newEdge
        dom_eq := by
          change Q.dom = (rootedLocationCore B.G ℒ).edgeSet ∩ (P_part.restrict B_H).dom ∪ newEdge
            '' ℒ
          rw [Q_star.restrict_dom hG_Q_le, hQ_star.dom_eq, hG_Q_E, hQ_star.edgeSet_eq,
            show B.G = B_H from rfl, hcore_eq, P_part.restrict_dom hle_B]
          ext e
          simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_image, Set.mem_insert_iff,
            Set.mem_sdiff, Set.mem_singleton_iff, e₀]
          constructor
          · rintro ⟨⟨hc, hd⟩ | ⟨A, rfl | hA, rfl⟩, _, hne_e₀⟩
            · have he_B : e ∈ B_H.edgeSet :=
                (mem_rootedLocationCore_edgeSet_iff.1 (hcore_eq.symm ▸ hc)).1
              exact Or.inl ⟨hc, hd, he_B⟩
            · exact (hne_e₀ rfl).elim
            · exact Or.inr ⟨A, hA, rfl⟩
          · rintro (⟨hc, hd, _⟩ | ⟨A, hA, rfl⟩)
            · refine ⟨Or.inl ⟨hc, hd⟩, Or.inl hc, fun hEq ↦ ?_⟩
              rw [hEq] at hc
              exact hQ_star.newEdge_notMem_core (Or.inl rfl) hc
            · refine ⟨Or.inr ⟨A, Or.inr hA, rfl⟩, Or.inr ⟨A, Or.inr hA, rfl⟩, fun hEq ↦ ?_⟩
              have hAG₀ : A = G₀ := hQ_star.injOn_newEdge (Or.inr hA) (Or.inl rfl) hEq
              rw [hAG₀] at hA
              exact hG₀_notMem_ℒ hA
        μ_core := fun f hf ↦ by
          change f ∈ (rootedLocationCore B.G ℒ).edgeSet ∩ (P_part.restrict B_H).dom at hf
          have hf_star : f ∈ (rootedLocationCore P_part.G ℒ_star).edgeSet ∩ P_part.dom := by
            rw [show B.G = B_H from rfl, hcore_eq, P_part.restrict_dom hle_B] at hf
            exact ⟨hf.1, hf.2.1⟩
          exact hQ_star.μ_core hf_star
        μ_newEdge := fun A hA ↦ hQ_star.μ_newEdge (Or.inr hA)
        Δ_core := fun f hf ↦ by
          have hf_G_Q : f ∈ G_Q.edgeSet := Or.inl hf
          have hf_star : f ∈ (rootedLocationCore P_part.G ℒ_star).edgeSet :=
            hcore_eq ▸ hf
          have hf_B : f ∈ B_H.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 hf).1
          change Q.Δ f = (P_part.restrict B_H).Δ f
          rw [Q_star.restrict_Δ hG_Q_le hf_G_Q, hQ_star.Δ_core hf_star,
            P_part.restrict_Δ hle_B hf_B]
        Δ_newEdge := fun A hA ↦ by
          have hA_G_Q : newEdge A ∈ G_Q.edgeSet := Or.inr ⟨A, hA, rfl⟩
          have hle_A_B : A.toHypergraph ≤ B_H.toHypergraph := (hℒ_B.isComplemented hA).le
          rw [Q_star.restrict_Δ hG_Q_le hA_G_Q, hQ_star.Δ_newEdge (Or.inr hA)]
          exact (Patchwork.restrict_restrict_equiv hle_B hle_A_B).symm.feasibleGroupings_eq
        φ_core := fun f hf ↦ by
          have hf_star : f ∈ (rootedLocationCore P_part.G ℒ_star).edgeSet := hcore_eq ▸ hf
          exact hQ_star.φ_core hf_star
        φ_newEdge := fun A hA ↦ hQ_star.φ_newEdge (Or.inr hA) }
    exact ⟨Q, hQ_mem, ℒ, hℒ_B, ⟨newEdge, hQ_heart⟩, hB_restrict_mem⟩
  · -- Case 1: `t ∉ T.edges`, so `t = T.root` and `B_H = P.G`.
    have ht_root : t = T.root := by
      by_contra hne
      exact ht_edge (T.mem_edges_iff.2 ⟨htv, hne⟩)
    subst ht_root
    have hB_H_eq : B_H = P.G := by
      dsimp only [B_H]
      rw [GM04.cross_subtreeAt_root, hdec.isTreeDecomposition.cross_verts_eq]
    obtain ⟨hℒ_B, _⟩ := isRootedLocation_children hdec.isTreeDecomposition htv
    have hℒ_P : IsRootedLocation P_part.G ℒ := by
      change IsRootedLocation P.G ℒ
      rw [← hB_H_eq]
      exact hℒ_B
    obtain ⟨newEdge, Q, hQ, _⟩ := exists_fresh_isPlaceHeart P_part hℒ_P
    have hloc_eq : rootedLocationToLocation P_part.G ℒ = vertexLocation S σ T.root :=
      (vertexLocation_eq_children_or_parent hrootless hdec hT_verts hT_S hσ T.root).2 ht_edge
    have hQ_piece : IsPiece P_part S σ T.root Q :=
      ⟨ℒ, ⟨hP_part_total, hℒ_P⟩, hloc_eq, ⟨newEdge, hQ⟩⟩
    have hQ_mem : Q ∈ rootingClosure 𝒞 := Or.inl (hpieces T.root Q hQ_piece)
    have hB_equiv : PatchworkEquiv P_part B := by
      change PatchworkEquiv P_part (P_part.restrict B_H)
      rw [hB_H_eq]
      exact (patchworkEquiv_restrict_self P_part).symm
    exact ⟨Q, hQ_mem, ℒ, hℒ_B, ⟨newEdge, hQ.congr_left hB_equiv⟩, hB_restrict_mem⟩

/-! ## Claim (2) of (6.6) and proof of Theorem (6.6) -/

/-- A class `W : Set (GM04.Patchwork Ω α β)` of total `Ω`-patchworks (where `Ω` is
well-quasi-ordered)
is well-quasi-ordered by `GM04.Simulated` if and only if its image `toPartialPatchwork '' W` is
well-behaved. -/
theorem wellBehaved_image_toPartialPatchwork_iff [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω)
    (W : Set (GM04.Patchwork Ω α β)) :
    WellBehaved (toPartialPatchwork '' W) ↔
      ∀ x : ℕ → GM04.Patchwork Ω α β, (∀ n, x n ∈ W) →
        ∃ i j, i < j ∧ GM04.Simulated (x i) (x j) := by
  classical
  constructor
  · intro hWB x hx
    let UnitType := PUnit.{max w (max u v) + 1}
    have hUnit_wqo : WellQuasiOrderedLE UnitType := Finite.to_wellQuasiOrderedLE
    let Ω' : Type (max w (max u v)) := DisjointUnionQuasiOrder Ω UnitType
    have hΩ'_wqo : WellQuasiOrderedLE Ω' := wellQuasiOrderedLE_disjointUnion hΩ hUnit_wqo
    let ι : Ω ↪o Ω' := DisjointUnionQuasiOrder.inlEmb Ω UnitType
    let Q : ℕ → GM04.Patchwork Ω' α β := fun n ↦
      { G := (x n).G
        dom := (x n).dom
        μ := (x n).μ
        Δ := (x n).Δ
        φ := fun e ↦ Sum.inl ((x n).φ e)
        dom_subset := (x n).dom_subset
        μ_nodup := (x n).μ_nodup
        μ_set := (x n).μ_set
        Δ_verts := (x n).Δ_verts
        Δ_free := (x n).Δ_free }
    have hQ_comp : ∀ n, ∃ P ∈ toPartialPatchwork '' W, IsCompletion ι P (Q n) := by
      intro n
      refine ⟨toPartialPatchwork (x n), ⟨x n, hx n, rfl⟩,
        ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, ?_⟩⟩
      intro e _ ω hφ
      change Sum.inl ((x n).φ e) = Sum.inl ω
      exact congrArg Sum.inl (WithBot.coe_inj.1 hφ)
    obtain ⟨i, j, hij, ηv, ηe, hexp, hreal⟩ := hWB Ω' ι hΩ'_wqo Q hQ_comp
    refine ⟨i, j, hij, ηv, ηe, ?_, hreal⟩
    refine
      { vertex_nonempty := hexp.vertex_nonempty
        vertex_subset := hexp.vertex_subset
        edge_mem := hexp.edge_mem
        vertex_disjoint := hexp.vertex_disjoint
        edge_injOn := hexp.edge_injOn
        mem_dom_iff := hexp.mem_dom_iff
        ends_nonempty := hexp.ends_nonempty
        μ_length := hexp.μ_length
        μ_mem := hexp.μ_mem
        roots_length := hexp.roots_length
        roots_mem := hexp.roots_mem
        maps_Δ := hexp.maps_Δ
        φ_le := fun e he ↦ (ι.map_rel_iff).1 (hexp.φ_le e he) }
  · intro hwqo Ω' _ ι _ Q hQ
    choose P hP_mem hcomp using hQ
    choose R hR_W hR_eq using hP_mem
    obtain ⟨i, j, hij, ηv, ηe, hexp, H, ⟨δ, hδ, hH⟩, hcomp_H⟩ := hwqo R hR_W
    have hG_i : (Q i).G = (R i).G := (hcomp i).G_eq.trans (congrArg GM04.Patchwork.G (hR_eq i).symm)
    have hG_j : (Q j).G = (R j).G := (hcomp j).G_eq.trans (congrArg GM04.Patchwork.G (hR_eq j).symm)
    have hdom_i : (Q i).dom = (R i).dom :=
      (hcomp i).dom_eq.trans (congrArg GM04.Patchwork.dom (hR_eq i).symm)
    have hdom_j : (Q j).dom = (R j).dom :=
      (hcomp j).dom_eq.trans (congrArg GM04.Patchwork.dom (hR_eq j).symm)
    have hμ_i : ∀ e ∈ (R i).dom, (Q i).μ e = (R i).μ e := fun e he ↦ by
      have h := (hcomp i).μ_eq (by rw [← hR_eq i]; exact he)
      rw [← hR_eq i] at h
      exact h
    have hμ_j : ∀ e ∈ (R j).dom, (Q j).μ e = (R j).μ e := fun e he ↦ by
      have h := (hcomp j).μ_eq (by rw [← hR_eq j]; exact he)
      rw [← hR_eq j] at h
      exact h
    have hΔ_i : ∀ e ∈ (R i).G.edgeSet, (Q i).Δ e = (R i).Δ e := fun e he ↦ by
      have h := (hcomp i).Δ_eq (by rw [← hR_eq i]; exact he)
      rw [← hR_eq i] at h
      exact h
    have hΔ_j : ∀ e ∈ (R j).G.edgeSet, (Q j).Δ e = (R j).Δ e := fun e he ↦ by
      have h := (hcomp j).Δ_eq (by rw [← hR_eq j]; exact he)
      rw [← hR_eq j] at h
      exact h
    have hφ_i : ∀ e ∈ (R i).G.edgeSet, (Q i).φ e = ι ((R i).φ e) := fun e he ↦
      (hcomp i).φ_eq (by rw [← hR_eq i]; exact he) (by rw [← hR_eq i]; rfl)
    have hφ_j : ∀ e ∈ (R j).G.edgeSet, (Q j).φ e = ι ((R j).φ e) := fun e he ↦
      (hcomp j).φ_eq (by rw [← hR_eq j]; exact he) (by rw [← hR_eq j]; rfl)
    refine ⟨i, j, hij, ηv, ηe, ?_, H, ⟨⟨δ, fun e he ↦ ?_, ?_⟩, fun v hv ↦ hcomp_H v (hG_i ▸ hv)⟩⟩
    · refine
        { vertex_nonempty := fun v hv ↦ hexp.vertex_nonempty v (hG_i ▸ hv)
          vertex_subset := fun v hv ↦ hG_j.symm ▸ hexp.vertex_subset v (hG_i ▸ hv)
          edge_mem := fun e he ↦ hG_j.symm ▸ hexp.edge_mem e (hG_i ▸ he)
          vertex_disjoint := fun v₁ hv₁ v₂ hv₂ hne ↦
            hexp.vertex_disjoint v₁ (hG_i ▸ hv₁) v₂ (hG_i ▸ hv₂) hne
          edge_injOn := hG_i.symm ▸ hexp.edge_injOn
          mem_dom_iff := fun e he ↦ by
            rw [hdom_i, hdom_j]
            exact hexp.mem_dom_iff e (hG_i ▸ he)
          ends_nonempty := fun e he hnd v hinc ↦ by
            have he' : e ∈ (R i).G.edgeSet := hG_i ▸ he
            have hnd' : e ∉ (R i).dom := hdom_i ▸ hnd
            have hinc' : (R i).G.Inc e v := hG_i ▸ hinc
            obtain ⟨v', hv', hinc_j⟩ := hexp.ends_nonempty e he' hnd' v hinc'
            exact ⟨v', hv', hG_j.symm ▸ hinc_j⟩
          μ_length := fun e he ↦ by
            have he' : e ∈ (R i).dom := hdom_i ▸ he
            have heE' : e ∈ (R i).G.edgeSet := (R i).dom_subset he'
            have hηe' : ηe e ∈ (R j).dom := (hexp.mem_dom_iff e heE').1 he'
            rw [hμ_i e he', hμ_j (ηe e) hηe']
            exact hexp.μ_length e he'
          μ_mem := fun e he k hk hk' ↦ by
            have he' : e ∈ (R i).dom := hdom_i ▸ he
            have heE' : e ∈ (R i).G.edgeSet := (R i).dom_subset he'
            have hηe' : ηe e ∈ (R j).dom := (hexp.mem_dom_iff e heE').1 he'
            have hk₁ : k < ((R i).μ e).length := (hμ_i e he') ▸ hk
            have hk₂ : k < ((R j).μ (ηe e)).length := (hμ_j (ηe e) hηe') ▸ hk'
            have hmem := hexp.μ_mem e he' k hk₁ hk₂
            simpa [hμ_i e he', hμ_j (ηe e) hηe'] using hmem
          roots_length := by
            rw [hG_i, hG_j]
            exact hexp.roots_length
          roots_mem := fun k hk hk' ↦ by
            have hk₁ : k < (R i).G.roots.length := hG_i ▸ hk
            have hk₂ : k < (R j).G.roots.length := hG_j ▸ hk'
            have hmem := hexp.roots_mem k hk₁ hk₂
            simpa [hG_i, hG_j] using hmem
          maps_Δ := fun e he ↦ by
            have he' : e ∈ (R i).dom := hdom_i ▸ he
            have heE' : e ∈ (R i).G.edgeSet := (R i).dom_subset he'
            have hηe' : ηe e ∈ (R j).dom := (hexp.mem_dom_iff e heE').1 he'
            have hηeE' : ηe e ∈ (R j).G.edgeSet := hexp.edge_mem e heE'
            rw [hμ_i e he', hμ_j (ηe e) hηe', hΔ_i e heE', hΔ_j (ηe e) hηeE']
            exact hexp.maps_Δ e he'
          φ_le := fun e he ↦ by
            have heE' : e ∈ (R i).G.edgeSet := hG_i ▸ he
            have hηeE' : ηe e ∈ (R j).G.edgeSet := hexp.edge_mem e heE'
            rw [hφ_i e heE', hφ_j (ηe e) hηeE']
            exact ι.monotone (hexp.φ_le e heE') }
    · have he_R : e ∈ ((R j).deleteEdges (ηe '' (R i).G.edgeSet)).G.edgeSet := by
        simpa [GM04.Patchwork.deleteEdges, RootedHypergraph.deleteEdges, Hypergraph.deleteEdges,
          hG_i, hG_j] using he
      change δ e ∈ (Q j).Δ e
      rw [hΔ_j e he_R.1]
      exact hδ e he_R
    · simpa [GM04.Patchwork.deleteEdges, RootedHypergraph.deleteEdges, Hypergraph.deleteEdges,
        hG_i, hG_j] using hH

/-- Disjoint copy of `T i` in `Σ k : ℕ, ι k` with first coordinate `i`. -/
noncomputable def sigmaTree {ι : ℕ → Type*} (T : ∀ i : ℕ, GM04.RootedTree (ι i)) (i : ℕ) :
    GM04.RootedTree (Σ k : ℕ, ι k) where
  verts := (T i).verts.map ⟨Sigma.mk i, sigma_mk_injective⟩
  root := ⟨i, (T i).root⟩
  parent p := ⟨p.1, (T p.1).parent p.2⟩
  root_mem := Finset.mem_map_of_mem _ (T i).root_mem
  parent_mem p hp := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hp
    exact Finset.mem_map_of_mem _ ((T i).parent_mem v hv)
  parent_root := Sigma.ext rfl (heq_of_eq (T i).parent_root)
  exists_iterate_eq_root p hp := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨n, hn⟩ := (T i).exists_iterate_eq_root v hv
    refine ⟨n, ?_⟩
    have hiter : ∀ (m : ℕ) (w : ι i),
        ((fun q : Σ k : ℕ, ι k ↦ (⟨q.1, (T q.1).parent q.2⟩ : Σ k : ℕ, ι k))^[m] ⟨i, w⟩) =
          ⟨i, (T i).parent^[m] w⟩ := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro w
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    change (fun q : Σ k : ℕ, ι k ↦ (⟨q.1, (T q.1).parent q.2⟩ : Σ k : ℕ, ι k))^[n] ⟨i, v⟩ =
      ⟨i, (T i).root⟩
    rw [hiter, hn]

theorem sigmaTree_verts {ι : ℕ → Type*} (T : ∀ i : ℕ, GM04.RootedTree (ι i)) (i : ℕ) :
    (sigmaTree T i).verts = (T i).verts.map ⟨Sigma.mk i, sigma_mk_injective⟩ := by
  rfl

theorem sigmaTree_root {ι : ℕ → Type*} (T : ∀ i : ℕ, GM04.RootedTree (ι i)) (i : ℕ) :
    (sigmaTree T i).root = ⟨i, (T i).root⟩ := by
  rfl

theorem sigmaTree_parent_mk {ι : ℕ → Type*} (T : ∀ i : ℕ, GM04.RootedTree (ι i)) (i : ℕ)
    (t : ι i) : (sigmaTree T i).parent ⟨i, t⟩ = ⟨i, (T i).parent t⟩ := by
  rfl

theorem sigmaTree_parent_iterate {ι : ℕ → Type*} (T : ∀ i : ℕ, GM04.RootedTree (ι i))
    (m : ℕ) (p : Σ k : ℕ, ι k) :
    ((fun q : Σ k : ℕ, ι k ↦ (⟨q.1, (T q.1).parent q.2⟩ : Σ k : ℕ, ι k))^[m] p) =
      ⟨p.1, (T p.1).parent^[m] p.2⟩ := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]

@[simp]
theorem mem_sigmaTree_verts {ι : ℕ → Type*} (T : ∀ i : ℕ, GM04.RootedTree (ι i))
    (i : ℕ) (p : Σ k : ℕ, ι k) :
    p ∈ (sigmaTree T i).verts ↔ ∃ (h : p.1 = i), h ▸ p.2 ∈ (T i).verts := by
  rcases p with ⟨j, v⟩
  simp only [sigmaTree, Finset.mem_map, Function.Embedding.coeFn_mk, Sigma.mk.inj_iff]
  constructor
  · rintro ⟨w, hw, rfl, hEq⟩
    cases hEq
    exact ⟨rfl, hw⟩
  · rintro ⟨rfl, hv⟩
    exact ⟨v, hv, rfl, HEq.rfl⟩

theorem mem_sigmaTree_verts_mk {ι : ℕ → Type*} (T : ∀ i : ℕ, GM04.RootedTree (ι i))
    (i : ℕ) (v : ι i) :
    (⟨i, v⟩ : Σ k : ℕ, ι k) ∈ (sigmaTree T i).verts ↔ v ∈ (T i).verts := by
  rw [mem_sigmaTree_verts]
  exact ⟨fun ⟨_, hv⟩ ↦ hv, fun hv ↦ ⟨rfl, hv⟩⟩

theorem mem_sigmaTree_edges_mk {ι : ℕ → Type*} (T : ∀ i : ℕ, GM04.RootedTree (ι i))
    (i : ℕ) (v : ι i) :
    (⟨i, v⟩ : Σ k : ℕ, ι k) ∈ (sigmaTree T i).edges ↔ v ∈ (T i).edges := by
  rw [GM04.RootedTree.mem_edges_iff, mem_sigmaTree_verts_mk, GM04.RootedTree.mem_edges_iff]
  simp only [sigmaTree, ne_eq, Sigma.mk.inj_iff, true_and, heq_eq_eq]

theorem sigmaTree_reaches_mk_iff {ι : ℕ → Type*} (T : ∀ i : ℕ, GM04.RootedTree (ι i))
    (i : ℕ) (u v : ι i) :
    (sigmaTree T i).Reaches ⟨i, u⟩ ⟨i, v⟩ ↔ (T i).Reaches u v := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hv, n, hn⟩
    rw [mem_sigmaTree_verts_mk] at hv
    change (fun q : Σ k : ℕ, ι k ↦ (⟨q.1, (T q.1).parent q.2⟩ : Σ k : ℕ, ι k))^[n] ⟨i, v⟩
      = ⟨i, u⟩ at hn
    rw [sigmaTree_parent_iterate, Sigma.mk.inj_iff, heq_eq_eq] at hn
    exact ⟨hv, n, hn.2⟩
  · rintro ⟨hv, n, hn⟩
    refine ⟨(mem_sigmaTree_verts_mk T i v).2 hv, n, ?_⟩
    change (fun q : Σ k : ℕ, ι k ↦ (⟨q.1, (T q.1).parent q.2⟩ : Σ k : ℕ, ι k))^[n] ⟨i, v⟩ = ⟨i, u⟩
    rw [sigmaTree_parent_iterate, hn]

theorem sigmaTree_precedes_mk_iff {ι : ℕ → Type*} (T : ∀ i : ℕ, GM04.RootedTree (ι i))
    (φ : ∀ i, ι i → ℕ) (i : ℕ) (v w : ι i) :
    (sigmaTree T i).Precedes (fun p ↦ φ p.1 p.2) ⟨i, v⟩ ⟨i, w⟩ ↔
      (T i).Precedes (φ i) v w := by
  simp only [GM04.RootedTree.Precedes, sigmaTree_reaches_mk_iff]
  refine and_congr ?_ (and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩)
  · simp [sigmaTree]
  · intro h g hgv hvg hgw
    exact h ⟨i, g⟩ (fun hEq ↦ hgv (sigma_mk_injective hEq))
      ((sigmaTree_reaches_mk_iff T i v g).2 hvg)
      ((sigmaTree_reaches_mk_iff T i g w).2 hgw)
  · intro h ⟨j, g⟩ hjg hvg hgw
    have hj : j = i := ((mem_sigmaTree_verts T i ⟨j, g⟩).1 hvg.1).1
    subst hj
    rw [sigmaTree_reaches_mk_iff] at hvg hgw
    exact h g (fun hEq ↦ hjg (congrArg (Sigma.mk j) hEq)) hvg hgw

/-- For `p : Σ k : ℕ, ι k`, the subtree patchwork `(P p.1).restrict (GM04.cross (τ p.1) ((T
p.1).subtreeAt p.2) p.2)`. -/
noncomputable def sigmaSubtreePatchwork {ι : ℕ → Type*} (P : ℕ → GM04.Patchwork Ω α β)
    (T : ∀ i : ℕ, GM04.RootedTree (ι i)) (τ : ∀ i : ℕ, ι i → RootedHypergraph α β)
    (p : Σ k : ℕ, ι k) : GM04.Patchwork Ω α β :=
  (P p.1).restrict (GM04.cross (τ p.1) ((T p.1).subtreeAt p.2) p.2)

/-- The set of out-neighbours in `⋃_i T_i` of vertices in `X : Set (Σ k : ℕ, ι k)`
(Graph Minors XVIII, proof of (6.6), Claim (2), page 105). -/
def sigmaOutNeighbours {ι : ℕ → Type*} (T : ∀ i : ℕ, GM04.RootedTree (ι i))
    (X : Set (Σ k : ℕ, ι k)) : Set (Σ k : ℕ, ι k) :=
  {y | ∃ i, y ∈ (sigmaTree T i).edges ∧ (sigmaTree T i).parent y ∈ X}

theorem sigmaSubtreePatchwork_mk {ι : ℕ → Type*} (P : ℕ → GM04.Patchwork Ω α β)
    (T : ∀ i : ℕ, GM04.RootedTree (ι i)) (τ : ∀ i : ℕ, ι i → RootedHypergraph α β) (i : ℕ)
    (t : ι i) :
    sigmaSubtreePatchwork P T τ ⟨i, t⟩ = (P i).restrict (GM04.cross (τ i) ((T i).subtreeAt t) t)
      := by
  rfl

theorem mem_sigmaOutNeighbours {ι : ℕ → Type*} (T : ∀ i : ℕ, GM04.RootedTree (ι i))
    (X : Set (Σ k : ℕ, ι k)) (y : Σ k : ℕ, ι k) :
    y ∈ sigmaOutNeighbours T X ↔ ∃ i, y ∈ (sigmaTree T i).edges ∧ (sigmaTree T i).parent y ∈ X :=
  Iff.rfl

/-- **Claim (2)** in the proof of Graph Minors XVIII, (6.6) (page 105):
"(2) *If $X \subseteq V(M)$ and $B(N(X))$ is well-quasi-ordered by simulation, then so is
$B(X)$.*" -/
theorem lemma_6_6_claim_2 [Infinite β] [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω)
    {ι : ℕ → Type*} [∀ i, Fintype (ι i)]
    {𝒞 : Set (PartialPatchwork Ω α β)} (h𝒞 : WellBehaved 𝒞)
    {P : ℕ → GM04.Patchwork Ω α β} (hrootless : ∀ i, IsRootless (P i))
    {S : ∀ i, SimpleGraph (ι i)} {σ : ∀ i, ι i → Hypergraph α β}
    (hprop : ∀ i, IsProper (P i).G.toHypergraph (S i) (σ i))
    {T : ∀ i, GM04.RootedTree (ι i)} (hT_verts : ∀ i, (T i).verts = Finset.univ)
    (hT_S : ∀ i, arborescenceUnderlying (T i) = S i)
    {τ : ∀ i, ι i → RootedHypergraph α β}
    (hdec : ∀ i, IsRootedDecomposition (P i) (T i) (τ i))
    (hσ : ∀ i u, (τ i u).toHypergraph = σ i u)
    (hpieces : ∀ i u (Q : PartialPatchwork Ω α β),
      IsPiece (toPartialPatchwork (P i)) (S i) (σ i) u Q → Q ∈ 𝒞)
    {X : Set (Σ k : ℕ, ι k)}
    (hY_wqo : ∀ y : ℕ → GM04.Patchwork Ω α β,
      (∀ n, y n ∈ sigmaSubtreePatchwork P T τ '' sigmaOutNeighbours T X) →
      ∃ i j, i < j ∧ GM04.Simulated (y i) (y j)) :
    ∀ x : ℕ → GM04.Patchwork Ω α β,
      (∀ n, x n ∈ sigmaSubtreePatchwork P T τ '' X) →
      ∃ i j, i < j ∧ GM04.Simulated (x i) (x j) := by
  have hY_wb : WellBehaved
      (equivClosure (toPartialPatchwork '' (sigmaSubtreePatchwork P T τ '' sigmaOutNeighbours T
        X))) :=
    wellBehaved_equivClosure ((wellBehaved_image_toPartialPatchwork_iff hΩ _).2 hY_wqo)
  have h_enl_wb : WellBehaved
      (enlargementClass (rootingClosure 𝒞)
        (equivClosure (toPartialPatchwork '' (sigmaSubtreePatchwork P T τ '' sigmaOutNeighbours T
          X)))) :=
    theorem_6_3_proof (wellBehaved_rootingClosure h𝒞) hY_wb
  have hX_sub : toPartialPatchwork '' (sigmaSubtreePatchwork P T τ '' X) ⊆
      enlargementClass (rootingClosure 𝒞)
        (equivClosure (toPartialPatchwork '' (sigmaSubtreePatchwork P T τ '' sigmaOutNeighbours T
          X))) := by
    rintro _ ⟨_, ⟨⟨i, t⟩, hxt, rfl⟩, rfl⟩
    have hclaim1 :=
      lemma_6_6_claim_1 (hrootless i) (hprop i) (hT_verts i) (hT_S i) (hdec i) (hσ i) (hpieces i) t
    obtain ⟨Q, hQ_mem, ℒ, hℒ, hheart, hA_mem⟩ := hclaim1
    refine ⟨Q, hQ_mem, ℒ, hℒ, hheart, fun A hA ↦ ?_⟩
    obtain ⟨y, hy, hEq⟩ := hA_mem A hA
    obtain ⟨hye, hpar_y⟩ := (T i).mem_children_iff.1 hy
    refine ⟨toPartialPatchwork (sigmaSubtreePatchwork P T τ ⟨i, y⟩),
      ⟨sigmaSubtreePatchwork P T τ ⟨i, y⟩, ⟨⟨i, y⟩, ?_, rfl⟩, rfl⟩, hEq⟩
    refine ⟨i, (mem_sigmaTree_edges_mk T i y).2 hye, ?_⟩
    change (⟨i, (T i).parent y⟩ : Σ k : ℕ, ι k) ∈ X
    rwa [hpar_y]
  exact (wellBehaved_image_toPartialPatchwork_iff hΩ _).1 (h_enl_wb.mono hX_sub)

end GraphMinor.GM18
end
