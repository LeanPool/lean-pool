/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10c
public import LeanPool.GraphMinor.GM04.Patchwork.Main
public import LeanPool.GraphMinor.Minor.Basic

/-!
# Directed graphs, directed minors, and directed patchworks for Graph Minors XX, (10.5)

This file formalizes directed graphs, directed minors ("A directed graph is a minor of another if
the first can be obtained from a subgraph of the second by contracting edges.", Graph Minors XX,
Section 10, page 355), and the directed patchwork and minor-model lemmas used in the proof of
`GM20.theorem_10_5_proof`:

* `Digraph`: a directed multigraph consisting of an underlying `Graph α β` (`toGraph`) together with
  `tail` and `head` maps on `E(toGraph)` such that `toGraph.IsLink e.1 (tail e) (head e)` for every
  `e : E(toGraph)`.
* `Digraph.ofSubgraph`, `Digraph.contract`, `Digraph.Iso`, `Digraph.IsIsoMinor`: subgraphs, edge
  contractions, isomorphisms, and the minor relation for directed graphs.
* `IsDirMinorModel` and `isIsoMinor_of_isDirMinorModel`: directed minor models (Graph Minors IV,
  Section 7, pages 242–243, with tail and head preserved) and the construction of a directed minor
  from a model.
* `isDirMinorModel_of_hasCliqueMinor` and `isIsoMinor_of_hasCliqueMinor`: "Let $p = 2|E(G_1)| +
  |V(G_1)|$; then every tournament with $p$ vertices has a minor isomorphic to $G_1$." (Graph Minors
  XX, page 355).
* `digraphPatchwork`, `isFree_digraphPatchwork`, and `isDirMinorModel_of_simulated`: the free
  `Unit`-patchwork of a finite directed graph where `μ(e)` lists the ends of `e` tail first, and the
  deduction of a directed minor model from simulation.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Graph Relation GraphMinor.GM18 GraphMinor.GM04

universe u v u' v' u'' v''

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'} {α'' : Type u''} {β'' : Type v''}

/-! ### Directed graphs, subgraphs, contractions, and minors -/

/-- A directed graph (allowing loops and multiple edges), represented by its underlying undirected
graph `toGraph : Graph α β` together with `tail` and `head` functions assigning to each edge
`e : E(toGraph)` its tail and head. -/
structure Digraph (α : Type u) (β : Type v) where
  /-- The underlying undirected graph $G'$ of $G$. -/
  toGraph : Graph α β
  /-- The tail of each edge of `toGraph`. -/
  tail : E(toGraph) → α
  /-- The head of each edge of `toGraph`. -/
  head : E(toGraph) → α
  /-- Every edge `e : E(toGraph)` links `tail e` and `head e` in `toGraph`. -/
  isLink_of_mem : ∀ e : E(toGraph), toGraph.IsLink e.1 (tail e) (head e)

namespace Digraph

theorem tail_mem (G : Digraph α β) (e : E(G.toGraph)) : G.tail e ∈ V(G.toGraph) :=
  (G.isLink_of_mem e).left_mem

theorem head_mem (G : Digraph α β) (e : E(G.toGraph)) : G.head e ∈ V(G.toGraph) :=
  (G.isLink_of_mem e).right_mem

theorem inc_tail (G : Digraph α β) (e : E(G.toGraph)) : G.toGraph.Inc e.1 (G.tail e) :=
  (G.isLink_of_mem e).inc_left

theorem inc_head (G : Digraph α β) (e : E(G.toGraph)) : G.toGraph.Inc e.1 (G.head e) :=
  (G.isLink_of_mem e).inc_right

/-- A subgraph `H ≤ G.toGraph` of the underlying undirected graph inherits the edge orientations of
`G` to form a directed subgraph of `G`. -/
def ofSubgraph (G : Digraph α β) (H : Graph α β) (hH : H ≤ G.toGraph) : Digraph α β where
  toGraph := H
  tail e := G.tail ⟨e.1, hH.edgeSet_mono e.2⟩
  head e := G.head ⟨e.1, hH.edgeSet_mono e.2⟩
  isLink_of_mem e := (hH.isLink_iff e.2).2 (G.isLink_of_mem ⟨e.1, hH.edgeSet_mono e.2⟩)

@[simp]
theorem ofSubgraph_toGraph (G : Digraph α β) (H : Graph α β) (hH : H ≤ G.toGraph) :
    (G.ofSubgraph H hH).toGraph = H := rfl

@[simp]
theorem ofSubgraph_tail (G : Digraph α β) (H : Graph α β) (hH : H ≤ G.toGraph) (e : E(H)) :
    (G.ofSubgraph H hH).tail e = G.tail ⟨e.1, hH.edgeSet_mono e.2⟩ := rfl

@[simp]
theorem ofSubgraph_head (G : Digraph α β) (H : Graph α β) (hH : H ≤ G.toGraph) (e : E(H)) :
    (G.ofSubgraph H hH).head e = G.head ⟨e.1, hH.edgeSet_mono e.2⟩ := rfl

/-- The vertex set of the component of `v` used by `GraphMinor.contract`. -/
abbrev comp (G : Graph α β) (C : Set β) (v : α) : Set α :=
  contractComponent G C v

theorem contract_isLink (G : Graph α β) (C : Set β) (e : β) (X Y : Set α) :
    (GraphMinor.contract G C).IsLink e X Y ↔
      e ∉ C ∧ ∃ x y, G.IsLink e x y ∧ comp G C x = X ∧ comp G C y = Y :=
  GraphMinor.contract_isLink G C e X Y

theorem vertexSet_contract (G : Graph α β) (C : Set β) :
    V(GraphMinor.contract G C) = comp G C '' V(G) :=
  GraphMinor.vertexSet_contract G C

theorem edgeSet_contract (G : Graph α β) (C : Set β) :
    E(GraphMinor.contract G C) = E(G) \ C :=
  GraphMinor.edgeSet_contract G C

theorem mem_vertexSet_contract {G : Graph α β} {C : Set β} {X : Set α} :
    X ∈ V(GraphMinor.contract G C) ↔ ∃ v ∈ V(G), comp G C v = X :=
  GraphMinor.mem_vertexSet_contract

theorem mem_edgeSet_contract {G : Graph α β} {C : Set β} {e : β} :
    e ∈ E(GraphMinor.contract G C) ↔ e ∈ E(G) ∧ e ∉ C :=
  GraphMinor.mem_edgeSet_contract

/-- The directed graph obtained from `G` by contracting the edges in `C`. Its underlying undirected
graph is `GraphMinor.contract G.toGraph C`, and each uncontracted edge `e` has tail and head equal
to
the `C`-components of `G.tail` and `G.head`. -/
def contract (G : Digraph α β) (C : Set β) : Digraph (Set α) β where
  toGraph := GraphMinor.contract G.toGraph C
  tail e := comp G.toGraph C (G.tail ⟨e.1, (mem_edgeSet_contract.1 e.2).1⟩)
  head e := comp G.toGraph C (G.head ⟨e.1, (mem_edgeSet_contract.1 e.2).1⟩)
  isLink_of_mem e := by
    have he := mem_edgeSet_contract.1 e.2
    rw [contract_isLink]
    exact ⟨he.2, _, _, G.isLink_of_mem ⟨e.1, he.1⟩, rfl, rfl⟩

@[simp]
theorem contract_toGraph (G : Digraph α β) (C : Set β) :
    (G.contract C).toGraph = GraphMinor.contract G.toGraph C := rfl

@[simp]
theorem contract_tail (G : Digraph α β) (C : Set β) (e : E((G.contract C).toGraph)) :
    (G.contract C).tail e = comp G.toGraph C (G.tail ⟨e.1, (mem_edgeSet_contract.1 e.2).1⟩) := rfl

@[simp]
theorem contract_head (G : Digraph α β) (C : Set β) (e : E((G.contract C).toGraph)) :
    (G.contract C).head e = comp G.toGraph C (G.head ⟨e.1, (mem_edgeSet_contract.1 e.2).1⟩) := rfl

/-- An isomorphism of directed graphs: an isomorphism of the underlying undirected graphs that
preserves the tail and head of every edge. -/
structure Iso (H : Digraph α' β') (G : Digraph α β) extends GraphMinor.Iso H.toGraph G.toGraph where
  /-- The vertex equivalence preserves the tail of every edge. -/
  tail_eq (e : E(H.toGraph)) :
    (vertexEquiv ⟨H.tail e, H.tail_mem e⟩).1 = G.tail (edgeEquiv e)
  /-- The vertex equivalence preserves the head of every edge. -/
  head_eq (e : E(H.toGraph)) :
    (vertexEquiv ⟨H.head e, H.head_mem e⟩).1 = G.head (edgeEquiv e)

/-- The identity isomorphism of a directed graph. -/
def Iso.refl (G : Digraph α β) : Iso G G where
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  isLink_iff _ _ _ := Iff.rfl
  tail_eq _ := rfl
  head_eq _ := rfl

/-- The inverse of a directed graph isomorphism. -/
def Iso.symm {H : Digraph α' β'} {G : Digraph α β} (φ : Iso H G) : Iso G H where
  vertexEquiv := φ.vertexEquiv.symm
  edgeEquiv := φ.edgeEquiv.symm
  isLink_iff e x y := by
    have h := φ.isLink_iff (φ.edgeEquiv.symm e) (φ.vertexEquiv.symm x) (φ.vertexEquiv.symm y)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  tail_eq e := by
    have h := φ.tail_eq (φ.edgeEquiv.symm e)
    have hsub : ⟨G.tail e, G.tail_mem e⟩ =
        φ.vertexEquiv ⟨H.tail (φ.edgeEquiv.symm e), H.tail_mem (φ.edgeEquiv.symm e)⟩ := by
      apply Subtype.ext
      rw [h, Equiv.apply_symm_apply]
    exact congrArg Subtype.val (φ.vertexEquiv.symm_apply_eq.2 hsub)
  head_eq e := by
    have h := φ.head_eq (φ.edgeEquiv.symm e)
    have hsub : ⟨G.head e, G.head_mem e⟩ =
        φ.vertexEquiv ⟨H.head (φ.edgeEquiv.symm e), H.head_mem (φ.edgeEquiv.symm e)⟩ := by
      apply Subtype.ext
      rw [h, Equiv.apply_symm_apply]
    exact congrArg Subtype.val (φ.vertexEquiv.symm_apply_eq.2 hsub)

/-- The composition of two directed graph isomorphisms. -/
def Iso.trans {H : Digraph α'' β''} {K : Digraph α' β'} {G : Digraph α β}
    (φ : Iso H K) (ψ : Iso K G) : Iso H G where
  vertexEquiv := φ.vertexEquiv.trans ψ.vertexEquiv
  edgeEquiv := φ.edgeEquiv.trans ψ.edgeEquiv
  isLink_iff e x y := (φ.isLink_iff e x y).trans (ψ.isLink_iff _ _ _)
  tail_eq e := by
    have h₁ : φ.vertexEquiv ⟨H.tail e, H.tail_mem e⟩ =
        ⟨K.tail (φ.edgeEquiv e), K.tail_mem (φ.edgeEquiv e)⟩ := Subtype.ext (φ.tail_eq e)
    change (ψ.vertexEquiv (φ.vertexEquiv ⟨H.tail e, H.tail_mem e⟩)).1 =
      G.tail (ψ.edgeEquiv (φ.edgeEquiv e))
    rw [h₁, ψ.tail_eq]
  head_eq e := by
    have h₁ : φ.vertexEquiv ⟨H.head e, H.head_mem e⟩ =
        ⟨K.head (φ.edgeEquiv e), K.head_mem (φ.edgeEquiv e)⟩ := Subtype.ext (φ.head_eq e)
    change (ψ.vertexEquiv (φ.vertexEquiv ⟨H.head e, H.head_mem e⟩)).1 =
      G.head (ψ.edgeEquiv (φ.edgeEquiv e))
    rw [h₁, ψ.head_eq]

/-- Graph Minors XX, Section 10 (page 355): "A directed graph is a minor of another if the first can
be obtained from a subgraph of the second by contracting edges."
`H.IsIsoMinor G` means that `H` is isomorphic to a directed minor of `G`. -/
def IsIsoMinor (H : Digraph α' β') (G : Digraph α β) : Prop :=
  ∃ (G' : Graph α β) (hG' : G' ≤ G.toGraph) (C : Set β),
    C ⊆ E(G') ∧ Nonempty (Iso H ((G.ofSubgraph G' hG').contract C))

/-- Any undirected graph `G` can be given an orientation of its edges to form a directed graph with
underlying graph `G`. -/
noncomputable def ofGraph (G : Graph α β) : Digraph α β where
  toGraph := G
  tail e := (exists_isLink_of_mem_edgeSet e.2).choose
  head e := (exists_isLink_of_mem_edgeSet e.2).choose_spec.choose
  isLink_of_mem e := (exists_isLink_of_mem_edgeSet e.2).choose_spec.choose_spec

@[simp]
theorem ofGraph_toGraph (G : Graph α β) : (ofGraph G).toGraph = G := rfl

/-- If `H` is isomorphic to a directed minor of `G`, then the underlying undirected graph
`H.toGraph`
is isomorphic to an undirected minor of `G.toGraph`. -/
theorem IsIsoMinor.toGraph {H : Digraph α' β'} {G : Digraph α β}
    (h : H.IsIsoMinor G) : GraphMinor.IsIsoMinor H.toGraph G.toGraph := by
  obtain ⟨G', hG', C, hC, ⟨φ⟩⟩ := h
  exact ⟨G', hG', C, hC, ⟨φ.toIso⟩⟩

theorem Iso.isIsoMinor_left {H₁ : Digraph α'' β''} {H₂ : Digraph α' β'} {G : Digraph α β}
    (φ : Iso H₁ H₂) (h : H₂.IsIsoMinor G) : H₁.IsIsoMinor G := by
  obtain ⟨G', hG', C, hC, ⟨ψ⟩⟩ := h
  exact ⟨G', hG', C, hC, ⟨Iso.trans φ ψ⟩⟩

end Digraph

/-! ### Directed minor models and construction of a directed minor from a model -/

/-- A model `(ηv, ηe)` of a directed graph `H` in a directed graph `G` (Graph Minors IV, Section 7,
pages 242–243): a model of `H.toGraph` in `G.toGraph` such that for every edge `e` of `H`, the tail
of `ηe e` in `G` belongs to `ηv (H.tail e)` and the head of `ηe e` in `G` belongs to
`ηv (H.head e)`. -/
structure IsDirMinorModel (H : Digraph α' β') (G : Digraph α β) (ηv : α' → Set α) (ηe : β' → β) :
    Prop extends IsMinorModel H.toGraph G.toGraph ηv ηe where
  /-- The tail of `ηe e` lies in the branch set of the tail of `e`. -/
  tail_mem : ∀ e : E(H.toGraph), G.tail ⟨ηe e.1, edge_mem e.1 e.2⟩ ∈ ηv (H.tail e)
  /-- The head of `ηe e` lies in the branch set of the head of `e`. -/
  head_mem : ∀ e : E(H.toGraph), G.head ⟨ηe e.1, edge_mem e.1 e.2⟩ ∈ ηv (H.head e)

section DirModelToMinor

variable {H : Digraph α' β'} {G : Digraph α β} {ηv : α' → Set α} {ηe : β' → β}

/-- A directed minor model gives a directed minor. This is the step in the proof of Graph Minors XX,
(10.5), page 356, that invokes Graph Minors IV, Section 7, pages 242–243 (reference [1] in XX,
misprinted as [2] on page 356). -/
theorem isIsoMinor_of_isDirMinorModel (h : IsDirMinorModel H G ηv ηe) : H.IsIsoMinor G := by
  let hm := h.toIsMinorModel
  refine ⟨modelSubgraph hm, modelSubgraph_le hm, modelContractEdges hm,
    modelContractEdges_subset hm, ⟨?_⟩⟩
  exact
    { toIso := modelContractionIso hm
      tail_eq := fun e ↦
        (comp_modelSubgraph_eq hm (H.tail_mem e) (h.tail_mem e)).symm
      head_eq := fun e ↦
        (comp_modelSubgraph_eq hm (H.head_mem e) (h.head_mem e)).symm }

end DirModelToMinor

/-! ### Tournaments with $p = 2|E(G_1)| + |V(G_1)|$ vertices have $G_1$ as a minor -/

private theorem isLink_of_inc_of_ne_aux {G : Graph α β} {e : β} {x y : α} (hx : G.Inc e x)
    (hy : G.Inc e y) (hne : x ≠ y) : G.IsLink e x y := by
  have h₁ := hx.isLink_other
  rcases hy.eq_or_eq_of_isLink h₁ with h | h
  · exact absurd h.symm hne
  · rw [h]
    exact h₁

/-- Graph Minors XX, proof of (10.5) (page 355): "Let $p = 2|E(G_1)| + |V(G_1)|$; then every
tournament with $p$ vertices has a minor isomorphic to $G_1$.", in minor-model form. -/
theorem isDirMinorModel_of_hasCliqueMinor [Nonempty β] {H : Digraph α' β'} {G : Digraph α β}
    (hVH : V(H.toGraph).Finite) (hEH : E(H.toGraph).Finite)
    (hVG : V(G.toGraph).Finite) (hEG : E(G.toGraph).Finite) {p : ℕ}
    (hp : V(H.toGraph).ncard + 2 * E(H.toGraph).ncard ≤ p)
    (hc : HasCliqueMinor (Hypergraph.ofGraph G.toGraph hVG hEG) p) :
    ∃ (ηv : α' → Set α) (ηe : β' → β), IsDirMinorModel H G ηv ηe := by
  classical
  obtain ⟨a, h₁, h₂, h₃⟩ := hc
  have : Finite V(H.toGraph) := hVH
  have : Finite E(H.toGraph) := hEH
  let ι := V(H.toGraph) ⊕ (E(H.toGraph) × Bool)
  have : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι ≤ Fintype.card (Fin p) := by
    have h₄ : Nat.card ι = V(H.toGraph).ncard + E(H.toGraph).ncard * 2 := by
      rw [show Nat.card ι = _ + _ from Nat.card_sum, Nat.card_prod, Nat.card_coe_set_eq,
        Nat.card_coe_set_eq, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, h₄]
    omega
  obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le hcard
  let b : ι → Set α := fun i ↦ a (j i)
  have hne' : ∀ {i i' : ι}, i ≠ i' → j i ≠ j i' := fun h h' ↦ h (j.injective h')
  have huniq : ∀ {i i' x}, x ∈ b i → x ∈ b i' → i = i' := by
    intro i i' x hi hi'
    by_contra hne
    exact Set.disjoint_left.mp (h₂ _ _ (hne' hne)) hi hi'
  have hlink : ∀ (i i' : ι), i ≠ i' → ∃ u ∈ b i, ∃ w ∈ b i', ∃ f, G.toGraph.IsLink f u w := by
    intro i i' hne
    obtain ⟨u, hu, w, hw, huw, f, hf₁, hf₂⟩ := h₃ _ _ (hne' hne)
    exact ⟨u, hu, w, hw, f, isLink_of_inc_of_ne_aux hf₁ hf₂ huw⟩
  choose cu hcu cw hcw cf hcf using hlink
  have hbne : ∀ e : E(H.toGraph), (Sum.inr (e, true) : ι) ≠ Sum.inr (e, false) := fun e ↦ by
    simp
  let dir : E(H.toGraph) → Prop := fun e ↦
    G.tail ⟨cf _ _ (hbne e), (hcf _ _ (hbne e)).edge_mem⟩ = cu _ _ (hbne e)
  let tl : E(H.toGraph) → V(H.toGraph) := fun e ↦
    if dir e then ⟨H.tail e, H.tail_mem e⟩ else ⟨H.head e, H.head_mem e⟩
  let hd : E(H.toGraph) → V(H.toGraph) := fun e ↦
    if dir e then ⟨H.head e, H.head_mem e⟩ else ⟨H.tail e, H.tail_mem e⟩
  have htl : ∀ e : E(H.toGraph), H.toGraph.IsLink e.1 (tl e).1 (hd e).1 := fun e ↦ by
    dsimp [tl, hd]
    split_ifs
    · exact H.isLink_of_mem e
    · exact (H.isLink_of_mem e).symm
  let en : E(H.toGraph) × Bool → V(H.toGraph) := fun e ↦ if e.2 then tl e.1 else hd e.1
  let own : ι → α' := fun i ↦ Sum.elim (fun v ↦ v.1) (fun e ↦ (en e).1) i
  let ηv : α' → Set α := fun v ↦ ⋃ i ∈ {i | own i = v}, b i
  let ηe : β' → β := fun e ↦
    if h : e ∈ E(H.toGraph) then cf _ _ (hbne ⟨e, h⟩) else Classical.arbitrary β
  have hηe : ∀ e : E(H.toGraph),
      G.toGraph.IsLink (ηe e.1) (cu _ _ (hbne e)) (cw _ _ (hbne e)) := fun e ↦ by
    simp only [ηe, dite_eq_left e.2]
    exact hcf _ _ (hbne e)
  have hmemv : ∀ {i x}, x ∈ b i → x ∈ ηv (own i) := fun {i x} hx ↦
    mem_biUnion (x := i) rfl hx
  have hownv : ∀ {v x}, x ∈ ηv v → ∃ i, own i = v ∧ x ∈ b i := fun {v x} hx ↦ by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact ⟨i, hi, hxi⟩
  have hsubV : ∀ {i}, b i ⊆ V(G.toGraph) := fun {i} ↦ (h₁ (j i)).2.1
  have hnot : ∀ {f s t i i'}, G.toGraph.IsLink f s t → s ∈ b i → t ∈ b i' →
      (∀ e : E(H.toGraph), ¬ (i = Sum.inr (e, true) ∧ i' = Sum.inr (e, false)) ∧
        ¬ (i = Sum.inr (e, false) ∧ i' = Sum.inr (e, true))) →
      f ∉ ηe '' E(H.toGraph) := by
    rintro f s t i i' hf hs ht hno ⟨e, he, rfl⟩
    have hl := hηe ⟨e, he⟩
    rcases hf.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (hno ⟨e, he⟩).1 ⟨huniq hs (hcu _ _ _), huniq ht (hcw _ _ _)⟩
    · exact (hno ⟨e, he⟩).2 ⟨huniq hs (hcw _ _ _), huniq ht (hcu _ _ _)⟩
  have hadjK : ∀ {v f s t}, G.toGraph.IsLink f s t → f ∉ ηe '' E(H.toGraph) →
      s ∈ ηv v → t ∈ ηv v →
      ((G.toGraph.deleteEdges (ηe '' E(H.toGraph))).induce (ηv v)).Adj s t :=
    fun hf hn hs ht ↦ ⟨_, ⟨(deleteEdges_isLink ..).mpr ⟨hf, hn⟩, hs, ht⟩⟩
  have hblock : ∀ {v i}, own i = v → ∀ x ∈ b i, ∀ y ∈ b i, Relation.ReflTransGen
      ((G.toGraph.deleteEdges (ηe '' E(H.toGraph))).induce (ηv v)).Adj x y := by
    rintro v i rfl x hx y hy
    refine Relation.ReflTransGen.mono (fun u w huw ↦ ?_) _ _ ((h₁ (j i)).2.2 x hx y hy)
    obtain ⟨⟨hne, f, hf₁, hf₂⟩, hu, hw⟩ := huw
    have hl := isLink_of_inc_of_ne_aux hf₁ hf₂ hne
    refine hadjK hl (hnot hl hu hw fun e ↦ ⟨?_, ?_⟩) (hmemv hu) (hmemv hw)
    · rintro ⟨rfl, h₄⟩
      exact hbne e h₄
    · rintro ⟨rfl, h₄⟩
      exact hbne e h₄.symm
  have hsubη : ∀ {v}, ηv v ⊆ V(G.toGraph) := fun {v} x hx ↦ by
    obtain ⟨i, -, hxi⟩ := hownv hx
    exact hsubV hxi
  have hconnected : ∀ v ∈ V(H.toGraph),
      ∃ K ≤ G.toGraph.deleteEdges (ηe '' E(H.toGraph)), V(K) = ηv v ∧ GraphConnected K := by
    intro v hv
    set K := (G.toGraph.deleteEdges (ηe '' E(H.toGraph))).induce (ηv v)
    have hsymm : ∀ ⦃a b⦄, K.Adj a b → K.Adj b a := fun _ _ h ↦ h.symm
    let i₀ : ι := Sum.inl ⟨v, hv⟩
    obtain ⟨r, hr⟩ := (h₁ (j i₀)).1
    have hto : ∀ i, own i = v → ∀ y ∈ b i, Relation.ReflTransGen K.Adj y r := by
      rintro (w | e) hown y hy
      · have hw : w = ⟨v, hv⟩ := Subtype.ext hown
        subst hw
        exact hblock rfl y hy r hr
      · have hne : (i₀ : ι) ≠ Sum.inr e := Sum.inl_ne_inr
        have hl := hcf _ _ hne
        have hnt : cf _ _ hne ∉ ηe '' E(H.toGraph) := hnot hl (hcu _ _ hne) (hcw _ _ hne) fun e' ↦
          ⟨fun h ↦ Sum.inl_ne_inr h.1, fun h ↦ Sum.inl_ne_inr h.1⟩
        have hm₁ : cu _ _ hne ∈ ηv v := hmemv (i := i₀) (hcu _ _ hne)
        have hm₂ : cw _ _ hne ∈ ηv v := by
          have := hmemv (hcw _ _ hne)
          rwa [hown] at this
        have hadj : K.Adj (cw _ _ hne) (cu _ _ hne) := (hadjK hl hnt hm₁ hm₂).symm
        exact (hblock hown y hy _ (hcw _ _ hne)).trans
          (Relation.ReflTransGen.head hadj (hblock (i := i₀) rfl _ (hcu _ _ hne) r hr))
    refine ⟨K, Graph.induce_le hsubη, rfl, ⟨r, hmemv (i := i₀) hr⟩, fun x hx y hy ↦ ?_⟩
    obtain ⟨i, hi, hxi⟩ := hownv hx
    obtain ⟨i', hi', hyi⟩ := hownv hy
    have hrev : ∀ {a b}, Relation.ReflTransGen K.Adj a b → Relation.ReflTransGen K.Adj b a := by
      intro a b h
      induction h with
      | refl => exact .refl
      | tail _ hbc ih => exact .head (hsymm hbc) ih
    exact (hto i hi x hxi).trans (hrev (hto i' hi' y hyi))
  have hownT : ∀ e : E(H.toGraph), own (Sum.inr (e, true)) = (tl e).1 := fun e ↦ by simp [own, en]
  have hownF : ∀ e : E(H.toGraph), own (Sum.inr (e, false)) = (hd e).1 := fun e ↦ by simp [own, en]
  have hmemT : ∀ e : E(H.toGraph), cu _ _ (hbne e) ∈ ηv (tl e).1 := fun e ↦ by
    rw [← hownT]
    exact hmemv (hcu _ _ _)
  have hmemF : ∀ e : E(H.toGraph), cw _ _ (hbne e) ∈ ηv (hd e).1 := fun e ↦ by
    rw [← hownF]
    exact hmemv (hcw _ _ _)
  have hownT' : ∀ {e : E(H.toGraph)} {v}, cu _ _ (hbne e) ∈ ηv v → (tl e).1 = v := fun {e v} h ↦ by
    obtain ⟨i, hi, hxi⟩ := hownv h
    rw [← hownT, ← hi, huniq (hcu _ _ (hbne e)) hxi]
  have hownF' : ∀ {e : E(H.toGraph)} {v}, cw _ _ (hbne e) ∈ ηv v → (hd e).1 = v := fun {e v} h ↦ by
    obtain ⟨i, hi, hxi⟩ := hownv h
    rw [← hownF, ← hi, huniq (hcw _ _ (hbne e)) hxi]
  have hm : IsMinorModel H.toGraph G.toGraph ηv ηe :=
    { vertex_nonempty := fun v hv ↦ by
        obtain ⟨r, hr⟩ := (h₁ (j (Sum.inl ⟨v, hv⟩))).1
        exact ⟨r, hmemv (i := Sum.inl ⟨v, hv⟩) hr⟩
      vertex_subset := fun v _ ↦ hsubη
      edge_mem := fun e he ↦ (hηe ⟨e, he⟩).edge_mem
      vertex_disjoint := fun v₁ _ v₂ _ hne ↦ Set.disjoint_left.mpr fun x h₄ h₅ ↦ by
        obtain ⟨i, rfl, hxi⟩ := hownv h₄
        obtain ⟨i', rfl, hxi'⟩ := hownv h₅
        exact hne (congrArg own (huniq hxi hxi'))
      edge_injOn := fun e₁ h₄ e₂ h₅ heq ↦ by
        by_contra hne
        have hl₁ := hηe ⟨e₁, h₄⟩
        have hl₂ := hηe ⟨e₂, h₅⟩
        rw [heq] at hl₁
        have hE : ∀ {t t' : Bool} {z}, z ∈ b (Sum.inr (⟨e₁, h₄⟩, t)) →
            z ∈ b (Sum.inr (⟨e₂, h₅⟩, t')) → False := fun {t t' z} hz hz' ↦ by
          have h₇ : ((⟨e₁, h₄⟩, t) : E(H.toGraph) × Bool) = (⟨e₂, h₅⟩, t') :=
            Sum.inr_injective (huniq hz hz')
          exact hne (congrArg Subtype.val (congrArg Prod.fst h₇))
        rcases hl₁.eq_and_eq_or_eq_and_eq hl₂ with ⟨h₆, -⟩ | ⟨h₆, -⟩
        · exact hE (t := true) (t' := true) (hcu _ _ _) (by rw [h₆]; exact hcu _ _ _)
        · exact hE (t := true) (t' := false) (hcu _ _ _) (by rw [h₆]; exact hcw _ _ _)
      inc_iff := fun v hv e he ↦ by
        have hl := hηe ⟨e, he⟩
        constructor
        · intro hinc
          rcases hinc.eq_or_eq_of_isLink (htl ⟨e, he⟩) with rfl | rfl
          · exact ⟨_, hmemT _, hl.inc_left⟩
          · exact ⟨_, hmemF _, hl.inc_right⟩
        · rintro ⟨x, hx, hinc⟩
          rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
          · rw [← hownT' hx]
            exact (htl ⟨e, he⟩).inc_left
          · rw [← hownF' hx]
            exact (htl ⟨e, he⟩).inc_right
      isLoopAt_iff := fun v hv e he ↦ by
        have hl := hηe ⟨e, he⟩
        have hL := htl ⟨e, he⟩
        constructor
        · intro hloop x hinc
          have h₄ := hloop.eq_of_inc hL.inc_left
          have h₅ := hloop.eq_of_inc hL.inc_right
          rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
          · have := hmemT ⟨e, he⟩
            rwa [← h₄] at this
          · have := hmemF ⟨e, he⟩
            rwa [← h₅] at this
        · intro hall
          have h₄ := hownT' (hall _ hl.inc_left)
          have h₅ := hownF' (hall _ hl.inc_right)
          rw [h₄, h₅] at hL
          exact hL
      connected := hconnected }
  have hends (e : E(H.toGraph)) :
      G.tail ⟨ηe e.1, hm.edge_mem e.1 e.2⟩ ∈ ηv (H.tail e) ∧
        G.head ⟨ηe e.1, hm.edge_mem e.1 e.2⟩ ∈ ηv (H.head e) := by
    let f : E(G.toGraph) := ⟨cf _ _ (hbne e), (hcf _ _ (hbne e)).edge_mem⟩
    have hf : (⟨ηe e.1, hm.edge_mem e.1 e.2⟩ : E(G.toGraph)) = f :=
      Subtype.ext (by simp [ηe, e.2, f])
    rw [hf]
    rcases (G.isLink_of_mem f).eq_and_eq_or_eq_and_eq (hcf _ _ (hbne e)) with
      ⟨ht, hh⟩ | ⟨ht, hh⟩
    · have hdir : dir e := ht
      simpa [ht, hh, tl, hd, hdir] using And.intro (hmemT e) (hmemF e)
    · have hdir : ¬ dir e := fun h ↦ hbne e (huniq (hcu _ _ _) ((h.symm.trans ht) ▸ hcw _ _ _))
      simpa [ht, hh, tl, hd, hdir] using And.intro (hmemF e) (hmemT e)
  exact ⟨ηv, ηe, hm, fun e ↦ (hends e).1, fun e ↦ (hends e).2⟩

/-- Graph Minors XX, proof of (10.5) (page 355): "Let $p = 2|E(G_1)| + |V(G_1)|$; then every
tournament with $p$ vertices has a minor isomorphic to $G_1$." -/
theorem isIsoMinor_of_hasCliqueMinor [Nonempty β] {H : Digraph α' β'} {G : Digraph α β}
    (hVH : V(H.toGraph).Finite) (hEH : E(H.toGraph).Finite)
    (hVG : V(G.toGraph).Finite) (hEG : E(G.toGraph).Finite) {p : ℕ}
    (hp : V(H.toGraph).ncard + 2 * E(H.toGraph).ncard ≤ p)
    (hc : HasCliqueMinor (Hypergraph.ofGraph G.toGraph hVG hEG) p) :
    H.IsIsoMinor G := by
  obtain ⟨ηv, ηe, hm⟩ := isDirMinorModel_of_hasCliqueMinor hVH hEH hVG hEG hp hc
  exact isIsoMinor_of_isDirMinorModel hm

/-! ### Directed patchworks and simulation -/

/-- The `Unit`-patchwork $P_i = (H_i, \mu, \Delta, \phi)$ of a finite directed graph $G_i$ from the
proof of (10.5) (Graph Minors XX, Section 10, pages 355–356):
"for $e \in E(G_i)$, $\mu(e)$ is the one- or two-vertex sequence enumerating the ends of $e$ in
$G_i$ (tail first)". -/
noncomputable def digraphPatchwork (G : Digraph α β) (hV : V(G.toGraph).Finite)
    (hE : E(G.toGraph).Finite) : Patchwork Unit α β where
  G := (Hypergraph.ofGraph G.toGraph hV hE).toRooted
  dom := E(G.toGraph)
  μ e := open Classical in
    if he : e ∈ E(G.toGraph) then
      if G.tail ⟨e, he⟩ = G.head ⟨e, he⟩ then [G.tail ⟨e, he⟩]
      else [G.tail ⟨e, he⟩, G.head ⟨e, he⟩]
    else []
  Δ e := graphPatch ((Hypergraph.ofGraph G.toGraph hV hE).ends e)
  φ _ := ()
  dom_subset := le_rfl
  μ_nodup e he := by
    rw [dite_eq_left he]
    split_ifs with h
    · simp
    · simp [h]
  μ_set e he := by
    rw [dite_eq_left he]
    ext v
    have hl := G.isLink_of_mem ⟨e, he⟩
    split_ifs with h
    · simp only [mem_ofPred_eq, List.mem_singleton]
      change v = G.tail ⟨e, he⟩ ↔ G.toGraph.Inc e v
      refine ⟨?_, fun hinc ↦ ?_⟩
      · rintro rfl
        exact hl.inc_left
      · rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
        · rfl
        · exact h.symm
    · simp only [mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false]
      change (v = G.tail ⟨e, he⟩ ∨ v = G.head ⟨e, he⟩) ↔ G.toGraph.Inc e v
      refine ⟨?_, fun hinc ↦ hinc.eq_or_eq_of_isLink hl⟩
      rintro (rfl | rfl)
      · exact hl.inc_left
      · exact hl.inc_right
  Δ_verts _ _ := rfl
  Δ_free _ he hne := absurd he hne

@[simp]
theorem digraphPatchwork_G (G : Digraph α β) (hV : V(G.toGraph).Finite)
    (hE : E(G.toGraph).Finite) :
    (digraphPatchwork G hV hE).G = (Hypergraph.ofGraph G.toGraph hV hE).toRooted := rfl

theorem digraphPatchwork_vertexSet (G : Digraph α β) (hV : V(G.toGraph).Finite)
    (hE : E(G.toGraph).Finite) :
    (digraphPatchwork G hV hE).G.vertexSet = V(G.toGraph) := rfl

theorem digraphPatchwork_edgeSet (G : Digraph α β) (hV : V(G.toGraph).Finite)
    (hE : E(G.toGraph).Finite) :
    (digraphPatchwork G hV hE).G.edgeSet = E(G.toGraph) := rfl

theorem digraphPatchwork_ends (G : Digraph α β) (hV : V(G.toGraph).Finite)
    (hE : E(G.toGraph).Finite) (e : β) :
    (digraphPatchwork G hV hE).G.ends e = {v | G.toGraph.Inc e v} := rfl

@[simp]
theorem digraphPatchwork_dom (G : Digraph α β) (hV : V(G.toGraph).Finite)
    (hE : E(G.toGraph).Finite) :
    (digraphPatchwork G hV hE).dom = E(G.toGraph) := rfl

@[simp]
theorem digraphPatchwork_Δ (G : Digraph α β) (hV : V(G.toGraph).Finite)
    (hE : E(G.toGraph).Finite) (e : β) :
    (digraphPatchwork G hV hE).Δ e = graphPatch {v | G.toGraph.Inc e v} := rfl

/-- Graph Minors XX, proof of (10.5) (page 356): "Then $P_i$ is a free $\Omega$-patchwork." -/
theorem isFree_digraphPatchwork (G : Digraph α β) (hV : V(G.toGraph).Finite)
    (hE : E(G.toGraph).Finite) : IsFree (digraphPatchwork G hV hE) := by
  intro e _ δ hg hv
  replace hv : δ.verts = (Hypergraph.ofGraph G.toGraph hV hE).ends e := hv
  replace hg : IsGrouping ((Hypergraph.ofGraph G.toGraph hV hE).ends e) δ := hg
  change δ = emptySubgraph _ ∨ δ = completeSubgraph _
  by_cases h : ∃ a b, δ.Adj a b
  · right
    obtain ⟨a, b, hab⟩ := h
    have hin : ∀ {x}, x ∈ δ.verts → G.toGraph.Inc e x := fun {x} hx ↦ by
      rw [hv] at hx
      exact hx
    have ha : G.toGraph.Inc e a := hin (δ.edge_vert hab)
    have hb : G.toGraph.Inc e b := hin (δ.edge_vert hab.symm)
    refine SimpleGraph.Subgraph.ext hv ?_
    ext x y
    rw [completeSubgraph_adj]
    constructor
    · intro hxy
      exact ⟨hv ▸ δ.edge_vert hxy, hv ▸ δ.edge_vert hxy.symm, hxy.ne⟩
    · rintro ⟨hx, hy, hne⟩
      have hx' : G.toGraph.Inc e x := hx
      have hy' : G.toGraph.Inc e y := hy
      have hl := isLink_of_inc_of_ne_aux ha hb hab.ne
      rcases hx'.eq_or_eq_of_isLink hl with rfl | rfl <;>
        rcases hy'.eq_or_eq_of_isLink hl with rfl | rfl
      · exact absurd rfl hne
      · exact hab
      · exact hab.symm
      · exact absurd rfl hne
  · left
    refine SimpleGraph.Subgraph.ext hv ?_
    ext x y
    exact ⟨fun hxy ↦ h ⟨x, y, hxy⟩, fun hxy ↦ (not_emptySubgraph_adj hxy).elim⟩

/-- If `digraphPatchwork H hVH hEH` is simulated in `digraphPatchwork G hVG hEG`, then there is a
directed minor model of `H` in `G`. This uses the discussion in Graph Minors IV, Section 7,
pages 242–243, cited in Graph Minors XX, proof of (10.5), page 356 (reference [1], misprinted as
[2] there). -/
theorem isDirMinorModel_of_simulated {H G : Digraph α β}
    {hVH : V(H.toGraph).Finite} {hEH : E(H.toGraph).Finite}
    {hVG : V(G.toGraph).Finite} {hEG : E(G.toGraph).Finite}
    (hsim : Simulated (digraphPatchwork H hVH hEH) (digraphPatchwork G hVG hEG)) :
    ∃ (ηv : α → Set α) (ηe : β → β), IsDirMinorModel H G ηv ηe := by
  let PH := digraphPatchwork H hVH hEH
  let PG := digraphPatchwork G hVG hEG
  obtain ⟨ηv, ηe, hexp, R, hreal⟩ := hsim
  have hVP : ∀ v, v ∈ PH.G.vertexSet ↔ v ∈ V(H.toGraph) := fun _ ↦ Iff.rfl
  have hEP : ∀ e, e ∈ PH.G.edgeSet ↔ e ∈ E(H.toGraph) := fun _ ↦ Iff.rfl
  have hdomH : ∀ e, e ∈ PH.dom ↔ e ∈ E(H.toGraph) := fun _ ↦ Iff.rfl
  have hdomG : ∀ e, e ∈ PG.dom ↔ e ∈ E(G.toGraph) := fun _ ↦ Iff.rfl
  have hinc_iff : ∀ v ∈ V(H.toGraph), ∀ e ∈ E(H.toGraph),
      H.toGraph.Inc e v ↔ ∃ x ∈ ηv v, G.toGraph.Inc (ηe e) x := by
    intro v hv e he
    have he' : ηe e ∈ E(G.toGraph) := hexp.edge_mem e ((hEP e).mpr he)
    have hμH := PH.μ_set e ((hdomH e).mpr he)
    have hμG := PG.μ_set (ηe e) ((hdomG (ηe e)).mpr he')
    rw [digraphPatchwork_ends] at hμH hμG
    constructor
    · intro hinc
      have hv_mem : v ∈ PH.μ e := by
        have hv_ends : v ∈ {u | H.toGraph.Inc e u} := hinc
        rw [← hμH] at hv_ends
        exact hv_ends
      obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hv_mem
      have hr' : r < (PG.μ (ηe e)).length := hexp.μ_length e ((hdomH e).mpr he) ▸ hr
      refine ⟨(PG.μ (ηe e))[r], hexp.μ_mem e ((hdomH e).mpr he) r hr hr', ?_⟩
      have hx_mem : (PG.μ (ηe e))[r] ∈ {x | x ∈ PG.μ (ηe e)} := List.getElem_mem hr'
      rw [hμG] at hx_mem
      exact hx_mem
    · rintro ⟨x, hxv, hinc'⟩
      have hx_mem : x ∈ PG.μ (ηe e) := by
        have hx_ends : x ∈ {u | G.toGraph.Inc (ηe e) u} := hinc'
        rw [← hμG] at hx_ends
        exact hx_ends
      obtain ⟨r, hr', rfl⟩ := List.mem_iff_getElem.mp hx_mem
      have hr : r < (PH.μ e).length := (hexp.μ_length e ((hdomH e).mpr he)).symm ▸ hr'
      let w := (PH.μ e)[r]
      have hw_inc : H.toGraph.Inc e w := by
        have hw_mem : w ∈ {u | u ∈ PH.μ e} := List.getElem_mem hr
        rw [hμH] at hw_mem
        exact hw_mem
      have hw_v : w ∈ V(H.toGraph) := hw_inc.vertex_mem
      have hxw : (PG.μ (ηe e))[r] ∈ ηv w := hexp.μ_mem e ((hdomH e).mpr he) r hr hr'
      have hvw : v = w := by
        by_contra hne
        exact Set.disjoint_left.mp
          (hexp.vertex_disjoint v ((hVP v).mpr hv) w ((hVP w).mpr hw_v) hne) hxv hxw
      exact hvw ▸ hw_inc
  have hisLoopAt_iff : ∀ v ∈ V(H.toGraph), ∀ e ∈ E(H.toGraph),
      H.toGraph.IsLoopAt e v ↔ ∀ x, G.toGraph.Inc (ηe e) x → x ∈ ηv v := by
    intro v hv e he
    have he' : ηe e ∈ E(G.toGraph) := hexp.edge_mem e ((hEP e).mpr he)
    have hμH := PH.μ_set e ((hdomH e).mpr he)
    have hμG := PG.μ_set (ηe e) ((hdomG (ηe e)).mpr he')
    rw [digraphPatchwork_ends] at hμH hμG
    constructor
    · intro hloop x hinc'
      have hx_mem : x ∈ PG.μ (ηe e) := by
        have hx_ends : x ∈ {u | G.toGraph.Inc (ηe e) u} := hinc'
        rw [← hμG] at hx_ends
        exact hx_ends
      obtain ⟨r, hr', rfl⟩ := List.mem_iff_getElem.mp hx_mem
      have hr : r < (PH.μ e).length := (hexp.μ_length e ((hdomH e).mpr he)).symm ▸ hr'
      let w := (PH.μ e)[r]
      have hw_inc : H.toGraph.Inc e w := by
        have hw_mem : w ∈ {u | u ∈ PH.μ e} := List.getElem_mem hr
        rw [hμH] at hw_mem
        exact hw_mem
      have hvw : v = w := hloop.eq_of_inc hw_inc
      exact hvw ▸ hexp.μ_mem e ((hdomH e).mpr he) r hr hr'
    · intro hall
      obtain ⟨a, b, hab⟩ := H.toGraph.exists_isLink_of_mem_edgeSet he
      have ha_eq : a = v := by
        obtain ⟨x, hxa, hinc_x⟩ := (hinc_iff a hab.left_mem e he).mp hab.inc_left
        have hxv := hall x hinc_x
        by_contra hne
        exact Set.disjoint_left.mp
          (hexp.vertex_disjoint a ((hVP a).mpr hab.left_mem) v ((hVP v).mpr hv) hne) hxa hxv
      have hb_eq : b = v := by
        obtain ⟨x, hxb, hinc_x⟩ := (hinc_iff b hab.right_mem e he).mp hab.inc_right
        have hxv := hall x hinc_x
        by_contra hne
        exact Set.disjoint_left.mp
          (hexp.vertex_disjoint b ((hVP b).mpr hab.right_mem) v ((hVP v).mpr hv) hne) hxb hxv
      rw [← isLink_self_iff]
      rw [ha_eq, hb_eq] at hab
      exact hab
  have hconnected : ∀ v ∈ V(H.toGraph),
      ∃ K ≤ G.toGraph.deleteEdges (ηe '' E(H.toGraph)), V(K) = ηv v ∧ GraphConnected K := by
    intro v hv
    let K : Graph α β := (G.toGraph.deleteEdges (ηe '' E(H.toGraph))).induce (ηv v)
    have hK_le : K ≤ G.toGraph.deleteEdges (ηe '' E(H.toGraph)) :=
      Graph.induce_le (hexp.vertex_subset v ((hVP v).mpr hv))
    refine ⟨K, hK_le, rfl, hexp.vertex_nonempty v ((hVP v).mpr hv), ?_⟩
    intro x hx y hy
    obtain ⟨D, ⟨z, rfl⟩, hD_verts⟩ := hreal.2 v ((hVP v).mpr hv)
    obtain ⟨δ, hδ, hR_eq⟩ := hreal.1
    have hR_adj_to_K : ∀ a b : R.verts,
        a.1 ∈ ηv v → b.1 ∈ ηv v → R.coe.Adj a b → K.Adj a.1 b.1 := by
      intro a b ha hb hab
      have hR_adj : (realizationOf (PG.deleteEdges (ηe '' PH.G.edgeSet)).G.toHypergraph δ).Adj
          a.1 b.1 := by
        rw [← hR_eq]
        exact hab
      rw [realizationOf_adj] at hR_adj
      obtain ⟨e', he', hδ_adj⟩ := hR_adj
      have hδ_mem := hδ e' he'
      have he'_sdiff : e' ∈ PG.G.edgeSet ∧ e' ∉ ηe '' PH.G.edgeSet := he'
      have hδ_cases : δ e' = emptySubgraph {w | G.toGraph.Inc e' w} ∨
          δ e' = completeSubgraph {w | G.toGraph.Inc e' w} := by
        change δ e' ∈ PG.Δ e' at hδ_mem
        rw [digraphPatchwork_Δ, mem_graphPatch_iff] at hδ_mem
        exact hδ_mem
      rcases hδ_cases with hEq | hEq
      · rw [hEq] at hδ_adj
        exact (not_emptySubgraph_adj hδ_adj).elim
      · rw [hEq, completeSubgraph_adj] at hδ_adj
        obtain ⟨ha_inc, hb_inc, hne⟩ := hδ_adj
        change G.toGraph.Inc e' a.1 at ha_inc
        change G.toGraph.Inc e' b.1 at hb_inc
        have hlink : G.toGraph.IsLink e' a.1 b.1 := isLink_of_inc_of_ne_aux ha_inc hb_inc hne
        refine ⟨e', ?_⟩
        simp only [K, Graph.induce_isLink, Graph.deleteEdges_isLink]
        exact ⟨⟨hlink, he'_sdiff.2⟩, ha, hb⟩
    have hreach_K : ∀ u : R.verts, R.coe.Reachable z u → Relation.ReflTransGen K.Adj z.1 u.1 := by
      intro u hr
      rw [SimpleGraph.reachable_iff_reflTransGen] at hr
      induction hr with
      | refl => exact Relation.ReflTransGen.refl
      | @tail a b ha_rel hab ih =>
        have ha_reach : R.coe.Reachable z a := by
          rw [SimpleGraph.reachable_iff_reflTransGen]
          exact ha_rel
        have hb_reach : R.coe.Reachable z b := ha_reach.trans (SimpleGraph.Adj.reachable hab)
        have ha_v : a.1 ∈ ηv v := hD_verts ▸ ⟨a.2, ha_reach⟩
        have hb_v : b.1 ∈ ηv v := hD_verts ▸ ⟨b.2, hb_reach⟩
        exact ih.tail (hR_adj_to_K a b ha_v hb_v hab)
    have hxD : x ∈ (component R z).verts := hD_verts.symm ▸ hx
    have hyD : y ∈ (component R z).verts := hD_verts.symm ▸ hy
    obtain ⟨hxR, hx_reach⟩ := hxD
    obtain ⟨hyR, hy_reach⟩ := hyD
    have hzx : Relation.ReflTransGen K.Adj z.1 x := hreach_K ⟨x, hxR⟩ hx_reach
    have hzy : Relation.ReflTransGen K.Adj z.1 y := hreach_K ⟨y, hyR⟩ hy_reach
    have hxz : Relation.ReflTransGen K.Adj x z.1 := by
      clear *- hzx
      induction hzx with
      | refl => exact Relation.ReflTransGen.refl
      | @tail a b _ hab ih => exact (Relation.ReflTransGen.single hab.symm).trans ih
    exact hxz.trans hzy
  have hm : IsMinorModel H.toGraph G.toGraph ηv ηe :=
    { vertex_nonempty := fun v hv ↦ hexp.vertex_nonempty v ((hVP v).mpr hv)
      vertex_subset := fun v hv ↦ hexp.vertex_subset v ((hVP v).mpr hv)
      edge_mem := fun e he ↦ hexp.edge_mem e ((hEP e).mpr he)
      vertex_disjoint := fun v₁ hv₁ v₂ hv₂ ↦
        hexp.vertex_disjoint v₁ ((hVP v₁).mpr hv₁) v₂ ((hVP v₂).mpr hv₂)
      edge_injOn := hexp.edge_injOn
      inc_iff := hinc_iff
      isLoopAt_iff := hisLoopAt_iff
      connected := hconnected }
  have hends (e : E(H.toGraph)) :
      G.tail ⟨ηe e.1, hm.edge_mem e.1 e.2⟩ ∈ ηv (H.tail e) ∧
        G.head ⟨ηe e.1, hm.edge_mem e.1 e.2⟩ ∈ ηv (H.head e) := by
    classical
    have he' : ηe e.1 ∈ E(G.toGraph) := hm.edge_mem e.1 e.2
    have hμH : PH.μ e.1 =
        (if H.tail e = H.head e then [H.tail e] else [H.tail e, H.head e]) := by
      change (if he : e.1 ∈ E(H.toGraph) then _ else _) = _
      rw [dite_eq_left e.2]
    have hμG : PG.μ (ηe e.1) =
        (if G.tail ⟨ηe e.1, he'⟩ = G.head ⟨ηe e.1, he'⟩ then [G.tail ⟨ηe e.1, he'⟩]
          else [G.tail ⟨ηe e.1, he'⟩, G.head ⟨ηe e.1, he'⟩]) := by
      change (if he : ηe e.1 ∈ E(G.toGraph) then _ else _) = _
      rw [dite_eq_left he']
    have hr : 0 < (PH.μ e.1).length := by rw [hμH]; split_ifs <;> simp
    have hr' : 0 < (PG.μ (ηe e.1)).length := hexp.μ_length e.1 ((hdomH e.1).mpr e.2) ▸ hr
    have h0H : (PH.μ e.1)[0] = H.tail e := by
      revert hr; rw [hμH]; split_ifs <;> intro _ <;> rfl
    have h0G : (PG.μ (ηe e.1))[0] = G.tail ⟨ηe e.1, he'⟩ := by
      revert hr'; rw [hμG]; split_ifs <;> intro _ <;> rfl
    have hmem0 := hexp.μ_mem e.1 ((hdomH e.1).mpr e.2) 0 hr hr'
    have htail : G.tail ⟨ηe e.1, he'⟩ ∈ ηv (H.tail e) := by rwa [h0H, h0G] at hmem0
    refine ⟨htail, ?_⟩
    have hlen : (PH.μ e.1).length = (PG.μ (ηe e.1)).length :=
      hexp.μ_length e.1 ((hdomH e.1).mpr e.2)
    by_cases hH : H.tail e = H.head e
    · have hlenH : (PH.μ e.1).length = 1 := by simp [hμH, hH]
      have hG : G.tail ⟨ηe e.1, he'⟩ = G.head ⟨ηe e.1, he'⟩ := by
        simpa [hμG, apply_ite List.length] using hlen.symm.trans hlenH
      simpa only [hH, hG] using htail
    · have hlenH : (PH.μ e.1).length = 2 := by simp [hμH, hH]
      have hG : G.tail ⟨ηe e.1, he'⟩ ≠ G.head ⟨ηe e.1, he'⟩ := by
        simpa [hμG, apply_ite List.length] using hlen.symm.trans hlenH
      have hr : 1 < (PH.μ e.1).length := by omega
      have hr' : 1 < (PG.μ (ηe e.1)).length := hlen ▸ hr
      have h1H : (PH.μ e.1)[1] = H.head e := by
        revert hr; rw [hμH, ite_eq_right hH]; intro _; rfl
      have h1G : (PG.μ (ηe e.1))[1] = G.head ⟨ηe e.1, he'⟩ := by
        revert hr'; rw [hμG, ite_eq_right hG]; intro _; rfl
      have hmem1 := hexp.μ_mem e.1 ((hdomH e.1).mpr e.2) 1 hr hr'
      rwa [h1H, h1G] at hmem1
  exact ⟨ηv, ηe, hm, fun e ↦ (hends e).1, fun e ↦ (hends e).2⟩

/-! ### Isomorphism with a finite directed graph on `ℕ` and transport of `IsIsoMinor` -/

/-- Every finite directed graph is isomorphic to a finite directed graph on `ℕ`. -/
theorem exists_digraph_iso_nat (G : Digraph α β) (hV : V(G.toGraph).Finite)
    (hE : E(G.toGraph).Finite) :
    ∃ G' : Digraph ℕ ℕ, V(G'.toGraph).Finite ∧ E(G'.toGraph).Finite ∧
      Nonempty (Digraph.Iso G G') := by
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_injOn.mp hV.countable
  obtain ⟨g, hg⟩ := Set.countable_iff_exists_injOn.mp hE.countable
  let G₀ : Graph ℕ ℕ :=
    { vertexSet := f '' V(G.toGraph)
      IsLink := fun e x y ↦
        ∃ e₀ x₀ y₀, G.toGraph.IsLink e₀ x₀ y₀ ∧ g e₀ = e ∧ f x₀ = x ∧ f y₀ = y
      isLink_symm := fun _ _ ↦
        ⟨fun _ _ ⟨e₀, x₀, y₀, h, h₁, h₂, h₃⟩ ↦ ⟨e₀, y₀, x₀, h.symm, h₁, h₃, h₂⟩⟩
      eq_or_eq_of_isLink_of_isLink := by
        rintro _ _ _ _ _ ⟨e₀, x₀, y₀, h, rfl, rfl, rfl⟩ ⟨e₁, x₁, y₁, h', he, rfl, rfl⟩
        obtain rfl := hg h'.edge_mem h.edge_mem he
        rcases h.left_eq_or_eq h' with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      left_mem_of_isLink := by
        rintro _ _ _ ⟨e₀, x₀, y₀, h, -, rfl, -⟩
        exact ⟨x₀, h.left_mem, rfl⟩ }
  have hEG₀ : E(G₀) = g '' E(G.toGraph) := by
    ext e
    change (∃ x y, G₀.IsLink e x y) ↔ _
    constructor
    · rintro ⟨_, _, e₀, x₀, y₀, h, rfl, -⟩
      exact ⟨e₀, h.edge_mem, rfl⟩
    · rintro ⟨e₀, he, rfl⟩
      obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
      exact ⟨_, _, e₀, x, y, h, rfl, rfl, rfl⟩
  have hbijE : BijOn g E(G.toGraph) E(G₀) := hEG₀ ▸ hg.bijOn_image
  let eE : E(G.toGraph) ≃ E(G₀) := hbijE.equiv g
  let eV : V(G.toGraph) ≃ V(G₀) := (hf.bijOn_image).equiv f
  let G' : Digraph ℕ ℕ :=
    { toGraph := G₀
      tail := fun e ↦ f (G.tail (eE.symm e))
      head := fun e ↦ f (G.head (eE.symm e))
      isLink_of_mem := fun e ↦ by
        let e₀ := eE.symm e
        have he₀ : g e₀.1 = e.1 := congrArg Subtype.val (eE.apply_symm_apply e)
        exact ⟨e₀.1, G.tail e₀, G.head e₀, G.isLink_of_mem e₀, he₀, rfl, rfl⟩ }
  refine ⟨G', hV.image f, hEG₀ ▸ hE.image g, ⟨?_⟩⟩
  refine
    { vertexEquiv := eV
      edgeEquiv := eE
      isLink_iff := by
        rintro ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩
        constructor
        · intro h
          exact ⟨e, x, y, h, rfl, rfl, rfl⟩
        · rintro ⟨e₀, x₀, y₀, h, h₁, h₂, h₃⟩
          have h₄ : e₀ = e := hg h.edge_mem he h₁
          have h₅ : x₀ = x := hf h.left_mem hx h₂
          have h₆ : y₀ = y := hf h.right_mem hy h₃
          subst h₄ h₅ h₆
          exact h
      tail_eq := fun e ↦ by
        change f (G.tail e) = f (G.tail (eE.symm (eE e)))
        rw [Equiv.symm_apply_apply]
      head_eq := fun e ↦ by
        change f (G.head e) = f (G.head (eE.symm (eE e)))
        rw [Equiv.symm_apply_apply] }

/-- Transport a directed minor model `(ηv', ηe')` of `H'` in `G'` along isomorphisms
`φH : H.Iso H'` and `φG : G.Iso G'` when `H` and `G` share the same edge type `β`. -/
theorem IsDirMinorModel.transport_iso {H G : Digraph α β} {H' G' : Digraph α' β'}
    {ηv' : α' → Set α'} {ηe' : β' → β'} (hm : IsDirMinorModel H' G' ηv' ηe')
    (φH : Digraph.Iso H H') (φG : Digraph.Iso G G') :
    ∃ (ηv : α → Set α) (ηe : β → β), IsDirMinorModel H G ηv ηe := by
  classical
  let ηv : α → Set α := fun v ↦
    if hv : v ∈ V(H.toGraph) then
      {x ∈ V(G.toGraph) | ∃ hx : x ∈ V(G.toGraph),
        (φG.vertexEquiv ⟨x, hx⟩).1 ∈ ηv' (φH.vertexEquiv ⟨v, hv⟩).1}
    else ∅
  let ηe : β → β := fun e ↦
    if he : e ∈ E(H.toGraph) then
      (φG.edgeEquiv.symm ⟨ηe' (φH.edgeEquiv ⟨e, he⟩).1,
        hm.edge_mem _ (φH.edgeEquiv ⟨e, he⟩).2⟩).1
    else e
  have hηv_mem : ∀ {v : α} (hv : v ∈ V(H.toGraph)) {x : α},
      x ∈ ηv v ↔ ∃ hx : x ∈ V(G.toGraph),
        (φG.vertexEquiv ⟨x, hx⟩).1 ∈ ηv' (φH.vertexEquiv ⟨v, hv⟩).1 := by
    intro v hv x
    simp [ηv, hv]
  have hηe_eq : ∀ (e : E(H.toGraph)),
      (⟨ηe e.1, by
        simp only [ηe, dite_eq_left e.2]
        exact (φG.edgeEquiv.symm _).2⟩ : E(G.toGraph)) =
      φG.edgeEquiv.symm ⟨ηe' (φH.edgeEquiv e).1, hm.edge_mem _ (φH.edgeEquiv e).2⟩ := by
    intro e
    apply Subtype.ext
    simp [ηe, e.2]
  have hηe_mem : ∀ e ∈ E(H.toGraph), ηe e ∈ E(G.toGraph) := by
    intro e he
    simp only [ηe, dite_eq_left he]
    exact (φG.edgeEquiv.symm _).2
  have hφG_ηe : ∀ (e : E(H.toGraph)),
      φG.edgeEquiv ⟨ηe e.1, hηe_mem e.1 e.2⟩ =
        ⟨ηe' (φH.edgeEquiv e).1, hm.edge_mem _ (φH.edgeEquiv e).2⟩ := by
    intro e
    rw [hηe_eq e, Equiv.apply_symm_apply]
  have hinc_G : ∀ {f : β} {x : α} (hf : f ∈ E(G.toGraph)) (hx : x ∈ V(G.toGraph)),
      G.toGraph.Inc f x ↔ G'.toGraph.Inc (φG.edgeEquiv ⟨f, hf⟩).1 (φG.vertexEquiv ⟨x, hx⟩).1 := by
    intro f x hf hx
    constructor
    · rintro ⟨y, hl⟩
      exact ⟨(φG.vertexEquiv ⟨y, hl.right_mem⟩).1,
        (φG.isLink_iff ⟨f, hf⟩ ⟨x, hx⟩ ⟨y, hl.right_mem⟩).1 hl⟩
    · rintro ⟨y', hl'⟩
      obtain ⟨⟨y, hy⟩, hy_eq⟩ := φG.vertexEquiv.surjective ⟨y', hl'.right_mem⟩
      have hl'' : G'.toGraph.IsLink (φG.edgeEquiv ⟨f, hf⟩).1 (φG.vertexEquiv ⟨x, hx⟩).1
          (φG.vertexEquiv ⟨y, hy⟩).1 := by
        rwa [congrArg Subtype.val hy_eq]
      exact ⟨y, (φG.isLink_iff ⟨f, hf⟩ ⟨x, hx⟩ ⟨y, hy⟩).2 hl''⟩
  have hinc_H : ∀ {e : β} {v : α} (he : e ∈ E(H.toGraph)) (hv : v ∈ V(H.toGraph)),
      H.toGraph.Inc e v ↔ H'.toGraph.Inc (φH.edgeEquiv ⟨e, he⟩).1 (φH.vertexEquiv ⟨v, hv⟩).1 := by
    intro e v he hv
    constructor
    · rintro ⟨w, hl⟩
      exact ⟨(φH.vertexEquiv ⟨w, hl.right_mem⟩).1,
        (φH.isLink_iff ⟨e, he⟩ ⟨v, hv⟩ ⟨w, hl.right_mem⟩).1 hl⟩
    · rintro ⟨w', hl'⟩
      obtain ⟨⟨w, hw⟩, hw_eq⟩ := φH.vertexEquiv.surjective ⟨w', hl'.right_mem⟩
      have hl'' : H'.toGraph.IsLink (φH.edgeEquiv ⟨e, he⟩).1 (φH.vertexEquiv ⟨v, hv⟩).1
          (φH.vertexEquiv ⟨w, hw⟩).1 := by
        rwa [congrArg Subtype.val hw_eq]
      exact ⟨w, (φH.isLink_iff ⟨e, he⟩ ⟨v, hv⟩ ⟨w, hw⟩).2 hl''⟩
  refine ⟨ηv, ηe,
    { vertex_nonempty := fun v hv ↦ by
        obtain ⟨x', hx'⟩ := hm.vertex_nonempty _ (φH.vertexEquiv ⟨v, hv⟩).2
        have hx'G' : x' ∈ V(G'.toGraph) :=
          hm.vertex_subset _ (φH.vertexEquiv ⟨v, hv⟩).2 hx'
        obtain ⟨⟨x, hx⟩, hx_eq⟩ := φG.vertexEquiv.surjective ⟨x', hx'G'⟩
        refine ⟨x, (hηv_mem hv).2 ⟨hx, ?_⟩⟩
        rwa [congrArg Subtype.val hx_eq]
      vertex_subset := fun v hv x hx ↦ ((hηv_mem hv).1 hx).1
      edge_mem := hηe_mem
      vertex_disjoint := fun v₁ hv₁ v₂ hv₂ hne ↦ by
        rw [disjoint_left]
        intro x hx₁ hx₂
        obtain ⟨hx, hx₁'⟩ := (hηv_mem hv₁).1 hx₁
        obtain ⟨_, hx₂'⟩ := (hηv_mem hv₂).1 hx₂
        have hne' : (φH.vertexEquiv ⟨v₁, hv₁⟩).1 ≠ (φH.vertexEquiv ⟨v₂, hv₂⟩).1 := fun h ↦
          hne (Subtype.mk.inj (φH.vertexEquiv.injective (Subtype.ext h)))
        exact (hm.vertex_disjoint _ (φH.vertexEquiv ⟨v₁, hv₁⟩).2
          _ (φH.vertexEquiv ⟨v₂, hv₂⟩).2 hne').notMem_of_mem_left hx₁' hx₂'
      edge_injOn := fun e₁ he₁ e₂ he₂ heq ↦ by
        have hsub : (⟨ηe e₁, hηe_mem e₁ he₁⟩ : E(G.toGraph)) = ⟨ηe e₂, hηe_mem e₂ he₂⟩ :=
          Subtype.ext heq
        have h₁ := congrArg φG.edgeEquiv hsub
        rw [hφG_ηe ⟨e₁, he₁⟩, hφG_ηe ⟨e₂, he₂⟩] at h₁
        have h₂ := hm.edge_injOn (φH.edgeEquiv ⟨e₁, he₁⟩).2 (φH.edgeEquiv ⟨e₂, he₂⟩).2
          (congrArg Subtype.val h₁)
        exact Subtype.mk.inj (φH.edgeEquiv.injective (Subtype.ext h₂))
      inc_iff := fun v hv e he ↦ by
        rw [hinc_H he hv,
          hm.inc_iff _ (φH.vertexEquiv ⟨v, hv⟩).2 _ (φH.edgeEquiv ⟨e, he⟩).2]
        constructor
        · rintro ⟨x', hx', hinc'⟩
          have hx'G' : x' ∈ V(G'.toGraph) :=
            hm.vertex_subset _ (φH.vertexEquiv ⟨v, hv⟩).2 hx'
          obtain ⟨⟨x, hx⟩, hx_eq⟩ := φG.vertexEquiv.surjective ⟨x', hx'G'⟩
          have hx_val : (φG.vertexEquiv ⟨x, hx⟩).1 = x' := congrArg Subtype.val hx_eq
          refine ⟨x, (hηv_mem hv).2 ⟨hx, hx_val.symm ▸ hx'⟩, ?_⟩
          rw [hinc_G (hηe_mem e he) hx, hφG_ηe ⟨e, he⟩, hx_val]
          exact hinc'
        · rintro ⟨x, hx, hinc⟩
          obtain ⟨hxG, hx'⟩ := (hηv_mem hv).1 hx
          refine ⟨(φG.vertexEquiv ⟨x, hxG⟩).1, hx', ?_⟩
          have := (hinc_G (hηe_mem e he) hxG).1 hinc
          rwa [hφG_ηe ⟨e, he⟩] at this
      isLoopAt_iff := fun v hv e he ↦ by
        have hloop_H : H.toGraph.IsLoopAt e v ↔
            H'.toGraph.IsLoopAt (φH.edgeEquiv ⟨e, he⟩).1 (φH.vertexEquiv ⟨v, hv⟩).1 :=
          φH.isLink_iff ⟨e, he⟩ ⟨v, hv⟩ ⟨v, hv⟩
        rw [hloop_H,
          hm.isLoopAt_iff _ (φH.vertexEquiv ⟨v, hv⟩).2 _ (φH.edgeEquiv ⟨e, he⟩).2]
        constructor
        · intro hall x hinc
          have hxG : x ∈ V(G.toGraph) := hinc.vertex_mem
          have hinc' := (hinc_G (hηe_mem e he) hxG).1 hinc
          rw [hφG_ηe ⟨e, he⟩] at hinc'
          exact (hηv_mem hv).2 ⟨hxG, hall _ hinc'⟩
        · intro hall x' hinc'
          have hx'G' : x' ∈ V(G'.toGraph) := hinc'.vertex_mem
          obtain ⟨⟨x, hx⟩, hx_eq⟩ := φG.vertexEquiv.surjective ⟨x', hx'G'⟩
          have hx_val : (φG.vertexEquiv ⟨x, hx⟩).1 = x' := congrArg Subtype.val hx_eq
          have hinc : G.toGraph.Inc (ηe e) x := by
            rw [hinc_G (hηe_mem e he) hx, hφG_ηe ⟨e, he⟩, hx_val]
            exact hinc'
          obtain ⟨_, hx'⟩ := (hηv_mem hv).1 (hall x hinc)
          rwa [← hx_val]
      connected := fun v hv ↦ by
        obtain ⟨K', hK'_le, hK'_V, hK'_conn⟩ :=
          hm.connected _ (φH.vertexEquiv ⟨v, hv⟩).2
        let K : Graph α β := (G.toGraph.deleteEdges (ηe '' E(H.toGraph))).induce (ηv v)
        have hK_le : K ≤ G.toGraph.deleteEdges (ηe '' E(H.toGraph)) :=
          Graph.induce_le fun x hx ↦ ((hηv_mem hv).1 hx).1
        obtain ⟨r', hr'⟩ := hK'_conn.1
        have hr'η : r' ∈ ηv' (φH.vertexEquiv ⟨v, hv⟩).1 := hK'_V ▸ hr'
        have hr'G' : r' ∈ V(G'.toGraph) :=
          hm.vertex_subset _ (φH.vertexEquiv ⟨v, hv⟩).2 hr'η
        obtain ⟨⟨r, hrG⟩, hr_eq⟩ := φG.vertexEquiv.surjective ⟨r', hr'G'⟩
        have hr_val : (φG.vertexEquiv ⟨r, hrG⟩).1 = r' := congrArg Subtype.val hr_eq
        have hrη : r ∈ ηv v := (hηv_mem hv).2 ⟨hrG, hr_val.symm ▸ hr'η⟩
        refine ⟨K, hK_le, rfl, ⟨r, hrη⟩, fun x hx y hy ↦ ?_⟩
        obtain ⟨hxG, hx'⟩ := (hηv_mem hv).1 hx
        obtain ⟨hyG, hy'⟩ := (hηv_mem hv).1 hy
        have hwalk := hK'_conn.2 (φG.vertexEquiv ⟨x, hxG⟩).1 (hK'_V.symm ▸ hx')
          (φG.vertexEquiv ⟨y, hyG⟩).1 (hK'_V.symm ▸ hy')
        have hstep : ∀ {a' b' : α'}, ReflTransGen K'.Adj a' b' →
            ∀ {a b : α} (ha : a ∈ V(G.toGraph)) (hb : b ∈ V(G.toGraph)),
            (φG.vertexEquiv ⟨a, ha⟩).1 = a' → (φG.vertexEquiv ⟨b, hb⟩).1 = b' →
            ReflTransGen K.Adj a b := by
          intro a' b' hab'
          induction hab' with
          | refl =>
            intro a b ha hb ha_eq hb_eq
            have hsub : (⟨a, ha⟩ : V(G.toGraph)) = ⟨b, hb⟩ :=
              φG.vertexEquiv.injective (Subtype.ext (ha_eq.trans hb_eq.symm))
            exact Subtype.mk.inj hsub ▸ .refl
          | @tail c' d' h₁ hcd' ih =>
            intro a b ha hb ha_eq hb_eq
            obtain ⟨f', hlK'⟩ := hcd'
            have hc'η : c' ∈ ηv' (φH.vertexEquiv ⟨v, hv⟩).1 := hK'_V ▸ hlK'.left_mem
            have hd'η : d' ∈ ηv' (φH.vertexEquiv ⟨v, hv⟩).1 := hK'_V ▸ hlK'.right_mem
            have hc'G' : c' ∈ V(G'.toGraph) :=
              hm.vertex_subset _ (φH.vertexEquiv ⟨v, hv⟩).2 hc'η
            obtain ⟨⟨c, hcG⟩, hc_eq⟩ := φG.vertexEquiv.surjective ⟨c', hc'G'⟩
            have hc_val : (φG.vertexEquiv ⟨c, hcG⟩).1 = c' := congrArg Subtype.val hc_eq
            have hlD' := hlK'.mono hK'_le
            rw [deleteEdges_isLink] at hlD'
            obtain ⟨hlG', hf'_not⟩ := hlD'
            obtain ⟨⟨f, hfG⟩, hf_eq⟩ := φG.edgeEquiv.surjective ⟨f', hlG'.edge_mem⟩
            have hf_val : (φG.edgeEquiv ⟨f, hfG⟩).1 = f' := congrArg Subtype.val hf_eq
            have hlG : G.toGraph.IsLink f c b := by
              apply (φG.isLink_iff ⟨f, hfG⟩ ⟨c, hcG⟩ ⟨b, hb⟩).2
              rwa [hf_val, hc_val, hb_eq]
            have hf_not : f ∉ ηe '' E(H.toGraph) := by
              rintro ⟨e, he, rfl⟩
              apply hf'_not
              refine ⟨(φH.edgeEquiv ⟨e, he⟩).1, (φH.edgeEquiv ⟨e, he⟩).2, ?_⟩
              have := congrArg Subtype.val (hφG_ηe ⟨e, he⟩)
              exact this.symm.trans hf_val
            have hcη : c ∈ ηv v := (hηv_mem hv).2 ⟨hcG, hc_val.symm ▸ hc'η⟩
            have hbη : b ∈ ηv v := (hηv_mem hv).2 ⟨hb, hb_eq.symm ▸ hd'η⟩
            have hadj : K.Adj c b := ⟨f, (deleteEdges_isLink ..).mpr ⟨hlG, hf_not⟩, hcη, hbη⟩
            exact (ih ha hcG ha_eq hc_val).tail hadj
        exact hstep hwalk hxG hyG rfl rfl },
    fun e ↦ ?_, fun e ↦ ?_⟩
  · refine (hηv_mem (H.tail_mem e)).2 ⟨G.tail_mem ⟨ηe e.1, hηe_mem e.1 e.2⟩, ?_⟩
    rw [φG.tail_eq ⟨ηe e.1, hηe_mem e.1 e.2⟩, φH.tail_eq e]
    have h₁ : G'.tail (φG.edgeEquiv ⟨ηe e.1, hηe_mem e.1 e.2⟩) =
        G'.tail ⟨ηe' (φH.edgeEquiv e).1, hm.edge_mem _ (φH.edgeEquiv e).2⟩ := by
      congr 1
      exact hφG_ηe e
    rw [h₁]
    exact hm.tail_mem (φH.edgeEquiv e)
  · refine (hηv_mem (H.head_mem e)).2 ⟨G.head_mem ⟨ηe e.1, hηe_mem e.1 e.2⟩, ?_⟩
    rw [φG.head_eq ⟨ηe e.1, hηe_mem e.1 e.2⟩, φH.head_eq e]
    have h₁ : G'.head (φG.edgeEquiv ⟨ηe e.1, hηe_mem e.1 e.2⟩) =
        G'.head ⟨ηe' (φH.edgeEquiv e).1, hm.edge_mem _ (φH.edgeEquiv e).2⟩ := by
      congr 1
      exact hφG_ηe e
    rw [h₁]
    exact hm.head_mem (φH.edgeEquiv e)

end GraphMinor.GM20
