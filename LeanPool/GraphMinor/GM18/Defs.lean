/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Axioms
public import LeanPool.GraphMinor.GM04.Higman
public import LeanPool.GraphMinor.GM04.Patchwork.Defs
public import LeanPool.GraphMinor.GM10.Defs2
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.WithBot
import LeanPool.GraphMinor.GM04.Decomposition.Basic

/-!
# Definitions for Graph Minors XVIII: Tree-decompositions and well-quasi-ordering

This file formalizes the definitions of Sections 2–7 of Robertson and Seymour,
*Graph Minors. XVIII. Tree-decompositions and well-quasi-ordering*, J. Combin. Theory Ser. B 89
(2003) 77–108.

Where Graph Minors XVIII reuses a notion from Graph Minors IV or Graph Minors X with the same
meaning, we use the interface definition directly (`Hypergraph`, `RootedHypergraph`,
`GM10.IsTreeDecomposition`, `GM10.IsTangle`, `GM10.IsLocation`, `GM10.locationCore`,
`GM10.IsTieBreaker`, `GM10.IsDistinction`, `GM10.IsRobust`, `GM10.IsTitanic`, `GM04.Patch`,
`GM04.Patchwork`, `GM04.RootedTree`, etc.).

Where Graph Minors XVIII introduces a new notion or uses a term in a sense different from
Graph Minors IV or X, it is defined in the `GraphMinor.GM18` namespace:
* Section 2 (pages 78–82): `vertexLocation`, `IsProper`, `IsStandardDecomposition`, `IsRotund`
  (unrooted rotund tree-decompositions, distinct from `GM04.IsRotund`).
* Section 3 (pages 82–84): `IsLinkedTo` (a separation linked to a tangle, distinct from
  `GM04.IsLinked`), `locationOrder`, `locationHeart`, `locationTreeWidth`.
* Section 4 (pages 85–89): `Isolates` (`θ`-isolation of a tangle by a location),
  `IsLocationEnlargement`, `IsLocationEnlargementByTreeWidth` (enlargement of locations, distinct
  from `GM10.IsEnlargement` of designs).
* Section 5 (pages 89–100): `UnlabeledPatchwork`, `PartialPatchwork`, `PartialPatchwork.domφ`,
  `PartialPatchwork.IsTotal`, `ConnectedIn`, `IsFeasibleGrouping`, `feasibleGroupings` (`gr(P)`),
  `IsComplemented`, `complement` (`G \ A`), `IsRootedLocation`, `rootedLocationToLocation` (`ℒ⁻`),
  `rootedLocationCore` (`M(G, ℒ)`), `IsPatchworkHeart`, `HasPatchworkHeart`, `IsPartialPlace`,
  `IsOmegaPlace`, `IsPlaceHeart`, `HasPlaceHeart`, `HasPatchworkTreeWidthLE`,
  `IsPlaceEnlargementByTreeWidth`.
* Section 6 (pages 100–107): `DisjointUnionPreorder`, `IsCompletion`, `WellBehaved`, `IsRootless`,
  `IsRooting`, `IsPlaceEnlargementByClass`, `enlargementClass`, `arborescenceUnderlying`,
  `IsRootedDecomposition`, `rootedDecompRootSide` (`τ × (T, f)`), `IsPiece`.
* Section 7 (pages 107–108): `IsLambdaLinkedTo` (`λ`-linked to a tangle `𝒯`).
-/

@[expose] public section

namespace GraphMinor.GM18

open Hypergraph SimpleGraph

universe u v w

variable {α : Type u} {β : Type v} {Ω : Type w} {ι : Type*}

/-! ## Section 2: Hypergraphs, Tree-Decompositions and Tangles -/

/-- The location of a vertex `t₀ ∈ V(T)` in a tree-decomposition `(T, τ)` of a hypergraph `G`
(Graph Minors XVIII, Section 2, (2.4), page 80):
"**2.4.** *Let $(T, \tau)$ be a tree-decomposition of a hypergraph $G$, let $t_0 \in V(T)$ and let
$e_1, \dots, e_k$ be the edges of $T$ incident with $t_0$. For $1 \le i \le k$ let the components
of $T \setminus e_i$ be $T_i, T'_i$, where $t_0 \in V(T'_i)$. Then*
$$\{(\tau \times T_i, \tau \times T'_i): 1 \le i \le k\}$$
*is a location.* We call this the *location of $t_0$ in $(T, \tau)$*." -/
def vertexLocation [Fintype ι] (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (t₀ : ι) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p | ∃ u : ι, T.Adj t₀ u ∧
    p = (GM10.treeDecompSide T τ s(u, t₀) u, GM10.treeDecompSide T τ s(u, t₀) t₀)}

/-- A tree-decomposition `(T, τ)` of a hypergraph `G` is proper
(Graph Minors XVIII, Section 2, page 80):
"We say $(T, \tau)$ is *proper* if no edge of $T$ makes a separation $(A, B)$ with $B = G$." -/
def IsProper [Fintype ι] (G : Hypergraph α β) (T : SimpleGraph ι)
    (τ : ι → Hypergraph α β) : Prop :=
  ∀ ⦃e : Sym2 ι⦄, e ∈ T.edgeSet → ∀ ⦃A B : Hypergraph α β⦄,
    GM10.MakesSeparation T τ e A B → B ≠ G

/-- A standard decomposition `(T, τ)` of `G` relative to distinct tangles `𝒯₁, …, 𝒯ₙ` of the same
order `θ` (Graph Minors XVIII, Section 2, (2.6), page 81):
"Let $\mathscr{T}_1, \dots, \mathscr{T}_n$ be distinct tangles of order $\theta$ in a
hypergraph $G$ with $n \ge 1$, and let $\lambda$ be a tie-breaker. Then there is a
tree-decomposition $(T, \tau)$ of $G$ where $V(T) = \{t_1, \dots, t_n\}$, with the following
properties:* 1. *if $e \in E(T)$ and $T_1, T_2$ are the components of $T \setminus e$ and $1
\le i \le n$ and $t_i \in V(T_2)$ then $(\tau \times T_1, \tau \times T_2) \in
\mathscr{T}_i$,* 2. *for $1 \le i < j \le n$, let $e$ be the edge of the path of $T$ between
$t_i, t_j$ making separations of minimum $\lambda$-order; then these separations are the
$(\mathscr{T}_i, \mathscr{T}_j)$- and $(\mathscr{T}_j, \mathscr{T}_i)$-distinctions.* We
call $(T, \tau)$ a *standard decomposition* of $G$ relative to $\mathscr{T}_1, \dots,
\mathscr{T}_n$ in which $t_i$ represents $\mathscr{T}_i$ for $i = 1, \dots, n$." -/
structure IsStandardDecomposition {n : ℕ} {Λ : Type*} [LinearOrder Λ]
    (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → Λ)
    (𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β))
    (T : SimpleGraph (Fin n)) (τ : Fin n → Hypergraph α β) : Prop where
  /-- `(T, τ)` is a tree-decomposition of `G`. -/
  isTreeDecomposition : GM10.IsTreeDecomposition G T τ
  /-- (2.6.1) If `e = s(u, v) ∈ E(T)` and `i` lies in the component of `T \ e` containing `v`, then
  `(τ × T_u, τ × T_v) ∈ 𝒯 i`. -/
  side_mem_tangle : ∀ (i u v : Fin n), T.Adj u v →
    (T.deleteEdges {s(u, v)}).Reachable v i →
    (GM10.treeDecompSide T τ s(u, v) u, GM10.treeDecompSide T τ s(u, v) v) ∈ 𝒯 i
  /-- (2.6.2) For `i ≠ j`, the edge on the path in `T` between `i` and `j` making separations of
  minimum `λ`-order makes the `(𝒯 i, 𝒯 j)`- and `(𝒯 j, 𝒯 i)`-distinctions. -/
  path_min_isDistinction : ∀ ⦃i j : Fin n⦄, i ≠ j →
    ∃ e ∈ T.edgeSet,
      (∀ p : T.Walk i j, p.IsPath → e ∈ p.edges) ∧
      (∀ e' ∈ T.edgeSet, (∀ p : T.Walk i j, p.IsPath → e' ∈ p.edges) →
        ∀ A B A' B', GM10.MakesSeparation T τ e A B → GM10.MakesSeparation T τ e' A' B' →
          lam (A, B) ≤ lam (A', B')) ∧
      ∃ A B, GM10.MakesSeparation T τ e A B ∧
        GM10.IsDistinction lam (𝒯 i) (𝒯 j) A B ∧ GM10.IsDistinction lam (𝒯 j) (𝒯 i) B A

/-- An unrooted tree-decomposition `(T, τ)` of a hypergraph `G` is rotund in the sense of
Graph Minors XVIII (Section 2, page 81; contrast with `GM04.IsRotund` for rooted trees, which
Section 6, page 102 relates to this notion):
"A tree-decomposition $(T, \tau)$ of a hypergraph $G$ is *rotund* if for every two edges
$f_1, f_2 \in E(T)$, making separations $(A_1, B_1)$ and $(A_2, B_2)$ of the same order $k$,
where $B_2 \subseteq A_1$ and $B_1 \subseteq A_2$, the following holds: if there is a
separation $(H_1, H_2)$ of $G$ with $B_1 \subseteq H_1$ and $B_2 \subseteq H_2$ of order $<
k$, then some edge of $F$ makes a separation of order $< k$, where $F$ is the path of $T$
with first and last edges $f_1, f_2$."

In a tree `T`, a simple path `p : T.Walk t₁ t₂` (`p.IsPath`) has first edge `f₁` and last edge `f₂`
if and only if `t₁ ∈ f₁`, `t₂ ∈ f₂`, `f₁ ∈ p.edges`, and `f₂ ∈ p.edges`. -/
def IsRotund [Fintype ι] (G : Hypergraph α β) (T : SimpleGraph ι)
    (τ : ι → Hypergraph α β) : Prop :=
  ∀ ⦃t₁ t₂ : ι⦄ (p : T.Walk t₁ t₂), p.IsPath →
    ∀ ⦃f₁ f₂ : Sym2 ι⦄, t₁ ∈ f₁ → t₂ ∈ f₂ → f₁ ∈ p.edges → f₂ ∈ p.edges →
    ∀ ⦃A₁ B₁ A₂ B₂ : Hypergraph α β⦄,
      GM10.MakesSeparation T τ f₁ A₁ B₁ →
      GM10.MakesSeparation T τ f₂ A₂ B₂ →
      B₂ ≤ A₁ → B₁ ≤ A₂ →
      separationOrder A₁ B₁ = separationOrder A₂ B₂ →
      (∃ H₁ H₂ : Hypergraph α β, G.IsSeparation H₁ H₂ ∧ B₁ ≤ H₁ ∧ B₂ ≤ H₂ ∧
        separationOrder H₁ H₂ < separationOrder A₁ B₁) →
      ∃ e ∈ p.edges, ∃ C D : Hypergraph α β,
        GM10.MakesSeparation T τ e C D ∧ separationOrder C D < separationOrder A₁ B₁

/-! ## Section 3: Tree-Width of a Location -/

/-- A separation `(A, B) ∈ 𝒯` is linked to a tangle `𝒯`
(Graph Minors XVIII, Section 3, page 82; distinct from `GM04.IsLinked` for edge sets in rooted
tree-decompositions):
"If $\mathscr{T}$ is a tangle in a hypergraph $G$, we say that $(A, B) \in \mathscr{T}$ is
*linked to* $\mathscr{T}$ if there is no $(A', B') \in \mathscr{T}$ of smaller order with
$A \subseteq A'$ and $B' \subseteq B$." -/
def IsLinkedTo (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (A B : Hypergraph α β) : Prop :=
  (A, B) ∈ 𝒯 ∧ ∀ ⦃A' B' : Hypergraph α β⦄, (A', B') ∈ 𝒯 →
    A ≤ A' → B' ≤ B → separationOrder A B ≤ separationOrder A' B'

/-- The order of a location `ℒ` in a hypergraph `G` (Graph Minors XVIII, Section 3, page 83):
"Let $\mathscr{L}$ be a location in $G$. The *order* of $\mathscr{L}$ is the maximum order of
the members of $\mathscr{L}$ (or $0$ if $\mathscr{L} = \emptyset$)." -/
noncomputable def locationOrder (ℒ : Set (Hypergraph α β × Hypergraph α β)) : ℕ :=
  sSup ((fun p : Hypergraph α β × Hypergraph α β ↦ separationOrder p.1 p.2) '' ℒ)

/-- The heart `H` of a location `ℒ` in a hypergraph `G` (Graph Minors XVIII, Section 3, page 83):
"For each $(A, B) \in \mathscr{L}$ let $e(A, B)$ be a new element, and let $H$ be the
hypergraph with $$V(H) = V(M(G, \mathscr{L})),$$ $$E(H) = E(M(G, \mathscr{L})) \cup \{e(A,
B) \colon (A, B) \in \mathscr{L}\},$$ where for $e \in E(M(\mathscr{L}))$ its ends are as in
$G$, and for $(A, B) \in \mathscr{L}$ the ends of $e(A, B)$ are the elements of $V(A \cap
B)$. This is a hypergraph by 2.3.2, and we call it the *heart* of $\mathscr{L}$."

Here the edge type of the heart is `β ⊕ (Hypergraph α β × Hypergraph α β)`, with `Sum.inl e`
for `e ∈ E(M(G, ℒ))` and `Sum.inr (A, B)` for `(A, B) ∈ ℒ`. To ensure that `locationHeart G ℒ` is a
well-defined finite hypergraph for any set `ℒ` without requiring `IsLocation G ℒ` as a dependent
argument, new edges are restricted to separations `(A, B) ∈ ℒ` of `G` satisfying
`V(A ∩ B) ⊆ V(M(G, ℒ))` (which holds for all `(A, B) ∈ ℒ` whenever `IsLocation G ℒ`, by 2.3.2). -/
def locationHeart (G : Hypergraph α β) (ℒ : Set (Hypergraph α β × Hypergraph α β)) :
    Hypergraph α (β ⊕ (Hypergraph α β × Hypergraph α β)) where
  vertexSet := (GM10.locationCore G ℒ).vertexSet
  edgeSet := (Sum.inl '' (GM10.locationCore G ℒ).edgeSet) ∪
    (Sum.inr '' {p ∈ ℒ | G.IsSeparation p.1 p.2 ∧
      (p.1 ∩ p.2).vertexSet ⊆ (GM10.locationCore G ℒ).vertexSet})
  Inc e v :=
    match e with
    | Sum.inl e₀ => (GM10.locationCore G ℒ).Inc e₀ v
    | Sum.inr p => p ∈ ℒ ∧ G.IsSeparation p.1 p.2 ∧
        (p.1 ∩ p.2).vertexSet ⊆ (GM10.locationCore G ℒ).vertexSet ∧ v ∈ (p.1 ∩ p.2).vertexSet
  vertex_mem_of_inc e v h := by
    cases e with
    | inl e₀ => exact (GM10.locationCore G ℒ).vertex_mem_of_inc h
    | inr p => exact h.2.2.1 h.2.2.2
  edge_mem_of_inc e v h := by
    cases e with
    | inl e₀ => exact Or.inl ⟨e₀, (GM10.locationCore G ℒ).edge_mem_of_inc h, rfl⟩
    | inr p => exact Or.inr ⟨p, ⟨h.1, h.2.1, h.2.2.1⟩, rfl⟩
  vertexSet_finite := (GM10.locationCore G ℒ).vertexSet_finite
  edgeSet_finite := by
    refine Set.Finite.union ((GM10.locationCore G ℒ).edgeSet_finite.image Sum.inl) ?_
    refine Set.Finite.image Sum.inr ?_
    have hsub_fin : {H : Hypergraph α β | H ≤ G}.Finite := by
      let f : Hypergraph α β → Set α × Set β := fun H ↦ (H.vertexSet, H.edgeSet)
      have hinj : Set.InjOn f {H : Hypergraph α β | H ≤ G} := by
        rintro H₁ h₁ H₂ h₂ hfeq
        have hV : H₁.vertexSet = H₂.vertexSet := congrArg Prod.fst hfeq
        have hE : H₁.edgeSet = H₂.edgeSet := congrArg Prod.snd hfeq
        apply Hypergraph.ext hV hE
        ext e v
        constructor <;> intro hinc
        · have he₁ : e ∈ H₁.edgeSet := H₁.edge_mem_of_inc hinc
          have he₂ : e ∈ H₂.edgeSet := hE ▸ he₁
          have hG : G.Inc e v := (Set.ext_iff.mp (h₁.ends_eq e he₁) v).mpr hinc
          exact (Set.ext_iff.mp (h₂.ends_eq e he₂) v).mp hG
        · have he₂ : e ∈ H₂.edgeSet := H₂.edge_mem_of_inc hinc
          have he₁ : e ∈ H₁.edgeSet := hE.symm ▸ he₂
          have hG : G.Inc e v := (Set.ext_iff.mp (h₂.ends_eq e he₂) v).mpr hinc
          exact (Set.ext_iff.mp (h₁.ends_eq e he₁) v).mp hG
      have hprod_fin : (G.vertexSet.powerset ×ˢ G.edgeSet.powerset).Finite :=
        G.vertexSet_finite.powerset.prod G.edgeSet_finite.powerset
      have himg_sub : f '' {H : Hypergraph α β | H ≤ G} ⊆
          G.vertexSet.powerset ×ˢ G.edgeSet.powerset := by
        rintro _ ⟨H, hH, rfl⟩
        exact ⟨hH.vertexSet_subset, hH.edgeSet_subset⟩
      exact Set.Finite.of_finite_image (hprod_fin.subset himg_sub) hinj
    refine (hsub_fin.prod hsub_fin).subset ?_
    rintro ⟨A, B⟩ ⟨_, hsep, _⟩
    exact ⟨hsep.left_le, hsep.right_le⟩

/-- The tree-width of a location `ℒ` in a hypergraph `G` (Graph Minors XVIII, Section 3, page 83):
"We define the *tree-width* of $\mathscr{L}$ to be the tree-width of $H$ ... ." -/
noncomputable def locationTreeWidth (G : Hypergraph α β)
    (ℒ : Set (Hypergraph α β × Hypergraph α β)) : ℤ :=
  GM10.treeWidth (locationHeart G ℒ)

/-! ## Section 4: Isolating Locations -/

/-- A location `ℒ` in `G` `θ`-isolates a tangle `𝒯` with respect to a tie-breaker `λ`
(Graph Minors XVIII, Section 4, page 85):
"Let $\mathcal{T}$ be a tangle in a hypergraph $G$, and let $\lambda$ be a tie-breaker in
$G$. A location $\mathcal{L}$ is said to $\theta$-isolate $\mathcal{T}$ if $\mathcal{L}
\subseteq \mathcal{T}$ and has order $<\theta$, and for every $(C, D) \in \mathcal{L}$ and
every tangle $\mathcal{T}'$ in $G$ of order $\ge \theta$ with $(D, C) \in \mathcal{T}'$, if
$(A, B)$ is the $(\mathcal{T}, \mathcal{T}')$-distinction then $A \subseteq C$ and $D
\subseteq B$." -/
structure Isolates {Λ : Type*} [LE Λ] (G : Hypergraph α β)
    (lam : Hypergraph α β × Hypergraph α β → Λ) (θ : ℕ)
    (𝒯 ℒ : Set (Hypergraph α β × Hypergraph α β)) : Prop where
  /-- `ℒ` is a location in `G`. -/
  isLocation : GM10.IsLocation G ℒ
  /-- `ℒ ⊆ 𝒯`. -/
  subset : ℒ ⊆ 𝒯
  /-- `ℒ` has order `< θ` (so `1 ≤ θ` and every `(C, D) ∈ ℒ` has order `< θ`). -/
  locationOrder_lt : locationOrder ℒ < θ
  /-- Every `(C, D) ∈ ℒ` has order `< θ`. -/
  order_lt : ∀ ⦃C D : Hypergraph α β⦄, (C, D) ∈ ℒ → separationOrder C D < θ
  /-- For every `(C, D) ∈ ℒ` and every tangle `𝒯'` of order `≥ θ` with `(D, C) ∈ 𝒯'`, the
  `(𝒯, 𝒯')`-distinction `(A, B)` satisfies `A ⊆ C` and `D ⊆ B`. -/
  distinction_le : ∀ ⦃C D : Hypergraph α β⦄, (C, D) ∈ ℒ →
    ∀ ⦃θ' : ℕ⦄ ⦃𝒯' : Set (Hypergraph α β × Hypergraph α β)⦄,
      GM10.IsTangle G θ' 𝒯' → θ ≤ θ' → (D, C) ∈ 𝒯' →
      ∀ ⦃A B : Hypergraph α β⦄, GM10.IsDistinction lam 𝒯 𝒯' A B →
        A ≤ C ∧ D ≤ B

/-- A location `ℒ*` is an enlargement of a location `ℒ` in `G` via a partition `part` indexed by
`p ∈ ℒ` (Graph Minors XVIII, Section 4, pages 86–87; distinct from `GM10.IsEnlargement` of
designs):
"Let $\mathcal{L}, \mathcal{L}^*$ be locations in a hypergraph $G$, and let $\mathcal{L} =
\{(C_1, D_1), \dots, (C_k, D_k)\}$. We say that $\mathcal{L}^*$ is an *enlargement* of
$\mathcal{L}$ if there exist $\mathcal{L}_1, \dots, \mathcal{L}_k \subseteq \mathcal{L}^*$,
mutually disjoint (possibly empty) and with union $\mathcal{L}^*$, such that for $1 \le h
\le k$, every ... $(A, B) \in \mathcal{L}_h$ satisfies $A \subseteq C_h$ and $D_h \subseteq B$." -/
structure IsLocationEnlargementVia (G : Hypergraph α β)
    (ℒ ℒ_star : Set (Hypergraph α β × Hypergraph α β))
    (part : Hypergraph α β × Hypergraph α β → Set (Hypergraph α β × Hypergraph α β)) : Prop where
  /-- `ℒ` is a location in `G`. -/
  isLocation_left : GM10.IsLocation G ℒ
  /-- `ℒ*` is a location in `G`. -/
  isLocation_right : GM10.IsLocation G ℒ_star
  /-- Each `part p` (`p ∈ ℒ`) is a subset of `ℒ*`. -/
  part_subset : ∀ ⦃p⦄, p ∈ ℒ → part p ⊆ ℒ_star
  /-- The sets `part p` (`p ∈ ℒ`) are mutually disjoint. -/
  part_disjoint : ∀ ⦃p₁⦄, p₁ ∈ ℒ → ∀ ⦃p₂⦄, p₂ ∈ ℒ → p₁ ≠ p₂ → Disjoint (part p₁) (part p₂)
  /-- The union of `part p` over `p ∈ ℒ` equals `ℒ*`. -/
  biUnion_eq : (⋃ p ∈ ℒ, part p) = ℒ_star
  /-- For each `p = (C_h, D_h) ∈ ℒ` and `(A, B) ∈ part p`, `A ⊆ C_h` and `D_h ⊆ B`. -/
  le_of_mem_part : ∀ ⦃p⦄, p ∈ ℒ → ∀ ⦃q⦄, q ∈ part p → q.1 ≤ p.1 ∧ p.2 ≤ q.2

/-- A location `ℒ*` is an enlargement of a location `ℒ` in `G`
(Graph Minors XVIII, Section 4, pages 86–87). -/
def IsLocationEnlargement (G : Hypergraph α β)
    (ℒ ℒ_star : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∃ part, IsLocationEnlargementVia G ℒ ℒ_star part

/-- A location `ℒ*` is an enlargement of a location `ℒ` in `G` by tree-width `≤ w`
(Graph Minors XVIII, Section 4, page 87):
"If in addition $w \ge 0$ and $\mathcal{L}_h \cup \{(D_h, C_h)\}$ has tree-width $\le w$ for
$1 \le h \le k$, we say that $\mathcal{L}^*$ is an *enlargement of $\mathcal{L}$ by
tree-width $\le w$."
Here `w : ℚ` allows both rational bounds such as `(9 / 4 : ℚ) * θ` in (4.3) and integer bounds
`(w : ℚ)` in (4.4), (5.5), and (6.7). -/
def IsLocationEnlargementByTreeWidth (G : Hypergraph α β)
    (ℒ ℒ_star : Set (Hypergraph α β × Hypergraph α β)) (w : ℚ) : Prop :=
  0 ≤ w ∧ ∃ part, IsLocationEnlargementVia G ℒ ℒ_star part ∧
    ∀ ⦃p⦄, p ∈ ℒ → (locationTreeWidth G (part p ∪ {(p.2, p.1)}) : ℚ) ≤ w

/-! ## Section 5: Patchworks -/

/-- A patchwork `P = (G, μ, Δ)` without edge labels (Graph Minors XVIII, Section 5, pages 89–90),
represented as a `GM04.Patchwork Unit α β`. -/
abbrev UnlabeledPatchwork (α : Type u) (β : Type v) := GM04.Patchwork Unit α β

/-- A partial `Ω`-patchwork `P = (G, μ, Δ, φ)` (Graph Minors XVIII, Section 5, page 90):
"If $\Omega$ is a quasi-order, a *partial $\Omega$-patchwork* is a quadruple $(G, \mu,
\Delta, \phi)$, where $(G, \mu, \Delta)$ is a patchwork and $\phi$ is a function from a
subset $dom(\phi)$ of $E(G)$ into $E(\Omega)$. It is an *$\Omega$-patchwork* if $dom(\phi) =
E(G)$. It is *robust* if $(G, \mu, \Delta)$ is robust."

Represented as `GM04.Patchwork (WithBot Ω) α β`, where `P.φ e = ⊥` for `e ∉ dom(φ)` and
`P.φ e = ↑(φ(e))` for `e ∈ dom(φ)`. Under the standard `Preorder (WithBot Ω)`, the condition
`∀ e ∈ E(G), P.φ e ≤ P'.φ (ηe e)` in `GM04.IsExpansion` is equivalent to: for every
`e ∈ dom(φ)`, `ηe e ∈ dom(φ')` and `φ(e) ≤ φ'(ηe e)` (Section 5, page 90). -/
abbrev PartialPatchwork (Ω : Type w) (α : Type u) (β : Type v) :=
  GM04.Patchwork (WithBot Ω) α β

/-- The domain `dom(φ) ⊆ E(G)` of a partial `Ω`-patchwork `P`
(Graph Minors XVIII, Section 5, page 90). -/
def PartialPatchwork.domφ (P : PartialPatchwork Ω α β) : Set β :=
  {e ∈ P.G.edgeSet | P.φ e ≠ ⊥}

/-- A partial `Ω`-patchwork `P` is a (total) `Ω`-patchwork if `dom(φ) = E(G)`
(Graph Minors XVIII, Section 5, page 90). -/
def PartialPatchwork.IsTotal (P : PartialPatchwork Ω α β) : Prop :=
  ∀ e ∈ P.G.edgeSet, P.φ e ≠ ⊥

/-- Embeds a total `Ω`-patchwork `P : GM04.Patchwork Ω α β` as a `PartialPatchwork Ω α β` with
`dom(φ) = E(G)`. -/
def PartialPatchwork.ofPatchwork (P : GM04.Patchwork Ω α β) : PartialPatchwork Ω α β where
  G := P.G
  dom := P.dom
  μ := P.μ
  Δ := P.Δ
  φ e := (P.φ e : WithBot Ω)
  dom_subset := P.dom_subset
  μ_nodup := P.μ_nodup
  μ_set := P.μ_set
  Δ_verts := P.Δ_verts
  Δ_free := P.Δ_free

/-- Forgets the edge-labelling `φ` of a patchwork `P : GM04.Patchwork Ω α β`, yielding the
underlying unlabeled patchwork `(G, μ, Δ) : UnlabeledPatchwork α β`. -/
def _root_.GraphMinor.GM04.Patchwork.toUnlabeled (P : GM04.Patchwork Ω α β) :
    UnlabeledPatchwork α β where
  G := P.G
  dom := P.dom
  μ := P.μ
  Δ := P.Δ
  φ _ := ()
  dom_subset := P.dom_subset
  μ_nodup := P.μ_nodup
  μ_set := P.μ_set
  Δ_verts := P.Δ_verts
  Δ_free := P.Δ_free

/-- Two vertices `x, y` of a subgraph `H` are connected in `H` if they belong to the same
component of `H` (Graph Minors XVIII, Section 5, page 91):
"Two vertices of a graph $H$ are *connected in $H$* if they belong to the same component of $H$." -/
def ConnectedIn (H : (⊤ : SimpleGraph α).Subgraph) (x y : α) : Prop :=
  ∃ D, GM04.IsComponent H D ∧ x ∈ D.verts ∧ y ∈ D.verts

/-- A grouping `K` is feasible in a patchwork `P` (Graph Minors XVIII, Section 5, page 92):
"Let $P = (G, \mu, \Delta)$ be a patchwork. A grouping $K$ is *feasible* in $P$ if $V(K) =
\bar{\pi}(G)$ and there is a realization $H$ of $P$ such that for distinct $x, y \in V(K)$,
$x$ and $y$ are connected in $H$ if and only if they are adjacent in $K$. A grouping is
*feasible* in a partial $\Omega$-patchwork $(G, \mu, \Delta, \phi)$ if it is feasible in
$(G, \mu, \Delta)$." -/
def IsFeasibleGrouping (P : GM04.Patchwork Ω α β) (K : (⊤ : SimpleGraph α).Subgraph) : Prop :=
  GM04.IsGrouping P.G.rootSet K ∧ K.verts = P.G.rootSet ∧
    ∃ H, P.IsRealization H ∧ ∀ x ∈ P.G.rootSet, ∀ y ∈ P.G.rootSet, x ≠ y →
      (ConnectedIn H x y ↔ K.Adj x y)

/-- The patch `gr(P)` of all groupings feasible in `P`, with vertex set `πBar(G)`
(Graph Minors XVIII, Section 5, page 92):
"The set of all groupings feasible in $P$ will be denoted by $gr(P)$." -/
def feasibleGroupings (P : GM04.Patchwork Ω α β) : GM04.Patch α where
  verts := P.G.rootSet
  groupings := {K | IsFeasibleGrouping P K}
  isGrouping _ hK := hK.1
  verts_eq _ hK := hK.2.1

/-- A rooted subhypergraph `A ⊆ G` is complemented in `G`
(Graph Minors XVIII, Section 5, page 92):
"Let $G$ be a rooted hypergraph. We say that $A \subseteq G$ is *complemented* if
$\bar{\pi}(A)$ contains every vertex $v \in V(A)$ such that either $v \in \bar{\pi}(G)$ or
some edge $e \in E(G) \setminus E(A)$ is incident with $v$." -/
structure IsComplemented (G A : RootedHypergraph α β) : Prop where
  /-- `A ⊆ G` (`A⁻ ⊆ G⁻`). -/
  le : A.toHypergraph ≤ G.toHypergraph
  /-- Every `v ∈ V(A) ∩ πBar(G)` belongs to `πBar(A)`. -/
  roots_mem : ∀ ⦃v : α⦄, v ∈ A.vertexSet → v ∈ G.rootSet → v ∈ A.rootSet
  /-- Every `v ∈ V(A)` incident in `G` with an edge `e ∈ E(G) \ E(A)` belongs to `πBar(A)`. -/
  inc_diff_mem : ∀ ⦃v : α⦄ ⦃e : β⦄, v ∈ A.vertexSet → e ∈ G.edgeSet \ A.edgeSet →
    G.Inc e v → v ∈ A.rootSet

/-- The complementary rooted hypergraph `G \ A` for a complemented rooted subhypergraph `A ⊆ G`
(Graph Minors XVIII, Section 5, pages 92–93):
"If $A$ is complemented, we define $G \setminus A \subseteq G$ to be the rooted hypergraph with
$$
\begin{aligned}
V(G \setminus A) &= (V(G) \setminus V(A)) \cup \bar{\pi}(A), \\
E(G \setminus A) &= E(G) \setminus E(A), \\
\pi(G \setminus A) &= \pi(G).
\end{aligned}
$$" -/
def complement (G A : RootedHypergraph α β) (hA : IsComplemented G A) : RootedHypergraph α β where
  toHypergraph :=
    { vertexSet := (G.vertexSet \ A.vertexSet) ∪ A.rootSet
      edgeSet := G.edgeSet \ A.edgeSet
      Inc e v := e ∈ G.edgeSet \ A.edgeSet ∧ G.Inc e v
      vertex_mem_of_inc e v h := by
        by_cases hvA : v ∈ A.vertexSet
        · exact Or.inr (hA.inc_diff_mem hvA h.1 h.2)
        · exact Or.inl ⟨G.vertex_mem_of_inc h.2, hvA⟩
      edge_mem_of_inc _ _ h := h.1
      vertexSet_finite := (G.vertexSet_finite.sdiff).union
        (A.vertexSet_finite.subset A.roots_subset)
      edgeSet_finite := G.edgeSet_finite.sdiff }
  roots := G.roots
  roots_nodup := G.roots_nodup
  roots_subset v hv := by
    by_cases hvA : v ∈ A.vertexSet
    · exact Or.inr (hA.roots_mem hvA hv)
    · exact Or.inl ⟨G.roots_subset v hv, hvA⟩

/-- The underlying hypergraph `(G \ A)⁻` of the complement `G \ A`, defined unconditionally for any
rooted hypergraphs `G, A` (when `IsComplemented G A`, this equals `(complement G A
hA).toHypergraph`). -/
def complementHypergraph (G A : RootedHypergraph α β) : Hypergraph α β where
  vertexSet := (G.vertexSet \ A.vertexSet) ∪ (G.vertexSet ∩ A.rootSet)
  edgeSet := G.edgeSet \ A.edgeSet
  Inc e v := e ∈ G.edgeSet \ A.edgeSet ∧ G.Inc e v ∧
    v ∈ (G.vertexSet \ A.vertexSet) ∪ (G.vertexSet ∩ A.rootSet)
  vertex_mem_of_inc _ _ h := h.2.2
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := (G.vertexSet_finite.sdiff).union (G.vertexSet_finite.inter_of_left _)
  edgeSet_finite := G.edgeSet_finite.sdiff

/-- A rooted location `ℒ` in a rooted hypergraph `G` (Graph Minors XVIII, Section 5, page 93):
"A *rooted location* $\mathscr{L}$ in a rooted hypergraph $G$ is a set $\mathscr{L}$ of
complemented rooted hypergraphs $A$ with $A \subseteq G$ such that $A_1 \subseteq G
\setminus A_2$ for all distinct $A_1, A_2 \in \mathscr{L}$." -/
structure IsRootedLocation (G : RootedHypergraph α β)
    (ℒ : Set (RootedHypergraph α β)) : Prop where
  /-- Every `A ∈ ℒ` is complemented in `G`. -/
  isComplemented : ∀ ⦃A : RootedHypergraph α β⦄, A ∈ ℒ → IsComplemented G A
  /-- For distinct `A₁, A₂ ∈ ℒ`, `A₁ ⊆ G \ A₂`. -/
  le_complement : ∀ ⦃A₁ : RootedHypergraph α β⦄, A₁ ∈ ℒ →
    ∀ ⦃A₂ : RootedHypergraph α β⦄ (hA₂ : A₂ ∈ ℒ), A₁ ≠ A₂ →
      A₁.toHypergraph ≤ (complement G A₂ (isComplemented hA₂)).toHypergraph

/-- The unrooted location `ℒ⁻ = {(A⁻, (G \ A)⁻) : A ∈ ℒ}` in `G⁻` associated to a rooted location
`ℒ` in `G` (Graph Minors XVIII, Section 5, page 93):
"If $\mathscr{L}$ is a rooted location in $G$ then $\{(A^-, (G \setminus A)^-) \colon A \in
\mathscr{L}\}$ is a location in $G^-$ which we denote by $\mathscr{L}^-$." -/
def rootedLocationToLocation (G : RootedHypergraph α β) (ℒ : Set (RootedHypergraph α β)) :
    Set (Hypergraph α β × Hypergraph α β) :=
  (fun A : RootedHypergraph α β ↦ (A.toHypergraph, complementHypergraph G A)) '' ℒ

/-- The hypergraph `M(G, ℒ) = M(G⁻, ℒ⁻)` for a rooted location `ℒ` in `G`
(Graph Minors XVIII, Section 5, page 93):
"We define `M(G, ℒ) = M(G⁻, ℒ⁻)`." -/
def rootedLocationCore (G : RootedHypergraph α β) (ℒ : Set (RootedHypergraph α β)) :
    Hypergraph α β :=
  GM10.locationCore G.toHypergraph (rootedLocationToLocation G ℒ)

/-- A partial `Ω`-place `(P, ℒ)` (Graph Minors XVIII, Section 5, page 94):
"Now let $P = (G, \mu, \Delta, \phi)$ be a partial $\Omega$-patchwork, and let $\mathscr{L}$
be a rooted location in $G$. We call $(P, \mathscr{L})$ a *partial $\Omega$-place*." -/
def IsPartialPlace (P : PartialPatchwork Ω α β) (ℒ : Set (RootedHypergraph α β)) : Prop :=
  IsRootedLocation P.G ℒ

/-- An `Ω`-place `(P, ℒ)` (Graph Minors XVIII, Section 5, page 94):
"If $dom(\phi) = E(G)$ we call $(P, \mathscr{L})$ an *$\Omega$-place*." -/
def IsOmegaPlace (P : PartialPatchwork Ω α β) (ℒ : Set (RootedHypergraph α β)) : Prop :=
  P.IsTotal ∧ IsRootedLocation P.G ℒ

/-- `P'` is the heart `P | ℒ` of a patchwork or partial `Ω`-patchwork `(P, ℒ)` using new elements
`e : RootedHypergraph α β → β` (Graph Minors XVIII, Section 5, pages 93–94):
"Let $P = (G, \mu, \Delta)$ be a patchwork and let $\mathscr{L}$ be a rooted location in $G$. For
each $A \in \mathscr{L}$ let $e(A)$ be a new element, and let $G'$ be the rooted hypergraph with
$$\begin{aligned}
V(G') &= V(M(G, \mathscr{L})), \\
E(G') &= E(M(G, \mathscr{L})) \cup \{e(A) \colon A \in \mathscr{L}\}, \\
\pi(G') &= \pi(G),
\end{aligned}$$
where for $e \in E(M(G, \mathscr{L}))$ its ends are as in $G^-$, and for $A \in \mathscr{L}$ the
ends of $e(A)$ are the vertices in $\bar{\pi}(A)$. We define the *heart* $P | \mathscr{L}$ of
$(P, \mathscr{L})$ to be the patchwork $(G', \mu', \Delta')$ such that $\mu'(e(A)) = \pi(A)$ and
$\Delta'(e(A)) = gr(P | A)$ for all $A \in \mathscr{L}$ and $\mu'(e) \equiv \mu(e)$ and
$\Delta'(e) = \Delta(e)$ for all $e \in E(M(G, \mathscr{L}))$."
"For $e \in E(M(G, \mathscr{L})) \cap dom(\phi)$ let $\phi'(e) = \phi(e)$, and let $(G',
\mu', \Delta')$ be the heart of $((G, \mu, \Delta), \mathscr{L})$; then $(G', \mu', \Delta',
\phi')$ is a partial $\Omega$-patchwork which we call the *heart* (again denoted by $P |
\mathscr{L}$) of $(P, \mathscr{L})$." -/
structure IsPlaceHeart (P : PartialPatchwork Ω α β) (ℒ : Set (RootedHypergraph α β))
    (newEdge : RootedHypergraph α β → β) (P' : PartialPatchwork Ω α β) : Prop where
  /-- `ℒ` is a rooted location in `P.G`. -/
  isRootedLocation : IsRootedLocation P.G ℒ
  /-- The new elements `newEdge A` (`A ∈ ℒ`) are distinct. -/
  injOn_newEdge : Set.InjOn newEdge ℒ
  /-- None of the new elements `newEdge A` (`A ∈ ℒ`) belongs to `E(M(G, ℒ))`. -/
  newEdge_notMem_core : ∀ ⦃A⦄, A ∈ ℒ → newEdge A ∉ (rootedLocationCore P.G ℒ).edgeSet
  /-- `V(G') = V(M(G, ℒ))`. -/
  vertexSet_eq : P'.G.vertexSet = (rootedLocationCore P.G ℒ).vertexSet
  /-- `E(G') = E(M(G, ℒ)) ∪ {e(A) : A ∈ ℒ}`. -/
  edgeSet_eq : P'.G.edgeSet = (rootedLocationCore P.G ℒ).edgeSet ∪ (newEdge '' ℒ)
  /-- `π(G') = π(G)`. -/
  roots_eq : P'.G.roots = P.G.roots
  /-- For `f ∈ E(M(G, ℒ))`, the ends of `f` in `G'` are as in `G`. -/
  ends_core : ∀ ⦃f⦄, f ∈ (rootedLocationCore P.G ℒ).edgeSet → P'.G.ends f = P.G.ends f
  /-- For `A ∈ ℒ`, the ends of `e(A)` in `G'` are `πBar(A)`. -/
  ends_newEdge : ∀ ⦃A⦄, A ∈ ℒ → P'.G.ends (newEdge A) = A.rootSet
  /-- `dom(μ') = (E(M(G, ℒ)) ∩ dom(μ)) ∪ {e(A) : A ∈ ℒ}`. -/
  dom_eq : P'.dom = ((rootedLocationCore P.G ℒ).edgeSet ∩ P.dom) ∪ (newEdge '' ℒ)
  /-- For `f ∈ E(M(G, ℒ)) ∩ dom(μ)`, `μ'(f) = μ(f)`. -/
  μ_core : ∀ ⦃f⦄, f ∈ (rootedLocationCore P.G ℒ).edgeSet ∩ P.dom → P'.μ f = P.μ f
  /-- For `A ∈ ℒ`, `μ'(e(A)) = π(A)`. -/
  μ_newEdge : ∀ ⦃A⦄, A ∈ ℒ → P'.μ (newEdge A) = A.roots
  /-- For `f ∈ E(M(G, ℒ))`, `Δ'(f) = Δ(f)`. -/
  Δ_core : ∀ ⦃f⦄, f ∈ (rootedLocationCore P.G ℒ).edgeSet → P'.Δ f = P.Δ f
  /-- For `A ∈ ℒ`, `Δ'(e(A)) = gr(P | A)`. -/
  Δ_newEdge : ∀ ⦃A⦄, A ∈ ℒ →
    P'.Δ (newEdge A) = feasibleGroupings (P.restrict A)
  /-- For `f ∈ E(M(G, ℒ))`, `φ'(f) ≡ φ(f)`. -/
  φ_core : ∀ ⦃f⦄, f ∈ (rootedLocationCore P.G ℒ).edgeSet → P'.φ f = P.φ f
  /-- For `A ∈ ℒ`, `e(A) ∉ dom(φ')` (`φ'(e(A)) = ⊥`). -/
  φ_newEdge : ∀ ⦃A⦄, A ∈ ℒ → P'.φ (newEdge A) = ⊥

/-- `P'` is a heart of the partial `Ω`-place `(P, ℒ)` (for some choice of new elements `e(A)`). -/
def HasPlaceHeart (P : PartialPatchwork Ω α β) (ℒ : Set (RootedHypergraph α β))
    (P' : PartialPatchwork Ω α β) : Prop :=
  ∃ newEdge : RootedHypergraph α β → β, IsPlaceHeart P ℒ newEdge P'

/-- `P'` is the heart `P | ℒ` of an unlabeled patchwork `P = (G, μ, Δ)` and rooted location `ℒ`
using new elements `newEdge` (Graph Minors XVIII, Section 5, page 93). -/
structure IsPatchworkHeart (P : UnlabeledPatchwork α β) (ℒ : Set (RootedHypergraph α β))
    (newEdge : RootedHypergraph α β → β) (P' : UnlabeledPatchwork α β) : Prop where
  /-- `ℒ` is a rooted location in `P.G`. -/
  isRootedLocation : IsRootedLocation P.G ℒ
  /-- The new elements `newEdge A` (`A ∈ ℒ`) are distinct. -/
  injOn_newEdge : Set.InjOn newEdge ℒ
  /-- None of the new elements `newEdge A` (`A ∈ ℒ`) belongs to `E(M(G, ℒ))`. -/
  newEdge_notMem_core : ∀ ⦃A⦄, A ∈ ℒ → newEdge A ∉ (rootedLocationCore P.G ℒ).edgeSet
  /-- `V(G') = V(M(G, ℒ))`. -/
  vertexSet_eq : P'.G.vertexSet = (rootedLocationCore P.G ℒ).vertexSet
  /-- `E(G') = E(M(G, ℒ)) ∪ {e(A) : A ∈ ℒ}`. -/
  edgeSet_eq : P'.G.edgeSet = (rootedLocationCore P.G ℒ).edgeSet ∪ (newEdge '' ℒ)
  /-- `π(G') = π(G)`. -/
  roots_eq : P'.G.roots = P.G.roots
  /-- For `f ∈ E(M(G, ℒ))`, the ends of `f` in `G'` are as in `G`. -/
  ends_core : ∀ ⦃f⦄, f ∈ (rootedLocationCore P.G ℒ).edgeSet → P'.G.ends f = P.G.ends f
  /-- For `A ∈ ℒ`, the ends of `e(A)` in `G'` are `πBar(A)`. -/
  ends_newEdge : ∀ ⦃A⦄, A ∈ ℒ → P'.G.ends (newEdge A) = A.rootSet
  /-- `dom(μ') = (E(M(G, ℒ)) ∩ dom(μ)) ∪ {e(A) : A ∈ ℒ}`. -/
  dom_eq : P'.dom = ((rootedLocationCore P.G ℒ).edgeSet ∩ P.dom) ∪ (newEdge '' ℒ)
  /-- For `f ∈ E(M(G, ℒ)) ∩ dom(μ)`, `μ'(f) = μ(f)`. -/
  μ_core : ∀ ⦃f⦄, f ∈ (rootedLocationCore P.G ℒ).edgeSet ∩ P.dom → P'.μ f = P.μ f
  /-- For `A ∈ ℒ`, `μ'(e(A)) = π(A)`. -/
  μ_newEdge : ∀ ⦃A⦄, A ∈ ℒ → P'.μ (newEdge A) = A.roots
  /-- For `f ∈ E(M(G, ℒ))`, `Δ'(f) = Δ(f)`. -/
  Δ_core : ∀ ⦃f⦄, f ∈ (rootedLocationCore P.G ℒ).edgeSet → P'.Δ f = P.Δ f
  /-- For `A ∈ ℒ`, `Δ'(e(A)) = gr(P | A)`. -/
  Δ_newEdge : ∀ ⦃A⦄, A ∈ ℒ →
    P'.Δ (newEdge A) = feasibleGroupings (P.restrict A)

/-- `P'` is a heart of the unlabeled patchwork `P` and rooted location `ℒ`. -/
def HasPatchworkHeart (P : UnlabeledPatchwork α β) (ℒ : Set (RootedHypergraph α β))
    (P' : UnlabeledPatchwork α β) : Prop :=
  ∃ newEdge : RootedHypergraph α β → β, IsPatchworkHeart P ℒ newEdge P'

/-- A partial `Ω`-patchwork `P = (G, μ, Δ, φ)` has tree-width `≤ w` (where `w ≥ 0`)
(Graph Minors XVIII, Section 5, page 95):
"A partial $\Omega$-patchwork $(G, \mu, \Delta, \phi)$ has *tree-width* $\le w$, where $w \ge
0$, if there is a tree-decomposition $(T, \tau)$ of $G^-$ of width $\le w$ such that
$\bar{\pi}(G) \subseteq V(\tau(t))$ for some $t \in V(T)$." -/
def HasPatchworkTreeWidthLE (P : GM04.Patchwork Ω α β) (w : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (t₀ : ι),
    GM10.IsTreeDecomposition P.G.toHypergraph T τ ∧
    GM10.treeDecompWidth τ ≤ (w : ℤ) ∧
    P.G.rootSet ⊆ (τ t₀).vertexSet

/-- A partial `Ω`-patchwork `P` is an enlargement of `P'` (`= P | ℒ`) by tree-width `≤ w`
(Graph Minors XVIII, Section 5, page 95):
"If $(P, \mathscr{L})$ is a partial $\Omega$-place, and $P|A$ has tree-width $\le w$ for all
$A \in \mathscr{L}$, we say that $P$ is an *enlargement* of $P|\mathscr{L}$ by tree-width
$\le w$." -/
def IsPlaceEnlargementByTreeWidth (w : ℕ) (P' P : PartialPatchwork Ω α β) : Prop :=
  ∃ ℒ : Set (RootedHypergraph α β),
    IsRootedLocation P.G ℒ ∧
    HasPlaceHeart P ℒ P' ∧
    ∀ A ∈ ℒ, HasPatchworkTreeWidthLE (P.restrict A) w

/-! ## Section 6: Well-Behavedness -/

/-- The disjoint union quasi-order `Ω₁ ∪ Ω₂` on `Ω₁ ⊕ Ω₂`
(Graph Minors XVIII, Section 5, page 90):
"If $\Omega_1, \Omega_2$ are quasi-orders with $E(\Omega_1) \cap E(\Omega_2) = \emptyset$ we
denote by $\Omega_1 \cup \Omega_2$ the quasi-order $\Omega$ with $E(\Omega) = E(\Omega_1)
\cup E(\Omega_2)$ in which $x \le y$ if and only if for some $i \in \{1, 2\}$, $x, y \in
E(\Omega_i)$ and $x \le y$ in $\Omega_i$." -/
inductive DisjointUnionLE {Ω₁ Ω₂ : Type*} [LE Ω₁] [LE Ω₂] : Ω₁ ⊕ Ω₂ → Ω₁ ⊕ Ω₂ → Prop
  | inl {x y : Ω₁} : x ≤ y → DisjointUnionLE (Sum.inl x) (Sum.inl y)
  | inr {x y : Ω₂} : x ≤ y → DisjointUnionLE (Sum.inr x) (Sum.inr y)

/-- Type alias for `Ω₁ ⊕ Ω₂` equipped with the disjoint union quasi-order `Ω₁ ∪ Ω₂`. -/
def DisjointUnionQuasiOrder (Ω₁ Ω₂ : Type*) := Ω₁ ⊕ Ω₂

instance {Ω₁ Ω₂ : Type*} [Preorder Ω₁] [Preorder Ω₂] :
    Preorder (DisjointUnionQuasiOrder Ω₁ Ω₂) where
  le := DisjointUnionLE
  le_refl x := by
    cases x with
    | inl a => exact DisjointUnionLE.inl (le_refl a)
    | inr b => exact DisjointUnionLE.inr (le_refl b)
  le_trans x y z hxy hyz := by
    cases hxy with
    | inl h₁ =>
      cases hyz with
      | inl h₂ => exact DisjointUnionLE.inl (le_trans h₁ h₂)
    | inr h₁ =>
      cases hyz with
      | inr h₂ => exact DisjointUnionLE.inr (le_trans h₁ h₂)

/-- An `Ω'`-completion of a partial `Ω`-patchwork `P` along an order-embedding `ι : Ω ↪o Ω'`
(Graph Minors XVIII, Section 6, page 100):
"Let $P = (G, \mu, \Delta, \phi)$ be a partial $\Omega$-patchwork, and let $\Omega'$ be a
quasi-order with $\Omega \subseteq \Omega'$. By an $\Omega'$-completion of $P$ we mean an
$\Omega'$-patchwork $(G, \mu, \Delta, \phi')$ such that $\phi'(e) = \phi(e)$ for each $e \in
dom(\phi)$." -/
structure IsCompletion {Ω' : Type*} [Preorder Ω] [Preorder Ω'] (ι : Ω ↪o Ω')
    (P : PartialPatchwork Ω α β) (Q : GM04.Patchwork Ω' α β) : Prop where
  /-- `Q` has the same underlying rooted hypergraph `G` as `P`. -/
  G_eq : Q.G = P.G
  /-- `Q` has the same `dom(μ)` as `P`. -/
  dom_eq : Q.dom = P.dom
  /-- `Q` has the same march function `μ` on `dom(μ)` as `P`. -/
  μ_eq : ∀ ⦃e⦄, e ∈ P.dom → Q.μ e = P.μ e
  /-- `Q` has the same patch function `Δ` on `E(G)` as `P`. -/
  Δ_eq : ∀ ⦃e⦄, e ∈ P.G.edgeSet → Q.Δ e = P.Δ e
  /-- For `e ∈ dom(φ)` with `φ(e) = ω`, `φ'(e) = ι(ω)`. -/
  φ_eq : ∀ ⦃e⦄, e ∈ P.G.edgeSet → ∀ ⦃ω : Ω⦄, P.φ e = (ω : WithBot Ω) → Q.φ e = ι ω

/-- A class `𝒞` of partial `Ω`-patchworks is well-behaved
(Graph Minors XVIII, Section 6, page 100):
"If $\Omega$ is a well-quasi-order, a class $\mathcal{C}$ of partial $\Omega$-patchworks is
*well-behaved* if for every well-quasi-order $\Omega'$ with $\Omega \subseteq \Omega'$ and
every countable sequence $P_i'$ ($i = 1, 2, \dots$) of $\Omega'$-completions of members of
$\mathcal{C}$ there exist $j > i \ge 1$ such that $P_i'$ is simulated in $P_j'$."

Here `Ω'` ranges over `Type (max w (max u v))`, which is closed under forming patchworks
`GM04.Patchwork Ω' α β` and disjoint unions `DisjointUnionQuasiOrder`, as used in (6.1) and (6.3).
-/
def WellBehaved [Preorder Ω] (𝒞 : Set (PartialPatchwork Ω α β)) : Prop :=
  ∀ (Ω' : Type (max w (max u v))) [Preorder Ω'] (ι : Ω ↪o Ω'),
    WellQuasiOrderedLE Ω' →
    ∀ (Q : ℕ → GM04.Patchwork Ω' α β),
      (∀ i, ∃ P ∈ 𝒞, IsCompletion ι P (Q i)) →
      ∃ i j, i < j ∧ GM04.Simulated (Q i) (Q j)

/-- A patchwork or partial `Ω`-patchwork `P = (G, μ, Δ, φ)` is rootless if `πBar(G) = ∅`
(Graph Minors XVIII, Section 6, page 100):
"A partial $\Omega$-patchwork $P = (G, \mu, \Delta, \phi)$ is *rootless* if $\bar{\pi}(G) =
\emptyset$." -/
def IsRootless (P : GM04.Patchwork Ω α β) : Prop :=
  P.G.rootSet = ∅

/-- A partial `Ω`-patchwork `P'` is a rooting of a rootless partial `Ω`-patchwork `P`
(Graph Minors XVIII, Section 6, page 100):
"Let $P = (G, \mu, \Delta, \phi)$ be a rootless partial $\Omega$-patchwork, let $e \in
dom(\mu) \setminus dom(\phi)$, and let $P' = (G', \mu', \Delta', \phi')$ be the partial
$\Omega$-patchwork with $G'^- = G^- \setminus e$, $\pi(G') = \mu(e)$, and $P' = P|G'$. We
call $P'$ a *rooting* of $P$." -/
def IsRooting (P P' : PartialPatchwork Ω α β) : Prop :=
  IsRootless P ∧
    ∃ e ∈ P.dom, P.φ e = ⊥ ∧
      P'.G.toHypergraph ≤ P.G.toHypergraph ∧
      P'.G.toHypergraph = P.G.toHypergraph.deleteEdges {e} ∧
      P'.G.roots = P.μ e ∧
      P' = P.restrict P'.G

/-- A partial `Ω`-patchwork `P` is an enlargement of `P'` (`= P | ℒ`) by a class `𝒞` of partial
`Ω`-patchworks (Graph Minors XVIII, Section 6, page 101):
"Let $\mathcal{C}$ be a class of partial $\Omega$-patchworks, and let $(P, \mathcal{L})$ be a
partial $\Omega$-place. If $P|A \in \mathcal{C}$ for all $A \in \mathcal{L}$ we say that $P$
is an *enlargement of* $P|\mathcal{L}$ *by* $\mathcal{C}$." -/
def IsPlaceEnlargementByClass (𝒞 : Set (PartialPatchwork Ω α β))
    (P' P : PartialPatchwork Ω α β) : Prop :=
  ∃ ℒ : Set (RootedHypergraph α β),
    IsRootedLocation P.G ℒ ∧
    HasPlaceHeart P ℒ P' ∧
    ∀ A ∈ ℒ, P.restrict A ∈ 𝒞

/-- The class of all enlargements of members of `𝒞₁` by `𝒞₂`
(Graph Minors XVIII, Section 6, (6.3), page 101). -/
def enlargementClass (𝒞₁ 𝒞₂ : Set (PartialPatchwork Ω α β)) :
    Set (PartialPatchwork Ω α β) :=
  {P | ∃ P' ∈ 𝒞₁, IsPlaceEnlargementByClass 𝒞₂ P' P}

open Classical in
/-- The underlying undirected graph `T⁻` of an arborescence `T : GM04.RootedTree ι`
(Graph Minors XVIII, Section 6, page 102):
"An *arborescence* is a directed graph $T$, whose underlying graph is a tree (denoted by
$T^-$), such that every vertex is the head of at most one edge." -/
noncomputable def arborescenceUnderlying (T : GM04.RootedTree ι) : SimpleGraph ι where
  Adj u v := (u ∈ T.edges ∧ T.parent u = v) ∨ (v ∈ T.edges ∧ T.parent v = u)
  symm := ⟨fun _ _ h ↦ Or.symm h⟩
  loopless := ⟨fun v h ↦ by
    rcases h with ⟨hv, hp⟩ | ⟨hv, hp⟩ <;> exact T.parent_ne_self hv hp⟩

/-- A rooted decomposition `(T, τ)` of a partial `Ω`-patchwork `P = (G, μ, Δ, φ)`
(Graph Minors XVIII, Section 6, page 102):
"Let $P = (G, \mu, \Delta, \phi)$ be a partial $\Omega$-patchwork. A *rooted decomposition*
of $P$ is a pair $(T, \tau)$, where * $T$ is an arborescence, and for each $t \in V(T)$,
$\tau(t) \subseteq G$ is a rooted hypergraph, * $(T^-, \tau^-)$ is a tree-decomposition of
$G^-$, where $\tau^-(t) = \tau(t)^-$ for each $t \in V(T)$, * $\pi(\tau(o(T))) = \pi(G)$, *
for every subarborescence $S$ of $T$, let $\tau \times S$ denote the rooted hypergraph $H$
with $H^- = \tau^- \times S^-$ and $\pi(H) = \pi(\tau(o(S)))$; then for every edge $f \in
E(T)$ with head $t$, $$ \bar{\pi}(\tau(t)) = V(\tau \times T^f) \cap V(\tau \times T_f), $$
* for every directed path $F$ of $T$ with first edge $f_1$ and last edge $f_2$ such that
$f_1, f_2$ make separations under $(T^-, \tau^-)$ of the same order and no edge of $F$ makes
a separation of smaller order, $P|\tau \times T^{f_2}$ is simulated in $P|\tau \times
T^{f_1}$." -/
structure IsRootedDecomposition [Preorder Ω] (P : GM04.Patchwork Ω α β)
    (T : GM04.RootedTree ι) (τ : ι → RootedHypergraph α β) : Prop where
  /-- `(T, τ)` is a rooted tree-decomposition of `G = ‖P‖` (capturing the first four conditions, by
  `GM04.IsTreeDecomposition.subtreeAt_inter_rootSide_eq`). -/
  isTreeDecomposition : GM04.IsTreeDecomposition P.G T τ
  /-- `E(T)` is linked in `(T, τ)` with respect to simulation of restrictions of `P`. -/
  isLinked : GM04.IsLinked
    (fun H₁ H₂ ↦ GM04.Simulated (P.restrict H₁) (P.restrict H₂))
    T τ (T.edges : Set ι)

/-- The rooted hypergraph `τ × (T, f) = ((τ × T_f)⁻, π(τ × T^f))` for an edge `f ∈ E(T)` of a
rooted decomposition `(T, τ)` (Graph Minors XVIII, Section 6, page 102):
"If $(T, \tau)$ is a rooted decomposition of a partial $\Omega$-patchwork $(G, \mu, \Delta,
\phi)$ and $f \in E(T)$, we define $\tau \times (T, f)$ to be the rooted hypergraph $((\tau
\times T_f)^-, \pi(\tau \times T^f))$." -/
noncomputable def rootedDecompRootSide {G : RootedHypergraph α β} {T : GM04.RootedTree ι}
    {τ : ι → RootedHypergraph α β} (h : GM04.IsTreeDecomposition G T τ)
    {f : ι} (hf : f ∈ T.edges) : RootedHypergraph α β where
  toHypergraph := (GM04.cross τ (T.rootSide f) T.root).toHypergraph
  roots := (GM04.cross τ (T.subtreeAt f) f).roots
  roots_nodup := (GM04.cross τ (T.subtreeAt f) f).roots_nodup
  roots_subset v hv := by
    have hsep := h.isSeparation_edge hf
    have hv_rootSet : v ∈ (GM04.cross τ (T.subtreeAt f) f).rootSet := hv
    rw [hsep.rootSet_left] at hv_rootSet
    exact hv_rootSet.2

/-- `Q` is a piece of a rootless `Ω`-patchwork `P` at `t₀ ∈ V(T)` under a tree-decomposition
`(T, τ)` of `G⁻` (Graph Minors XVIII, Section 6, page 104):
"Let $P = (G, \mu, \Delta, \phi)$ be a rootless $\Omega$-patchwork, and let $(T, \tau)$ be a
tree-decomposition of $G^-$. If $(P, \mathcal{L})$ is an $\Omega$-place such that
$\mathcal{L}^-$ is the location of $t_0$ in $(T, \tau)$ for some $t_0 \in V(T)$, we call the
heart of $(P, \mathcal{L})$ a *piece of* $P$ (*at* $t_0$, *under* $(T, \tau)$)." -/
def IsPiece [Fintype ι] (P : PartialPatchwork Ω α β)
    (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (t₀ : ι)
    (Q : PartialPatchwork Ω α β) : Prop :=
  ∃ ℒ : Set (RootedHypergraph α β),
    IsOmegaPlace P ℒ ∧
    rootedLocationToLocation P.G ℒ = vertexLocation T τ t₀ ∧
    HasPlaceHeart P ℒ Q

/-! ## Section 7: More on Isolation -/

/-- A separation `(A, B) ∈ 𝒯` is `λ`-linked to a tangle `𝒯`
(Graph Minors XVIII, Section 7, page 107):
"Let $\lambda$ be a tie-breaker in a hypergraph $G$, let $\mathscr{T}$ be a tangle in $G$,
and let $(A, B) \in \mathscr{T}$. We say that $(A, B)$ is $\lambda$-*linked to*
$\mathscr{T}$ if there is no $(A', B') \in \mathscr{T}$ with smaller $\lambda$-order with $A
\subseteq A'$ and $B' \subseteq B$." -/
def IsLambdaLinkedTo {Λ : Type*} [LE Λ]
    (lam : Hypergraph α β × Hypergraph α β → Λ)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (A B : Hypergraph α β) : Prop :=
  (A, B) ∈ 𝒯 ∧ ∀ ⦃A' B' : Hypergraph α β⦄, (A', B') ∈ 𝒯 →
    A ≤ A' → B' ≤ B → lam (A, B) ≤ lam (A', B')

end GraphMinor.GM18
