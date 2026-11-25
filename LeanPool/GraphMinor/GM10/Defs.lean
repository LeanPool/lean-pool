/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Order.Lattice.Nat
public import LeanPool.GraphMinor.Hypergraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Definitions for Graph Minors X, Sections 1–5

This file formalizes the definitions of N. Robertson and P. D. Seymour,
*Graph Minors. X. Obstructions to tree-decomposition*, J. Combin. Theory Ser. B 52 (1991) 153–190,
Sections 1–5 (pages 153–170):

- **Section 1 (pages 153–155):** vertex deletion `G \ X` (`deleteVertices`), the three tangle
  axioms (`TangleAxiom1`, `TangleAxiom2`, `TangleAxiom3`), tangles of order `θ` (`IsTangle`),
  the tangle number `θ(G)` (`tangleNumber`), and truncation of a tangle (`truncation`).
- **Section 2 (pages 155–159):** the size of an edge (`edgeSize`), the single-edge hypergraph `K_e`
  (`edgeHypergraph`), the single-vertex edgeless hypergraph `K_v` (`vertexHypergraph`), the null
  hypergraph (`⊥`) and non-null hypergraphs (`IsNonNull`), and extreme separations in a tangle
  (`IsExtreme`).
- **Section 3 (pages 159–164):** connectivity functions on a finite set `E`
  (`IsConnectivityFunction`), efficient sets (`IsEfficient`), biases (`IsBias`), biases extending
  a set `𝒜` (`BiasExtends`), leaves of a tree (`IsLeaf`, `leafSet`), ternary trees
  (`IsTernaryTree`), incidences in a tree (`IsTreeIncidence`), tree-labellings over `𝒜`
  (`IsTreeLabelling`), passive incidences (`IsPassiveIncidence`), forks (`IsFork`), exact forks
  (`IsExactFork`), and exact tree-labellings (`IsExactTreeLabelling`).
- **Section 4 (pages 164–167):** branch-decompositions of a hypergraph (`IsBranchDecomposition`),
  the order of an edge in a branch-decomposition (`branchEdgeOrder`), the width of a
  branch-decomposition (`branchDecompWidth`), branch-width `β(G)` (`branchWidth`), the maximum
  edge size `γ(G)` (`maxEdgeSize`), and the complete graph `K_n` as a hypergraph (`completeGraph`).
- **Section 5 (pages 168–170):** paths in undirected trees (`OnTreePath`), tree-decompositions of
  a hypergraph (`IsTreeDecomposition`), width of a tree-decomposition (`treeDecompWidthPlusOne`,
  `treeDecompWidth`), and tree-width `ω(G)` (`treeWidthPlusOne`, representing `ω(G) + 1 : ℕ`, and
  `treeWidth`, representing `ω(G) : ℤ`, which is `-1` when `V(G) = ∅`).
-/

@[expose] public section

namespace GraphMinor

namespace Hypergraph

variable {α β : Type*}

/-- `G \ X` for a set of vertices `X ⊆ V(G)` (Graph Minors X, Section 1, page 154):
"while if $X \subseteq V(G)$, $G \setminus X$ is the subhypergraph with $V(G') = V(G) - X$
and $E(G')$ the set of those edges of $G$ incident with no vertex in $X$. We sometimes
abbreviate $G \setminus \{x\}$ to $G \setminus x$, etc." -/
def deleteVertices (G : Hypergraph α β) (X : Set α) : Hypergraph α β where
  vertexSet := G.vertexSet \ X
  edgeSet := {e ∈ G.edgeSet | ∀ v ∈ X, ¬ G.Inc e v}
  Inc e v := G.Inc e v ∧ ∀ w ∈ X, ¬ G.Inc e w
  vertex_mem_of_inc _ _ h := ⟨G.vertex_mem_of_inc h.1, fun hv ↦ h.2 _ hv h.1⟩
  edge_mem_of_inc _ _ h := ⟨G.edge_mem_of_inc h.1, h.2⟩
  vertexSet_finite := G.vertexSet_finite.subset Set.sdiff_subset
  edgeSet_finite := G.edgeSet_finite.subset fun _ h ↦ h.1

/-- The null hypergraph, with `V(G) = ∅` and `E(G) = ∅`. -/
instance : Bot (Hypergraph α β) where
  bot :=
    { vertexSet := ∅
      edgeSet := ∅
      Inc := fun _ _ ↦ False
      vertex_mem_of_inc := fun _ _ h ↦ h.elim
      edge_mem_of_inc := fun _ _ h ↦ h.elim
      vertexSet_finite := Set.finite_empty
      edgeSet_finite := Set.finite_empty }

instance : OrderBot (Hypergraph α β) where
  bot_le _ := ⟨Set.empty_subset _, Set.empty_subset _, fun _ h ↦ h.elim⟩

end Hypergraph

namespace GM10

open SimpleGraph Hypergraph

variable {α β ι ι' : Type*}

/-! ## Section 1: Tangles -/

export Hypergraph (deleteVertices)

/-- The first tangle axiom (Graph Minors X, Section 1, page 154):
"(i) for every separation $(A, B)$ of $G$ of order $< \theta$, one of $(A, B)$, $(B, A)$ is
in $\mathscr{T}$" -/
def TangleAxiom1 (G : Hypergraph α β) (θ : ℕ)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∀ ⦃A B : Hypergraph α β⦄, G.IsSeparation A B → separationOrder A B < θ →
    (A, B) ∈ 𝒯 ∨ (B, A) ∈ 𝒯

/-- The second tangle axiom (Graph Minors X, Section 1, page 154):
"(ii) if $(A_1, B_1), (A_2, B_2), (A_3, B_3) \in \mathscr{T}$ then $A_1 \cup A_2 \cup A_3 \ne G$" -/
def TangleAxiom2 (G : Hypergraph α β) (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∀ ⦃A₁ B₁ A₂ B₂ A₃ B₃ : Hypergraph α β⦄,
    (A₁, B₁) ∈ 𝒯 → (A₂, B₂) ∈ 𝒯 → (A₃, B₃) ∈ 𝒯 → A₁ ∪ A₂ ∪ A₃ ≠ G

/-- The third tangle axiom (Graph Minors X, Section 1, page 154):
"(iii) if $(A, B) \in \mathscr{T}$ then $V(A) \ne V(G)$." -/
def TangleAxiom3 (G : Hypergraph α β) (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → A.vertexSet ≠ G.vertexSet

/-- The tangle induced in `G` by a tangle in `H`, obtained by restricting each separation
to `H` while retaining the order bound in `G`. -/
def inducedTangleFromSubgraph (G H : Hypergraph α β) (θ : ℕ)
    (T : Set (Hypergraph α β × Hypergraph α β)) : Set (Hypergraph α β × Hypergraph α β) :=
  {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧ (p.1 ∩ H, p.2 ∩ H) ∈ T}

/-- A tangle in `G` of order `θ` (Graph Minors X, Section 1, page 154):
"Let $G$ be a hypergraph and let $\theta \ge 1$ be an integer. A *tangle* in $G$ of *order*
$\theta$ is a set $\mathscr{T}$ of separations of $G$, each of order $< \theta$, such that
(i) for every separation $(A, B)$ of $G$ of order $< \theta$, one of $(A, B)$, $(B, A)$ is
in $\mathscr{T}$ (ii) if $(A_1, B_1), (A_2, B_2), (A_3, B_3) \in \mathscr{T}$ then $A_1 \cup
A_2 \cup A_3 \ne G$ (iii) if $(A, B) \in \mathscr{T}$ then $V(A) \ne V(G)$. We refer to
these as the *first*, *second*, and *third (tangle) axioms*." -/
structure IsTangle (G : Hypergraph α β) (θ : ℕ)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) : Prop where
  /-- The order of a tangle satisfies `θ ≥ 1`. -/
  one_le : 1 ≤ θ
  /-- Every member of `𝒯` is a separation of `G`. -/
  isSeparation : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → G.IsSeparation A B
  /-- Every member of `𝒯` has order `< θ`. -/
  order_lt : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → separationOrder A B < θ
  /-- The first tangle axiom (i). -/
  axiom1 : TangleAxiom1 G θ 𝒯
  /-- The second tangle axiom (ii). -/
  axiom2 : TangleAxiom2 G 𝒯
  /-- The third tangle axiom (iii). -/
  axiom3 : TangleAxiom3 G 𝒯

/-- The tangle number `θ(G)` of `G` (Graph Minors X, Section 1, page 154):
"The *tangle number* of $G$, denoted $\theta(G)$, is the maximum order of tangles in $G$ (or
0, if there are no tangles)." -/
noncomputable def tangleNumber (G : Hypergraph α β) : ℕ :=
  sSup {θ : ℕ | ∃ 𝒯, IsTangle G θ 𝒯}

/-- The truncation of a tangle `𝒯` to order `θ'` (Graph Minors X, Section 1, page 155, and
Section 6, page 170):
"Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$, let $1 \le \theta' \le
\theta$, and let $\mathscr{T}'$ be the set of all members of $\mathscr{T}$ with order $<
\theta'$. Then it is easy to see that $\mathscr{T}'$ is a tangle in $G$ of order $\theta'$;
we call $\mathscr{T}'$ the *truncation* of $\mathscr{T}$ to order $\theta'$." -/
def truncation (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p ∈ 𝒯 | separationOrder p.1 p.2 < θ'}

/-! ## Section 2: Some Tangle Lemmas -/

/-- The size of an edge `e` of `G` (Graph Minors X, Section 2, page 156):
"For an edge $e$ of a hypergraph $G$, the *ends* of $e$ are the vertices of $G$ incident with
$e$, and the *size* of $e$ is the number of ends of $e$." -/
noncomputable def edgeSize (G : Hypergraph α β) (e : β) : ℕ :=
  (G.ends e).ncard

/-- The hypergraph `K_e` formed by an edge `e` and its ends in `G`
(Graph Minors X, Section 2, (2.7), page 157):
"where $K_e$ is the hypergraph formed by $e$ and its ends." -/
def edgeHypergraph (G : Hypergraph α β) (e : β) : Hypergraph α β where
  vertexSet := G.ends e
  edgeSet := {e}
  Inc e' v := e' = e ∧ G.Inc e v
  vertex_mem_of_inc _ _ h := h.2
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ G.vertex_mem_of_inc h
  edgeSet_finite := Set.finite_singleton e

/-- The hypergraph `K_v` with vertex set `{v}` and no edges
(Graph Minors X, Section 2, proofs of (2.3) and (2.8), pages 155 and 157):
"Let $K_v$ be the hypergraph with vertex set $\{v\}$ and with no edges." -/
def vertexHypergraph (v : α) : Hypergraph α β where
  vertexSet := {v}
  edgeSet := ∅
  Inc _ _ := False
  vertex_mem_of_inc _ _ h := h.elim
  edge_mem_of_inc _ _ h := h.elim
  vertexSet_finite := Set.finite_singleton v
  edgeSet_finite := Set.finite_empty

/-- A hypergraph `G` is non-null if it is not the null hypergraph `⊥`, that is, `V(G) ≠ ∅` or
`E(G) ≠ ∅` (Graph Minors X, Section 2, (2.8), page 157). -/
def IsNonNull (G : Hypergraph α β) : Prop :=
  G.vertexSet.Nonempty ∨ G.edgeSet.Nonempty

/-- A separation `(A, B) ∈ 𝒯` is extreme in `𝒯` (Graph Minors X, Section 2, page 157):
"Let $\mathscr{T}$ be a tangle in a hypergraph $G$. A separation $(A, B)\in \mathscr{T}$ is
*extreme* if $A' = A$ and $B' = B$ for every $(A', B')\in \mathscr{T}$ with $A\subseteq A'$
and $B'\subseteq B$." -/
def IsExtreme (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (A B : Hypergraph α β) : Prop :=
  (A, B) ∈ 𝒯 ∧ ∀ ⦃A' B' : Hypergraph α β⦄, (A', B') ∈ 𝒯 → A ≤ A' → B' ≤ B → A' = A ∧ B' = B

/-! ## Section 3: A Lemma About Submodular Functions -/

/-- A connectivity function on a set `E` (Graph Minors X, Section 3, page 159):
"Let $E$ be a finite set. A *connectivity function* on $E$ is a function $\kappa$ from the
set of all subsets of $E$ to the set of integers such that (i) for $X\subseteq E$,
$\kappa(X) = \kappa(E - X)$ (ii) for $X, Y\subseteq E$, $\kappa(X\cup Y) + \kappa(X\cap
Y)\le \kappa(X) + \kappa(Y)$." -/
structure IsConnectivityFunction (E : Set β) (κ : Set β → ℤ) : Prop where
  /-- (i) For `X ⊆ E`, `κ(X) = κ(E - X)`. -/
  compl_eq : ∀ ⦃X : Set β⦄, X ⊆ E → κ X = κ (E \ X)
  /-- (ii) For `X, Y ⊆ E`, `κ(X ∪ Y) + κ(X ∩ Y) ≤ κ(X) + κ(Y)`. -/
  submodular : ∀ ⦃X Y : Set β⦄, X ⊆ E → Y ⊆ E → κ (X ∪ Y) + κ (X ∩ Y) ≤ κ X + κ Y

/-- A subset `X ⊆ E` is efficient for `κ` (Graph Minors X, Section 3, page 159):
"A subset $X\subseteq E$ is *efficient* if $\kappa(X)\le 0$." -/
def IsEfficient (E : Set β) (κ : Set β → ℤ) (X : Set β) : Prop :=
  X ⊆ E ∧ κ X ≤ 0

/-- A bias for `(E, κ)` (Graph Minors X, Section 3, page 159):
"A *bias* is a set $\mathscr{B}$ of efficient sets, such that (i) if $X\subseteq E$ is
efficient then $\mathscr{B}$ contains one of $X, E - X$ (ii) if $X, Y, Z\in \mathscr{B}$
then $X\cup Y\cup Z\ne E$." -/
structure IsBias (E : Set β) (κ : Set β → ℤ) (ℬ : Set (Set β)) : Prop where
  /-- Every member of `ℬ` is an efficient subset of `E`. -/
  isEfficient : ∀ ⦃X : Set β⦄, X ∈ ℬ → IsEfficient E κ X
  /-- (i) If `X ⊆ E` is efficient then `ℬ` contains one of `X, E - X`. -/
  mem_or_compl_mem : ∀ ⦃X : Set β⦄, IsEfficient E κ X → X ∈ ℬ ∨ E \ X ∈ ℬ
  /-- (ii) If `X, Y, Z ∈ ℬ` then `X ∪ Y ∪ Z ≠ E`. -/
  union_ne : ∀ ⦃X Y Z : Set β⦄, X ∈ ℬ → Y ∈ ℬ → Z ∈ ℬ → X ∪ Y ∪ Z ≠ E

/-- A bias `ℬ` extends a set `𝒜` of efficient sets (Graph Minors X, Section 3, page 159):
"A bias $\mathscr{B}$ is said to *extend* a set $\mathscr{A}$ of efficient sets if
$\mathscr{A}\subseteq \mathscr{B}$." -/
def BiasExtends (E : Set β) (κ : Set β → ℤ) (𝒜 ℬ : Set (Set β)) : Prop :=
  IsBias E κ ℬ ∧ 𝒜 ⊆ ℬ

open Classical in
/-- A vertex `v` of a tree `T` is a leaf if it has valency `≤ 1`
(Graph Minors X, Section 3, page 159):
"A tree is a connected non-null graph with no circuits; its vertices of valency $\le 1$ are
its *leaves*." -/
def IsLeaf [Fintype ι] (T : SimpleGraph ι) (v : ι) : Prop :=
  T.degree v ≤ 1

/-- The set of leaves of `T`. -/
def leafSet [Fintype ι] (T : SimpleGraph ι) : Set ι :=
  {v | IsLeaf T v}

open Classical in
/-- A tree `T` is ternary if every vertex has valency `1` or `3`
(Graph Minors X, Section 3, page 159):
"A tree is *ternary* if every vertex has valency $1$ or $3$. (Thus, ternary trees have $\ge
2$ leaves.)" -/
structure IsTernaryTree [Fintype ι] (T : SimpleGraph ι) : Prop where
  /-- `T` is a tree (connected, non-null, and acyclic). -/
  isTree : T.IsTree
  /-- Every vertex of `T` has valency `1` or `3`. -/
  degree_eq_one_or_three : ∀ v : ι, T.degree v = 1 ∨ T.degree v = 3

/-- An incidence in a tree `T` (Graph Minors X, Section 3, page 159):
"An *incidence* in a tree $T$ is a pair $(v, e)$, where $v\in V(T)$, $e\in E(T)$, and $e$ is
incident with $v$." -/
def IsTreeIncidence (T : SimpleGraph ι) (v : ι) (e : Sym2 ι) : Prop :=
  e ∈ T.incidenceSet v

open Classical in
/-- A tree-labelling `(T, α)` over `𝒜` (Graph Minors X, Section 3, pages 159–160):
"A *tree-labelling over* $\mathscr{A}$ is a pair $(T, \alpha)$, where $T$ is a ternary tree,
and $\alpha$ is a function from the set of all incidences in $T$ to the set of efficient
subsets of $E$, such that ... (i) for each $e\in E(T)$ with ends $u, v$, say, $\alpha(u, e) = E
- \alpha(v, e)$ (ii) for each incidence $(v, e)$ in $T$ such that $v$ is a leaf, either
$\alpha(v, e) = E$ or $\alpha(v, e)\cup X = E$ for some $X\in \mathscr{A}$ (iii) if $v\in
V(T)$ has valency $3$, incident with $e_1, e_2, e_3$, say, then $\alpha(v, e_1)\cup
\alpha(v, e_2)\cup \alpha(v, e_3) = E$." -/
structure IsTreeLabelling [Fintype ι] (E : Set β) (κ : Set β → ℤ) (𝒜 : Set (Set β))
    (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β) : Prop where
  /-- `T` is a ternary tree. -/
  isTernaryTree : IsTernaryTree T
  /-- `α` maps every incidence of `T` to an efficient subset of `E`. -/
  isEfficient : ∀ ⦃v : ι⦄ ⦃e : Sym2 ι⦄, IsTreeIncidence T v e → IsEfficient E κ (α v e)
  /-- (i) For each edge `s(u, v)` of `T` with ends `u, v`, `α(u, e) = E - α(v, e)`. -/
  compl_eq : ∀ ⦃u v : ι⦄, T.Adj u v → α u s(u, v) = E \ α v s(u, v)
  /-- (ii) For each incidence `(v, e)` in `T` such that `v` is a leaf, either `α(v, e) = E` or
  `α(v, e) ∪ X = E` for some `X ∈ 𝒜`. -/
  leaf_eq_or_union_eq : ∀ ⦃v : ι⦄ ⦃e : Sym2 ι⦄, IsTreeIncidence T v e → IsLeaf T v →
    α v e = E ∨ ∃ X ∈ 𝒜, α v e ∪ X = E
  /-- (iii) If `v ∈ V(T)` has valency `3`, incident with distinct `e₁, e₂, e₃`, then
  `α(v, e₁) ∪ α(v, e₂) ∪ α(v, e₃) = E`. -/
  degree_three_union_eq : ∀ ⦃v : ι⦄ ⦃e₁ e₂ e₃ : Sym2 ι⦄,
    IsTreeIncidence T v e₁ → IsTreeIncidence T v e₂ → IsTreeIncidence T v e₃ →
    e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ → α v e₁ ∪ α v e₂ ∪ α v e₃ = E

/-- An incidence `(v, e)` of `T` is passive with respect to a bias `ℬ` and a tree-labelling `α`
(Graph Minors X, Section 3, proof of (3.1), page 160):
"An incidence $(v, e)$ of $T$ is *passive* if $\alpha(v, e)\notin \mathscr{B}$." -/
def IsPassiveIncidence (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β) (ℬ : Set (Set β))
    (v : ι) (e : Sym2 ι) : Prop :=
  IsTreeIncidence T v e ∧ α v e ∉ ℬ

/-- A fork `{e₁, e₂}` in `T` with nub `t` (Graph Minors X, Section 3, page 160):
"A *fork* in $T$ is an unordered pair $\{e_1, e_2\}$ of distinct edges of $T$ with a common
end (the *nub* of the fork)." -/
def IsFork (T : SimpleGraph ι) (t : ι) (e₁ e₂ : Sym2 ι) : Prop :=
  IsTreeIncidence T t e₁ ∧ IsTreeIncidence T t e₂ ∧ e₁ ≠ e₂

/-- A fork `{e₁, e₂}` with nub `t` is exact for `α` (Graph Minors X, Section 3, page 160):
"A fork $\{e_1, e_2\}$ with nub $t$ is *exact* (for $\alpha$) if $\alpha(t, e_1)\cap
\alpha(t, e_2) = \emptyset$." -/
def IsExactFork (α : ι → Sym2 ι → Set β) (t : ι) (e₁ e₂ : Sym2 ι) : Prop :=
  α t e₁ ∩ α t e₂ = ∅

/-- An exact tree-labelling `(T, α)` over `𝒜` (Graph Minors X, Section 3, page 160):
"We say that $(T, \alpha)$ is *exact* if every fork of $T$ is exact." -/
structure IsExactTreeLabelling [Fintype ι] (E : Set β) (κ : Set β → ℤ) (𝒜 : Set (Set β))
    (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β) : Prop where
  /-- `(T, α)` is a tree-labelling over `𝒜`. -/
  isTreeLabelling : IsTreeLabelling E κ 𝒜 T α
  /-- Every fork of `T` is exact for `α`. -/
  isExactFork : ∀ ⦃t : ι⦄ ⦃e₁ e₂ : Sym2 ι⦄, IsFork T t e₁ e₂ → IsExactFork α t e₁ e₂

/-! ## Section 4: Branch-Width -/

/-- `(T, τ)` is a branch-decomposition of a hypergraph `G` (Graph Minors X, Section 4, page 164):
"A *branch-decomposition* of a hypergraph $G$ is a pair $(T, \tau)$, where $T$ is a ternary
tree and $\tau$ is a bijection from the set of leaves of $T$ to $E(G)$." -/
structure IsBranchDecomposition [Fintype ι] (G : Hypergraph α β) (T : SimpleGraph ι)
    (τ : ι → β) : Prop where
  /-- `T` is a ternary tree. -/
  isTernaryTree : IsTernaryTree T
  /-- `τ` is a bijection from the set of leaves of `T` to `E(G)`. -/
  bijOn : Set.BijOn τ (leafSet T) G.edgeSet

/-- The order of an edge `e` of `T` in a branch-decomposition `(T, τ)` of `G`
(Graph Minors X, Section 4, page 164):
"The *order* of an edge $e$ of $T$ is the number of vertices $v$ of $G$ such that there are
leaves $t_1, t_2$ of $T$ in different components of $T \setminus e$, with $\tau(t_1),
\tau(t_2)$ both incident with $v$." -/
noncomputable def branchEdgeOrder [Fintype ι] (G : Hypergraph α β) (T : SimpleGraph ι)
    (τ : ι → β) (e : Sym2 ι) : ℕ :=
  {v ∈ G.vertexSet | ∃ t₁ ∈ leafSet T, ∃ t₂ ∈ leafSet T,
    ¬ (T.deleteEdges {e}).Reachable t₁ t₂ ∧ G.Inc (τ t₁) v ∧ G.Inc (τ t₂) v}.ncard

/-- The width of a branch-decomposition `(T, τ)` of `G` (Graph Minors X, Section 4, page 164):
"The *width* of $(T, \tau)$ is the maximum order of the edges of $T$" -/
noncomputable def branchDecompWidth [Fintype ι] (G : Hypergraph α β) (T : SimpleGraph ι)
    (τ : ι → β) : ℕ :=
  sSup (branchEdgeOrder G T τ '' T.edgeSet)

/-- The branch-width `β(G)` of `G` (Graph Minors X, Section 4, page 164):
"the *branch-width* $\beta(G)$ of $G$ is the minimum width of all branch-decompositions of
$G$ (or 0 if $|E(G)| \le 1$, when $G$ has no branch-decompositions)."

The infimum quantifies over trees whose vertex type `ι` lies in `Type`; see
`IsBranchDecomposition.relabel` and `branchWidth_le_of_isBranchDecomposition` for any finite index
type `ι : Type*`. When `|E(G)| ≤ 1`, `G` has no branch-decompositions and `sInf ∅ = 0`. -/
noncomputable def branchWidth (G : Hypergraph α β) : ℕ :=
  sInf {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → β),
    IsBranchDecomposition G T τ ∧ branchDecompWidth G T τ = w}

/-- `γ(G)`, the maximum size of an edge of `G` (Graph Minors X, Section 4, page 165):
"We denote by $\gamma(G)$ the maximum size of an edge of $G$ (setting $\gamma(G) = 0$ if
$E(G) = \emptyset$)." -/
noncomputable def maxEdgeSize (G : Hypergraph α β) : ℕ :=
  sSup (edgeSize G '' G.edgeSet)

/-- The complete graph `K_n` on `n` vertices, as a hypergraph with vertex set `Fin n` and an edge
`s(u, v)` for every pair of distinct vertices `u, v : Fin n`
(Graph Minors X, Section 4, (4.4), page 166). -/
def completeGraph (n : ℕ) : Hypergraph (Fin n) (Sym2 (Fin n)) where
  vertexSet := Set.univ
  edgeSet := {e : Sym2 (Fin n) | ¬ e.IsDiag}
  Inc e v := ¬ e.IsDiag ∧ v ∈ e
  vertex_mem_of_inc _ _ _ := Set.mem_univ _
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := Set.finite_univ
  edgeSet_finite := Set.toFinite _

/-! ## Section 5: Branch-Width and Tree-Width -/

/-- `t'` lies on the path of `T` between `t` and `t''`: every path in `T` from `t` to `t''`
contains `t'`. In a tree there is a unique such path (`SimpleGraph.IsTree.existsUnique_path`). -/
def OnTreePath (T : SimpleGraph ι) (t t'' t' : ι) : Prop :=
  ∀ p : T.Walk t t'', p.IsPath → t' ∈ p.support

/-- `(T, τ)` is a tree-decomposition of a hypergraph `G` (Graph Minors X, Section 5, page 168):
"A tree-decomposition of a hypergraph $G$ is a pair $(T, \tau)$, where $T$ is a tree and for
$t \in V(T)$, $\tau(t)$ is a subhypergraph of $G$ with the following properties: (i)
$\bigcup (\tau(t) : t \in V(T)) = G$ (ii) for distinct $t, t' \in V(T)$, $E(\tau(t) \cap
\tau(t')) = \emptyset$ (iii) for $t, t', t'' \in V(T)$, if $t'$ is on the path of $T$
between $t$ and $t''$ then $\tau(t) \cap \tau(t'') \subseteq \tau(t')$." -/
structure IsTreeDecomposition [Fintype ι] (G : Hypergraph α β) (T : SimpleGraph ι)
    (τ : ι → Hypergraph α β) : Prop where
  /-- `T` is a tree. -/
  isTree : T.IsTree
  /-- Each `τ(t)` is a subhypergraph of `G`. -/
  le : ∀ t : ι, τ t ≤ G
  /-- (i) `⋃ (τ(t) : t ∈ V(T)) = G`. -/
  biUnion_eq : Hypergraph.biUnion Finset.univ τ = G
  /-- (ii) For distinct `t, t' ∈ V(T)`, `E(τ(t) ∩ τ(t')) = ∅`. -/
  edgeSet_inter_eq : ∀ ⦃t t' : ι⦄, t ≠ t' → (τ t ∩ τ t').edgeSet = ∅
  /-- (iii) For `t, t', t'' ∈ V(T)`, if `t'` is on the path of `T` between `t` and `t''` then
  `τ(t) ∩ τ(t'') ⊆ τ(t')`. -/
  inter_le : ∀ ⦃t t' t'' : ι⦄, OnTreePath T t t'' t' → τ t ∩ τ t'' ≤ τ t'

/-- One plus the width of a tree-decomposition `(T, τ)`: `max_{t ∈ V(T)} |V(τ(t))|` as a natural
number (Graph Minors X, Section 5, page 168). -/
noncomputable def treeDecompWidthPlusOne (τ : ι → Hypergraph α β) : ℕ :=
  sSup (Set.range fun t : ι ↦ (τ t).vertexSet.ncard)

/-- The width of a tree-decomposition `(T, τ)` as an integer (Graph Minors X, Section 5, page 168):
"The width of such a tree-decomposition is the maximum of $(|V(\tau(t))| - 1)$, taken over
all $t \in V(T)$" -/
noncomputable def treeDecompWidth (τ : ι → Hypergraph α β) : ℤ :=
  (treeDecompWidthPlusOne τ : ℤ) - 1

/-- `ω(G) + 1` as a natural number (Graph Minors X, Section 5, page 168):
"the tree-width $\omega(G)$ of $G$ is the minimum width of all tree-decomposition of $G$. (Thus,
$\omega(G) \ge 0$ unless $V(G) = \emptyset$, when $\omega(G) = -1$.)"

Since `ω(G) = -1` when `V(G) = ∅` and Sections 5's main theorems (5.1) and (5.2) are stated in
terms of `ω(G) + 1`, we define `treeWidthPlusOne G : ℕ` as the minimum of
`treeDecompWidthPlusOne τ` over all tree-decompositions `(T, τ)` of `G` (with vertex type in
`Type`; see `IsTreeDecomposition.relabel` and `treeWidthPlusOne_le_of_isTreeDecomposition`), and
`treeWidth G : ℤ` as `(treeWidthPlusOne G : ℤ) - 1`. -/
noncomputable def treeWidthPlusOne (G : Hypergraph α β) : ℕ :=
  sInf {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β),
    IsTreeDecomposition G T τ ∧ treeDecompWidthPlusOne τ = w}

/-- The tree-width `ω(G)` of `G` as an integer (Graph Minors X, Section 5, page 168):
`ω(G) = (ω(G) + 1) - 1`, which is `-1` when `V(G) = ∅` and `≥ 0` otherwise. -/
noncomputable def treeWidth (G : Hypergraph α β) : ℤ :=
  (treeWidthPlusOne G : ℤ) - 1

/-! ## Relabelling of trees in branch- and tree-decompositions -/

/-- The graph isomorphism `T ≃g T.map e.toEmbedding` induced by an equivalence `e : ι ≃ ι'`. -/
def mapIso (T : SimpleGraph ι) (e : ι ≃ ι') : T ≃g T.map e.toEmbedding where
  toEquiv := e
  map_rel_iff' := (SimpleGraph.Iso.map e T).map_rel_iff

/-- Relabelling a tree along `e : ι ≃ ι'` preserves degrees, regardless of the `Fintype` instances
on the neighbor sets. -/
theorem degree_map_equiv (T : SimpleGraph ι) (e : ι ≃ ι') (v : ι)
    {inst₁ : Fintype ((T.map e.toEmbedding).neighborSet (e v))}
    {inst₂ : Fintype (T.neighborSet v)} :
    @SimpleGraph.degree _ (T.map e.toEmbedding) (e v) inst₁ =
      @SimpleGraph.degree _ T v inst₂ := by
  rw [← @SimpleGraph.ncard_neighborSet _ _ _ inst₁,
      ← @SimpleGraph.ncard_neighborSet _ _ _ inst₂]
  refine Set.ncard_congr (fun x _ ↦ e.symm x) ?_ (fun _ _ _ _ h ↦ e.symm.injective h) ?_
  · intro x hx
    have hx' : (T.map e.toEmbedding).Adj (mapIso T e v) (mapIso T e (e.symm x)) := by
      change (T.map e.toEmbedding).Adj (e v) (e (e.symm x))
      rw [e.apply_symm_apply]
      exact hx
    exact (mapIso T e).map_rel_iff.1 hx'
  · intro y hy
    exact ⟨e y, (mapIso T e).map_rel_iff.2 hy, e.symm_apply_apply y⟩

open Classical in
/-- Relabelling the vertex type of a tree along an equivalence `e : ι ≃ ι'` preserves `IsLeaf`. -/
theorem isLeaf_map [Fintype ι] [Fintype ι'] {T : SimpleGraph ι} (e : ι ≃ ι') (v : ι) :
    IsLeaf (T.map e.toEmbedding) (e v) ↔ IsLeaf T v := by
  unfold IsLeaf
  rw [degree_map_equiv T e v]

/-- Relabelling the vertex type of a tree along an equivalence `e : ι ≃ ι'` maps `leafSet T` to
`leafSet (T.map e.toEmbedding)`. -/
theorem leafSet_map [Fintype ι] [Fintype ι'] {T : SimpleGraph ι} (e : ι ≃ ι') :
    leafSet (T.map e.toEmbedding) = e '' leafSet T := by
  ext w
  obtain ⟨v, rfl⟩ := e.surjective w
  simp only [leafSet, Set.mem_ofPred_eq, isLeaf_map, Set.mem_image, EmbeddingLike.apply_eq_iff_eq,
    exists_eq_right]

open Classical in
/-- Relabelling a ternary tree along an equivalence `e : ι ≃ ι'` gives a ternary tree. -/
theorem IsTernaryTree.map [Fintype ι] [Fintype ι'] {T : SimpleGraph ι} (hT : IsTernaryTree T)
    (e : ι ≃ ι') : IsTernaryTree (T.map e.toEmbedding) where
  isTree := (mapIso T e).isTree_iff.1 hT.isTree
  degree_eq_one_or_three w := by
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [degree_map_equiv T e v]
    exact hT.degree_eq_one_or_three v

/-- Relabelling a tree-labelling `α` along an equivalence `e : ι ≃ ι'`. -/
def relabelLabelling (e : ι ≃ ι') (α : ι → Sym2 ι → Set β) : ι' → Sym2 ι' → Set β :=
  fun v' f' ↦ α (e.symm v') (f'.map e.symm)

/-- Relabelling a tree along `e : ι ≃ ι'` preserves `IsTreeIncidence`. -/
theorem isTreeIncidence_map {T : SimpleGraph ι} (e : ι ≃ ι') (v : ι) (f : Sym2 ι) :
    IsTreeIncidence (T.map e.toEmbedding) (e v) (f.map e) ↔ IsTreeIncidence T v f := by
  induction f using Sym2.ind with | _ x y =>
  change s(e x, e y) ∈ (T.map e.toEmbedding).edgeSet ∧ e v ∈ s(e x, e y) ↔
    s(x, y) ∈ T.edgeSet ∧ v ∈ s(x, y)
  simp only [SimpleGraph.mem_edgeSet, Sym2.mem_iff, e.injective.eq_iff]
  exact and_congr_left fun _ ↦ (mapIso T e).map_rel_iff

/-- Relabelling a tree-labelling `(T, α)` along an equivalence `e : ι ≃ ι'` gives a tree-labelling
`(T.map e.toEmbedding, relabelLabelling e α)`. -/
theorem IsTreeLabelling.relabel [Fintype ι] [Fintype ι'] {E : Set β} {κ : Set β → ℤ}
    {𝒜 : Set (Set β)} {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (h : IsTreeLabelling E κ 𝒜 T α) (e : ι ≃ ι') :
    IsTreeLabelling E κ 𝒜 (T.map e.toEmbedding) (relabelLabelling e α) where
  isTernaryTree := h.isTernaryTree.map e
  isEfficient {v' f'} hinc := by
    obtain ⟨v, rfl⟩ := e.surjective v'
    obtain ⟨f, rfl⟩ : ∃ f : Sym2 ι, Sym2.map e f = f' := by
      induction f' using Sym2.ind with | _ x' y' =>
      exact ⟨s(e.symm x', e.symm y'), by simp⟩
    rw [isTreeIncidence_map] at hinc
    simpa [relabelLabelling, Sym2.map_map] using h.isEfficient hinc
  compl_eq {u' v'} hadj := by
    obtain ⟨u, rfl⟩ := e.surjective u'
    obtain ⟨v, rfl⟩ := e.surjective v'
    have hadj' : T.Adj u v := (mapIso T e).map_rel_iff.1 hadj
    simpa [relabelLabelling] using h.compl_eq hadj'
  leaf_eq_or_union_eq {v' f'} hinc hleaf := by
    obtain ⟨v, rfl⟩ := e.surjective v'
    obtain ⟨f, rfl⟩ : ∃ f : Sym2 ι, Sym2.map e f = f' := by
      induction f' using Sym2.ind with | _ x' y' =>
      exact ⟨s(e.symm x', e.symm y'), by simp⟩
    rw [isTreeIncidence_map] at hinc
    rw [isLeaf_map] at hleaf
    simpa [relabelLabelling, Sym2.map_map] using h.leaf_eq_or_union_eq hinc hleaf
  degree_three_union_eq {v' e₁' e₂' e₃'} h₁ h₂ h₃ h12 h13 h23 := by
    obtain ⟨v, rfl⟩ := e.surjective v'
    obtain ⟨e₁, rfl⟩ : ∃ f : Sym2 ι, Sym2.map e f = e₁' := by
      induction e₁' using Sym2.ind with | _ x' y' => exact ⟨s(e.symm x', e.symm y'), by simp⟩
    obtain ⟨e₂, rfl⟩ : ∃ f : Sym2 ι, Sym2.map e f = e₂' := by
      induction e₂' using Sym2.ind with | _ x' y' => exact ⟨s(e.symm x', e.symm y'), by simp⟩
    obtain ⟨e₃, rfl⟩ : ∃ f : Sym2 ι, Sym2.map e f = e₃' := by
      induction e₃' using Sym2.ind with | _ x' y' => exact ⟨s(e.symm x', e.symm y'), by simp⟩
    rw [isTreeIncidence_map] at h₁ h₂ h₃
    simpa [relabelLabelling, Sym2.map_map] using
      h.degree_three_union_eq h₁ h₂ h₃ (ne_of_apply_ne _ h12) (ne_of_apply_ne _ h13)
        (ne_of_apply_ne _ h23)

/-- Relabelling an exact tree-labelling `(T, α)` along an equivalence `e : ι ≃ ι'` gives an exact
tree-labelling. -/
theorem IsExactTreeLabelling.relabel [Fintype ι] [Fintype ι'] {E : Set β} {κ : Set β → ℤ}
    {𝒜 : Set (Set β)} {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (h : IsExactTreeLabelling E κ 𝒜 T α) (e : ι ≃ ι') :
    IsExactTreeLabelling E κ 𝒜 (T.map e.toEmbedding) (relabelLabelling e α) where
  isTreeLabelling := h.isTreeLabelling.relabel e
  isExactFork {t' e₁' e₂'} hf := by
    rcases hf with ⟨h₁, h₂, h12⟩
    obtain ⟨t, rfl⟩ := e.surjective t'
    obtain ⟨e₁, rfl⟩ : ∃ f : Sym2 ι, Sym2.map e f = e₁' := by
      induction e₁' using Sym2.ind with | _ x' y' => exact ⟨s(e.symm x', e.symm y'), by simp⟩
    obtain ⟨e₂, rfl⟩ : ∃ f : Sym2 ι, Sym2.map e f = e₂' := by
      induction e₂' using Sym2.ind with | _ x' y' => exact ⟨s(e.symm x', e.symm y'), by simp⟩
    rw [isTreeIncidence_map] at h₁ h₂
    simpa [IsExactFork, relabelLabelling, Sym2.map_map] using
      h.isExactFork ⟨h₁, h₂, ne_of_apply_ne _ h12⟩

/-- Relabelling a branch-decomposition `(T, τ)` along an equivalence `e : ι ≃ ι'` gives a
branch-decomposition `(T.map e.toEmbedding, τ ∘ e.symm)`. -/
theorem IsBranchDecomposition.relabel [Fintype ι] [Fintype ι'] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → β} (h : IsBranchDecomposition G T τ) (e : ι ≃ ι') :
    IsBranchDecomposition G (T.map e.toEmbedding) (τ ∘ e.symm) where
  isTernaryTree := h.isTernaryTree.map e
  bijOn := by
    rw [leafSet_map]
    refine h.bijOn.comp ⟨?_, fun x _ y _ hxy ↦ e.symm.injective hxy, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      simpa using hx
    · rintro x hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

/-- Relabelling a branch-decomposition preserves the order of every edge. -/
theorem branchEdgeOrder_map [Fintype ι] [Fintype ι'] (G : Hypergraph α β) (T : SimpleGraph ι)
    (τ : ι → β) (e : ι ≃ ι') (f : Sym2 ι) :
    branchEdgeOrder G (T.map e.toEmbedding) (τ ∘ e.symm) (f.map e) =
      branchEdgeOrder G T τ f := by
  classical
  simp only [branchEdgeOrder]
  congr 1
  ext v
  simp only [Set.mem_sep_iff, leafSet_map, Set.mem_image, exists_exists_and_eq_and,
    Function.comp_apply, Equiv.symm_apply_apply]
  refine and_congr_right fun _ ↦ exists_congr fun t₁ ↦ and_congr_right fun _ ↦
    exists_congr fun t₂ ↦ and_congr_right fun _ ↦ and_congr_left fun _ ↦ not_congr ?_
  let φ : (T.deleteEdges {f}) ≃g ((T.map e.toEmbedding).deleteEdges {f.map e}) :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
        refine and_congr (SimpleGraph.Iso.map e T).map_rel_iff (not_congr ?_)
        have : s(e x, e y) = Sym2.map e s(x, y) := rfl
        rw [this, (Sym2.map.injective e.injective).eq_iff] }
  exact ⟨fun ⟨w⟩ ↦ ⟨(w.map φ.symm.toHom).copy (e.symm_apply_apply _) (e.symm_apply_apply _)⟩,
    fun ⟨w⟩ ↦ ⟨w.map φ.toHom⟩⟩

/-- Relabelling a branch-decomposition preserves its width. -/
theorem branchDecompWidth_map [Fintype ι] [Fintype ι'] (G : Hypergraph α β) (T : SimpleGraph ι)
    (τ : ι → β) (e : ι ≃ ι') :
    branchDecompWidth G (T.map e.toEmbedding) (τ ∘ e.symm) = branchDecompWidth G T τ := by
  simp only [branchDecompWidth]
  congr 1
  ext w
  simp only [Set.mem_image]
  constructor
  · rintro ⟨f', hf', rfl⟩
    obtain ⟨f, rfl⟩ : ∃ f : Sym2 ι, Sym2.map e f = f' := by
      induction f' using Sym2.ind with | _ x' y' =>
      exact ⟨s(e.symm x', e.symm y'), by simp⟩
    refine ⟨f, ?_, (branchEdgeOrder_map G T τ e f).symm⟩
    induction f using Sym2.ind with | _ x y =>
    have hf'' : (T.map e.toEmbedding).Adj (e x) (e y) := by
      simpa [SimpleGraph.mem_edgeSet] using hf'
    simpa [SimpleGraph.mem_edgeSet] using (SimpleGraph.Iso.map e T).map_rel_iff.1 hf''
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f.map e, ?_, branchEdgeOrder_map G T τ e f⟩
    induction f using Sym2.ind with | _ x y =>
    have hf' : T.Adj x y := by simpa [SimpleGraph.mem_edgeSet] using hf
    simpa [SimpleGraph.mem_edgeSet] using (SimpleGraph.Iso.map e T).map_rel_iff.2 hf'

/-- Any branch-decomposition `(T, τ)` on an arbitrary finite type `ι : Type*` bounds
`branchWidth G`. -/
theorem branchWidth_le_of_isBranchDecomposition [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → β} (h : IsBranchDecomposition G T τ) :
    branchWidth G ≤ branchDecompWidth G T τ := by
  let e := Fintype.equivFin ι
  apply Nat.sInf_le
  exact ⟨Fin (Fintype.card ι), inferInstance, T.map e.toEmbedding, τ ∘ e.symm,
    h.relabel e, branchDecompWidth_map G T τ e⟩

/-- Relabelling a tree along an equivalence `e : ι ≃ ι'` preserves `OnTreePath`. -/
theorem onTreePath_map {T : SimpleGraph ι} (e : ι ≃ ι') {t₁ t₂ t : ι} :
    OnTreePath (T.map e.toEmbedding) (e t₁) (e t₂) (e t) ↔ OnTreePath T t₁ t₂ t := by
  constructor
  · intro h p hp
    have hp' : (p.map (mapIso T e).toHom).IsPath := hp.map (mapIso T e).injective
    have hm : e t ∈ (p.map (mapIso T e).toHom).support := h (p.map (mapIso T e).toHom) hp'
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    exact e.injective hxe ▸ hx
  · intro h p hp
    have he₁ : (mapIso T e).symm.toHom (e t₁) = t₁ := e.symm_apply_apply t₁
    have he₂ : (mapIso T e).symm.toHom (e t₂) = t₂ := e.symm_apply_apply t₂
    have hq : ((p.map (mapIso T e).symm.toHom).copy he₁ he₂).IsPath := by
      rw [SimpleGraph.Walk.isPath_copy]
      exact hp.map (mapIso T e).symm.injective
    have hm : t ∈ ((p.map (mapIso T e).symm.toHom).copy he₁ he₂).support := h _ hq
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    have : x = e t := by
      apply e.symm.injective
      change e.symm x = t at hxe
      rw [hxe, e.symm_apply_apply]
    exact this ▸ hx

/-- Relabelling a tree-decomposition `(T, τ)` along an equivalence `e : ι ≃ ι'` gives a
tree-decomposition `(T.map e.toEmbedding, τ ∘ e.symm)`. -/
theorem IsTreeDecomposition.relabel [Fintype ι] [Fintype ι'] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ) (e : ι ≃ ι') :
    IsTreeDecomposition G (T.map e.toEmbedding) (τ ∘ e.symm) where
  isTree := (SimpleGraph.Iso.map e T).isTree_iff.1 h.isTree
  le t' := h.le (e.symm t')
  biUnion_eq := by
    rw [← h.biUnion_eq]
    ext v <;> simp only [biUnion, Set.mem_iUnion, Finset.mem_univ, true_and, Function.comp_apply]
    · exact e.symm.exists_congr (fun _ ↦ Iff.rfl)
    · exact e.symm.exists_congr (fun _ ↦ Iff.rfl)
    · exact e.symm.exists_congr (fun _ ↦ Iff.rfl)
  edgeSet_inter_eq t₁ t₂ hne := h.edgeSet_inter_eq (e.symm.injective.ne hne)
  inter_le {t₁ t₂ t₃} hp := by
    apply h.inter_le
    rw [← onTreePath_map e]
    simpa using hp

/-- Relabelling a tree-decomposition preserves `treeDecompWidthPlusOne`. -/
theorem treeDecompWidthPlusOne_comp_equiv (τ : ι → Hypergraph α β)
    (e : ι ≃ ι') :
    treeDecompWidthPlusOne (τ ∘ e.symm) = treeDecompWidthPlusOne τ := by
  simp only [treeDecompWidthPlusOne]
  congr 1
  ext n
  simp only [Set.mem_range, Function.comp_apply]
  exact e.symm.exists_congr (fun _ ↦ Iff.rfl)

/-- Any tree-decomposition `(T, τ)` on an arbitrary finite type `ι : Type*` bounds
`treeWidthPlusOne G`. -/
theorem treeWidthPlusOne_le_of_isTreeDecomposition [Fintype ι] {G : Hypergraph α β}
    {T : SimpleGraph ι} {τ : ι → Hypergraph α β} (h : IsTreeDecomposition G T τ) :
    treeWidthPlusOne G ≤ treeDecompWidthPlusOne τ := by
  let e := Fintype.equivFin ι
  apply Nat.sInf_le
  exact ⟨Fin (Fintype.card ι), inferInstance, T.map e.toEmbedding, τ ∘ e.symm,
    h.relabel e, treeDecompWidthPlusOne_comp_equiv τ e⟩

end GM10

end GraphMinor
