/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs
public import LeanPool.GraphMinor.GM01.Defs
public import LeanPool.GraphMinor.Minor.Model
public import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# Definitions for Graph Minors X, Sections 6–12

This file formalizes the definitions of N. Robertson and P. D. Seymour,
*Graph Minors. X. Obstructions to tree-decomposition*, J. Combin. Theory Ser. B 52 (1991) 153–190,
Sections 6–12 (pages 170–190):

- **Section 2 (page 158):** circuits in a hypergraph (`HasCircuit`), used in (2.10).
- **Section 6 (pages 170–171):** literal minors of a graph (`IsMinor`), the tangle in `G` induced
  by a tangle in a minor `H` (`inducedTangle`), the hypergraph `G / W` obtained by removing `W`
  from the vertex set and keeping all edges (`quotientVertices`), and the tangle `𝒯 / W` in `G / W`
  (`quotientTangle`).
- **Section 7 (pages 171–173):** the `θ`-grid as a hypergraph (`gridHypergraph`), its horizontal
  paths `Pᵢ` (`gridRowPath`) and vertical paths `Qⱼ` (`gridColPath`), the boundary `∂(X)` of an
  edge set `X` (`edgeBoundary`), small edge sets (`IsSmallEdgeSet`), and the grid tangle of order
  `θ` (`gridTangle`).
- **Section 8 (pages 174–177):** robust separations (`IsRobust`), titanic separations
  (`IsTitanic`), the tangle in `G'` constructed from a titanic separation in (8.3)
  (`titanicTransferredTangle`), the tangle in `G \ e` in (8.4) (`deleteEdgeTangle`), and the tangle
  in `G \ W` in (8.5) (`deleteVerticesTangle`).
- **Section 9 (pages 177–180):** crossing of two separations (`SeparationsCross`), laminar sets of
  separations (`IsLaminar`), the subhypergraph `G_i^e` of a component of `T \ e` (`treeDecompSide`),
  separations made by an edge of a tree-decomposition (`MakesSeparation`, `separationsMadeBy`),
  tie-breakers and the three tie-breaker axioms (`TieBreakerAxiom1`, `TieBreakerAxiom2`,
  `TieBreakerAxiom3`, `IsTieBreaker`), smaller `λ`-order (`HasSmallerLambdaOrder`), `λ`-robust
  separations (`IsLambdaRobust`), and doubly `λ`-robust separations (`IsDoublyLambdaRobust`).
- **Section 10 (pages 180–184):** indistinguishable and distinguishable tangles
  (`AreIndistinguishable`, `AreDistinguishable`), separations distinguishing `𝒯₁` from `𝒯₂`
  (`Distinguishes`), the `(𝒯₁, 𝒯₂)`-distinction (`IsDistinction`), homes for a tangle in a
  tree-decomposition (`IsHome`), and standard tree-decompositions relative to `𝒯₁, …, 𝒯ₙ`
  (`IsStandardTreeDecomposition`).
- **Section 11 (pages 184–188):** designs (`Design`, `IsDesign`), the design of a vertex in a
  tree-decomposition (`vertexDesign`), tree-decompositions over a class of designs
  (`IsTreeDecompositionOver`), `n`-enlargements (`IsEnlargementVia`, `IsEnlargement`,
  `enlargementClass`), the class `ℛ_n` of designs with `|V(H)| ≤ n` (`smallDesignClass`), locations
  (`IsLocation`), the design of a location (`locationDesign`), `θ`-pervasive classes of designs
  (`IsPervasive`), and the `Z`-extension of a design (`designExtension`).
- **Section 12 (pages 188–190):** the rank function `r(X)` of a tangle (`tangleRank`), the matroid
  rank axioms of (12.1) (`IsMatroidRankOn`), free sets (`IsFreeSet`), and Tutte-order
  (`tutteOrder`).
-/

@[expose] public section

namespace GraphMinor.GM10

open Graph SimpleGraph Hypergraph

variable {α β α' ι : Type*}

/-! ## Section 2 (continued): Circuits for (2.10) -/

/-- A hypergraph `G` has a circuit (Graph Minors X, Section 2, (2.10), page 158):
either `G` has an edge with at most one end (a loop in a graph), or `G` has two distinct edges with
at least two common ends (parallel edges in a graph), or the 1-skeleton `G.skeleton` has a simple
cycle of length at least `3` (`¬ G.skeleton.IsAcyclic`). For a graph `G`, this is equivalent to `G`
having a circuit in the sense of Graph Minors X. -/
def HasCircuit (G : Hypergraph α β) : Prop :=
  (∃ e ∈ G.edgeSet, (G.ends e).ncard ≤ 1) ∨
    (∃ e₁ ∈ G.edgeSet, ∃ e₂ ∈ G.edgeSet, e₁ ≠ e₂ ∧ 2 ≤ (G.ends e₁ ∩ G.ends e₂).ncard) ∨
    ¬ G.skeleton.IsAcyclic

/-! ## Section 6: New Tangles from Old -/

/-- `H` is a literal minor of `G` (Graph Minors X, Section 4, page 164, and Section 6, (6.1),
page 170): "$H$ can be obtained from a subgraph of $G$ by contracting edges", that is,
`H = contract G' C` for some subgraph `G' ≤ G` and some set of edges `C ⊆ E(G')`. Because
`E(contract G' C) = E(G') \ C ⊆ E(G)`, the edge set of `H` is literally a subset of `E(G)`. -/
def IsMinor (H : Graph (Set α) β) (G : Graph α β) : Prop :=
  ∃ G' ≤ G, ∃ C ⊆ E(G'), H = contract G' C

/-- The tangle in `G` induced by a tangle `𝒯'` in a minor `H` of `G`
(Graph Minors X, Section 6, (6.1), page 170):
"Let $H$ be a minor of a graph $G$, and let $\mathscr{T}'$ be a tangle in $H$ of order
$\theta \ge 2$. Let $\mathscr{T}$ be the set of all separations $(A, B)$ of $G$ of order $<
\theta$ such that there exists $(A', B') \in \mathscr{T}'$ with $E(A') = E(A) \cap E(H)$.
Then $\mathscr{T}$ is a tangle in $G$ of order $\theta$."
"We call $\mathscr{T}$ in (6.1) the tangle in $G$ *induced by* $\mathscr{T}'$."

Here `G` has vertex type `α` and `H` has vertex type `α'` (which is `Set α` when `H = contract G' C`
is a literal minor of a graph `G` viewed as a hypergraph via `Hypergraph.ofGraph`), while both share
the edge type `β` with `E(H) ⊆ E(G)`. Separations `(A, B)` of `G` and `(A', B')` of `H` are
compared through their edge sets in `Set β` via the condition `E(A') = E(A) ∩ E(H)`. -/
def inducedTangle (G : Hypergraph α β) (H : Hypergraph α' β)
    (𝒯' : Set (Hypergraph α' β × Hypergraph α' β)) (θ : ℕ) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧
    ∃ p' ∈ 𝒯', p'.1.edgeSet = p.1.edgeSet ∩ H.edgeSet}

/-- `G / W` for a hypergraph `G` and a set `W` (Graph Minors X, Section 6, page 170):
"Let $G$ be a hypergraph and $W$ a set. We denote by $G/W$ the hypergraph $G'$ with vertex
set $V(G) - W$ and edge set $E(G)$, in which $v \in V(G')$ and $e \in E(G')$ are incident if
and only if they are incident in $G$. (This may produce edges with no ends.)"

Note that `G / W` keeps every edge of `G`, and edges incident with vertices in `W` lose those ends
(possibly all of their ends), so `G / W` is in general not a subhypergraph of `G`. -/
def quotientVertices (G : Hypergraph α β) (W : Set α) : Hypergraph α β where
  vertexSet := G.vertexSet \ W
  edgeSet := G.edgeSet
  Inc e v := G.Inc e v ∧ v ∉ W
  vertex_mem_of_inc _ _ h := ⟨G.vertex_mem_of_inc h.1, h.2⟩
  edge_mem_of_inc _ _ h := G.edge_mem_of_inc h.1
  vertexSet_finite := G.vertexSet_finite.subset Set.sdiff_subset
  edgeSet_finite := G.edgeSet_finite

/-- The tangle `𝒯 / W` in `G / W` (Graph Minors X, Section 6, (6.2), page 171):
"Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$, and let $W \subseteq
V(G)$ with $|W| < \theta$. Let $\mathscr{T}'$ be the set of all separations $(A', B')$ of
$G/W$ such that there exists $(A, B) \in \mathscr{T}$ with $W \subseteq V(A \cap B)$, $A/W =
A'$, and $B/W = B'$. Then $\mathscr{T}'$ is a tangle in $G/W$ of order $\theta - |W|$."
"We denote the tangle $\mathscr{T}'$ of (6.2) by $\mathscr{T}/W$." -/
def quotientTangle (G : Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (W : Set α) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p' | (quotientVertices G W).IsSeparation p'.1 p'.2 ∧
    ∃ p ∈ 𝒯, W ⊆ (p.1 ∩ p.2).vertexSet ∧
      quotientVertices p.1 W = p'.1 ∧ quotientVertices p.2 W = p'.2}

/-! ## Section 7: A Tangle in a Grid -/

/-- The `θ`-grid as a hypergraph (Graph Minors X, Section 7, page 171):
"Let $\theta \ge 2$ be an integer. Let $G$ be a simple graph with $V(G) = \{(i, j) : 1 \le i,
j \le \theta\}$, where $(i, j)$ and $(i', j')$ are adjacent if $|i' - i| + |j' - j| = 1$. We
call $G$ a *$\theta$-grid*."

Here the vertices are `Fin θ × Fin θ` (0-indexed, so `(i, j)` represents `(i + 1, j + 1)`), using
`GM01.gridGraph θ` viewed as a hypergraph via `Hypergraph.ofGraph`. -/
def gridHypergraph (θ : ℕ) : Hypergraph (Fin θ × Fin θ) (Sym2 (Fin θ × Fin θ)) :=
  Hypergraph.ofGraph (GM01.gridGraph θ) Set.finite_univ (Set.toFinite _)

/-- The `i`-th horizontal path `Pᵢ` of the `θ`-grid (Graph Minors X, Section 7, page 171):
"For $1 \le i \le \theta$, let $P_i$ be the path of $G$ with vertex set $\{(i, j) : 1 \le j
\le \theta" -/
def gridRowPath (θ : ℕ) (i : Fin θ) :
    Hypergraph (Fin θ × Fin θ) (Sym2 (Fin θ × Fin θ)) where
  vertexSet := {v : Fin θ × Fin θ | v.1 = i}
  edgeSet := {e ∈ (gridHypergraph θ).edgeSet |
    ∀ v, (gridHypergraph θ).Inc e v → v.1 = i}
  Inc e v := (gridHypergraph θ).Inc e v ∧
    ∀ w, (gridHypergraph θ).Inc e w → w.1 = i
  vertex_mem_of_inc _ _ h := h.2 _ h.1
  edge_mem_of_inc _ _ h := ⟨(gridHypergraph θ).edge_mem_of_inc h.1, h.2⟩
  vertexSet_finite := Set.toFinite _
  edgeSet_finite := Set.toFinite _

/-- The `j`-th vertical path `Qⱼ` of the `θ`-grid (Graph Minors X, Section 7, page 171):
"and for $1 \le j \le \theta$, define $Q_j$ similarly." -/
def gridColPath (θ : ℕ) (j : Fin θ) :
    Hypergraph (Fin θ × Fin θ) (Sym2 (Fin θ × Fin θ)) where
  vertexSet := {v : Fin θ × Fin θ | v.2 = j}
  edgeSet := {e ∈ (gridHypergraph θ).edgeSet |
    ∀ v, (gridHypergraph θ).Inc e v → v.2 = j}
  Inc e v := (gridHypergraph θ).Inc e v ∧
    ∀ w, (gridHypergraph θ).Inc e w → w.2 = j
  vertex_mem_of_inc _ _ h := h.2 _ h.1
  edge_mem_of_inc _ _ h := ⟨(gridHypergraph θ).edge_mem_of_inc h.1, h.2⟩
  vertexSet_finite := Set.toFinite _
  edgeSet_finite := Set.toFinite _

/-- The boundary `∂(X)` of a set of edges `X ⊆ E(G)` (Graph Minors X, Section 7, page 171):
"When $X \subseteq E(G)$, we define $\partial(X)$ to be the set of vertices $v \in X$ such that $v$
is incident with an edge in $X$ and with an edge in $E(G) - X$."
(Here $v \in X$ in the paper is a misprint for $v \in V(G)$.) -/
def edgeBoundary (G : Hypergraph α β) (X : Set β) : Set α :=
  {v ∈ G.vertexSet | (∃ e ∈ X, G.Inc e v) ∧ (∃ e ∈ G.edgeSet \ X, G.Inc e v)}

/-- A subset `X ⊆ E(G)` of the `θ`-grid is small (Graph Minors X, Section 7, page 172):
"If $X \subseteq E(G)$, we say that $X$ is *small* (in $G$) if $|\partial(X)| < \theta$ and
$X$ includes $E(P_i)$ for no $i$ $(1 \le i \le \theta)$." -/
def IsSmallEdgeSet (θ : ℕ) (X : Set (Sym2 (Fin θ × Fin θ))) : Prop :=
  (edgeBoundary (gridHypergraph θ) X).ncard < θ ∧
    ∀ i : Fin θ, ¬ (gridRowPath θ i).edgeSet ⊆ X

/-- The natural tangle of order `θ` in the `θ`-grid (Graph Minors X, Section 7, (7.3), page 173):
"Given a $\theta$-grid $G$ with $P_1, \dots, P_\theta, Q_1, \dots, Q_\theta$ as before, let
$\mathscr{T}$ be the set of all separations $(A, B)$ of $G$ of order $<\theta$ such that
$E(A)$ is small." -/
def gridTangle (θ : ℕ) :
    Set (Hypergraph (Fin θ × Fin θ) (Sym2 (Fin θ × Fin θ)) ×
         Hypergraph (Fin θ × Fin θ) (Sym2 (Fin θ × Fin θ))) :=
  {p | (gridHypergraph θ).IsSeparation p.1 p.2 ∧
    separationOrder p.1 p.2 < θ ∧ IsSmallEdgeSet θ p.1.edgeSet}

/-! ## Section 8: Robust and Titanic Separations -/

/-- A separation `(A, B)` of `G` is robust (Graph Minors X, Section 8, page 174):
"A separation $(A, B)$ of $G$ is *robust* if for every separation $(C, D)$ of $A$, one of the
separations $(C, B \cup D)$, $(D, B \cup C)$ has order at least that of $(A, B)$." -/
def IsRobust (G A B : Hypergraph α β) : Prop :=
  G.IsSeparation A B ∧
    ∀ ⦃C D : Hypergraph α β⦄, A.IsSeparation C D →
      separationOrder A B ≤ separationOrder C (B ∪ D) ∨
        separationOrder A B ≤ separationOrder D (B ∪ C)

/-- A separation `(A, B)` of `G` is titanic (Graph Minors X, Section 8, page 174):
"A separation $(A, B)$ of $G$ is *titanic* if for every triple $(X, Y, Z)$ of subhypergraphs
of $A$ such that $A = X \cup Y \cup Z$ and $E(X)$, $E(Y)$, $E(Z)$ are mutually disjoint, we
have either $$|V((X \cup Y) \cap Z)| \ge |V((X \cup Y) \cap B)|$$ or $$|V((Y \cup Z) \cap
X)| \ge |V((Y \cup Z) \cap B)|$$ or $$|V((Z \cup X) \cap Y)| \ge |V((Z \cup X) \cap B)|.$$" -/
def IsTitanic (G A B : Hypergraph α β) : Prop :=
  G.IsSeparation A B ∧
    ∀ ⦃X Y Z : Hypergraph α β⦄, X ≤ A → Y ≤ A → Z ≤ A → X ∪ Y ∪ Z = A →
      Disjoint X.edgeSet Y.edgeSet → Disjoint Y.edgeSet Z.edgeSet → Disjoint X.edgeSet Z.edgeSet →
      ((X ∪ Y) ∩ B).vertexSet.ncard ≤ ((X ∪ Y) ∩ Z).vertexSet.ncard ∨
        ((Y ∪ Z) ∩ B).vertexSet.ncard ≤ ((Y ∪ Z) ∩ X).vertexSet.ncard ∨
        ((Z ∪ X) ∩ B).vertexSet.ncard ≤ ((Z ∪ X) ∩ Y).vertexSet.ncard

/-- The tangle `𝒯'` in `G'` constructed in (8.3) (Graph Minors X, Section 8, (8.3), page 175):
"Let* $\mathscr{T}'$ *be the set of all separations* $(A', B')$ *of* $G'$ *of order*
$<\theta$ *such that there exists* $(A, B) \in \mathscr{T}$ *with* $E(A \cap D) = E(A' \cap
D)$." -/
def titanicTransferredTangle (G' D : Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p' | G'.IsSeparation p'.1 p'.2 ∧ separationOrder p'.1 p'.2 < θ ∧
    ∃ p ∈ 𝒯, (p.1 ∩ D).edgeSet = (p'.1 ∩ D).edgeSet}

/-- The tangle `𝒯'` in `G \ e` constructed in (8.4) (Graph Minors X, Section 8, (8.4), page 176):
"Let* $\mathscr{T}'$ *be the set of all separations* $(A', B')$ *of* $G \setminus e$ *of
order* $<\theta$ *such that there exists* $(A, B) \in \mathscr{T}$ *with* $E(A \cap (G
\setminus e)) = E(A')$." -/
def deleteEdgeTangle (G : Hypergraph α β) (e : β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p' | (G.deleteEdges {e}).IsSeparation p'.1 p'.2 ∧ separationOrder p'.1 p'.2 < θ ∧
    ∃ p ∈ 𝒯, (p.1 ∩ G.deleteEdges {e}).edgeSet = p'.1.edgeSet}

/-- The tangle `𝒯'` in `G \ W` constructed in (8.5) (Graph Minors X, Section 8, (8.5), page 177):
"Let $\mathscr{T}'$ be the set of all separations $(A', B')$ of $G \setminus W$ of order $<
\theta - |W|$ such that there exists $(A, B) \in \mathscr{T}$ with $W \subseteq V(A \cap B)$
and $A \setminus W = A'$, $B \setminus W = B'$." -/
def deleteVerticesTangle (G : Hypergraph α β) (W : Set α)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p' | (G.deleteVertices W).IsSeparation p'.1 p'.2 ∧ separationOrder p'.1 p'.2 < θ - W.ncard ∧
    ∃ p ∈ 𝒯, W ⊆ (p.1 ∩ p.2).vertexSet ∧
      p.1.deleteVertices W = p'.1 ∧ p.2.deleteVertices W = p'.2}

/-! ## Section 9: Laminar Separations -/

/-- Two separations `(A₁, B₁)` and `(A₂, B₂)` cross (Graph Minors X, Section 9, page 177):
"Let $(A_1, B_1)$, $(A_2, B_2)$ be separations of a hypergraph $G$. We say these separations
*cross* unless either $A_1 \subseteq A_2$ and $B_2 \subseteq B_1$, or $A_1 \subseteq B_2$
and $A_2 \subseteq B_1$, or $B_1 \subseteq A_2$ and $B_2 \subseteq A_1$, or $B_1 \subseteq
B_2$ and $A_2 \subseteq A_1$." -/
def SeparationsCross (A₁ B₁ A₂ B₂ : Hypergraph α β) : Prop :=
  ¬ ((A₁ ≤ A₂ ∧ B₂ ≤ B₁) ∨ (A₁ ≤ B₂ ∧ A₂ ≤ B₁) ∨ (B₁ ≤ A₂ ∧ B₂ ≤ A₁) ∨ (B₁ ≤ B₂ ∧ A₂ ≤ A₁))

/-- A set of separations is laminar (Graph Minors X, Section 9, page 177):
"A set of separations is *laminar* if no two of its members cross." -/
def IsLaminar (𝒮 : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∀ ⦃p₁⦄, p₁ ∈ 𝒮 → ∀ ⦃p₂⦄, p₂ ∈ 𝒮 → ¬ SeparationsCross p₁.1 p₁.2 p₂.1 p₂.2

open Classical in
/-- Given a tree `T`, a mapping `τ : ι → Hypergraph α β`, an edge `e` of `T`, and an end `u` of `e`,
`treeDecompSide T τ e u` is the union `⋃ (τ(t) : t ∈ V(T_u))` over the vertex set of the component
`T_u` of `T \ e` containing `u` (Graph Minors X, Section 9, page 177). -/
noncomputable def treeDecompSide [Fintype ι] (T : SimpleGraph ι) (τ : ι → Hypergraph α β)
    (e : Sym2 ι) (u : ι) : Hypergraph α β :=
  Hypergraph.biUnion (Finset.univ.filter fun t ↦ (T.deleteEdges {e}).Reachable u t) τ

/-- A separation `(A, B)` is made by an edge `e ∈ E(T)` under a tree-decomposition `(T, τ)`
(Graph Minors X, Section 9, page 177):
"Let $(T, \tau)$ be a tree-decomposition of a hypergraph $G$. For each $e \in E(T)$, let
$T_1$, $T_2$ be the components of $T \setminus e$ and let $$ G_i^e = \bigcup (\tau(t) : t
\in V(T_i)) \qquad (i = 1, 2). $$ Then $(G_1^e, G_2^e)$ is a separation of $G$, and we call
$(G_1^e, G_2^e)$ and $(G_2^e, G_1^e)$ the separations *made by* $e$ (under the given
tree-decomposition)." -/
def MakesSeparation [Fintype ι] (T : SimpleGraph ι) (τ : ι → Hypergraph α β)
    (e : Sym2 ι) (A B : Hypergraph α β) : Prop :=
  ∃ u v : ι, T.Adj u v ∧ e = s(u, v) ∧
    A = treeDecompSide T τ s(u, v) u ∧ B = treeDecompSide T τ s(u, v) v

/-- The set of all separations made by edges of `T` under `(T, τ)`
(Graph Minors X, Section 9, (9.1), page 177). -/
def separationsMadeBy [Fintype ι] (T : SimpleGraph ι) (τ : ι → Hypergraph α β) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p | ∃ e ∈ T.edgeSet, MakesSeparation T τ e p.1 p.2}

/-- The first tie-breaker axiom (Graph Minors X, Section 9, page 178):
"(i) if $(A, B)$, $(C, D)$ are separations of $G$, they have the same $\lambda$-order if and
only if $(A, B) = (C, D)$ or $(A, B) = (D, C)$" -/
def TieBreakerAxiom1 {Λ : Type*} (G : Hypergraph α β)
    (lam : Hypergraph α β × Hypergraph α β → Λ) : Prop :=
  ∀ ⦃A B C D : Hypergraph α β⦄, G.IsSeparation A B → G.IsSeparation C D →
    (lam (A, B) = lam (C, D) ↔ (A = C ∧ B = D) ∨ (A = D ∧ B = C))

/-- The second tie-breaker axiom (Graph Minors X, Section 9, page 178):
"(ii) if $(A, B)$, $(C, D)$ are separations of $G$, then either $(A \cup C, B \cap D)$ has
$\lambda$-order at most that of $(A, B)$ or $(A \cap C, B \cup D)$ has $\lambda$-order
smaller than that of $(C, D)$" -/
def TieBreakerAxiom2 {Λ : Type*} [LinearOrder Λ] (G : Hypergraph α β)
    (lam : Hypergraph α β × Hypergraph α β → Λ) : Prop :=
  ∀ ⦃A B C D : Hypergraph α β⦄, G.IsSeparation A B → G.IsSeparation C D →
    lam (A ∪ C, B ∩ D) ≤ lam (A, B) ∨ lam (A ∩ C, B ∪ D) < lam (C, D)

/-- The third tie-breaker axiom (Graph Minors X, Section 9, page 178):
"(iii) if $(A, B)$, $(C, D)$ are separations of $G$ and $(A, B)$ has smaller order than $(C,
D)$, then $(A, B)$ has smaller $\lambda$-order than $(C, D)$." -/
def TieBreakerAxiom3 {Λ : Type*} [LinearOrder Λ] (G : Hypergraph α β)
    (lam : Hypergraph α β × Hypergraph α β → Λ) : Prop :=
  ∀ ⦃A B C D : Hypergraph α β⦄, G.IsSeparation A B → G.IsSeparation C D →
    separationOrder A B < separationOrder C D → lam (A, B) < lam (C, D)

/-- A tie-breaker `λ` in a hypergraph `G` (Graph Minors X, Section 9, pages 177–178):
"A *tie-breaker* $\lambda$ in a hypergraph $G$ is a function from the set of all separations
of $G$ into some linearly ordered set $(\Lambda, <)$, satisfying certain axioms given below.
For each separation $(A, B)$, $\lambda(A, B)$ is called the $\lambda$-*order* of $(A, B)$,
... and, if $(A, B)$, $(C, D)$ are separations, we say that $(A, B)$ has *smaller*
$\lambda$-*order than* $(C, D)$ if $\lambda(A, B) < \lambda(C, D)$. The tie-breaker
$\lambda$ must satisfy the following conditions: (i) if $(A, B)$, $(C, D)$ are separations
of $G$, they have the same $\lambda$-order if and only if $(A, B) = (C, D)$ or $(A, B) = (D,
C)$ (ii) if $(A, B)$, $(C, D)$ are separations of $G$, then either $(A \cup C, B \cap D)$
has $\lambda$-order at most that of $(A, B)$ or $(A \cap C, B \cup D)$ has $\lambda$-order
smaller than that of $(C, D)$ (iii) if $(A, B)$, $(C, D)$ are separations of $G$ and $(A,
B)$ has smaller order than $(C, D)$, then $(A, B)$ has smaller $\lambda$-order than $(C,
D)$. We refer to these as the *first*, *second*, and *third tie-breaker axioms*."

We parameterize `IsTieBreaker` by an arbitrary `LinearOrder Λ` so that theorems taking a
tie-breaker (such as (9.3), (9.4), (10.2), and (10.3)) apply to any linearly ordered codomain `Λ`,
while (9.2) ("In every hypergraph there is a tie-breaker") can instantiate `Λ` with a concrete
linear order (such as `ℕ ×ₗ ℕ ×ₗ ℕ`, or `ℝ ×ₗ ℝ ×ₗ ℝ` as in the paper's proof). Since `G` has only
finitely many separations, any tie-breaker into `(Λ, <)` also induces an order-preserving
tie-breaker into `ℕ`. -/
structure IsTieBreaker {Λ : Type*} [LinearOrder Λ] (G : Hypergraph α β)
    (lam : Hypergraph α β × Hypergraph α β → Λ) : Prop where
  /-- The first tie-breaker axiom (i). -/
  axiom1 : TieBreakerAxiom1 G lam
  /-- The second tie-breaker axiom (ii). -/
  axiom2 : TieBreakerAxiom2 G lam
  /-- The third tie-breaker axiom (iii). -/
  axiom3 : TieBreakerAxiom3 G lam

/-- `(A, B)` has smaller `λ`-order than `(C, D)`: `λ(A, B) < λ(C, D)`
(Graph Minors X, Section 9, page 178). -/
def HasSmallerLambdaOrder {Λ : Type*} [LT Λ]
    (lam : Hypergraph α β × Hypergraph α β → Λ) (A B C D : Hypergraph α β) : Prop :=
  lam (A, B) < lam (C, D)

/-- A separation `(A, B)` of `G` is `λ`-robust (Graph Minors X, Section 9, page 180):
"Given a tie-breaker $\lambda$, a separation $(A, B)$ of $G$ is $\lambda$-*robust* if for
every separation $(C, D)$ of $A$, one of $(C, B \cup D)$, $(D, B \cup C)$ has
$\lambda$-order at least the $\lambda$-order of $(A, B)$." -/
def IsLambdaRobust {Λ : Type*} [LE Λ] (G : Hypergraph α β)
    (lam : Hypergraph α β × Hypergraph α β → Λ) (A B : Hypergraph α β) : Prop :=
  G.IsSeparation A B ∧
    ∀ ⦃C D : Hypergraph α β⦄, A.IsSeparation C D →
      lam (A, B) ≤ lam (C, B ∪ D) ∨ lam (A, B) ≤ lam (D, B ∪ C)

/-- A separation `(A, B)` of `G` is doubly `λ`-robust (Graph Minors X, Section 9, page 180):
"The separation $(A, B)$ is *doubly* $\lambda$-*robust* if both $(A, B)$ and $(B, A)$ are
$\lambda$-robust." -/
def IsDoublyLambdaRobust {Λ : Type*} [LE Λ] (G : Hypergraph α β)
    (lam : Hypergraph α β × Hypergraph α β → Λ) (A B : Hypergraph α β) : Prop :=
  IsLambdaRobust G lam A B ∧ IsLambdaRobust G lam B A

/-! ## Section 10: Tangle Tree-Decompositions -/

/-- Two tangles `𝒯₁` and `𝒯₂` are indistinguishable (Graph Minors X, Section 10, page 180):
"Let $\mathscr{T}_1$, $\mathscr{T}_2$ be tangles in a graph $G$. They are *indistinguishable*
if one is a truncation of the other, that is, either $\mathscr{T}_1 \subseteq \mathscr{T}_2$
or $\mathscr{T}_2 \subseteq \mathscr{T}_1$, and otherwise they are *distinguishable*." -/
def AreIndistinguishable (𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  𝒯₁ ⊆ 𝒯₂ ∨ 𝒯₂ ⊆ 𝒯₁

/-- Two tangles `𝒯₁` and `𝒯₂` are distinguishable (Graph Minors X, Section 10, page 180):
"and otherwise they are *distinguishable*." -/
def AreDistinguishable (𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ¬ AreIndistinguishable 𝒯₁ 𝒯₂

/-- A separation `(A, B)` distinguishes `𝒯₁` from `𝒯₂` (Graph Minors X, Section 10, page 180):
"A separation $(A, B)$ of $G$ *distinguishes* $\mathscr{T}_1$ *from* $\mathscr{T}_2$ if $(A,
B) \in \mathscr{T}_1$ and $(B, A) \in \mathscr{T}_2$." -/
def Distinguishes (𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β))
    (A B : Hypergraph α β) : Prop :=
  (A, B) ∈ 𝒯₁ ∧ (B, A) ∈ 𝒯₂

/-- A separation `(A, B)` is the `(𝒯₁, 𝒯₂)`-distinction with respect to a tie-breaker `λ`
(Graph Minors X, Section 10, page 181):
"Given a tie-breaker $\lambda$, a separation $(A, B)$ which distinguishes $\mathscr{T}_1$
from $\mathscr{T}_2$ is a *$(\mathscr{T}_1, \mathscr{T}_2)$-distinction* if it has minimum
$\lambda$-order of all separations which distinguish $\mathscr{T}_1$ from $\mathscr{T}_2$.
From the first tie-breaker axiom, $(A, B)$ is unique, and we may speak of *the*
$(\mathscr{T}_1, \mathscr{T}_2)$-distinction." -/
def IsDistinction {Λ : Type*} [LE Λ]
    (lam : Hypergraph α β × Hypergraph α β → Λ)
    (𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)) (A B : Hypergraph α β) : Prop :=
  Distinguishes 𝒯₁ 𝒯₂ A B ∧
    ∀ ⦃A' B' : Hypergraph α β⦄, Distinguishes 𝒯₁ 𝒯₂ A' B' → lam (A, B) ≤ lam (A', B')

/-- A vertex `t₀ ∈ V(T)` is a home for a tangle `𝒯` in a tree-decomposition `(T, τ)`
(Graph Minors X, Section 10, proof of (10.3), page 182):
"For $1 \le i \le n$, we say $t_0 \in V(T)$ is a *home* for $\mathscr{T}_i$ if for every $e
\in E(T)$, $$ \left( \bigcup_{t \in V(T_1)} \tau(t), \bigcup_{t \in V(T_2)} \tau(t) \right)
\notin \mathscr{T}_i, $$ where $T_1, T_2$ are the components of $T \setminus e$ and $t_0 \in
V(T_1)$." -/
def IsHome [Fintype ι] (T : SimpleGraph ι) (τ : ι → Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (t₀ : ι) : Prop :=
  ∀ ⦃u v : ι⦄, T.Adj u v → (T.deleteEdges {s(u, v)}).Reachable u t₀ →
    (treeDecompSide T τ s(u, v) u, treeDecompSide T τ s(u, v) v) ∉ 𝒯

/-- A tree-decomposition `(T, τ)` of `G` with `V(T) = Fin n` is a standard tree-decomposition of
`G` relative to `𝒯₁, …, 𝒯ₙ` and tie-breaker `λ` (Graph Minors X, Section 10, (10.3), pages
181–184):
"(i) *For every $e \in E(T)$ and for $1 \le i \le n$, if $T_1, T_2$ are the components of $T
  \setminus e$ and $t_i \in V(T_1)$ then* $$ \left( \bigcup_{t \in V(T_1)} \tau(t), \bigcup_{t
  \in V(T_2)} \tau(t) \right) \notin \mathscr{T}_i. $$ (ii) *For all $i \ne j$ with $1 \le i,
  j \le n$, let $e$ be the edge of the path of $T$ between $t_i$ and $t_j$ making separations
  of smallest $\lambda$-order; then these separations are the $(\mathscr{T}_i,
  \mathscr{T}_j)$- and $(\mathscr{T}_j, \mathscr{T}_i)$-distinctions."
"We call the tree-decomposition of (10.3) the *standard tree-decomposition* of $G$ relative
to $\mathscr{T}_1, \dots, \mathscr{T}_n$." -/
structure IsStandardTreeDecomposition {n : ℕ} {Λ : Type*} [LinearOrder Λ]
    (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → Λ)
    (𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β))
    (T : SimpleGraph (Fin n)) (τ : Fin n → Hypergraph α β) : Prop where
  /-- `(T, τ)` is a tree-decomposition of `G`. -/
  isTreeDecomposition : IsTreeDecomposition G T τ
  /-- (i) Each vertex `i` is a home for `𝒯 i`. -/
  isHome : ∀ i : Fin n, IsHome T τ (𝒯 i) i
  /-- (ii) For `i ≠ j`, on the path in `T` between `i` and `j`, the edge making separations of
  minimum `λ`-order makes the `(𝒯 i, 𝒯 j)`- and `(𝒯 j, 𝒯 i)`-distinctions. -/
  path_min_isDistinction : ∀ ⦃i j : Fin n⦄, i ≠ j →
    ∃ e ∈ T.edgeSet,
      (∀ p : T.Walk i j, p.IsPath → e ∈ p.edges) ∧
      (∀ e' ∈ T.edgeSet, (∀ p : T.Walk i j, p.IsPath → e' ∈ p.edges) →
        ∀ A B A' B', MakesSeparation T τ e A B → MakesSeparation T τ e' A' B' →
          lam (A, B) ≤ lam (A', B')) ∧
      ∃ A B, MakesSeparation T τ e A B ∧
        IsDistinction lam (𝒯 i) (𝒯 j) A B ∧ IsDistinction lam (𝒯 j) (𝒯 i) B A

/-! ## Section 11: Structure Relative to a Tangle -/

/-- A design `(H, M)` (Graph Minors X, Section 11, page 185):
"A design is a pair $(H, M)$, where $H$ is a hypergraph and $M$ is a set of subsets of $V(H)$." -/
abbrev Design (α β : Type*) := Hypergraph α β × Set (Set α)

/-- A pair `(H, M)` is a valid design if every member of `M` is a subset of `V(H)`
(Graph Minors X, Section 11, page 185). -/
def IsDesign (d : Design α β) : Prop :=
  ∀ ⦃X : Set α⦄, X ∈ d.2 → X ⊆ d.1.vertexSet

/-- The design of a vertex `t₀ ∈ V(T)` in a tree-decomposition `(T, τ)`
(Graph Minors X, Section 11, page 185):
"If $(T, \tau)$ is a tree-decomposition of a hypergraph $G$ and $t_0 \in V(T)$, and $t_0$ has
neighbours $t_1, \dots, t_k$ in $T$, then $$ (\tau(t_0), \{V(\tau(t_0) \cap \tau(t_i)): 1
\le i \le k\}) $$ is a design, called the *design of $t_0$ in $(T, \tau)$*." -/
def vertexDesign (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (t₀ : ι) : Design α β :=
  (τ t₀, {X | ∃ t, T.Adj t₀ t ∧ X = (τ t₀ ∩ τ t).vertexSet})

/-- A tree-decomposition `(T, τ)` of `G` is over a class of designs `𝒮`
(Graph Minors X, Section 11, page 185):
"If $\mathscr{S}$ is a class of designs, a tree-decomposition $(T, \tau)$ is said to be *over
$\mathscr{S}$* if for each $t_0 \in V(T)$, $\mathscr{S}$ contains the design of $t_0$ in
$(T, \tau)$." -/
def IsTreeDecompositionOver [Fintype ι] (G : Hypergraph α β) (𝒮 : Set (Design α β))
    (T : SimpleGraph ι) (τ : ι → Hypergraph α β) : Prop :=
  IsTreeDecomposition G T τ ∧ ∀ t₀ : ι, vertexDesign T τ t₀ ∈ 𝒮

/-- `(H', M')` is an enlargement of `(H, M)` via `Z ⊆ V(H')`
(Graph Minors X, Section 11, page 185):
"Let $(H, M)$, $(H', M')$ be designs and let $Z \subseteq V(H')$ be such that (i) $H$ is a
subhypergraph of $H'$ and $V(H') - V(H) \subseteq Z$ (ii) every edge of $H'$ is an edge of
$H$ (iii) for every $X \in M'$ with $X \ne Z$, $X \cap V(H) \in M$. ($Z$ may or may not be a
member of $M'$.) In these circumstances, we say that $(H', M')$ is an *$n$-enlargement* of
$(H, M)$ for every integer $n \ge |Z|$." -/
structure IsEnlargementVia (d d' : Design α β) (Z : Set α) : Prop where
  /-- `d` is a design. -/
  isDesign : IsDesign d
  /-- `d'` is a design. -/
  isDesign' : IsDesign d'
  /-- `Z ⊆ V(H')`. -/
  subset_vertexSet : Z ⊆ d'.1.vertexSet
  /-- (i) `H` is a subhypergraph of `H'`. -/
  le : d.1 ≤ d'.1
  /-- (i) `V(H') - V(H) ⊆ Z`. -/
  sdiff_subset : d'.1.vertexSet \ d.1.vertexSet ⊆ Z
  /-- (ii) Every edge of `H'` is an edge of `H`. -/
  edgeSet_subset : d'.1.edgeSet ⊆ d.1.edgeSet
  /-- (iii) For every `X ∈ M'` with `X ≠ Z`, `X ∩ V(H) ∈ M`. -/
  inter_mem : ∀ ⦃X : Set α⦄, X ∈ d'.2 → X ≠ Z → X ∩ d.1.vertexSet ∈ d.2

/-- `(H', M')` is an `n`-enlargement of `(H, M)` (Graph Minors X, Section 11, page 185). -/
def IsEnlargement (n : ℕ) (d d' : Design α β) : Prop :=
  ∃ Z : Set α, Z.ncard ≤ n ∧ IsEnlargementVia d d' Z

/-- `𝒮^n`, the class of all `n`-enlargements of members of `𝒮`
(Graph Minors X, Section 11, page 185):
"If $\mathscr{S}$ is a class of designs, we denote the class of all $n$-enlargements of
members of $\mathscr{S}$ by $\mathscr{S}^n$." -/
def enlargementClass (𝒮 : Set (Design α β)) (n : ℕ) : Set (Design α β) :=
  {d' | ∃ d ∈ 𝒮, IsEnlargement n d d'}

/-- `ℛ_n`, the class of all designs `(H, M)` with `|V(H)| ≤ n`
(Graph Minors X, Section 11, page 185):
"For any integer $n \ge 0$, we denote by $\mathscr{R}_n$ the class of all designs $(H, M)$
with $|V(H)| \le n$." -/
def smallDesignClass (n : ℕ) : Set (Design α β) :=
  {d | IsDesign d ∧ d.1.vertexSet.ncard ≤ n}

/-- A location `ℒ` in a hypergraph `G` (Graph Minors X, Section 11, page 185):
"A *location* in a hypergraph $G$ is a set $\{(A_1, B_1), \dots, (A_k, B_k)\}$ of separations
of $G$ such that $A_i \subseteq B_j$ for all distinct $i, j$ with $1 \le i, j \le k$."
Since `G` is finite, any set of separations of `G` is finite. -/
structure IsLocation (G : Hypergraph α β)
    (ℒ : Set (Hypergraph α β × Hypergraph α β)) : Prop where
  /-- Every member of `ℒ` is a separation of `G`. -/
  isSeparation : ∀ ⦃p⦄, p ∈ ℒ → G.IsSeparation p.1 p.2
  /-- For distinct `p₁, p₂ ∈ ℒ`, `A₁ ⊆ B₂`. -/
  left_le_right : ∀ ⦃p₁⦄, p₁ ∈ ℒ → ∀ ⦃p₂⦄, p₂ ∈ ℒ → p₁ ≠ p₂ → p₁.1 ≤ p₂.2

/-- The intersection `G ∩ B₁ ∩ … ∩ B_k` for a set `ℒ` of separations of `G`
(Graph Minors X, Section 11, page 185). -/
def locationCore (G : Hypergraph α β)
    (ℒ : Set (Hypergraph α β × Hypergraph α β)) : Hypergraph α β where
  vertexSet := {v ∈ G.vertexSet | ∀ p ∈ ℒ, v ∈ p.2.vertexSet}
  edgeSet := {e ∈ G.edgeSet | ∀ p ∈ ℒ, e ∈ p.2.edgeSet}
  Inc e v := G.Inc e v ∧ (∀ p ∈ ℒ, v ∈ p.2.vertexSet) ∧ (∀ p ∈ ℒ, e ∈ p.2.edgeSet)
  vertex_mem_of_inc _ _ h := ⟨G.vertex_mem_of_inc h.1, h.2.1⟩
  edge_mem_of_inc _ _ h := ⟨G.edge_mem_of_inc h.1, h.2.2⟩
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
  edgeSet_finite := G.edgeSet_finite.subset fun _ h ↦ h.1

/-- The design of a location `ℒ` in `G` (Graph Minors X, Section 11, page 185):
"If $\{(A_1, B_1), \dots, (A_k, B_k)\}$ is a location in $G$, then
$$
(G \cap B_1 \cap \dots \cap B_k; \{V(A_i \cap B_i): 1 \le i \le k\})
$$
is a design, which we call the *design of the location*." -/
def locationDesign (G : Hypergraph α β)
    (ℒ : Set (Hypergraph α β × Hypergraph α β)) : Design α β :=
  (locationCore G ℒ, (fun p ↦ (p.1 ∩ p.2).vertexSet) '' ℒ)

/-- A class of designs `𝒮` is `θ`-pervasive in a hypergraph `G`
(Graph Minors X, Section 11, page 185):
"Let $\theta \ge 1$ be an integer, and let $\mathscr{S}$ be a class of designs. We say that
$\mathscr{S}$ is *$\theta$-pervasive* in a hypergraph $G$ if for every subhypergraph $G'$ of
$G$ and every tangle $\mathscr{T}$ in $G'$ of order $\ge \theta$ there is a location
$\mathscr{L}$ in $G'$ such that $\mathscr{L} \subseteq \mathscr{T}$ and the design of
$\mathscr{L}$ belongs to $\mathscr{S}$." -/
def IsPervasive (G : Hypergraph α β) (θ : ℕ) (𝒮 : Set (Design α β)) : Prop :=
  ∀ ⦃G' : Hypergraph α β⦄, G' ≤ G →
    ∀ ⦃θ' : ℕ⦄ ⦃𝒯 : Set (Hypergraph α β × Hypergraph α β)⦄,
      θ ≤ θ' → IsTangle G' θ' 𝒯 →
      ∃ ℒ, IsLocation G' ℒ ∧ ℒ ⊆ 𝒯 ∧ locationDesign G' ℒ ∈ 𝒮

/-- The `Z`-extension `(H, M ∪ {Z})` of a design `(H, M)`
(Graph Minors X, Section 11, page 186):
"If $(H, M)$ is a design and $Z \subseteq V(H)$ then $(H, M \cup \{Z\})$ is a design, which
we call the *$Z$-extension* of $(H, M)$." -/
def designExtension (d : Design α β) (Z : Set α) : Design α β :=
  (d.1, insert Z d.2)

/-! ## Section 12: Tangles and Matroids -/

open Classical in
/-- The rank function `r(X)` of a tangle `𝒯` of order `θ` in `G`
(Graph Minors X, Section 12, page 188):
"Let $\mathscr{T}$ be a tangle in a hypergraph $G$, of order $\theta$. For $X \subseteq
V(G)$, let us define $r(X)$ to be the least order of a separation $(A, B) \in \mathscr{T}$
with $X \subseteq V(A)$, if one exists, and $\theta$ otherwise." -/
noncomputable def tangleRank
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) (X : Set α) : ℕ :=
  if ∃ p ∈ 𝒯, X ⊆ p.1.vertexSet then
    sInf {k : ℕ | ∃ p ∈ 𝒯, X ⊆ p.1.vertexSet ∧ separationOrder p.1 p.2 = k}
  else
    θ

/-- `r` satisfies the matroid rank axioms on `E` (Graph Minors X, Section 12, (12.1),
pages 188–189):
"(i) $r$ is integral-valued (ii) for $X \subseteq V(G)$, $0 \le r(X) \le |X|$ (iii) for $X
\subseteq Y \subseteq V(G)$, $r(X) \le r(Y)$ (iv) for $X, Y \subseteq V(G)$, $r(X \cup Y) +
r(X \cap Y) \le r(X) + r(Y)$."
Condition (i) and `0 ≤ r(X)` are automatic for `r : Set α → ℕ`. -/
structure IsMatroidRankOn (E : Set α) (r : Set α → ℕ) : Prop where
  /-- (ii) For `X ⊆ E`, `r(X) ≤ |X|`. -/
  le_ncard : ∀ ⦃X : Set α⦄, X ⊆ E → r X ≤ X.ncard
  /-- (iii) For `X ⊆ Y ⊆ E`, `r(X) ≤ r(Y)`. -/
  mono : ∀ ⦃X Y : Set α⦄, X ⊆ Y → Y ⊆ E → r X ≤ r Y
  /-- (iv) For `X, Y ⊆ E`, `r(X ∪ Y) + r(X ∩ Y) ≤ r(X) + r(Y)`. -/
  submodular : ∀ ⦃X Y : Set α⦄, X ⊆ E → Y ⊆ E → r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y

/-- A subset `X ⊆ V(G)` is free with respect to a tangle `𝒯` of order `θ`
(Graph Minors X, Section 12, page 189):
"Thus, given $\mathscr{T}$, $G$ as before, let us say that $X \subseteq V(G)$ is *free* if
$|X| \le \theta$ and there is no $(A, B) \in \mathscr{T}$ of order $< |X|$ with $X \subseteq
V(A)$." -/
def IsFreeSet (G : Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) (X : Set α) : Prop :=
  X ⊆ G.vertexSet ∧ X.ncard ≤ θ ∧
    ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → X ⊆ A.vertexSet → X.ncard ≤ separationOrder A B

/-- The Tutte-order of a separation `(A, B)` of `G` (Graph Minors X, Section 12, page 189):
"$$|V(A \cap B)| + 1 + \kappa(G) - \kappa(A) - \kappa(B),$$ where $\kappa(F)$ denotes the
number of components of $F$, for a subgraph $F$ of $G$" -/
noncomputable def tutteOrder (G A B : Hypergraph α β) : ℤ :=
  (separationOrder A B : ℤ) + 1 +
    (Nat.card (G.skeleton.induce G.vertexSet).ConnectedComponent : ℤ) -
    (Nat.card (A.skeleton.induce A.vertexSet).ConnectedComponent : ℤ) -
    (Nat.card (B.skeleton.induce B.vertexSet).ConnectedComponent : ℤ)

end GraphMinor.GM10
