/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Minor.CompleteGraph

public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM16.ProperArrangementDefs
public import LeanPool.GraphMinor.GM05.Defs

/-!
# Definitions for Graph Minors XVI: Excluding a non-planar graph

This file formalizes the definitions of N. Robertson and P. D. Seymour,
*Graph Minors. XVI. Excluding a non-planar graph*, J. Combin. Theory Ser. B 89 (2003) 43–76,
over the shared definitions from `GraphMinor.GM09.Defs`, `GraphMinor.GM10.Defs`,
`GraphMinor.GM10.Defs2`, `GraphMinor.GM11.Defs`, `GraphMinor.GM14.Defs`, and
`GraphMinor.GM15.Defs`:

- **Section 1 (pages 43–46):** clique-sums (`IsCliqueSum`), tree-structures over a class of graphs
  (`HasTreeStructureOver`), tree-width via tree-structures (`HasTreeWidthLE`), the complete graph
  $K_n$ (`completeGraph`), the Wagner graph $V_8$ (`wagnerGraphV8`), drawings of a graph in a
  surface (`CanBeDrawnIn`), $(\le n)$-vertex extensions (`IsVertexExtension`), $r$-rings with
  perimeter $t_1, \dots, t_n$ (`IsRRing`).
- **Section 2 (pages 47–48):** designs, locations, tree-decompositions, and $n$-enlargements over
  graphs (`GraphDesign`, `IsGraphDesign`, `IsGraphLocation`, `graphLocationCore`,
  `graphLocationDesign`, `IsGraphPervasive`, `IsGraphTreeDecomposition`, `graphVertexDesign`,
  `IsGraphTreeDecompositionOver`, `IsGraphEnlargementVia`, `IsGraphEnlargement`,
  `graphEnlargementClass`, `smallGraphDesignClass`), and torsos of a design (`IsTorsoOfDesign`,
  `torsosOfClass`).
- **Section 3 (pages 48–52):** proper arrangements (`IsProperArrangement`), $\rho$-vortices in the
  sense of Graph Minors XVI (`IsRhoVortex`), segregations of type $(\rho, \kappa)$ in the sense of
  Graph Minors XVI (`IsSegregationOfType`), tangles controlling an $L$-minor (`ControlsMinor`),
  and the statements of (3.1) and (3.2) (`GM16Theorem31Statement`, `GM16Theorem32Statement`).
- **Section 5 & Section 6 (pages 54–61):** horns at $v \in V(G) \setminus V(\eta(H))$ of breadth
  $\ge \theta$ (`IsHorn`), animals $(H, \eta, \mathcal{T}, X, Y)$ with $\chi$ horns and $\delta$
  hairs of strength $\ge (\theta, \sigma)$ (`IsAnimal`, `HasAnimal`), and hairless animals
  (`IsHairlessAnimal`, `HasHairlessAnimal`).
- **Section 8 (pages 64–70):** $\gamma$-envelopes $(\Lambda_y : y \in Y)$ around $Y \subseteq V(H)$
  (`IsEnvelope`, `clearEnvelopeDrawing`).
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15

export GM14 (IsRegionChain regionalDistance IsBattlefield)
export GM15 (IsCentralSegregation)

universe u v w

/-! ## Section 1: Tree-Structure, Clique-Sums, Vertex Extensions, and Rings (pages 43–46) -/

section Section1

variable {α : Type u} {β : Type v}

/-- Embed a graph `G : Graph α β` into the edge type `β ⊕ ℕ` via `Sum.inl`, providing an
infinite supply of fresh edge labels `Sum.inr n` for clique-sums. -/
def liftEdgeInl (G : Graph α β) : Graph α (β ⊕ ℕ) where
  vertexSet := V(G)
  edgeSet := Sum.inl '' E(G)
  IsLink e x y := ∃ e₀, e = Sum.inl e₀ ∧ G.IsLink e₀ x y
  isLink_symm _ _ := ⟨fun _ _ ⟨e₀, he, hlink⟩ => ⟨e₀, he, hlink.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h1 h2 := by
    rcases h1 with ⟨_, he₁, h₁⟩
    rcases h2 with ⟨_, he₂, h₂⟩
    cases he₁.symm.trans he₂
    exact G.eq_or_eq_of_isLink_of_isLink h₁ h₂
  edge_mem_iff_exists_isLink e := by
    rcases e with e₀ | n
    · simp only [mem_image, Sum.inl.injEq, exists_eq_right, exists_eq_left']
      exact G.edge_mem_iff_exists_isLink e₀
    · simp
  left_mem_of_isLink _ _ _ h := by
    rcases h with ⟨_, _, hlink⟩
    exact hlink.left_mem

@[simp]
theorem vertexSet_liftEdgeInl (G : Graph α β) : V(liftEdgeInl G) = V(G) := rfl

@[simp]
theorem edgeSet_liftEdgeInl (G : Graph α β) : E(liftEdgeInl G) = Sum.inl '' E(G) := rfl

@[simp]
theorem liftEdgeInl_isLink_inl {G : Graph α β} {e : β} {x y : α} :
    (liftEdgeInl G).IsLink (Sum.inl e) x y ↔ G.IsLink e x y :=
  ⟨fun ⟨_, he, hlink⟩ => Sum.inl.inj he ▸ hlink, fun hlink => ⟨e, rfl, hlink⟩⟩

@[simp]
theorem not_liftEdgeInl_isLink_inr {G : Graph α β} {n : ℕ} {x y : α} :
    ¬ (liftEdgeInl G).IsLink (Sum.inr n) x y := by
  rintro ⟨_, he, _⟩
  cases he

/-- Every graph `G` is canonically isomorphic to `liftEdgeInl G`. -/
noncomputable def isoLiftEdgeInl (G : Graph α β) : Iso G (liftEdgeInl G) where
  vertexEquiv := Equiv.refl V(G)
  edgeEquiv := Equiv.Set.image Sum.inl E(G) Sum.inl_injective
  isLink_iff _ _ _ := liftEdgeInl_isLink_inl.symm

/-- `K` is a complete graph with vertex set `W` (no loops, and a unique edge joining each pair of
distinct vertices of `W`). -/
def IsCompleteGraphOn (K : Graph α β) (W : Set α) : Prop :=
  V(K) = W ∧ (∀ e x, ¬ K.IsLoopAt e x) ∧
    ∀ x ∈ W, ∀ y ∈ W, x ≠ y → ∃! e, K.IsLink e x y

/-- Clique-sum of graphs (Graph Minors XVI, Section 1, page 44):
"Let $G$ be a graph with a separation $(H_1, H_2)$ (that is, $H_1$ and $H_2$ are subgraphs of $G$
with no common edges and $H_1 \cup H_2 = G$). Let $K$ be a complete graph with
$V(K) = V(H_1) \cap V(H_2)$ and with no edges in common with $H_1$ and $H_2$. Let
$G_i = H_i \cup K$ ($i = 1, 2$). Then we say that $G$ is the *clique-sum* of $G_1$ and $G_2$." -/
def IsCliqueSum (G G₁ G₂ : Graph α β) : Prop :=
  ∃ H₁ H₂ K : Graph α β,
    IsGraphSeparation G H₁ H₂ ∧
    IsCompleteGraphOn K (V(H₁) ∩ V(H₂)) ∧
    IsGraphSeparation G₁ H₁ K ∧
    IsGraphSeparation G₂ H₂ K

/-- Tree-structure over a class of graphs (Graph Minors XVI, Section 1, page 44):
"If $G$ can be constructed from members of a class $\mathcal{C}$ of graphs by (repeated) clique-sums
we say that $G$ is a *tree-structure over* $\mathcal{C}$." -/
inductive HasTreeStructureOver (𝒞 : Set (Graph α β)) : Graph α β → Prop
  | base {G : Graph α β} (hG : G ∈ 𝒞) : HasTreeStructureOver 𝒞 G
  | cliqueSum {G G₁ G₂ : Graph α β}
      (hsum : IsCliqueSum G G₁ G₂)
      (h₁ : HasTreeStructureOver 𝒞 G₁)
      (h₂ : HasTreeStructureOver 𝒞 G₂) : HasTreeStructureOver 𝒞 G

/-- Tree-width $\le N$ via tree-structures (Graph Minors XVI, Section 1, page 44):
"Let us say that $G$ has *tree-width* $\le N$ if $G$ is a tree-structure over the class of all
graphs with $\le N + 1$ vertices (and the smallest such $N$ is of course the *tree-width* of $G$)."
-/
def HasTreeWidthLE (G : Graph α β) (N : ℕ) : Prop :=
  HasTreeStructureOver {H : Graph α (β ⊕ ℕ) | V(H).encard ≤ (N + 1 : ℕ)} (liftEdgeInl G)

/-- The surface `S` has a drawing of the graph `H`: `H` can be drawn in `S`
(Graph Minors XVI, Section 1, page 44). -/
def CanBeDrawnIn {α' : Type*} {β' : Type*} (S : Type w) [TopologicalSpace S]
    (H : Graph α' β') : Prop :=
  ∃ (ν : α' → S) (edgeOf : β' → Set S), InjOn ν V(H) ∧
    (∀ e ∈ E(H), ∀ u v : α', H.IsLink e u v → u ≠ v →
      IsLineWithEnds (edgeOf e) (ν u) (ν v)) ∧
    (∀ e ∈ E(H), ∀ v : α', H.IsLoopAt e v → IsOArc (edgeOf e) ∧ ν v ∈ edgeOf e) ∧
    (∀ e ∈ E(H), ∀ f ∈ E(H), e ≠ f → edgeOf e ∩ edgeOf f ⊆ ν '' V(H)) ∧
    (∀ e ∈ E(H), ∀ v ∈ V(H), ν v ∈ edgeOf e → H.Inc e v)

/-- The complete graph $K_n$ on `Fin n` with edge type `Sym2 (Fin n)`
(Graph Minors XVI, Section 1, page 44). -/
abbrev completeGraph (n : ℕ) : Graph (Fin n) (Sym2 (Fin n)) := GraphMinor.completeGraph n

/-- The Wagner graph $V_8$ (Graph Minors XVI, Section 1, page 44):
"($V_8$ is obtained from an eight-vertex circuit by adding edges joining the four opposite pairs of
vertices.)" -/
def wagnerGraphV8 : Graph (Fin 8) (Fin 12) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y :=
    if h : e.1 < 8 then
      (x.1 = e.1 ∧ y.1 = (e.1 + 1) % 8) ∨ (y.1 = e.1 ∧ x.1 = (e.1 + 1) % 8)
    else
      (x.1 = e.1 - 8 ∧ y.1 = (e.1 - 8 + 4) % 8) ∨ (y.1 = e.1 - 8 ∧ x.1 = (e.1 - 8 + 4) % 8)
  isLink_symm e _ := ⟨fun x y h => by
    by_cases he : e.1 < 8 <;> simp only [he, ↓reduceDIte] at h ⊢ <;> exact h.symm⟩
  eq_or_eq_of_isLink_of_isLink e x y z w h1 h2 := by
    by_cases he : e.1 < 8 <;> simp only [he, ↓reduceDIte] at h1 h2
    · rcases h1 with ⟨hx, hy⟩ | ⟨hy, hx⟩ <;> rcases h2 with ⟨hz, hw⟩ | ⟨hw, hz⟩
      · left; exact Fin.ext (hx.trans hz.symm)
      · right; exact Fin.ext (hx.trans hw.symm)
      · right; exact Fin.ext (hx.trans hw.symm)
      · left; exact Fin.ext (hx.trans hz.symm)
    · rcases h1 with ⟨hx, hy⟩ | ⟨hy, hx⟩ <;> rcases h2 with ⟨hz, hw⟩ | ⟨hw, hz⟩
      · left; exact Fin.ext (hx.trans hz.symm)
      · right; exact Fin.ext (hx.trans hw.symm)
      · right; exact Fin.ext (hx.trans hw.symm)
      · left; exact Fin.ext (hx.trans hz.symm)
  edge_mem_iff_exists_isLink e := by
    simp only [mem_univ, true_iff]
    by_cases he : e.1 < 8
    · refine ⟨⟨e.1, he⟩, ⟨(e.1 + 1) % 8, Nat.mod_lt _ (by decide)⟩, ?_⟩
      simp [he]
    · refine ⟨⟨e.1 - 8, by omega⟩, ⟨(e.1 - 8 + 4) % 8, Nat.mod_lt _ (by decide)⟩, ?_⟩
      simp [he]
  left_mem_of_isLink _ _ _ _ := Set.mem_univ _

/-- $(\le n)$-vertex extension (Graph Minors XVI, Section 1, page 45):
"If a subgraph $G'$ of $G$ can be obtained from $G$ by deleting $\le n$ vertices of $G$, let us call
$G$ a *($\le n$)-vertex extension* of $G'$." -/
def IsVertexExtension (n : ℕ) (G G' : Graph α β) : Prop :=
  ∃ Z ⊆ V(G), Z.encard ≤ n ∧ deleteVertices G Z = G'

/-- Loose $(\le n)$-vertex extension: `G'` is a subgraph of `G` and there exists $Z \subseteq V(G)$
with $|Z| \le n$ such that $G \setminus Z = G' \setminus Z$.
This notion is not in the paper. It is here for the sentence on page 48 claiming that every torso of
a member of $\mathscr{D}^n$ is a $(\le n)$-vertex extension of a torso of a member of $\mathscr{D}$,
and for (2.3) (`theorem_2_3_proof`): because the definition of $\mathscr{D}^n$ on page 47 allows
$Z \subseteq V(H')$ to meet $V(H)$ and allows $Z \in M'$ without $Z \cap V(H) \in M$, a torso $G$
of $(H', M') \in \mathscr{D}^n$ can have torso edges with both ends in $Z \cap V(H)$, so the torso
$G' = H \cup (G \setminus Z)$ of $(H, M)$ keeps the vertices of $Z \cap V(H)$ and satisfies
$G \setminus Z = G' \setminus Z$ rather than $G \setminus Z = G'$. -/
def IsLooseVertexExtension (n : ℕ) (G G' : Graph α β) : Prop :=
  ∃ Z ⊆ V(G), Z.encard ≤ n ∧ G' ≤ G ∧ deleteVertices G Z = deleteVertices G' Z

/-- $r$-ring with perimeter $t_1, \dots, t_n$ (Graph Minors XVI, Section 1, page 45):
"More precisely, we say $G$ is an *$r$-ring with perimeter $t_1, \dots, t_n$* if
$t_1, \dots, t_n \in V(G)$ are distinct and there is a sequence $X_1, \dots, X_n$ of subsets of
$V(G)$, such that
* $X_1 \cup \dots \cup X_n = V(G)$, and every edge of $G$ has both ends in some $X_i$,
* $t_i \in X_1$ for $1 \le i \le n$,
* $X_i \cap X_k \subseteq X_j$ for $1 \le i \le j \le k \le n$,
* $|X_i| \le r$ for $1 \le i \le n$."
The print has "$t_i \in X_1$", a misprint for $t_i \in X_i$, which the Lean uses. See the
correction on page 45 in `corrections/GM16.md`. -/
def IsRRing (G : Graph α β) (r : ℕ) (t : List α) : Prop :=
  t.Nodup ∧ (∀ x ∈ t, x ∈ V(G)) ∧
  ∃ X : Fin t.length → Set α,
    (∀ i, X i ⊆ V(G)) ∧
    (⋃ i, X i) = V(G) ∧
    (∀ e ∈ E(G), ∃ i, ∀ v : α, G.Inc e v → v ∈ X i) ∧
    (∀ i : Fin t.length, t[i.1] ∈ X i) ∧
    (∀ i j k : Fin t.length, i ≤ j → j ≤ k → X i ∩ X k ⊆ X j) ∧
    (∀ i : Fin t.length, (X i).encard ≤ r)

end Section1

/-! ## Section 2: Designs, Locations, Tree-Decompositions, and Torsos (pages 47–48) -/

section Section2

variable {α : Type u} {β : Type v} {ι : Type*}

/-- A design `(H, M)` where `H` is a graph and `M` is a set of subsets of `V(H)`
(Graph Minors XVI, Section 2, page 47):
"A *design* is a pair $(H, M)$ where $H$ in a graph and $M$ is a set of subsets of $V(H)$."
("$H$ in a graph" is a misprint for "$H$ is a graph". See the correction on page 47 in
`corrections/GM16.md`.) -/
abbrev GraphDesign (α : Type u) (β : Type v) := Graph α β × Set (Set α)

/-- `d = (H, M)` is a valid graph design if `H` is finite and every `X ∈ M` is a subset of `V(H)`
(Graph Minors XVI, Section 2, page 47). -/
def IsGraphDesign (d : GraphDesign α β) : Prop :=
  V(d.1).Finite ∧ E(d.1).Finite ∧ ∀ ⦃X : Set α⦄, X ∈ d.2 → X ⊆ V(d.1)

/-- A location in a graph `G` (Graph Minors XVI, Section 2, page 47):
"A *location* in $G$ is a set $\{(A_1, B_1), \ldots, (A_k, B_k)\}$ of separations of $G$ such that
$A_i \subseteq B_j$ for all distinct $i, j$ with $1 \le i, j \le k$." -/
structure IsGraphLocation (G : Graph α β)
    (ℒ : Set (Graph α β × Graph α β)) : Prop where
  /-- `ℒ` is finite. -/
  finite : ℒ.Finite
  /-- Every member of `ℒ` is a separation of `G`. -/
  isSeparation : ∀ ⦃p⦄, p ∈ ℒ → IsGraphSeparation G p.1 p.2
  /-- For distinct `p₁, p₂ ∈ ℒ`, `A₁ ≤ B₂`. -/
  left_le_right : ∀ ⦃p₁⦄, p₁ ∈ ℒ → ∀ ⦃p₂⦄, p₂ ∈ ℒ → p₁ ≠ p₂ → p₁.1 ≤ p₂.2

/-- The core subgraph `G ∩ B₁ ∩ ⋯ ∩ B_k` of a location `ℒ` in `G`
(Graph Minors XVI, Section 2, page 47). -/
def graphLocationCore (G : Graph α β) (ℒ : Set (Graph α β × Graph α β)) : Graph α β :=
  (G.induce {v ∈ V(G) | ∀ p ∈ ℒ, v ∈ V(p.2)}).restrict {e ∈ E(G) | ∀ p ∈ ℒ, e ∈ E(p.2)}

/-- The design of a location `ℒ` in `G` (Graph Minors XVI, Section 2, page 47):
"If $\{(A_1, B_1), \ldots, (A_k, B_k)\}$ is a location then
$$(G \cap B_1 \cap \cdots \cap B_k, \{V(A_i \cap B_i) \colon 1 \le i \le k\})$$
is a design, which we call the *design of the location*." -/
def graphLocationDesign (G : Graph α β) (ℒ : Set (Graph α β × Graph α β)) : GraphDesign α β :=
  (graphLocationCore G ℒ, (fun p => V(p.1) ∩ V(p.2)) '' ℒ)

/-- A separation `(A_H, B_H)` of `Hypergraph.ofGraph G` corresponds to a graph separation `(A, B)`
of `G`. -/
def SeparationOfGraphSep (G A B : Graph α β) (A_H B_H : Hypergraph α β) : Prop :=
  IsGraphSeparation G A B ∧
    A_H.vertexSet = V(A) ∧ A_H.edgeSet = E(A) ∧
    B_H.vertexSet = V(B) ∧ B_H.edgeSet = E(B)

/-- A class of designs `𝒟` is `θ`-pervasive in a graph `G`
(Graph Minors XVI, Section 2, page 47):
"Let $\theta \ge 1$ be an integer, and let $\mathscr{D}$ be a class of designs. We say that
$\mathscr{D}$ is *$\theta$-pervasive in a graph $G$* if for every subgraph $G'$ of $G$ and every
tangle $\mathscr{T}$ in $G'$ of order $\ge \theta$ there is a location $\mathscr{L} \subseteq
\mathscr{T}$
with its design in $\mathscr{D}$." -/
def IsGraphPervasive (G : Graph α β) (θ : ℕ) (𝒟 : Set (GraphDesign α β)) : Prop :=
  ∀ ⦃G' : Graph α β⦄, G' ≤ G →
    ∀ ⦃θ' : ℕ⦄ ⦃𝒯 : Set (Hypergraph α β × Hypergraph α β)⦄,
      θ ≤ θ' → IsGraphTangle G' θ' 𝒯 →
      ∃ ℒ : Set (Graph α β × Graph α β),
        IsGraphLocation G' ℒ ∧
        (∀ p ∈ ℒ, ∃ p_H ∈ 𝒯, SeparationOfGraphSep G' p.1 p.2 p_H.1 p_H.2) ∧
        graphLocationDesign G' ℒ ∈ 𝒟

/-- A tree-decomposition `(T, τ)` of a graph `G` (Graph Minors XVI, Section 2, page 47):
"A *tree-decomposition* of a graph $G$ is a pair $(T, \tau)$, where $T$ is a tree and for each
$t \in V(T)$, $\tau(t)$ is a subgraph of $G$, such that
* $\cup(\tau(t) \colon t \in V(T)) = G$, and $E(\tau(t) \cap \tau(t')) = \emptyset$ for all
  distinct $t, t' \in V(T)$,
* if $t, t', t'' \in V(T)$ and $t'$ lies on the path of $T$ between $t$ and $t''$ then
  $\tau(t) \cap \tau(t'') \subseteq \tau(t')$." -/
structure IsGraphTreeDecomposition [Fintype ι] (G : Graph α β)
    (T : SimpleGraph ι) (τ : ι → Graph α β) : Prop where
  /-- `T` is a tree. -/
  isTree : T.IsTree
  /-- Each `τ t` is a subgraph of `G`. -/
  le_G : ∀ t : ι, τ t ≤ G
  /-- `⋃_t τ(t) = G` on vertices. -/
  vertexSet_union : (⋃ t : ι, V(τ t)) = V(G)
  /-- `⋃_t τ(t) = G` on edges. -/
  edgeSet_union : (⋃ t : ι, E(τ t)) = E(G)
  /-- `E(τ(t) ∩ τ(t')) = ∅` for distinct `t, t'`. -/
  edge_disjoint : ∀ ⦃t₁ t₂ : ι⦄, t₁ ≠ t₂ → Disjoint E(τ t₁) E(τ t₂)
  /-- Interpolation along paths in `T`: `V(τ(t₁)) ∩ V(τ(t₃)) ⊆ V(τ(t₂))` when `t₂` lies on a path of
  `T` between `t₁` and `t₃`. -/
  inter_subset_of_mem_path : ∀ ⦃t₁ t₂ t₃ : ι⦄ (p : T.Walk t₁ t₃),
    p.IsPath → t₂ ∈ p.support → V(τ t₁) ∩ V(τ t₃) ⊆ V(τ t₂)

/-- The design of a vertex `t₀ ∈ V(T)` in a tree-decomposition `(T, τ)` of a graph `G`
(Graph Minors XVI, Section 2, page 47):
"If $(T, \tau)$ is a tree-decomposition of $G$ and $t_0 \in V(T)$, and $t_0$ has neighbours
$t_1, \ldots, t_k \in V(T)$, then
$$(\tau(t_0), \{V(\tau(t_0) \cap \tau(t_i)) \colon 1 \le i \le k\})$$
is a design, called the *design of $t_0$ in $(T, \tau)$*." -/
def graphVertexDesign (T : SimpleGraph ι) (τ : ι → Graph α β) (t₀ : ι) : GraphDesign α β :=
  (τ t₀, {X : Set α | ∃ t : ι, T.Adj t₀ t ∧ X = V(τ t₀) ∩ V(τ t)})

/-- `(T, τ)` is a tree-decomposition of `G` whose vertex designs all belong to `𝒟`
(Graph Minors XVI, Section 2, page 48). -/
def IsGraphTreeDecompositionOver [Fintype ι] (G : Graph α β) (𝒟 : Set (GraphDesign α β))
    (T : SimpleGraph ι) (τ : ι → Graph α β) : Prop :=
  IsGraphTreeDecomposition G T τ ∧ ∀ t₀ : ι, graphVertexDesign T τ t₀ ∈ 𝒟

/-- `(H', M')` is an `n`-enlargement of `(H, M)` via `Z ⊆ V(H')`
(Graph Minors XVI, Section 2, page 47):
"Let $(H, M)$, $(H', M')$ be designs. We say that $(H', M')$ is an *$n$-enlargement of $(H, M)$* if
there exists $Z \subseteq V(H')$ such that
* $H$ is a subgraph of $H'$ and $V(H') \setminus V(H) \subseteq Z$,
* every edge of $H'$ is an edge of $H$,
* for every $X \in M'$ with $X \ne Z$, $X \cap V(H) \in M$,
* $n$ is an integer and $|Z| \le n$." -/
structure IsGraphEnlargementVia (d d' : GraphDesign α β) (Z : Set α) : Prop where
  /-- `d` is a design. -/
  isDesign : IsGraphDesign d
  /-- `d'` is a design. -/
  isDesign' : IsGraphDesign d'
  /-- `Z ⊆ V(H')`. -/
  subset_vertexSet : Z ⊆ V(d'.1)
  /-- `H ≤ H'`. -/
  le : d.1 ≤ d'.1
  /-- `V(H') \ V(H) ⊆ Z`. -/
  sdiff_subset : V(d'.1) \ V(d.1) ⊆ Z
  /-- `E(H') ⊆ E(H)`. -/
  edgeSet_subset : E(d'.1) ⊆ E(d.1)
  /-- For every `X ∈ M'` with `X ≠ Z`, `X ∩ V(H) ∈ M`. -/
  inter_mem : ∀ ⦃X : Set α⦄, X ∈ d'.2 → X ≠ Z → X ∩ V(d.1) ∈ d.2

/-- `(H', M')` is an `n`-enlargement of `(H, M)` (Graph Minors XVI, Section 2, page 47). -/
def IsGraphEnlargement (n : ℕ) (d d' : GraphDesign α β) : Prop :=
  ∃ Z : Set α, Z.ncard ≤ n ∧ IsGraphEnlargementVia d d' Z

/-- The class `𝒟^n` of all `n`-enlargements of members of `𝒟`
(Graph Minors XVI, Section 2, page 47):
"If $\mathscr{D}$ is a class of designs and $n \ge 0$ is an integer, the class of all
$n$-enlargements of members of $\mathscr{D}$ is denoted by $\mathscr{D}^n$." -/
def graphEnlargementClass (𝒟 : Set (GraphDesign α β)) (n : ℕ) : Set (GraphDesign α β) :=
  {d' | ∃ d ∈ 𝒟, IsGraphEnlargement n d d'}

/-- The class `ℛ_n` of all designs `(H, M)` with `|V(H)| ≤ n`
(Graph Minors XVI, Section 2, page 47):
"The class of all designs $(H, M)$ with $|V(H)| \le n$ is denoted by $\mathscr{R}_n$." -/
def smallGraphDesignClass (n : ℕ) : Set (GraphDesign α β) :=
  {d | IsGraphDesign d ∧ V(d.1).ncard ≤ n}

/-- Torso of a design `(H, M)` (Graph Minors XVI, Section 2, page 48):
"Let $(H, M)$ be a design. A graph $H'$ is a *torso* of $(H, M)$ if $V(H) = V(H')$, $H$ is a
subgraph of $H'$, and for every $e \in E(H') \setminus E(H)$ there exists $X \in M$ including the
ends of $e$." -/
def IsTorsoOfDesign (d : GraphDesign α β) (H' : Graph α β) : Prop :=
  V(d.1) = V(H') ∧
  d.1 ≤ H' ∧
  ∀ e ∈ E(H') \ E(d.1), ∃ X ∈ d.2, ∀ v : α, H'.Inc e v → v ∈ X

/-- The class `𝒟'` of torsos of members of `𝒟` (Graph Minors XVI, Section 2, (2.2), page 48). -/
def torsosOfClass (𝒟 : Set (GraphDesign α β)) : Set (Graph α β) :=
  {H' : Graph α β | ∃ d ∈ 𝒟, IsTorsoOfDesign d H'}

end Section2

/-! ## Section 3: Proper Arrangements, $\rho$-Vortices, Segregations of Type $(\rho, \kappa)$, and
Controlling Minors (pages 48–52) -/

section Section3

variable {α : Type u} {β : Type v}

/-- A society `(G, Ω)` is a `ρ`-vortex in the sense of Graph Minors XVI
(Graph Minors XVI, Section 3, page 49):
"A society $(G, \Omega)$ is a *$\rho$-vortex*, where $\rho \ge 0$ is an integer, if for all distinct
$u, v \in \bar{\Omega}$ there do not exist $\rho + 1$ mutually vertex-disjoint paths of $G$ between
$I \cup \{u\}$ and $J \cup \{v\}$, where $I$ denotes the set of vertices in $\bar{\Omega}$ after $u$
and before $v$ and $J$ is the set after $v$ and before $u$, in the natural sense (so
$(I \cup \{u\}, J \cup \{v\})$ is a partition of $\bar{\Omega}$)." -/
def IsRhoVortex (S : Society α β) (ρ : ℕ) : Prop :=
  ∀ u ∈ S.Ω.bar, ∀ v ∈ S.Ω.bar, u ≠ v →
    ¬ ∃ P : Fin (ρ + 1) → Graph α β,
      Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
      ∀ i : Fin (ρ + 1),
        ∃ a ∈ S.Ω.interval u v ∪ {u}, ∃ b ∈ S.Ω.interval v u ∪ {v},
          IsGraphPathWithEnds S.G (P i) a b

/-- A segregation `S_seg` of `G` is of type `(ρ, κ)` in the sense of Graph Minors XVI
(Graph Minors XVI, Section 3, page 49):
"A segregation $\mathscr{S}$ is of *type $(\rho, \kappa)$*, where $\rho, \kappa \ge 0$ are integers,
if $|\bar{\Omega}| > 3$ for at most $\kappa$ members $(A, \Omega)$ of $\mathscr{S}$, and each such
member is a $\rho$-vortex." -/
structure IsSegregationOfType (G : Graph α β) (ρ κ : ℕ) (S_seg : Set (Society α β)) : Prop where
  /-- `S_seg` is a segregation of `G`. -/
  isSegregation : IsGraphSegregation G S_seg
  /-- At most `κ` members `(A, Ω) ∈ S_seg` satisfy `|ΩBar| > 3`. -/
  vortex_count_le : {S ∈ S_seg | 3 < S.Ω.bar.ncard}.ncard ≤ κ
  /-- Every member `(A, Ω) ∈ S_seg` with `|ΩBar| > 3` is a `ρ`-vortex (`IsRhoVortex S ρ`). -/
  is_rho_vortex : ∀ ⦃S : Society α β⦄, S ∈ S_seg → 3 < S.Ω.bar.ncard → IsRhoVortex S ρ

/-- A tangle `T_star` in a graph `G` controls an `L`-minor of `G`
(Graph Minors XVI, Section 3, page 49):
"Let $L$ be a graph, and let $\mathscr{T}^*$ be a tangle in a graph $G$. We say that $\mathscr{T}^*$
*controls an $L$-minor of $G$* if there is a function $\alpha$, with domain $V(L) \cup E(L)$, such
that
* for each $v \in V(L)$, $\alpha(v)$ is a non-null connected subgraph of $G$, and for all distinct
  $u, v \in V(L)$, $\alpha(u)$ and $\alpha(v)$ are vertex-disjoint,
* for each $e \in E(L)$ with distinct ends $u, v$, $\alpha(e) \in E(G)$ with one end in
  $V(\alpha(u))$ and the other in $V(\alpha(v))$,
* for every loop $e \in E(L)$ with end $v$, $\alpha(e) \in E(G) \setminus E(\alpha(v))$ with both
  ends in $V(\alpha(v))$,
* for all distinct $e, f \in E(L)$, $\alpha(e) \ne \alpha(f)$,
* there is no $(A, B) \in \mathscr{T}^*$ of order $< |V(L)|$ and $v \in V(L)$ such that
  $V(\alpha(v)) \subseteq V(A)$." -/
def ControlsMinor {α' : Type*} {β' : Type*} (G : Graph α β) (L : Graph α' β')
    (T_star : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∃ (α_v : α' → Graph α β) (α_e : β' → β),
    (∀ v ∈ V(L), α_v v ≤ G ∧ V(α_v v).Nonempty ∧ GraphConnected (α_v v)) ∧
    (∀ u ∈ V(L), ∀ v ∈ V(L), u ≠ v → Disjoint V(α_v u) V(α_v v)) ∧
    (∀ e ∈ E(L), ∀ u ∈ V(L), ∀ v ∈ V(L), u ≠ v → L.IsLink e u v →
      α_e e ∈ E(G) ∧ ∃ x ∈ V(α_v u), ∃ y ∈ V(α_v v), G.IsLink (α_e e) x y) ∧
    (∀ e ∈ E(L), ∀ v ∈ V(L), L.IsLoopAt e v →
      α_e e ∈ E(G) \ E(α_v v) ∧ ∃ x ∈ V(α_v v), ∃ y ∈ V(α_v v), G.IsLink (α_e e) x y) ∧
    InjOn α_e E(L) ∧
    ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ T_star → separationOrder A B < V(L).ncard →
      ∀ v ∈ V(L), ¬ V(α_v v) ⊆ A.vertexSet

/-- The deleted-vertices tangle `T \ Z` in `G \ Z` (Graph Minors XVI, Section 3, page 49):
"If $\mathscr{T}$ is a tangle in $G$ of order $\theta$ and $Z \subseteq V(G)$ with $|Z| < \theta$,
we
denote by $\mathscr{T} \setminus Z$ the set of all separations $(A', B')$ of $G \setminus Z$ of
order
$<\theta - |Z|$ such that there exists $(A, B) \in \mathscr{T}$ with $Z \subseteq V(A \cap B)$,
$A \setminus Z = A'$ and $B \setminus Z = B'$." -/
def deleteGraphVerticesTangle (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (Z : Set α) (T : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) :
    Set (Hypergraph α β × Hypergraph α β) :=
  GM10.deleteVerticesTangle (Hypergraph.ofGraph G hV hE) Z T θ

/-- Statement of Graph Minors XVI, (3.1) (page 49):
"For any graph $L$, there are integers $\kappa, \rho, \zeta \ge 0$ and $\theta \ge 1$ with the
following property. Let $\mathscr{T}$ be a tangle of order $\ge \theta$ in a graph $G$, controlling
no $L$-minor of $G$. Then there exists $Z \subseteq V(G)$ with $|Z| \le \zeta$, and a
$\mathscr{T} \setminus Z$-central segregation of $G \setminus Z$ of type $(\rho, \kappa)$ which has
a
proper arrangement in some surface in which $L$ cannot be drawn." -/
def GM16Theorem31Statement : Prop :=
  ∀ {α' : Type*} {β' : Type*} (L : Graph α' β'), V(L).Finite → E(L).Finite →
    ∃ κ ρ ζ θ : ℕ, 1 ≤ θ ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_G : ℕ)
        (T : Set (Hypergraph α β × Hypergraph α β))
        (hT : IsGraphTangle G θ_G T),
        θ ≤ θ_G → ¬ ControlsMinor G L T →
        ∃ (Z : Set α) (S_seg : Set (Society α β))
          (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
          (α_disc : Society α β → Set S) (α_pt : α → S),
          Z ⊆ V(G) ∧ Z.ncard ≤ ζ ∧ Z.ncard < θ_G ∧
          IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
          IsCentralSegregation (deleteVertices G Z)
            (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T θ_G) S_seg ∧
          IsSegregationOfType (deleteVertices G Z) ρ κ S_seg ∧
          IsProperArrangement S_seg α_disc α_pt

/-- Statement of Graph Minors XVI, (3.2) (page 50):
"Let $(G, \Omega)$ be a $\rho$-vortex, and let the vertices in $\bar{\Omega}$ be $t_1, \ldots, t_n$
in order, where $n \ge 1$. Then there are separations $(A_1, B_1), \ldots, (A_n, B_n)$ of $G$, such
that:
1. $t_1, \ldots, t_n \in V(B_i)$ for $1 \le i \le n$,
2. $t_i \in V(A_i)$ for $1 \le i \le n$,
3. $\mathscr{L} = \{(A_1, B_1), \ldots, (A_n, B_n)\}$ is a location in $G$,
4. $(A_i, B_i)$ has order $\le 2\rho + 1$ for $1 \le i \le n$, and
5. every torso of the design of $\mathscr{L}$ is a $(2\rho + 1)$-ring with perimeter
$t_1, \ldots, t_n$." -/
def GM16Theorem32Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (S : Society α β) (ρ n : ℕ) (t : Fin n → α),
    1 ≤ n → IsRhoVortex S ρ →
    Injective t → range t = S.Ω.bar → S.Ω.IsClockwiseSeq (List.ofFn t) →
    ∃ A B : Fin n → Graph α β,
      (∀ i : Fin n, IsGraphSeparation S.G (A i) (B i)) ∧
      (∀ i j : Fin n, t j ∈ V(B i)) ∧
      (∀ i : Fin n, t i ∈ V(A i)) ∧
      IsGraphLocation S.G (range fun i : Fin n => (A i, B i)) ∧
      (∀ i : Fin n, (V(A i) ∩ V(B i)).ncard ≤ 2 * ρ + 1) ∧
      (∀ H' : Graph α β,
        IsTorsoOfDesign (graphLocationDesign S.G (range fun i : Fin n => (A i, B i))) H' →
        IsRRing H' (2 * ρ + 1) (List.ofFn t))

end Section3

/-! ## Section 5 & Section 6: Horns and Animals (pages 54–61) -/

section Section5And6

variable {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}

/-- Horn at $v \in V(G) \setminus V(\eta(H))$ of breadth $\ge \theta$ over $H, \eta, \mathcal{T}$
(Graph Minors XVI, Section 5, page 55):
"A horn at $v$ of breadth $\ge \theta$ (over $H, \eta, \mathscr{T}$) is a set
$\{P_1, \dots, P_\sigma\}$ of paths of $G$, such that
* $P_1, \dots, P_\sigma$ each have one end $v$ and are otherwise mutually disjoint,
* for $1 \le i \le \sigma$, $P_i$ has precisely one vertex in $V(\eta(H))$, its end different from
  $v$; let this end be $\eta(u_i)$, where $u_i \in V(H)$,
* for $1 \le i < j \le \sigma$, $d(u_i, u_j) \ge \theta$ where $d$ is the metric of $\mathscr{T}$
  (see [8, section 3])." -/
def IsHorn (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (d : Set S → Set S → ℕ) (v : α) (θ σ : ℕ)
    (P : Fin σ → Graph α β) (u : Fin σ → S) : Prop :=
  v ∈ V(G) \ V(η.imageGraph) ∧
  (∀ i : Fin σ, u i ∈ H.V) ∧
  (∀ i : Fin σ, IsGraphPathWithEnds G (P i) v (η.vMap (u i))) ∧
  (∀ i : Fin σ, V(P i) ∩ V(η.imageGraph) = {η.vMap (u i)}) ∧
  (∀ i j : Fin σ, i ≠ j → V(P i) ∩ V(P j) = {v} ∧ Disjoint E(P i) E(P j)) ∧
  (∀ i j : Fin σ, i ≠ j → θ ≤ d {u i} {u j})

/-- Animal $(H, \eta, \mathcal{T}, X, Y)$ with $\chi$ horns and $\delta$ hairs, of strength
$\ge (\theta, \sigma)$ (Graph Minors XVI, Section 5, page 55):
"Let $\Sigma$ be a surface. An animal (in $G$, with respect to $\mathscr{T}^*$) is a quintuple
$(H, \eta, \mathscr{T}, X, Y)$, such that $H, \eta, \mathscr{T}$ is a $\Sigma$-span,
$X \subseteq V(G) \setminus V(\eta(H))$ and $Y \subseteq V(H)$. If $|X| = \chi$ and $|Y| = \delta$,
we call this an animal with $\chi$ horns and $\delta$ hairs. The animal has strength
$\ge (\theta, \sigma)$, where $\theta \ge 1$ and $\sigma \ge 0$ are integers, if
* $\mathscr{T}$ has order $\ge \theta$,
* for each $v \in X$ there is a horn at $v$ of cardinality $\ge \sigma$ and breadth $\ge \theta$,
* for each $u \in Y$ there is an $\eta(H)$-path (see [8, section 3]) $P$ with ends
  $\eta(u), \eta(v)$ say, such that $X \cap V(P) = \emptyset$ and $d(u, v) \ge \theta$, where $d$ is
  the metric of $\mathscr{T}$,
* $d(u_1, u_2) \ge \theta$ for all distinct $u_1, u_2 \in Y$." -/
def IsAnimal (G : Graph α β)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (θ_star : ℕ)
    (H : Drawing S) (η : SpanEmbedding H G) (θ_span : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (X : Set α) (Y : Set S) (χ δ θ σ : ℕ) : Prop :=
  1 ≤ θ ∧ θ ≤ θ_span ∧
  IsSigmaSpan G H η θ_star θ_span T_star T ∧
  HasTangleMetric H θ_span T d ∧
  X ⊆ V(G) \ V(η.imageGraph) ∧ X.ncard = χ ∧
  Y ⊆ H.V ∧ Y.ncard = δ ∧
  (∀ v ∈ X, ∃ (P : Fin σ → Graph α β) (u : Fin σ → S),
    IsHorn G H η d v θ σ P u) ∧
  (∀ u ∈ Y, ∃ (v : S) (P : Graph α β),
    v ∈ H.V ∧ u ≠ v ∧ IsHPathWithEnds G η.imageGraph P (η.vMap u) (η.vMap v) ∧
    Disjoint X V(P) ∧ θ ≤ d {u} {v}) ∧
  (∀ u₁ ∈ Y, ∀ u₂ ∈ Y, u₁ ≠ u₂ → θ ≤ d {u₁} {u₂})

/-- Existence of an animal in `G` with respect to `T_star` on surface `S` with `χ` horns and `δ`
hairs, of strength `≥ (θ, σ)` (Graph Minors XVI, Section 5, page 55). -/
def HasAnimal (S : Type w) [TopologicalSpace S] [T2Space S]
    (G : Graph α β) (T_star : Set (Hypergraph α β × Hypergraph α β)) (θ_star : ℕ)
    (χ δ θ σ : ℕ) : Prop :=
  ∃ (H : Drawing S) (η : SpanEmbedding H G) (θ_span : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (X : Set α) (Y : Set S),
    IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ σ

/-- Hairless animal (Graph Minors XVI, Section 5, page 55):
"The animal $(H, \eta, \mathscr{T}, X, Y)$ is hairless if $Y = \emptyset$, and in that case we shall
speak of $(H, \eta, \mathscr{T}, X)$ or $(H, \mathscr{T}, X)$." -/
def IsHairlessAnimal (G : Graph α β)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) (θ_star : ℕ)
    (H : Drawing S) (η : SpanEmbedding H G) (θ_span : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (X : Set α) (χ θ σ : ℕ) : Prop :=
  IsAnimal G T_star θ_star H η θ_span T d X ∅ χ 0 θ σ

/-- Existence of a hairless animal in `G` with respect to `T_star` on surface `S` with `χ` horns,
of strength `≥ (θ, σ)` (Graph Minors XVI, Section 5, page 55). -/
def HasHairlessAnimal (S : Type w) [TopologicalSpace S] [T2Space S]
    (G : Graph α β) (T_star : Set (Hypergraph α β × Hypergraph α β)) (θ_star : ℕ)
    (χ θ σ : ℕ) : Prop :=
  HasAnimal S G T_star θ_star χ 0 θ σ

end Section5And6

/-! ## Section 8: $\gamma$-Envelopes around $Y \subseteq V(H)$ (pages 64–70) -/

section Section8

variable {S : Type w} [TopologicalSpace S] [T1Space S]

/-- $\gamma$-envelope around $Y \subseteq V(H)$ (Graph Minors XVI, Section 8, page 64):
"Let $\mathcal{T}$ be a respectful tangle (see [8, section 3]) of order $\theta$ in a rigid drawing
$H$ in a surface $\Sigma$, and let $Y \subseteq V(H)$. If $\gamma \ge 0$, a *$\gamma$-envelope
around
$Y$* is a family $(\Lambda_y\colon y \in Y)$ such that:
- for each $y \in Y$, $\Lambda_y$ is a $\gamma$-zone around $y$,
- for all distinct $y, y' \in Y$, $\bar{\Lambda}_y \cap \bar{\Lambda}_{y'} = \emptyset$,
- for every subset $Y' \subseteq Y$, the drawing $H \cap (\Sigma \setminus \cup (\Lambda_y\colon y
  \in Y'))$
  is rigid." -/
def IsEnvelope (H : Drawing S) (d : Set S → Set S → ℕ)
    (Y : Set S) (γ : ℕ) (Λ : S → Set S) : Prop :=
  Y ⊆ H.V ∧
  (∀ y ∈ Y, IsLambdaZoneAround H d γ {y} (Λ y)) ∧
  (∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → Disjoint (closure (Λ y₁)) (closure (Λ y₂))) ∧
  (∀ Y' ⊆ Y, IsRigid (H.interSet (univ \ ⋃ y ∈ Y', Λ y)))

/-- The subdrawing $H' = H \cap (\Sigma \setminus \bigcup_{y \in Y} \Lambda_y)$ obtained by clearing
a $\gamma$-envelope $(\Lambda_y : y \in Y)$ around $Y$
(Graph Minors XVI, Section 8, page 64). -/
def clearEnvelopeDrawing (H : Drawing S) (Y : Set S) (Λ : S → Set S) : Drawing S :=
  H.interSet (univ \ ⋃ y ∈ Y, Λ y)

end Section8

end GraphMinor.GM16
