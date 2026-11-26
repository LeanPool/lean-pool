/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import LeanPool.GraphMinor.Surface.PlaneOrientation
public import LeanPool.GraphMinor.GM06.Defs

/-!
# Definitions of Graph Minors IX

This file formalizes the definitions of N. Robertson and P. D. Seymour,
*Graph Minors. IX. Disjoint crossed paths*, J. Combin. Theory Ser. B **49** (1990) 40–77.

## Contents

- **Section 1 (pages 40–42):** Cyclic permutations (`CyclicPerm`), restrictions (`Ω | X`),
  `Ω`-clockwise sequences (`IsClockwiseSeq`), crossing pairs (`Crosses`), intervals `Ω(v₁, v₂)`
  (`interval`), fences (`IsFence`), societies (`Society`), `Ω`-paths (`IsOmegaPath`),
  fences for sets of `Ω`-paths (`IsFenceFor`), transactions (`IsTransaction`), peripheral paths
  (`IsPeripheralIn`), crooked transactions (`IsCrookedTransaction`), neighborhoods (`Neighborhood`),
  rural neighborhoods (`IsRural`), separations of societies (`IsSocietySeparation`), compositions
  (`IsComposition`), and sophistication (`HasSophisticationLE`, `sophistication`).
- **Section 2 (pages 43–46):** Avoiding and catching (`Avoids`, `Catches`), `X → Y` paths
  (`IsFromToPath`), `X' ⇒ Y'` with respect to `X, Y` (`RedirectsTo`), `k`-separations and internal
  `k`-separations (`IsKSeparation`, `IsInternalKSeparation`, `IsKConnected`,
  `IsInternallyKConnected`), crosses and tripods (`IsCross`, `IsTripod`), and rural societies
  (`IsRuralSociety`).
- **Section 3 (pages 46–48):** Attachments `P` to `P_set` (`IsAttachment`), feet and legs (`IsFoot`,
  `IsLeg`), switches (`IsSwitch`), exchangeable attachments (`IsExchangeableAttachment`),
  overpasses (`IsOverpass`), and overpass attachments (`IsOverpassAttachment`).
- **Section 4 (pages 49–52):** Non-separating and separating `Ω`-paths (`IsNonSeparatingOmegaPath`,
  `IsSeparatingOmegaPath`), Statement **S** (`StatementS`), `W(Q_set)` (`uncoveredSet`),
  half-covered paths (`IsHalfCovered`), and `Ω`-paths in order (`AreInOrder`).
- **Section 6 (pages 55–58):** `U(P)`, `U(P_set)`, and `C(P_set)` (`peripheralIntervalSet`,
  `transactionPeripheralUnion`, `coveredComponentUnion`).
- **Section 7 (pages 58–60):** Crosscap, leap, and doublecross transactions
  (`IsCrosscapTransaction`, `IsLeapTransaction`, `IsDoublecrossTransaction`).
- **Section 8 (pages 60–62):** Linear decompositions of a society and their depth
  (`HasLinearDecompositionOfDepthLE`).
- **Section 10 (pages 63–67):** Presentations `(Σ, Γ, Δ, Δ₀)` of a rural neighborhood
  (`Presentation`), `s`-nests (`IsNest`), breadth `≥ s` (`HasBreadthGe`), and weakly-linked and
  linked subsets of `ΩBar` (`IsWeaklyLinked`, `IsLinked`).
- **Section 11 (pages 67–77):** `Δ(P)` (`IsPathDisc`), prominences (`IsProminence`), lawns
  (`IsLawn`), walls and internal/external/wall edges (`wallDisc`, `wall`, `IsInternalEdge`,
  `IsExternalEdge`, `IsWallEdge`), triangles (`IsTriangle`), parks (`IsParkOf`, `IsPark`),
  consolidations and their cores (`IsConsolidation`, `consolidationCore`), patterns of transactions
  (`transactionPattern`), segregations of a society (`IsSocietySegregation`), arrangements in a
  closed disc (`IsDiscArrangement`), and feasible segregations (`IsFeasibleSegregation`).
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Topology Graph GraphMinor.Surface GraphMinor.GM06

universe u v w

/-! ## Section 1: Cyclic permutations, societies, transactions, and rural neighborhoods (pages
40–42) -/

/-- A cyclic permutation `Ω` of a finite set `ΩBar` (`bar`)
(Graph Minors IX, Section 1, page 41: "Let $\Omega$ be a cyclic permutation of the elements of some
finite set; we denote this set
by $\bar{\Omega}$. We denote the image under $\Omega$ of $x \in \bar{\Omega}$ by $\Omega(x)$"). -/
structure CyclicPerm (α : Type u) where
  /-- The underlying finite set `ΩBar`. -/
  bar : Set α
  /-- The permutation map `Ω(x)`. -/
  toFun : α → α
  /-- `ΩBar` is finite. -/
  finite_bar : bar.Finite
  /-- `Ω` is a bijection from `ΩBar` to `ΩBar`. -/
  bijOn : BijOn toFun bar bar
  /-- `Ω` acts transitively as a single cycle on `ΩBar`. -/
  single_orbit : ∀ x ∈ bar, ∀ y ∈ bar, ∃ k : ℕ, (toFun^[k]) x = y

instance {α : Type u} : CoeFun (CyclicPerm α) (fun _ => α → α) :=
  ⟨CyclicPerm.toFun⟩

namespace CyclicPerm

variable {α : Type u} (Ω : CyclicPerm α)

/-- "If $V$ is a set, a cyclic permutation $\Omega$ is said to be *in* $V$ if $\bar{\Omega}
\subseteq V$"
(Graph Minors IX, Section 1, page 41). -/
def InSet (V : Set α) : Prop :=
  Ω.bar ⊆ V

/-- `y` is the first term of the sequence `Ω(x), Ω(Ω(x)), …` which belongs to `X`
(Graph Minors IX, Section 1, page 41). -/
def FirstHitIn (X : Set α) (x y : α) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ (Ω.toFun^[k]) x = y ∧ y ∈ X ∧ ∀ j : ℕ, 1 ≤ j → j < k → (Ω.toFun^[j]) x ∉ X

/-- `Ω'` is the restriction `Ω | X` of `Ω` to `X ⊆ ΩBar` (Graph Minors IX, Section 1, page 41:
"If $X \subseteq \bar{\Omega}$, $\Omega$ induces a cyclic permutation $\Omega'$ of $X$ in the
natural way—that is, for $x \in X$ we define $\Omega'(x)$ to be the first term of the
sequence $\Omega(x)$, $\Omega(\Omega(x))$, ... which is in $X$. We define $\Omega \mid X =
\Omega'$"). -/
def IsRestriction (X : Set α) (Ω' : CyclicPerm α) : Prop :=
  Ω'.bar = Ω.bar ∩ X ∧ ∀ x ∈ Ω'.bar, Ω.FirstHitIn Ω'.bar x (Ω' x)

/-- "Let $v_1, ..., v_k \in \bar{\Omega}$ be distinct. We say that $(v_1, v_2, ..., v_k)$ is
$\Omega$-*clockwise* (or more briefly, *clockwise*, when the dependence on $\Omega$ is to be
understood) if $\Omega'(v_1) = v_2$, $\Omega'(v_2) = v_3$, ..., $\Omega'(v_k) = v_1$ where
$\Omega' = \Omega \mid X$" with `X = {v₁, …, v_k}`
(Graph Minors IX, Section 1, page 41). -/
def IsClockwiseSeq (L : List α) : Prop :=
  L.Nodup ∧ (∀ v ∈ L, v ∈ Ω.bar) ∧
    ∀ (i : ℕ) (hi : i < L.length),
      Ω.FirstHitIn {v | v ∈ L} (L[i]) (L[(i + 1) % L.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)))

/-- `(v₁, v₂, v₃)` is `Ω`-clockwise (Graph Minors IX, Section 1, page 41). -/
def IsClockwise3 (v₁ v₂ v₃ : α) : Prop :=
  Ω.IsClockwiseSeq [v₁, v₂, v₃]

/-- `(v₁, v₂, v₃, v₄)` is `Ω`-clockwise (Graph Minors IX, Section 1, page 41). -/
def IsClockwise4 (v₁ v₂ v₃ v₄ : α) : Prop :=
  Ω.IsClockwiseSeq [v₁, v₂, v₃, v₄]

/-- "If $v_1, v_2, v_3, v_4 \in \bar{\Omega}$ are distinct and one of $(v_1, v_2, v_3, v_4)$,
$(v_4, v_3, v_2, v_1)$ is clockwise, we say that $\{v_1, v_3\}$ *crosses* $\{v_2, v_4"
(Graph Minors IX, Section 1, page 41). -/
def Crosses (v₁ v₃ v₂ v₄ : α) : Prop :=
  Ω.IsClockwiseSeq [v₁, v₂, v₃, v₄] ∨ Ω.IsClockwiseSeq [v₄, v₃, v₂, v₁]

/-- `{v₁, v₃}` crosses `{v₂, v₄}` as 2-element sets (Graph Minors IX, Section 1, page 41). -/
def CrossesSet (A B : Set α) : Prop :=
  ∃ v₁ v₃ v₂ v₄ : α, A = {v₁, v₃} ∧ B = {v₂, v₄} ∧ Ω.Crosses v₁ v₃ v₂ v₄

/-- "If $v_1, v_2 \in \bar{\Omega}$ are distinct, we define $$\Omega(v_1, v_2) = \{v \in
\bar{\Omega} - \{v_1, v_2\} : (v_1, v, v_2) \text{ is clockwise}"
(Graph Minors IX, Section 1, page 41). -/
def interval (v₁ v₂ : α) : Set α :=
  {v ∈ Ω.bar \ {v₁, v₂} | Ω.IsClockwise3 v₁ v v₂}

/-- "A fence of $\Omega$ is a pair $(A, B)$ of subsets of $\bar{\Omega}$ such that $A \cap B =
\emptyset$, $A \cup B = \bar{\Omega}$, and for distinct $a_1, a_2 \in A$ and distinct $b_1,
b_2 \in B$, $\{a_1, a_2\}$ does not cross $\{b_1, b_2"
(Graph Minors IX, Section 1, page 41). -/
def IsFence (A B : Set α) : Prop :=
  A ⊆ Ω.bar ∧ B ⊆ Ω.bar ∧ Disjoint A B ∧ A ∪ B = Ω.bar ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ → ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → ¬ Ω.Crosses a₁ a₂ b₁ b₂

/-- The inverse map of `Ω` on `ΩBar` (and the identity outside `ΩBar`). -/
noncomputable def invFunBar (Ω : CyclicPerm α) (x : α) : α := by
  classical
  exact if h : ∃ y ∈ Ω.bar, Ω.toFun y = x then Classical.choose h else x

theorem invFunBar_mem {Ω : CyclicPerm α} {x : α} (hx : x ∈ Ω.bar) :
    Ω.invFunBar x ∈ Ω.bar := by
  classical
  have h : ∃ y ∈ Ω.bar, Ω.toFun y = x := Ω.bijOn.surjOn hx
  simp only [invFunBar, h, ↓reduceDIte]
  exact (Classical.choose_spec h).1

theorem toFun_invFunBar {Ω : CyclicPerm α} {x : α} (hx : x ∈ Ω.bar) :
    Ω.toFun (Ω.invFunBar x) = x := by
  classical
  have h : ∃ y ∈ Ω.bar, Ω.toFun y = x := Ω.bijOn.surjOn hx
  simp only [invFunBar, h, ↓reduceDIte]
  exact (Classical.choose_spec h).2

theorem invFunBar_toFun {Ω : CyclicPerm α} {z : α} (hz : z ∈ Ω.bar) :
    Ω.invFunBar (Ω.toFun z) = z := by
  classical
  have h : ∃ y ∈ Ω.bar, Ω.toFun y = Ω.toFun z := ⟨z, hz, rfl⟩
  have hspec := Classical.choose_spec h
  simp only [invFunBar, h, ↓reduceDIte]
  exact Ω.bijOn.injOn hspec.1 hz hspec.2

/-- The reverse (inverse) cyclic permutation `Ω⁻¹` on the same set `ΩBar`
(Graph Minors IX, Section 1, page 41). -/
noncomputable def reverse (Ω : CyclicPerm α) : CyclicPerm α where
  bar := Ω.bar
  toFun := Ω.invFunBar
  finite_bar := Ω.finite_bar
  bijOn :=
    ⟨fun _ hx => Ω.invFunBar_mem hx,
     fun _ hx _ hy h => by rw [← Ω.toFun_invFunBar hx, ← Ω.toFun_invFunBar hy, h],
     fun x hx => ⟨Ω.toFun x, Ω.bijOn.mapsTo hx, Ω.invFunBar_toFun hx⟩⟩
  single_orbit := by
    intro x hx y hy
    obtain ⟨k, hk⟩ := Ω.single_orbit y hy x hx
    refine ⟨k, ?_⟩
    have hmem : ∀ (n : ℕ) {z : α}, z ∈ Ω.bar → (Ω.toFun^[n]) z ∈ Ω.bar := by
      intro n
      induction n with
      | zero => intro z hz; exact hz
      | succ m ihm => intro z hz; rw [Function.iterate_succ_apply']; exact Ω.bijOn.mapsTo (ihm hz)
    have hinv : ∀ (n : ℕ) {z : α}, z ∈ Ω.bar →
        (Ω.invFunBar^[n]) ((Ω.toFun^[n]) z) = z := by
      intro n
      induction n with
      | zero => intro z _; rfl
      | succ n ih =>
        intro z hz
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply',
          Ω.invFunBar_toFun (hmem n hz)]
        exact ih hz
    rw [← hk]
    exact hinv k hy

noncomputable instance : Inv (CyclicPerm α) := ⟨CyclicPerm.reverse⟩

end CyclicPerm

/-! ### Graph operations, subgraphs, paths, and separations (Section 1, pages 41–42) -/

/-- `P` is a path in `G` with ends `a` and `b`: `P ≤ G` and the vertices and edges of `P` are those
of a simple walk of `G` between `a` and `b` (Graph Minors IX, Section 1, page 41). -/
def IsGraphPathWithEnds {α : Type u} {β : Type v} (G P : Graph α β) (a b : α) : Prop :=
  P ≤ G ∧ ∃ W : GraphWalk P a b, W.IsSimple ∧
    V(P) = {x | x ∈ W.support} ∧ E(P) = {e | e ∈ W.edges}

/-- `P` is a path in `G` (Graph Minors IX, Section 1, page 41). -/
def IsGraphPath {α : Type u} {β : Type v} (G P : Graph α β) : Prop :=
  ∃ a b : α, IsGraphPathWithEnds G P a b

/-- `C` is a circuit in `G`: `C ≤ G` and the vertices and edges of `C` are those of a simple closed
walk of positive length in `G` (Graph Minors IX, Section 1, page 41). -/
def IsGraphCircuit {α : Type u} {β : Type v} (G C : Graph α β) : Prop :=
  C ≤ G ∧ ∃ (u : α) (W : GraphWalk C u u), W.IsSimpleClosed ∧ 0 < W.length ∧
    V(C) = {x | x ∈ W.support} ∧ E(C) = {e | e ∈ W.edges}

/-- The set of ends of a path `P` in `G` (Graph Minors IX, Section 1, page 41). -/
def pathEnds {α : Type u} {β : Type v} (G P : Graph α β) : Set α :=
  {v : α | ∃ b : α, IsGraphPathWithEnds G P v b}

/-- The internal vertices of a path `P` in `G` (Graph Minors IX, Section 1, page 41). -/
def pathInternalVerts {α : Type u} {β : Type v} (G P : Graph α β) : Set α :=
  V(P) \ pathEnds G P

/-- The union `G₁ ∪ G₂` of two subgraphs of a graph `G`, with vertex set `V(G₁) ∪ V(G₂)` and edge
set `E(G₁) ∪ E(G₂)` (Graph Minors IX, Section 1, page 41). -/
def subgraphUnion {α : Type u} {β : Type v} (G G₁ G₂ : Graph α β) : Graph α β :=
  (G.induce (V(G₁) ∪ V(G₂))).restrict (E(G₁) ∪ E(G₂))

/-- The intersection `G₁ ∩ G₂` of two subgraphs of a graph `G`, with vertex set `V(G₁) ∩ V(G₂)` and
edge set `E(G₁) ∩ E(G₂)` (Graph Minors IX, Section 1, page 41). -/
def subgraphInter {α : Type u} {β : Type v} (G G₁ G₂ : Graph α β) : Graph α β :=
  (G.induce (V(G₁) ∩ V(G₂))).restrict (E(G₁) ∩ E(G₂))

/-- The union `⋃ P_set` of a family `P_set` of subgraphs of `G`
(Graph Minors IX, Section 1, page 41). -/
def subgraphSUnion {α : Type u} {β : Type v} (G : Graph α β) (P_set : Set (Graph α β)) :
    Graph α β :=
  (G.induce (⋃ P ∈ P_set, V(P))).restrict (⋃ P ∈ P_set, E(P))

/-- `G \ X`, the subgraph obtained from `G` by deleting a set `X` of vertices and all incident
edges (Graph Minors IX, Section 2, page 43). -/
def deleteVertices {α : Type u} {β : Type v} (G : Graph α β) (X : Set α) : Graph α β :=
  G.induce (V(G) \ X)

/-- The point in `S` representing a vertex `v` in a graph drawing `Γ : GraphDrawing G S` (as a
singleton set `{x}` when `v ∈ V(G)` and `∅` otherwise). -/
def graphDrawingVertexSet {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) (v : α) : Set S :=
  {x : S | ∃ hv : v ∈ V(G), (Γ.iso.vertexEquiv ⟨v, hv⟩).1 = x}

/-- The edge arc in `S` representing an edge `e` in a graph drawing `Γ : GraphDrawing G S`. -/
def graphDrawingEdgeSet {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) (e : β) : Set S :=
  ⋃ (he : e ∈ E(G)), (Γ.iso.edgeEquiv ⟨e, he⟩).1

/-- The underlying point set `U(Γ(P))` of a subgraph `P ≤ G` in a graph drawing `Γ`. -/
def graphDrawingSubgraphU {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) (P : Graph α β) : Set S :=
  (⋃ v ∈ V(P), graphDrawingVertexSet Γ v) ∪ (⋃ e ∈ E(P), closure (graphDrawingEdgeSet Γ e))

/-- "A society is a pair $(G, \Omega)$ where $G$ is a graph and $\Omega$ is a cyclic permutation
in $V(G)$"
(Graph Minors IX, Section 1, page 41). Graphs in the paper are finite. -/
structure Society (α : Type u) (β : Type v) where
  /-- The underlying graph `G`. -/
  G : Graph α β
  /-- The cyclic permutation `Ω` in `V(G)`. -/
  Ω : CyclicPerm α
  /-- `V(G)` is finite. -/
  finite_V : V(G).Finite
  /-- `E(G)` is finite. -/
  finite_E : E(G).Finite
  /-- `ΩBar ⊆ V(G)`. -/
  bar_subset : Ω.bar ⊆ V(G)

namespace Society

variable {α : Type u} {β : Type v} (S : Society α β)

/-- `P` is an `Ω`-path in `(G, Ω)` with ends `a, b` (Graph Minors IX, Section 1, page 41:
"If $(G, \Omega)$ is a society we say that $P$ is an $\Omega$-*path* if $P$ is a path in $G$
with ends distinct and both in $\bar{\Omega}$"). -/
def IsOmegaPathWithEnds (P : Graph α β) (a b : α) : Prop :=
  IsGraphPathWithEnds S.G P a b ∧ a ≠ b ∧ a ∈ S.Ω.bar ∧ b ∈ S.Ω.bar

/-- `P` is an `Ω`-path in `(G, Ω)` (Graph Minors IX, Section 1, page 41). -/
def IsOmegaPath (P : Graph α β) : Prop :=
  ∃ a b : α, S.IsOmegaPathWithEnds P a b

/-- `P_set` is a set of mutually vertex-disjoint `Ω`-paths in `(G, Ω)`
(Graph Minors IX, Section 1, page 41). -/
def IsDisjointOmegaPathSet (P_set : Set (Graph α β)) : Prop :=
  (∀ P ∈ P_set, S.IsOmegaPath P) ∧ P_set.Pairwise (fun P₁ P₂ => Disjoint V(P₁) V(P₂))

/-- "If $\mathcal{P}$ is a set of mutually vertex-disjoint $\Omega$-paths, we say that a fence
$(A, B)$ of $\Omega$ is a *fence for* $\mathcal{P}$ if each $P \in \mathcal{P}$ has one end
in $A$ and the other in $B$"
(Graph Minors IX, Section 1, page 41). -/
def IsFenceFor (P_set : Set (Graph α β)) (A B : Set α) : Prop :=
  S.IsDisjointOmegaPathSet P_set ∧ S.Ω.IsFence A B ∧
    ∀ P ∈ P_set, ∃ a ∈ A, ∃ b ∈ B, S.IsOmegaPathWithEnds P a b

/-- "and if there is a fence for $\mathcal{P}$ we say that $\mathcal{P}$ is a *transaction in*
$(G, \Omega)$"
(Graph Minors IX, Section 1, page 41). -/
def IsTransaction (P_set : Set (Graph α β)) : Prop :=
  ∃ A B : Set α, S.IsFenceFor P_set A B

/-- `V(P_set)`, "the set of all ends of all members of $\mathcal{P}$"
(Graph Minors IX, Section 1, page 41). -/
def transactionEnds (P_set : Set (Graph α β)) : Set α :=
  {v : α | ∃ P ∈ P_set, ∃ b : α, S.IsOmegaPathWithEnds P v b}

/-- `⋃ P_set`, "the subgraph of $G$ which is the union of all members of $\mathcal{P}$"
(Graph Minors IX, Section 1, page 41). -/
def transactionUnion (P_set : Set (Graph α β)) : Graph α β :=
  subgraphSUnion S.G P_set

/-- "Let $P \in \mathcal{P}$ have ends $a, b$. We say that $P$ is *peripheral in* $\mathcal{P}$
if one of $\Omega(a, b) \cap V(\mathcal{P})$, $\Omega(b, a) \cap V(\mathcal{P})$ is empty" (Graph
Minors IX, Section 1, page 41). -/
def IsPeripheralIn (P_set : Set (Graph α β)) (P : Graph α β) : Prop :=
  P ∈ P_set ∧ ∃ a b : α, S.IsOmegaPathWithEnds P a b ∧
    (Disjoint (S.Ω.interval a b) (S.transactionEnds P_set) ∨
      Disjoint (S.Ω.interval b a) (S.transactionEnds P_set))

/-- "A transaction with no peripheral members is said to be *crooked*"
(Graph Minors IX, Section 1, page 41). -/
def IsCrookedTransaction (P_set : Set (Graph α β)) : Prop :=
  S.IsTransaction P_set ∧ ∀ P ∈ P_set, ¬ S.IsPeripheralIn P_set P

/-- "A separation of a society $(G, \Omega)$ is a separation $(G_1, G_2)$ of $G$ such that
$\bar{\Omega} \subseteq V(G_2)$"
(Graph Minors IX, Section 1, page 42). -/
def IsSocietySeparation (G₁ G₂ : Graph α β) : Prop :=
  IsGraphSeparation S.G G₁ G₂ ∧ S.Ω.bar ⊆ V(G₂)

end Society

/-- "We say that $(G, \Omega, \Omega_0)$ is a *neighborhood* if $G$ is a graph and $\Omega,
\Omega_0$ are both cyclic permutations in $V(G)$" (Graph Minors IX, Section 1, page 42). -/
structure Neighborhood (α : Type u) (β : Type v) where
  /-- The underlying graph `G`. -/
  G : Graph α β
  /-- The outer cyclic permutation `Ω` in `V(G)`. -/
  Ω : CyclicPerm α
  /-- The inner cyclic permutation `Ω₀` in `V(G)`. -/
  Ω₀ : CyclicPerm α
  /-- `V(G)` is finite. -/
  finite_V : V(G).Finite
  /-- `E(G)` is finite. -/
  finite_E : E(G).Finite
  /-- `ΩBar ⊆ V(G)`. -/
  bar_subset : Ω.bar ⊆ V(G)
  /-- `ΩBar₀ ⊆ V(G)`. -/
  bar₀_subset : Ω₀.bar ⊆ V(G)

/-- A cyclic permutation `Ω` of a finite subset of an `O`-arc `C` agrees with a homeomorphism
`φ : Circle ≃ₜ C` (orienting `C`) under `ν : α → S` if the cyclic order of `Ω` on `ΩBar` matches the
circular order on `Circle` induced by `φ` (Graph Minors IX, Section 1, page 42). -/
def AgreesWithOArcHomeo {S : Type w} [TopologicalSpace S] {α : Type u}
    (ν : α → S) (Ω : CyclicPerm α) (C : Set S) (φ : Circle ≃ₜ C) : Prop :=
  (∀ v ∈ Ω.bar, ν v ∈ C) ∧
    ∀ v₁ v₂ v₃ : α, Ω.IsClockwise3 v₁ v₂ v₃ →
      ∃ (t₁ t₂ t₃ : ℝ), t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₁ + 2 * Real.pi ∧
        (φ (Circle.exp t₁)).1 = ν v₁ ∧
        (φ (Circle.exp t₂)).1 = ν v₂ ∧
        (φ (Circle.exp t₃)).1 = ν v₃

/-- Clockwise agreement for a `GraphDrawing Γ` on an `O`-arc `C` via `φ : Circle ≃ₜ C`. -/
def DrawingAgreesWithOArcHomeo {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
    {G : Graph α β} (Γ : GraphDrawing G S) (Ω : CyclicPerm α) (C : Set S)
    (φ : Circle ≃ₜ C) : Prop :=
  (∀ v ∈ Ω.bar, graphDrawingVertexSet Γ v ⊆ C) ∧
    ∀ v₁ v₂ v₃ : α, Ω.IsClockwise3 v₁ v₂ v₃ →
      ∃ (t₁ t₂ t₃ : ℝ), t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₁ + 2 * Real.pi ∧
        (φ (Circle.exp t₁)).1 ∈ graphDrawingVertexSet Γ v₁ ∧
        (φ (Circle.exp t₂)).1 ∈ graphDrawingVertexSet Γ v₂ ∧
        (φ (Circle.exp t₃)).1 ∈ graphDrawingVertexSet Γ v₃

/-- "Let $\Sigma$ be a plane, with some orientation called “clockwise.” We say that a
neighborhood $(G, \Omega, \Omega_0)$ is *rural* if $G$ has a drawing $\Gamma$ in $\Sigma$
without crossings (so $G$ is planar) and there are closed discs $\Delta_0 \subseteq \Delta
\subseteq \Sigma$, such that (i) the drawing $\Gamma$ uses no point of $\Sigma$ outside
$\Delta$, and none in the interior of $\Delta_0$, and (ii) for $v \in V(G)$, the point of
$\Sigma$ representing $v$ in the drawing $\Gamma$ lies in $bd(\Delta)$ (respectively,
$bd(\Delta_0)$) if and only if $v \in \bar{\Omega}$ (respectively, $v \in \bar{\Omega}_0$),
and the cyclic permutation of $\bar{\Omega}$ (respectively, $\bar{\Omega}_0$) obtained from
the clockwise orientation of $bd(\Delta)$ (respectively, $bd(\Delta_0)$) coincides (in the
natural sense) with $\Omega$ (respectively, $\Omega_0$)."
(Graph Minors IX, Section 1, page 42). -/
def Neighborhood.IsRural {α : Type u} {β : Type v} (N : Neighborhood α β) : Prop :=
  ∃ (Γ : GraphDrawing N.G EuclideanPlane) (Δ Δ₀ : Set EuclideanPlane),
    IsClosedDisc Δ ∧ Δ₀ ⊆ Δ ∧ Γ.drawing.U ⊆ Δ \ interior Δ₀ ∧
    (∀ v ∈ V(N.G), (graphDrawingVertexSet Γ v ⊆ subBd Δ ↔ v ∈ N.Ω.bar)) ∧
    (∀ v ∈ V(N.G), (graphDrawingVertexSet Γ v ⊆ subBd Δ₀ ↔ v ∈ N.Ω₀.bar)) ∧
    (∃ φ : Circle ≃ₜ subBd Δ,
      IsClockwiseDiscHomeo Δ φ ∧ DrawingAgreesWithOArcHomeo Γ N.Ω (subBd Δ) φ) ∧
    ((Δ₀ = ∅ ∧ N.Ω₀.bar = ∅) ∨
      (IsClosedDisc Δ₀ ∧
        ∃ φ₀ : Circle ≃ₜ subBd Δ₀,
          IsClockwiseDiscHomeo Δ₀ φ₀ ∧ DrawingAgreesWithOArcHomeo Γ N.Ω₀ (subBd Δ₀) φ₀))

/-- "Let $(G_1, G_2)$ be a separation of $(G, \Omega)$, and let $\Omega_1$ be a cyclic
permutation with $\bar{\Omega}_1 = V(G_1 \cap G_2)$. Then we say that $(G, \Omega)$ is the
*composition* of the society $(G_1, \Omega_1)$ with the neighborhood $(G_2, \Omega,
\Omega_1)$" (Graph Minors IX, Section 1, page 42). -/
def Society.IsComposition {α : Type u} {β : Type v} (S S₁ : Society α β) (N : Neighborhood α β) :
    Prop :=
  S.IsSocietySeparation S₁.G N.G ∧
    N.Ω = S.Ω ∧ N.Ω₀ = S₁.Ω ∧ S₁.Ω.bar = V(S₁.G) ∩ V(N.G)

/-- A society `(G, Ω)` has sophistication `≤ p` if it is the composition of a society `(G₁, Ω₁)`
which has no transaction of cardinality `> p` with a rural neighborhood `(G₂, Ω, Ω₁)`
(Graph Minors IX, Section 1, page 42). -/
def Society.HasSophisticationLE {α : Type u} {β : Type v} (S : Society α β) (p : ℕ) : Prop :=
  ∃ (S₁ : Society α β) (N : Neighborhood α β),
    S.IsComposition S₁ N ∧ N.IsRural ∧
    ∀ P_set : Set (Graph α β), S₁.IsTransaction P_set → P_set.ncard ≤ p

/-- "The *sophistication* of $(G, \Omega)$ is the minimum $p \ge 0$ such that $(G, \Omega)$ is
the composition of a society which has no transaction of cardinality $> p$ with a rural
neighborhood"
(Graph Minors IX, Section 1, page 42). -/
noncomputable def Society.sophistication {α : Type u} {β : Type v} (S : Society α β) : ℕ :=
  sInf {p : ℕ | S.HasSophisticationLE p}

/-! ## Section 2: Two Crossing Paths (pages 43–46) -/

/-- "If $P$ is a path in a graph $G$ and $Z \subseteq V(G)$ with $Z \cap V(P) = \emptyset$, we
say that $P$ *avoids* $Z$" (Graph Minors IX, Section 2, page 43). -/
def Avoids {α : Type u} {β : Type v} (P : Graph α β) (Z : Set α) : Prop :=
  Disjoint Z V(P)

/-- "We say that $Z$ *catches* $G$ if $Z \subseteq V(G)$ and $Z \cap V(G') \ne \emptyset$ for
every component $G'$ of $G$" (Graph Minors IX, Section 2, page 43). -/
def Catches {α : Type u} {β : Type v} (Z : Set α) (G : Graph α β) : Prop :=
  Z ⊆ V(G) ∧ ∀ G' ∈ graphComponents G, (Z ∩ V(G')).Nonempty

/-- "Let $G$ be a graph and let $X, Y \subseteq V(G)$. By an $X \to Y$ path in $G$ we mean a path
with initial vertex and no other in $X$, and with terminal vertex and no other in $Y$"
(Graph Minors IX, Section 2, page 44). -/
def IsFromToPathWithEnds {α : Type u} {β : Type v} (G P : Graph α β) (X Y : Set α)
    (x y : α) : Prop :=
  IsGraphPathWithEnds G P x y ∧ V(P) ∩ X = {x} ∧ V(P) ∩ Y = {y}

/-- `P` is an `X → Y` path in `G` (Graph Minors IX, Section 2, page 44). -/
def IsFromToPath {α : Type u} {β : Type v} (G P : Graph α β) (X Y : Set α) : Prop :=
  ∃ x y : α, IsFromToPathWithEnds G P X Y x y

/-- "Let $X' \subseteq X$ and $Y' \subseteq Y$ be such that $|X'| = |Y'|$. We write $X'
\Rightarrow Y'$ (with respect to $X, Y$) if there are $|X'|$ mutually disjoint $X \to Y$
paths of $G$ from $X'$ to $Y'$"
(Graph Minors IX, Section 2, page 44). -/
def RedirectsTo {α : Type u} {β : Type v} (G : Graph α β) (X Y X' Y' : Set α) : Prop :=
  X' ⊆ X ∧ Y' ⊆ Y ∧ X'.ncard = Y'.ncard ∧
    ∃ P : Fin X'.ncard → Graph α β,
      Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
      ∀ i : Fin X'.ncard, ∃ x ∈ X', ∃ y ∈ Y', IsFromToPathWithEnds G (P i) X Y x y

/-- "Let $(G, \Omega)$ be a society, and let $(G_1, G_2)$ be a separation of $(G, \Omega)$. Let
$k \ge 0$ be an integer. We say that $(G_1, G_2)$ is a *$k$-separation* of $(G, \Omega)$ if
$|V(G_1 \cap G_2)| \le k$, and $V(G_2) \ne V(G)$" (Graph Minors IX, Section 2, page 44). -/
def Society.IsKSeparation {α : Type u} {β : Type v} (S : Society α β) (k : ℕ)
    (G₁ G₂ : Graph α β) : Prop :=
  S.IsSocietySeparation G₁ G₂ ∧ (V(G₁) ∩ V(G₂)).ncard ≤ k ∧ V(G₂) ≠ V(S.G)

/-- "A $k$-separation is *internal* if $|V(G)| \ge |V(G_2)| + 2$"
(Graph Minors IX, Section 2, page 44). -/
def Society.IsInternalKSeparation {α : Type u} {β : Type v} (S : Society α β) (k : ℕ)
    (G₁ G₂ : Graph α β) : Prop :=
  S.IsKSeparation k G₁ G₂ ∧ V(G₂).ncard + 2 ≤ V(S.G).ncard

/-- "We say that $(G, \Omega)$ is *$k$-connected* if it has no $k'$-separation for $k' < k$, and
*internally $k$-connected* if it has no internal $k'$-separation for $k' < k$"
(Graph Minors IX, Section 2, page 44). -/
def Society.IsKConnected {α : Type u} {β : Type v} (S : Society α β) (k : ℕ) : Prop :=
  ∀ k' < k, ∀ G₁ G₂ : Graph α β, ¬ S.IsKSeparation k' G₁ G₂

/-- `(G, Ω)` is internally `k`-connected (Graph Minors IX, Section 2, page 44). -/
def Society.IsInternallyKConnected {α : Type u} {β : Type v} (S : Society α β) (k : ℕ) : Prop :=
  ∀ k' < k, ∀ G₁ G₂ : Graph α β, ¬ S.IsInternalKSeparation k' G₁ G₂

/-- "Let $P_1, P_2$ be disjoint $\Omega$-paths in $(G, \Omega)$, where $P_i$ has ends $s_i, t_i$
($i = 1, 2$). If $\{s_1, t_1\}$ crosses $\{s_2, t_2\}$, we say that $P_1$ *crosses* $P_2$,
and that $\{P_1, P_2\}$ is a *cross" (Graph Minors IX, Section 2, page 44). -/
def Society.OmegaPathsCross {α : Type u} {β : Type v} (S : Society α β)
    (P₁ P₂ : Graph α β) : Prop :=
  Disjoint V(P₁) V(P₂) ∧
    ∃ s₁ t₁ s₂ t₂ : α,
      S.IsOmegaPathWithEnds P₁ s₁ t₁ ∧
      S.IsOmegaPathWithEnds P₂ s₂ t₂ ∧
      S.Ω.Crosses s₁ t₁ s₂ t₂

/-- `{P₁, P₂}` is a cross in `(G, Ω)` (Graph Minors IX, Section 2, page 44). -/
def Society.IsCross {α : Type u} {β : Type v} (S : Society α β) (P₁ P₂ : Graph α β) : Prop :=
  S.OmegaPathsCross P₁ P₂

/-- "Now let $u, v$ be distinct vertices of $G$, and let $P_1, P_2, P_3$ all be paths between $u$
and $v$, mutually disjoint except for $u$ and $v$. We say that $\{P_1, P_2, P_3\}$ is a
*tripod* in $(G, \Omega)$ if there is an internal vertex $s_i$ of $P_i$ ($i = 1, 2, 3$), and
there exist $t_1, t_2, t_3 \in \bar{\Omega}$ such that $\{s_1, s_2, s_3\} \Rightarrow \{t_1,
t_2, t_3\}$ with respect to $V(P_1 \cup P_2 \cup P_3), \bar{\Omega}$"
(Graph Minors IX, Section 2, page 44). -/
def Society.IsTripod {α : Type u} {β : Type v} (S : Society α β) (P₁ P₂ P₃ : Graph α β) : Prop :=
  ∃ u v : α, u ≠ v ∧
    IsGraphPathWithEnds S.G P₁ u v ∧
    IsGraphPathWithEnds S.G P₂ u v ∧
    IsGraphPathWithEnds S.G P₃ u v ∧
    V(P₁) ∩ V(P₂) = {u, v} ∧
    V(P₁) ∩ V(P₃) = {u, v} ∧
    V(P₂) ∩ V(P₃) = {u, v} ∧
    ∃ s₁ ∈ V(P₁) \ {u, v}, ∃ s₂ ∈ V(P₂) \ {u, v}, ∃ s₃ ∈ V(P₃) \ {u, v},
    ∃ t₁ ∈ S.Ω.bar, ∃ t₂ ∈ S.Ω.bar, ∃ t₃ ∈ S.Ω.bar,
      RedirectsTo S.G (V(P₁) ∪ V(P₂) ∪ V(P₃)) S.Ω.bar {s₁, s₂, s₃} {t₁, t₂, t₃}

/-- "A society $(G, \Omega)$ is rural if $(G, \Omega, \Omega_0)$ is rural where $\bar{\Omega}_0 =
\emptyset$"
(Graph Minors IX, Section 2, page 45). -/
def Society.IsRuralSociety {α : Type u} {β : Type v} (S : Society α β) : Prop :=
  ∃ (Ω₀ : CyclicPerm α) (h₀ : Ω₀.bar ⊆ V(S.G)),
    Ω₀.bar = ∅ ∧ (Neighborhood.mk S.G S.Ω Ω₀ S.finite_V S.finite_E S.bar_subset h₀).IsRural

/-! ## Section 3: Attachments (pages 46–48) -/

namespace Society

variable {α : Type u} {β : Type v} (S : Society α β)

/-- "Let $\mathscr{P}$ be a transaction in $(G, \Omega)$, and let $P$ be a $V(\bigcup
\mathscr{P}) \to (\bar{\Omega} - V(\mathscr{P}))$ path in $G$. We call $P$ an *attachment*
to $\mathscr{P}$. The common vertex of $\bigcup \mathscr{P}$ and $P$ is called the *foot* of
the attachment, while the member $P_1$ of $\mathscr{P}$ of which the foot is a vertex is
called the *leg" (Graph Minors IX, Section 3, page 46). -/
def IsAttachmentWithEnds (P_set : Set (Graph α β)) (P : Graph α β) (b u : α) : Prop :=
  IsFromToPathWithEnds S.G P V(S.transactionUnion P_set) (S.Ω.bar \ S.transactionEnds P_set) b u

/-- `P` is an attachment to `P_set` (Graph Minors IX, Section 3, page 46). -/
def IsAttachment (P_set : Set (Graph α β)) (P : Graph α β) : Prop :=
  ∃ b u : α, S.IsAttachmentWithEnds P_set P b u

/-- `b` is the foot of an attachment `P` to `P_set` (Graph Minors IX, Section 3, page 46). -/
def IsFoot (P_set : Set (Graph α β)) (P : Graph α β) (b : α) : Prop :=
  ∃ u : α, S.IsAttachmentWithEnds P_set P b u

/-- `L` is the leg of an attachment `P` to `P_set` (Graph Minors IX, Section 3, page 46). -/
def IsLeg (P_set : Set (Graph α β)) (P L : Graph α β) : Prop :=
  L ∈ P_set ∧ ∃ b : α, S.IsFoot P_set P b ∧ b ∈ V(L)

/-- "The union of $P$ with a subpath of $P_1$ from the foot to an end of $P_1$ is called a *switch"
(Graph Minors IX, Section 3, page 46). -/
def IsSwitch (P_set : Set (Graph α β)) (P L L' : Graph α β) : Prop :=
  L ∈ P_set ∧
    ∃ b u a₁ b₁ : α,
      S.IsAttachmentWithEnds P_set P b u ∧
      b ∈ V(L) ∧
      S.IsOmegaPathWithEnds L a₁ b₁ ∧
      ∃ Q : Graph α β,
        (IsGraphPathWithEnds L Q b a₁ ∨ IsGraphPathWithEnds L Q b b₁) ∧
        L' = subgraphUnion S.G P Q

/-- "If $\mathscr{P}$ is crooked, the attachment $P$ is *exchangeable* if there is a switch $S$
such that $(\mathscr{P} - \{P_1\}) \cup \{S\}$ is a crooked transaction" (Graph Minors IX, Section
3, page 46). -/
def IsExchangeableAttachment (P_set : Set (Graph α β)) (P : Graph α β) : Prop :=
  S.IsAttachment P_set P ∧
    ∃ L L' : Graph α β, S.IsSwitch P_set P L L' ∧
      S.IsCrookedTransaction ((P_set \ {L}) ∪ {L'})

/-- "Let $\mathscr{P}$ be a crooked transaction and let $P \in \mathscr{P}$. If $\mathscr{P} -
\{P\}$ has two peripheral members we say that $P$ is an *overpass* of $\mathscr{P}$" (Graph Minors
IX, Section 3, page 46). -/
def IsOverpass (P_set : Set (Graph α β)) (P : Graph α β) : Prop :=
  S.IsCrookedTransaction P_set ∧ P ∈ P_set ∧
    ∃ P₁ ∈ P_set \ {P}, ∃ P₂ ∈ P_set \ {P},
      P₁ ≠ P₂ ∧ S.IsPeripheralIn (P_set \ {P}) P₁ ∧ S.IsPeripheralIn (P_set \ {P}) P₂

/-- "If $P$ is an attachment to $\mathscr{P}$ with leg an overpass of $\mathscr{P}$, we call it
an *overpass attachment" (Graph Minors IX, Section 3, page 47). -/
def IsOverpassAttachment (P_set : Set (Graph α β)) (P : Graph α β) : Prop :=
  S.IsAttachment P_set P ∧
    ∃ L : Graph α β, S.IsLeg P_set P L ∧ S.IsOverpass P_set L

/-! ## Section 4: Separating `Ω`-Paths (pages 49–52) -/

/-- "Let $(G, \Omega)$ be a society. An $\Omega$-path $P$ is *non-separating* if there is an
$\Omega$-path $P'$ such that $P'$ crosses $P$, and *separating* otherwise" (Graph Minors IX, Section
4, page 49). -/
def IsNonSeparatingOmegaPath (P : Graph α β) : Prop :=
  S.IsOmegaPath P ∧ ∃ P' : Graph α β, S.OmegaPathsCross P' P

/-- `P` is a separating `Ω`-path in `(G, Ω)` (Graph Minors IX, Section 4, page 49). -/
def IsSeparatingOmegaPath (P : Graph α β) : Prop :=
  S.IsOmegaPath P ∧ ¬ ∃ P' : Graph α β, S.OmegaPathsCross P' P

/-- Statement **S** of Graph Minors IX, Section 4 (page 49):
"{Q}$ is a transaction in a society $(G, \Omega)$, such that no member of $\mathscr{Q}$ has
an internal vertex in $\bar{\Omega}$. A crooked transaction $\mathscr{P}$ in $(G, \Omega)$
is chosen with $|\mathscr{P}| \ge p$ (where $p \ge 2$ is some given integer), such that* (i)
*$\bigcup \mathscr{P} \cup \bigcup \mathscr{Q}$ is minimal* (ii) *subject to (i),
$|\mathscr{P}|$ is minimum,* *and $(A, B)$ is a fence for $\mathscr{P}$." -/
structure StatementS (p : ℕ) (P_set Q_set : Set (Graph α β)) (A B : Set α) : Prop where
  /-- `p ≥ 2`. -/
  two_le_p : 2 ≤ p
  /-- `Q_set` is a transaction in `(G, Ω)`. -/
  isTransaction_Q : S.IsTransaction Q_set
  /-- No member of `Q_set` has an internal vertex in `ΩBar`. -/
  no_internal_in_bar : ∀ Q ∈ Q_set, Disjoint (pathInternalVerts S.G Q) S.Ω.bar
  /-- `P_set` is a crooked transaction in `(G, Ω)`. -/
  isCrooked_P : S.IsCrookedTransaction P_set
  /-- `|P_set| ≥ p`. -/
  card_P_ge : p ≤ P_set.ncard
  /-- (i) `⋃ P_set ∪ ⋃ Q_set` is minimal. -/
  minimal_union : ∀ P_set' : Set (Graph α β),
    S.IsCrookedTransaction P_set' → p ≤ P_set'.ncard →
    subgraphUnion S.G (S.transactionUnion P_set') (S.transactionUnion Q_set) ≤
      subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set) →
    subgraphUnion S.G (S.transactionUnion P_set') (S.transactionUnion Q_set) =
      subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set)
  /-- (ii) Subject to (i), `|P_set|` is minimum. -/
  minimal_card : ∀ P_set' : Set (Graph α β),
    S.IsCrookedTransaction P_set' → p ≤ P_set'.ncard →
    subgraphUnion S.G (S.transactionUnion P_set') (S.transactionUnion Q_set) =
      subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set) →
    P_set.ncard ≤ P_set'.ncard
  /-- `(A, B)` is a fence for `P_set`. -/
  isFenceFor_P : S.IsFenceFor P_set A B

/-- `W(Q_set)`, the set of vertices `v ∈ V(Q_set)` such that `v ∉ V(P_set)` and `Q ∩ ⋃ P_set` is
non-null, where `Q` is the member of `Q_set` with end `v` (Graph Minors IX, Section 4,
pages 49–50). -/
def uncoveredSet (P_set Q_set : Set (Graph α β)) : Set α :=
  {v ∈ S.transactionEnds Q_set | v ∉ S.transactionEnds P_set ∧
    ∃ Q ∈ Q_set, v ∈ pathEnds S.G Q ∧ (V(Q) ∩ V(S.transactionUnion P_set)).Nonempty}

/-- "If $v \in W(\mathscr{Q})$, we define the *attachment corresponding to $v$* to be the minimal
subpath of $\bigcup \mathscr{Q}$ between $v$ and $\bigcup \mathscr{P}$" (Graph Minors IX, Section 4,
page 50). -/
def IsCorrespondingAttachment (P_set Q_set : Set (Graph α β)) (v : α) (P : Graph α β) : Prop :=
  v ∈ S.uncoveredSet P_set Q_set ∧
    ∃ Q ∈ Q_set, v ∈ pathEnds S.G Q ∧ P ≤ Q ∧
      ∃ b : α, S.IsAttachmentWithEnds P_set P b v

/-- "If $Q$ satisfies (4.3) (iii) we say that $Q$ is *half-covered" (Graph Minors IX, Section 4,
page 50), where (4.3) (iii) states: "$Q$ meets exactly one member $P$ of $\mathscr{P}$, $P \cap Q$
is a path, and $P, Q$ and $P
\cap Q$ have a common end, and the other end of $Q$ is not in $V(\mathscr{P})$." -/
def IsHalfCovered (P_set : Set (Graph α β)) (Q : Graph α β) : Prop :=
  ∃ P ∈ P_set,
    (V(P) ∩ V(Q)).Nonempty ∧
    (∀ P' ∈ P_set, (V(P') ∩ V(Q)).Nonempty → P' = P) ∧
    ∃ s t a b c : α,
      S.IsOmegaPathWithEnds P s t ∧
      S.IsOmegaPathWithEnds Q a b ∧
      s = a ∧ b ∉ S.transactionEnds P_set ∧
      IsGraphPathWithEnds S.G (subgraphInter S.G P Q) s c

/-- "Let $P_1, ..., P_k$ be mutually disjoint $\Omega$-paths. We say that $P_1, ..., P_k$ are *in
order* if there is a clockwise sequence $$ (a_k, a_{k-1}, ..., a_2, a_1, b_1, b_2, ...,
b_{k-1}, b_k), $$ where $P_i$ has ends $a_i, b_i$ ($1 \le i \le k$)" (Graph Minors IX, Section 4,
page 50). -/
def AreInOrder (Q : List (Graph α β)) : Prop :=
  Q.Pairwise (fun P₁ P₂ => Disjoint V(P₁) V(P₂)) ∧
    ∃ (a b : List α) (ha : a.length = Q.length) (hb : b.length = Q.length),
      (∀ (i : ℕ) (hi : i < Q.length),
        S.IsOmegaPathWithEnds (Q[i]) (a[i]'(by omega)) (b[i]'(by omega))) ∧
      S.Ω.IsClockwiseSeq (a.reverse ++ b)

/-! ## Section 6: The Main Theorem (pages 55–58) -/

/-- "Let $\mathcal{P}$ be a transaction in $(G, \Omega)$, with $|\mathcal{P}| \ge 2$. If $P \in
\mathcal{P}$ is peripheral and has ends $s, t$, we define $U(P) = \Omega(t, s)$, where
$\Omega(s, t) \cap V(\mathcal{P}) = \emptyset$."
(Graph Minors IX, Section 6, page 55). -/
def peripheralIntervalSet (P_set : Set (Graph α β)) (P : Graph α β) : Set α :=
  ⋃ (s : α) (t : α)
    (_ : S.IsOmegaPathWithEnds P s t ∧ Disjoint (S.Ω.interval s t) (S.transactionEnds P_set)),
    S.Ω.interval t s

/-- "If $\mathcal{P}$ is crooked, we define $U(\mathcal{P}) = \bar{\Omega}$, and otherwise we
define $U(\mathcal{P})$ to be the intersection of the sets $U(P)$, taken over all peripheral
$P \in \mathcal{P}$"
(Graph Minors IX, Section 6, page 55). -/
def transactionPeripheralUnion (P_set : Set (Graph α β)) : Set α :=
  S.Ω.bar ∩ ⋂ P ∈ {P ∈ P_set | S.IsPeripheralIn P_set P}, S.peripheralIntervalSet P_set P

/-- "We define $C(\mathcal{P})$ to be the set of all vertices $v$ of $G$ such that there is a
path in $G$ between $\{v\}$ and $U(\mathcal{P})$ which avoids every peripheral member of
$\mathcal{P}$"
(Graph Minors IX, Section 6, page 55). -/
def coveredComponentUnion (P_set : Set (Graph α β)) : Set α :=
  {v ∈ V(S.G) | ∃ u ∈ S.transactionPeripheralUnion P_set, ∃ Q : Graph α β,
    IsGraphPathWithEnds S.G Q v u ∧
    ∀ P ∈ P_set, S.IsPeripheralIn P_set P → Avoids Q V(P)}

/-! ## Section 7: Some Special Transactions (pages 58–60) -/

/-- "Let $\mathcal{P}$ be a transaction. If there is a fence $(A, B)$ for $\mathcal{P}$, and an
enumeration $\mathcal{P} = \{P_1, \dots, P_p\}$, where $P_i$ has ends $a_i \in A$, $b_i \in
B$ ($1 \le i \le p$), such that $(a_p, a_{p-1}, \dots, a_1, b_1)$ is clockwise, and (i) $p
\ge 2$ and $(a_p, a_{p-1}, \dots, a_2, a_1, b_p, b_{p-1}, \dots, b_2, b_1)$ is clockwise, we
say $\mathcal{P}$ is a *crosscap" (Graph Minors IX, Section 7, page 59). -/
def IsCrosscapTransaction (P_set : Set (Graph α β)) : Prop :=
  ∃ A B : Set α, S.IsFenceFor P_set A B ∧
    ∃ (p : ℕ) (_ : 2 ≤ p) (P : Fin p → Graph α β) (a b : Fin p → α),
      Function.Injective P ∧ range P = P_set ∧
      (∀ i, a i ∈ A ∧ b i ∈ B ∧ S.IsOmegaPathWithEnds (P i) (a i) (b i)) ∧
      S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ (List.ofFn b).reverse)

/-- "(ii) $p \ge 3$ and $(a_p, a_{p-1}, \dots, a_2, a_1, b_2, b_3, \dots, b_p, b_1)$ is
clockwise, we say $\mathcal{P}$ is a *leap" (Graph Minors IX, Section 7, page 59). -/
def IsLeapTransaction (P_set : Set (Graph α β)) : Prop :=
  ∃ A B : Set α, S.IsFenceFor P_set A B ∧
    ∃ (p : ℕ) (hp : 3 ≤ p) (P : Fin p → Graph α β) (a b : Fin p → α),
      Function.Injective P ∧ range P = P_set ∧
      (∀ i, a i ∈ A ∧ b i ∈ B ∧ S.IsOmegaPathWithEnds (P i) (a i) (b i)) ∧
      S.Ω.IsClockwiseSeq
        ((List.ofFn a).reverse ++
          List.ofFn (fun i : Fin (p - 1) => b ⟨i.1 + 1, by omega⟩) ++
          [b ⟨0, by omega⟩])

/-- "(iii) $p \ge 4$ and $(a_p, a_{p-1}, \dots, a_2, a_1, b_2, b_1, b_3, b_4, \dots, b_{p-3},
b_{p-2}, b_p, b_{p-1})$ is clockwise, we say $\mathcal{P}$ is a *doublecross" (Graph Minors IX,
Section 7, page 59). -/
def IsDoublecrossTransaction (P_set : Set (Graph α β)) : Prop :=
  ∃ A B : Set α, S.IsFenceFor P_set A B ∧
    ∃ (p : ℕ) (hp : 4 ≤ p) (P : Fin p → Graph α β) (a b : Fin p → α),
      Function.Injective P ∧ range P = P_set ∧
      (∀ i, a i ∈ A ∧ b i ∈ B ∧ S.IsOmegaPathWithEnds (P i) (a i) (b i)) ∧
      S.Ω.IsClockwiseSeq
        ((List.ofFn a).reverse ++
          [b ⟨1, by omega⟩, b ⟨0, by omega⟩] ++
          List.ofFn (fun i : Fin (p - 4) => b ⟨i.1 + 2, by omega⟩) ++
          [b ⟨p - 1, by omega⟩, b ⟨p - 2, by omega⟩])

/-! ## Section 8: Societies with No Large Transaction (pages 60–62) -/

/-- "Let $(G, \Omega)$ be a society. A *linear decomposition* of $(G, \Omega)$ is an enumeration
$\{t_1, \dots, t_n\}$ of $\bar{\Omega}$ where $(t_1, \dots, t_n)$ is clockwise, together with a
family $(X_i: 1 \le i \le n)$ of subgraphs of $G$, with the following properties:
(i) $\bigcup(X_i: 1 \le i \le n) = G$
(ii) for $1 \le i < i' \le n$, $E(X_i \cap X_{i'}) = \emptyset$
(iii) for $1 \le i \le n$, $t_i \in V(X_i)$
(iv) for $1 \le i \le i' \le i'' \le n$, $X_i \cap X_{i''} \subseteq X_{i'}$.
The *depth* of such a linear decomposition is
$$\max(|V(X_i \cap X_{i'})|: 1 \le i < i' \le n).$$"
(Graph Minors IX, Section 8, page 60). -/
structure IsLinearDecomposition {n : ℕ} (t : Fin n → α) (X : Fin n → Graph α β) : Prop where
  /-- `t` is injective. -/
  injective_t : Function.Injective t
  /-- `{t₁, …, t_n} = ΩBar`. -/
  range_t : range t = S.Ω.bar
  /-- `(t₁, …, t_n)` is `Ω`-clockwise. -/
  clockwise_t : S.Ω.IsClockwiseSeq (List.ofFn t)
  /-- Each `X_i` is a subgraph of `G`. -/
  le_G : ∀ i : Fin n, X i ≤ S.G
  /-- (i) `⋃ (X_i : 1 ≤ i ≤ n) = G`. -/
  union_eq : subgraphSUnion S.G (range X) = S.G
  /-- (ii) For `1 ≤ i < i' ≤ n`, `E(X_i ∩ X_{i'}) = ∅`. -/
  edge_disjoint : ∀ i i' : Fin n, i < i' → Disjoint E(X i) E(X i')
  /-- (iii) For `1 ≤ i ≤ n`, `t_i ∈ V(X_i)`. -/
  mem_vertexSet : ∀ i : Fin n, t i ∈ V(X i)
  /-- (iv) For `1 ≤ i ≤ i' ≤ i'' ≤ n`, `X_i ∩ X_{i''} ⊆ X_{i'}`. -/
  inter_le : ∀ i i' i'' : Fin n, i ≤ i' → i' ≤ i'' → subgraphInter S.G (X i) (X i'') ≤ X i'

/-- `(G, Ω)` has a linear decomposition of depth `≤ k` (Graph Minors IX, Section 8, page 60). -/
def HasLinearDecompositionOfDepthLE (k : ℕ) : Prop :=
  ∃ (n : ℕ) (t : Fin n → α) (X : Fin n → Graph α β),
    S.IsLinearDecomposition t X ∧
    ∀ i i' : Fin n, i < i' → (V(X i) ∩ V(X i')).ncard ≤ k

end Society

/-! ## Section 10: Exploiting a Rural Neighborhood (pages 63–67) -/

/-- A *presentation* `(Γ, Δ, Δ₀)` of a rural neighborhood `(G, Ω, Ω₀)` in the plane
(Graph Minors IX, Section 10, page 63). -/
structure Presentation {α : Type u} {β : Type v} (N : Neighborhood α β) where
  /-- The drawing `Γ` of `G` in `EuclideanPlane`. -/
  Γ : GraphDrawing N.G EuclideanPlane
  /-- The outer closed disc `Δ ⊆ EuclideanPlane`. -/
  Δ : Set EuclideanPlane
  /-- The inner closed disc `Δ₀ ⊆ Δ` (or `∅` when `ΩBar₀ = ∅`). -/
  Δ₀ : Set EuclideanPlane
  /-- `Δ` is a closed disc. -/
  isClosedDisc_Δ : IsClosedDisc Δ
  /-- `Δ₀ ⊆ Δ`. -/
  Δ₀_subset_Δ : Δ₀ ⊆ Δ
  /-- `U(Γ) ⊆ Δ \ interior Δ₀`. -/
  U_subset : Γ.drawing.U ⊆ Δ \ interior Δ₀
  /-- `v ∈ ΩBar` if and only if `ν(v) ∈ bd(Δ)`. -/
  mem_bd_Δ_iff : ∀ v ∈ V(N.G), (graphDrawingVertexSet Γ v ⊆ subBd Δ ↔ v ∈ N.Ω.bar)
  /-- `v ∈ ΩBar₀` if and only if `ν(v) ∈ bd(Δ₀)`. -/
  mem_bd_Δ₀_iff : ∀ v ∈ V(N.G), (graphDrawingVertexSet Γ v ⊆ subBd Δ₀ ↔ v ∈ N.Ω₀.bar)
  /-- Clockwise orientation agreement on `bd(Δ)`. -/
  agrees_Δ : ∃ φ : Circle ≃ₜ subBd Δ,
    IsClockwiseDiscHomeo Δ φ ∧ DrawingAgreesWithOArcHomeo Γ N.Ω (subBd Δ) φ
  /-- `Δ₀` is either empty (when `ΩBar₀ = ∅`) or a closed disc with clockwise orientation agreement.
  -/
  agrees_Δ₀ : (Δ₀ = ∅ ∧ N.Ω₀.bar = ∅) ∨
    (IsClosedDisc Δ₀ ∧ ∃ φ₀ : Circle ≃ₜ subBd Δ₀,
      IsClockwiseDiscHomeo Δ₀ φ₀ ∧ DrawingAgreesWithOArcHomeo Γ N.Ω₀ (subBd Δ₀) φ₀)

namespace Neighborhood

variable {α : Type u} {β : Type v} (N : Neighborhood α β)

/-- "For a fixed presentation and integer $s \ge 0$, an *$s$-nest* is a sequence $(C_1, \dots,
C_s)$ of circuits of $G$, mutually disjoint, such that $\Delta_0 \subseteq \Delta_1
\subseteq \dots \subseteq \Delta_s \subseteq \Delta$, where $\Delta_i$ denotes the closed
disc in $\Sigma$ bounded by the image under $\Gamma$ of $C_i$ ($1 \le i \le s$)"
(Graph Minors IX, Section 10, page 63). -/
def IsNest (P : Presentation N) {s : ℕ} (C : Fin s → Graph α β) : Prop :=
  (∀ i, IsGraphCircuit N.G (C i)) ∧
  Pairwise (fun i j => Disjoint V(C i) V(C j)) ∧
  ∃ D : Fin s → Set EuclideanPlane,
    (∀ i, IsClosedDisc (D i) ∧ subBd (D i) = graphDrawingSubgraphU P.Γ (C i)) ∧
    (∀ i : Fin s, P.Δ₀ ⊆ D i ∧ D i ⊆ P.Δ) ∧
    (∀ i j : Fin s, i ≤ j → D i ⊆ D j)

/-- "If there is an $s$-nest in some presentation of $(G, \Omega, \Omega_0)$, we say that $(G,
\Omega, \Omega_0)$ has *breadth* $\ge s$" (Graph Minors IX, Section 10, page 63). -/
def HasBreadthGe (s : ℕ) : Prop :=
  ∃ (P : Presentation N) (C : Fin s → Graph α β), N.IsNest P C

/-- "Again, let $(G, \Omega, \Omega_0)$ be a neighborhood. We say that $X \subseteq \bar{\Omega}$
is *weakly-linked* if there are $|X|$ mutually disjoint $X \to \bar{\Omega}_0$ paths of $G$" (Graph
Minors IX, Section 10, page 63). -/
def IsWeaklyLinked (X : Set α) : Prop :=
  X ⊆ N.Ω.bar ∧ ∃ P : Fin X.ncard → Graph α β,
    (∀ i, IsFromToPath N.G (P i) X N.Ω₀.bar) ∧
    Pairwise (fun i j => Disjoint V(P i) V(P j))

/-- "and *linked* if these paths can be chosen such that each has only its initial vertex in
$\bar{\Omega}$"
(Graph Minors IX, Section 10, page 63). -/
def IsLinked (X : Set α) : Prop :=
  X ⊆ N.Ω.bar ∧ ∃ P : Fin X.ncard → Graph α β,
    (∀ i, ∃ x ∈ X, ∃ y ∈ N.Ω₀.bar, IsFromToPathWithEnds N.G (P i) N.Ω.bar N.Ω₀.bar x y) ∧
    Pairwise (fun i j => Disjoint V(P i) V(P j))

end Neighborhood

/-! ## Section 11: Coping with Connectivity Failure (pages 67–77) -/

/-- A graph `G` is simple if it has no loops and no parallel edges
(Graph Minors IX, Section 11, page 67). -/
def IsSimpleGraph {α : Type u} {β : Type v} (G : Graph α β) : Prop :=
  (∀ e ∈ E(G), ∀ v : α, ¬ G.IsLink e v v) ∧
    (∀ e₁ ∈ E(G), ∀ e₂ ∈ E(G), ∀ u v : α, G.IsLink e₁ u v → G.IsLink e₂ u v → e₁ = e₂)

/-- `D = Δ(P)` for a presentation `P_pres = (Σ, Γ, Δ, Δ₀)` of a rural neighborhood `(G, Ω, Ω₀)` and
a path `P` of `G` with distinct ends in `ΩBar₀` and no internal vertex in `ΩBar₀`: `D ⊆ Δ` is a
closed
disc bounded by the image of `P` under `Γ` and a portion of `bd(Δ₀)` such that `Δ₀ ⊈ D`
(Graph Minors IX, Section 11, page 67). -/
def IsPathDisc {α : Type u} {β : Type v} {N : Neighborhood α β}
    (P_pres : Presentation N) (P : Graph α β) (D : Set EuclideanPlane) : Prop :=
  (∃ a b : α, IsGraphPathWithEnds N.G P a b ∧ a ≠ b ∧ a ∈ N.Ω₀.bar ∧ b ∈ N.Ω₀.bar ∧
    Disjoint (V(P) \ {a, b}) N.Ω₀.bar) ∧
  IsClosedDisc D ∧ D ⊆ P_pres.Δ ∧ ¬ (P_pres.Δ₀ ⊆ D) ∧
  graphDrawingSubgraphU P_pres.Γ P ⊆ subBd D ∧
  subBd D ⊆ graphDrawingSubgraphU P_pres.Γ P ∪ subBd P_pres.Δ₀

/-- "A *prominence* is a path $P$ of $G$ with the following properties: (i) the ends of $P$ are
distinct and are both in $\bar{\Omega}_0$ (ii) no internal vertex of $P$ is in
$\bar{\Omega}_0$ (iii) $P$ has at most two edges (iv) subject to (i), (ii), and (iii),
$\Delta(P)$ is maximal."
(Graph Minors IX, Section 11, page 67). -/
def IsProminenceWithDisc {α : Type u} {β : Type v} {N : Neighborhood α β}
    (P_pres : Presentation N) (P : Graph α β) (L : Set EuclideanPlane) : Prop :=
  IsPathDisc P_pres P L ∧ E(P).ncard ≤ 2 ∧
    ∀ (P' : Graph α β) (L' : Set EuclideanPlane),
      IsPathDisc P_pres P' L' → E(P').ncard ≤ 2 → L ⊆ L' → L' = L

/-- `P` is a prominence of `P_pres` (Graph Minors IX, Section 11, page 67). -/
def IsProminence {α : Type u} {β : Type v} {N : Neighborhood α β}
    (P_pres : Presentation N) (P : Graph α β) : Prop :=
  ∃ L : Set EuclideanPlane, IsProminenceWithDisc P_pres P L

/-- "If $P$ is a prominence, $\Delta(P)$ is a *lawn" (Graph Minors IX, Section 11, page 67). -/
def IsLawn {α : Type u} {β : Type v} {N : Neighborhood α β}
    (P_pres : Presentation N) (L : Set EuclideanPlane) : Prop :=
  ∃ P : Graph α β, IsProminenceWithDisc P_pres P L

/-- The union of `Δ₀` with all lawns of `P_pres` (Graph Minors IX, Section 11, page 67). -/
def wallDisc {α : Type u} {β : Type v} {N : Neighborhood α β}
    (P_pres : Presentation N) : Set EuclideanPlane :=
  P_pres.Δ₀ ∪ ⋃ L ∈ {L : Set EuclideanPlane | IsLawn P_pres L}, L

/-- "It follows that the union of $\Delta_0$ with all lawns is a closed disc; we call its
boundary the *wall" (Graph Minors IX, Section 11, page 67). -/
def wall {α : Type u} {β : Type v} {N : Neighborhood α β}
    (P_pres : Presentation N) : Set EuclideanPlane :=
  subBd (wallDisc P_pres)

/-- "Let $e \in E(G)$; we call it an *internal*, *external*, or *wall edge* if the arc which
represents $e$ in the drawing $\Gamma$ is a subset of the interior of the disc bounded by
the wall, the complement in $\Delta$ of this disc, or the wall itself, respectively"
(Graph Minors IX, Section 11, page 67). -/
def IsInternalEdge {α : Type u} {β : Type v} {N : Neighborhood α β}
    (P_pres : Presentation N) (e : β) : Prop :=
  e ∈ E(N.G) ∧ graphDrawingEdgeSet P_pres.Γ e ⊆ interior (wallDisc P_pres)

/-- `e ∈ E(G)` is an external edge with respect to `P_pres`
(Graph Minors IX, Section 11, page 67). -/
def IsExternalEdge {α : Type u} {β : Type v} {N : Neighborhood α β}
    (P_pres : Presentation N) (e : β) : Prop :=
  e ∈ E(N.G) ∧ graphDrawingEdgeSet P_pres.Γ e ⊆ P_pres.Δ \ wallDisc P_pres

/-- `e ∈ E(G)` is a wall edge with respect to `P_pres`
(Graph Minors IX, Section 11, page 67). -/
def IsWallEdge {α : Type u} {β : Type v} {N : Neighborhood α β}
    (P_pres : Presentation N) (e : β) : Prop :=
  e ∈ E(N.G) ∧ graphDrawingEdgeSet P_pres.Γ e ⊆ wall P_pres

/-- "A triangle in $G$ is a circuit of length 3" (Graph Minors IX, Section 11, page 68). -/
def IsTriangle {α : Type u} {β : Type v} (G T : Graph α β) : Prop :=
  IsGraphCircuit G T ∧ E(T).ncard = 3

/-- "The clockwise orientation of the wall provides a cyclic permutation $\Omega^*$ of the
vertices of $G$ drawn in it. Let $G^*$ be the subgraph of $G$ consisting of all vertices and
edges drawn in the closed disc bounded by the wall. Then $(G^*, \Omega^*, \Omega_0)$ is a
rural neighborhood, called the *park* of $(G, \Omega, \Omega_0)$ (under the presentation
$(\Sigma, \Gamma, \Delta, \Delta_0)$). Any rural neighborhood which can be constructed this
way is called a *park" (Graph Minors IX, Section 11, page 68). -/
def IsParkOf {α : Type u} {β : Type v} {N : Neighborhood α β}
    (P_pres : Presentation N) (N_star : Neighborhood α β) : Prop :=
  IsSimpleGraph N.G ∧
  N_star.Ω₀ = N.Ω₀ ∧
  V(N_star.G) = {v ∈ V(N.G) | graphDrawingVertexSet P_pres.Γ v ⊆ wallDisc P_pres} ∧
  E(N_star.G) = {e ∈ E(N.G) | graphDrawingEdgeSet P_pres.Γ e ⊆ wallDisc P_pres} ∧
  N_star.G ≤ N.G ∧
  N_star.Ω.bar = {v ∈ V(N.G) | graphDrawingVertexSet P_pres.Γ v ⊆ wall P_pres} ∧
  IsClosedDisc (wallDisc P_pres) ∧
  ∃ φ : Circle ≃ₜ wall P_pres,
    IsClockwiseDiscHomeo (wallDisc P_pres) φ ∧
      DrawingAgreesWithOArcHomeo P_pres.Γ N_star.Ω (wall P_pres) φ

/-- `N_star` is a park (Graph Minors IX, Section 11, page 68). -/
def Neighborhood.IsPark {α : Type u} {β : Type v} (N_star : Neighborhood α β) : Prop :=
  ∃ (N : Neighborhood α β) (P_pres : Presentation N), IsParkOf P_pres N_star

/-- "Let $(G, \Omega)$ be a society. A set $\mathcal{D}$ of separations of $(G, \Omega)$ is a
*consolidation* of $(G, \Omega)$ if (i) $|V(A \cap B)| \le 3$ for all $(A, B) \in
\mathcal{D}$ (ii) $A \subseteq B'$ for all distinct $(A, B), (A', B') \in \mathcal{D}$ (iii)
$\bigcup (A: (A, B) \in \mathcal{D}) = G$ (iv) for each $(A, B) \in \mathcal{D}$ and every
choice of distinct $u, v \in V(A \cap B)$ there is a path of $A$ with ends $u, v$ and with
no internal vertex in $B$."
(Graph Minors IX, Section 11, page 70). -/
structure IsConsolidation {α : Type u} {β : Type v} (S : Society α β)
    (D_set : Set (Graph α β × Graph α β)) : Prop where
  /-- Every `(A, B) ∈ D_set` is a separation of `(G, Ω)`. -/
  isSocietySeparation : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D_set → S.IsSocietySeparation A B
  /-- (i) `|V(A ∩ B)| ≤ 3` for all `(A, B) ∈ D_set`. -/
  order_le_three : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D_set → (V(A) ∩ V(B)).ncard ≤ 3
  /-- (ii) `A ⊆ B'` for all distinct `(A, B), (A', B') ∈ D_set`. -/
  left_le_right : ∀ ⦃A B A' B' : Graph α β⦄, (A, B) ∈ D_set → (A', B') ∈ D_set →
    (A, B) ≠ (A', B') → A ≤ B'
  /-- (iii) `⋃ (A : (A, B) ∈ D_set) = G`. -/
  union_eq : subgraphSUnion S.G (Prod.fst '' D_set) = S.G
  /-- (iv) For each `(A, B) ∈ D_set` and distinct `u, v ∈ V(A ∩ B)`, there is a path of `A` with
  ends `u, v` and with no internal vertex in `B`. -/
  exists_path : ∀ ⦃A B : Graph α β⦄, (A, B) ∈ D_set →
    ∀ u ∈ V(A) ∩ V(B), ∀ v ∈ V(A) ∩ V(B), u ≠ v →
      ∃ P : Graph α β, IsGraphPathWithEnds A P u v ∧ Disjoint (V(P) \ {u, v}) V(B)

/-- "Let $\mathcal{D}$ be a consolidation of $(G, \Omega)$. Its *core* is the simple graph $C$
with $V(C) = \bigcap (V(B): (A, B) \in \mathcal{D})$ in which distinct vertices $u, v$ are
adjacent if there exists $(A, B) \in \mathcal{D}$ with $u, v \in V(A \cap B)$" (Graph Minors IX,
Section 11, page 70). -/
def consolidationCore {α : Type u} {β : Type v} (S : Society α β)
    (D_set : Set (Graph α β × Graph α β)) : Graph α (Sym2 α) where
  vertexSet := V(S.G) ∩ ⋂ p ∈ D_set, V(p.2)
  edgeSet := {e : Sym2 α | ∃ u v : α, u ≠ v ∧ e = s(u, v) ∧
    u ∈ V(S.G) ∩ ⋂ p ∈ D_set, V(p.2) ∧ v ∈ V(S.G) ∩ ⋂ p ∈ D_set, V(p.2) ∧
    ∃ p ∈ D_set, u ∈ V(p.1) ∩ V(p.2) ∧ v ∈ V(p.1) ∩ V(p.2)}
  IsLink e x y := x ≠ y ∧ e = s(x, y) ∧
    x ∈ V(S.G) ∩ ⋂ p ∈ D_set, V(p.2) ∧ y ∈ V(S.G) ∩ ⋂ p ∈ D_set, V(p.2) ∧
    ∃ p ∈ D_set, x ∈ V(p.1) ∩ V(p.2) ∧ y ∈ V(p.1) ∩ V(p.2)
  isLink_symm _ _ := ⟨fun _ _ ⟨hxy, he, hx, hy, p, hp, hxp, hyp⟩ =>
    ⟨hxy.symm, he.trans (Sym2.eq_swap), hy, hx, p, hp, hyp, hxp⟩⟩
  eq_or_eq_of_isLink_of_isLink e x y z w h1 h2 := by
    have heq : s(x, y) = s(z, w) := h1.2.1.symm.trans h2.2.1
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink _ := ⟨fun ⟨u, v, h⟩ => ⟨u, v, h⟩, fun ⟨u, v, h⟩ => ⟨u, v, h⟩⟩
  left_mem_of_isLink _ _ _ h := h.2.2.1

/-- "The pattern of a transaction $\mathcal{P}$ in $(G, \Omega)$ is the set $\{X(P): P \in
\mathcal{P}\}$ where $X(P)$ denotes the set of ends of $P \in \mathcal{P}$" (Graph Minors IX,
Section 11, page 73). -/
def Society.transactionPattern {α : Type u} {β : Type v} (S : Society α β)
    (P_set : Set (Graph α β)) : Set (Set α) :=
  (fun P => pathEnds S.G P) '' P_set

/-- "A segregation of a society $(G, \Omega)$ is a set $\{(A_0, \Omega_0), \dots, (A_k,
\Omega_k)\}$ of societies such that (i) $A_0 \cup \dots \cup A_k = G$ and $E(A_i \cap A_j) =
\emptyset$ for $0 \le i, j \le k$ with $i \neq j$ (ii) $V(A_i \cap A_j) \subseteq
\bar{\Omega}_i$ for $0 \le i, j \le k$ with $i \neq j$ (iii) $\bar{\Omega} \subseteq
\bar{\Omega}_0 \cup \dots \cup \bar{\Omega}_k$."
(Graph Minors IX, Section 11, page 74). -/
structure IsSocietySegregation {α : Type u} {β : Type v} (S : Society α β)
    {k : ℕ} (A₀ : Society α β) (A : Fin k → Society α β) : Prop where
  /-- `A₀ ≤ G`. -/
  le_zero : A₀.G ≤ S.G
  /-- `A_i ≤ G` for `1 ≤ i ≤ k`. -/
  le_succ : ∀ i : Fin k, (A i).G ≤ S.G
  /-- (i) `V(A₀) ∪ ⋃_i V(A_i) = V(G)`. -/
  vertexSet_union : V(A₀.G) ∪ (⋃ i : Fin k, V((A i).G)) = V(S.G)
  /-- (i) `E(A₀) ∪ ⋃_i E(A_i) = E(G)`. -/
  edgeSet_union : E(A₀.G) ∪ (⋃ i : Fin k, E((A i).G)) = E(S.G)
  /-- (i) `E(A₀ ∩ A_i) = ∅` for `1 ≤ i ≤ k`. -/
  disjoint_zero : ∀ i : Fin k, Disjoint E(A₀.G) E((A i).G)
  /-- (i) `E(A_i ∩ A_j) = ∅` for `1 ≤ i < j ≤ k`. -/
  disjoint_succ : Pairwise (fun i j : Fin k => Disjoint E((A i).G) E((A j).G))
  /-- (ii) `V(A₀ ∩ A_i) ⊆ ΩBar₀ ∩ ΩBar_i` for `1 ≤ i ≤ k`. -/
  inter_zero_subset : ∀ i : Fin k, V(A₀.G) ∩ V((A i).G) ⊆ A₀.Ω.bar ∩ (A i).Ω.bar
  /-- (ii) `V(A_i ∩ A_j) ⊆ ΩBar_i ∩ ΩBar_j` for `1 ≤ i < j ≤ k`. -/
  inter_succ_subset : ∀ i j : Fin k, i ≠ j → V((A i).G) ∩ V((A j).G) ⊆ (A i).Ω.bar ∩ (A j).Ω.bar
  /-- (iii) `ΩBar ⊆ ΩBar₀ ∪ ⋯ ∪ ΩBar_k`. -/
  bar_subset_union : S.Ω.bar ⊆ A₀.Ω.bar ∪ ⋃ i : Fin k, (A i).Ω.bar

/-- "An arrangement of a segregation $\{(A_0, \Omega_0), \dots, (A_k, \Omega_k)\}$ of $(G,
\Omega)$ in a closed disc $\Delta$ is a function $\alpha$ with domain $$ \{(A_0, \Omega_0),
\dots, (A_k, \Omega_k)\} \cup \bar{\Omega}_0 \cup \dots \cup \bar{\Omega}_k $$ and with the
following properties: (i) for $0 \le i \le k$, $\alpha((A_i, \Omega_i))$ is a closed disc
$\Delta_i \subseteq \Delta$ and $\alpha(v) \in bd(\Delta_i)$ for each $v \in
\bar{\Omega}_i$, and $\alpha(v) \in bd(\Delta)$ for each $v \in \bar{\Omega}$ (ii) for $0
\le i < j \le k$, if $x \in \Delta_i \cap \Delta_j$, then $x = \alpha(v)$ for some $v \in
\bar{\Omega}_i \cap \bar{\Omega}_j$, and for $0 \le i \le k$, if $x \in \Delta_i \cap
bd(\Delta)$ then $x = \alpha(v)$ for some $v \in \bar{\Omega}_i \cap \bar{\Omega}$ (iii)
$\alpha(u) \neq \alpha(v)$ for distinct $u, v \in \bar{\Omega}_0 \cup \dots \cup
\bar{\Omega}_k$ (iv) for $0 \le i \le k$, $\Omega_i$ is the cyclic permutation of
$\bar{\Omega}_i$ derived (under $\alpha^{-1}$) from the clockwise orientation of
$bd(\Delta_i)$, and $\Omega$ is the permutation derived from the clockwise orientation of
$bd(\Delta)$."
(Graph Minors IX, Section 11, page 74). -/
structure IsDiscArrangement {α : Type u} {β : Type v} (S : Society α β)
    {k : ℕ} (A₀ : Society α β) (A : Fin k → Society α β)
    (Δ : Set EuclideanPlane) (α₀ : Set EuclideanPlane) (α_disc : Fin k → Set EuclideanPlane)
    (α_pt : α → EuclideanPlane) : Prop where
  /-- `Δ` is a closed disc in `EuclideanPlane`. -/
  isClosedDisc_Δ : IsClosedDisc Δ
  /-- (i) `α((A₀, Ω₀))` is a closed disc `Δ₀ ⊆ Δ`. -/
  isClosedDisc_zero : IsClosedDisc α₀ ∧ α₀ ⊆ Δ
  /-- (i) `α((A_i, Ω_i))` is a closed disc `Δ_i ⊆ Δ` for `1 ≤ i ≤ k`. -/
  isClosedDisc_succ : ∀ i : Fin k, IsClosedDisc (α_disc i) ∧ α_disc i ⊆ Δ
  /-- (i) and (iv) for `(A₀, Ω₀)`: `α(v) ∈ bd(Δ₀)` for `v ∈ ΩBar₀`, and clockwise agreement. -/
  bd_zero : ∃ φ₀ : Circle ≃ₜ subBd α₀,
    IsClockwiseDiscHomeo α₀ φ₀ ∧ AgreesWithOArcHomeo α_pt A₀.Ω (subBd α₀) φ₀
  /-- (i) and (iv) for `(A_i, Ω_i)`: `α(v) ∈ bd(Δ_i)` for `v ∈ ΩBar_i`, and clockwise agreement. -/
  bd_succ : ∀ i : Fin k, ∃ φ_i : Circle ≃ₜ subBd (α_disc i),
    IsClockwiseDiscHomeo (α_disc i) φ_i ∧
      AgreesWithOArcHomeo α_pt (A i).Ω (subBd (α_disc i)) φ_i
  /-- (i) and (iv) for `(G, Ω)`: `α(v) ∈ bd(Δ)` for `v ∈ ΩBar`, and clockwise agreement. -/
  bd_outer : ∃ φ : Circle ≃ₜ subBd Δ,
    IsClockwiseDiscHomeo Δ φ ∧ AgreesWithOArcHomeo α_pt S.Ω (subBd Δ) φ
  /-- (ii) Between `Δ₀` and `Δ_i`: `Δ₀ ∩ Δ_i ⊆ α '' (ΩBar₀ ∩ ΩBar_i)`. -/
  inter_zero : ∀ i : Fin k, α₀ ∩ α_disc i ⊆ α_pt '' (A₀.Ω.bar ∩ (A i).Ω.bar)
  /-- (ii) Between `Δ_i` and `Δ_j` for `i ≠ j`: `Δ_i ∩ Δ_j ⊆ α '' (ΩBar_i ∩ ΩBar_j)`. -/
  inter_succ : ∀ i j : Fin k, i ≠ j → α_disc i ∩ α_disc j ⊆ α_pt '' ((A i).Ω.bar ∩ (A j).Ω.bar)
  /-- (ii) Between `Δ₀` and `bd(Δ)`: `Δ₀ ∩ bd(Δ) ⊆ α '' (ΩBar₀ ∩ ΩBar)`. -/
  inter_bd_zero : α₀ ∩ subBd Δ ⊆ α_pt '' (A₀.Ω.bar ∩ S.Ω.bar)
  /-- (ii) Between `Δ_i` and `bd(Δ)`: `Δ_i ∩ bd(Δ) ⊆ α '' (ΩBar_i ∩ ΩBar)`. -/
  inter_bd_succ : ∀ i : Fin k, α_disc i ∩ subBd Δ ⊆ α_pt '' ((A i).Ω.bar ∩ S.Ω.bar)
  /-- (iii) `α(u) ≠ α(v)` for distinct `u, v ∈ ΩBar₀ ∪ ⋯ ∪ ΩBar_k`. -/
  injOn_pts : InjOn α_pt (A₀.Ω.bar ∪ ⋃ i : Fin k, (A i).Ω.bar)

/-- "A segregation is *feasible* if there is an arrangement of it in some disc"
(Graph Minors IX, Section 11, page 74). -/
def IsFeasibleSegregation {α : Type u} {β : Type v} (S : Society α β)
    {k : ℕ} (A₀ : Society α β) (A : Fin k → Society α β) : Prop :=
  IsSocietySegregation S A₀ A ∧
    ∃ (Δ α₀ : Set EuclideanPlane) (α_disc : Fin k → Set EuclideanPlane) (α_pt : α → EuclideanPlane),
      IsDiscArrangement S A₀ A Δ α₀ α_disc α_pt

end GraphMinor.GM09
