/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM10.Defs2
public import LeanPool.GraphMinor.GM11.Defs

/-!
# Definitions of Graph Minors XIV

This file formalizes the definitions of N. Robertson and P. D. Seymour,
*Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B **65** (1995) 23–50.

## Contents

- **Section 1 (pages 24–25):** Subdivisions of simple 3-connected graphs
  (`IsSubdivisionOfSimpleThreeConnected`) and `ins(φ)` for `H`-normal closed curves (`curveIns`).
- **Section 2 (pages 25–26):** Radial drawings `K` of `H` (`GM11.PaintingOrDrawing.IsRadialDrawing`)
  and the atom `x'` of `K` corresponding to an atom `x` of `H` (`IsCorrespondingAtom`).
- **Section 3 (pages 27–29):** Respectful tangles in drawings (`IsRespectfulDrawingTangle`),
  the inside function `ins` and metric `d(x, y)` of a respectful tangle (`tangleMetric`),
  `λ`-zones around an atom `z` (`IsLambdaZoneAround`, `IsLambdaZone`), the subdrawing
  `H ∩ (Σ - Λ)` (`clearedSubdrawing`), tangles obtained by clearing `Λ` (`IsClearedTangle`),
  free sets (`GM10.IsFreeSet`), `H`-paths (`IsHPath`), embeddings of a drawing `H` as a subgraph of
  `G` (`SpanEmbedding`, `DrawingSubgraph`), and eyes of `H` in `G` with respect to `T`
  (`IsDrawingEye`).
- **Section 4 (pages 29–31):** Dials for `F, H` (`IsDial`), rigid drawings (`IsRigid`), natural
  orders of `X ⊆ F` from an `O`-arc `F` (`IsNaturalOrderFrom`), segregations and 3-segregations of a
  graph `G` (`IsGraphSegregation`, `IsThreeSegregation`), arrangements of a segregation in a surface
  `Σ` (`IsSurfaceArrangement`), arrangements compatible with `H` (`IsCompatibleWith`), `T`-local
  segregations (`IsTangleLocal`), and bridges of `H` in `G` (`IsBridge`).
- **Section 5 (pages 31–32):** Connected sets of regions (`IsConnectedRegionSet`), chains of
  points and regions (`IsRegionChain`), and regional distance (`regionalDistance`).
- **Section 6 (pages 33–35):** Simply-connected subsets `X ⊆ Σ` in the sense of Section 6
  (`IsArcSimplyConnected`) and isomorphic drawings (`AreIsomorphicDrawings`).
- **Section 7 (pages 37–39):** `α`-normal subsets `X ⊆ Σ` (`IsArrangementNormal`).
- **Section 8 (pages 39–45):** Pullback cyclic permutation `α⁻¹(F)` (`IsPullbackPerm`) and
  cylinder breadth `≥ q` (`HasCylinderBreadthGe`).
- **Section 9 (pages 45–47):** Battlefields `(Λ, C, X)` of size `β` around `z` (`IsBattlefield`) and
  pullback subgraphs `α⁻¹(Σ')` (`arrangementPullbackGraph`).
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10
  GraphMinor.GM11 Hypergraph

universe u v w

/-! ## Section 1: Introduction (pages 24–25) -/

/-- A graph `G₀` is simple and 3-connected if it is simple, has at least 4 vertices, and has no
separation `(G₁, G₂)` of order `< 3` with `V(G₁) ≠ V(G₀)` and `V(G₂) ≠ V(G₀)`
(Graph Minors XIV, Section 1, page 24). -/
def IsSimpleThreeConnectedGraph {α : Type u} {β : Type v} (G₀ : Graph α β) : Prop :=
  IsSimpleGraph G₀ ∧ 4 ≤ V(G₀).ncard ∧
    ∀ G₁ G₂ : Graph α β, IsGraphSeparation G₀ G₁ G₂ →
      (V(G₁) ∩ V(G₂)).ncard < 3 → V(G₁) = V(G₀) ∨ V(G₂) = V(G₀)

/-- `G` is a subdivision of `G₀` if `G` is obtained from `G₀` by replacing each edge `e ∈ E(G₀)`
with a path `P_e` of `G` between the ends of `e`, of length `≥ 1`, such that the paths `P_e` are
mutually internally vertex-disjoint and meet `V(G₀)` only at their ends
(Graph Minors XIV, Section 1, page 24). -/
def IsSubdivisionOf {α : Type u} {β : Type v} (G G₀ : Graph α β) : Prop :=
  V(G₀) ⊆ V(G) ∧
    ∃ P : β → Graph α β,
      (∀ e ∈ E(G₀), ∃ u v : α, G₀.IsLink e u v ∧ IsGraphPathWithEnds G (P e) u v ∧
        E(P e).Nonempty ∧ V(P e) ∩ V(G₀) = {u, v}) ∧
      (∀ e₁ ∈ E(G₀), ∀ e₂ ∈ E(G₀), e₁ ≠ e₂ →
        Disjoint E(P e₁) E(P e₂) ∧ V(P e₁) ∩ V(P e₂) ⊆ V(G₀)) ∧
      V(G) = V(G₀) ∪ (⋃ e ∈ E(G₀), V(P e)) ∧
      E(G) = ⋃ e ∈ E(G₀), E(P e)

/-- `G` is a subdivision of a simple 3-connected graph (Graph Minors XIV, Section 1, page 24). -/
def IsSubdivisionOfSimpleThreeConnected {α : Type u} {β : Type v} (G : Graph α β) : Prop :=
  ∃ G₀ : Graph α β, IsSimpleThreeConnectedGraph G₀ ∧ IsSubdivisionOf G G₀

section SurfaceDefs

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- For an `H`-normal closed curve `φ : S¹ → Σ` in a surface `Σ` that is not a sphere, `ins(φ)` is
the union of `|φ|` and all closed discs in `Σ` with boundary included in `|φ|`
(Graph Minors XIV, Section 1, (1.1), page 24). -/
def curveIns (φ : C(Circle, S)) : Set S :=
  range φ ∪ ⋃ Δ ∈ {Δ : Set S | IsClosedDisc Δ ∧ subBd Δ ⊆ range φ}, Δ

/-! ## Section 2: Radial Drawings (pages 25–26) -/

/-- "If $K$ is a radial drawing of $H$, then to every atom $x$ of $H$ there naturally corresponds
an atom $x'$ of $K$; namely, if $x = \{v\}$ for some $v \in V(H)$ then $x' = x$, if $x \in E(H)$,
then $x' \in R(K)$ includes $e$; and if $x \in R(H)$, then $x' = \{v\}$ for the unique $v \in V(K)$
with $v \in x$. We call $x'$ the *atom of $K$ corresponding to $x$*"
(Graph Minors XIV, Section 2, page 26; the paper writes $e$ for $x$). -/
def IsCorrespondingAtom (H K : Drawing S) (x x' : Set S) : Prop :=
  x ∈ H.A ∧ x' ∈ K.A ∧
    ((∃ v ∈ H.V, x = {v} ∧ x' = {v}) ∨
      (x ∈ H.E ∧ x' ∈ K.R ∧ x ⊆ x') ∨
      (x ∈ H.R ∧ ∃ v ∈ K.V ∩ x, x' = {v}))

/-! ## Section 3: Tangles (pages 27–29) -/

/-- `T` is a respectful tangle of order `θ` in a 2-cell drawing `H` in `Σ`
(Graph Minors XIV, Section 3, page 27). -/
def IsRespectfulDrawingTangle (H : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) : Prop :=
  (PaintingOrDrawing.drawing H).IsTwoCell ∧
    IsTangle H.toHypergraph θ T ∧
    (PaintingOrDrawing.drawing H).IsRespectful θ T

/-- The metric `d(x, y)` of a respectful tangle `T` of order `θ` in `H` (with radial drawing `K`
and derived inside function `ins`), for `x, y ∈ A(H)` with corresponding atoms `x', y'` of `K`:
- `0` if `x = y`,
- `k` if `x ≠ y` and there is a closed walk `W` of `K` with length `< 2θ` with `x', y' ⊆ ins(W)`,
  and the shortest such walk has length `2k`,
- `θ` otherwise
(Graph Minors XIV, Section 3, page 27; Graph Minors XII, Section 1, page 242). -/
noncomputable def tangleMetric (H K : Drawing S) (ins : Drawing S → Set S) (θ : ℕ)
    (x y : Set S) : ℕ :=
  open Classical in
  if x = y then 0
  else if ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
      IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
      W.length < 2 * θ ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W then
    sInf {k : ℕ | ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
      IsCorrespondingAtom H K x x' ∧ IsCorrespondingAtom H K y y' ∧
      W.length < 2 * θ ∧ W.length = 2 * k ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W}
  else θ

/-- `d` is the metric of the respectful tangle `T` of order `θ` in `H`
(Graph Minors XIV, Section 3, page 27). -/
def HasTangleMetric (H : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) : Prop :=
  IsRespectfulDrawingTangle H θ T ∧
    ∃ (K : Drawing S) (ins : Drawing S → Set S),
      (PaintingOrDrawing.drawing H).IsRadialDrawing K ∧
      IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins ∧
      ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y

/-- The corrected definition of a zone in Graph Minors XIV, §3. The printed text reads:
"Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in $H$
of order $\theta$, with metric $d$. Let $z \in A(H)$ and let $\lambda \ge 0$ be an integer.
A *$\lambda$-zone around $z$* is an open disc $\Lambda \subseteq \Sigma$ with $z \subseteq
\Lambda$, such that $bd(\Lambda)$ is an $O$-arc and hence $\overline{\Lambda}$ is a closed
disc, $bd(\Lambda) \subseteq U(H)$, $d(z, x) \le \lambda$ for all $x \in A(H)$ with $x
\subseteq \overline{\Lambda}$, and if $z \in E(H)$ then $\lambda \ge 2$" (Graph Minors XIV, Section
3, page 28). The formal definition requires the closure to be a closed disc as a separate
condition. The printed implication from an $O$-arc boundary fails on the projective plane. -/
structure IsLambdaZoneAround (H : Drawing S) (d : Set S → Set S → ℕ) (lam : ℕ)
    (z Λ : Set S) : Prop where
  /-- `z ∈ A(H)`. -/
  z_mem : z ∈ H.A
  /-- `Λ` is an open disc in `Σ`. -/
  isOpenDisc : IsOpenDisc Λ
  /-- `z ⊆ Λ`. -/
  z_subset : z ⊆ Λ
  /-- `bd(Λ)` is an `O`-arc. -/
  isOArc_bd : IsOArc (subBd Λ)
  /-- `closure Λ` is a closed disc. -/
  isClosedDisc_closure : IsClosedDisc (closure Λ)
  /-- `bd(Λ) ⊆ U(H)`. -/
  bd_subset_U : subBd Λ ⊆ H.U
  /-- `d(z, x) ≤ λ` for all `x ∈ A(H)` with `x ⊆ closure Λ`. -/
  dist_le : ∀ x ∈ H.A, x ⊆ closure Λ → d z x ≤ lam
  /-- If `z ∈ E(H)` then `λ ≥ 2`. -/
  two_le_of_edge : z ∈ H.E → 2 ≤ lam

/-- "A *$\lambda$-zone (for $H$)* is a subset of $\Sigma$ which is a $\lambda$-zone around $z$
for some $z \in A(H)$"
(Graph Minors XIV, Section 3, page 28). -/
def IsLambdaZone (H : Drawing S) (d : Set S → Set S → ℕ) (lam : ℕ) (Λ : Set S) : Prop :=
  ∃ z ∈ H.A, IsLambdaZoneAround H d lam z Λ

/-- `H' = H ∩ (Σ - Λ)`, the subdrawing of `H` outside `Λ`
(Graph Minors XIV, Section 3, page 28). -/
def clearedSubdrawing (H : Drawing S) (Λ : Set S) : Drawing S :=
  H.interSet (univ \ Λ)

/-- "We say that $\mathscr{T}'$ is a *tangle of order $\theta - 4\lambda - 2$ obtained by clearing
$\Lambda$* if $\mathscr{T}'$ is a tangle in $H'$ of order $\theta - 4\lambda - 2$, and
(i) $\mathscr{T}'$ is respectful, and has metric $d'$ say
(ii) $(A \cap H', B \cap H') \in \mathscr{T}'$ for all $(A, B) \in \mathscr{T}$ of order $<\theta -
4\lambda - 2$, and
(iii) if $x, y \in A(H)$ and $x', y' \in A(H')$ with $x \subseteq x'$ and $y \subseteq y'$, then
$d(x, y) \ge d'(x', y') \ge d(x, y) - 4\lambda - 2$."
(Graph Minors XIV, Section 3, page 28, where $H' = H \cap (\Sigma - \Lambda)$). -/
structure IsClearedTangle (H : Drawing S)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (θ lam : ℕ) (Λ : Set S)
    (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d' : Set S → Set S → ℕ) : Prop where
  /-- `(i)` `T'` is a respectful tangle of order `θ - 4λ - 2` in `H' = H ∩ (Σ - Λ)` with metric
  `d'`. -/
  hasMetric : HasTangleMetric (clearedSubdrawing H Λ) (θ - 4 * lam - 2) T' d'
  /-- `(ii)` `(A ∩ H', B ∩ H') ∈ T'` for all `(A, B) ∈ T` of order `< θ - 4λ - 2`. -/
  mem_of_order_lt : ∀ A B : Hypergraph S (Set S),
    (A, B) ∈ T → separationOrder A B < θ - 4 * lam - 2 →
      (A ∩ (clearedSubdrawing H Λ).toHypergraph,
        B ∩ (clearedSubdrawing H Λ).toHypergraph) ∈ T'
  /-- `(iii)` Distance comparison for `x, y ∈ A(H)` and `x', y' ∈ A(H')` with `x ⊆ x'`, `y ⊆ y'`. -/
  dist_bounds : ∀ x ∈ H.A, ∀ y ∈ H.A,
    ∀ x' ∈ (clearedSubdrawing H Λ).A, ∀ y' ∈ (clearedSubdrawing H Λ).A,
      x ⊆ x' → y ⊆ y' → d x y - 4 * lam - 2 ≤ d' x' y' ∧ d' x' y' ≤ d x y

/-- "If $H$ is a subgraph of $G$, an *$H$-path* is a path of $G$ with distinct ends both in
$V(H)$ and with no other vertex or edge in $H$" (Graph Minors XIV, Section 3, page 28). -/
def IsHPathWithEnds {α : Type v} {β : Type w} (G H P : Graph α β) (a b : α) : Prop :=
  H ≤ G ∧ IsGraphPathWithEnds G P a b ∧ a ≠ b ∧ a ∈ V(H) ∧ b ∈ V(H) ∧
    V(P) ∩ V(H) = {a, b} ∧ Disjoint E(P) E(H)

/-- `P` is an `H`-path in `G` (Graph Minors XIV, Section 3, page 28). -/
def IsHPath {α : Type v} {β : Type w} (G H P : Graph α β) : Prop :=
  ∃ a b : α, IsHPathWithEnds G H P a b

/-- Four distinct vertices `a, b, c, d` occur in `V(C)` in that cyclic order along the circuit `C`
(Graph Minors XIV, Section 3, page 28). -/
def OccurInCircuitOrder (C : Drawing S) (a b c d : S) : Prop :=
  ∃ φ : Circle ≃ₜ C.U,
    ∃ (t₁ t₂ t₃ t₄ : ℝ), 0 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₄ ∧ t₄ < 2 * Real.pi ∧
      (φ (Circle.exp t₁)).1 = a ∧ (φ (Circle.exp t₂)).1 = b ∧
      (φ (Circle.exp t₃)).1 = c ∧ (φ (Circle.exp t₄)).1 = d

/-- An embedding `η` of a drawing `H` in `Σ` as a subgraph `imageGraph ≤ G` of an abstract graph
`G : Graph α β` (Graph Minors XIV, Section 3, page 28; Graph Minors XV, Section 1, page 114). -/
structure SpanEmbedding {α : Type v} {β : Type w} (H : Drawing S) (G : Graph α β) where
  /-- The image subgraph `η(H) ≤ G`. -/
  imageGraph : Graph α β
  /-- The vertex bijection `η_V : S → α` on `V(H)`. -/
  vMap : S → α
  /-- The edge bijection `η_E : Set S → β` on `E(H)`. -/
  eMap : Set S → β
  /-- `imageGraph ≤ G`. -/
  imageGraph_le : imageGraph ≤ G
  /-- `vMap` maps `V(H)` bijectively onto `V(imageGraph)`. -/
  bijOn_v : BijOn vMap H.V V(imageGraph)
  /-- `eMap` maps `E(H)` bijectively onto `E(imageGraph)`. -/
  bijOn_e : BijOn eMap H.E E(imageGraph)
  /-- `η` preserves the incidence relation between vertices and edges. -/
  inc_iff : ∀ e ∈ H.E, ∀ v ∈ H.V, imageGraph.Inc (eMap e) (vMap v) ↔ v ∈ closure e

/-- Alias for `SpanEmbedding`. -/
abbrev DrawingSubgraph {α : Type v} {β : Type w} (H : Drawing S) (G : Graph α β) :=
  SpanEmbedding H G

/-- "Let $H$ be a subgraph of $G$, and let $H$ be a 2-cell drawing in $\Sigma$. Let $\mathscr{T}$
be a respectful tangle in $H$. A region $r$ of $H$ is an *eye of $H$(in $G$) with respect to
$\mathscr{T}$* if (i) there is a circuit $C$ of $H$ with $U(C) = bd(r)$ (ii) there are
distinct vertices $a, b, c, d$ occurring in $V(C)$ in that order, and $\{a, b, c, d\}$ is
free with respect to $\mathscr{T}$, and ... (iii) there are two disjoint $H$-paths in $G$ with
ends $a, c$ and $b, d$ respectively."
(Graph Minors XIV, Section 3, pages 28–29). -/
def IsDrawingEye {α : Type v} {β : Type w} (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (r : Set S) : Prop :=
  r ∈ H.R ∧
    ∃ (C : Drawing S) (a b c d : S) (P₁ P₂ : Graph α β),
      C.IsCircuit ∧ C.IsSubdrawing H ∧ C.U = subBd r ∧
      a ∈ C.V ∧ b ∈ C.V ∧ c ∈ C.V ∧ d ∈ C.V ∧
      ([a, b, c, d]).Nodup ∧ OccurInCircuitOrder C a b c d ∧
      IsFreeSet H.toHypergraph T θ {a, b, c, d} ∧
      Disjoint V(P₁) V(P₂) ∧
      IsHPathWithEnds G η.imageGraph P₁ (η.vMap a) (η.vMap c) ∧
      IsHPathWithEnds G η.imageGraph P₂ (η.vMap b) (η.vMap d)

/-! ## Section 4: Statement of the Theorem (pages 29–31) -/

/-- "Let $H$ be a drawing in a surface $\Sigma$. If $F \subseteq \Sigma$ is an $O$-arc with $F
\cap U(H) \subseteq V(H)$ and $|F \cap V(H)| \le 2$, a *dial for $F$ (or for $F, H$ in case
of ambiguity)* is a closed disc $\Delta \subseteq \Sigma$ with $bd(\Delta) = F$, such that
either (i) $\Delta \cap U(H) \subseteq F$, or (ii) $|F \cap V(H)| = 2$ and $H \cap \Delta$
is a path joining the two vertices in $F \cap V(H)$."
(Graph Minors XIV, Section 4, page 29). -/
def IsDial (H : Drawing S) (F Δ : Set S) : Prop :=
  IsClosedDisc Δ ∧ subBd Δ = F ∧
    (Δ ∩ H.U ⊆ F ∨
      ∃ u v : S, u ≠ v ∧ F ∩ H.V = {u, v} ∧ (H.interSet Δ).IsPathBetween u v)

/-- "We say that $H$ is *rigid (in $\Sigma$)* if $\Sigma$ includes a dial for every $O$-arc $F
\subseteq \Sigma$ with $F \cap U(H) \subseteq V(H)$ and $|F \cap V(H)| \le 2$" (Graph Minors XIV,
Section 4, page 29). -/
def IsRigid (H : Drawing S) : Prop :=
  ∀ F : Set S, IsOArc F → F ∩ H.U ⊆ H.V → (F ∩ H.V).ncard ≤ 2 →
    ∃ Δ : Set S, IsDial H F Δ

/-- "If $F$ is an $O$-arc, and $X \subseteq F$ is finite, then both orientations of $F$ induce
cyclic permutations of $X$, and we call these the *natural orders of $X$ from $F$"
(Graph Minors XIV, Section 4, page 29). -/
def IsNaturalOrderFrom {α : Type v} (α_pt : α → S) (Ω : CyclicPerm α) (F : Set S) : Prop :=
  IsOArc F ∧ ∃ φ : Circle ≃ₜ F, AgreesWithOArcHomeo α_pt Ω F φ

/-- "A *segregation* of a graph $G$ is a set $\mathscr{S}$ of societies such that (i) $A
\subseteq G$ for every $(A, \Omega) \in \mathscr{S}$, and $\bigcup (A \colon (A, \Omega) \in
\mathscr{S}) = G$, and (ii) $V(A \cap A') \subseteq \overline{\Omega} \cap
\overline{\Omega}'$ and $E(A \cap A') = \emptyset$ for all distinct $(A, \Omega), (A',
\Omega') \in \mathscr{S}$."
(Graph Minors XIV, Section 4, page 29). -/
structure IsGraphSegregation {α : Type v} {β : Type w} (G : Graph α β)
    (S_seg : Set (Society α β)) : Prop where
  /-- `S_seg` is finite. -/
  finite : S_seg.Finite
  /-- `(i)` `A ≤ G` for every `(A, Ω) ∈ S_seg`. -/
  le : ∀ S₀ ∈ S_seg, S₀.G ≤ G
  /-- `(i)` `⋃_{(A, Ω) ∈ S_seg} A = G`. -/
  union_eq : subgraphSUnion G ((fun S₀ : Society α β => S₀.G) '' S_seg) = G
  /-- `(ii)` `V(A ∩ A') ⊆ ΩBar ∩ ΩBar'` for distinct `(A, Ω), (A', Ω') ∈ S_seg`. -/
  vertex_inter_subset : ∀ S₁ ∈ S_seg, ∀ S₂ ∈ S_seg, S₁ ≠ S₂ →
    V(S₁.G) ∩ V(S₂.G) ⊆ S₁.Ω.bar ∩ S₂.Ω.bar
  /-- `(ii)` `E(A ∩ A') = ∅` for distinct `(A, Ω), (A', Ω') ∈ S_seg`. -/
  edge_disjoint : ∀ S₁ ∈ S_seg, ∀ S₂ ∈ S_seg, S₁ ≠ S₂ → Disjoint E(S₁.G) E(S₂.G)

/-- `V(S_seg) = ⋃ (ΩBar : (A, Ω) ∈ S_seg)` (Graph Minors XIV, Section 4, page 29). -/
def segregationVertices {α : Type v} {β : Type w} (S_seg : Set (Society α β)) : Set α :=
  ⋃ S₀ ∈ S_seg, S₀.Ω.bar

/-- "A segregation $\mathscr{S}$ is a *3-segregation* if $|\overline{\Omega}| \le 3$ for all $(A,
\Omega) \in \mathscr{S}$"
(Graph Minors XIV, Section 4, page 29). -/
def IsThreeSegregation {α : Type v} {β : Type w} (G : Graph α β)
    (S_seg : Set (Society α β)) : Prop :=
  IsGraphSegregation G S_seg ∧ ∀ S₀ ∈ S_seg, S₀.Ω.bar.ncard ≤ 3

/-- "Let $\mathscr{S} = \{(A_1, \Omega_1), \dots, (A_k, \Omega_k)\}$ be a segregation of $G$, and
let $\Sigma$ be a surface. An *arrangement of $\mathscr{S}$ in $\Sigma$* is a function $\alpha$
with domain $\mathscr{S} \cup V(\mathscr{S})$, such that (writing $\alpha(A, \Omega)$ for
$\alpha((A, \Omega))$):
(i) $1 \le i \le k$, $\alpha(A_i, \Omega_i)$ is a closed disc $\Delta_i \subseteq \Sigma$, and
$\alpha(x) \in bd(\Delta_i)$ for each $x \in \overline{\Omega}_i$
(ii) for $1 \le i < j \le k$, if $x \in \Delta_i \cap \Delta_j$ then $x = \alpha(v)$ for some $v
\in \overline{\Omega}_i \cap \overline{\Omega}_j$; and for $1 \le i \le k$, if $x \in \Delta_i
\cap bd(\Sigma)$ then $x = \alpha(v)$ for some $v \in \overline{\Omega}_i$,
(iii) for distinct $x, y \in V(\mathscr{S})$, $\alpha(x) \ne \alpha(y)$, and
(iv) for $1 \le i \le k$, $\Omega_i$ is mapped by $\alpha$ to a natural order of
$\alpha(\Omega_i)$ from $bd(\Delta_i)$."
(Graph Minors XIV, Section 4, page 29). -/
structure IsSurfaceArrangement {α : Type v} {β : Type w}
    (S_seg : Set (Society α β)) (α_disc : Society α β → Set S) (α_pt : α → S) : Prop where
  /-- `(i)` `α(A, Ω)` is a closed disc in `Σ` and `α(x) ∈ bd(α(A, Ω))` for `x ∈ ΩBar`. -/
  isClosedDisc : ∀ S₀ ∈ S_seg, IsClosedDisc (α_disc S₀) ∧
    ∀ x ∈ S₀.Ω.bar, α_pt x ∈ subBd (α_disc S₀)
  /-- `(ii)` Intersection of two discs `α(S₁) ∩ α(S₂)` for `S₁ ≠ S₂`. -/
  inter_discs : ∀ S₁ ∈ S_seg, ∀ S₂ ∈ S_seg, S₁ ≠ S₂ →
    α_disc S₁ ∩ α_disc S₂ ⊆ α_pt '' (S₁.Ω.bar ∩ S₂.Ω.bar)
  /-- `(ii)` Intersection with the surface boundary `bd(Σ)`. -/
  inter_bd : ∀ S₀ ∈ S_seg, α_disc S₀ ∩ bd S ⊆ α_pt '' S₀.Ω.bar
  /-- `(iii)` `α` is injective on `V(S_seg)`. -/
  injOn_pts : InjOn α_pt (segregationVertices S_seg)
  /-- `(iv)` `Ω` is mapped by `α` to a natural order of `α(ΩBar)` from `bd(α(A, Ω))`. -/
  natural_order : ∀ S₀ ∈ S_seg, IsNaturalOrderFrom α_pt S₀.Ω (subBd (α_disc S₀))

/-- "Now let $H$ be a subgraph of $G$, and let $H$ be a 2-cell drawing in $\Sigma$. Let $\alpha$
be an arrangement in $\Sigma$ of a segregation $\mathscr{S}$ of $G$. We say that $\alpha$ is
*compatible with $H$* if (i) $\alpha(v) = v$ for all $v \in V(H) \cap V(\mathscr{S})$, and
(ii) for each $(A, \Omega) \in \mathscr{S}$, $U(H) \cap bd(\alpha(A, \Omega)) = V(H) \cap
\overline{\Omega}$, and $H \cap \alpha(A, \Omega) = H \cap A$."
(Graph Minors XIV, Section 4, page 30). -/
structure IsCompatibleWith {α : Type v} {β : Type w} (G : Graph α β) (H : Drawing S)
    (η : SpanEmbedding H G) (S_seg : Set (Society α β))
    (α_disc : Society α β → Set S) (α_pt : α → S) : Prop where
  /-- `(i)` `α(η(v)) = v` for all `v ∈ V(H)` with `η(v) ∈ V(S_seg)`. -/
  pt_eq : ∀ v ∈ H.V, η.vMap v ∈ segregationVertices S_seg → α_pt (η.vMap v) = v
  /-- `(ii)` `U(H) ∩ bd(α(A, Ω)) = {v ∈ V(H) : η(v) ∈ ΩBar}`. -/
  bd_inter_eq : ∀ S₀ ∈ S_seg, H.U ∩ subBd (α_disc S₀) = {v ∈ H.V | η.vMap v ∈ S₀.Ω.bar}
  /-- `(ii)` `V(H ∩ α(A, Ω))` corresponds under `η` to `V(η(H) ∩ A)`. -/
  inter_V_iff : ∀ S₀ ∈ S_seg, ∀ v ∈ H.V, v ∈ α_disc S₀ ↔ η.vMap v ∈ V(S₀.G)
  /-- `(ii)` An edge of `H` is included in `α(A, Ω)` if and only if its image under `η` belongs to
  `E(A)`. -/
  inter_E_iff : ∀ S₀ ∈ S_seg, ∀ e ∈ H.E, e ⊆ α_disc S₀ ↔ η.eMap e ∈ E(S₀.G)

/-- "If $H$ is a subgraph of $G$ and $\mathscr{S}$ is a segregation of $G$, and $\mathscr{T}$ is
a tangle in $H$, we say that $\mathscr{S}$ is *$\mathscr{T}$-local* if $(A \cap H, B \cap H)
\in \mathscr{T}$ for all $(A, \Omega) \in \mathscr{S}$, where $B$ is the unique subgraph of
$G$ such that $(A, B)$ is a separation of $G$ and $V(A \cap B) = \overline{\Omega}$"
(Graph Minors XIV, Section 4, page 30). -/
def IsTangleLocal {α : Type v} {β : Type w} (G : Graph α β) (H : Drawing S)
    (η : SpanEmbedding H G)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (S_seg : Set (Society α β)) : Prop :=
  ∀ S₀ ∈ S_seg, ∀ B : Graph α β,
    IsGraphSeparation G S₀.G B → V(S₀.G) ∩ V(B) = S₀.Ω.bar →
    ∃ A_H B_H : Hypergraph S (Set S),
      H.toHypergraph.IsSeparation A_H B_H ∧
      A_H.vertexSet = {v ∈ H.V | η.vMap v ∈ V(S₀.G)} ∧
      B_H.vertexSet = {v ∈ H.V | η.vMap v ∈ V(B)} ∧
      A_H.edgeSet = {e ∈ H.E | η.eMap e ∈ E(S₀.G)} ∧
      B_H.edgeSet = {e ∈ H.E | η.eMap e ∈ E(B)} ∧
      (A_H, B_H) ∈ T

/-- "A bridge of $H$ in $G$ is a subgraph of $G$, consisting of either an edge of $G$ not in
$E(H)$ but with both ends in $V(H)$, or a component of $G \setminus V(H)$ and all edges
between it and $V(H)$ (and their ends)" (Graph Minors XIV, Section 4, page 30). -/
def IsBridge {α : Type v} {β : Type w} (G H J : Graph α β) : Prop :=
  H ≤ G ∧ J ≤ G ∧
    ((∃ e ∈ E(G) \ E(H), ∃ u ∈ V(H), ∃ v ∈ V(H),
        G.IsLink e u v ∧ V(J) = {u, v} ∧ E(J) = {e}) ∨
      (∃ C ∈ graphComponents (deleteVertices G V(H)),
        V(J) = V(C) ∪ {v ∈ V(H) | ∃ e ∈ E(G), ∃ u ∈ V(C), G.IsLink e u v} ∧
        E(J) = E(C) ∪ {e ∈ E(G) | ∃ u ∈ V(C), ∃ v ∈ V(H), G.IsLink e u v}))

/-! ## Section 5: Distance in a Drawing (pages 31–32) -/

/-- "A set $\mathscr{R}$ of regions of a drawing $H$ is *connected* if for all $r, r' \in
\mathscr{R}$ there is a sequence $r = r_1, r_2, \dots, r_k = r'$ of members of $\mathscr{R}$ such
that for $1 \le i < k$, there is an edge of $H$ incident with $r_i$ and with $r_{i+1}$."
(Graph Minors XIV, Section 5, page 31). -/
def IsConnectedRegionSet (H : Drawing S) (R_set : Set (Set S)) : Prop :=
  R_set ⊆ H.R ∧
    ∀ r ∈ R_set, ∀ r' ∈ R_set,
      Relation.ReflTransGen
        (fun r₁ r₂ => r₁ ∈ R_set ∧ r₂ ∈ R_set ∧
          ∃ e ∈ H.E, H.EdgeRegionIncident e r₁ ∧ H.EdgeRegionIncident e r₂) r r'

/-- "If $H$ is a drawing in $\Sigma$, a *chain* is a sequence $v_0, r_1, \dots, r_k, v_k$ such
that $r_1, \dots, r_k$ are regions of $H$ and for $1 \le i \le k$, $\{v_{i-1}, v_i\}
\subseteq \bar{r}_i$. (We do not insist that $v_0, \dots, v_k$ are vertices.) The chain has
*length* $k$, and $v_0, v_k$ are its *ends"
(Graph Minors XIV, Section 5, page 32). -/
def IsRegionChain (H : Drawing S) (X Y : Set S) {k : ℕ} (v_seq : Fin (k + 1) → S)
    (r_seq : Fin k → Set S) : Prop :=
  v_seq 0 ∈ X ∧ v_seq (Fin.last k) ∈ Y ∧
    ∀ i : Fin k, r_seq i ∈ H.R ∧
      v_seq i.castSucc ∈ closure (r_seq i) ∧
      v_seq i.succ ∈ closure (r_seq i)

/-- "If $X, Y \subseteq \Sigma$ are non-empty, we define the *regional distance* between $X$ and
$Y$ to be the minimum length of a chain with one end in $X$ and the other in $Y$"
(Graph Minors XIV, Section 5, page 32). -/
noncomputable def regionalDistance (H : Drawing S) (X Y : Set S) : ℕ :=
  sInf {k : ℕ | ∃ (v_seq : Fin (k + 1) → S) (r_seq : Fin k → Set S),
    IsRegionChain H X Y v_seq r_seq}

/-! ## Section 6: Simply-Connected Subsets (pages 33–35) -/

/-- "A subset $X \subseteq \Sigma$ is *simply-connected* if $X$ is arc-wise connected and every
O-arc $F \subseteq X$ bounds a closed disc $\Delta \subseteq X$."
(Graph Minors XIV, Section 6, page 33). -/
def IsArcSimplyConnected (X : Set S) : Prop :=
  IsArcConnected X ∧ ∀ F : Set S, IsOArc F → F ⊆ X → ∃ Δ : Set S, IsClosedDisc Δ ∧ subBd Δ = F
    ∧ Δ ⊆ X

/-- "Two drawings are *isomorphic* if they are isomorphic as graphs"
(Graph Minors XIV, Section 6, page 34). -/
def AreIsomorphicDrawings (H₁ H₂ : Drawing S) : Prop :=
  Nonempty (Iso H₁.toGraph H₂.toGraph)

/-! ## Section 7: Modifying an Arrangement (pages 37–39) -/

/-- "If $\alpha$ is an arrangement in a surface $\Sigma$ of a segregation $\mathscr{S}$ of $G$, a
subset $X \subseteq \Sigma$ is said to be $\alpha$-normal if
$$X \cap \alpha(A, \Omega) \subseteq \{\alpha(v) : v \in \bar{\Omega}\}$$
for all $(A, \Omega) \in \mathscr{S}$."
(Graph Minors XIV, Section 7, page 37). -/
def IsArrangementNormal {α : Type v} {β : Type w} (S_seg : Set (Society α β))
    (α_disc : Society α β → Set S) (α_pt : α → S) (X : Set S) : Prop :=
  ∀ S₀ ∈ S_seg, X ∩ α_disc S₀ ⊆ α_pt '' S₀.Ω.bar

/-! ## Section 8: Segregation in a Cylinder (pages 39–45) -/

/-- Given an arrangement `α` of `S_seg` in `Σ` and an `α`-normal `O`-arc `F ⊆ Σ` with a cyclic order
on `F`, `Ω` is the pullback cyclic permutation `α⁻¹(F)` on `{v ∈ V(S_seg) : α(v) ∈ F}`
(Graph Minors XIV, Section 8, page 39). -/
def IsPullbackPerm {α : Type v} {β : Type w} (S_seg : Set (Society α β))
    (α_pt : α → S) (F : Set S) (Ω : CyclicPerm α) : Prop :=
  Ω.bar = {v ∈ segregationVertices S_seg | α_pt v ∈ F} ∧ IsNaturalOrderFrom α_pt Ω F

/-- "Let $(H, \Omega_1, \Omega_2)$ be a rural neighbourhood, in a closed cylinder $\Sigma$ with
ends $F_1, F_2$. It has *breadth* $\ge q$ if there are $q$ circuits of $H$, mutually
disjoint, and each winding around $\Sigma$, in the natural sense" (Graph Minors XIV, Section 8, page
40). -/
def HasCylinderBreadthGe {α : Type v} {β : Type w}
    (N : Neighborhood α β) (q : ℕ) : Prop :=
  N.HasBreadthGe q

/-! ## Section 9: Battlefields (pages 45–47) -/

/-- The normalized battlefield of size `β` used in XVI (8.1) has `|X| = β`. The original
definition in XIV allows a larger free set. See `GM16.IsBattlefieldData.normalize` for the
reduction to the normalized form. The printed definition reads:
"Let $H$ be a 2-cell drawing in $\Sigma$, let $z \in A(H)$, and let $\mathscr{T}$ be a
respectful tangle in $H$ of order $\theta$, with metric $d$. Let $\beta \ge 4$ be an even integer.
A triple $(\Lambda, C, X)$ is a *battlefield of size $\beta$ around $z$* if
(i) $\Lambda$ is a $(3\beta + 3)$-zone around $z$, and $H \cap (\Sigma - \Lambda)$ is a rigid
drawing in $\Sigma$
(ii) $X \subseteq V(H) \cap bd(\Lambda)$, and $\theta \ge 12\beta + 15$, and $X$ is free with
respect to the tangle of order $\theta - 4(3\beta + 3) - 2$ obtained by clearing $\Lambda$,
(iii) $C$ is a circuit of $H$ with $U(C) \subseteq \Lambda$, and there are $\beta$ disjoint paths
of $H$ from $U(C)$ to $X$, each with no vertex in $H \cap bd(\Lambda)$ except its last,
(iv) the regional distance between $U(C)$ and $bd(\Lambda)$ is at least $1 + \frac{1}{2}\beta$,
(v) the open disc in $\Lambda$ bounded by $U(C)$ includes every $x \in A(K)$ with $d(z, x) <
\beta$."
(Graph Minors XIV, Section 9, page 45; in `(v)` the paper writes `A(K)` for `A(H)`). -/
structure IsBattlefield (H : Drawing S)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (θ beta : ℕ) (z : Set S)
    (Λ : Set S) (C : Drawing S) (X : Set S) : Prop where
  /-- `β ≥ 4` is even, `θ ≥ 12β + 15`, and `z ∈ A(H)`. -/
  params_valid : 4 ≤ beta ∧ Even beta ∧ 12 * beta + 15 ≤ θ ∧ z ∈ H.A
  /-- `(i)` `Λ` is a `(3β + 3)`-zone around `z`. -/
  isZone : IsLambdaZoneAround H d (3 * beta + 3) z Λ
  /-- `(i)` `H ∩ (Σ - Λ)` is rigid. -/
  isRigid_cleared : IsRigid (clearedSubdrawing H Λ)
  /-- `(ii)` `X ⊆ V(H) ∩ bd(Λ)` with `|X| = β`, and `X` is free with respect to the tangle of order
  `θ - 4(3β + 3) - 2` obtained by clearing `Λ`. -/
  isFree_X : X ⊆ H.V ∩ subBd Λ ∧ X.ncard = beta ∧
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S → Set S → ℕ),
      IsClearedTangle H T d θ (3 * beta + 3) Λ T' d' ∧
      IsFreeSet (clearedSubdrawing H Λ).toHypergraph T' (θ - 4 * (3 * beta + 3) - 2) X
  /-- `(iii)` `C` is a circuit of `H` with `U(C) ⊆ Λ`, and there are `β` mutually disjoint paths of
  `H` from `V(C)` to `X`, each intersecting `H ∩ bd(Λ)` only in its last vertex. -/
  circuit_and_paths :
    C.IsCircuit ∧ C.IsSubdrawing H ∧ C.U ⊆ Λ ∧
    ∃ P : Fin beta → Drawing S,
      (∀ k : Fin beta, ∃ u ∈ C.V, ∃ v ∈ X,
        (P k).IsPathBetween u v ∧ (P k).IsSubdrawing H ∧
        (P k).U ∩ (H.U ∩ subBd Λ) = {v}) ∧
      Pairwise (fun k₁ k₂ : Fin beta => Disjoint (P k₁).V (P k₂).V)
  /-- `(iv)` The regional distance between `U(C)` and `bd(Λ)` is at least `1 + β / 2`. -/
  regionalDistance_ge : 1 + beta / 2 ≤ regionalDistance H C.U (subBd Λ)
  /-- `(v)` The open disc in `Λ` bounded by `U(C)` includes every `x ∈ A(H)` with `d(z, x) < β`. -/
  openDisc_includes : ∃ Δ₀ : Set S,
    IsOpenDisc Δ₀ ∧ Δ₀ ⊆ Λ ∧ subBd Δ₀ = C.U ∧
    ∀ x ∈ H.A, d z x < beta → x ⊆ Δ₀

/-- "We define $\alpha^{-1}(\Sigma')$ to be the subgraph of $G$ formed by $$ \bigcup (A : (A,
\Omega) \in \mathscr{S} \text{ and } \alpha(A, \Omega) \subseteq \Sigma') $$ together with
all $v \in V(\mathscr{S})$ such that $\alpha(v) \in \Sigma'$"
(Graph Minors XIV, Section 9, page 47). -/
def arrangementPullbackGraph {α : Type v} {β : Type w} (G : Graph α β) (S_seg : Set (Society α β))
    (α_disc : Society α β → Set S) (α_pt : α → S) (S' : Set S) : Graph α β :=
  (G.induce (((⋃ S₀ ∈ {S₀ ∈ S_seg | α_disc S₀ ⊆ S'}, V(S₀.G)) ∪
    {v ∈ segregationVertices S_seg | α_pt v ∈ S'}) ∩ V(G))).restrict
    (⋃ S₀ ∈ {S₀ ∈ S_seg | α_disc S₀ ⊆ S'}, E(S₀.G))

end SurfaceDefs

end GraphMinor.GM14
