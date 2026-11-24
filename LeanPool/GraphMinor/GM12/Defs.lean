/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs

/-!
# Definitions of Graph Minors XII

This file formalizes the definitions of N. Robertson and P. D. Seymour, *Graph Minors. XII. Distance
on a surface*, J. Combin. Theory Ser. B 64 (1995) 240–272. Everything is stated over the actual
drawings of `GraphMinor/Surface/Defs.lean`.

Graph Minors XIV restates the definitions of Section 1 of this paper, and the project keeps one copy
of them, in `GraphMinor/GM14/Defs.lean`. We use those directly:

- A respectful tangle is `GM14.IsRespectfulDrawingTangle`, or its parts `GM10.IsTangle` and
  `GM11.PaintingOrDrawing.IsRespectful` for a drawing that need not be 2-cell, as in Section 5.
- The metric of a respectful tangle is `GM14.HasTangleMetric`, built from `GM14.tangleMetric`, which
  is `d(a(c₁), a(c₂))` of the paper. The paper's distance is half the length of a closed walk of a
  bipartite drawing, and so it is an integer.
- The radial drawing is `GM11.PaintingOrDrawing.IsRadialDrawing`, the definition of Graph Minors XI.
  This paper replaces the last two conditions of that definition by: "for every $v \in V(\Gamma)$,
  the edges
  of $K \cup \Gamma$ incident with $v$ belong alternately to $\Gamma$ and to $K$ (in their cyclic
  order around
  $v$)". When `E(Γ) ≠ ∅` both say that each corner of `Γ` at `v` holds exactly one edge of `K`.
- Free sets are `GM10.IsFreeSet`.

This file adds the rest:

- **Section 2:** the length of a closed curve (`curveLength`) and its traces (`IsTrace`).
- **Section 3:** the statement (*) (`HasConnectingSubdrawings`) and the feasibility condition
  (`IsTopologicallyFeasible`).
- **Section 4:** the tangle in `G` induced by a tangle in a subgraph (`inducedBySubgraph`) and
  control
  of a minor (`ControlsMinor`).
- **Section 5:** the cut of a surface along `O`-arcs and its capped side (`IsCappedSplit`), handles
  and crosscaps (`IsHandleSplit`, `IsCrosscapSplit`), `Γ ∩ Σ̂₁` (`IsCappedDrawing`), and the tangle
  induced across the cut (`inducedAcross`).
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 Hypergraph

universe u v

section Main

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-! ## Section 2 -/

/-- The closed curve `φ : S¹ → Σ` as a function of the real parameter `t`, with period `1`. -/
noncomputable def periodicCurve (φ : C(Circle, S)) : ℝ → S :=
  fun t => φ (Circle.exp (2 * Real.pi * t))

/-- The *length* of `φ` with respect to `Γ` (Graph Minors XII, Section 2, page 243): "If $\{x \in
S^1 \colon \phi(x) \in U(\Gamma)\}$ is finite, we call its cardinality the
*length* of $\phi$" -/
noncomputable def curveLength (Γ : Drawing S) (φ : C(Circle, S)) : ℕ :=
  {x | φ x ∈ Γ.U}.ncard

/-- `φ` has finite length, with `|φ|` `Γ`-normal: the setting of the definition of a trace (Graph
Minors XII, Section 2, page 243). -/
def IsNormalCurve (Γ : Drawing S) (φ : C(Circle, S)) : Prop :=
  {x | φ x ∈ Γ.U}.Finite ∧ Γ.IsNormal (range φ)

/-- The curve `ξ` follows `f` on `[h, c]` for its first part, and then traces the edge `e` of `K` to
`w`. This is `φ_e` of the definition of a trace (Graph Minors XII, Section 2, page 243): "the
restriction of $\phi$ to the portion of $I_{i-1}$ between $h$ and $x_i$, concatenated
with a curve tracing $e$ from $v_{2i}$ to $v_{2i-1}$". -/
def IsEntryCurve (f : ℝ → S) (h c : ℝ) (e : Set S) (w : S) (ξ : Curve S) : Prop :=
  ∃ s : unitInterval, 0 < s ∧ s < 1 ∧
    (∀ t : unitInterval, t ≤ s → ξ t = f (h + t.1 / s.1 * (c - h))) ∧
    InjOn ξ (Ioo s 1) ∧ ξ '' Ioo s 1 = e ∧ ξ 1 = w

/-- The edge `e`, from the vertex `v` to the point `w` of the region `r`, *enters `v` in the same
way
as* `f` on `(a, c)`, with `f(c) = v` (Graph Minors XII, Section 2, page 243, (iii)): "choose $h \in
I_{i-1}$ ... $\phi_e$ is homotopic in $r_{2i-1} \cup \{v_{2i}\}$ to a curve in
$r_{2i-1}$". The paper
says that the choice of `h` does not matter. -/
def EntersLike (f : ℝ → S) (a c : ℝ) (e r : Set S) (v w : S) : Prop :=
  ∃ h ∈ Ioo a c, ∃ ξ ρ : Curve S, IsEntryCurve f h c e w ξ ∧ range ρ ⊆ r ∧
    CurvesHomotopicIn (r ∪ {v}) ξ ρ

/-- The edge `e` *leaves `v` in the same way as* `f` on `(a, c)`, with `f(a) = v` (Graph Minors XII,
Section 2, page 243, (iv)): this is (iii) for the curve run backwards. -/
def LeavesLike (f : ℝ → S) (a c : ℝ) (e r : Set S) (v w : S) : Prop :=
  EntersLike (fun t => f (-t)) (-c) (-a) e r v w

/-- The closed walk from `u` to `v` of `K` follows `f` from `a` to `b`, in steps of two edges: each
step of the walk goes from a vertex of `Γ` at parameter `a` through the vertex `w` of `K` in a
region
`r` of `Γ` to a vertex of `Γ` at parameter `c`, where `f` maps `(a, c)` into `r`. -/
def TraceSteps (Γ K : Drawing S) (f : ℝ → S) : (a b : ℝ) → {u v : S} →
    GraphWalk K.toGraph u v → Prop
  | a, b, u, _, .nil _ => a = b ∧ f a = u ∧ u ∈ Γ.V
  | _, _, _, _, .cons _ (.nil _) => False
  | a, b, u, _, .cons (e := e) (v := w) _ (.cons (e := e') (v := x) _ rest) =>
      ∃ c, a < c ∧ f a = u ∧ u ∈ Γ.V ∧ f c = x ∧ w ∈ K.V ∧ ∃ r ∈ Γ.R, w ∈ r ∧
        (∀ t ∈ Ioo a c, f t ∈ r) ∧ LeavesLike f a c e r u w ∧ EntersLike f a c e' r x w ∧
        TraceSteps Γ K f c b rest

/-- `W` is a *trace* of `φ` in `K` (Graph Minors XII, Section 2, page 243). Here `φ` has finite
length and `|φ|` is `Γ`-normal. If `φ` has length `0`, "its only trace is the zero-edge walk with
one vertex $v$, where $v \in V(K)$ is the vertex
of $K$ in the region of $\Gamma$ including $|\phi|$". If `φ` has
length `n > 0`, then `W` has `2n` edges, and is built from the points `x₁, …, x_n` of `S¹` that `φ`
maps to `V(Γ)`, in their order on the circle, as in `TraceSteps`. In the paper, (ii) reads "the
region of $\Gamma$ including $\{\phi(x) \colon x \in I_i", but `I_i` lies between `x_i` and
`x_{i+1}` and (iii) uses
`I_{i-1}` for the same region, so (ii) must be read with `I_{i-1}`, and this is what we state. -/
def IsTrace (Γ K : Drawing S) (φ : C(Circle, S)) {u : S} (W : GraphWalk K.toGraph u u) : Prop :=
  IsNormalCurve Γ φ ∧
    ((curveLength Γ φ = 0 ∧ W.length = 0 ∧ u ∈ K.V ∧ ∃ r ∈ Γ.R, range φ ⊆ r ∧ u ∈ r) ∨
      (0 < curveLength Γ φ ∧ W.length = 2 * curveLength Γ φ ∧
        ∃ a, TraceSteps Γ K (periodicCurve φ) a (a + 1) W))

/-! ## Section 3 -/

/-- A subdrawing is *connected*: any two of its vertices are joined by a walk. -/
def IsConnectedDrawing (H : Drawing S) : Prop :=
  ∀ a ∈ H.V, ∀ b ∈ H.V, Nonempty (GraphWalk H.toGraph a b)

/-- The statement (*) (Graph Minors XII, Section 3, page 245): "There are mutually disjoint,
connected subdrawings $H_1, \dots, H_p$ of $\Gamma$ with
$V(H_j) \cap Z = Z_j$ $(1 \le j \le p)$." -/
def HasConnectingSubdrawings (Γ : Drawing S) {p : ℕ} (Z : Set S) (Zs : Fin p → Set S) : Prop :=
  ∃ H : Fin p → Drawing S, (∀ j, (H j).IsSubdrawing Γ) ∧ (∀ j, IsConnectedDrawing (H j)) ∧
    (∀ i j, i ≠ j → Disjoint (H i).V (H j).V) ∧ ∀ j, (H j).V ∩ Z = Zs j

/-- The *topological feasibility condition* (Graph Minors XII, Section 3, page 245): "There exist
mutually disjoint closed discs $D_1, \dots, D_p \subseteq \Sigma$ such that
$$D_j \cap (\Delta_1 \cup \dots \cup \Delta_t) = Z_j \quad (1 \le j \le p).$$" -/
def IsTopologicallyFeasible {t p : ℕ} (Δ : Fin t → Set S) (Zs : Fin p → Set S) : Prop :=
  ∃ D : Fin p → Set S, (∀ j, IsClosedDisc (D j)) ∧ (∀ i j, i ≠ j → Disjoint (D i) (D j)) ∧
    ∀ j, D j ∩ ⋃ i, Δ i = Zs j

/-! ## Section 5 -/

/-- The closed annulus `1 ≤ x² + y² ≤ 2` of the definition of a handle. -/
def ClosedAnnulus : Set EuclideanPlane :=
  {p | 1 ≤ p 0 ^ 2 + p 1 ^ 2 ∧ p 0 ^ 2 + p 1 ^ 2 ≤ 2}

/-- The Möbius band: the square `[0, 1] × [0, 1]` with `(0, y)` glued to `(1, 1 - y)`. -/
def mobiusSetoid : Setoid (unitInterval × unitInterval) :=
  Relation.EqvGen.setoid fun p q => p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2

/-- The data of (5.3) (Graph Minors XII, Section 5, pages 254–255):
"Let $\Sigma$ be a connected surface, and let $C_1, \dots, C_t$ be mutually disjoint $O$-arcs in
$\Sigma$. Let $\Sigma_1, \Sigma_2$ be 2-manifolds with boundary, such that
$\Sigma_1 \cup \Sigma_2 = \Sigma$ and
$$\Sigma_1 \cap \Sigma_2 = bd(\Sigma_1) = bd(\Sigma_2) = C_1 \cup \dots \cup C_t.$$
Let $\hat{\Sigma}_1$ be a surface with $\Sigma_1 \subseteq \hat{\Sigma}_1$, such that each $C_i$
bounds an open disc $D_i \subseteq \hat{\Sigma}_1$, and $D_1, \dots, D_t$ are mutually disjoint,
and $\hat{\Sigma}_1 - \Sigma_1 = D_1 \cup \dots \cup D_t$." The surface `Σ̂₁` is another space `T`,
and `ι` is the inclusion `Σ₁ ⊆ Σ̂₁`, a topological embedding. -/
structure IsCappedSplit {T : Type v} [TopologicalSpace T] {t : ℕ} (C : Fin t → Set S)
    (P₁ P₂ : Set S) (ι : P₁ → T) (D : Fin t → Set T) : Prop where
  /-- `Σ` is a connected surface. -/
  surface : IsClosedSurface S ∧ ConnectedSpace S
  /-- Each `C_i` is an `O`-arc. -/
  isOArc : ∀ i, IsOArc (C i)
  /-- The `C_i` are mutually disjoint. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j)
  /-- `Σ₁` is a 2-manifold with boundary. -/
  manifold₁ : IsSurface P₁
  /-- `Σ₂` is a 2-manifold with boundary. -/
  manifold₂ : IsSurface P₂
  /-- `Σ₁ ∪ Σ₂ = Σ`. -/
  union : P₁ ∪ P₂ = univ
  /-- `Σ₁ ∩ Σ₂ = C₁ ∪ ⋯ ∪ C_t`. -/
  inter : P₁ ∩ P₂ = ⋃ i, C i
  /-- `bd(Σ₁) = C₁ ∪ ⋯ ∪ C_t`. -/
  bd₁ : (↑) '' bd P₁ = ⋃ i, C i
  /-- `bd(Σ₂) = C₁ ∪ ⋯ ∪ C_t`. -/
  bd₂ : (↑) '' bd P₂ = ⋃ i, C i
  /-- `Σ̂₁` is a surface. -/
  surface_hat : IsClosedSurface T
  /-- The inclusion `Σ₁ ⊆ Σ̂₁`. -/
  isEmbedding : IsEmbedding ι
  /-- Each `D_i` is an open disc. -/
  isOpenDisc : ∀ i, IsOpenDisc (D i)
  /-- Each `C_i` bounds `D_i`. -/
  bounds : ∀ i, subBd (D i) = ι '' ((↑) ⁻¹' C i)
  /-- The `D_i` are mutually disjoint. -/
  disjoint_D : ∀ i j, i ≠ j → Disjoint (D i) (D j)
  /-- `Σ̂₁ − Σ₁ = D₁ ∪ ⋯ ∪ D_t`. -/
  compl : (range ι)ᶜ = ⋃ i, D i

/-- `Σ₂` is a *handle* of `Σ` (Graph Minors XII, Section 5, page 254):
"If $t = 2$, $\hat{\Sigma}_1$ is connected, and $\Sigma_2$ is homeomorphic to
$\{(x, y) \colon 1 \le x^2 + y^2 \le 2\}$ we say $\Sigma_2$ is a handle of $\Sigma$." -/
def IsHandleSplit {T : Type v} [TopologicalSpace T] (C : Fin 2 → Set S) (P₁ P₂ : Set S)
    (ι : P₁ → T) (D : Fin 2 → Set T) : Prop :=
  IsCappedSplit C P₁ P₂ ι D ∧ ConnectedSpace T ∧ Nonempty (P₂ ≃ₜ ClosedAnnulus)

/-- `Σ₂` is a *crosscap* of `Σ` (Graph Minors XII, Section 5, page 254):
"if $t = 1$, $\hat{\Sigma}_1$ is connected, and $\Sigma_2$ is homeomorphic to a Möbius band, we say
that $\Sigma_2$ is a crosscap of $\Sigma$." -/
def IsCrosscapSplit {T : Type v} [TopologicalSpace T] (C : Fin 1 → Set S) (P₁ P₂ : Set S)
    (ι : P₁ → T) (D : Fin 1 → Set T) : Prop :=
  IsCappedSplit C P₁ P₂ ι D ∧ ConnectedSpace T ∧ Nonempty (P₂ ≃ₜ Quotient mobiusSetoid)

/-- `Γ₁` is `Γ ∩ Σ̂₁` (Graph Minors XII, Section 5, page 255), a drawing in `Σ̂₁`: its point set and
vertex set are those of `Γ` in `Σ₁`, moved by the inclusion `ι`. -/
def IsCappedDrawing {T : Type v} [TopologicalSpace T] {P₁ : Set S} (ι : P₁ → T) (Γ : Drawing S)
    (Γ₁ : Drawing T) : Prop :=
  Γ₁.U = ι '' ((↑) ⁻¹' Γ.U) ∧ Γ₁.V = ι '' ((↑) ⁻¹' Γ.V)

/-- The tangle in `Γ` induced by a tangle `𝒯₁` in `Γ ∩ Σ̂₁` (Graph Minors XII, Section 5, pages
253–255; the definition is on page 248): the separations `(A, B)` of `Γ` of order `< θ` such that
`(A ∩ Γ₁, B ∩ Γ₁) ∈ 𝒯₁`. The drawing `Γ₁` lives in another space, so `A ∩ Γ₁` is compared with a
member of
`𝒯₁` through the inclusion `ι`: same vertices and same edges of `Γ₁`, moved by `ι`. -/
def inducedAcross {T : Type v} [TopologicalSpace T] {P₁ : Set S} (ι : P₁ → T) (Γ : Drawing S)
    (Γ₁ : Drawing T) (θ : ℕ) (𝒯₁ : Set (Hypergraph T (Set T) × Hypergraph T (Set T))) :
    Set (Hypergraph S (Set S) × Hypergraph S (Set S)) :=
  {p | Γ.toHypergraph.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧
    ∃ q ∈ 𝒯₁,
      q.1.vertexSet = ι '' ((↑) ⁻¹' p.1.vertexSet) ∧ q.2.vertexSet = ι '' ((↑) ⁻¹' p.2.vertexSet) ∧
      (∀ e ∈ Γ₁.E, e ∈ q.1.edgeSet ↔ ∃ f ∈ p.1.edgeSet, e = ι '' ((↑) ⁻¹' f)) ∧
      (∀ e ∈ Γ₁.E, e ∈ q.2.edgeSet ↔ ∃ f ∈ p.2.edgeSet, e = ι '' ((↑) ⁻¹' f))}

end Main

/-! ## Section 4 -/

/-- The tangle in `G` *induced* by a tangle `𝒯'` in a subgraph `G'` (Graph Minors XII, Section 4,
page 248): "Let $\mathscr{T}$ be the set of all separations $(A, B)$ of $G$ of order $< \theta$ such
that $(A \cap G', B \cap G') \in \mathscr{T}'$." -/
def inducedBySubgraph {α β : Type*} (G G' : Hypergraph α β) (θ : ℕ)
    (𝒯' : Set (Hypergraph α β × Hypergraph α β)) : Set (Hypergraph α β × Hypergraph α β) :=
  {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧ (p.1 ∩ G', p.2 ∩ G') ∈ 𝒯'}

/-- A subhypergraph is *connected*: any two of its vertices are joined in its skeleton. -/
def IsConnectedSub {α β : Type*} (H : Hypergraph α β) : Prop :=
  ∀ a ∈ H.vertexSet, ∀ b ∈ H.vertexSet, H.skeleton.Reachable a b

/-- `𝒯` *controls an `L` minor* of `G` (Graph Minors XII, Section 4, page 249): there is a function
`α` with domain `V(L) ∪ E(L)` such that
"(i) for each $v \in V(L)$, $\alpha(v)$ is a non-null connected subgraph of $G$, and
$\alpha(u), \alpha(v)$ are disjoint for all distinct $u, v \in V(L)$ (ii) for each $e \in
E(L)$ with distinct ends $u, v$, $\alpha(e)$ is an edge of $G$ with ends in $V(\alpha(u))$
and in $V(\alpha(v))$ (iii) for each loop $e \in E(L)$ with end $v$, $\alpha(e)$ is an edge
of $G$ not in $E(\alpha(v))$ with both ends in $V(\alpha(v))$ (iv) for distinct $e, f \in
E(L)$, $\alpha(e) \ne \alpha(f)$ (v) $\mathscr{T}$ has order $\ge |V(L)|$, and there is no
$(A, B) \in \mathscr{T}$ of order $< |V(L)|$ such that $V(\alpha(v)) \subseteq V(A)$ for
some $v \in V(L)$." -/
def ControlsMinor {α β γ δ : Type*} (G : Hypergraph α β) (θ : ℕ)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (L : Graph γ δ) : Prop :=
  ∃ (a : γ → Hypergraph α β) (b : δ → β),
    (∀ v ∈ L.vertexSet, (a v).IsSubhypergraph G ∧ (a v).vertexSet.Nonempty ∧ IsConnectedSub (a v)) ∧
    (∀ u ∈ L.vertexSet, ∀ v ∈ L.vertexSet, u ≠ v → Disjoint (a u).vertexSet (a v).vertexSet) ∧
    (∀ e u v, L.IsLink e u v → u ≠ v → b e ∈ G.edgeSet ∧
      (∃ x ∈ (a u).vertexSet, G.Inc (b e) x) ∧ ∃ y ∈ (a v).vertexSet, G.Inc (b e) y) ∧
    (∀ e v, L.IsLink e v v → b e ∈ G.edgeSet ∧ b e ∉ (a v).edgeSet ∧
      ∀ x, G.Inc (b e) x → x ∈ (a v).vertexSet) ∧
    (∀ e ∈ L.edgeSet, ∀ f ∈ L.edgeSet, e ≠ f → b e ≠ b f) ∧
    L.vertexSet.ncard ≤ θ ∧
    ∀ A B : Hypergraph α β, (A, B) ∈ 𝒯 → separationOrder A B < L.vertexSet.ncard →
      ∀ v ∈ L.vertexSet, ¬ (a v).vertexSet ⊆ A.vertexSet

/-- The points of the list `l` occur in this order on the circle `F`, going once around it. This is
what the papers mean by "numbered in order on `F`" (Graph Minors XII, Section 6, page 257). It also
says what an opposite pair is in (5.2), page 254: on a list of `2θ` points in order, the `i`-th
point and
the `(i + θ)`-th point. -/
def IsListedInOrderOn {X : Type*} [TopologicalSpace X] (F : Set X) (l : List X) : Prop :=
  ∃ (f : Circle ≃ₜ F) (t : ℕ → ℝ), StrictMono t ∧ (∀ i < l.length, t i < t 0 + 2 * Real.pi) ∧
    ∀ (i : ℕ) (h : i < l.length), ((f (Circle.exp (t i)) : F) : X) = l[i]

end GraphMinor.GM12
