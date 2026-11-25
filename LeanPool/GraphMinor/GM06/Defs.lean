/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Circle
public import LeanPool.GraphMinor.Surface.Disc
public import LeanPool.GraphMinor.Surface.Cylinder

/-!
# Definitions and Statements for Graph Minors VI (Disjoint Paths across a Disc)

This file formalizes the definitions and the statements of the numbered results of
N. Robertson and P. D. Seymour, *Graph Minors. VI. Disjoint paths across a disc*,
J. Combin. Theory Ser. B **41** (1986), 115–138, Sections 1–5:

- **Section 1 (pages 115–116):**
  - Divisions (`IsDivision`, `divisionUnion`), connected graphs (`IsGraphConnected`), connected
    components of graphs (`IsGraphComponent`, `graphComponents`), realizations of a division in a
    graph (`IsRealization`), feasibility of a division (`IsFeasible`), and vertex valency
    (`vertexValency`).
- **Section 2 (pages 116–119):**
  - Segments of a circle with respect to a finite vertex set (`IsSegmentOf`, `segmentsOf`), dual
    point sets $U$ (`IsDualPointSet`), crossing pairs on a circle (`CrossesOn`), the dual and
    double-dual divisions $\Delta^*$ and $\Delta^{**}$ (`dualEquivRel`, `dualDivision`,
    `doubleDualDivision`), cross-free divisions (`IsCrossFree`), the counting function
    $\Delta(x, y)$ (`divisionCount`), $\Delta$-minimizers and $\Delta^*$-maximizers, and the
    statements of (2.1)–(2.4).
- **Section 3 (pages 119–122):**
  - Closed disc spaces (`IsClosedDiscSpace`), dual drawings $G^*$ on a closed disc
    (`IsDiscDualDrawing`), peripheral vertices and regions (`ChainTerm`, `ChainTerm.IsPeripheral`),
    $(x, y)$-chains (`IsXYChain`), chain length (`chainLength`), $\Delta$-redundancy
    (`chainRedundancy`), and the statements of (3.1)–(3.3), (3.5), and (3.6).
- **Section 4 (pages 122–127):**
  - Path drawings (`IsPathDrawing`) and homotopy of paths (`PathsHomotopic`, `PathHomotopicToArc`),
    the routed forest containment problem (`HasHomotopicForestSubgraph`), the minimal boundary path
    $P(s, t, S)$ (`IsEnclosedDisc`, `IsMinimalBoundaryPath`), Reductions 1 and 2
    (`Section4Reduction1Applies`, `Section4Condition41Applies`, `Section4Reduction2Applies`),
    sub-arcs $S(a, b)$ (`cuffSubArc`), bad components (`IsBadComponent`), $C$-bases and
    interval-based components (`IsCuffBase`, `IsIntervalBasedOn`), and the statements of
    (4.1)–(4.3).
- **Section 5 (pages 127–135):**
  - Standard boundary vertex sets $M_1, M_2$ and dual boundary sets $N_1, N_2$ on `ClosedCylinder`
    (`cylinderM1Point`, `cylinderM2Point`, `cylinderM1`, `cylinderM2`, `cylinderN1Point`,
    `cylinderN2Point`, `cylinderN1`, `cylinderN2`), cylinder drawings (`IsCylinderSection5Drawing`),
    linkages $\mathcal{L}$ in $G$ (`CylinderLinkage`), feasible winding numbers $\theta$
    (`IsThetaFeasible`), strips $\Sigma_i$ and regions $R_i$ (`cylinderStrip`, `cylinderRegion`),
    graph separations (`IsGraphSeparation`), Section 5 Reductions 1–4 (`Section5ReductionStep`),
    $G$-normal curves (`IsNormalCurve`), vertex hit count $L_G(f)$ (`curveVertexHits`, `curveL`),
    helices (`IsHelix`), the potential $\phi_G(f) = \theta(f) + k^{-1} L_G(f)$ (`curvePhi`), and the
    statements of (5.1)–(5.6), (5.8)–(5.10), and (5.12).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Function Real Topology unitInterval Graph GraphMinor.Surface

universe u v w

/-! ## Section 1: Divisions, Realizations, Feasibility, and Valency (pages 115–116) -/

/-- A *division* is a finite set of non-empty pairwise disjoint sets.
Graph Minors VI, Section 1 (page 116): "A *division* is a finite set of non-empty pairwise disjoint
sets." -/
def IsDivision {α : Type u} (Δ : Set (Set α)) : Prop :=
  Δ.Finite ∧ (∀ δ ∈ Δ, δ.Nonempty) ∧ Δ.PairwiseDisjoint id

/-- For a division $\Delta$, $\bigcup \Delta$ denotes $\bigcup (\delta \in \Delta)$.
Graph Minors VI, Section 1 (page 116): "If $\Delta$ is a division, we abbreviate
$\bigcup (\delta \in \Delta)$ by $\bigcup \Delta$." -/
def divisionUnion {α : Type u} (Δ : Set (Set α)) : Set α :=
  ⋃₀ Δ

/-- A multigraph $G$ is *connected* if its vertex set is nonempty and any two vertices of $G$ are
joined by a walk in $G$.
Graph Minors VI, Section 1 (page 116). -/
def IsGraphConnected {α : Type u} {β : Type v} (G : Graph α β) : Prop :=
  V(G).Nonempty ∧ ∀ u ∈ V(G), ∀ v ∈ V(G), Nonempty (GraphWalk G u v)

/-- A subgraph $C$ of $G$ is a *connected component* of $G$ if $C$ is a maximal connected subgraph
of $G$.
Graph Minors VI, Section 1 (page 116). -/
def IsGraphComponent {α : Type u} {β : Type v} (C G : Graph α β) : Prop :=
  C ≤ G ∧ IsGraphConnected C ∧
    ∀ C' : Graph α β, C ≤ C' → C' ≤ G → IsGraphConnected C' → C' = C

/-- The set of connected components of a multigraph $G$. -/
def graphComponents {α : Type u} {β : Type v} (G : Graph α β) : Set (Graph α β) :=
  {C : Graph α β | IsGraphComponent C G}

/-- If $G$ is a graph and $\Delta$ is a division with $\bigcup \Delta \subseteq V(G)$, a
*realization* of $\Delta$ in $G$ is a subgraph $H$ of $G$ which is a forest with $|\Delta|$
components $H(\delta)$ ($\delta \in \Delta$) such that $\delta \subseteq V(H(\delta))$ for each
$\delta \in \Delta$.
Graph Minors VI, Section 1 (page 116): "If $G$ is a graph and $\Delta$ is a division with
$\bigcup \Delta \subseteq V(G)$, a *realization* of $\Delta$ in $G$ is a subgraph of $G$ which is a
forest with $|\Delta|$ components $H(\delta)$ ($\delta \in \Delta$) such that
$\delta \subseteq V(H(\delta))$ ($\delta \in \Delta$)." -/
def IsRealization {α : Type u} {β : Type v} (G : Graph α β) (Δ : Set (Set α))
    (H : Graph α β) : Prop :=
  IsDivision Δ ∧ divisionUnion Δ ⊆ V(G) ∧
  H ≤ G ∧ IsGraphForest H ∧
  ∃ H_comp : Set α → Graph α β,
    InjOn H_comp Δ ∧
    (∀ δ ∈ Δ, IsGraphComponent (H_comp δ) H ∧ δ ⊆ V(H_comp δ)) ∧
    graphComponents H = H_comp '' Δ

/-- A division $\Delta$ is *feasible* in $G$ if there is a realization of $\Delta$ in $G$.
Graph Minors VI, Section 1 (page 116): "We say that $\Delta$ is *feasible* in $G$ if there is a
realization of $\Delta$ in $G$." -/
def IsFeasible {α : Type u} {β : Type v} (G : Graph α β) (Δ : Set (Set α)) : Prop :=
  ∃ H : Graph α β, IsRealization G Δ H

/-- The *valency* of a vertex $v$ in a graph $G$ is the number of edges incident with $v$, counting
loops twice.
Graph Minors VI, Section 1 (page 116): "The *valency* of a vertex is the number of edges incident
with it; loops are counted twice." -/
noncomputable def vertexValency {α : Type u} {β : Type v} (G : Graph α β) (v : α) : ℕ :=
  {e ∈ E(G) | ∃ w ≠ v, G.IsLink e v w}.ncard + 2 * {e ∈ E(G) | G.IsLink e v v}.ncard

/-! ## Section 2: Divisions on a Circle (pages 116–119) -/

/-- A subset $S \subseteq C$ is a *segment* of $C$ with respect to $V$ if $S$ is a connected
component of $C \setminus V$ homeomorphic to the open interval $(0, 1)$.
Graph Minors VI, Section 2 (page 117): "Let $C$ be homeomorphic to a circle and let $V \subseteq C$
be finite. Every component of $C - V$ homeomorphic to $(0, 1)$ is called a *segment* (of $C$ with
respect to $V$)." -/
def IsSegmentOf {S : Type u} [TopologicalSpace S] (C V seg : Set S) : Prop :=
  seg ∈ componentsIn (C \ V) ∧ Nonempty (Ioo (0 : ℝ) 1 ≃ₜ seg)

/-- The set of all segments of $C$ with respect to $V$.
Graph Minors VI, Section 2 (page 117). -/
def segmentsOf {S : Type u} [TopologicalSpace S] (C V : Set S) : Set (Set S) :=
  {seg : Set S | IsSegmentOf C V seg}

/-- A subset $U \subseteq C \setminus V$ is a *dual point set* for $(C, V)$ if $U = \emptyset$ when
$V = \emptyset$, and when $V \ne \emptyset$, $U \subseteq C \setminus V$ with $|U \cap S| = 1$ for
every segment $S$ of $C$ with respect to $V$.
Graph Minors VI, Section 2 (page 117): "If $V = \emptyset$ let $U = \emptyset$. If
$V \ne \emptyset$ let $U \subseteq C - V$ with $|U \cap S| = 1$ for every segment $S$ of $C$ with
respect to $V$." -/
def IsDualPointSet {S : Type u} [TopologicalSpace S] (C V U : Set S) : Prop :=
  (V = ∅ → U = ∅) ∧
  (V.Nonempty → U ⊆ C \ V ∧ ∀ seg ∈ segmentsOf C V, (U ∩ seg).ncard = 1)

/-- Four points $a, b, c, d \in C$ satisfy '$\{a, c\}$ *crosses* $\{b, d\}$' on $C$ if $a, b, c, d$
are distinct points of $C$ occurring in cyclic order around $C$, that is, $b$ and $d$ lie in
different connected components of $C \setminus \{a, c\}$.
Graph Minors VI, Section 2 (page 117): "If $a, b, c, d$ are distinct points of $C$ occurring in
that order, we say that $\{a, c\}$ *crosses* $\{b, d\}$." -/
abbrev CrossesOn {S : Type u} [TopologicalSpace S] (C : Set S) (a c b d : S) : Prop :=
  Surface.PairsCrossOn C a c b d

/-- The relation on $U$ defining the dual division $\Delta^*$: there is no $\delta \in \Delta$ and
$v, v' \in \delta$ such that $\{v, v'\}$ crosses $\{u, u'\}$.
Graph Minors VI, Section 2 (page 117): "The relation between $u, u' \in U$, ...there is no $\delta
\in \Delta$ and $v, v' \in
\delta$ such that $\{v, v'\}$ crosses $\{u, u'\}$... is an equivalence relation on $U$, as
is easily seen." -/
def dualEquivRel {S : Type u} [TopologicalSpace S] (C : Set S) (Δ : Set (Set S))
    (u u' : S) : Prop :=
  ¬ ∃ δ ∈ Δ, ∃ v ∈ δ, ∃ v' ∈ δ, CrossesOn C v v' u u'

/-- The dual division $\Delta^*$ on $U$, defined as the set of equivalence classes of
`dualEquivRel C Δ` on $U$.
Graph Minors VI, Section 2 (page 117): "We denote the set of equivalence classes by $\Delta^*$." -/
def dualDivision {S : Type u} [TopologicalSpace S] (C U : Set S) (Δ : Set (Set S)) :
    Set (Set S) :=
  (fun u : S => {u' ∈ U | dualEquivRel C Δ u u'}) '' U

/-- The double-dual division $\Delta^{**}$ on $V = \bigcup \Delta$, defined as the set of
equivalence classes on $V$ of `dualEquivRel C Δ*`.
Graph Minors VI, Section 2 (page 117): "We define $\Delta^{**}$ to be the set of equivalence classes
on $V$ of the relation between
$v, v' \in V$, ...there is no $\delta^* \in \Delta^*$ and $u, u' \in \delta^*$ such that
$\{u, u'\}$ crosses $\{v, v'\}$...." -/
def doubleDualDivision {S : Type u} [TopologicalSpace S] (C U : Set S) (Δ : Set (Set S)) :
    Set (Set S) :=
  dualDivision C (divisionUnion Δ) (dualDivision C U Δ)

/-- A division $\Delta$ on $C$ is *cross-free* if there do not exist distinct
$\delta, \delta' \in \Delta$ and $s, t \in \delta$, $s', t' \in \delta'$ such that $\{s, t\}$
crosses $\{s', t'\}$.
Graph Minors VI, Section 2 (page 117): "We say that $\Delta$ is *cross-free* if there do not exist
distinct $\delta, \delta' \in \Delta$ and $s, t \in \delta$, $s', t' \in \delta'$ such that
$\{s, t\}$ crosses $\{s', t'\}$." -/
def IsCrossFree {S : Type u} [TopologicalSpace S] (C : Set S) (Δ : Set (Set S)) : Prop :=
  ¬ ∃ δ ∈ Δ, ∃ δ' ∈ Δ, δ ≠ δ' ∧ ∃ s ∈ δ, ∃ t ∈ δ, ∃ s' ∈ δ', ∃ t' ∈ δ',
    CrossesOn C s t s' t'

/-- For $x, y \in W$, $\Delta(x, y)$ is the number of members $\delta \in \Delta$ that either meet
$\{x, y\}$ or contain $u, v \in \delta$ such that $\{u, v\}$ crosses $\{x, y\}$.
Graph Minors VI, Section 2 (page 118):
"$$\Delta(x, y) = |\{\delta \in \Delta : \text{either } \delta \cap \{x, y\} \ne
\emptyset\text{, or there exist } u, v \in \delta \text{ such that } \{u, v\} \text{ crosses
} \{x, y\}\}|" -/
noncomputable def divisionCount {S : Type u} [TopologicalSpace S] (C : Set S)
    (Δ : Set (Set S)) (x y : S) : ℕ :=
  {δ ∈ Δ | (δ ∩ {x, y}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn C u v x y}.ncard

/-- A pair $(v_1, v_2)$ is a *$\Delta$-minimizer* with respect to $(C_1, C_2, x, y)$ if
(i) $v_1 \in C_1 \cap V$, $v_2 \in C_2 \cap V$, and $v_1, v_2 \ne x$; and
(ii) there exists $\delta \in \Delta$ such that $v_1, v_2 \in \delta$ and $\{v, x\}$ crosses
$\{v_1, v_2\}$ for every $v \in \delta \setminus \{v_1, v_2\}$.
Graph Minors VI, Section 2, proof of (2.4) (pages 118–119). -/
def IsDeltaMinimizer {S : Type u} [TopologicalSpace S] (C C₁ C₂ : Set S)
    (Δ : Set (Set S)) (x : S) (p : S × S) : Prop :=
  p.1 ∈ C₁ ∩ divisionUnion Δ ∧ p.2 ∈ C₂ ∩ divisionUnion Δ ∧ p.1 ≠ x ∧ p.2 ≠ x ∧
  ∃ δ ∈ Δ, p.1 ∈ δ ∧ p.2 ∈ δ ∧
    ∀ v ∈ δ \ {p.1, p.2}, CrossesOn C v x p.1 p.2

/-- A pair $(u_1, u_2)$ is a *$\Delta^*$-maximizer* with respect to $(C_1, C_2, U, x, y)$ if
(i) $u_1 \in C_1 \cap U$, $u_2 \in C_2 \cap U$, and $u_1, u_2 \ne y$; and
(ii) there exists $\delta^* \in \Delta^*$ such that $u_1, u_2 \in \delta^*$ and $\{u, y\}$ crosses
$\{u_1, u_2\}$ for every $u \in \delta^* \setminus \{u_1, u_2\}$.
Graph Minors VI, Section 2, proof of (2.4) (page 119). -/
def IsDualMaximizer {S : Type u} [TopologicalSpace S] (C C₁ C₂ U : Set S)
    (Δ : Set (Set S)) (y : S) (p : S × S) : Prop :=
  p.1 ∈ C₁ ∩ U ∧ p.2 ∈ C₂ ∩ U ∧ p.1 ≠ y ∧ p.2 ≠ y ∧
  ∃ δ_star ∈ dualDivision C U Δ, p.1 ∈ δ_star ∧ p.2 ∈ δ_star ∧
    ∀ u ∈ δ_star \ {p.1, p.2}, CrossesOn C u y p.1 p.2

/-- **Graph Minors VI, (2.1)** (page 117):
"$\Delta^*$ is cross-free, for any $\Delta$." -/
def Statement21 : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (C U : Set S) (Δ : Set (Set S)),
    IsOArc C → IsDivision Δ → divisionUnion Δ ⊆ C →
    IsDualPointSet C (divisionUnion Δ) U →
    IsCrossFree C (dualDivision C U Δ)

/-- **Graph Minors VI, (2.2)** (page 117):
"If $\Delta$ is cross-free then $\Delta^{**} = \Delta$." -/
def Statement22 : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (C U : Set S) (Δ : Set (Set S)),
    IsOArc C → IsDivision Δ → (divisionUnion Δ).Finite → divisionUnion Δ ⊆ C →
    IsDualPointSet C (divisionUnion Δ) U → IsCrossFree C Δ →
    doubleDualDivision C U Δ = Δ

/-- **Graph Minors VI, (2.3)** (page 118):
"If $W \ne \emptyset$, one of $\Delta, \Delta^*$ has a member with cardinality $1$." -/
def Statement23 : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (C U : Set S) (Δ : Set (Set S)),
    IsOArc C → IsDivision Δ → (divisionUnion Δ).Finite → divisionUnion Δ ⊆ C →
    IsDualPointSet C (divisionUnion Δ) U →
    (divisionUnion Δ ∪ U).Nonempty →
    ∃ γ ∈ Δ ∪ dualDivision C U Δ, γ.ncard = 1

/-- **Graph Minors VI, (2.4)** (page 118):
"If $\Delta$ is cross-free and $x, y \in W$, then
$$\begin{aligned}
\Delta(x, y) - \Delta^*(x, y) &= 1 &&\text{if } x, y \in V \\
&= -1 &&\text{if } x, y \in U. \\
&= 0 &&\text{otherwise.}
\end{aligned}$$" -/
def Statement24 : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (C U : Set S) (Δ : Set (Set S)) (x y : S),
    IsOArc C → IsDivision Δ → (divisionUnion Δ).Finite → divisionUnion Δ ⊆ C →
    IsDualPointSet C (divisionUnion Δ) U → IsCrossFree C Δ →
    x ∈ divisionUnion Δ ∪ U → y ∈ divisionUnion Δ ∪ U →
    ((x ∈ divisionUnion Δ ∧ y ∈ divisionUnion Δ →
        (divisionCount C Δ x y : ℤ) - (divisionCount C (dualDivision C U Δ) x y : ℤ) = 1) ∧
     (x ∈ U ∧ y ∈ U →
        (divisionCount C Δ x y : ℤ) - (divisionCount C (dualDivision C U Δ) x y : ℤ) = -1) ∧
     (¬ (x ∈ divisionUnion Δ ∧ y ∈ divisionUnion Δ) → ¬ (x ∈ U ∧ y ∈ U) →
        (divisionCount C Δ x y : ℤ) - (divisionCount C (dualDivision C U Δ) x y : ℤ) = 0))

/-! ## Section 3: The Disjoint Subgraph Problem on a Disc (pages 119–122) -/

/-- A topological space $S$ is a *closed disc* if it is homeomorphic to `ClosedUnitDisc`.
Graph Minors VI, Section 1 (page 116) & Section 3 (page 119). -/
def IsClosedDiscSpace (S : Type u) [TopologicalSpace S] : Prop :=
  Nonempty (ClosedUnitDisc ≃ₜ S)

/-- A drawing $G^*$ on a closed disc $\Sigma$ is a *dual drawing* of a proper drawing $G$ on
$\Sigma$ (in the one-way sense of Graph Minors VI, Section 3, pages 119–120) if:
- $G$ and $G^*$ are properly drawn in $\Sigma$;
- each region of $G$ contains a unique vertex of $G^*$, and every vertex of $G^*$ lies in a region
  of $G$;
- each segment of $\operatorname{bd}(\Sigma)$ with respect to $V(G) \cap \operatorname{bd}(\Sigma)$
  contains a unique vertex of $G^*$, and no other vertices of $G^*$ lie in
  $\operatorname{bd}(\Sigma)$;
- the edges of $G^*$ separate distinct vertices of $G$ in $\Sigma \setminus U(G^*)$, and there is a
  bijection between $E(G)$ and $E(G^*)$ such that for each edge $e \in E(G)$ and its corresponding
  edge $e^* \in E(G^*)$, $e$ and $e^*$ cross at a single point, every region of $G^*$ incident with
  $e^*$ meets $e$, and the ends of $e^*$ in $G^*$ are the dual vertices of the regions of $G$
  incident with $e$.
Graph Minors VI, Section 3 (pages 119–120). -/
def IsDiscDualDrawing {S : Type u} [TopologicalSpace S] (G G_dual : Drawing S) : Prop :=
  G.IsProper ∧ G_dual.IsProper ∧
  (∀ r ∈ G.R, ∃! w, w ∈ r ∧ w ∈ G_dual.V) ∧
  (∀ w ∈ G_dual.V, ∃ r ∈ G.R, w ∈ r) ∧
  IsDualPointSet (bd S) (G.V ∩ bd S) (G_dual.V ∩ bd S) ∧
  (∀ v₁ ∈ G.V, ∀ v₂ ∈ G.V,
    connectedComponentIn (univ \ G_dual.U) v₁ = connectedComponentIn (univ \ G_dual.U) v₂ →
      v₁ = v₂) ∧
  ∃ edgeEquiv : G.E ≃ G_dual.E,
    ∀ e : G.E,
      ((edgeEquiv e).1 ∩ G.U = (edgeEquiv e).1 ∩ e.1) ∧
      (e.1 ∩ G_dual.U = e.1 ∩ (edgeEquiv e).1) ∧
      ((edgeEquiv e).1 ∩ e.1).ncard = 1 ∧
      (∀ r' ∈ G_dual.R, G_dual.EdgeRegionIncident (edgeEquiv e).1 r' → (r' ∩ e.1).Nonempty) ∧
      (∀ r₁ ∈ G.R, ∀ r₂ ∈ G.R, ∀ w₁ ∈ r₁ ∩ G_dual.V, ∀ w₂ ∈ r₂ ∩ G_dual.V,
        G_dual.toGraph.IsLink (edgeEquiv e).1 w₁ w₂ ↔
          G.EdgeRegionIncident e.1 r₁ ∧ G.EdgeRegionIncident e.1 r₂ ∧
          ∀ r ∈ G.R, G.EdgeRegionIncident e.1 r → r = r₁ ∨ r = r₂)

/-- A pair of drawings $(G, G^*)$ on a closed disc $\Sigma$ is a *dual drawing pair* if each is a
dual drawing of the other and vertex-region incidence is transposed between $G$ and $G^*$.
Graph Minors VI, Section 3 (pages 119–120). -/
def IsDiscDualDrawingPair {S : Type u} [TopologicalSpace S] (G G_dual : Drawing S) : Prop :=
  G.IsProper ∧ G_dual.IsProper ∧
  G.V ∩ G_dual.V = ∅ ∧
  (∀ r ∈ G.R, ∃! w, w ∈ r ∧ w ∈ G_dual.V) ∧
  (∀ w ∈ G_dual.V, ∃ r ∈ G.R, w ∈ r) ∧
  (∀ r_dual ∈ G_dual.R, ∃! v, v ∈ r_dual ∧ v ∈ G.V) ∧
  (∀ v ∈ G.V, ∃ r_dual ∈ G_dual.R, v ∈ r_dual) ∧
  (∀ v ∈ G.V, ∀ r ∈ G.R, ∀ w ∈ r ∩ G_dual.V, ∀ r_dual ∈ G_dual.R, v ∈ r_dual →
    (v ∈ closure r ↔ w ∈ closure r_dual)) ∧
  IsDualPointSet (bd S) (G.V ∩ bd S) (G_dual.V ∩ bd S) ∧
  IsDualPointSet (bd S) (G_dual.V ∩ bd S) (G.V ∩ bd S) ∧
  ∃ edgeEquiv : G.E ≃ G_dual.E,
    ∀ e : G.E,
      ((edgeEquiv e).1 ∩ G.U = (edgeEquiv e).1 ∩ e.1) ∧
      (e.1 ∩ G_dual.U = e.1 ∩ (edgeEquiv e).1) ∧
      ((edgeEquiv e).1 ∩ e.1).ncard = 1 ∧
      (∀ r₁ ∈ G.R, ∀ r₂ ∈ G.R, ∀ w₁ ∈ r₁ ∩ G_dual.V, ∀ w₂ ∈ r₂ ∩ G_dual.V,
        G_dual.toGraph.IsLink (edgeEquiv e).1 w₁ w₂ ↔
          G.EdgeRegionIncident e.1 r₁ ∧ G.EdgeRegionIncident e.1 r₂ ∧
          ∀ r ∈ G.R, G.EdgeRegionIncident e.1 r → r = r₁ ∨ r = r₂) ∧
      (∀ r₁' ∈ G_dual.R, ∀ r₂' ∈ G_dual.R, ∀ v₁ ∈ r₁' ∩ G.V, ∀ v₂ ∈ r₂' ∩ G.V,
        G.toGraph.IsLink e.1 v₁ v₂ ↔
          G_dual.EdgeRegionIncident (edgeEquiv e).1 r₁' ∧
          G_dual.EdgeRegionIncident (edgeEquiv e).1 r₂' ∧
          ∀ r' ∈ G_dual.R, G_dual.EdgeRegionIncident (edgeEquiv e).1 r' → r' = r₁' ∨ r' = r₂')

/-- A term $A_i$ of an $(x, y)$-chain in a drawing $G$ on $\Sigma$: either a vertex `.inl v`
($v \in \Sigma$) or a region `.inr r` ($r \subseteq \Sigma$).
Graph Minors VI, Section 3 (page 121). -/
abbrev ChainTerm (S : Type u) : Type u :=
  S ⊕ Set S

namespace ChainTerm

variable {S : Type u} [TopologicalSpace S]

/-- A chain term is valid in $G$ if it is either a vertex in $V(G)$ or a region in $R(G)$. -/
def IsValid (G : Drawing S) : ChainTerm S → Prop
  | .inl v => v ∈ G.V
  | .inr r => r ∈ G.R

/-- Whether a chain term is a vertex term. -/
def IsVertex : ChainTerm S → Prop
  | .inl _ => True
  | .inr _ => False

instance (t : ChainTerm S) : Decidable t.IsVertex :=
  match t with
  | .inl _ => isTrue trivial
  | .inr _ => isFalse not_false

/-- A vertex $v$ of $G$ is *peripheral* if $v \in \operatorname{bd}(\Sigma)$, and a region $r$ of
$G$ is *peripheral* if it contains a segment of $\operatorname{bd}(\Sigma)$ with respect to
$V(G) \cap \operatorname{bd}(\Sigma)$.
Graph Minors VI, Section 3 (page 121): "A vertex $v$ of $G$ is *peripheral* if
$v \in \operatorname{bd}(\Sigma)$, and a region is *peripheral* if it contains a segment of
$\operatorname{bd}(\Sigma)$ (with respect to $\bigcup \Delta$)." -/
def IsPeripheral (G : Drawing S) : ChainTerm S → Prop
  | .inl v => v ∈ G.V ∧ v ∈ bd S
  | .inr r => r ∈ G.R ∧ ∃ seg ∈ segmentsOf (bd S) (G.V ∩ bd S), seg ⊆ r

/-- Two chain terms $A_i, A_{i+1}$ are incident in $G$ if one is a vertex of $G$, the other is a
region of $G$, and the vertex lies in the closure of the region.
Graph Minors VI, Section 3 (page 121): "(i) for $1 \le i < k$, one of $A_i, A_{i+1}$ is a vertex of
$G$, the other is a region, and
they are incident" -/
def AreIncident (G : Drawing S) : ChainTerm S → ChainTerm S → Prop
  | .inl v, .inr r => v ∈ G.V ∧ r ∈ G.R ∧ v ∈ closure r
  | .inr r, .inl v => v ∈ G.V ∧ r ∈ G.R ∧ v ∈ closure r
  | _, _ => False

/-- Condition (ii) of an $(x, y)$-chain at an endpoint $z \in W$: if the endpoint term is a vertex
then it equals $z$; if it is a region then $z$ lies in that region.
Graph Minors VI, Section 3 (page 121): "(ii) if $A_1$ is a vertex then $A_1 = x$; if $A_1$ is a
region then $x \in A_1$; if $A_k$ is
a vertex then $A_k = y$; if $A_k$ is a region then $y \in A_k$" -/
def MatchesEnd (z : S) : ChainTerm S → Prop
  | .inl v => v = z
  | .inr r => z ∈ r

/-- The left endpoint of a chain term, using `x` when the chain starts in a region. -/
def leftEndpoint {S : Type u} (A : List (ChainTerm S)) (x : S) (i : Fin A.length) : S :=
  match A[i.1]'i.2 with
  | .inl v => v
  | .inr _ =>
    if i.1 = 0 then x
    else
      match A[i.1 - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2) with
      | .inl v => v
      | .inr _ => x

/-- The right endpoint of a chain term, using `y` when the chain ends in a region. -/
def rightEndpoint {S : Type u} (A : List (ChainTerm S)) (y : S) (i : Fin A.length) : S :=
  match A[i.1]'i.2 with
  | .inl v => v
  | .inr _ =>
    if hi : i.1 + 1 = A.length then y
    else
      match A[i.1 + 1]'(Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.2) hi) with
      | .inl v => v
      | .inr _ => y

end ChainTerm

/-- For $x, y \in W$, a sequence $A = [A_1, \dots, A_k]$ ($k \ge 1$) is an *$(x, y)$-chain* of $G$
if:
(i) consecutive terms consist of a vertex of $G$ and a region of $G$ that are incident;
(ii) $A_1$ matches $x$ and $A_k$ matches $y$; and
(iii) $A_i$ is peripheral if and only if $i = 1$ or $i = k$.
Graph Minors VI, Section 3 (page 121). -/
structure IsXYChain {S : Type u} [TopologicalSpace S] (G : Drawing S) (x y : S)
    (A : List (ChainTerm S)) : Prop where
  /-- The chain has at least one term ($k \ge 1$). -/
  ne_nil : A ≠ []
  /-- Every term is a vertex or region of $G$. -/
  valid : ∀ t ∈ A, t.IsValid G
  /-- (i) Consecutive terms alternate between incident vertices and regions of $G$. -/
  isChain : A.IsChain (ChainTerm.AreIncident G)
  /-- (ii) $A_1$ matches $x$. -/
  head_matches : (A.head ne_nil).MatchesEnd x
  /-- (ii) $A_k$ matches $y$. -/
  last_matches : (A.getLast ne_nil).MatchesEnd y
  /-- (iii) $A_i$ is peripheral if and only if $i$ is the first or last index. -/
  peripheral_iff : ∀ i : Fin A.length,
    (A[i]).IsPeripheral G ↔ (i.1 = 0 ∨ i.1 + 1 = A.length)

/-- Consecutive terms of a chain share their endpoints at the intervening drawing vertex. -/
theorem IsXYChain.endpoints_eq {S : Type u} [TopologicalSpace S] {G : Drawing S}
    {A : List (ChainTerm S)} {x y : S} (h : IsXYChain G x y A)
    (i : Fin A.length) (hi : i.1 + 1 < A.length) :
    ChainTerm.rightEndpoint A y i = ChainTerm.leftEndpoint A x ⟨i.1 + 1, hi⟩ := by
  have hinc := List.isChain_iff_getElem.mp h.isChain i.1 hi
  rcases hcurrent : A[i.1]'i.2 with v | r <;>
    rcases hnext : A[i.1 + 1]'hi with w | r'
  · rw [hcurrent, hnext] at hinc
    exact False.elim hinc
  · simp [ChainTerm.rightEndpoint, ChainTerm.leftEndpoint, hcurrent, hnext]
  · simp [ChainTerm.rightEndpoint, ChainTerm.leftEndpoint, hcurrent, hnext, ne_of_lt hi]
  · rw [hcurrent, hnext] at hinc
    exact False.elim hinc

/-- The *length* of an $(x, y)$-chain is the number of terms which are vertices.
Graph Minors VI, Section 3 (page 121): "The *length* of an $(x, y)$-chain is the number of terms
which are vertices." -/
def chainLength {S : Type u} (A : List (ChainTerm S)) : ℕ :=
  (A.filter (fun t => decide t.IsVertex)).length

theorem ncard_inl_mem_le_chainLength {S : Type u} (A : List (ChainTerm S)) :
    {v : S | Sum.inl v ∈ A}.ncard ≤ chainLength A := by
  induction A with
  | nil => simp [chainLength]
  | cons hd tl ih =>
    rcases hd with v | r
    · have h_eq : {w : S | Sum.inl w ∈ (Sum.inl v : ChainTerm S) :: tl} =
          insert v {w : S | Sum.inl w ∈ tl} := by
        ext w; simp
      have h_len : chainLength ((Sum.inl v : ChainTerm S) :: tl) = chainLength tl + 1 := rfl
      rw [h_eq, h_len]
      exact (ncard_insert_le v _).trans (Nat.add_le_add_right ih 1)
    · have h_eq : {w : S | Sum.inl w ∈ (Sum.inr r : ChainTerm S) :: tl} =
          {w : S | Sum.inl w ∈ tl} := by
        ext w; simp
      have h_len : chainLength ((Sum.inr r : ChainTerm S) :: tl) = chainLength tl := rfl
      rw [h_eq, h_len]
      exact ih

theorem finite_inl_mem {S : Type u} (A : List (ChainTerm S)) :
    {v : S | Sum.inl v ∈ A}.Finite := by
  induction A with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with v | r
    · have h_eq : {w : S | Sum.inl w ∈ (Sum.inl v : ChainTerm S) :: tl} =
          insert v {w : S | Sum.inl w ∈ tl} := by
        ext w; simp
      rw [h_eq]
      exact ih.insert v
    · have h_eq : {w : S | Sum.inl w ∈ (Sum.inr r : ChainTerm S) :: tl} =
          {w : S | Sum.inl w ∈ tl} := by
        ext w; simp
      rw [h_eq]
      exact ih

/-- The *$\Delta$-redundancy* of an $(x, y)$-chain in $G$ is its length minus $\Delta(x, y)$.
Graph Minors VI, Section 3 (page 121): "The *$\Delta$-redundancy* of an $(x, y)$-chain in $G$ is
its length minus $\Delta(x, y)$." -/
noncomputable def chainRedundancy {S : Type u} [TopologicalSpace S] (_G : Drawing S)
    (Δ : Set (Set S)) (x y : S) (A : List (ChainTerm S)) : ℤ :=
  (chainLength A : ℤ) - (divisionCount (bd S) Δ x y : ℤ)

/-- **Graph Minors VI, (3.1)** (page 120):
"If $G$ is connected and properly drawn on a disc $\Sigma$, then $G^{**} = G$. (More precisely, the
drawing of $G$ is a drawing of $G^{**}$.)" -/
def Statement31 : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (G G_dual : Drawing S),
    IsClosedDiscSpace S → IsGraphConnected G.toGraph →
    IsDiscDualDrawing G G_dual →
    IsDiscDualDrawing G_dual G

/-- **Graph Minors VI, (3.2)** (page 120):
"Let $G$ be a connected graph, properly drawn on a disc $\Sigma$. Let $\Delta$ be a
cross-free division with* $$\bigcup \Delta = V(G) \cap bd(\Sigma).$$ *Let the drawing of
$G^*$ be chosen so that* $$\bigcup \Delta^* = V(G^*) \cap bd(\Sigma).$$ *Then $\Delta$ is
feasible in $G$ if and only if $\Delta^*$ is feasible in $G^*$." -/
def Statement32 : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (G G_dual : Drawing S) (Δ : Set (Set S)),
    IsClosedDiscSpace S → IsGraphConnected G.toGraph →
    IsDivision Δ → divisionUnion Δ = G.V ∩ bd S →
    IsCrossFree (bd S) Δ → IsDiscDualDrawing G G_dual →
    (IsFeasible G.toGraph Δ ↔
      IsFeasible G_dual.toGraph (dualDivision (bd S) (G_dual.V ∩ bd S) Δ))

/-- **Graph Minors VI, (3.3)(i)** (page 120):
"If $|\delta| = 1$ for some $\delta \in \Delta$, and $\delta = \{v\}$ say, then $\Delta$ is feasible
in $G$ if and only if $\Delta - \{\delta\}$ is feasible in the graph obtained from $G$ by deleting
$v$." -/
def Statement33i : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (Δ : Set (Set α)) (v : α),
    IsDivision Δ → divisionUnion Δ ⊆ V(G) → {v} ∈ Δ →
    (IsFeasible G Δ ↔ IsFeasible (G.deleteVerts {v}) (Δ \ {{v}}))

/-- **Graph Minors VI, (3.3)(ii)** (page 120):
"If $G$ has a component $G'$ with no vertex in $\operatorname{bd}(\Sigma)$ then $\Delta$ is feasible
in $G$ if and only if it is feasible in the graph obtained from $G$ by deleting $V(G')$." -/
def Statement33ii : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (G : Drawing S) (G' : Graph S (Set S)) (Δ : Set (Set S)),
    IsDivision Δ → divisionUnion Δ ⊆ G.V ∩ bd S →
    IsGraphComponent G' G.toGraph → Disjoint V(G') (bd S) →
    (IsFeasible G.toGraph Δ ↔ IsFeasible (G.toGraph.deleteVerts V(G')) Δ)

/-- **Graph Minors VI, (3.3)(iii)** (page 121):
"If there exists $\delta \in \Delta$ which intersects more than one component of $G$ then $\Delta$
is not feasible in $G$." -/
def Statement33iii : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (Δ : Set (Set α)) (δ : Set α)
    (G₁ G₂ : Graph α β),
    δ ∈ Δ → IsGraphComponent G₁ G → IsGraphComponent G₂ G → G₁ ≠ G₂ →
    (δ ∩ V(G₁)).Nonempty → (δ ∩ V(G₂)).Nonempty →
    ¬ IsFeasible G Δ

/-- **Graph Minors VI, (3.3)(iv)** (page 121):
"If $G$ has components $G_1, \dots, G_k$ for $k \ge 2$, and (ii), (iii) do not apply, let
$(\Delta_1, \dots, \Delta_k)$ be the partition of $\Delta$ such that* $$\bigcup \Delta_i =
V(G_i) \cap bd(\Sigma) \qquad (1 \le i \le k);$$ *then $\Delta$ is feasible in $G$ if and
only if $\Delta_i$ is feasible in $G_i$ for each $i$." -/
def Statement33iv : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (G : Drawing S) (Δ : Set (Set S))
    (k : ℕ) (G_comp : Fin k → Graph S (Set S)) (Δ_part : Fin k → Set (Set S)),
    2 ≤ k → IsDivision Δ → divisionUnion Δ = G.V ∩ bd S →
    InjOn G_comp Set.univ →
    graphComponents G.toGraph = Set.range G_comp →
    (∀ i : Fin k, Δ_part i = {δ ∈ Δ | δ ⊆ V(G_comp i)}) →
    (∀ δ ∈ Δ, ∃ i : Fin k, δ ⊆ V(G_comp i)) →
    (IsFeasible G.toGraph Δ ↔ ∀ i : Fin k, IsFeasible (G_comp i) (Δ_part i))

/-- **Graph Minors VI, (3.5)** (page 121):
"If $G$ is connected, any $(x, y)$-chain of $G^*$ corresponds to an $(x, y)$-chain of $G$, and if
$\Delta$ is cross-free the $\Delta^*$-redundancy of the first chain equals the $\Delta$-redundancy
of the second." -/
def Statement35 : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (G G_dual : Drawing S) (Δ : Set (Set S)) (x y : S)
    (A_dual : List (ChainTerm S)),
    IsClosedDiscSpace S → IsGraphConnected G.toGraph →
    IsDivision Δ → divisionUnion Δ = G.V ∩ bd S →
    IsCrossFree (bd S) Δ → IsDiscDualDrawing G G_dual →
    x ∈ (G_dual.V ∩ bd S) ∪ divisionUnion Δ →
    y ∈ (G_dual.V ∩ bd S) ∪ divisionUnion Δ →
    IsXYChain G_dual x y A_dual →
    ∃ A : List (ChainTerm S),
      IsXYChain G x y A ∧
      chainRedundancy G_dual (dualDivision (bd S) (G_dual.V ∩ bd S) Δ) x y A_dual =
        chainRedundancy G Δ x y A

/-- **Graph Minors VI, (3.6)** (page 122):
"Let $G$ be properly drawn on a disc $\Sigma$, and let $\Delta$ be a division with* $$\bigcup
\Delta = V(G) \cap bd(\Sigma).$$ *Then $\Delta$ is feasible in $G$ if and only if* (i)
*$\Delta$ is cross-free, and* (ii) *every $(x, y)$-chain has non-negative redundancy, for
all $x, y \in W$" -/
def Statement36 : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (G : Drawing S) (Δ : Set (Set S)) (U : Set S),
    IsClosedDiscSpace S → G.IsProper →
    IsDivision Δ → divisionUnion Δ = G.V ∩ bd S →
    IsDualPointSet (bd S) (divisionUnion Δ) U →
    (IsFeasible G.toGraph Δ ↔
      IsCrossFree (bd S) Δ ∧
      ∀ x ∈ U ∪ divisionUnion Δ, ∀ y ∈ U ∪ divisionUnion Δ,
        ∀ A : List (ChainTerm S), IsXYChain G x y A →
          0 ≤ chainRedundancy G Δ x y A)

/-! ## Section 4: The Cylinder and Routed Forest Containment (pages 122–127) -/

/-- A continuous injection $f \colon [0, 1] \to \Sigma$ *parametrizes* a subset $X \subseteq \Sigma$
from $s$ to $t$ if $f$ is injective, $\operatorname{range}(f) = X$, $f(0) = s$, and $f(1) = t$.
Graph Minors VI, Section 4 (page 123). -/
def ParametrizesSet {S : Type u} [TopologicalSpace S] (f : Curve S) (X : Set S)
    (s t : S) : Prop :=
  f.IsLine ∧ Set.range f = X ∧ f 0 = s ∧ f 1 = t

/-- A drawing $P$ in $\Sigma$ is a *path drawing* with end-vertices $s, t$ if $P.toGraph$ is traced
by a simple walk $W$ between $s$ and $t$ with $V(P) = \operatorname{support}(W)$ and
$E(P) = \operatorname{edges}(W)$, and $U(P)$ is parameterized by a continuous injection from $s$ to
$t$.
Graph Minors VI, Section 4 (page 123). -/
def IsPathDrawing {S : Type u} [TopologicalSpace S] (P : Drawing S) (s t : S) : Prop :=
  (∃ W : GraphWalk P.toGraph s t, W.IsSimple ∧
    P.V = {x | x ∈ W.support} ∧ P.E = {e | e ∈ W.edges}) ∧
  ∃ f : Curve S, ParametrizesSet f P.U s t

/-- Two paths $P_1, P_2$ drawn on $\Sigma$ with end-vertices $s, t$ are *homotopic* if there are
continuous injections $f_1, f_2 \colon [0, 1] \to \Sigma$ with images $U(P_1), U(P_2)$ and
$f_i(0) = s, f_i(1) = t$ such that $f_1$ is homotopic to $f_2$.
Graph Minors VI, Section 4 (page 123). -/
def PathsHomotopic {S : Type u} [TopologicalSpace S] (P₁ P₂ : Drawing S) (s t : S) : Prop :=
  ∃ f₁ f₂ : Curve S,
    ParametrizesSet f₁ P₁.U s t ∧ ParametrizesSet f₂ P₂.U s t ∧ CurvesHomotopic f₁ f₂

/-- A path $P$ drawn on $\Sigma$ with end-vertices $s, t \in C$ on a cuff $C$ is *homotopic to* a
component $S_{\text{arc}}$ of $C \setminus \{s, t\}$ if there are continuous injections
$f_1, f_2 \colon [0, 1] \to \Sigma$ from $s$ to $t$ with images $U(P)$ and
$\overline{S_{\text{arc}}}$
that are homotopic in $\Sigma$.
Graph Minors VI, Section 4 (page 124): "Suppose that $C$ is a cuff of $\Sigma$, and $s, t \in C$ are
distinct, and $S$ is a
component of $C - \{s, t\}$. Suppose that $P$ is a path drawn on $\Sigma$ with end-vertices
$s$ and $t$. Then we define ...$P$ is homotopic to $S$... in the obvious way." -/
def PathHomotopicToArc {S : Type u} [TopologicalSpace S] (P : Drawing S) (s t : S)
    (S_arc : Set S) : Prop :=
  ∃ f₁ f₂ : Curve S,
    ParametrizesSet f₁ P.U s t ∧ ParametrizesSet f₂ (closure S_arc) s t ∧ CurvesHomotopic f₁ f₂

/-- **ROUTED FOREST CONTAINMENT (ON $\Sigma$)** (Graph Minors VI, Section 4, page 123):
Given a surface $\Sigma$, a graph $G$ drawn on $\Sigma$, and a forest $H$ drawn on $\Sigma$ with
$V(H) \cap \operatorname{bd}(\Sigma) \subseteq V(G)$, does $G$ have a forest subgraph homotopic to
$H$? -/
def HasHomotopicForestSubgraph {S : Type u} [TopologicalSpace S] (G H : Drawing S) : Prop :=
  ∃ F : Drawing S, F.IsSubdrawing G ∧ F.U ⊆ G.U ∧ ForestsHomotopic F H

/-- A closed disc $\Delta \subseteq \Sigma$ is *the portion of $\Sigma$ enclosed by $P \cup S$* if
$\Delta$ is a closed disc containing $S$ whose boundary $O$-arc is $U(P) \cup \bar{S}$.
Graph Minors VI, Section 4 (page 124). -/
def IsEnclosedDisc {S : Type u} [TopologicalSpace S] (P : Drawing S) (S_arc Δ : Set S) : Prop :=
  IsClosedDisc Δ ∧ S_arc ⊆ Δ ∧ discBd Δ = P.U ∪ closure S_arc

/-- $P$ is the minimal boundary path $P(s, t, S)$ in $G$ if $P$ is a path subdrawing of $G$ between
$s$ and $t$ homotopic to $S$ enclosing a closed disc $\Delta$, and for every path subdrawing $P'$ of
$G$ between $s$ and $t$ homotopic to $S$ enclosing a closed disc $\Delta'$, $\Delta \subseteq
\Delta'$.
Graph Minors VI, Section 4 (page 124): "there is such a path $P$ of $G$ where the portion of
$\Sigma$ enclosed by $P \cup S$ is minimal, and this path is unique. ... This path is denoted by
$P(s, t, S)$." -/
def IsMinimalBoundaryPath {S : Type u} [TopologicalSpace S] (G : Drawing S) (s t : S)
    (S_arc : Set S) (P : Drawing S) : Prop :=
  P.IsSubdrawing G ∧ P.U ⊆ G.U ∧ IsPathDrawing P s t ∧ PathHomotopicToArc P s t S_arc ∧
  ∃ Δ : Set S, IsEnclosedDisc P S_arc Δ ∧
    ∀ (P' : Drawing S) (Δ' : Set S),
      P'.IsSubdrawing G → P'.U ⊆ G.U → IsPathDrawing P' s t → PathHomotopicToArc P' s t S_arc →
      IsEnclosedDisc P' S_arc Δ' → Δ ⊆ Δ'

/-- A path $Q$ is the subpath of a path drawing $P$ between two vertices $u, v \in V(P)$.
Graph Minors VI, Section 4 (pages 124–126). -/
def IsSubpathOf {S : Type u} [TopologicalSpace S] (P Q : Drawing S) (u v : S) : Prop :=
  Q.IsSubdrawing P ∧ Q.U ⊆ P.U ∧ IsPathDrawing Q u v

/-- **Reduction 1** of Section 4 (Graph Minors VI, page 124):
"If some component $H'$ of $H$ is such that $G$ has a subgraph with vertex set $V(H') \cap
bd(\Sigma)$ which is homotopic to $H'$" -/
def Section4Reduction1Applies {S : Type u} [TopologicalSpace S] (G H : Drawing S) : Prop :=
  ∃ H' : Drawing S, H'.IsSubdrawing H ∧ H'.U ⊆ H.U ∧
    IsGraphComponent H'.toGraph H.toGraph ∧
    ∃ K : Drawing S, K.IsSubdrawing G ∧ K.U ⊆ G.U ∧
      K.V = H'.V ∩ bd S ∧ ForestsHomotopic K H'

/-- The infeasibility condition **(4.1)** of Section 4 (Graph Minors VI, page 124):
There is a segment $S$ of $\operatorname{bd}(\Sigma) \setminus (V(H) \cap
\operatorname{bd}(\Sigma))$
with distinct ends $s, t$ joined in $H$ by a path $H_{st}$ homotopic to $S$, such that either:
(i) $P(s, t, S)$ does not exist, or
(ii) some vertex of $P(s, t, S)$ lies in $V(H') \cap \operatorname{bd}(\Sigma)$ for some component
$H'$ of $H$ not containing $s, t$, or
(iii) some vertex $v$ of $P(s, t, S)$ lies in $\operatorname{bd}(\Sigma)$ and is joined to $t$ in
$H$ by a path not homotopic to the subpath of $P(s, t, S)$ between $v$ and $t$. -/
def Section4Condition41Applies {S : Type u} [TopologicalSpace S] (G H : Drawing S) : Prop :=
  ∃ S_arc ∈ segmentsOf (bd S) (H.V ∩ bd S),
    ∃ s ∈ H.V ∩ bd S, ∃ t ∈ H.V ∩ bd S,
      s ≠ t ∧ s ∈ closure S_arc ∧ t ∈ closure S_arc ∧
      (∃ H_st : Drawing S, IsSubpathOf H H_st s t ∧ PathHomotopicToArc H_st s t S_arc) ∧
      ((¬ ∃ P : Drawing S, IsMinimalBoundaryPath G s t S_arc P) ∨
       (∃ P : Drawing S, IsMinimalBoundaryPath G s t S_arc P ∧
         ∃ H' : Graph S (Set S), IsGraphComponent H' H.toGraph ∧
           (s ∉ V(H') ∨ t ∉ V(H')) ∧ (P.V ∩ (V(H') ∩ bd S)).Nonempty) ∨
       (∃ P : Drawing S, IsMinimalBoundaryPath G s t S_arc P ∧
         ∃ v ∈ P.V ∩ bd S, ∃ H_vt Q_vt : Drawing S,
           IsSubpathOf H H_vt v t ∧ IsSubpathOf P Q_vt v t ∧ ¬ PathsHomotopic H_vt Q_vt v t))

/-- **Reduction 2** of Section 4 (Graph Minors VI, pages 124–125):
There is a segment $S$ with distinct ends $s, t$ joined in $H$ by a path homotopic to $S$, and for
$P = P(s, t, S)$ enclosing $\Delta$:
(i) $\Delta \setminus (U(P) \cup \bar{S})$ meets $U(G)$ ($P(s, t, S) \cup S$ properly encloses a
vertex or edge of $G$), or
(ii) $P(s, t, S)$ has a vertex not in $\operatorname{bd}(\Sigma)$, or
(iii) $P(s, t, S)$ consists of a single edge $e$. -/
def Section4Reduction2Applies {S : Type u} [TopologicalSpace S] (G H : Drawing S) : Prop :=
  ∃ S_arc ∈ segmentsOf (bd S) (H.V ∩ bd S),
    ∃ s ∈ H.V ∩ bd S, ∃ t ∈ H.V ∩ bd S,
      s ≠ t ∧ s ∈ closure S_arc ∧ t ∈ closure S_arc ∧
      (∃ H_st : Drawing S, IsSubpathOf H H_st s t ∧ PathHomotopicToArc H_st s t S_arc) ∧
      ∃ P : Drawing S, IsMinimalBoundaryPath G s t S_arc P ∧
        ((∃ Δ : Set S, IsEnclosedDisc P S_arc Δ ∧ ((Δ \ (P.U ∪ closure S_arc)) ∩ G.U).Nonempty) ∨
         (P.V \ bd S).Nonempty ∨
         P.E.ncard = 1)

/-- For a cuff $C$, a connected subset $S \subset C$, and distinct $a, b \in S$, $S(a, b)$ denotes
the connected component of $C \setminus \{a, b\}$ which is contained in $S$.
Graph Minors VI, Section 4 (page 125): "Let $C$ be a cuff of a cylinder $\Sigma$, and let
$S \subset C$ be connected. For distinct $a, b \in S$ we denote by $S(a, b)$ the component of
$C - \{a, b\}$ which is contained in $S$." -/
def cuffSubArc {S : Type u} [TopologicalSpace S] (C S_arc : Set S) (a b : S) : Set S :=
  ⋃₀ {K ∈ componentsIn (C \ {a, b}) | K ⊆ S_arc}

/-- A component $H'$ of a forest $H$ drawn on $\Sigma$ is *bad* if it has more than one vertex on
some cuff of $\Sigma$.
Graph Minors VI, Section 4, proof of (4.2) (page 125): "Let us say a component of $H$ is *bad* if
it has more than one vertex on some cuff of $\Sigma$." -/
def IsBadComponent {S : Type u} [TopologicalSpace S] (H' : Graph S (Set S)) : Prop :=
  ∃ C ∈ cuffs S, 1 < (V(H') ∩ C).ncard

/-- Let $C$ be a cuff of $\Sigma$, $H'$ a component of $H$, $s, t \in C \setminus V(H)$ distinct,
and $S$ a component of $C \setminus \{s, t\}$. Then $S$ is a *$C$-base* for $H'$ if
$V(H') \cap C = V(H) \cap S$ and for all distinct $a, b \in V(H) \cap S$, the path $H(a, b)$ of $H$
between $a$ and $b$ is homotopic to $S(a, b)$.
Graph Minors VI, Section 4, proof of (4.2) (pages 125–126). -/
def IsCuffBase {S : Type u} [TopologicalSpace S] (H : Drawing S) (H' : Graph S (Set S))
    (C S_arc : Set S) : Prop :=
  C ∈ cuffs S ∧ IsGraphComponent H' H.toGraph ∧
  (∃ s ∈ C \ H.V, ∃ t ∈ C \ H.V, s ≠ t ∧ S_arc ∈ componentsIn (C \ {s, t})) ∧
  V(H') ∩ C = H.V ∩ S_arc ∧
  ∀ a ∈ H.V ∩ S_arc, ∀ b ∈ H.V ∩ S_arc, a ≠ b →
    ∃ H_ab : Drawing S, IsSubpathOf H H_ab a b ∧
      PathHomotopicToArc H_ab a b (cuffSubArc C S_arc a b)

/-- A component $H'$ of $H$ is *interval-based on $C$* if it has a $C$-base.
Graph Minors VI, Section 4, proof of (4.2) (page 126): "If $H'$ has a $C$-base we say that $H'$ is
*interval-based on $C$*." -/
def IsIntervalBasedOn {S : Type u} [TopologicalSpace S] (H : Drawing S) (H' : Graph S (Set S))
    (C : Set S) : Prop :=
  ∃ S_arc : Set S, IsCuffBase H H' C S_arc

/-- **Graph Minors VI, (4.1)** (page 124):
"With $\Sigma, G, H$ as before, if there is a segment $S$ with distinct ends $s$, $t$, and $s, t$
are joined in $H$ by a path homotopic to $S$, and if either
(i) $P(s, t, S)$ does not exist, or
(ii) some vertex of $P(s, t, S)$ lies in $V(H') \cap bd(\Sigma)$ for some component $H'$ of $H$ not
containing $s, t$, or
(iii) some vertex $v$ of $P(s, t, S)$ lies in $bd(\Sigma)$, and is joined to $t$ in $H$ by a path
not homotopic to the subpath of $P(s, t, S)$ between $v$ and $t$
then $G$ has no forest subgraph homotopic to $H$." -/
def Statement41 : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] (G H : Drawing S),
    IsSurface S → G.IsProper → H.IsProper → IsGraphForest H.toGraph →
    H.V ∩ bd S = G.V ∩ bd S →
    Section4Condition41Applies G H →
    ¬ HasHomotopicForestSubgraph G H

/-- **Graph Minors VI, (4.2)** (page 125):
"If $\Sigma$ is a cylinder and neither (4.1) nor reduction 1 nor reduction 2 applies, then each
component of $H$ has exactly one vertex in each cuff of $\Sigma$." -/
def Statement42 : Prop :=
  ∀ (G H : Drawing ClosedCylinder),
    G.IsProper → H.IsProper → IsGraphForest H.toGraph →
    H.V ∩ bd ClosedCylinder = G.V ∩ bd ClosedCylinder →
    ¬ Section4Condition41Applies G H →
    ¬ Section4Reduction1Applies G H →
    ¬ Section4Reduction2Applies G H →
    ∀ H' : Graph ClosedCylinder (Set ClosedCylinder),
      IsGraphComponent H' H.toGraph →
      (V(H') ∩ cylinderCuff1).ncard = 1 ∧ (V(H') ∩ cylinderCuff2).ncard = 1

/-- **Graph Minors VI, (4.3)** (page 125):
"Let $\Sigma$ be a cylinder, and let $C$ be a cuff of $\Sigma$. Let $s, t \in C$ be distinct, and
let $S$ be a component of $C - \{s, t\}$. Let $K$ be a connected graph with $|V(K)| \ge 2$,
properly drawn on $\Sigma$ with $V(K) \subseteq S$. Then there is an edge of $K$ with distinct ends
$a, b$ say, such that $S(a, b) \cap V(K) = \emptyset$." -/
def Statement43 : Prop :=
  ∀ (C : Set ClosedCylinder) (s t : ClosedCylinder) (S_arc : Set ClosedCylinder)
    (K : Drawing ClosedCylinder),
    C ∈ cuffs ClosedCylinder → s ∈ C → t ∈ C → s ≠ t →
    S_arc ∈ componentsIn (C \ {s, t}) →
    K.IsProper → IsGraphConnected K.toGraph → 2 ≤ K.V.ncard → K.V ⊆ S_arc →
    ∃ e ∈ K.E, ∃ a ∈ K.V, ∃ b ∈ K.V,
      a ≠ b ∧ K.toGraph.IsLink e a b ∧ Disjoint (cuffSubArc C S_arc a b) K.V

/-! ## Section 5: Disjoint Paths along a Cylinder (pages 127–135) -/

/-- The $j$-th vertex $s_j = (1, \frac{2j}{k}\pi)$ on the inner cuff $C_1$ of `ClosedCylinder`
(indexed by `j : Fin k` for $1 \le j \le k$).
Graph Minors VI, Section 5 (pages 127–128):
"$$M_i = \left\{\left(i, \frac{2j}{k}\pi\right): 1 \le j \le k\right\} \qquad (i = 1, 2)" and
"$s_i = (1, \frac{2i}{k}\pi)$." -/
noncomputable def cylinderM1Point (k : ℕ) (j : Fin k) : ClosedCylinder :=
  cylinderPoint 1 (by simp) (2 * ((j.1 + 1 : ℕ) : ℝ) * π / k)

/-- The $j$-th vertex $(2, \frac{2j}{k}\pi)$ on the outer cuff $C_2$ of `ClosedCylinder`
(indexed by `j : Fin k` for $1 \le j \le k$).
Graph Minors VI, Section 5 (page 127). -/
noncomputable def cylinderM2Point (k : ℕ) (j : Fin k) : ClosedCylinder :=
  cylinderPoint 2 (by simp) (2 * ((j.1 + 1 : ℕ) : ℝ) * π / k)

/-- The set $M_1 = \{(1, \frac{2j}{k}\pi) : 1 \le j \le k\} \subseteq C_1$.
Graph Minors VI, Section 5 (page 127). -/
noncomputable def cylinderM1 (k : ℕ) : Set ClosedCylinder :=
  Set.range (cylinderM1Point k)

/-- The set $M_2 = \{(2, \frac{2j}{k}\pi) : 1 \le j \le k\} \subseteq C_2$.
Graph Minors VI, Section 5 (page 127). -/
noncomputable def cylinderM2 (k : ℕ) : Set ClosedCylinder :=
  Set.range (cylinderM2Point k)

/-- The $j$-th dual boundary point $(1, \frac{2j+1}{k}\pi)$ on the inner cuff $C_1$ of
`ClosedCylinder` (indexed by `j : Fin k` for $1 \le j \le k$).
Graph Minors VI, Section 5 (pages 128, 130):
"$$N_i = \left\{\left(i, \frac{2j+1}{k}\pi\right): 1 \le j \le k\right\} \qquad (i = 1, 2).$$" -/
noncomputable def cylinderN1Point (k : ℕ) (j : Fin k) : ClosedCylinder :=
  cylinderPoint 1 (by simp) ((2 * ((j.1 + 1 : ℕ) : ℝ) + 1) * π / k)

/-- The $j$-th dual boundary point $(2, \frac{2j+1}{k}\pi)$ on the outer cuff $C_2$ of
`ClosedCylinder` (indexed by `j : Fin k` for $1 \le j \le k$).
Graph Minors VI, Section 5 (page 130). -/
noncomputable def cylinderN2Point (k : ℕ) (j : Fin k) : ClosedCylinder :=
  cylinderPoint 2 (by simp) ((2 * ((j.1 + 1 : ℕ) : ℝ) + 1) * π / k)

/-- The set $N_1 = \{(1, \frac{2j+1}{k}\pi) : 1 \le j \le k\} \subseteq C_1$.
Graph Minors VI, Section 5 (page 130). -/
noncomputable def cylinderN1 (k : ℕ) : Set ClosedCylinder :=
  Set.range (cylinderN1Point k)

/-- The set $N_2 = \{(2, \frac{2j+1}{k}\pi) : 1 \le j \le k\} \subseteq C_2$.
Graph Minors VI, Section 5 (page 130). -/
noncomputable def cylinderN2 (k : ℕ) : Set ClosedCylinder :=
  Set.range (cylinderN2Point k)

/-- The standing assumption on $G$ in Section 5 (Graph Minors VI, page 128):
"Throughout this section, $G$ is a graph, properly drawn in $\Sigma$ with $$V(G) \cap
bd(\Sigma) = M_1 \cup M_2.$$" -/
def IsCylinderSection5Drawing (k : ℕ) (G : Drawing ClosedCylinder) : Prop :=
  0 < k ∧ G.IsProper ∧ G.V ∩ bd ClosedCylinder = cylinderM1 k ∪ cylinderM2 k

/-- A *linkage* $\mathcal{L} = \{P_1, \dots, P_k\}$ in $G$ on `ClosedCylinder` consists of $k$
pairwise disjoint path subdrawings of $G$, where for $1 \le i \le k$ the initial vertex of $P_i$ is
$s_i = (1, \frac{2i}{k}\pi) \in M_1$ and the terminal vertex lies in $M_2$.
Graph Minors VI, Section 5 (pages 127–128): "Let $\mathcal{L}$ be a set of $k$ paths drawn on
$\Sigma$, pairwise disjoint, and each with
an initial vertex in $M_1$ and a terminal vertex in $M_2$. We call such a set $\mathcal{L}$
a ... *linkage*. ... A linkage in $G$ is a linkage $\mathcal{L}$ every member of which is a
subgraph of $G$. ... Let $\mathcal{L} = \{P_1, \dots, P_k\}$, where for $1 \le i \le k$ the
initial vertex of $P_i$ is $$s_i = \left(1, \frac{2i}{k}\pi\right).$$" -/
structure CylinderLinkage (k : ℕ) (G : Drawing ClosedCylinder) where
  /-- The $k$ path subdrawings $P_1, \dots, P_k$ of $G$. -/
  pathDrawing : Fin k → Drawing ClosedCylinder
  /-- Continuous injections $f_i \colon [0, 1] \to \Sigma$ parameterizing $P_i$ from $s_i \in M_1$
  to $M_2$. -/
  curve : Fin k → Curve ClosedCylinder
  /-- Each $P_i$ is a subdrawing of $G$. -/
  isSubdrawing : ∀ i : Fin k, (pathDrawing i).IsSubdrawing G ∧ (pathDrawing i).U ⊆ G.U
  /-- Each $P_i$ is a path drawing from $s_i$ to `curve i 1`. -/
  isPath : ∀ i : Fin k, IsPathDrawing (pathDrawing i) (cylinderM1Point k i) (curve i 1)
  /-- Each `curve i` parameterizes `(pathDrawing i).U` from $s_i$ to `curve i 1`. -/
  curve_parametrizes : ∀ i : Fin k,
    ParametrizesSet (curve i) (pathDrawing i).U (cylinderM1Point k i) (curve i 1)
  /-- The terminal vertex of each $P_i$ lies in $M_2$. -/
  curve_one_mem : ∀ i : Fin k, curve i 1 ∈ cylinderM2 k
  /-- The paths $P_1, \dots, P_k$ are pairwise disjoint. -/
  pairwise_disjoint : Pairwise fun i j : Fin k => Disjoint (pathDrawing i).U (pathDrawing j).U

/-- A linkage $\mathcal{L}$ in $G$ has winding number $\theta(\mathcal{L}) = \theta$ if every path
$P_i$ of $\mathcal{L}$ has winding number $\theta$.
Graph Minors VI, Section 5 (page 128): "If $\mathcal{L}$ is a linkage then clearly $\theta(P)$ is
constant for $P \in \mathcal{L}$, and we denote this common value by $\theta(\mathcal{L})$." -/
def CylinderLinkage.HasTheta {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (θ : ℝ) : Prop :=
  ∀ i : Fin k, windingNumber (L.curve i) = θ

/-- A real number $\theta$ is *feasible* in $G$ if there is a linkage $\mathcal{L}$ in $G$ with
$\theta(\mathcal{L}) = \theta$.
Graph Minors VI, Section 5 (page 128): "If $\theta$ is a real number, we say that $\theta$ is
feasible in $G$ if there is a linkage $\mathcal{L}$ in $G$ with $\theta(\mathcal{L}) = \theta$." -/
def IsThetaFeasible (k : ℕ) (G : Drawing ClosedCylinder) (θ : ℝ) : Prop :=
  ∃ L : CylinderLinkage k G, L.HasTheta θ

/-- For $1 \le i \le k$, $\Sigma_i$ is the connected component of
$\Sigma \setminus (P_1 \cup \dots \cup P_k)$ containing $(1, \frac{2i+1}{k}\pi)$.
Graph Minors VI, Section 5 (page 128). -/
noncomputable def cylinderStrip {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (i : Fin k) : Set ClosedCylinder :=
  connectedComponentIn (Set.univ \ ⋃ j : Fin k, (L.pathDrawing j).U) (cylinderN1Point k i)

/-- For $1 \le i \le k$, $R_i$ is the region of $G$ containing $(1, \frac{2i+1}{k}\pi)$.
Graph Minors VI, Section 5 (page 128). -/
noncomputable def cylinderRegion (k : ℕ) (G : Drawing ClosedCylinder) (i : Fin k) :
    Set ClosedCylinder :=
  connectedComponentIn (Set.univ \ G.U) (cylinderN1Point k i)

/-- Cyclic predecessor $i - 1 \pmod k$ on `Fin k` ("Throughout the following, subscripts should be
read modulo $k$, so that $P_0$, for example, means $P_k$", Graph Minors VI, Section 5, page 128). -/
def finPredCycle {k : ℕ} (i : Fin k) : Fin k :=
  if _ : i.1 = 0 then ⟨k - 1, Nat.sub_lt i.pos zero_lt_one⟩
  else ⟨i.1 - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2⟩

/-- Cyclic successor $i + 1 \pmod k$ on `Fin k` (Graph Minors VI, Section 5, page 128). -/
def finSuccCycle {k : ℕ} (i : Fin k) : Fin k :=
  if h : i.1 + 1 < k then ⟨i.1 + 1, h⟩
  else ⟨0, i.pos⟩

/-- Radial-angular coordinates on the universal cover of the closed cylinder.
The radius lies in $[1,2]$, while the angle is a real number. -/
abbrev CylinderCover := Set.Icc (1 : ℝ) 2 × ℝ

/-- The universal covering projection $(r,a) \mapsto (r,\exp(a))$. -/
noncomputable def cylinderCoverProjection (p : CylinderCover) : ClosedCylinder :=
  ⟨(p.1.1, Circle.exp p.2), p.1.2, Set.mem_univ _⟩

/-- Lift a curve to radial-angular coordinates, with initial angle a.
When exp(a) is the angle of the curve's initial point, this is its
lift to the universal cover beginning on that sheet. -/
noncomputable def cylinderCurveLiftAt (f : Curve ClosedCylinder) (a : ℝ) :
    C(unitInterval, CylinderCover) :=
  ⟨fun t => (⟨(f t).1.1, (f t).2.1⟩,
    cylinderAngleLift f t + (a - cylinderAngleLift f 0)),
    (((continuous_fst.comp (continuous_subtype_val.comp f.continuous)).subtype_mk _).prodMk
      ((cylinderAngleLift f).continuous.add continuous_const))⟩

/-- The lift of the initial vertex $s_i$ at angle $2(i+1)\pi/k$.
The `Fin` index starts at zero, whereas the paper starts at one. -/
noncomputable def cylinderInitialLift (k : ℕ) (i : Fin k) : CylinderCover :=
  (⟨1, by norm_num⟩, 2 * ((i.val + 1 : ℕ) : ℝ) * π / k)

/-- The component between linkage lifts that contains the lifted initial
cuff point of angle $(2m+1)\pi/k$. This retains the side information lost
by projecting the two sides of a single linkage path onto one component. -/
noncomputable def cylinderCoverStrip {k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (m : ℤ) : Set CylinderCover :=
  connectedComponentIn
    (cylinderCoverProjection ⁻¹' (Set.univ \ ⋃ j : Fin k, (L.pathDrawing j).U))
    (⟨1, by norm_num⟩, (2 * (m : ℝ) + 1) * π / k)

/-- Side-sensitive form of the edge condition in Reduction 1, Graph Minors VI,
page 128. The edge has a connected lift in the preceding strip, whose
closure contains the chosen lift of $s_i$. For one path this distinguishes
the two sides of that path. See the correction to Reduction 1 and (5.5) in `corrections/GM06.md`. -/
def IsClockwiseInitialEdge {k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (i : Fin k) (e : Set ClosedCylinder) : Prop :=
  ∃ A : Set CylinderCover, IsConnected A ∧ cylinderCoverProjection '' A = e ∧
    cylinderInitialLift k i ∈ closure A ∧ A ⊆ cylinderCoverStrip L (i.val : ℤ)

/-- A *separation* of a graph $G$ is a pair $(G_1, G_2)$ of subgraphs of $G$ with
$V(G_1) \cup V(G_2) = V(G)$, $E(G_1) \cup E(G_2) = E(G)$, and $E(G_1) \cap E(G_2) = \emptyset$.
Graph Minors VI, Section 5 (page 128). -/
def IsGraphSeparation {α : Type u} {β : Type v} (G G₁ G₂ : Graph α β) : Prop :=
  G₁ ≤ G ∧ G₂ ≤ G ∧ V(G₁) ∪ V(G₂) = V(G) ∧ E(G₁) ∪ E(G₂) = E(G) ∧ Disjoint E(G₁) E(G₂)

/-- **Reduction 1** of Section 5 (Graph Minors VI, page 128):
"Delete any edge which for some $i$ is incident with $s_i$ and contained in $\Sigma_{i-1}$."
Incidence is taken on the clockwise side in the angular cover. This agrees
with the printed condition for k ≥ 2 and corrects it for one path (see
the correction to Reduction 1 and (5.5) in `corrections/GM06.md`). -/
def Section5Reduction1Step (k : ℕ) (G : Drawing ClosedCylinder) (L : CylinderLinkage k G)
    (G' : Drawing ClosedCylinder) (L' : CylinderLinkage k G') : Prop :=
  ∃ (i : Fin k) (e : Set ClosedCylinder),
    e ∈ G.E ∧ IsClockwiseInitialEdge L i e ∧
    G'.V = G.V ∧ G'.E = G.E \ {e} ∧ G'.U = G.U \ e ∧
    L'.pathDrawing = L.pathDrawing ∧ L'.curve = L.curve

/-- **Reduction 2** of Section 5 (Graph Minors VI, page 129):
"If there is a separation $(G_1, G_2)$ of $G$ with $V(G_1) \cap V(G_2) \subseteq \{s_i\}$ for some
$i$, and with $P_1, \dots, P_k$ all paths of $G_1 \ne G$, replace $G$ by $G_1$." -/
def Section5Reduction2Step (k : ℕ) (G : Drawing ClosedCylinder) (L : CylinderLinkage k G)
    (G' : Drawing ClosedCylinder) (L' : CylinderLinkage k G') : Prop :=
  ∃ (i : Fin k) (G₂ : Drawing ClosedCylinder),
    IsGraphSeparation G.toGraph G'.toGraph G₂.toGraph ∧
    G'.U ⊆ G.U ∧ G₂.U ⊆ G.U ∧
    G'.V ∩ G₂.V ⊆ {cylinderM1Point k i} ∧
    G'.toGraph ≠ G.toGraph ∧
    L'.pathDrawing = L.pathDrawing ∧ L'.curve = L.curve

/-- **Reduction 3** of Section 5 (Graph Minors VI, page 129):
"If some $s_i$ has valency 1 and its neighbour $v$ is not in $C_2$, contract the edge joining $s_i$
and $v$, moving $v$ in $\Sigma$ to $s_i$ along the edge." -/
def Section5Reduction3Step (k : ℕ) (G : Drawing ClosedCylinder) (L : CylinderLinkage k G)
    (G' : Drawing ClosedCylinder) (L' : CylinderLinkage k G') : Prop :=
  ∃ (i : Fin k) (e : Set ClosedCylinder) (v : ClosedCylinder)
    (π_map : C(ClosedCylinder, ClosedCylinder))
    (H_id : C(unitInterval × ClosedCylinder, ClosedCylinder)),
    vertexValency G.toGraph (cylinderM1Point k i) = 1 ∧
    e ∈ G.E ∧ v ∈ G.V ∧ v ≠ cylinderM1Point k i ∧ v ∉ cylinderCuff2 ∧
    G.toGraph.IsLink e (cylinderM1Point k i) v ∧
    (∀ p : ClosedCylinder, H_id (0, p) = p) ∧
    (∀ p : ClosedCylinder, H_id (1, p) = π_map p) ∧
    (∀ p ∈ bd ClosedCylinder, ∀ t : unitInterval, H_id (t, p) = p) ∧
    π_map ⁻¹' {cylinderM1Point k i} = closure e ∧
    Nonempty ({x : ClosedCylinder // x ∉ closure e} ≃ₜ
      {y : ClosedCylinder // y ≠ cylinderM1Point k i}) ∧
    (∀ x : ClosedCylinder, x ∉ closure e → ∀ y : ClosedCylinder, y ∉ closure e →
      π_map x = π_map y → x = y) ∧
    (∀ z : ClosedCylinder, z ≠ cylinderM1Point k i → ∃ x ∉ closure e, π_map x = z) ∧
    (∀ U_open : Set ClosedCylinder, IsOpen U_open → Disjoint U_open (closure e) →
      IsOpen (π_map '' U_open)) ∧
    G'.U = π_map '' G.U ∧
    G'.V = π_map '' G.V ∧
    G'.E = (fun e' => π_map '' e') '' (G.E \ {e}) ∧
    (∀ j : Fin k, (L'.pathDrawing j).U = π_map '' (L.pathDrawing j).U ∧
      CurvesHomotopic (L'.curve j) (π_map.comp (L.curve j))) ∧
    (∀ j : Fin k, j ≠ i → L'.pathDrawing j = L.pathDrawing j ∧ L'.curve j = L.curve j)

/-- The tail used in Reduction 4, possibly consisting of one vertex.
Graph Minors VI, page 129, uses the subpath between the contact vertex
and the terminal cuff. At a terminal contact this subpath is a singleton. -/
def IsSection5Tail (P T : Drawing ClosedCylinder) (v t : ClosedCylinder) : Prop :=
  (v = t ∧ T.U = {v} ∧ T.V = {v}) ∨ IsSubpathOf P T v t

/-- The region of the lifted drawing containing the gap immediately
counterclockwise from the chosen lift of sᵢ. Unlike its projected
region, it retains the side when there is only one linkage path. -/
noncomputable def cylinderCoverRegion (k : ℕ) (G : Drawing ClosedCylinder) (i : Fin k) :
    Set CylinderCover :=
  connectedComponentIn (cylinderCoverProjection ⁻¹' (univ \ G.U))
    (⟨1, by norm_num⟩, (2 * ((i.val + 1 : ℕ) : ℝ) + 1) * π / k)

/-- Lifted incidence data for the one-path correction of VI Reduction 4,
page 129. The old prefix fails incidence on the specified side,
while the new prefix is incident and reaches the same lifted contact.
The tail may be the singleton terminal vertex. -/
def Section5Reduction4SideCondition (k : ℕ) (G : Drawing ClosedCylinder)
    (L : CylinderLinkage k G) (G' : Drawing ClosedCylinder) (L' : CylinderLinkage k G') : Prop :=
  ∃ (i : Fin k) (u : unitInterval) (T Q : Drawing ClosedCylinder)
    (q : Curve ClosedCylinder),
    L.curve i u ∈ (L.pathDrawing i).V ∧
    cylinderCurveLiftAt (L.curve i) (cylinderInitialLift k i).2 u ∈
      closure (cylinderCoverRegion k G i) ∧
    ¬ (cylinderCurveLiftAt (L.curve i) (cylinderInitialLift k i).2 '' Icc 0 u ⊆
      closure (cylinderCoverRegion k G i)) ∧
    IsSection5Tail (L.pathDrawing i) T (L.curve i u) (L.curve i 1) ∧
    Q.IsSubdrawing G ∧ Q.U ⊆ G.U ∧
    IsPathDrawing Q (cylinderM1Point k i) (L.curve i u) ∧
    ParametrizesSet q Q.U (cylinderM1Point k i) (L.curve i u) ∧
    range (cylinderCurveLiftAt q (cylinderInitialLift k i).2) ⊆
      closure (cylinderCoverRegion k G i) ∧
    cylinderCurveLiftAt q (cylinderInitialLift k i).2 1 =
      cylinderCurveLiftAt (L.curve i) (cylinderInitialLift k i).2 u ∧
    (L'.pathDrawing i).U = Q.U ∪ T.U ∧
    (∀ j : Fin k, j ≠ i → L'.pathDrawing j = L.pathDrawing j ∧ L'.curve j = L.curve j)


/-- The region-incidence and path data in the printed Reduction 4,
Graph Minors VI, page 129. For at least two paths these are used
unchanged. For one path incidence must instead specify a lifted side. -/
def Section5Reduction4PrintedCondition (k : ℕ) (G : Drawing ClosedCylinder)
    (L : CylinderLinkage k G) (G' : Drawing ClosedCylinder) (L' : CylinderLinkage k G') : Prop :=
  ∃ (i : Fin k) (v : ClosedCylinder) (P_sv P_vt Q_i : Drawing ClosedCylinder),
    v ∈ (L.pathDrawing i).V ∧ v ∈ closure (cylinderRegion k G i) ∧
    IsSubpathOf (L.pathDrawing i) P_sv (cylinderM1Point k i) v ∧
    IsSection5Tail (L.pathDrawing i) P_vt v (L.curve i 1) ∧
    ¬ (P_sv.U ⊆ closure (cylinderRegion k G i)) ∧
    Q_i.IsSubdrawing G ∧ Q_i.U ⊆ G.U ∧ IsPathDrawing Q_i (cylinderM1Point k i) v ∧
    Q_i.U ⊆ closure (cylinderRegion k G i) ∧
    (L'.pathDrawing i).U = Q_i.U ∪ P_vt.U ∧
    (∀ j : Fin k, j ≠ i → L'.pathDrawing j = L.pathDrawing j ∧ L'.curve j = L.curve j)

/-- **Reduction 4** of Section 5 (Graph Minors VI, page 129):
"If for some $i$ there is a vertex $v$ of $P_i$ such that $v$ is incident with $R_i$, but not every
vertex and edge of $P_i$ between $s_i$ and $v$ is incident with $R_i$, let $Q_i$ be a path in $G$
between $s_i$ and $v$ such that every vertex and edge of it is incident with $R_i$, and replace
$P_i$ by the concatenation of $Q_i$ and the subpath of $P_i$ between $v$ and $C_2$."
The tail may be the one-vertex drawing when v is the terminal vertex.
For k ≥ 2 the printed condition is unchanged. For one path the chosen
lifted region and contact distinguish the side (see the correction to Reduction 4 and (5.6) in
`corrections/GM06.md`). -/
def Section5Reduction4Step (k : ℕ) (G : Drawing ClosedCylinder) (L : CylinderLinkage k G)
    (G' : Drawing ClosedCylinder) (L' : CylinderLinkage k G') : Prop :=
  G' = G ∧ ((1 < k ∧ Section5Reduction4PrintedCondition k G L G' L') ∨
    (k = 1 ∧ Section5Reduction4SideCondition k G L G' L'))

/-- $(G', \mathcal{L}')$ is produced from $(G, \mathcal{L})$ by one of Reductions 1, ..., 4 of
Section 5 (Graph Minors VI, pages 128–129). -/
def Section5ReductionStep (k : ℕ) (G : Drawing ClosedCylinder) (L : CylinderLinkage k G)
    (G' : Drawing ClosedCylinder) (L' : CylinderLinkage k G') : Prop :=
  Section5Reduction1Step k G L G' L' ∨
  Section5Reduction2Step k G L G' L' ∨
  Section5Reduction3Step k G L G' L' ∨
  Section5Reduction4Step k G L G' L'

/-- Whether any of Reductions 1, ..., 4 of Section 5 applies to $(G, \mathcal{L})$. -/
def Section5AnyReductionApplies (k : ℕ) (G : Drawing ClosedCylinder)
    (L : CylinderLinkage k G) : Prop :=
  ∃ (G' : Drawing ClosedCylinder) (L' : CylinderLinkage k G'),
    IsCylinderSection5Drawing k G' ∧ Section5ReductionStep k G L G' L'

/-- A continuous curve $f \colon [0, 1] \to \Sigma$ is *$G$-normal* if $e \cap |f| = \emptyset$ for
every edge $e$ of $G$, that is, $|f| \cap U(G) \subseteq V(G)$.
Graph Minors VI, Section 5 (page 129): "We say $f$ is *$G$-normal* if $e \cap |f| = \emptyset$ for
every edge $e$ of $G$; that is, every point of $|f|$ is either a vertex or lies in some region of
$G$." -/
def IsNormalCurve {S : Type u} [TopologicalSpace S] (G : Drawing S) (f : Curve S) : Prop :=
  G.IsNormal (Set.range f)

/-- The set $\{x \in [0, 1] : f(x) \in V(G)\}$ of parameter values at which a curve $f$ meets
$V(G)$.
Graph Minors VI, Section 5 (page 129). -/
def curveVertexHits {S : Type u} [TopologicalSpace S] (G : Drawing S)
    (f : Curve S) : Set unitInterval :=
  {x : unitInterval | f x ∈ G.V}

/-- For a $G$-normal curve $f$, $L_G(f) = |\{x \in [0, 1] : f(x) \in V(G)\}|$.
Graph Minors VI, Section 5 (page 129): "If $f$ is $G$-normal, we define $L(f) = L_G(f)$ to be $$|\{x
\in [0, 1]: f(x) \in V(G)\}|.$$" -/
noncomputable def curveL {S : Type u} [TopologicalSpace S] (G : Drawing S) (f : Curve S) : ℕ :=
  (curveVertexHits G f).ncard

/-- A continuous curve $f \colon [0, 1] \to \Sigma$ on `ClosedCylinder` is a *helix* (in $G$) if $f$
is $G$-normal, $f(0) \in N_1$, $f(1) \in N_2$, and $L_G(f)$ is finite.
Graph Minors VI, Section 5 (page 130): "If $f: [0, 1] \to \Sigma$ is continuous, $G$-normal, with
$f(0) \in N_1, f(1) \in N_2$ and
with $L_G(f)$ finite, we say $f$ is a *helix* (in $G$)." -/
def IsHelix (k : ℕ) (G : Drawing ClosedCylinder) (f : Curve ClosedCylinder) : Prop :=
  IsNormalCurve G f ∧ f 0 ∈ cylinderN1 k ∧ f 1 ∈ cylinderN2 k ∧ (curveVertexHits G f).Finite

/-- For a helix $f$ in $G$, $\phi_G(f) = \theta(f) + k^{-1} L_G(f)$.
Graph Minors VI, Section 5 (page 130): "We abbreviate $\theta(f) + k^{-1} L(f)$ by $\phi(f)$ or
$\phi_G(f)$." -/
noncomputable def curvePhi (k : ℕ) (G : Drawing ClosedCylinder) (f : Curve ClosedCylinder) : ℝ :=
  windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ)

/-- **Graph Minors VI, (5.1)** (page 129):
"Suppose that none of reductions 1, ..., 4 apply to $G$. Then either some $s_i$ has valency 1 and
its neighbour is in $C_2$, or $\theta(\mathcal{L}) + 1/k$ is feasible." -/
def Statement51 : Prop :=
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (L : CylinderLinkage k G) (θ : ℝ),
    IsCylinderSection5Drawing k G → L.HasTheta θ →
    ¬ Section5AnyReductionApplies k G L →
    (∃ i : Fin k, vertexValency G.toGraph (cylinderM1Point k i) = 1 ∧
      ∃ e ∈ G.E, ∃ t ∈ G.V ∩ cylinderCuff2, G.toGraph.IsLink e (cylinderM1Point k i) t) ∨
    IsThetaFeasible k G (θ + 1 / (k : ℝ))

/-- **Graph Minors VI, (5.2)** (page 130):
"Let $\theta$ be feasible in $G$, and let $f$ be a helix. Then $L(f) \ge k|\theta(f) -
\theta|$, that is,* $$\theta(f) - k^{-1}L(f) \le \theta \le \theta(f) + k^{-1}L(f).$$" -/
def Statement52 : Prop :=
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (θ : ℝ) (f : Curve ClosedCylinder),
    IsCylinderSection5Drawing k G → IsThetaFeasible k G θ → IsHelix k G f →
    windingNumber f - (k : ℝ)⁻¹ * (curveL G f : ℝ) ≤ θ ∧
      θ ≤ windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ)

/-- **Graph Minors VI, (5.3)** (page 130):
"If $\theta$ is feasible in $G$ and $\theta + 1/k$ is not, then there is a helix $f$ with
$\phi(f) = \theta$." -/
def Statement53 : Prop :=
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (θ : ℝ),
    IsCylinderSection5Drawing k G →
    IsThetaFeasible k G θ → ¬ IsThetaFeasible k G (θ + 1 / (k : ℝ)) →
    ∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f = θ

/-- **Graph Minors VI, (5.4)** (page 130):
"If $(G', \mathcal{L}')$ is produced from $(G, \mathcal{L})$ by one of the reductions 1, ..., 4, and
$\theta(\mathcal{L}') + 1/k$ is feasible in $G'$, then $\theta(\mathcal{L}) + 1/k$ is feasible in
$G$." -/
def Statement54 : Prop :=
  ∀ (k : ℕ) (G G' : Drawing ClosedCylinder) (L : CylinderLinkage k G)
    (L' : CylinderLinkage k G') (θ θ' : ℝ),
    IsCylinderSection5Drawing k G → IsCylinderSection5Drawing k G' →
    L.HasTheta θ → L'.HasTheta θ' →
    Section5ReductionStep k G L G' L' →
    IsThetaFeasible k G' (θ' + 1 / (k : ℝ)) →
    IsThetaFeasible k G (θ + 1 / (k : ℝ))

/-- **Graph Minors VI, (5.5)** (page 130):
"If $(G', \mathcal{L}')$ is produced from $(G, \mathcal{L})$ by one of the reductions 1, ..., 4, and
$f'$ is a helix in $G'$ then there is a helix $f$ in $G$ with $\phi_G(f) \le \phi_{G'}(f')$." -/
def Statement55 : Prop :=
  ∀ (k : ℕ) (G G' : Drawing ClosedCylinder) (L : CylinderLinkage k G)
    (L' : CylinderLinkage k G') (f' : Curve ClosedCylinder),
    IsCylinderSection5Drawing k G → IsCylinderSection5Drawing k G' →
    Section5ReductionStep k G L G' L' →
    IsHelix k G' f' →
    ∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f ≤ curvePhi k G' f'

/-- **Graph Minors VI, (5.6)** (page 133):
"If $(G', \mathscr{L}')$ is produced from $(G, \mathscr{L})$ by one of the reductions 1,...,
4, then $\theta(\mathscr{L}') + 1/k$ is feasible in $G'$ if and only if $\theta(\mathscr{L})
+ 1/k$ is feasible in $G$." -/
def Statement56 : Prop :=
  ∀ (k : ℕ) (G G' : Drawing ClosedCylinder) (L : CylinderLinkage k G)
    (L' : CylinderLinkage k G') (θ θ' : ℝ),
    IsCylinderSection5Drawing k G → IsCylinderSection5Drawing k G' →
    L.HasTheta θ → L'.HasTheta θ' →
    Section5ReductionStep k G L G' L' →
    (IsThetaFeasible k G' (θ' + 1 / (k : ℝ)) ↔ IsThetaFeasible k G (θ + 1 / (k : ℝ)))

/-- **Graph Minors VI, (5.8)** (page 133):
"If $\theta$ is feasible in $G$, the following are equivalent:
(i) there is a helix $f$ in $G$ with $\phi(f) = \theta$
(ii) $\theta + 1/k$ is not feasible
(iii) no $\theta' > \theta$ is feasible." -/
def Statement58 : Prop :=
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (θ : ℝ),
    IsCylinderSection5Drawing k G → IsThetaFeasible k G θ →
    (((∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f = θ) ↔
        ¬ IsThetaFeasible k G (θ + 1 / (k : ℝ))) ∧
     (¬ IsThetaFeasible k G (θ + 1 / (k : ℝ)) ↔
        ∀ θ' : ℝ, θ < θ' → ¬ IsThetaFeasible k G θ'))

/-- **Graph Minors VI, (5.9)** (page 134):
"If $\theta_1 \le \theta_2 \le \theta_3$ and $\theta_1, \theta_3$ are feasible in $G$ and
$k\theta_2$
is an integer, then $\theta_2$ is feasible in $G$." -/
def Statement59 : Prop :=
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (θ₁ θ₂ θ₃ : ℝ),
    IsCylinderSection5Drawing k G →
    θ₁ ≤ θ₂ → θ₂ ≤ θ₃ →
    IsThetaFeasible k G θ₁ → IsThetaFeasible k G θ₃ →
    (∃ m : ℤ, (k : ℝ) * θ₂ = m) →
    IsThetaFeasible k G θ₂

/-- **Graph Minors VI, (5.10)** (page 134):
"$\theta$ is feasible in $G$ if and only if
(i) $k\theta$ is an integer;
(ii) there is some linkage in $G$; and
(iii) for every helix $f$, $\theta(f) - k^{-1} L(f) \le \theta \le \theta(f) + k^{-1} L(f)$." -/
def Statement510 : Prop :=
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (θ : ℝ),
    IsCylinderSection5Drawing k G →
    (IsThetaFeasible k G θ ↔
      (∃ m : ℤ, (k : ℝ) * θ = m) ∧
      Nonempty (CylinderLinkage k G) ∧
      ∀ f : Curve ClosedCylinder, IsHelix k G f →
        windingNumber f - (k : ℝ)⁻¹ * (curveL G f : ℝ) ≤ θ ∧
          θ ≤ windingNumber f + (k : ℝ)⁻¹ * (curveL G f : ℝ))

/-- **Graph Minors VI, (5.12)** (page 135):
"If $\theta_1, \theta_2$ are both feasible in $G$ then* $$|\theta_1 - \theta_2| \le
\frac{1}{k^2} |V(G)|.$$" -/
def Statement512 : Prop :=
  ∀ (k : ℕ) (G : Drawing ClosedCylinder) (θ₁ θ₂ : ℝ),
    IsCylinderSection5Drawing k G →
    IsThetaFeasible k G θ₁ → IsThetaFeasible k G θ₂ →
    |θ₁ - θ₂| ≤ (1 / ((k : ℝ) ^ 2)) * (G.V.ncard : ℝ)

end GraphMinor.GM06
