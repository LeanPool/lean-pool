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

This file defines the divisions, dual drawings, and chains used in Sections 1–3 of
N. Robertson and P. D. Seymour, *Graph Minors. VI. Disjoint paths across a disc*,
J. Combin. Theory Ser. B **41** (1986), 115–138. It also defines graph separations
from Section 5, used by the society results of Graph Minors IX.

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
    $\Delta(x, y)$ (`divisionCount`), and the statements of (2.1)–(2.4).
- **Section 3 (pages 119–122):**
  - Closed disc spaces (`IsClosedDiscSpace`), dual drawings $G^*$ on a closed disc
    (`IsDiscDualDrawing`), peripheral vertices and regions (`ChainTerm`, `ChainTerm.IsPeripheral`),
    $(x, y)$-chains (`IsXYChain`), chain length (`chainLength`), $\Delta$-redundancy
    (`chainRedundancy`), and the statements of (3.1)–(3.3), (3.5), and (3.6).
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

/-! ## Graph separations -/

/-- A *separation* of a graph $G$ is a pair $(G_1, G_2)$ of subgraphs of $G$ with
$V(G_1) \cup V(G_2) = V(G)$, $E(G_1) \cup E(G_2) = E(G)$, and $E(G_1) \cap E(G_2) = \emptyset$.
Graph Minors VI, Section 5 (page 128). -/
def IsGraphSeparation {α : Type u} {β : Type v} (G G₁ G₂ : Graph α β) : Prop :=
  G₁ ≤ G ∧ G₂ ≤ G ∧ V(G₁) ∪ V(G₂) = V(G) ∧ E(G₁) ∪ E(G₂) = E(G) ∧ Disjoint E(G₁) E(G₂)

end GraphMinor.GM06
