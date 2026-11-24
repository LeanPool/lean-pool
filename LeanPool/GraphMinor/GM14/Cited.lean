/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.Surface.TopologyStatements

/-!
# Results cited in Graph Minors XIV

This file states as `Prop`s the results from other papers of the series and external theorems that
are cited in *Graph Minors. XIV. Extending an embedding* (JCTB 65 (1995) 23–50) and are proved in
parallel tracks:

* `GM07Theorem42Statement`: Graph Minors VII, (4.2) (page 222), used in Section 9 (page 43).
* `GM07Theorem119Statement`: Graph Minors VII, (11.9) (page 253), used in Section 9 (page 43).
* `GM09Theorem91Statement`: Graph Minors IX, (9.1) (page 62), used in Section 8 (page 42).
* `GM09Theorem104Statement`: Graph Minors IX, (10.4) (page 65), used in Section 8 (page 40).
* `GM11Theorem63Statement`: Graph Minors XI, (6.3) (page 89), used in Section 7 (page 36).
* `GM11Theorem810Statement`: Graph Minors XI, (8.10) (page 100), used in Section 9 (pages 43–44).
* `GM11Theorem812Statement`: Graph Minors XI, (8.12) (page 102), used in Section 7 (page 35).
* `GM12Theorem710Statement`: Graph Minors XII, (7.10) (page 270), which gives (3.2) of XIV
  (page 28).
* `WhitneyPlanarUniquenessStatement`: Whitney's theorem on uniqueness of embeddings of subdivisions
  of simple 3-connected graphs in the 2-sphere, used in the proof of (6.4) (page 34).
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  Hypergraph

universe u v

/-- Statement of Graph Minors VII, (4.2) (page 222):
"Let $\Sigma$ be a connected surface with $bd(\Sigma) = \emptyset$, and let $Y \subseteq
\Sigma$ be connected and open. Suppose that every $O$-arc included in $Y$ bounds a disc
included in $Y$. Then either $\Sigma$ is a sphere and $Y = \Sigma$, or $Y$ is an open disc." -/
def GM07Theorem42Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ Y : Set S, IsConnected Y → IsOpen Y →
      (∀ F : Set S, IsOArc F → F ⊆ Y → ∃ Δ : Set S, IsClosedDisc Δ ∧ subBd Δ = F ∧ Δ ⊆ Y) →
      (IsSphere S ∧ Y = univ) ∨ IsOpenDisc Y

/-- Statement of Graph Minors VII, (11.9) (page 253):
"If $\Sigma$ is connected and $Z \subseteq \Sigma$ is flat and l.a.c., and either $Z$ is
closed or $Z$ is arc-connected, then there is an open simply connected subset $Y \subseteq
\Sigma$ with $Z \subseteq Y$." -/
def GM07Theorem119Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∀ Z : Set S, IsFlat Z → IsLocallyArcConnected Z →
      (IsClosed Z ∨ IsArcConnected Z) →
      ∃ Y : Set S, IsOpen Y ∧ IsArcSimplyConnected Y ∧ Z ⊆ Y

/-- Statement of Graph Minors IX, (9.1) (page 62):
"If the composition of a society $(G, \Omega)$ with some rural neighborhood has a crooked
transaction of cardinality $\ge p$, then so does $(G, \Omega)$." -/
def GM09Theorem91Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (S_comp S : Society α β) (N : Neighborhood α β)
    (p : ℕ) (P_set : Set (Graph α β)),
    N.IsRural → S_comp.IsComposition S N →
    S_comp.IsCrookedTransaction P_set → p ≤ P_set.ncard →
    ∃ P_set' : Set (Graph α β), S.IsCrookedTransaction P_set' ∧ p ≤ P_set'.ncard

/-- Statement of Graph Minors IX, (10.4) (page 65):
"Let $p \ge 2$ with $p \ne 3$. Let $(G, \Omega, \Omega_0)$ be a rural neighborhood of breadth
$\ge p + 5$, and let $X \subseteq \bar{\Omega}$ be linked with $|X| \ge 2p + 8$. Let $(G
\cup G_0, \Omega)$ be the composition of some society $(G_0, \Omega_0)$ with $(G, \Omega,
\Omega_0)$, and suppose that there is a crooked transaction $\mathscr{P}$ in $(G \cup G_0,
\Omega)$ with $|\mathscr{P}| \ge p$. Then $\mathscr{P}$ may be chosen with $V(\mathscr{P})
\subseteq X$ and such that no member of $\mathscr{P}$ has any internal vertex in
$\bar{\Omega}$." -/
def GM09Theorem104Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (S_comp S₀ : Society α β) (N : Neighborhood α β)
    (p : ℕ) (X : Set α) (P_set : Set (Graph α β)),
    2 ≤ p → p ≠ 3 →
    N.IsRural → N.HasBreadthGe (p + 5) →
    N.IsLinked X → 2 * p + 8 ≤ X.ncard →
    S_comp.IsComposition S₀ N →
    S_comp.IsCrookedTransaction P_set → p ≤ P_set.ncard →
    ∃ P_set' : Set (Graph α β),
      S_comp.IsCrookedTransaction P_set' ∧ p ≤ P_set'.ncard ∧
      S_comp.transactionEnds P_set' ⊆ X ∧
      ∀ P ∈ P_set', Disjoint (pathInternalVerts S_comp.G P) S_comp.Ω.bar

/-- Statement of Graph Minors XI, (6.3) (page 89):
"Let $\Gamma$ be a 2-cell painting or drawing in a connected surface $\Sigma$ with $E(\Gamma)
\ne \emptyset$, and let $\mathscr{T}$ be a respectful pretangle in $\Gamma$ of order $\theta
\ge 1$. Let $\Gamma'$ be a radial drawing of $\Gamma$, and let $ins$ be the derived slope.
Then for every separation $(A, B)$ of $\Gamma$ of order $< \theta$, the following are
equivalent:* (i) $(A, B) \in \mathscr{T}$ (ii) *there are circuits $C_1, \dots, C_k$ of
$\Gamma'$ with $V(C_i) \cap V(\Gamma) \subseteq V(A \cap B)$ ($1 \le i \le k$), such that
every edge of $A$ is a subset of one of $ins(C_1), \dots, ins(C_k)$.* *In particular,
$\mathscr{T}$ is the pretangle induced from $ins$." -/
def GM11Theorem63Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ (Γ : PaintingOrDrawing S) (Γ' : Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (ins : Drawing S → Set S),
      Γ.IsTwoCell → Γ.E.Nonempty → IsPretangle Γ.toHypergraph θ T → Γ.IsRespectful θ T →
      Γ.IsRadialDrawing Γ' → IsDerivedSlope Γ Γ' θ T ins →
      (∀ A B : Hypergraph S (Set S), Γ.toHypergraph.IsSeparation A B → separationOrder A B < θ →
        ((A, B) ∈ T ↔
          ∃ (k : ℕ) (C : Fin k → Drawing S),
            (∀ i : Fin k, (C i).IsCircuit ∧ (C i).IsSubdrawing Γ' ∧ (C i).length < 2 * θ ∧
              (C i).V ∩ Γ.V ⊆ (A ∩ B).vertexSet) ∧
            ∀ e ∈ A.edgeSet, ∃ i : Fin k, e ⊆ ins (C i))) ∧
      T = inducedPretangle Γ Γ' θ ins

/-- Statement of Graph Minors XI, (8.10) (page 100):
"Let $c \in \Sigma$, let $0 \le k < 2\theta$, and let $Z$ be the union of all restraints $X$
with $l(X) \le k$ and $c \in X$. Then $Z$ is simply-connected."
The paper allows `Z = ∅` (see the proof of (8.12)), but `IsSimplyConnectedSet` needs a point, so `Z`
is
assumed non-empty here. For `Z = ∅` the `Prop` would be false: take one vertex in the sphere, no
edges,
`k = 0`, and `c` not that vertex. -/
def GM11Theorem810Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ (Γ : Drawing S) (two_theta : ℕ) (ins : Drawing S → Set S),
      IsSlope Γ two_theta ins →
      ∀ (c : S) (k : ℕ), k < two_theta →
        (⋃ X ∈ {X : Set S | IsRestraint Γ ins two_theta X ∧
          perimeterWalkLength Γ X ≤ k ∧ c ∈ X}, X).Nonempty →
        IsSimplyConnectedSet
          (⋃ X ∈ {X : Set S | IsRestraint Γ ins two_theta X ∧
            perimeterWalkLength Γ X ≤ k ∧ c ∈ X}, X)

/-- Statement of Graph Minors XI, (8.12) (page 102):
"If $c \in \Sigma$, there is a region $r$ of $\Gamma$ such that there is no restraint $X$
with $c \in X$ and $r \subseteq X$." -/
def GM11Theorem812Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ (Γ : Drawing S) (two_theta : ℕ) (ins : Drawing S → Set S),
      IsSlope Γ two_theta ins →
      ∀ c : S, ∃ r ∈ Γ.R, ∀ X : Set S, IsRestraint Γ ins two_theta X → ¬ (c ∈ X ∧ r ⊆ X)

/-- The conclusion of Graph Minors XII, (7.10) for `(T', d')` in `Γ'`. -/
def IsClearedTangleAux {S : Type u} [TopologicalSpace S] [T1Space S]
    (Γ Γ' : Drawing S)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (θ k : ℕ)
    (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d' : Set S → Set S → ℕ) : Prop :=
  HasTangleMetric Γ' (θ - 4 * k - 2) T' d' ∧
  (∀ A B : Hypergraph S (Set S),
    (A, B) ∈ T → separationOrder A B < θ - 4 * k - 2 →
      (A ∩ Γ'.toHypergraph, B ∩ Γ'.toHypergraph) ∈ T') ∧
  (∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
    a ⊆ a' → b ⊆ b' → d a b - 4 * k - 2 ≤ d' a' b' ∧ d' a' b' ≤ d a b)

/-- Statement of Graph Minors XII, (7.10) (pages 270–271):
"Let $k \ge 0$ be an integer, and let $\mathscr{T}$ be a respectful tangle of order $\ge 4k + 3$ in
a 2-cell drawing $\Gamma$ in a connected surface $\Sigma$. Let its metric be $d$. Let $c \in
A(\Gamma)$, and let $\Gamma'$ be a 2-cell subdrawing of $\Gamma$ such that $d(c, e) \le k$ for all
$e \in E(\Gamma) - E(\Gamma')$, and such that if $c \in E(\Gamma) - E(\Gamma')$ then ... $k \ge 2$.
Then there is a respectful tangle $\mathscr{T}'$ of order $\theta - 4k - 2$ in $\Gamma'$, with
metric $d'$, such that $d'(a', b') \ge d(a, b) - 4k - 2$ for all $a, b \in A(\Gamma)$ and $a', b'
\in A(\Gamma')$ with $a \subseteq a'$ and $b \subseteq b'$. Moreover,
(i) $\mathscr{T}'$ is unique
(ii) $(A \cap \Gamma', B \cap \Gamma') \in \mathscr{T}'$ for all $(A, B) \in \mathscr{T}$ of order
$< \theta - 4k - 2$,
(iii) $d'(a', b') \le d(a, b)$ for all $a, b \in A(\Gamma)$ and $a', b' \in A(\Gamma')$ with $a
\subseteq a'$ and $b \subseteq b'$." -/
def GM12Theorem710Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ (Γ Γ' : Drawing S) (θ k : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (c : Set S),
      4 * k + 3 ≤ θ →
      HasTangleMetric Γ θ T d →
      c ∈ Γ.A →
      Γ'.IsSubdrawing Γ →
      (PaintingOrDrawing.drawing Γ').IsTwoCell →
      (∀ e ∈ Γ.E \ Γ'.E, d c e ≤ k) →
      (c ∈ Γ.E \ Γ'.E → 2 ≤ k) →
      (∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S → Set S → ℕ),
        IsClearedTangleAux Γ Γ' T d θ k T' d' ∧
        ∀ (T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d'' : Set S → Set S → ℕ),
          HasTangleMetric Γ' (θ - 4 * k - 2) T'' d'' →
          (∀ a ∈ Γ.A, ∀ b ∈ Γ.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
            a ⊆ a' → b ⊆ b' → d a b - 4 * k - 2 ≤ d'' a' b') →
          T'' = T')

/-- Whitney's theorem on uniqueness of planar embeddings of subdivisions of simple 3-connected
graphs, as used in the proof of Graph Minors XIV, (6.4) (page 34): any two drawings in a sphere of a
graph `J` which is a subdivision of a simple 3-connected graph are related by a homeomorphism of the
sphere extending the graph isomorphism on vertices and edges. -/
def WhitneyPlanarUniquenessStatement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsSurface S → IsSphere S →
    ∀ (J₁ J₂ : Drawing S),
      IsSubdivisionOfSimpleThreeConnected J₁.toGraph →
      ∀ φ_iso : Iso J₁.toGraph J₂.toGraph,
        ∃ h : S ≃ₜ S,
          (∀ v : V(J₁.toGraph), h v.1 = (φ_iso.vertexEquiv v).1) ∧
          (∀ e : E(J₁.toGraph), h '' e.1 = (φ_iso.edgeEquiv e).1)

end GraphMinor.GM14
