/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.GM17.Defs
public import LeanPool.GraphMinor.Minor.Model
public import LeanPool.GraphMinor.Surface.TopologyStatements

/-!
# Definitions for Graph Minors XV (Giant Steps)

This file formalizes the definitions introduced in N. Robertson and P. D. Seymour,
*Graph Minors. XV. Giant steps*, J. Combin. Theory Ser. B 68 (1996) 112–148.

Shared definitions from Graph Minors IX, X, XI, and XIV are imported from
`GraphMinor.GM09.Defs`, `GraphMinor.GM10.Defs`, `GraphMinor.GM10.Defs2`,
`GraphMinor.GM11.Defs`, and `GraphMinor.GM14.Defs`:
- **Societies and transactions (`GM09`):** `CyclicPerm`, `Society`, `Society.IsTransaction`,
  `Society.IsCrookedTransaction`, `Society.IsCrosscapTransaction`, `Society.IsLeapTransaction`,
  `Society.IsDoublecrossTransaction`, `Society.IsLinearDecomposition`,
  `Society.HasLinearDecompositionOfDepthLE`, `IsFeasibleSegregation`.
- **Tangles (`GM10`):** `GM10.IsTangle`, `GM10.truncation`, `GM10.inducedTangle`,
  `GM10.deleteVerticesTangle`, `GM10.IsFreeSet`.
- **Drawings, metrics, zones, segregations, and arrangements (`GM14`):**
  `IsRespectfulDrawingTangle`, `tangleMetric`, `HasTangleMetric`, `IsLambdaZoneAround`,
  `IsLambdaZone`, `clearedSubdrawing`, `IsClearedTangle`, `IsHPathWithEnds`, `IsHPath`,
  `OccurInCircuitOrder`, `SpanEmbedding`, `IsDrawingEye`, `IsDial`, `IsRigid`,
  `IsNaturalOrderFrom`, `IsGraphSegregation`, `segregationVertices`, `IsThreeSegregation`,
  `IsSurfaceArrangement`, `IsCompatibleWith`, `IsTangleLocal`, `IsBridge`,
  `IsArrangementNormal`, `IsPullbackPerm`, `arrangementPullbackGraph`.

The definitions new to Graph Minors XV are:
- **Section 1 (pages 113–115):**
  - `Society.IsPVortex` (`IsPVortex`): a `p`-vortex is a society with no transaction of
    cardinality `> p`.
  - `IsSegregationOfType`: a segregation of `G` of type `(p, κ)`.
  - `IsGraphTangle`: a tangle of order `θ` in a finite graph `G` (via `Hypergraph.ofGraph`).
  - `IsCentralSegregation`: a `T*`-central segregation of `G`.
  - `IsRestrictedSeparation`, `IsControllingTangle`, `IsSigmaSpan`: `Σ`-spans `H, η, T` of order
    `θ` in `G` with respect to `T*`.
  - `pointAtomDist`, `pointDist`: point-to-atom and point-to-point tangle distances `d(σ, b)` and
    `d(σ₁, σ₂)`.
  - `IsLambdaCompression`: a `λ`-compression `T'` of `T` in `H'`.
  - `IsRearrangedWithin`: a `Σ`-span `H', η', T'` obtained from `H, η, T` by rearranging within `λ`
    of `z ∈ A(H)`.
  - `IsMuStepped`, `IsMuSteppedSpan`, `IsFlatSpan`: `μ`-stepped `H`-paths, `μ`-stepped `Σ`-spans,
    and `(λ, μ)`-flat `Σ`-spans.
  - `IsEyeWithPaths`, `IsEye`, `HasEyesAtDistance`, `HasIndependentEyes`: eyes and independent eyes
    of a `Σ`-span.
  - `IsObtainedByAddingCrosscap`: a surface obtained by adding a crosscap to `Σ`.
- **Section 3 (page 118):**
  - `IsObtainedByAddingHandle`: a surface obtained by adding a handle to `Σ`.
- **Section 4 (page 125):**
  - `deleteAtomNeighborhood`: the subdrawing `H - z^λ` formed by edges at distance `> λ` from `z`
    and their ends.
- **Section 8 (pages 145–146):**
  - `ControlsCliqueMinor`: a tangle `T*` controlling a `K_p`-minor of `G`.
  - `IsLevelSpan`: a `(λ, μ)`-level `Σ`-span.
-/

@[expose] public section

namespace GraphMinor

open Set Function TopologicalSpace Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Section 1: Vortices, Segregations, `Σ`-Spans, Compression, Flatness, and Eyes -/

/-- A society `(G, Ω)` is a `p`-vortex (Graph Minors XV, Section 1, page 114):
"For $\rho \ge 0$, a $\rho$-vortex is a society with no transaction of cardinality $> \rho$." -/
def GM09.Society.IsPVortex (S : Society α β) (p : ℕ) : Prop :=
  ∀ ⦃P_set : Set (Graph α β)⦄, S.IsTransaction P_set → P_set.ncard ≤ p

namespace GM15

export GM09.Society (IsPVortex)

/-- A segregation `S_seg` of a graph `G` is of type `(p, κ)`
(Graph Minors XV, Section 1, page 114):
"A segregation $\mathscr{S}$ of a graph $G$ is of type $(\rho, \kappa)$, where $\rho, \kappa \ge 0$
are integers, if there are at most $\kappa$ members $(A, \Omega) \in \mathscr{S}$ with
$|\bar{\Omega}| > 3$, and each is a $\rho$-vortex." -/
structure IsSegregationOfType (G : Graph α β) (p κ : ℕ) (S_seg : Set (Society α β)) : Prop where
  /-- `S_seg` is a segregation of `G`. -/
  isSegregation : IsGraphSegregation G S_seg
  /-- At most `κ` members `(A, Ω) ∈ S_seg` satisfy `|ΩBar| > 3`. -/
  vortex_count_le : {S ∈ S_seg | 3 < S.Ω.bar.ncard}.ncard ≤ κ
  /-- Every member `(A, Ω) ∈ S_seg` with `|ΩBar| > 3` is a `p`-vortex. -/
  is_p_vortex : ∀ ⦃S : Society α β⦄, S ∈ S_seg → 3 < S.Ω.bar.ncard → S.IsPVortex p

/-- `T` is a tangle of order `θ` in a finite graph `G`, viewed as a hypergraph via
`Hypergraph.ofGraph` (Graph Minors X, Section 1, page 154; Graph Minors XV, Section 1, page 113). -/
structure IsGraphTangle (G : Graph α β) (θ : ℕ)
    (T : Set (Hypergraph α β × Hypergraph α β)) : Prop where
  /-- `V(G)` is finite. -/
  finite_V : V(G).Finite
  /-- `E(G)` is finite. -/
  finite_E : E(G).Finite
  /-- `T` is a tangle of order `θ` in `Hypergraph.ofGraph G`. -/
  isTangle : GM10.IsTangle (Hypergraph.ofGraph G finite_V finite_E) θ T

/-- A subhypergraph `B` of `Hypergraph.ofGraph G` is contained in a subgraph `A ≤ G`:
`V(B) ⊆ V(A)` and `E(B) ⊆ E(A)`. -/
def SubhypergraphInGraph (B : Hypergraph α β) (A : Graph α β) : Prop :=
  B.vertexSet ⊆ V(A) ∧ B.edgeSet ⊆ E(A)

/-- A segregation `S_seg` of `G` is `T*`-central (Graph Minors XV, Section 1, page 114):
"If $\mathscr{T}^*$ is a tangle in $G$, a segregation $\mathscr{S}$ of $G$ is
$\mathscr{T}^*$-central if for each $(A, \Omega) \in \mathscr{S}$ there is no $(A^*, B^*)
\in \mathscr{T}^*$ with $B^* \subseteq A$." -/
def IsCentralSegregation (G : Graph α β)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (S_seg : Set (Society α β)) : Prop :=
  IsGraphSegregation G S_seg ∧
    ∀ ⦃S : Society α β⦄, S ∈ S_seg →
      ∀ ⦃A_star B_star : Hypergraph α β⦄, (A_star, B_star) ∈ T_star →
        ¬ SubhypergraphInGraph B_star S.G

/-- Given an embedding `η` of a drawing `H` as a subgraph `η(H) ≤ G` and a separation `(A, B)` of
`G`, `(A_H, B_H)` is the restricted separation `(η⁻¹(A ∩ η(H)), η⁻¹(B ∩ η(H)))` of `H`
(Graph Minors XV, Section 1, page 114). -/
def IsRestrictedSeparation {S : Type w} [TopologicalSpace S]
    (H : Drawing S) (G : Graph α β) (η : SpanEmbedding H G)
    (A B : Hypergraph α β) (A_H B_H : Hypergraph S (Set S)) : Prop :=
  H.toHypergraph.IsSeparation A_H B_H ∧
    η.vMap '' A_H.vertexSet = A.vertexSet ∩ V(η.imageGraph) ∧
    η.eMap '' A_H.edgeSet = A.edgeSet ∩ E(η.imageGraph) ∧
    η.vMap '' B_H.vertexSet = B.vertexSet ∩ V(η.imageGraph) ∧
    η.eMap '' B_H.edgeSet = B.edgeSet ∩ E(η.imageGraph)

/-- Condition (iv) in the definition of a `Σ`-span (Graph Minors XV, Section 1, page 114):
"$\theta \le ord(\mathscr{T}^*)$, and $(A \cap \eta(H), B \cap \eta(H)) \in
\eta(\mathscr{T})$, for every $(A, B) \in \mathscr{T}^*$ of order $< \theta$." -/
structure IsControllingTangle {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) : Prop where
  /-- `θ ≤ ord(T*)`. -/
  theta_le : θ ≤ θ_star
  /-- `T*` is a tangle in `G` of order `θ_star`. -/
  isTangle_star : IsGraphTangle G θ_star T_star
  /-- `T` is a tangle in `H` of order `θ`. -/
  isTangle_H : GM10.IsTangle H.toHypergraph θ T
  /-- For every `(A, B) ∈ T*` of order `< θ` (and thus for every separation `(A, B)` of `G` of
  order `< θ`), `(A, B) ∈ T*` if and only if `(η⁻¹(A ∩ η(H)), η⁻¹(B ∩ η(H))) ∈ T`. -/
  controls : ∀ ⦃A B : Hypergraph α β⦄,
    (Hypergraph.ofGraph G isTangle_star.finite_V isTangle_star.finite_E).IsSeparation A B →
    separationOrder A B < θ →
    ∀ ⦃A_H B_H : Hypergraph S (Set S)⦄,
      IsRestrictedSeparation H G η A B A_H B_H →
      ((A, B) ∈ T_star ↔ (A_H, B_H) ∈ T)

/-- A triple `H, η, T` is a `Σ`-span of order `θ` in `G` with respect to `T*`
(Graph Minors XV, Section 1, page 114):
"Let $\mathscr{T}^*$ be a tangle in $G$, and let $\Sigma$ be a surface with $bd(\Sigma) =
\emptyset$. A triple $H, \eta, \mathscr{T}$ is a $\Sigma$-span of order $\theta$ (in $G$,
with respect to $\mathscr{T}^*$) if (i) $H$ is a rigid drawing in $\Sigma$ (ii) $\eta$ is an
isomorphism from $H$ to a subgraph $\eta(H)$ of $G$ (iii) $\mathscr{T}$ is a respectful
tangle in $H$ of order $\theta$ (iv) $\theta \le ord(\mathscr{T}^*)$, and $(A \cap \eta(H),
B \cap \eta(H)) \in \eta(\mathscr{T})$, for every $(A, B) \in \mathscr{T}^*$ of order $<
\theta$." -/
structure IsSigmaSpan {S : Type w} [TopologicalSpace S] [T2Space S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) : Prop where
  /-- `Σ` is a surface. -/
  isSurface : IsSurface S
  /-- `Σ` is connected. -/
  isConnected : ConnectedSpace S
  /-- `bd(Σ) = ∅`. -/
  bd_empty : bd S = ∅
  /-- `(i)` `H` is a rigid drawing in `Σ`. -/
  isRigid : IsRigid H
  /-- `(iii)` `T` is a respectful tangle in `H` of order `θ`. -/
  isRespectful : IsRespectfulDrawingTangle H θ T
  /-- `(iv)` `θ ≤ ord(T*)` and `T*` controls `T` via `η`. -/
  isControlling : IsControllingTangle G H η θ_star θ T_star T

/-- Point-to-atom distance `d(σ, b)` for `σ ∈ Σ` and `b ∈ A(H)`
(Graph Minors XV, Section 1, page 114):
"If $H$ is a 2-cell drawing in $\Sigma$, and $\mathscr{T}$ is a respectful tangle in $H$ with
metric $d$, then for $\sigma \in \Sigma$ and $b \in A(H)$, we define $d(\sigma, b) = d(a,
b)$ where $\sigma \in a \in A(H)$; and for $\sigma_1, \sigma_2 \in \Sigma$ we define
$d(\sigma_1, \sigma_2) = d(a_1, a_2)$ where $\sigma_1 \in a_1 \in A(H)$ and $\sigma_2 \in
a_2 \in A(H)$." -/
noncomputable def pointAtomDist {S : Type w} [TopologicalSpace S]
    (H : Drawing S) (d : Set S → Set S → ℕ) (σ : S) (b : Set S) : ℕ :=
  sInf {k : ℕ | ∃ a ∈ H.A, σ ∈ a ∧ d a b = k}

/-- Point-to-point distance `d(σ₁, σ₂)` for `σ₁, σ₂ ∈ Σ`
(Graph Minors XV, Section 1, page 114). -/
noncomputable def pointDist {S : Type w} [TopologicalSpace S]
    (H : Drawing S) (d : Set S → Set S → ℕ) (σ₁ σ₂ : S) : ℕ :=
  sInf {k : ℕ | ∃ a₁ ∈ H.A, ∃ a₂ ∈ H.A, σ₁ ∈ a₁ ∧ σ₂ ∈ a₂ ∧ d a₁ a₂ = k}

/-- `T'` is a `λ`-compression of `T` in `H'` (Graph Minors XV, Section 1, page 114):
"If $H'$ is another 2-cell drawing in $\Sigma$ with a respectful tangle $\mathscr{T}'$ with
metric $d'$, we say that $\mathscr{T}'$ is a $\lambda$-compression of $\mathscr{T}$ (where
$\lambda \ge 0$ is an integer) if $d'(\sigma_1, \sigma_2) \ge d(\sigma_1, \sigma_2) -
\lambda$ for all $\sigma_1, \sigma_2 \in \Sigma$, and $ord(\mathscr{T}') = ord(\mathscr{T})
- \lambda$." -/
structure IsLambdaCompression {S : Type w} [TopologicalSpace S] [T2Space S]
    (H H' : Drawing S) (θ lam : ℕ)
    (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d d' : Set S → Set S → ℕ) : Prop where
  /-- `λ < θ` (so `ord(T') = θ - λ ≥ 1`). -/
  lam_lt : lam < θ
  /-- `T` is a respectful tangle of order `θ` in the 2-cell drawing `H` with metric `d`. -/
  hasMetric : HasTangleMetric H θ T d
  /-- `T'` is a respectful tangle of order `θ - λ` in the 2-cell drawing `H'` with metric `d'`. -/
  hasMetric' : HasTangleMetric H' (θ - lam) T' d'
  /-- For all `σ₁, σ₂ ∈ Σ`, `d'(σ₁, σ₂) ≥ d(σ₁, σ₂) - λ`. -/
  dist_le : ∀ σ₁ σ₂ : S, pointDist H d σ₁ σ₂ ≤ pointDist H' d' σ₁ σ₂ + lam

/-- `H', η', T'` is obtained from `H, η, T` by rearranging within `λ` of `z ∈ A(H)`
(Graph Minors XV, Section 1, page 114):
"If $\Sigma, H, \eta, \mathscr{T}, H', \eta', \mathscr{T}', G^*, \mathscr{T}^*$ are as above,
and $z \in A(H)$, we say that $H', \eta', \mathscr{T}'$ is obtained from $H, \eta,
\mathscr{T}$ by rearranging within $\lambda$ of $z$, where $\lambda \ge 0$ is an integer, if
(i) $a \in A(H')$ for all $a \in A(H)$ with $d(z, a) > \lambda$, where $d$ is the metric of
$\mathscr{T}$, (ii) $\eta(x) = \eta'(x)$ for every vertex or edge $x$ of $H$ with $d(z, x) >
\lambda$, and (iii) $\mathscr{T}'$ is a $(4\lambda + 2)$-compression of $\mathscr{T}$." -/
structure IsRearrangedWithin {S : Type w} [TopologicalSpace S] [T2Space S]
    (G : Graph α β) (H H' : Drawing S) (η : SpanEmbedding H G) (η' : SpanEmbedding H' G)
    (θ_star θ lam : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d d' : Set S → Set S → ℕ) (z : Set S) : Prop where
  /-- `z ∈ A(H)`. -/
  z_mem : z ∈ H.A
  /-- `H, η, T` is a `Σ`-span of order `θ` in `G` with respect to `T*`. -/
  isSpan : IsSigmaSpan G H η θ_star θ T_star T
  /-- `H', η', T'` is a `Σ`-span of order `θ - (4λ + 2)` in `G` with respect to `T*`. -/
  isSpan' : IsSigmaSpan G H' η' θ_star (θ - (4 * lam + 2)) T_star T'
  /-- `(i)` `a ∈ A(H')` for all `a ∈ A(H)` with `d(z, a) > λ`. -/
  atom_mem : ∀ a ∈ H.A, lam < d z a → a ∈ H'.A
  /-- `(ii)` `η(v) = η'(v)` for every vertex `v ∈ V(H)` with `d(z, {v}) > λ`. -/
  vMap_eq : ∀ v ∈ H.V, lam < d z {v} → v ∈ H'.V ∧ η'.vMap v = η.vMap v
  /-- `(ii)` `η(e) = η'(e)` for every edge `e ∈ E(H)` with `d(z, e) > λ`. -/
  eMap_eq : ∀ e ∈ H.E, lam < d z e → e ∈ H'.E ∧ η'.eMap e = η.eMap e
  /-- `(iii)` `T'` is a `(4λ + 2)`-compression of `T`. -/
  isCompression : IsLambdaCompression H H' θ (4 * lam + 2) T T' d d'

/-- An `η(H)`-path `P` in `G` with ends `η(u), η(v)` is `μ`-stepped with respect to `(H, η, T, d)`
(Graph Minors XV, Section 1, page 115). -/
def IsMuStepped {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (d : Set S → Set S → ℕ) (μ : ℕ) (P : Graph α β) (u v : S) : Prop :=
  u ∈ H.V ∧ v ∈ H.V ∧ IsHPathWithEnds G η.imageGraph P (η.vMap u) (η.vMap v) ∧ μ ≤ d {u} {v}

/-- A `Σ`-span `H, η, T` is `μ`-stepped (Graph Minors XV, Section 1, page 115):
"A $\Sigma$-span $H, \eta, \mathscr{T}$ is $\mu$-stepped if there is an $\eta(H)$-path in $G$
with ends $\eta(u), \eta(v)$ such that $d(u, v) \ge \mu$, where $d$ is the metric of
$\mathscr{T}$." -/
def IsMuSteppedSpan {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (d : Set S → Set S → ℕ) (μ : ℕ) : Prop :=
  ∃ (P : Graph α β) (u v : S), IsMuStepped G H η d μ P u v

/-- A `Σ`-span `H, η, T` is `(λ, μ)`-flat (Graph Minors XV, Section 1, page 115):
"A $\Sigma$-span $H, \eta, \mathscr{T}$ is $(\lambda, \mu)$-flat, where $\lambda, \mu \ge 0$
are integers, if $ord(\mathscr{T}) \ge 4\lambda + \mu + 2$ and there is no $\mu$-stepped
$\Sigma$-span $H', \eta', \mathscr{T}'$ which can be obtained from $H, \eta, \mathscr{T}$ by
rearranging within $\lambda$ of any $z \in A(H)$." -/
structure IsFlatSpan {S : Type w} [TopologicalSpace S] [T2Space S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ lam μ : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) : Prop where
  /-- `H, η, T` is a `Σ`-span of order `θ` in `G` with respect to `T*`. -/
  isSpan : IsSigmaSpan G H η θ_star θ T_star T
  /-- `ord(T) ≥ 4λ + μ + 2`. -/
  order_ge : 4 * lam + μ + 2 ≤ θ
  /-- No `Σ`-span obtained from `H, η, T` by rearranging within `λ` of any `z ∈ A(H)` is
  `μ`-stepped. -/
  no_stepped_rearrangement :
    ∀ ⦃H' : Drawing S⦄ ⦃η' : SpanEmbedding H' G⦄
      ⦃T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))⦄
      ⦃d d' : Set S → Set S → ℕ⦄ ⦃z : Set S⦄,
      IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z →
      ¬ IsMuSteppedSpan G H' η' d' μ

/-- A region `r` of `H` is an eye of `H, η, T` in `G` witnessed by disjoint `η(H)`-paths `P₁, P₂`
(Graph Minors XIV, Section 3, pages 28–29; Graph Minors XV, Section 1, page 115). -/
def IsEyeWithPaths {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (r : Set S) (P₁ P₂ : Graph α β) : Prop :=
  r ∈ H.R ∧
    ∃ (C : Drawing S) (a b c d : S),
      C.IsCircuit ∧ C.IsSubdrawing H ∧ C.U = subBd r ∧
      a ∈ C.V ∧ b ∈ C.V ∧ c ∈ C.V ∧ d ∈ C.V ∧
      ([a, b, c, d]).Nodup ∧ OccurInCircuitOrder C a b c d ∧
      IsFreeSet H.toHypergraph T θ {a, b, c, d} ∧
      Disjoint V(P₁) V(P₂) ∧
      IsHPathWithEnds G η.imageGraph P₁ (η.vMap a) (η.vMap c) ∧
      IsHPathWithEnds G η.imageGraph P₂ (η.vMap b) (η.vMap d)

/-- Alias for `GM14.IsDrawingEye` (Graph Minors XV, Section 1, page 115). -/
abbrev IsEye {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (r : Set S) : Prop :=
  IsDrawingEye G H η θ T r

/-- `H, η, T` has `k` eyes mutually at distance `≥ δ`
(Graph Minors XV, Section 1, (1.2), page 115). -/
def HasEyesAtDistance {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (k δ : ℕ) : Prop :=
  ∃ r : Fin k → Set S,
    Injective r ∧
    (∀ i : Fin k, IsDrawingEye G H η θ T (r i)) ∧
    ∀ i j : Fin k, i ≠ j → δ ≤ d (r i) (r j)

/-- `r₁, ..., r_κ` are independent eyes of `H, η, T` in `G`
(Graph Minors XV, Section 1, page 115):
"Now let $r_1, ..., r_\kappa$ be eyes, with corresponding $\eta(H)$-paths $P_i, Q_i$ ($1 \le
i \le \kappa$). We say that $r_1, ..., r_\kappa$ are *independent eyes* if the paths $P_i,
Q_i$ can be chosen so that (i) for $1 \le i < j \le \kappa$, $d(r_i, r_j) =
ord(\mathscr{T})$, where $d$ is the metric of $\mathscr{T}$ (ii) for $1 \le i < j \le
\kappa$, $P_i \cup Q_i$ is disjoint from $P_j \cup Q_j$." -/
def HasIndependentEyes {S : Type w} [TopologicalSpace S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (κ : ℕ) : Prop :=
  ∃ (r : Fin κ → Set S) (P Q : Fin κ → Graph α β),
    Injective r ∧
    (∀ i : Fin κ, IsEyeWithPaths G H η θ T (r i) (P i) (Q i)) ∧
    (∀ i j : Fin κ, i ≠ j → d (r i) (r j) = θ) ∧
    ∀ i j : Fin κ, i ≠ j → Disjoint (V(P i) ∪ V(Q i)) (V(P j) ∪ V(Q j))

/-- A surface `S'` is obtained by adding a crosscap to `S`
(Graph Minors XV, Section 3, page 121):
"Let $\Sigma_1 = \Sigma - \Lambda$. We may assume that $\Sigma' = \Sigma_1 \cup \Sigma_2$,
where $\Sigma_2$ is homeomorphic to a Möbius band and $\Sigma_1 \cap \Sigma_2 = bd(\Sigma_1)
= bd(\Sigma_2)$." -/
def IsObtainedByAddingCrosscap
    (S : Type w) [TopologicalSpace S] (S' : Type w) [TopologicalSpace S'] : Prop :=
  IsSurface S ∧ IsSurface S' ∧ bd S' = ∅ ∧
    ∃ (Λ : Set S) (S₁ S₂ : Set S'),
      IsOpenDisc Λ ∧ Disjoint (closure Λ) (bd S) ∧
      S₁ ∪ S₂ = univ ∧
      S₁ ∩ S₂ = (↑) '' bd S₁ ∧
      S₁ ∩ S₂ = (↑) '' bd S₂ ∧
      Nonempty (↥((univ : Set S) \ Λ) ≃ₜ S₁) ∧
      Nonempty (MobiusBand ≃ₜ S₂)

/-! ## Section 3: Adding a Handle -/

/-- A surface `S'` is obtained from `S` by adding a handle (Graph Minors XV, Section 3, page 123):
"Let $\Sigma_1 = \Sigma - (\Lambda_1 \cup \Lambda_2)$. Let $\Sigma_2$ be homeomorphic to a
closed cylinder, with boundary $U(C_1) \cup U(C_2)$, such that $\Sigma' = \Sigma_1 \cup
\Sigma_2$ is a surface obtained from $\Sigma$ by adding a handle". -/
def IsObtainedByAddingHandle
    (S : Type w) [TopologicalSpace S] (S' : Type w) [TopologicalSpace S'] : Prop :=
  IsSurface S ∧ IsSurface S' ∧ bd S' = ∅ ∧
    ∃ (Λ₁ Λ₂ : Set S) (S₁ S₂ : Set S'),
      IsOpenDisc Λ₁ ∧ IsOpenDisc Λ₂ ∧ Disjoint (closure Λ₁) (closure Λ₂) ∧
      Disjoint (closure Λ₁) (bd S) ∧ Disjoint (closure Λ₂) (bd S) ∧
      S₁ ∪ S₂ = univ ∧
      S₁ ∩ S₂ = (↑) '' bd S₁ ∧
      S₁ ∩ S₂ = (↑) '' bd S₂ ∧
      Nonempty (↥((univ : Set S) \ (Λ₁ ∪ Λ₂)) ≃ₜ S₁) ∧
      Nonempty (ClosedCylinder ≃ₜ S₂)

/-! ## Section 4: Deleting an Atom Neighborhood `H - z^λ` -/

open Classical in
/-- The subdrawing `H - z^λ` (Graph Minors XV, Section 4, page 125):
for a 2-cell drawing `H` in `Σ`, a respectful tangle `T` in `H` of order `θ` with metric `d`,
an integer `λ ≥ 0` with `λ < θ`, and `z ∈ A(H)`, `H - z^λ` is the subdrawing of `H` formed by all
edges `e` of `H` with `d(z, e) > λ` and their ends (or `H` if `E(H) = ∅`). -/
noncomputable def deleteAtomNeighborhood {S : Type w} [TopologicalSpace S] [T1Space S]
    (H : Drawing S) (d : Set S → Set S → ℕ) (z : Set S) (lam : ℕ) : Drawing S :=
  if H.E = ∅ then H else H.span ∅ {e ∈ H.E | lam < d z e}

/-! ## Section 8: Controlling a Clique Minor and `(λ, μ)`-Level `Σ`-Spans -/

/-- A tangle `T*` in `G` controls a `K_p` minor of `G` (Graph Minors XV, Section 8, page 145):
`T*` has order `≥ p` and there are `p` non-null disjoint connected subgraphs `X₁, ..., X_p` of `G`
such that (i) for `1 ≤ i < j ≤ p` there is an edge of `G` with one end in `V(X_i)` and the other in
`V(X_j)`, and (ii) there is no `(A, B) ∈ T*` of order `< p` such that `V(X_i) ⊆ V(A)` for some `i`
(`1 ≤ i ≤ p`). -/
def ControlsCliqueMinor (G : Graph α β) (p : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β)) : Prop :=
  ∃ X_sub : Fin p → Graph α β,
    (∀ i : Fin p, X_sub i ≤ G ∧ V(X_sub i).Nonempty ∧ GraphConnected (X_sub i)) ∧
    (∀ i j : Fin p, i ≠ j → Disjoint V(X_sub i) V(X_sub j)) ∧
    (∀ i j : Fin p, i < j →
      ∃ e ∈ E(G), ∃ u ∈ V(X_sub i), ∃ v ∈ V(X_sub j), G.IsLink e u v) ∧
    ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ T_star → separationOrder A B < p →
      ∀ i : Fin p, ¬ V(X_sub i) ⊆ A.vertexSet

/-- A `Σ`-span `H, η, T` of order `θ` in `G` with respect to `T*` is `(λ, μ)`-level
(Graph Minors XV, Section 8, page 146):
"If $\mathcal{T}^*$ is a tangle in $G$ and $H, \eta, \mathcal{T}$ is a $\Sigma$-span of order
$\theta$, where $\Sigma$ is a surface with $\text{bd}(\Sigma) = \emptyset$, we say that $H,
\eta, \mathcal{T}$ is $(\lambda, \mu)$-level if (i) $\theta \ge 4\lambda + \mu + 2$ (ii) $H,
\eta, \mathcal{T}$ is not $\mu$-stepped, and (iii) for every $\Sigma$-span $H', \eta',
\mathcal{T}'$, obtained from $H, \eta, \mathcal{T}$ by rearranging within $\lambda$ of some
$z \in A(H)$, there is no $\eta'(H')$-path in $G$ with ends $\eta'(u), \eta'(v)$ with $d'(u,
v) \ge \mu$ and $d(z, u), d(z, v) \le \lambda$." -/
structure IsLevelSpan {S : Type w} [TopologicalSpace S] [T2Space S]
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ lam μ : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) : Prop where
  /-- `H, η, T` is a `Σ`-span of order `θ` in `G` with respect to `T*`. -/
  isSpan : IsSigmaSpan G H η θ_star θ T_star T
  /-- `d` is the metric of `T`. -/
  hasMetric : HasTangleMetric H θ T d
  /-- `(i)` `θ ≥ 4λ + μ + 2`. -/
  order_ge : 4 * lam + μ + 2 ≤ θ
  /-- `(ii)` `H, η, T` is not `μ`-stepped. -/
  not_stepped : ¬ IsMuSteppedSpan G H η d μ
  /-- `(iii)` For every `Σ`-span `H', η', T'` obtained from `H, η, T` by rearranging within `λ` of
  some `z ∈ A(H)`, there is no `η'(H')`-path in `G` with ends `η'(u), η'(v)` with `d'(u, v) ≥ μ` and
  `d(z, u), d(z, v) ≤ λ`. -/
  no_local_stepped_rearrangement :
    ∀ ⦃H' : Drawing S⦄ ⦃η' : SpanEmbedding H' G⦄
      ⦃T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))⦄
      ⦃d' : Set S → Set S → ℕ⦄ ⦃z : Set S⦄,
      IsRearrangedWithin G H H' η η' θ_star θ lam T_star T T' d d' z →
      ∀ ⦃P : Graph α β⦄ ⦃u v : S⦄,
        IsMuStepped G H' η' d' μ P u v →
        ¬ (pointAtomDist H d u z ≤ lam ∧ pointAtomDist H d v z ≤ lam)

end GM15

end GraphMinor
