/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM16.Battlefields
public import LeanPool.GraphMinor.GM15.Cited

/-!
# Results cited in Graph Minors XVI

This file states as `Prop`s the results from earlier papers of the Graph Minors series (and from
external papers cited in Graph Minors XVI) that are used in the proofs of N. Robertson and
P. D. Seymour, *Graph Minors. XVI. Excluding a non-planar graph*, J. Combin. Theory Ser. B 89
(2003) 43–76, over the shared definitions from `GraphMinor.GM09.Defs`, `GraphMinor.GM10.Defs`,
`GraphMinor.GM10.Defs2`, `GraphMinor.GM11.Defs`, `GraphMinor.GM12.Defs`, `GraphMinor.GM14.Defs`,
`GraphMinor.GM15.Defs`, and `GraphMinor.GM16.Defs`:

* **Graph Minors IX** (*Disjoint crossed paths*, JCTB 49 (1990) 40–77):
  - `GM15.GM09Theorem81Statement` (re-exported from `GraphMinor.GM15.Cited`), (8.1) (page 60),
    used in the proof of (3.2) of XVI (page 50);
  - `GM09Theorem105Statement`, (10.5) (page 66), used in Step (11) of the proof of (8.1) in
    Section 9 of XVI (page 74).
* **Graph Minors XII** (*Distance on a surface*, JCTB 64 (1995) 240–272):
  - `GM12Theorem42Statement`, (4.2) (page 249), monotonicity of controlling a minor, used in the
    proof of (3.1) of XVI (page 54);
  - `GM12Theorem43Statement`, (4.3) (page 250), stated as (4.3) of XVI (page 54);
  - `GM12Theorem44Statement`, (4.4) (page 251), stated as (5.2) of XVI (page 55);
  - `GM14.GM12Theorem710Statement` (re-exported from `GraphMinor.GM15.Cited`), (7.10) (page 270),
    clearing a $\lambda$-zone, used in (6.2), (6.3), and Section 9 of XVI.
* **Graph Minors XIV** (*Extending an embedding*, JCTB 65 (1995) 23–50):
  - `GM14Theorem75Statement`, (7.5) (page 36), inside of a short radial circuit in a zone, used in
    Step (10) of the proof of (8.1) in Section 9 of XVI (page 73);
  - `GM14Theorem92Statement`, (9.2) (page 43), existence of a $(\kappa + 2)$-zone around $z$, used
    in (6.3) and Section 9 of XVI;
  - `GM14Theorem93Statement`, (9.3) (page 44), existence of a $(\kappa + 5)$-zone around $z$ whose
    complement is rigid, used in (6.3) of XVI (page 60);
  - `GM14Theorem95Statement`, (9.5) (page 45), existence of a battlefield of size $\beta$ around
    $z$, used in Section 9 of XVI (page 71).
* **External results cited in Graph Minors XVI:**
  - `RST94Theorem23Statement`, Robertson, Seymour, and Thomas, (2.3) on grid minors
    controlled by a tangle, used in Step (2) of the proof of (4.2) of XVI (page 53).
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15

export GM15 (GM09Theorem81Statement GM12Theorem710Statement)

universe u v w

/-! ## Graph Minors IX: Disjoint crossed paths (JCTB 49 (1990) 40–77) -/

/-- Statement of Graph Minors IX, (10.5) (page 66), used in Step (11) of the proof of (8.1) in
Section 9 of Graph Minors XVI (page 74):
"Let $p \ge 0$ and let $(G, \Omega, \Omega_0)$ be a rural neighborhood of breadth $\ge
\frac{1}{2} p + 1$. Let $X \subseteq \bar{\Omega}$ be linked, with $|X| \ge p$. Let $(G \cup
G_0, \Omega)$ be the composition of some society $(G_0, \Omega_0)$ with $(G, \Omega,
\Omega_0)$, and let $Y \subseteq V(G_0)$. Then either there are $p$ mutually disjoint paths
of $G \cup G_0$ from $X$ to $Y$, each with only its initial vertex in $\bar{\Omega}$, or
there exists $W \subseteq V(G \cup G_0)$ with $|W| < p$ and $W \cap \bar{\Omega} =
\emptyset$ such that every path of $G \cup G_0$ from $\bar{\Omega}$ to $Y$ has a vertex in
$W$." -/
def GM09Theorem105Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (S_comp S₀ : Society α β) (N : Neighborhood α β)
    (p : ℕ) (X Y : Set α),
    N.IsRural → N.HasBreadthGe ((p + 1) / 2 + 1) →
    N.IsLinked X → p ≤ X.ncard →
    S_comp.IsComposition S₀ N → Y ⊆ V(S₀.G) →
    (∃ P : Fin p → Graph α β,
      (∀ i, ∃ x ∈ X, ∃ y ∈ Y, IsFromToPathWithEnds S_comp.G (P i) S_comp.Ω.bar Y x y) ∧
      Pairwise (fun i j => Disjoint V(P i) V(P j))) ∨
    (∃ W ⊆ V(S_comp.G), W.ncard < p ∧ Disjoint W S_comp.Ω.bar ∧
      ∀ P : Graph α β, IsFromToPath S_comp.G P S_comp.Ω.bar Y → (V(P) ∩ W).Nonempty)

/-! ## Graph Minors XII: Distance on a surface (JCTB 64 (1995) 240–272) -/

/-- Statement of Graph Minors XII, (4.2) (page 249), used in the proof of (3.1) of Graph Minors XVI
(page 54):
For any finite graph $L$ there exists $p \ge 0$ such that any tangle $\mathcal{T}^*$ in a graph $G$
controlling a $K_p$-minor (`GM12.ControlsMinor ... (completeGraph p)`) also controls an $L$-minor
(`GM12.ControlsMinor ... L`). -/
def GM12Theorem42Statement : Prop :=
  ∀ {α' : Type*} {β' : Type*} (L : Graph α' β'), V(L).Finite → E(L).Finite →
    ∃ p : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β))
      (hT : IsGraphTangle G θ_star T_star),
      GM12.ControlsMinor (Hypergraph.ofGraph G hT.finite_V hT.finite_E) θ_star T_star
        (completeGraph p) →
      GM12.ControlsMinor (Hypergraph.ofGraph G hT.finite_V hT.finite_E) θ_star T_star L

/-- Statement of Graph Minors XII, (4.3) (page 250), stated as (4.3) in Graph Minors XVI (page 54):
"If $L$ is a graph and $\Sigma$ is a surface such that $L$ can be drawn in $\Sigma$, there is an
integer $\theta \ge 1$ with the following property. If $\mathscr{T}^*$ is a tangle in a graph $G$
controlling no $L$ minor, then there is no $\Sigma$-span of order $\ge \theta$." -/
def GM12Theorem43Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    {α' : Type*} {β' : Type*} (L : Graph α' β'),
    IsClosedSurface S → ConnectedSpace S → V(L).Finite → E(L).Finite →
    CanBeDrawnIn S L →
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β))
        (H : Drawing S) (η : SpanEmbedding H G) (θ_span : ℕ)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (hT : IsGraphTangle G θ_star T_star),
        ¬ GM12.ControlsMinor (Hypergraph.ofGraph G hT.finite_V hT.finite_E) θ_star T_star L →
        θ ≤ θ_span → ¬ IsSigmaSpan G H η θ_star θ_span T_star T

/-- Statement of Graph Minors XII, (4.4) (page 251), stated as (5.2) in Graph Minors XVI (page 55):
"Let $\Sigma$ be a surface and let $p \ge 0$. Then there exists $\theta \ge 1$ such that if
$\mathscr{T}^*$ is a tangle in a graph $G$, and $H, \eta, \mathscr{T}$ is a $\Sigma$-span of order
$\ge \theta$ with metric $d$, and
* $s_1, t_1, \dots, s_\mu, t_\mu$ are distinct vertices of $H$, where $\mu = \frac{1}{2}p(p - 1)$,
  such that $d(u, v) \ge \theta$ for all distinct $u, v \in \{s_1, t_1, \dots, s_\mu, t_\mu\}$, and
* $Q_1, \dots, Q_\mu$ are mutually disjoint $\eta(H)$-paths, such that $Q_i$ has ends
  $\eta(s_i), \eta(t_i) (1 \le i \le \mu)$,
then $\mathscr{T}^*$ controls a $K_p$-minor of $G$." -/
def GM12Theorem44Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
    IsClosedSurface S → ConnectedSpace S →
    ∀ p : ℕ, ∃ θ : ℕ, 1 ≤ θ ∧
      let μ := p * (p - 1) / 2
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β))
        (H : Drawing S) (η : SpanEmbedding H G)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ)
        (s t : Fin μ → S) (Q : Fin μ → Graph α β)
        (hSpan : IsSigmaSpan G H η θ_star θ_span T_star T),
        HasTangleMetric H θ_span T d →
        θ ≤ θ_span →
        (∀ i : Fin μ, s i ∈ H.V ∧ t i ∈ H.V ∧ s i ≠ t i) →
        Injective s → Injective t → Disjoint (range s) (range t) →
        (∀ u ∈ range s ∪ range t, ∀ v ∈ range s ∪ range t, u ≠ v → θ ≤ d {u} {v}) →
        (∀ i : Fin μ, IsHPathWithEnds G η.imageGraph (Q i) (η.vMap (s i)) (η.vMap (t i))) →
        Pairwise (fun i j => Disjoint V(Q i) V(Q j)) →
        GM12.ControlsMinor
          (Hypergraph.ofGraph G hSpan.isControlling.isTangle_star.finite_V
            hSpan.isControlling.isTangle_star.finite_E)
          θ_star T_star (completeGraph p)

/-! ## Graph Minors XIV: Extending an embedding (JCTB 65 (1995) 23–50) -/

/-- Statement of Graph Minors XIV, (7.5) (page 36), used in Step (10) of the proof of (8.1) in
Section 9 of Graph Minors XVI (page 73):
Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathcal{T}$ be a respectful tangle in $H$ of
order $\theta$, with metric $d$. Let $\lambda \ge 0$ be an integer, and let $\Lambda \subseteq
\Sigma$
be a $\lambda$-zone. Let $K$ be a radial drawing of $H$, with derived slope `ins`, and let $D$ be a
circuit of $K$ with $U(D) \subseteq \bar{\Lambda}$ and $|E(D)| < 2(\theta - \lambda)$. Then
$\operatorname{ins}(D) \subseteq \bar{\Lambda}$. -/
def GM14Theorem75Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    (H K D : Drawing S) (θ lam : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (ins : Drawing S → Set S) (z Λ : Set S),
    IsClosedSurface S → ConnectedSpace S →
    HasTangleMetric H θ T d →
    (PaintingOrDrawing.drawing H).IsRadialDrawing K →
    IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins →
    IsLambdaZoneAround H d lam z Λ →
    D.IsCircuit → D.IsSubdrawing K →
    D.U ⊆ closure Λ →
    D.length < 2 * (θ - lam) →
    ins D ⊆ closure Λ

/-- Statement of Graph Minors XIV, (9.2) (page 43), used in the proof of (6.3) (page 60) and in
Section 9 (page 73) of Graph Minors XVI:
Let $H$ be a 2-cell drawing in $\Sigma$, and let $\mathcal{T}$ be a respectful tangle in $H$ of
order $\theta$, with metric $d$. Let $z \in A(H)$ and let $\kappa$ be an integer with
$2 \le \kappa \le \theta - 3$. Then there is a $(\kappa + 2)$-zone $\Lambda$ around $z$ such that
$x \subseteq \Lambda$ for every $x \in A(H)$ with $d(z, x) < \kappa$. -/
def GM14Theorem92Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    (H : Drawing S) (θ κ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (z : Set S),
    IsClosedSurface S → ConnectedSpace S →
    HasTangleMetric H θ T d → z ∈ H.A →
    2 ≤ κ → κ + 3 ≤ θ →
    ∃ Λ : Set S, IsLambdaZoneAround H d (κ + 2) z Λ ∧
      ∀ x ∈ H.A, d z x < κ → x ⊆ Λ

/-- Statement of Graph Minors XIV, (9.3) (page 44), used in the proof of (6.3) of Graph Minors XVI
(page 60):
Let $H$ be a 2-cell rigid drawing in $\Sigma$, and let $\mathcal{T}$ be a respectful tangle in $H$
of order $\theta$, with metric $d$. Let $z \in A(H)$, and let $\kappa$ be an integer with
$2 \le \kappa \le \theta - 6$. Then there is a $(\kappa + 5)$-zone $\Lambda$ around $z$ such that
$H \cap (\Sigma - \Lambda)$ is rigid and $x \subseteq \Lambda$ for every $x \in A(H)$ with
$d(z, x) < \kappa$. -/
def GM14Theorem93Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    (H : Drawing S) (θ κ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (z : Set S),
    IsClosedSurface S → ConnectedSpace S →
    IsRigid H → HasTangleMetric H θ T d → z ∈ H.A →
    2 ≤ κ → κ + 6 ≤ θ →
    ∃ Λ : Set S, IsLambdaZoneAround H d (κ + 5) z Λ ∧
      IsRigid (clearedSubdrawing H Λ) ∧
      ∀ x ∈ H.A, d z x < κ → x ⊆ Λ

/-- Graph Minors XIV, (9.5), page 45, used in XVI, Section 9, page 71:
"Let $H$ be a 2-cell, rigid drawing in $\Sigma$, let $z \in A(H)$, and let $\mathscr{T}$ be a
respectful tangle in $H$ of order $\theta$. Let $\beta \ge 4$ be an even integer with
$\theta \ge 16\beta + 17$. Then there is a battlefield around $z$ of size $\beta$."
The boundary-set normalization is proved by `IsBattlefieldData.normalize`. -/
def GM14Theorem95Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    (H : Drawing S) (θ β : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (z : Set S),
    IsClosedSurface S → ConnectedSpace S →
    IsRigid H → HasTangleMetric H θ T d → z ∈ H.A →
    4 ≤ β → Even β → 16 * β + 17 ≤ θ →
    ∃ (Λ : Set S) (C : Drawing S) (X : Set S),
      IsBattlefieldData H T d θ β z Λ C X

/-! ## Graph Minors XV: Giant steps (JCTB 68 (1996) 112–148) -/

/-- Statement of Graph Minors XV, (3.5), page 123, used in XVI (8.1),
Claim (4), page 72. The boundary order and the prohibition on a region
incident with both boundary circuits are explicit here.
The statement also includes the line condition of XII (5.1), missing
from XV (3.5) as printed. Without it the printed statement is false
for large `φ`.
"Let $\Sigma$ be a surface and let $\phi \ge 3$ be an integer. Let $\mathscr{T}^*$ be a
tangle in a graph $G$, and let $H, \eta, \mathscr{T}$ be a $\Sigma$-span. Let $\Lambda_1,
\Lambda_2 \subseteq \Sigma$ be distinct regions of $H$ so that $H \cap bd(\Lambda_i)$ is a
circuit $C_i$ ($i = 1, 2$), and no region of $H$ is incident with a vertex in $C_1$ and with
a vertex in $C_2$. Let $a_1, \dots, a_\phi$ be distinct vertices of $C_1$ in order, and let
$b_1, \dots, b_\phi$ be distinct vertices of $C_2$ in order (under some orientations of
$C_1$ and $C_2$), such that $\{a_1, \dots, a_\phi\}$ and $\{b_1, \dots, b_\phi\}$ are free
with respect to $\mathscr{T}$. For $1 \le i \le \phi$ let $P_i$ be an $\eta(H)$-path with
ends $\eta(a_i), \eta(b_i)$, such that $P_1, \dots, P_\phi$ are mutually disjoint. Then
there is a $\Sigma'$-span of order $\phi$, where $\Sigma'$ is the surface obtained by adding
a handle to $\Sigma$." -/
def GM15Theorem35Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v}
    (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ φ : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (Λ₁ Λ₂ : Set S) (P : Fin φ → Graph α β) (a b : Fin φ → S),
    IsSigmaSpan G H η θ_star θ T_star T → HasTangleMetric H θ T d →
    Λ₁ ∈ H.R → Λ₂ ∈ H.R → Λ₁ ≠ Λ₂ →
    (H.interSet (subBd Λ₁)).IsCircuit → (H.interSet (subBd Λ₂)).IsCircuit →
    (∀ r ∈ H.R, ¬ ((∃ x ∈ (H.interSet (subBd Λ₁)).V, x ∈ closure r) ∧
      ∃ y ∈ (H.interSet (subBd Λ₂)).V, y ∈ closure r)) →
    (∀ F : Set S, IsLine F → H.IsNormal F → F ⊆ univ \ (Λ₁ ∪ Λ₂) →
      (F ∩ subBd Λ₁).Nonempty → (F ∩ subBd Λ₂).Nonempty → φ ≤ (F ∩ H.V).ncard) →
    3 ≤ φ → Injective a → Injective b →
    GM12.IsListedInOrderOn (subBd Λ₁) (List.ofFn a) →
    GM12.IsListedInOrderOn (subBd Λ₂) (List.ofFn b) →
    (∀ i, a i ∈ (H.interSet (subBd Λ₁)).V ∧ b i ∈ (H.interSet (subBd Λ₂)).V) →
    (∀ i, IsHPathWithEnds G η.imageGraph (P i) (η.vMap (a i)) (η.vMap (b i))) →
    Pairwise (fun i j => Disjoint V(P i) V(P j)) →
    IsFreeSet H.toHypergraph T θ (range a) → IsFreeSet H.toHypergraph T θ (range b) →
    ∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
      IsObtainedByAddingHandle S S' ∧
      ∃ (H' : Drawing S') (η' : SpanEmbedding H' G)
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        IsSigmaSpan G H' η' θ_star φ T_star T'

/-! ## External theorems cited in Graph Minors XVI -/

/-- The form of Robertson, Seymour, and Thomas, *Quickly excluding a planar graph*, J. Combin.
Theory
Ser. B 62 (1994) 323–348, (2.3) (page 327), used in the proof of (4.2) of Graph Minors XVI (page
53).
XVI writes "theorem 6.1 of [10]", but (6.1) of the published paper bounds the tree-width of planar
graphs.
(2.3) says: "Let $g \ge 2$, and let $\mathscr{T}$ be a tangle in $G$ of order $\ge 20^{g^4(2g-1)}$.
Then $\mathscr{T}$ dominates a $g \times g$ grid minor." This gives the statement below with `g = 2θ
+ 1`. If `(A, B) ∈ 𝒯` has order `≤ 2θ` and `E(A)` includes a
row of the grid, then `(B, A)` is in `𝒯_H ⊆ 𝒯`, against the second axiom. XVI, Step (2):
"For every graph $G$ and tangle $\mathscr{T}^*$ in $G$ of order $\ge \theta^*$, there is a
$(2\theta + 1) \times (2\theta + 1)$ grid minor of $G$ such that for all $(A, B) \in \mathscr{T}^*$
of order $\le 2\theta$, $E(A)$ includes no row of the grid." -/
def RST94Theorem23Statement : Prop :=
  ∀ θ : ℕ, 1 ≤ θ →
    ∃ θ_star : ℕ, 1 ≤ θ_star ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_G : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β)),
        IsGraphTangle G θ_G T_star → θ_star ≤ θ_G →
        ∃ (ηv : Fin (2 * θ + 1) × Fin (2 * θ + 1) → Set α)
          (ηe : Sym2 (Fin (2 * θ + 1) × Fin (2 * θ + 1)) → β),
          IsMinorModel (GM01.gridGraph (2 * θ + 1)) G ηv ηe ∧
          ∀ A B : Hypergraph α β, (A, B) ∈ T_star → separationOrder A B ≤ 2 * θ →
            ∀ i : Fin (2 * θ + 1),
              ¬ (ηe '' (GM10.gridRowPath (2 * θ + 1) i).edgeSet ⊆ A.edgeSet)

end GraphMinor.GM16
