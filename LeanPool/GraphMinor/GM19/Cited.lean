/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.GM10.Defs2
public import LeanPool.GraphMinor.GM11.Cited
public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM14.Cited
public import LeanPool.GraphMinor.GM15.Cited
public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM17.Defs2

/-!
# Cited Theorems from Earlier Papers Used in Graph Minors XIX

This file collects the numbered theorems of earlier papers that N. Robertson and P. D. Seymour,
*Graph Minors. XIX. Well-quasi-ordering on a surface*, J. Combin. Theory Ser. B **90** (2004),
325–385, cites. Each one keeps the objects of its own paper, and each one is proved in another
file.

Each item gives the pages of XIX that cite the result.

Stated elsewhere, and reached through the imports:
- `GM14.GM07Theorem42Statement` (VII (4.2), XIX page 345), `GM14.GM07Theorem119Statement`
  (VII (11.9), XIX page 345), `GM11.GM07Theorem1110Statement` (VII (11.10), XIX page 338).
- `GM14.GM11Theorem63Statement` (XI (6.3), XIX page 379, proved as `GM11.theorem_6_3_proof`),
  `GM14.GM11Theorem810Statement` (XI (8.10), XIX page 345), `GM14.GM11Theorem812Statement` (XI
  (8.12), XIX pages 345 and 346).
- `GM15.GM11Theorem91Statement` (XI (9.1), XIX page 344).
- `GM16.GM14Theorem92Statement` (XIV (9.2), which XIX generalizes on page 344).
- XI (4.3) is proved: `GM11.theorem_4_3_i`, `GM11.theorem_4_3_ii`, `GM11.theorem_4_3_iii`.
- XIV (5.2) is proved: `GM14.theorem_5_2_proof` (XIX pages 345 and 363).

Stated here:
- `GM11Theorem85Statement` (XI (8.5), XIX pages 344 and 345), `GM11Theorem92Statement` (XI (9.2),
  XIX pages 344, 345 and 355), proved as `GM11.gm19_theorem_8_5` and `GM11.gm19_theorem_9_2`.
- `GM12Theorem32Statement` (XII (3.2), XIX page 383).
- `GM17Theorem141Statement` (XVII (14.1), XIX page 383).

- `GM07.GM07Theorem92Statement` (VII (9.2), XIX page 341) is stated in VII's words in
  `GraphMinor/GM07/Defs.lean`. XIX quotes it as (6.4), and `GM19.theorem_6_4_proof` proves that
  form.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology Graph
open GraphMinor.Surface GraphMinor.Hypergraph
open GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14

universe u

export GraphMinor.GM07 (GM07Theorem92Statement)
export GraphMinor.GM11 (GM07Theorem1110Statement)
export GraphMinor.GM14
  (GM07Theorem42Statement GM07Theorem119Statement
   GM11Theorem63Statement GM11Theorem810Statement GM11Theorem812Statement)
export GraphMinor.GM15 (GM11Theorem91Statement)
export GraphMinor.GM16 (GM14Theorem92Statement)

/-- **Graph Minors XI, (8.5)** (page 97):
"(8.5) *Let $W$ be a closed walk in $\Gamma$ of length $< 2\theta$. Then $\mathrm{ins}(W)$ is
a restraint and $l(\mathrm{ins}(W)) \le l(W)$." -/
def GM11Theorem85Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsClosedSurface S → ConnectedSpace S →
  ∀ (Γ : Surface.Drawing S) (two_theta : ℕ) (ins : Surface.Drawing S → Set S),
    IsSlope Γ two_theta ins →
  ∀ (u : S) (W : GraphWalk Γ.toGraph u u),
    W.length < two_theta →
    IsRestraint Γ ins two_theta (insWalk ins Γ W) ∧
    perimeterWalkLength Γ (insWalk ins Γ W) ≤ W.length

/-- **Graph Minors XI, (9.2)** (page 105):
"(9.2) *Let $a, b \in A(\Gamma)$ and let $Y$ be a restraint with $a, b \subseteq Y$. Then
there is a tie $X$ with $a, b \subseteq X \subseteq Y$ and $l(X) \le l(Y)$." -/
def GM11Theorem92Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsClosedSurface S → ConnectedSpace S →
  ∀ (Γ : Surface.Drawing S) (two_theta : ℕ) (ins : Surface.Drawing S → Set S),
    IsSlope Γ two_theta ins →
  ∀ (a b Y : Set S),
    a ∈ Γ.A → b ∈ Γ.A → IsRestraint Γ ins two_theta Y → a ⊆ Y → b ⊆ Y →
    ∃ X : Set S,
      IsTie Γ ins two_theta X ∧ a ⊆ X ∧ b ⊆ X ∧ X ⊆ Y ∧
      perimeterWalkLength Γ X ≤ perimeterWalkLength Γ Y

/-- **Graph Minors XII, (3.2)** (page 246):
"(3.2) *For every connected surface $\Sigma$ and all integers $t \ge 0$ and $z \ge 0$, there exists
an integer $\theta \ge 1$ such that the following is true. Let $\Delta_1, \dots, \Delta_t$ be
mutually disjoint closed discs in $\Sigma$, and let $\Gamma$ be a $2$-cell drawing in $\Sigma$ such
that $U(\Gamma) \cap \Delta_i = V(\Gamma) \cap \text{bd}(\Delta_i)$ for $1 \le i \le t$. Let
$|Z| \le z$, where*
$$Z = \bigcup_{1 \le i \le t} V(\Gamma) \cap \text{bd}(\Delta_i),$$
*and let $(Z_j \colon 1 \le j \le p)$ be a partition of $Z$ satisfying the topological feasibility
condition above. Let $\mathscr{T}$ be a respectful tangle of order $\ge \theta$ in $\Gamma$, with
metric $d$, such that*
(i) *$d(r_i, r_j) \ge \theta$ for $1 \le i < j \le t$, where $r_i$ is the region of $\Gamma$
meeting $\Delta_i$ for $1 \le i \le t$, and*
(ii) *$V(\Gamma) \cap \text{bd}(\Delta_i)$ is free for $1 \le i \le t$.*
Then (*) holds." -/
def GM12Theorem32Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
    IsClosedSurface S → ConnectedSpace S →
  ∀ (t z : ℕ),
    ∃ θ : ℕ, 1 ≤ θ ∧
    ∀ (Δ : Fin t → Set S) (Γ : Surface.Drawing S)
      (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (p : ℕ) (Zs : Fin p → Set S),
      (∀ i : Fin t, IsClosedDisc (Δ i) ∧ Γ.U ∩ Δ i = Γ.V ∩ subBd (Δ i)) →
      (∀ i j : Fin t, i ≠ j → Disjoint (Δ i) (Δ j)) →
      (⋃ i : Fin t, Γ.V ∩ subBd (Δ i)).ncard ≤ z →
      (⋃ j : Fin p, Zs j) = (⋃ i : Fin t, Γ.V ∩ subBd (Δ i)) →
      (∀ j₁ j₂ : Fin p, j₁ ≠ j₂ → Disjoint (Zs j₁) (Zs j₂)) →
      IsTopologicallyFeasible Δ Zs →
      θ ≤ ord → HasTangleMetric Γ ord T d →
      (∀ i j : Fin t, i ≠ j →
        ∀ rᵢ ∈ Γ.R, (rᵢ ∩ Δ i).Nonempty →
        ∀ rⱼ ∈ Γ.R, (rⱼ ∩ Δ j).Nonempty →
        θ ≤ d rᵢ rⱼ) →
      (∀ i : Fin t, IsFreeSet Γ.toHypergraph T ord (Γ.V ∩ subBd (Δ i))) →
      HasConnectingSubdrawings Γ (⋃ i : Fin t, Γ.V ∩ subBd (Δ i)) Zs

/-- **Graph Minors XVII, (14.1)** (page 207):
"(14.1) *Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$. Let $\theta^*
\ge 1$ with $\theta^* < 2/3\theta + 1$, and let $\mathscr{T}^*$ be the set of all
separations $(A', B')$ of $G^*$ of order $< \theta^*$ such that there exists $(A, B) \in
\mathscr{T}$ with $V(A) = V(A')$ and $V(B) = V(B')$. Then $\mathscr{T}^*$ is a tangle in
$G^*$ of order $\theta^*$."
Here `G*` is the 1-skeleton of `G`, `GM17.oneSkeletonHypergraph`, and `T*` is
`GM17.oneSkeletonTangle`. -/
def GM17Theorem141Statement : Prop :=
  ∀ (V E : Type u) (G : Hypergraph V E) (θ θstar : ℕ)
    (T : Set (Hypergraph V E × Hypergraph V E)),
    1 ≤ θstar → 3 * θstar < 2 * θ + 3 → GM10.IsTangle G θ T →
    GM10.IsTangle (GM17.oneSkeletonHypergraph G) θstar (GM17.oneSkeletonTangle G T θstar)

end GraphMinor.GM19
