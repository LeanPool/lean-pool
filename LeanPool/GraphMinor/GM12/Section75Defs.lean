/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section76

/-!
# Graph Minors XII, (7.4): statement definition for Section 7.5

This file defines `GM12.Theorem74Statement`, formalizing **(7.4)** of Graph Minors XII
(pages 262–263), using the same definitions (`HasTangleMetric`, `deleteVertices`, `IsTwoCell`)
as `GM12.Theorem75Statement` in `GraphMinor/GM12/Section76.lean`.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Function Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 Hypergraph

universe u

/-- **(7.4)** of Graph Minors XII (pages 262–263):
"Let $\mathscr{T}$ be a respectful tangle of order $\theta \ge 2$ in a 2-cell drawing
$\Gamma$ in a connected surface $\Sigma$, and let its metric be $d$. Let $v \in V(\Gamma)$.
Then there is a 2-cell component $\Gamma'$ of $\Gamma \setminus v$ and a respectful tangle
$\mathscr{T}'$ of order $\theta - 1$ in $\Gamma'$, with metric $d'$, such that if $r'$ is
the region of $\Gamma'$ containing $v$, then* (i) *$U(\Gamma) \subseteq U(\Gamma') \cup r'$*
(ii) *$d'(a, b) \ge d(a, b) - 2$ for all $a, b \in A(\Gamma) \cap A(\Gamma')$* (iii) *$d'(a,
r') \ge d(a, \{v\}) - 1$ for all $a \in A(\Gamma) \cap A(\Gamma')$, and* (iv) *$d(a, \{v\})
\le 2$ for all $a \in A(\Gamma)$ with $a \subseteq r'$." -/
def Theorem74Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T2Space S] [ConnectedSpace S],
    IsClosedSurface S →
    ∀ (Γ : Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (v : S),
      2 ≤ θ →
      HasTangleMetric Γ θ T d →
      v ∈ Γ.V →
      ∃ (Γ' : Drawing S)
        (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ) (r' : Set S),
        Γ'.IsSubdrawing (deleteVertices Γ {v}) ∧
        (PaintingOrDrawing.drawing Γ').IsTwoCell ∧
        HasTangleMetric Γ' (θ - 1) T' d' ∧
        r' ∈ Γ'.R ∧ v ∈ r' ∧
        Γ.U ⊆ Γ'.U ∪ r' ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 2 ≤ d' a b) ∧
        (∀ a ∈ Γ.A ∩ Γ'.A, d a {v} - 1 ≤ d' a r') ∧
        (∀ a ∈ Γ.A, a ⊆ r' → d a {v} ≤ 2)

end GraphMinor.GM12
