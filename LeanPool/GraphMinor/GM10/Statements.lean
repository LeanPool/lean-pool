/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs

/-!
# Statements of Graph Minors X, Sections 4 and 5

These results of Graph Minors X are proved in `TreeWidth.lean` (`theorem_4_3_statement` and the
next three theorems). Each statement follows the paper's wording.
-/

@[expose] public section

namespace GraphMinor.GM10

open Hypergraph

/-- Graph Minors X, (4.3) (page 165):
"(4.3) *For any hypergraph $G$, $\max(\beta(G), \gamma(G)) = \theta(G)$ unless $\gamma(G) = 0$ and
$V(G) \ne \emptyset$.*" -/
def Theorem43Statement : Prop :=
  ∀ {α β : Type*} (G : Hypergraph α β), ¬ (maxEdgeSize G = 0 ∧ G.vertexSet.Nonempty) →
    max (branchWidth G) (maxEdgeSize G) = tangleNumber G

/-- Graph Minors X, (4.5) (page 167): "Let $\theta \ge 2$, and let $\mathscr{T}$ be a set of
separations of a hypergraph $G$, each
of order $< \theta$. Suppose that the first tangle axiom holds, and* (i) *if $(A_1, B_1),
(A_2, B_2) \in \mathscr{T}$ then $B_1 \not\subseteq A_2$* (ii) *there do not exist
subhypergraphs $A_1, A_2, A_3 \subseteq G$, mutually edge-disjoint, with $A_1 \cup A_2 \cup
A_3 = G$ and with $(A_1, A_2 \cup A_3)$, $(A_2, A_3 \cup A_1)$, $(A_3, A_1 \cup A_2)$ all in
$\mathscr{T}$.* *Then the second tangle axiom holds." -/
def Theorem45Statement : Prop :=
  ∀ {α β : Type*} (G : Hypergraph α β) (θ : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
    2 ≤ θ →
    (∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → G.IsSeparation A B ∧ separationOrder A B < θ) →
    TangleAxiom1 G θ 𝒯 →
    (∀ ⦃A₁ B₁ A₂ B₂ : Hypergraph α β⦄, (A₁, B₁) ∈ 𝒯 → (A₂, B₂) ∈ 𝒯 → ¬ B₁ ≤ A₂) →
    (¬ ∃ A₁ A₂ A₃ : Hypergraph α β, A₁ ≤ G ∧ A₂ ≤ G ∧ A₃ ≤ G ∧
      Disjoint A₁.edgeSet A₂.edgeSet ∧ Disjoint A₂.edgeSet A₃.edgeSet ∧
      Disjoint A₁.edgeSet A₃.edgeSet ∧ A₁ ∪ A₂ ∪ A₃ = G ∧
      (A₁, A₂ ∪ A₃) ∈ 𝒯 ∧ (A₂, A₃ ∪ A₁) ∈ 𝒯 ∧ (A₃, A₁ ∪ A₂) ∈ 𝒯) →
    TangleAxiom2 G 𝒯

/-- Graph Minors X, (5.1) (page 168):
"(5.1) *For any hypergraph $G$, $\max(\beta(G), \gamma(G)) \le \omega(G) + 1 \le
\max(\lfloor(3/2) \beta(G)\rfloor, \gamma(G), 1)$.*" -/
def Theorem51Statement : Prop :=
  ∀ {α β : Type*} (G : Hypergraph α β),
    max (branchWidth G) (maxEdgeSize G) ≤ treeWidthPlusOne G ∧
      treeWidthPlusOne G ≤ max (max (3 * branchWidth G / 2) (maxEdgeSize G)) 1

/-- Graph Minors X, (5.2) (page 169): "For any hypergraph $G$, $\theta(G) \le \omega(G) + 1 \le
(3/2) \theta(G)$." The second inequality is written `2 (ω(G) + 1) ≤ 3 θ(G)`. -/
def Theorem52Statement : Prop :=
  ∀ {α β : Type*} (G : Hypergraph α β),
    tangleNumber G ≤ treeWidthPlusOne G ∧ 2 * treeWidthPlusOne G ≤ 3 * tangleNumber G

end GraphMinor.GM10
