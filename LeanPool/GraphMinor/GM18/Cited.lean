/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Higman
public import LeanPool.GraphMinor.GM04.Patchwork.Defs
public import LeanPool.GraphMinor.GM04.Patchwork.Menger
public import LeanPool.GraphMinor.GM04.TreeDecomposition
public import LeanPool.GraphMinor.GM10.Defs2
public import LeanPool.GraphMinor.GM10.Statements

/-!
# Results from Graph Minors IV and X cited in Graph Minors XVIII

This file states as `Prop`s the results from *Graph Minors IV. Tree-width and well-quasi-ordering*
(JCTB 48 (1990) 227–254) and *Graph Minors X. Obstructions to tree-decomposition* (JCTB 52 (1991)
153–190) that are cited in *Graph Minors XVIII. Tree-decompositions and well-quasi-ordering*
(JCTB 89 (2003) 77–108). `GraphMinor/GM18/Proved.lean` proves each of them:

* `GM04Theorem91Statement`: Graph Minors IV, (9.1) (page 252), well-quasi-ordering of robust
  `Ω`-patchworks of bounded tree-width under simulation.
* `GM10.Theorem52Statement` (re-exported from `GraphMinor.GM10.Statements`): Graph Minors X, (5.2)
  (page 169), `θ(G) ≤ ω(G) + 1 ≤ (3/2) θ(G)`.
* `GM10Theorem83Statement`: Graph Minors X, (8.3) (page 175), transfer of a tangle across a titanic
  separation.
* `GM10Theorem92Statement`: Graph Minors X, (9.2) (page 178), existence of a tie-breaker in every
  hypergraph.
* `GM10Theorem102Statement`: Graph Minors X, (10.2) (page 181), the `(𝒯₁, 𝒯₂)`-distinction is
  doubly `λ`-robust.
* `GM10Theorem103Statement`: Graph Minors X, (10.3) (page 181), existence of a standard
  tree-decomposition relative to mutually distinguishable tangles.
-/

@[expose] public section

namespace GraphMinor.GM18

universe u v w

/-- Statement of Graph Minors IV, (9.1) (page 252):
"Let $n \ge 0$, let $\Omega$ be a well-quasi-order, and let $P_i = (G_i, \mu_i, \Delta_i,
\phi_i)$ $(i = 1, 2, \dots)$ be a countable sequence of robust $\Omega$-patchworks, where
each $G_i$ has tree-width $\le n$. Then there exist $i' > i \ge 1$ such that there is a
realizable expansion of $P_i$ in $P_{i'}$." -/
def GM04Theorem91Statement : Prop :=
  ∀ {Ω : Type w} [Preorder Ω] {α : Type u} {β : Type v} (n : ℕ)
    (P : ℕ → GM04.Patchwork Ω α β),
    WellQuasiOrderedLE Ω →
    (∀ i, (P i).IsRobust) →
    (∀ i, GM04.TreeWidthLE (P i).G n) →
    ∃ i i', i < i' ∧ GM04.Simulated (P i) (P i')

/-- Statement of Graph Minors X, (8.3) (page 175):
"Let $(C, D)$ be a separation of a hypergraph $G$, and let $(C', D)$ be a titanic separation
of a hypergraph $G'$, with $V(C \cap D) = V(C' \cap D)$. Let $\mathscr{T}$ be a tangle in
$G$ of order $\theta \ge 2$ with $(C, D) \in \mathscr{T}$. Let $\mathscr{T}'$ be the set of
all separations $(A', B')$ of $G'$ of order $< \theta$ such that there exists $(A, B) \in
\mathscr{T}$ with $E(A \cap D) = E(A' \cap D)$. Then $\mathscr{T}'$ is a tangle in $G'$ of
order $\theta$." -/
def GM10Theorem83Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (G G' C C' D : Hypergraph α β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ),
    G.IsSeparation C D →
    GM10.IsTitanic G' C' D →
    (C ∩ D).vertexSet = (C' ∩ D).vertexSet →
    GM10.IsTangle G θ 𝒯 →
    2 ≤ θ →
    (C, D) ∈ 𝒯 →
    GM10.IsTangle G' θ (GM10.titanicTransferredTangle G' D 𝒯 θ)

/-- Statement of Graph Minors X, (9.2) (page 178):
"In every hypergraph there is a tie-breaker." -/
def GM10Theorem92Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Hypergraph α β),
    ∃ (Λ : Type) (_ : LinearOrder Λ) (lam : Hypergraph α β × Hypergraph α β → Λ),
      GM10.IsTieBreaker G lam

/-- Statement of Graph Minors X, (10.2) (page 181):
"If $\mathscr{T}_1, \mathscr{T}_2$ are distinguishable tangles in $G$, the $(\mathscr{T}_1,
\mathscr{T}_2)$-distinction is doubly $\lambda$-robust." -/
def GM10Theorem102Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {Λ : Type w} [LinearOrder Λ]
    (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → Λ)
    (θ₁ θ₂ : ℕ) (𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β))
    (A B : Hypergraph α β),
    GM10.IsTieBreaker G lam →
    GM10.IsTangle G θ₁ 𝒯₁ →
    GM10.IsTangle G θ₂ 𝒯₂ →
    GM10.IsDistinction lam 𝒯₁ 𝒯₂ A B →
    GM10.IsDoublyLambdaRobust G lam A B

/-- Statement of Graph Minors X, (10.3) (page 181):
"Let $\mathscr{T}_1, \dots, \mathscr{T}_n$ be mutually distinguishable tangles in a
hypergraph $G$ with $n \ge 1$, and let $\lambda$ be a tie-breaker. Then there is a
tree-decomposition $(T, \tau)$ of $G$, where $V(T) = \{t_1, \dots, t_n\}$, with the
following properties:* (i) *For every $e \in E(T)$ and for $1 \le i \le n$, if $T_1, T_2$
are the components of $T \setminus e$ and $t_i \in V(T_1)$ then* $$ \left( \bigcup_{t \in
V(T_1)} \tau(t), \bigcup_{t \in V(T_2)} \tau(t) \right) \notin \mathscr{T}_i. $$ (ii) *For
all $i \ne j$ with $1 \le i, j \le n$, let $e$ be the edge of the path of $T$ between $t_i$
and $t_j$ making separations of smallest $\lambda$-order; then these separations are the
$(\mathscr{T}_i, \mathscr{T}_j)$- and $(\mathscr{T}_j, \mathscr{T}_i)$-distinctions." -/
def GM10Theorem103Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {Λ : Type w} [LinearOrder Λ] {n : ℕ}
    (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → Λ)
    (θ : Fin n → ℕ) (𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β)),
    1 ≤ n →
    GM10.IsTieBreaker G lam →
    (∀ i : Fin n, GM10.IsTangle G (θ i) (𝒯 i)) →
    (∀ i j : Fin n, i ≠ j → GM10.AreDistinguishable (𝒯 i) (𝒯 j)) →
    ∃ (T : SimpleGraph (Fin n)) (τ : Fin n → Hypergraph α β),
      GM10.IsStandardTreeDecomposition G lam 𝒯 T τ

end GraphMinor.GM18
