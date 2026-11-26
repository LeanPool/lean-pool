/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.TreeDecomposition

/-!
# Simulation axioms, good classes, linked and rotund tree-decompositions

Graph Minors IV, Sections 3–5, works with a class `ℛ` of rooted hypergraphs and a relation
"`G` is simulated in `H`" on it, and assumes four axioms about them. Here `ℛ` is a set
`R : Set (RootedHypergraph α β)` and the relation is `sim : RootedHypergraph α β →
RootedHypergraph α β → Prop`, where `sim G H` says that `G` is simulated in `H`.

* `Axiom1`, `Axiom2` (Section 3, page 235), `Axiom3` (Section 4, page 236) and `Axiom4`
  (Section 5, page 240).
* `WellSimulated sim W`: the class `W` is well-quasi-ordered by simulation.
* `IsStarDecomposition S σ`, `index S σ`, `tips S σ`: star-decompositions, their index and their
  tips (Section 3).
* `IsGood R sim 𝒮`: the class `𝒮` of star-decompositions is good (Section 3).
* `IsSymmetric 𝒮` (Section 4).
* `branching T τ s`: the parts of the branching of `(T, τ)` at `s`, a star-decomposition with tree
  `T.starAt s` (Section 3).
* `IsLinked sim T τ F` and `IsRotund T τ F` (Sections 3 and 4).
* `starClass R n`: the class `𝒮_n` of Axiom 4.
* `Theorem53Statement`: the statement of (5.3).

A class of star-decompositions is a set of pairs `(S, σ)` of a tree `S` in a type `ι` and a
function `σ : ι → RootedHypergraph α β`.
-/

@[expose] public section

namespace GraphMinor.GM04

open Hypergraph

variable {α β ι : Type*}

/-- Axiom 1: "{R}$ is a class of rooted hypergraphs, and if $G \in \mathscr{R}$ and $H$ is a rooted
hypergraph with $H \subseteq G^-$ then $H \in \mathscr{R}$." -/
def Axiom1 (R : Set (RootedHypergraph α β)) : Prop :=
  ∀ G ∈ R, ∀ H : RootedHypergraph α β, H.toHypergraph ≤ G.toHypergraph → H ∈ R

/-- Axiom 2: "The relation “$G$ is simulated in $H$” defines a quasi-order on $\mathscr{R}$." -/
def Axiom2 (R : Set (RootedHypergraph α β))
    (sim : RootedHypergraph α β → RootedHypergraph α β → Prop) : Prop :=
  (∀ G ∈ R, sim G G) ∧
    ∀ G₁ ∈ R, ∀ G₂ ∈ R, ∀ G₃ ∈ R, sim G₁ G₂ → sim G₂ G₃ → sim G₁ G₃

/-- Axiom 3: "Let $G \in \mathscr{R}$ and let $(G_1, G_2)$ be a separation of $G$ of order
$|\bar{\pi}(G)|$. Suppose that there is no separation $(H_1, H_2)$ of $G$ with $G_1^-
\subseteq H_1^-$ of order less than $|\bar{\pi}(G)|$. Then there is a march $\pi_1$ with
$\bar{\pi}_1 = \bar{\pi}(G_1)$ such that $(G_1^-, \pi_1)$ is simulated in $G$." Here
`|πBar(G)|` is the length of the march `π(G)`, and `(G₁⁻, π₁)` is a rooted hypergraph `H` with
`H⁻ = G₁⁻` and `πBar(H) = πBar(G₁)`. -/
def Axiom3 (R : Set (RootedHypergraph α β))
    (sim : RootedHypergraph α β → RootedHypergraph α β → Prop) : Prop :=
  ∀ G ∈ R, ∀ G₁ G₂ : RootedHypergraph α β, G.IsSeparation G₁ G₂ →
    separationOrder G₁.toHypergraph G₂.toHypergraph = G.roots.length →
    (¬ ∃ H₁ H₂ : RootedHypergraph α β, G.IsSeparation H₁ H₂ ∧
        G₁.toHypergraph ≤ H₁.toHypergraph ∧
        separationOrder H₁.toHypergraph H₂.toHypergraph < G.roots.length) →
    ∃ H : RootedHypergraph α β, H.toHypergraph = G₁.toHypergraph ∧ H.rootSet = G₁.rootSet ∧
      sim H G

/-- The class `W` is well-simulated: it is well-quasi-ordered by simulation, that is, for every
sequence `x₁, x₂, …` of members of `W` there are `i < i'` with `xᵢ` simulated in `x_{i'}`. -/
def WellSimulated (sim : RootedHypergraph α β → RootedHypergraph α β → Prop)
    (W : Set (RootedHypergraph α β)) : Prop :=
  ∀ x : ℕ → RootedHypergraph α β, (∀ n, x n ∈ W) → ∃ i i', i < i' ∧ sim (x i) (x i')

/-- `(S, σ)` is a star-decomposition: a tree-decomposition whose tree `S` is a star. It is then a
tree-decomposition of `σ × S`. -/
def IsStarDecomposition (S : RootedTree ι) (σ : ι → RootedHypergraph α β) : Prop :=
  S.IsStar ∧ IsTreeDecomposition (cross σ S.verts S.root) S σ

/-- The index of the star-decomposition `(S, σ)`: `max(|πBar(σ(s))| : s ∈ V(S))`. -/
def index (S : RootedTree ι) (σ : ι → RootedHypergraph α β) : ℕ :=
  S.verts.sup fun s ↦ (σ s).roots.length

/-- The tips of the star-decomposition `(S, σ)`: the `σ(s)` for `s ∈ U(S) = V(S) - {o(S)}`. -/
def tips (S : RootedTree ι) (σ : ι → RootedHypergraph α β) : Set (RootedHypergraph α β) :=
  {H | ∃ s ∈ S.edges, H = σ s}

/-- The class `𝒮` of star-decompositions is good (Graph Minors IV, Section 3):
(a) `σ × S ∈ ℛ` for each `(S, σ) ∈ 𝒮`,
(b) `𝒮` has finite index, and
(c) for every countable sequence `(Sᵢ, σᵢ)` of members of `𝒮` such that the set of all tips of all
the `(Sᵢ, σᵢ)` is well-simulated, there exist `i' > i` such that `σᵢ × Sᵢ` is simulated in
`σ_{i'} × S_{i'}`.
The first condition says that `𝒮` is a class of star-decompositions. -/
def IsGood (R : Set (RootedHypergraph α β))
    (sim : RootedHypergraph α β → RootedHypergraph α β → Prop)
    (𝒮 : Set (RootedTree ι × (ι → RootedHypergraph α β))) : Prop :=
  (∀ p ∈ 𝒮, IsStarDecomposition p.1 p.2) ∧
  (∀ p ∈ 𝒮, cross p.2 p.1.verts p.1.root ∈ R) ∧
  (∃ n, ∀ p ∈ 𝒮, index p.1 p.2 ≤ n) ∧
  ∀ x : ℕ → RootedTree ι × (ι → RootedHypergraph α β), (∀ i, x i ∈ 𝒮) →
    WellSimulated sim (⋃ i, tips (x i).1 (x i).2) →
    ∃ i i', i < i' ∧ sim (cross (x i).2 (x i).1.verts (x i).1.root)
      (cross (x i').2 (x i').1.verts (x i').1.root)

/-- The class `𝒮` of star-decompositions is symmetric (Graph Minors IV, Section 4): for every
`(S, σ) ∈ 𝒮` and every star-decomposition `(S, σ')` with `σ'(s)⁻ = σ(s)⁻` and
`πBar(σ'(s)) = πBar(σ(s))` for each `s ∈ V(S)`, we have `(S, σ') ∈ 𝒮`. -/
def IsSymmetric (𝒮 : Set (RootedTree ι × (ι → RootedHypergraph α β))) : Prop :=
  ∀ p ∈ 𝒮, ∀ σ' : ι → RootedHypergraph α β, IsStarDecomposition p.1 σ' →
    (∀ s ∈ p.1.verts, (σ' s).toHypergraph = (p.2 s).toHypergraph ∧
      (σ' s).rootSet = (p.2 s).rootSet) →
    (p.1, σ') ∈ 𝒮

/-- The parts of the branching of `(T, τ)` at `s` (Graph Minors IV, Section 3): its tree is
`T.starAt s`, the maximal star with root `s` which is a subtree of `T`; `σ(s) = τ(s)`, and
`σ(t) = τ × T^t` for every other vertex `t` of the star. It is a star-decomposition of
`τ × T^s`. -/
noncomputable def branching (T : RootedTree ι) (τ : ι → RootedHypergraph α β) (s : ι) :
    ι → RootedHypergraph α β := by
  classical exact fun t ↦ if t = s then τ s else cross τ (T.subtreeAt t) t

/-- `F ⊆ E(T)` is linked in `(T, τ)` (Graph Minors IV, Section 3): for every directed path `P` of
`T` with first edge `f₂ ∈ F` and last edge `f₁ ∈ F` such that `f₁, f₂` have the same order and no
element of `E(P) ∩ F` has smaller order, `τ × T^{f₁}` is simulated in `τ × T^{f₂}`. (The paper
defines this when `τ × T ∈ ℛ`.) -/
def IsLinked (sim : RootedHypergraph α β → RootedHypergraph α β → Prop) (T : RootedTree ι)
    (τ : ι → RootedHypergraph α β) (F : Set ι) : Prop :=
  ∀ f₁ ∈ F, ∀ f₂ ∈ F, T.Reaches f₂ f₁ → edgeOrder T τ f₁ = edgeOrder T τ f₂ →
    (∀ g ∈ T.pathEdges f₂ f₁ ∩ F, edgeOrder T τ f₁ ≤ edgeOrder T τ g) →
    sim (cross τ (T.subtreeAt f₁) f₁) (cross τ (T.subtreeAt f₂) f₂)

/-- `F ⊆ E(T)` is rotund in `(T, τ)` (Graph Minors IV, Section 4): for every directed path `P` of
`T` with first edge `f₂ ∈ F` and last edge `f₁ ∈ F` such that `f₁, f₂` have the same order, `k`
say, and no element of `F ∩ E(P)` has smaller order, there is no separation `(H₁, H₂)` of
`(τ × T)⁻` with `(τ × T^{f₁})⁻ ⊆ H₁` and `(τ × T_{f₂})⁻ ⊆ H₂` of order smaller than `k`. -/
def IsRotund (T : RootedTree ι) (τ : ι → RootedHypergraph α β) (F : Set ι) : Prop :=
  ∀ f₁ ∈ F, ∀ f₂ ∈ F, T.Reaches f₂ f₁ → edgeOrder T τ f₁ = edgeOrder T τ f₂ →
    (∀ g ∈ T.pathEdges f₂ f₁ ∩ F, edgeOrder T τ f₁ ≤ edgeOrder T τ g) →
    ¬ ∃ H₁ H₂ : Hypergraph α β,
      (cross τ T.verts T.root).toHypergraph.IsSeparation H₁ H₂ ∧
      (cross τ (T.subtreeAt f₁) f₁).toHypergraph ≤ H₁ ∧
      (cross τ (T.rootSide f₂) T.root).toHypergraph ≤ H₂ ∧
      separationOrder H₁ H₂ < edgeOrder T τ f₁

/-- The class `𝒮_n` of Axiom 4: the star-decompositions `(S, σ)` with `σ × S ∈ ℛ` and
`|V(σ(o(S)))| ≤ n`, with trees in the type `ι`. -/
def starClass (ι : Type*) (R : Set (RootedHypergraph α β)) (n : ℕ) :
    Set (RootedTree ι × (ι → RootedHypergraph α β)) :=
  {p | IsStarDecomposition p.1 p.2 ∧ cross p.2 p.1.verts p.1.root ∈ R ∧
    (p.2 p.1.root).vertexSet.ncard ≤ n}

/-- Axiom 4: "For each `n ≥ 0`, `𝒮_n` is good", for star-decompositions with trees in `ι`. -/
def Axiom4 (ι : Type*) (R : Set (RootedHypergraph α β))
    (sim : RootedHypergraph α β → RootedHypergraph α β → Prop) : Prop :=
  ∀ n : ℕ, IsGood R sim (starClass ι R n)

/-- The statement of Graph Minors IV, (5.3): assuming Axioms 1–4, "Let $G_i$ ($i = 1, 2, \dots$) be
a countable sequence of elements of $\mathscr{R}$, each of
tree-width $\le n$. Then there exist $i' > i \ge 1$ such that $G_i$ is simulated in
$G_{i'}$." Axiom 4 is assumed for trees with vertices in `ℕ`, the
trees of `TreeWidthLE`. -/
def Theorem53Statement : Prop :=
  ∀ {α β : Type*} (R : Set (RootedHypergraph α β))
    (sim : RootedHypergraph α β → RootedHypergraph α β → Prop),
    Axiom1 R → Axiom2 R sim → Axiom3 R sim → Axiom4 ℕ R sim →
    ∀ (n : ℕ) (G : ℕ → RootedHypergraph α β), (∀ i, G i ∈ R) → (∀ i, TreeWidthLE (G i) n) →
      ∃ i i', i < i' ∧ sim (G i) (G i')

end GraphMinor.GM04
