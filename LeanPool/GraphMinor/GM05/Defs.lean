/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM01.Defs
public import LeanPool.GraphMinor.GM10.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Definitions for Graph Minors V, Sections 1–7 (The Grid Theorem)

This file formalizes the definitions and parameters of
N. Robertson and P. D. Seymour, *Graph Minors. V. Excluding a planar graph*,
J. Combin. Theory Ser. B **41** (1986), 92–114, Sections 1–7 (pages 92–109):

- **Section 1 (pages 92–94):**
  - Tree-decompositions `(T, χ)` of a graph `G` (`IsTreeDecomposition`), where `T : SimpleGraph ι`
    is a finite tree (`[Fintype ι]`, `T.IsTree`) and `χ : ι → Set V` assigns a subset of `V(G)` to
    each vertex of `T` satisfying conditions (i)–(iii).
  - The width of a tree-decomposition (`decompWidth` and the predicate `WidthLE χ w` for width at
    most `w`), and the tree-width of `G` (both as the predicate `TreeWidthLE G w`, stating that `G`
    has a tree-decomposition of width at most `w`, and as the minimum `treeWidth G : ℕ` of `w ≥ 0`
    such that `TreeWidthLE G w` holds).
  - Relabelling of tree-decompositions along an equivalence `e : ι ≃ ι'`
    (`IsTreeDecomposition.relabel`, `treeWidthLE_of_isTreeDecomposition`).
  - Separations `(V₁, V₂)` of a graph `G` (`IsSeparation`).
- **Section 2 (pages 94–95):**
  - The function `α(k, n)` (`α θ k n`) and the parameters `θ₁, …, θ₉` and `φ_k` (`θ₁ θ`, …,
    `θ₉ θ`, `φ θ k`).
- **Section 4 (pages 97–100):**
  - The parameter `ψ_k` (`ψ θ k`).
- **Section 6 (pages 102–106):**
  - The vertex-weight sum `w(X)` (`weightSum w X`).
-/

@[expose] public section

namespace GraphMinor.GM05

open SimpleGraph GM01

variable {V ι ι' : Type*}

/-! ## Section 1: Tree-Decompositions, Tree-Width, Separations, and Components -/

export GM10 (OnTreePath)

/-- `(T, χ)` is a tree-decomposition of a graph `G` (Graph Minors V, Section 1, pages 92–93):
"A *tree-decomposition* $(T, \chi)$ of a graph $G$ is a tree $T$ together with a family
$\chi = (X_t : t \in V(T))$ of subsets of $V(G)$, such that
(i) $\bigcup(X_t : t \in V(T)) = V(G)$;
(ii) for each edge $e$ of $G$ there exists $t \in V(T)$ such that $e$ has both ends (or its end, in
  the case of a loop) in $X_t$; ...
(iii) for $t, t', t'' \in V(T)$, if $t'$ lies on the path of $T$ between $t$ and $t''$, then
  $X_t \cap X_{t''} \subseteq X_{t'}$." -/
structure IsTreeDecomposition [Fintype ι] (G : (⊤ : SimpleGraph V).Subgraph)
    (T : SimpleGraph ι) (χ : ι → Set V) : Prop where
  /-- `T` is a tree. -/
  isTree : T.IsTree
  /-- (i) `⋃ (X_t : t ∈ V(T)) = V(G)`. -/
  iUnion_eq : (⋃ t : ι, χ t) = G.verts
  /-- (ii) For each edge of `G` there exists `t ∈ V(T)` containing both ends of the edge. -/
  adj_mem : ∀ ⦃u v : V⦄, G.Adj u v → ∃ t : ι, u ∈ χ t ∧ v ∈ χ t
  /-- (iii) For `t, t', t'' ∈ V(T)`, if `t'` lies on the path of `T` between `t` and `t''`, then
  `X_t ∩ X_{t''} ⊆ X_{t'}`. -/
  inter_subset : ∀ ⦃t t' t'' : ι⦄, OnTreePath T t t'' t' → χ t ∩ χ t'' ⊆ χ t'

/-- The tree-decomposition `(T, χ)` has width at most `w` (Graph Minors V, Section 1, page 93):
"The width of the tree-decomposition is $\max(|X_t| - 1 : t \in V(T))$;" Thus the width is `≤ w`
for `w : ℕ` when `|X_t| ≤ w + 1` for every `t ∈ V(T)`. -/
def WidthLE (χ : ι → Set V) (w : ℕ) : Prop :=
  ∀ t : ι, (χ t).ncard ≤ w + 1

/-- The width `max(|X_t| - 1 : t ∈ V(T))` of a tree-decomposition `(T, χ)` as a natural number
(Graph Minors V, Section 1, page 93). -/
noncomputable def decompWidth (χ : ι → Set V) : ℕ :=
  sSup (Set.range fun t : ι ↦ (χ t).ncard - 1)

/-- `G` has tree-width at most `w` (Graph Minors V, Section 1, page 93):
"and the *tree-width* of $G$ is the minimum $w \ge 0$ such that $G$ has a tree-decomposition
of width $\le w$."

The existential quantifies over finite trees whose vertex type `ι` lies in `Type`; see
`IsTreeDecomposition.relabel` and `treeWidthLE_of_isTreeDecomposition` for any finite index type
`ι : Type*`. -/
def TreeWidthLE (G : (⊤ : SimpleGraph V).Subgraph) (w : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (χ : ι → Set V),
    IsTreeDecomposition G T χ ∧ WidthLE χ w

/-- The tree-width of `G` as a natural number (Graph Minors V, Section 1, page 93):
"the *tree-width* of $G$ is the minimum $w \ge 0$ such that $G$ has a tree-decomposition of
width $\le w$." -/
noncomputable def treeWidth (G : (⊤ : SimpleGraph V).Subgraph) : ℕ :=
  sInf {w : ℕ | TreeWidthLE G w}

/-- Relabelling a tree-decomposition `(T, χ)` along an equivalence `e : ι ≃ ι'` gives a
tree-decomposition `(T.map e.toEmbedding, χ ∘ e.symm)`. -/
theorem IsTreeDecomposition.relabel [Fintype ι] [Fintype ι'] {G : (⊤ : SimpleGraph V).Subgraph}
    {T : SimpleGraph ι} {χ : ι → Set V} (h : IsTreeDecomposition G T χ) (e : ι ≃ ι') :
    IsTreeDecomposition G (T.map e.toEmbedding) (χ ∘ e.symm) where
  isTree := (SimpleGraph.Iso.map e T).isTree_iff.1 h.isTree
  iUnion_eq := by
    rw [← h.iUnion_eq]
    ext v
    simp only [Set.mem_iUnion, Function.comp_apply]
    exact e.symm.exists_congr (fun _ ↦ Iff.rfl)
  adj_mem {u v} hadj := by
    obtain ⟨t, hu, hv⟩ := h.adj_mem hadj
    exact ⟨e t, by simpa using hu, by simpa using hv⟩
  inter_subset {t₁ t₂ t₃} hp := by
    apply h.inter_subset
    rw [← GM10.onTreePath_map e]
    simpa using hp

/-- Relabelling a family of bags `χ` along an equivalence `e : ι ≃ ι'` preserves `WidthLE`. -/
theorem widthLE_comp_equiv {χ : ι → Set V} {w : ℕ} (e : ι ≃ ι') :
    WidthLE (χ ∘ e.symm) w ↔ WidthLE χ w :=
  ⟨fun h t ↦ by simpa using h (e t), fun h t' ↦ h (e.symm t')⟩

/-- Relabelling a tree-decomposition along an equivalence `e : ι ≃ ι'` preserves `decompWidth`. -/
theorem decompWidth_comp_equiv (χ : ι → Set V) (e : ι ≃ ι') :
    decompWidth (χ ∘ e.symm) = decompWidth χ := by
  simp only [decompWidth]
  congr 1
  ext n
  simp only [Set.mem_range, Function.comp_apply]
  exact e.symm.exists_congr (fun _ ↦ Iff.rfl)

/-- Any tree-decomposition `(T, χ)` of `G` of width `≤ w` on an arbitrary finite index type
`ι : Type*` witnesses `TreeWidthLE G w`. -/
theorem treeWidthLE_of_isTreeDecomposition [Fintype ι] {G : (⊤ : SimpleGraph V).Subgraph}
    {T : SimpleGraph ι} {χ : ι → Set V} {w : ℕ}
    (h : IsTreeDecomposition G T χ) (hw : WidthLE χ w) :
    TreeWidthLE G w := by
  let e := Fintype.equivFin ι
  exact ⟨Fin (Fintype.card ι), inferInstance, T.map e.toEmbedding, χ ∘ e.symm,
    h.relabel e, (widthLE_comp_equiv e).2 hw⟩

/-- Any tree-decomposition `(T, χ)` of `G` of width `≤ w` on an arbitrary finite index type
`ι : Type*` bounds `treeWidth G ≤ w`. -/
theorem treeWidth_le_of_isTreeDecomposition [Fintype ι] {G : (⊤ : SimpleGraph V).Subgraph}
    {T : SimpleGraph ι} {χ : ι → Set V} {w : ℕ}
    (h : IsTreeDecomposition G T χ) (hw : WidthLE χ w) :
    treeWidth G ≤ w :=
  Nat.sInf_le (treeWidthLE_of_isTreeDecomposition h hw)

/-- `(V₁, V₂)` is a separation of `G` (Graph Minors V, Section 1, page 94):
"A *separation* of a graph $G$ is a pair $(V_1, V_2)$, where $V_1, V_2 \subseteq V(G)$, $V_1
\cup V_2 = V(G)$, and no vertex of $V_1 - V_2$ is adjacent to any vertex of $V_2 - V_1$." -/
structure IsSeparation (G : (⊤ : SimpleGraph V).Subgraph) (V₁ V₂ : Set V) : Prop where
  /-- `V₁ ⊆ V(G)`. -/
  subset_left : V₁ ⊆ G.verts
  /-- `V₂ ⊆ V(G)`. -/
  subset_right : V₂ ⊆ G.verts
  /-- `V₁ ∪ V₂ = V(G)`. -/
  union_eq : V₁ ∪ V₂ = G.verts
  /-- No vertex of `V₁ - V₂` is adjacent in `G` to any vertex of `V₂ - V₁`. -/
  not_adj : ∀ ⦃u v : V⦄, u ∈ V₁ \ V₂ → v ∈ V₂ \ V₁ → ¬ G.Adj u v

/-! ## Section 2: The Parameters `α`, `θ₁, …, θ₉`, and `φ_k` -/

/-- The function `α(k, n)` (Graph Minors V, Section 2, page 94):
"Now let $\theta \ge 6$ be some even number. For $k \ge 2$, $n \ge 0$, define $\alpha(k, n)$
inductively by
$$
\begin{aligned}
\alpha(2, n) &= n + 1 \\
\alpha(k, n) &= 2^{n\theta^4} + \alpha(k - 1, 2^{n\theta^4} + n + 1), \quad \text{for } k \ge 3.
\end{aligned}
$$" -/
def α (θ : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | 1, n => n + 1
  | 2, n => n + 1
  | k + 3, n => 2 ^ (n * θ ^ 4) + α θ (k + 2) (2 ^ (n * θ ^ 4) + n + 1)

/-- The parameter `θ₁ = 2 α(θ²/2, θ²/2)` (Graph Minors V, Section 2, page 94):
"Define `θ₁ = 2 α(θ²/2, θ²/2)`." -/
def θ₁ (θ : ℕ) : ℕ :=
  2 * α θ (θ ^ 2 / 2) (θ ^ 2 / 2)

/-- Auxiliary upward recursion for `φ_k` in terms of `d = θ₁ - k`. -/
def φAux (θ : ℕ) : ℕ → ℕ
  | 0 => θ ^ 2 / 2
  | d + 1 =>
    let m := φAux θ d
    m * 2 ^ (m * θ ^ 2)

/-- The parameter `φ_k` (Graph Minors V, Section 2, page 94):
"Define $\phi_{\theta_1} = \theta^2/2$, and for $0 \le k < \theta_1$ define $\phi_k$
inductively by $$ \phi_k = \phi_{k+1} 2^{\phi_{k+1} \theta^2}." -/
def φ (θ k : ℕ) : ℕ :=
  φAux θ (θ₁ θ - k)

/-- The parameter `θ₂ = φ₀ + 2 φ₁ + 2 φ₂ + ⋯ + 2 φ_{θ₁ - 1} + φ_{θ₁}`
(Graph Minors V, Section 2, page 95). -/
def θ₂ (θ : ℕ) : ℕ :=
  φ θ 0 + (∑ i ∈ Finset.Ico 1 (θ₁ θ), 2 * φ θ i) + φ θ (θ₁ θ)

/-- The parameter `θ₃ = (θ²/2)^{θ₂ - 1}` (Graph Minors V, Section 2, page 95). -/
def θ₃ (θ : ℕ) : ℕ :=
  (θ ^ 2 / 2) ^ (θ₂ θ - 1)

/-- The parameter `θ₄ = θ₂ (θ₃.choose θ₂) + (θ²/2) (θ₃.choose (θ²/2))`
(Graph Minors V, Section 2, page 95). -/
def θ₄ (θ : ℕ) : ℕ :=
  θ₂ θ * (θ₃ θ).choose (θ₂ θ) + (θ ^ 2 / 2) * (θ₃ θ).choose (θ ^ 2 / 2)

/-- The parameter `θ₅ = (θ²/2)^{θ₄ - 1}` (Graph Minors V, Section 2, page 95). -/
def θ₅ (θ : ℕ) : ℕ :=
  (θ ^ 2 / 2) ^ (θ₄ θ - 1)

/-- The parameter `θ₆ = θ₃ (θ₅.choose θ₄) + (θ²/2) (θ₅.choose (θ²/2))`
(Graph Minors V, Section 2, page 95). -/
def θ₆ (θ : ℕ) : ℕ :=
  θ₃ θ * (θ₅ θ).choose (θ₄ θ) + (θ ^ 2 / 2) * (θ₅ θ).choose (θ ^ 2 / 2)

/-- The parameter `θ₇ = α(θ₅, θ₆)` (Graph Minors V, Section 2, page 95). -/
def θ₇ (θ : ℕ) : ℕ :=
  α θ (θ₅ θ) (θ₆ θ)

/-- The parameter `θ₈ = 3 θ₅ (3^{θ₅} - 1) / 4` (Graph Minors V, Section 2, page 95). -/
def θ₈ (θ : ℕ) : ℕ :=
  3 * θ₅ θ * (3 ^ θ₅ θ - 1) / 4

/-- The parameter `θ₉ = θ₇ (θ₈ + 1) + 1` (Graph Minors V, Section 2, page 95). -/
def θ₉ (θ : ℕ) : ℕ :=
  θ₇ θ * (θ₈ θ + 1) + 1

/-! ## Section 4: The Parameter `ψ_k` -/

/-- The parameter `ψ_k` (Graph Minors V, Section 4, page 99):
"Define $\phi_{\theta_1}, \dots, \phi_0$ as in Section 2. Define $\psi_{\theta_1} = 0$, and
for $0 \le k < \theta_1$, define $$\psi_k = \phi_k + 2\phi_{k+1} + 2\phi_{k+2} + \dots +
2\phi_{\theta_1 - 1} + \phi_{\theta_1}.$$ Then for $0 \le k < \theta_1$ we have $\psi_k =
\psi_{k+1} + \phi_k + \phi_{k+1}$." -/
def ψ (θ k : ℕ) : ℕ :=
  if k < θ₁ θ then
    φ θ k + (∑ i ∈ Finset.Ico (k + 1) (θ₁ θ), 2 * φ θ i) + φ θ (θ₁ θ)
  else
    0

/-! ## Section 6: Vertex Weights -/

/-- The sum `w(X) = ∑_{v ∈ X} w(v)` of a non-negative integer vertex weight `w : V → ℕ` over a set
`X ⊆ V(G)` (Graph Minors V, Section 6, page 103):
"Let $\mathbf{Z}^+$ denote the set of non-negative integers. If $G$ is a graph and
$w \colon V(G) \to \mathbf{Z}^+$ is a function and $X \subseteq V(G)$, then $w(X)$ denotes
$\sum_{v \in X} w(v)$." -/
noncomputable def weightSum (w : V → ℕ) (X : Set V) : ℕ :=
  ∑ᶠ v ∈ X, w v

end GraphMinor.GM05
