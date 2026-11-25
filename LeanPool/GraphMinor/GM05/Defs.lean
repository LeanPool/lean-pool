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
- **Section 3 (pages 95–97):**
  - `Statement31`, the statement of (3.1) (quoted from Graph Minors I, Theorem (2.9)).
- **Section 4 (pages 97–100):**
  - `(m, n)`-webs (`IsWeb`, `HasWeb`), spiders of an `(m, n)`-web (`IsSpider`,
    `HasWebWithSpiders`), the parameter `ψ_k` (`ψ θ k`), and `Statement43`, the statement of (4.3)
    (quoted from Graph Minors I, Theorem (2.8)).
- **Section 5 (pages 100–102):**
  - `(m, n)`-meshes (`IsMesh`, `HasMesh`).
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

/-! ## Section 3: Statement (3.1) -/

/-- Graph Minors V, (3.1) (page 95), quoted from Graph Minors I, Theorem (2.9) (page 49):
"Let $B_1, \ldots, B_n$ be disjoint connected subgraphs of $G \in \mathscr{F}_\theta$, and
let $V' \subseteq V(G)$. Let $r \ge 0$ be an integer. Then at least one of the following is
true:* (i) *there exists $J \subseteq \{1, \ldots, n\}$ with $|J| = r$ such that for each $j
\in J$ there is a path $P_j$ in $G$ from $B_j$ to $V'$, and the paths $P_j (j \in J)$ are
disjoint, and each has no internal vertex in $V' \cup \bigcup_{j \in J} V(B_j)$;* (ii)
*there exists $X \subseteq V(G)$ and $J \subseteq \{1, \ldots, n\}$ with $|X| + |J| \le
2^{r\theta^4}$ such that $X$ separates $V'$ from every $B_j$ ($j \in \{1, \ldots, n\} - J$)." -/
def Statement31 : Prop :=
  ∀ {V : Type*} {G : (⊤ : SimpleGraph V).Subgraph} {θ n : ℕ},
    6 ≤ θ → Even θ → G.verts.Finite → G ∈ 𝓕 θ →
    ∀ (B : Fin n → (⊤ : SimpleGraph V).Subgraph),
      (∀ j, B j ≤ G) → (∀ j, (B j).Connected) →
      Pairwise (fun j j' ↦ Disjoint (B j).verts (B j').verts) →
      ∀ (V' : Set V), V' ⊆ G.verts → ∀ (r : ℕ),
        (∃ (J : Finset (Fin n)) (P : J → Path V),
          J.card = r ∧
          (∀ j : J, (P j).IsFromTo G (B j.1).verts V') ∧
          Pairwise (fun j j' : J ↦ Disjoint (P j).verts (P j').verts) ∧
          (∀ j : J, Disjoint (P j).internalVerts (V' ∪ ⋃ j' ∈ J, (B j').verts))) ∨
        (∃ (X : Set V) (J : Finset (Fin n)),
          X ⊆ G.verts ∧ X.ncard + J.card ≤ 2 ^ (r * θ ^ 4) ∧
          ∀ j : Fin n, j ∉ J → Separates G X V' (B j).verts)

/-! ## Section 4: Webs, Spiders, `ψ_k`, and Statement (4.3) -/

/-- `((A₁, …, Aₘ), (B₁, …, Bₙ))` is an `(m, n)`-web in `G` (Graph Minors V, Section 4, page 97):
"Let $G$ be a graph. An ($m, n$)-web in $G$ is a pair $((A_1, \dots, A_m), (B_1, \dots,
B_n))$, where $A_1, \dots, A_m, B_1, \dots, B_n$ are paths of $G$, such that (i) $A_1,
\dots, A_m$ are disjoint, and $B_1, \dots, B_n$ are disjoint; (ii) each $A_i$ meets each
$B_j$; (iii) $A_1, \dots, A_m, B_1, \dots, B_n$ are pairwise edge-disjoint. (We permit $m =
0$ and $n = 0$.)" -/
structure IsWeb (G : (⊤ : SimpleGraph V).Subgraph) {m n : ℕ}
    (A : Fin m → Path V) (B : Fin n → Path V) : Prop where
  /-- Each `A_i` is a path of `G`. -/
  isIn_left : ∀ i, (A i).IsIn G
  /-- Each `B_j` is a path of `G`. -/
  isIn_right : ∀ j, (B j).IsIn G
  /-- (i) `A₁, …, Aₘ` are vertex-disjoint. -/
  disjoint_left : Pairwise fun i i' ↦ Disjoint (A i).verts (A i').verts
  /-- (i) `B₁, …, Bₙ` are vertex-disjoint. -/
  disjoint_right : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts
  /-- (ii) Each `A_i` meets each `B_j`. -/
  meets : ∀ i j, ((A i).verts ∩ (B j).verts).Nonempty
  /-- (iii) `A₁, …, Aₘ, B₁, …, Bₙ` are pairwise edge-disjoint (since `A₁, …, Aₘ` are vertex-disjoint
  and `B₁, …, Bₙ` are vertex-disjoint, this is equivalent to each `A_i` and `B_j` being
  edge-disjoint). -/
  edge_disjoint : ∀ i j, Disjoint (A i).edgeSet (B j).edgeSet

/-- `G` has an `(m, n)`-web (Graph Minors V, Section 4, page 97). -/
def HasWeb (G : (⊤ : SimpleGraph V).Subgraph) (m n : ℕ) : Prop :=
  ∃ (A : Fin m → Path V) (B : Fin n → Path V), IsWeb G A B

/-- `C` is a spider of the `(m, n)`-web `(A, B)` in `G` (Graph Minors V, Section 4, page 98):
"Let $((A_1, \dots, A_m), (B_1, \dots, B_n))$ be an ($m, n$)-web in a graph $G$. A spider of
this web is a connected subgraph $C$ of $G$ such that (i) $C$ is edge-disjoint from $B_1,
\dots, B_n$; (ii) for $1 \le i \le m$, $C$ has a unique vertex in common with $A_i$, and
that vertex has valency 1 in $C$." -/
structure IsSpider (G : (⊤ : SimpleGraph V).Subgraph) {m n : ℕ}
    (A : Fin m → Path V) (B : Fin n → Path V)
    (C : (⊤ : SimpleGraph V).Subgraph) : Prop where
  /-- `C` is a subgraph of `G`. -/
  le : C ≤ G
  /-- `C` is connected. -/
  connected : C.Connected
  /-- (i) `C` is edge-disjoint from `B₁, …, Bₙ`. -/
  edge_disjoint : ∀ j, Disjoint C.edgeSet (B j).edgeSet
  /-- (ii) For `1 ≤ i ≤ m`, `C` has a unique vertex in common with `A_i`, and that vertex has
  valency `1` in `C`. -/
  unique_leaf : ∀ i, ∃ v : V, C.verts ∩ (A i).verts = {v} ∧ IsLeafOf C v

/-- `G` has an `(m, n)`-web with `k` pairwise edge-disjoint spiders
(Graph Minors V, Section 4, (4.4)–(4.5), pages 98–99). -/
def HasWebWithSpiders (G : (⊤ : SimpleGraph V).Subgraph) (m n k : ℕ) : Prop :=
  ∃ (A : Fin m → Path V) (B : Fin n → Path V) (C : Fin k → (⊤ : SimpleGraph V).Subgraph),
    IsWeb G A B ∧ (∀ l, IsSpider G A B (C l)) ∧
      Pairwise fun l l' ↦ Disjoint (C l).edgeSet (C l').edgeSet

/-- Graph Minors V, (4.3) (page 98), quoted from Graph Minors I, Theorem (2.8) (page 48):
"Let $A_1, A_2 \subseteq V(G)$, where $G \in \mathcal{F}_\theta$, and let $D_1, \dots, D_m$
be disjoint subgraphs of $G$, each with at most $d$ components. Suppose that there are $n$
disjoint paths in $G$ from $A_1$ to $A_2$, and for $1 \le k \le m$, $D_k$ separates $A_1$
and $A_2$. Then either $n < d\theta^2/2$ or $m < 2^{d\theta^2/2}(\theta^2 +
2d\theta^{2\theta})$."

Note: we include `0 < d + n` to exclude the degenerate `d = 0, n = 0` case (`A₁ = A₂ = ∅`,
`D_k = ⊥`), where `n < 0` is impossible and `m` can be arbitrary. -/
def Statement43 : Prop :=
  ∀ {V : Type*} {G : (⊤ : SimpleGraph V).Subgraph} {θ m n d : ℕ},
    6 ≤ θ → Even θ → 0 < d + n → G.verts.Finite → G ∈ 𝓕 θ →
    ∀ (A₁ A₂ : Set V), A₁ ⊆ G.verts → A₂ ⊆ G.verts →
    ∀ (D : Fin m → (⊤ : SimpleGraph V).Subgraph),
      (∀ k, D k ≤ G) →
      Pairwise (fun k k' ↦ Disjoint (D k).verts (D k').verts) →
      (∀ k, numComponents (D k) ≤ d) →
      (∃ P : Fin n → Path V, IsDisjointPathFamily G A₁ A₂ P) →
      (∀ k, Separates G (D k).verts A₁ A₂) →
      n < d * θ ^ 2 / 2 ∨ m < 2 ^ (d * θ ^ 2 / 2) * (θ ^ 2 + 2 * d * θ ^ (2 * θ))

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

/-! ## Section 5: Meshes -/

/-- `((A₁, …, Aₘ), (B₁, …, Bₙ))` is an `(m, n)`-mesh in `G` (Graph Minors V, Section 5, page 100):
"An $(m, n)$-mesh in a graph $G$ is a pair $((A_1, ..., A_m), (B_1, ..., B_n))$, where (i)
$A_1, ..., A_m, B_1, ..., B_n$ are all connected subgraphs of $G$; (ii) $A_1, ..., A_m$ are
disjoint, and $B_1, ..., B_n$ are disjoint; (iii) each $A_i$ meets each $B_j$." -/
structure IsMesh (G : (⊤ : SimpleGraph V).Subgraph) {m n : ℕ}
    (A : Fin m → (⊤ : SimpleGraph V).Subgraph)
    (B : Fin n → (⊤ : SimpleGraph V).Subgraph) : Prop where
  /-- (i) Each `A_i` is a subgraph of `G`. -/
  le_left : ∀ i, A i ≤ G
  /-- (i) Each `B_j` is a subgraph of `G`. -/
  le_right : ∀ j, B j ≤ G
  /-- (i) Each `A_i` is connected. -/
  connected_left : ∀ i, (A i).Connected
  /-- (i) Each `B_j` is connected. -/
  connected_right : ∀ j, (B j).Connected
  /-- (ii) `A₁, …, Aₘ` are vertex-disjoint. -/
  disjoint_left : Pairwise fun i i' ↦ Disjoint (A i).verts (A i').verts
  /-- (ii) `B₁, …, Bₙ` are vertex-disjoint. -/
  disjoint_right : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts
  /-- (iii) Each `A_i` meets each `B_j`. -/
  meets : ∀ i j, ((A i).verts ∩ (B j).verts).Nonempty

/-- `G` has an `(m, n)`-mesh (Graph Minors V, Section 5, page 100). -/
def HasMesh (G : (⊤ : SimpleGraph V).Subgraph) (m n : ℕ) : Prop :=
  ∃ (A : Fin m → (⊤ : SimpleGraph V).Subgraph) (B : Fin n → (⊤ : SimpleGraph V).Subgraph),
    IsMesh G A B

/-! ## Section 6: Vertex Weights -/

/-- The sum `w(X) = ∑_{v ∈ X} w(v)` of a non-negative integer vertex weight `w : V → ℕ` over a set
`X ⊆ V(G)` (Graph Minors V, Section 6, page 103):
"Let $\mathbf{Z}^+$ denote the set of non-negative integers. If $G$ is a graph and
$w \colon V(G) \to \mathbf{Z}^+$ is a function and $X \subseteq V(G)$, then $w(X)$ denotes
$\sum_{v \in X} w(v)$." -/
noncomputable def weightSum (w : V → ℕ) (X : Set V) : ℕ :=
  ∑ᶠ v ∈ X, w v

end GraphMinor.GM05
