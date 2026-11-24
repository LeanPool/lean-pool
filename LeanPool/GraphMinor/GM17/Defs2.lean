/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Defs
public import LeanPool.GraphMinor.GM10.Defs2

/-!
# Remaining Definitions of Graph Minors XVII (*Taming a Vortex*)

This file extends `GraphMinor/GM17/Defs.lean` with the remaining definitions of
N. Robertson and P. D. Seymour, *Graph Minors. XVII. Taming a vortex*, J. Combin. Theory
Ser. B 77 (1999) 162–210:

- **Sections 1–2 (Pages 164–166):** Internal and border cells, cells and nodes bordering a cuff,
  cyclic enumerations of nodes and cells around a cuff, $\gamma(X)$ for $X \subseteq N(\Gamma)$,
  unions of cell hypergraphs $\bigcup_{c \in I} \alpha(c)$, and area subhypergraphs
  $\alpha(\Delta)$.
- **Section 4 (Pages 169–170):** Small subhypergraphs and attachments of a subhypergraph $A$ in $G$.
- **Section 5 (Page 171):** Shrinking an internal cell $c$ from a node $n \in \tilde{c}$, and the
  resulting shrunken portrayal.
- **Section 6 (Pages 174–176):** Quotient portrayals on $G / Z$ and terminals of vertices on a cuff.
- **Section 8 (Pages 181–183):** Regions of a painting $\Gamma$ and the non-dominated cell set
  $C^*(\Gamma)$.
- **Section 10 (Page 188):** Cuff orientations (tail and head of a border cell), standard linkages
  in border cells, and the circumnavigation subgraphs $L(v, n_0)$.
- **Section 11 (Pages 189–196):** $\gamma(I)$ for $I \subseteq C(\Gamma)$, the standard linkage
  vertex set $S$, and the crossing cell set $D(A, B)$.
- **Section 12 (Pages 196–200):** Cliques in $G$, tangles induced from a subhypergraph, the
  1-skeleton subhypergraph $A^*$, and the embodiment of a tangle in $G^*$ into $G$.
- **Section 13 (Pages 201–206):** Adding an isolated vertex $H + v$, the complexity invariant
  $h_p(\pi)$, and standards $\sigma(\Sigma, p, z)$.
- **Section 14 (Pages 207–209):** The induced tangle $\mathcal{T}^*$ in the 1-skeleton $G^*$.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v w

/-! ## 1. Paintings, Cells, Cuffs, and Areas (Sections 1–2, Pages 164–166) -/

open Classical in
/-- A subset $F \subseteq \Sigma$ is *$\Gamma$-normal* if $F \cap U(\Gamma) \subseteq N(\Gamma)$.
Graph Minors XVII, Section 1 (page 165). -/
def IsGammaNormal {S : Type} [TopologicalSpace S] (Γ : Painting S) (F : Set S) : Prop :=
  F ∩ Γ.U ⊆ Γ.N

open Classical in
/-- A cell $c \in C(\Gamma)$ is *internal* if $c \cap \operatorname{bd}(\Sigma) = \emptyset$.
Graph Minors XVII, Section 1 (page 165). -/
def Painting.IsInternalCell {S : Type} [TopologicalSpace S] (Γ : Painting S) (c : Set S) : Prop :=
  c ∈ Γ.C ∧ ¬ (c ∩ bd S).Nonempty

open Classical in
/-- A cell $c \in C(\Gamma)$ is a *border cell* if $c \cap \operatorname{bd}(\Sigma) \ne \emptyset$.
Graph Minors XVII, Section 1 (page 165). -/
def Painting.IsBorderCell {S : Type} [TopologicalSpace S] (Γ : Painting S) (c : Set S) : Prop :=
  c ∈ Γ.C ∧ (c ∩ bd S).Nonempty

open Classical in
/-- A cell $c \in C(\Gamma)$ *borders* a cuff $\Theta$ of $\Sigma$ if $\Theta$ is a cuff and
$c \cap \Theta \ne \emptyset$.
Graph Minors XVII, Section 1 (page 165). -/
def Painting.CellBordersCuff {S : Type} [TopologicalSpace S]
    (Γ : Painting S) (c Θ : Set S) : Prop :=
  c ∈ Γ.C ∧ Θ ∈ cuffs S ∧ (c ∩ Θ).Nonempty

open Classical in
/-- A node $n \in N(\Gamma)$ *borders* a cuff $\Theta$ of $\Sigma$ if $\Theta$ is a cuff and
$n \in \Theta$.
Graph Minors XVII, Section 1 (page 165). -/
def Painting.NodeBordersCuff {S : Type} [TopologicalSpace S]
    (Γ : Painting S) (n : S) (Θ : Set S) : Prop :=
  n ∈ Γ.N ∧ Θ ∈ cuffs S ∧ n ∈ Θ

open Classical in
/-- A node $n \in N(\Gamma)$ is a *border node* if $n \in \operatorname{bd}(\Sigma)$.
Graph Minors XVII, Section 1 (page 165). -/
def Painting.IsBorderNode {S : Type} [TopologicalSpace S] (Γ : Painting S) (n : S) : Prop :=
  n ∈ Γ.N ∧ n ∈ bd S

open Classical in
/-- A node $n \in N(\Gamma)$ is an *internal node* if $n \notin \operatorname{bd}(\Sigma)$.
Graph Minors XVII, Section 1 (page 165). -/
def Painting.IsInternalNode {S : Type} [TopologicalSpace S] (Γ : Painting S) (n : S) : Prop :=
  n ∈ Γ.N ∧ n ∉ bd S

open Classical in
/-- An enumeration $n_1, c_1, n_2, c_2, \dots, n_k, c_k, (n_1)$ of the nodes and cells of $\Gamma$
bordering a cuff $\Theta$ of $\Sigma$ in cyclic order around $\Theta$.
Graph Minors XVII, Section 2 (pages 165–166), Section 4 (page 170), and Section 10 (page 188). -/
structure Painting.CuffEnumeration {S : Type} [TopologicalSpace S]
    (Γ : Painting S) (Θ : Set S) (k : ℕ) where
  /-- $\Theta$ is a cuff of $\Sigma$. -/
  cuff_mem : Θ ∈ cuffs S
  /-- A cuff with border cells has at least two nodes on it. -/
  two_le : 2 ≤ k
  /-- The $k$ nodes bordering $\Theta$ in cyclic order. -/
  node : Fin k → S
  /-- The $k$ cells bordering $\Theta$ in cyclic order. -/
  cell : Fin k → Set S
  /-- The nodes are pairwise distinct. -/
  injective_node : Function.Injective node
  /-- The cells are pairwise distinct. -/
  injective_cell : Function.Injective cell
  /-- `node` enumerates all of $N(\Gamma) \cap \Theta$. -/
  range_node : Set.range node = Γ.N ∩ Θ
  /-- `cell` enumerates all cells of $\Gamma$ bordering $\Theta$. -/
  range_cell : Set.range cell = {c ∈ Γ.C | (c ∩ Θ).Nonempty}
  /-- For each $i$, the ends of `cell i` are `node i` and `node ((i + 1) mod k)`. -/
  cell_tilde : ∀ i : Fin k,
    tilde (cell i) = {node i, node ⟨(i.1 + 1) % k, Nat.mod_lt _ (by omega)⟩}
  /-- Any four indices $i_1 < i_2 < i_3 < i_4$ have their nodes in circular order on $\Theta$. -/
  nodes_in_order : ∀ i₁ i₂ i₃ i₄ : Fin k, i₁ < i₂ → i₂ < i₃ → i₃ < i₄ →
    GM19.InOrderOn Θ (node i₁) (node i₂) (node i₃) (node i₄)

open Classical in
/-- The next index in `Fin k` in cyclic order: $(i + 1) \bmod k$. -/
def cyclicSucc {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.1 + 1) % k, Nat.mod_lt _ hk⟩

open Classical in
/-- The previous index in `Fin k` in cyclic order: $(i + k - 1) \bmod k$. -/
def cyclicPred {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.1 + k - 1) % k, Nat.mod_lt _ hk⟩

open Classical in
/-- For any $X \subseteq N(\Gamma)$ (or $X \subseteq \Sigma$), $\gamma(X)$ denotes
$\{\gamma(n) : n \in X \cap \operatorname{dom}(\gamma)\}$.
Graph Minors XVII, Section 2 (page 165). -/
def Portrayal.gammaImage {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (X : Set π.S) : Set α :=
  π.nodeVertex '' (X ∩ π.domγ)

open Classical in
/-- The union $\bigcup (\alpha(c) : c \in I)$ of the cell subhypergraphs over a subset
$I \subseteq C(\Gamma)$.
Graph Minors XVII, Section 2, (2.1) (page 166). -/
def Portrayal.cellsUnion {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (I : Set (Set π.S)) : Hypergraph α β where
  vertexSet := ⋃ c ∈ I ∩ π.Γ.C, (π.cellGraph c).vertexSet
  edgeSet := ⋃ c ∈ I ∩ π.Γ.C, (π.cellGraph c).edgeSet
  Inc e v := (∃ c ∈ I ∩ π.Γ.C, e ∈ (π.cellGraph c).edgeSet) ∧ G.Inc e v
  vertex_mem_of_inc := by
    rintro e v ⟨⟨c, hc, hec⟩, hinc⟩
    have hle := π.cellGraph_le c hc.2
    have hinc_c : (π.cellGraph c).Inc e v := by
      have hends := hle.ends_eq e hec
      change v ∈ G.ends e at hinc
      rw [hends] at hinc
      exact hinc
    exact mem_iUnion₂.mpr ⟨c, hc, (π.cellGraph c).vertex_mem_of_inc hinc_c⟩
  edge_mem_of_inc := by
    rintro e v ⟨⟨c, hc, hec⟩, _⟩
    exact mem_iUnion₂.mpr ⟨c, hc, hec⟩
  vertexSet_finite := G.vertexSet_finite.subset
    (iUnion₂_subset fun c hc => (π.cellGraph_le c hc.2).vertexSet_subset)
  edgeSet_finite := G.edgeSet_finite.subset
    (iUnion₂_subset fun c hc => (π.cellGraph_le c hc.2).edgeSet_subset)

open Classical in
/-- The subhypergraph $\alpha(-c_0) = \bigcup (\alpha(c) : c \in C(\Gamma) \setminus \{c_0\})$
associated with the complement of a single cell $c_0$.
Graph Minors XVII, Section 2 (page 165). -/
def Portrayal.otherCellsGraph {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (c₀ : Set π.S) : Hypergraph α β :=
  π.cellsUnion (π.Γ.C \ {c₀})

open Classical in
/-- For a subset $\Delta \subseteq \Sigma$, the subhypergraph
$\alpha(\Delta) = \bigcup (\alpha(c) : c \in C(\Gamma), c \subseteq \Delta)$.
Graph Minors XVII, Section 5 (page 171): "if $\Sigma' \subseteq \Sigma$ we denote $\bigcup(\alpha(c)
\colon c \in C(\Gamma), c
\subseteq \Sigma')$ by $\alpha(\Sigma')$." -/
def Portrayal.areaGraph {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Δ : Set π.S) : Hypergraph α β :=
  π.cellsUnion {c ∈ π.Γ.C | c ⊆ Δ}

/-! ## 2. Small Subhypergraphs and Attachments (Section 4, Pages 169–170) -/

open Classical in
/-- A subhypergraph $A \subseteq G$ is *small* relative to $\mathcal{T}$ if $(A, B) \in \mathcal{T}$
for some $B \subseteq G$.
Graph Minors XVII, Section 4 (page 169). -/
def IsSmallWrt {α : Type u} {β : Type v}
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (A : Hypergraph α β) : Prop :=
  ∃ B, (A, B) ∈ 𝒯

open Classical in
/-- A vertex $v \in V(A)$ is an *attachment* of a subhypergraph $A \subseteq G$ in $G$ if $v$ is
incident in $G$ with some edge $e \in E(G) \setminus E(A)$.
Graph Minors XVII, Section 4 (page 169): "If $A$ is a subhypergraph of $G$, an *attachment* of $A$
in $G$ is a vertex of $A$ incident with an edge of $G$ not in $E(A)$." -/
def IsAttachment {α : Type u} {β : Type v} (G A : Hypergraph α β) (v : α) : Prop :=
  v ∈ A.vertexSet ∧ ∃ e ∈ G.edgeSet \ A.edgeSet, G.Inc e v

open Classical in
/-- The set of all attachments of a subhypergraph $A$ in $G$.
Graph Minors XVII, Section 4 (page 169). -/
def attachments {α : Type u} {β : Type v} (G A : Hypergraph α β) : Set α :=
  {v ∈ A.vertexSet | ∃ e ∈ G.edgeSet \ A.edgeSet, G.Inc e v}

open Classical in
/-- The complementary subhypergraph of $A \le G$ in $G$, with vertex set
$(V(G) \setminus V(A)) \cup \text{attachments}(G, A)$ and edge set $E(G) \setminus E(A)$, so that
$(A, \text{complSubhypergraph } G\, A)$ is a separation of $G$ whose intersection vertex set is
$\text{attachments}(G, A)$.
Graph Minors XVII, Section 4 (page 169). -/
def complSubhypergraph {α : Type u} {β : Type v} (G A : Hypergraph α β) : Hypergraph α β where
  vertexSet := (G.vertexSet \ A.vertexSet) ∪ attachments G A
  edgeSet := G.edgeSet \ A.edgeSet
  Inc e v := e ∈ G.edgeSet \ A.edgeSet ∧ G.Inc e v
  vertex_mem_of_inc := by
    rintro e v ⟨he, hinc⟩
    by_cases hv : v ∈ A.vertexSet
    · exact Or.inr ⟨hv, e, he, hinc⟩
    · exact Or.inl ⟨G.vertex_mem_of_inc hinc, hv⟩
  edge_mem_of_inc := fun _ _ h => h.1
  vertexSet_finite := (G.vertexSet_finite.subset sdiff_subset).union
    (A.vertexSet_finite.subset fun _ h => h.1)
  edgeSet_finite := G.edgeSet_finite.subset sdiff_subset

/-! ## 3. Shrinking a Cell from a Node (Section 5, Page 171) -/

open Classical in
/-- A painting $\Gamma'$ in $\Sigma$ is obtained from $\Gamma$ by *shrinking* an internal cell
$c \in C(\Gamma)$ from a node $n \in \tilde{c}$ using a closed disc $\Delta \subseteq \bar{c}$ if
$n \notin \Delta$, $\tilde{c} \setminus \{n\} \subseteq \Delta$,
$U(\Gamma') = (U(\Gamma) \setminus c) \cup \Delta$, $N(\Gamma') = N(\Gamma)$, and
$C(\Gamma') = (C(\Gamma) \setminus \{c\}) \cup \{\Delta \setminus (\tilde{c} \setminus \{n\})\}$.
Graph Minors XVII, Section 5 (page 171). -/
def Painting.IsShrunkenFrom {S : Type} [TopologicalSpace S]
    (Γ Γ' : Painting S) (c : Set S) (n : S) (Δ : Set S) : Prop :=
  Γ.IsInternalCell c ∧
  n ∈ tilde c ∧
  IsClosedDisc Δ ∧
  Δ ⊆ closure c ∧
  n ∉ Δ ∧
  tilde c \ {n} ⊆ Δ ∧
  Γ'.U = (Γ.U \ c) ∪ Δ ∧
  Γ'.N = Γ.N ∧
  let c' := Δ \ (tilde c \ {n})
  c' ∈ Γ'.C ∧
  ¬ (c' ∩ bd S).Nonempty ∧
  tilde c' = tilde c \ {n} ∧
  Γ'.C = (Γ.C \ {c}) ∪ {c'}

/-! ## 4. Quotient Portrayal and Cuff Terminals (Section 6, Pages 174–176) -/

open Classical in
/-- Given a portrayal $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ of $G$ and a vertex subset
$Z \subseteq V(G)$, the quotient portrayal $\pi' = (\Sigma, \Gamma, \alpha', \beta', \gamma')$ of
$G / Z$ has $\alpha'(c) = \alpha(c) / (Z \cap V(\alpha(c)))$, $\beta'(n) = \beta(n) \setminus Z$,
and $\operatorname{dom}(\gamma') = \{n \in \operatorname{dom}(\gamma) \mid \gamma(n) \notin Z\}$.
Graph Minors XVII, Section 6, (6.2) (page 174). -/
def Portrayal.quotientBy {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Z : Set α) : Portrayal (quotientVertices G Z) where
  S := π.S
  isSurface := π.isSurface
  connected := π.connected
  Γ := π.Γ
  cellGraph c := quotientVertices (π.cellGraph c) (Z ∩ (π.cellGraph c).vertexSet)
  borderSet n := π.borderSet n \ Z
  domγ := {n ∈ π.domγ | π.nodeVertex n ∉ Z}
  nodeVertex := π.nodeVertex
  cellGraph_le c hc := by
    have hle := π.cellGraph_le c hc
    refine ⟨?_, hle.edgeSet_subset, ?_⟩
    · intro v hv
      exact ⟨hle.vertexSet_subset hv.1, fun hz => hv.2 ⟨hz, hv.1⟩⟩
    · intro e he
      ext v
      have hends := hle.ends_eq e he
      have hv_iff : (π.cellGraph c).Inc e v ↔ G.Inc e v := by
        change v ∈ (π.cellGraph c).ends e ↔ v ∈ G.ends e
        rw [hends]
      exact ⟨fun ⟨hinc, hv⟩ => ⟨hv_iff.mpr hinc, fun ⟨hz, _⟩ => hv hz⟩,
        fun ⟨hinc, hv⟩ => ⟨hv_iff.mp hinc, fun hz => hv ⟨hz, (π.cellGraph c).vertex_mem_of_inc
          hinc⟩⟩⟩
  borderSet_subset n hn v hv := ⟨π.borderSet_subset n hn hv.1, hv.2⟩
  domγ_subset _ hn := π.domγ_subset hn.1
  nodeVertex_mem n hn := ⟨π.nodeVertex_mem n hn.1, hn.2⟩
  nodeVertex_injOn := π.nodeVertex_injOn.mono fun _ hn => hn.1
  p1_vertex v hv := by
    rcases π.p1_vertex v hv.1 with ⟨c, hc, hvc⟩
    exact ⟨c, hc, hvc, fun ⟨hz, _⟩ => hv.2 hz⟩
  p1_edge := π.p1_edge
  p1_disjoint := π.p1_disjoint
  p2 c hc n hn := ⟨π.p2 c hc n ⟨hn.1, hn.2.1⟩, fun ⟨hz, _⟩ => hn.2.2 hz⟩
  p3_notMem n hn hmem := π.p3_notMem n ⟨hn.1.1, hn.2⟩ hmem.1
  p3_subset c hc hbd n hnt v hv :=
    ⟨π.p3_subset c hc hbd n hnt hv.1, fun ⟨hz, _⟩ => hv.2 hz⟩
  p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne n₁ hn₁ n₂ hn₂ :=
    (π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne n₁ hn₁ n₂ hn₂).mono sdiff_subset sdiff_subset
  p4_notMem Θ hΘ n₁ hn₁ n₂ hn₂ hnot hmem :=
    π.p4_notMem Θ hΘ n₁ hn₁ n₂ hn₂.1 hnot hmem.1
  p5 c hc hbd v hv hex := by
    rcases hex with ⟨c', hc', hne, hvc'⟩
    rcases π.p5 c hc hbd v hv.1 ⟨c', hc', hne, hvc'.1⟩ with ⟨n, ⟨hnt, hnd⟩, rfl⟩
    exact ⟨n, ⟨hnt, hnd, fun hz => hv.2 ⟨hz, hv.1⟩⟩, rfl⟩
  p6 c hc hbd v hv hex := by
    rcases hex with ⟨c', hc', hne, hvc'⟩
    rcases π.p6 c hc hbd v hv.1 ⟨c', hc', hne, hvc'.1⟩ with ⟨n, hnt, hmem | ⟨hnd, rfl⟩⟩
    · exact ⟨n, hnt, Or.inl ⟨hmem, fun hz => hv.2 ⟨hz, hv.1⟩⟩⟩
    · exact ⟨n, hnt, Or.inr ⟨⟨hnd, fun hz => hv.2 ⟨hz, hv.1⟩⟩, rfl⟩⟩
  p7 Θ hΘ n₁ hn₁ n₂ hn₂ n₃ hn₃ n₄ hn₄ hord v hv₁ hv₃ := by
    have hv₁' : v ∈ π.borderSet n₁ ∨ (n₁ ∈ π.domγ ∧ v = π.nodeVertex n₁) := by
      rcases hv₁ with ⟨h, _⟩ | ⟨⟨h, _⟩, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, rfl⟩
    have hv₃' : v ∈ π.borderSet n₃ ∨ (n₃ ∈ π.domγ ∧ v = π.nodeVertex n₃) := by
      rcases hv₃ with ⟨h, _⟩ | ⟨⟨h, _⟩, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, rfl⟩
    have hvZ : v ∉ Z := by
      rcases hv₁ with ⟨_, hz⟩ | ⟨⟨_, hz⟩, rfl⟩ <;> exact hz
    rcases π.p7 Θ hΘ n₁ hn₁ n₂ hn₂ n₃ hn₃ n₄ hn₄ hord v hv₁' hv₃' with
      (h2 | ⟨h2, rfl⟩) | (h4 | ⟨h4, rfl⟩)
    · exact Or.inl (Or.inl ⟨h2, hvZ⟩)
    · exact Or.inl (Or.inr ⟨⟨h2, hvZ⟩, rfl⟩)
    · exact Or.inr (Or.inl ⟨h4, hvZ⟩)
    · exact Or.inr (Or.inr ⟨⟨h4, hvZ⟩, rfl⟩)

open Classical in
/-- In a cyclic enumeration $E$ of the nodes and cells around a cuff $\Theta$, the index $i$ is a
*terminal* of a vertex $x \in V(G)$ if $x \in \beta(n_i +)$ and $x \notin \beta(n_{i+1} +)$.
Graph Minors XVII, Section 6, proof of (6.6) (page 176). -/
def Portrayal.IsTerminalIndex {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k)
    (x : α) (i : Fin k) : Prop :=
  x ∈ π.borderPlus (E.node i) ∧
  x ∉ π.borderPlus (E.node (cyclicSucc (by have := E.two_le; omega) i))

/-! ## 5. Regions of $\Gamma$ and $C^*(\Gamma)$ (Section 8, Pages 181–183) -/

open Classical in
/-- A *region* of a painting $\Gamma$ in $\Sigma$ is an arc-wise connected component of
$\Sigma \setminus U(\Gamma)$.
Graph Minors XVII, Section 1 (page 165) and Section 8, (8.1)–(8.2) (page 181). -/
def Painting.regions {S : Type} [TopologicalSpace S] (Γ : Painting S) : Set (Set S) :=
  arcComponentsIn (Set.univ \ Γ.U)

open Classical in
/-- For a painting $\Gamma$, $C^*(\Gamma)$ is the set of all cells $c \in C(\Gamma)$ such that
there is no $c' \in C(\Gamma)$ with $c' \ne c$ and $\tilde{c} \subseteq \tilde{c}'$.
Graph Minors XVII, Section 8 (page 182): "We define $C^*(\Gamma)$ to be the set of all
$c \in C(\Gamma)$ such that there is no $c' \in C(\Gamma)$ with $c' \ne c$ and
$\tilde{c} \subseteq \tilde{c}'$." -/
def Painting.CStar {S : Type} [TopologicalSpace S] (Γ : Painting S) : Set (Set S) :=
  {c ∈ Γ.C | ¬ ∃ c' ∈ Γ.C, c' ≠ c ∧ tilde c ⊆ tilde c'}

/-! ## 6. Standard Linkages and Circumnavigating a Vortex (Section 10, Page 188) -/

open Classical in
/-- A family of $q$ paths `L : Fin q → PathFromTo (π.cellGraph c).skeleton (π.borderSet n₁)
(π.borderSet n₂)`
is a *standard linkage* in $\alpha(c)$ for a border cell $c$ with tail $n_1$ and head $n_2$
(where $q = \text{warpAt}(\Theta)$) if:
1. The paths are pairwise vertex-disjoint and avoid $\gamma(n_1)$ and $\gamma(n_2)$; and
2. Either there is a path $L_0$ from $\gamma(n_1)$ to $\gamma(n_2)$ disjoint from all $L_i$, or
   there is an internal cell $c' \in C(\Gamma)$ with $|\tilde{c}'| = 3$ and $\tilde{c} \subseteq
   \tilde{c}'$.
Graph Minors XVII, Section 10 (page 188) and (9.8) (page 188). -/
def Portrayal.IsStandardLinkage {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (c : Set π.S) (n₁ n₂ : π.S) (q : ℕ)
    (L : Fin q → PathFromTo (π.cellGraph c).skeleton (π.borderSet n₁) (π.borderSet n₂)) : Prop :=
  (Pairwise fun i j => Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support}) ∧
  (∀ i, π.nodeVertex n₁ ∉ (L i).walk.support ∧ π.nodeVertex n₂ ∉ (L i).walk.support) ∧
  ((∃ L₀ : PathFromTo (π.cellGraph c).skeleton {π.nodeVertex n₁} {π.nodeVertex n₂},
      ∀ i, Disjoint {z | z ∈ L₀.walk.support} {z | z ∈ (L i).walk.support}) ∨
    ∃ c' ∈ π.Γ.C, ¬ (c' ∩ bd π.S).Nonempty ∧ (tilde c').ncard = 3 ∧ tilde c ⊆ tilde c')

open Classical in
/-- A choice of standard linkages around a cuff $\Theta$ with cyclic enumeration $E$.
Graph Minors XVII, Section 10 (page 188). -/
structure CuffStandardLinkages {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Θ : Set π.S) (k q : ℕ) (E : π.Γ.CuffEnumeration Θ k) where
  /-- The $q$ paths of the standard linkage in $\alpha(c_i)$ from $\beta(n_i)$ to $\beta(n_{i+1})$.
  -/
  L : ∀ i : Fin k,
    Fin q → PathFromTo (π.cellGraph (E.cell i)).skeleton
      (π.borderSet (E.node i))
      (π.borderSet (E.node (cyclicSucc (by have := E.two_le; omega) i)))
  /-- Each `L i` is a standard linkage in $\alpha(c_i)$. -/
  isStandard : ∀ i : Fin k,
    π.IsStandardLinkage (E.cell i) (E.node i)
      (E.node (cyclicSucc (by have := E.two_le; omega) i)) q (L i)

open Classical in
/-- Given `SL : CuffStandardLinkages π Θ k q E`, a starting index $i_0 \in \text{Fin } k$, and a
vertex $v \in \beta(n_{i_0})$, the sequence of vertices $v_0, v_1, \dots, v_k$ obtained by
following the standard linkages around $\Theta$ starting at $v_0 = v$.
Graph Minors XVII, Section 10 (page 188). -/
noncomputable def CuffStandardLinkages.traceVertex {α : Type u} {β : Type v} {G : Hypergraph α β}
    {π : Portrayal G} {Θ : Set π.S} {k q : ℕ} {E : π.Γ.CuffEnumeration Θ k}
    (SL : CuffStandardLinkages π Θ k q E) (i₀ : Fin k) (v : α) : ℕ → α
  | 0 => v
  | m + 1 =>
    let idx : Fin k := ⟨(i₀.1 + m) % k, Nat.mod_lt _ (by have := E.two_le; omega)⟩
    let cur := SL.traceVertex i₀ v m
    if h : ∃ j : Fin q, (SL.L idx j).first = cur then
      (SL.L idx (Classical.choose h)).last
    else cur

open Classical in
/-- The vertex set $V(L(v, n_{i_0}))$ of the circumnavigation subgraph $L(v, n_{i_0}) = P_1 \cup
\dots \cup P_k$
around $\Theta$ starting at $v \in \beta(n_{i_0})$.
Graph Minors XVII, Section 10 (page 188). -/
noncomputable def CuffStandardLinkages.circumnavigationVertices {α : Type u} {β : Type v}
    {G : Hypergraph α β} {π : Portrayal G} {Θ : Set π.S} {k q : ℕ}
    {E : π.Γ.CuffEnumeration Θ k}
    (SL : CuffStandardLinkages π Θ k q E) (i₀ : Fin k) (v : α) : Set α :=
  ⋃ m ∈ Finset.range k,
    let idx : Fin k := ⟨(i₀.1 + m) % k, Nat.mod_lt _ (by have := E.two_le; omega)⟩
    let cur := SL.traceVertex i₀ v m
    if h : ∃ j : Fin q, (SL.L idx j).first = cur then
      {z | z ∈ (SL.L idx (Classical.choose h)).walk.support}
    else {cur}

/-! ## 7. Surface Separations, $\gamma(I)$, $S$, and $D(A, B)$ (Section 11, Pages 189–196) -/

open Classical in
/-- For a subset of cells $I \subseteq C(\Gamma)$, the set of nodes
$\bigcup (\tilde{c} : c \in I) \subseteq N(\Gamma)$.
Graph Minors XVII, Section 11 (page 189). -/
def Painting.tildeOfCells {S : Type} [TopologicalSpace S]
    (_Γ : Painting S) (I : Set (Set S)) : Set S :=
  ⋃ c ∈ I, tilde c

open Classical in
/-- For a subset of cells $I \subseteq C(\Gamma)$, the vertex set
$\gamma(I) = \bigcup (\gamma(\tilde{c}) : c \in I) \subseteq V(G)$.
Graph Minors XVII, Section 11 (page 189): "For $I \subseteq C(\Gamma)$ we define $\gamma(I) =
\bigcup (\gamma(\tilde{c}) \colon c \in
I)$." -/
def Portrayal.gammaOfCells {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (I : Set (Set π.S)) : Set α :=
  ⋃ c ∈ I, π.gammaImage (tilde c)

open Classical in
/-- For a separation $(A, B)$ of $G$, $D(A, B)$ is the set of cells $c \in C^*(\Gamma)$ such that
$\gamma(\tilde{c}) \not\subseteq V(A)$ and $\gamma(\tilde{c}) \not\subseteq V(B)$.
Graph Minors XVII, Section 11 (page 193):
"D(A, B) = \{c \in C^*(\Gamma) : \gamma(\tilde{c}) \nsubseteq V(A) \text{ and }
\gamma(\tilde{c}) \nsubseteq V(B)\}." -/
def Portrayal.crossingCells {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (A B : Hypergraph α β) : Set (Set π.S) :=
  {c ∈ π.Γ.CStar | ¬ (π.gammaImage (tilde c) ⊆ A.vertexSet) ∧
    ¬ (π.gammaImage (tilde c) ⊆ B.vertexSet)}

/-! ## 8. Cliques, Induced Tangles, and Embodiment (Section 12, Pages 196–200) -/

open Classical in
/-- A *clique* in a hypergraph $G$ is a subset $K \subseteq V(G)$ whose members are pairwise
adjacent in the 1-skeleton $G^*$.
Graph Minors XVII, Section 12 (page 196): "A *clique* in a hypergraph $G$ is (for our purposes)
a subset of $V(G)$ the members of which are mutually adjacent in $G^*$." -/
def IsClique {α : Type u} {β : Type v} (G : Hypergraph α β) (K : Set α) : Prop :=
  K ⊆ G.vertexSet ∧ ∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.skeleton.Adj u v

open Classical in
/-- Given a subhypergraph $G' \le G$ and a tangle $\mathcal{T}'$ in $G'$ of order $\theta$,
the *tangle induced by $\mathcal{T}'$* in $G$ is the set of all separations $(A, B)$ of $G$ of
order $< \theta$ such that $(A \cap G', B \cap G') \in \mathcal{T}'$.
Graph Minors XVII, Section 12 (page 199). -/
def inducedSubhypergraphTangle {α : Type u} {β : Type v}
    (G G' : Hypergraph α β) (𝒯' : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧
    (p.1 ∩ G', p.2 ∩ G') ∈ 𝒯'}

open Classical in
/-- The 1-skeleton $A^*$ of a hypergraph $A$, viewed as a `Hypergraph α (Sym2 α)` with vertex set
$V(A)$ and edge set consisting of the edges of the simple graph `A.skeleton` (that is, pairs
$s(u, v)$ of distinct vertices of $A$ incident with a common edge of $A$).
Graph Minors XVII, Section 3 (page 168) and Section 12, (12.5) (page 200). -/
def oneSkeletonHypergraph {α : Type u} {β : Type v}
    (A : Hypergraph α β) : Hypergraph α (Sym2 α) where
  vertexSet := A.vertexSet
  edgeSet := A.skeleton.edgeSet
  Inc e v := e ∈ A.skeleton.edgeSet ∧ v ∈ e
  vertex_mem_of_inc := by
    rintro e v ⟨he, hv⟩
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      rcases he with ⟨_, e₀, hx, hy⟩
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact A.vertex_mem_of_inc hx
      · exact A.vertex_mem_of_inc hy
  edge_mem_of_inc := fun _ _ h => h.1
  vertexSet_finite := A.vertexSet_finite
  edgeSet_finite := by
    have hsub : A.skeleton.edgeSet ⊆
        (fun p : α × α => s(p.1, p.2)) '' (A.vertexSet ×ˢ A.vertexSet) := by
      intro e he
      induction e using Sym2.ind with
      | _ x y =>
        rw [SimpleGraph.mem_edgeSet] at he
        rcases he with ⟨_, e₀, hx, hy⟩
        exact ⟨(x, y), ⟨A.vertex_mem_of_inc hx, A.vertex_mem_of_inc hy⟩, rfl⟩
    exact ((A.vertexSet_finite.prod A.vertexSet_finite).image _).subset hsub

open Classical in
/-- Given a tangle $\mathcal{T}^*$ of order $\theta$ in the 1-skeleton $G^*$ of a hypergraph $G$,
the *embodiment of $\mathcal{T}^*$ in $G$* is the set of all separations $(A, B)$ of $G$ of order
$< \theta$ such that $A^*$ is small relative to $\mathcal{T}^*$.
Graph Minors XVII, Section 12, (12.5) (page 200). -/
def embodimentTangle {α : Type u} {β : Type v}
    (G : Hypergraph α β)
    (𝒯_star : Set (Hypergraph α (Sym2 α) × Hypergraph α (Sym2 α))) (θ : ℕ) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧
    IsSmallWrt 𝒯_star (oneSkeletonHypergraph p.1)}

/-! ## 9. Adding a Vertex, Complexity $h_p(\pi)$, and Standards (Section 13, Pages 203–206) -/

open Classical in
/-- For a subhypergraph $H \subseteq G$ and a vertex $v \in V(G)$, $H + v$ is the subhypergraph
$(V(H) \cup \{v\}, E(H))$ with the same edges and incidences as $H$.
Graph Minors XVII, Section 13, proof of (13.1) (page 203): "by $H + v$ we mean the hypergraph
$(V(H) \cup \{v\}, E(H))$." -/
def addVertex {α : Type u} {β : Type v} (H : Hypergraph α β) (v : α) : Hypergraph α β where
  vertexSet := H.vertexSet ∪ {v}
  edgeSet := H.edgeSet
  Inc := H.Inc
  vertex_mem_of_inc := fun _ _ h => Or.inl (H.vertex_mem_of_inc h)
  edge_mem_of_inc := H.edge_mem_of_inc
  vertexSet_finite := H.vertexSet_finite.union (finite_singleton v)
  edgeSet_finite := H.edgeSet_finite

open Classical in
/-- The sum $r = \sum_{\Theta} \text{warpAt}(\pi, \Theta)$ of the warps of $\pi$ over all cuffs
$\Theta$ of $\Sigma$.
Graph Minors XVII, Section 13 (page 205). -/
noncomputable def Portrayal.totalCuffWarp {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) : ℕ :=
  if h : (cuffs π.S).Finite then
    ∑ Θ ∈ h.toFinset, π.warpAt Θ
  else 0

open Classical in
/-- Given surface classification parameters $(a, b, c)$ such that $\Sigma \cong \Sigma(a, b, c)$,
the complexity $h_p(\pi) = (4a + 2b + c)^2 p + r$, where $r$ is the sum over all cuffs $\Theta$
of $\Sigma$ of the warp of $\pi$ at $\Theta$.
Graph Minors XVII, Section 13 (page 205). -/
noncomputable def Portrayal.hpWithParams {α : Type u} {β : Type v} {G : Hypergraph α β}
    (p : ℕ) (π : Portrayal G) (a b c : ℕ) : ℕ :=
  (4 * a + 2 * b + c) ^ 2 * p + π.totalCuffWarp

open Classical in
/-- The complexity $h_p(\pi) = (4a + 2b + c)^2 p + r$ of a portrayal $\pi = (\Sigma, \Gamma, \alpha,
\beta, \gamma)$,
where $4a + 2b + c$ is the minimum over all $(a, b, c)$ with $\Sigma \cong \Sigma(a, b, c)$ (which
is
unique by the classification of compact connected surfaces).
Graph Minors XVII, Section 13 (page 205). -/
noncomputable def Portrayal.hp {α : Type u} {β : Type v} {G : Hypergraph α β}
    (p : ℕ) (π : Portrayal G) : ℕ :=
  let g := sInf {k : ℕ | ∃ a b c : ℕ, Nonempty (π.S ≃ₜ SurfaceModel a b c) ∧ 4 * a + 2 * b + c = k}
  g ^ 2 * p + π.totalCuffWarp

open Classical in
/-- A function $\sigma$ assigning a natural number $\sigma(\Sigma, p, z)$ to each connected
surface $\Sigma$ and integers $p \ge 1$ and $z \ge 0$ is a *standard* if
$\sigma(\Sigma, p, z) = \sigma(\Sigma', p, z)$ whenever $\Sigma$ and $\Sigma'$ are homeomorphic.
Graph Minors XVII, Section 13 (page 205). -/
def IsStandard (σ : (S : Type) → [TopologicalSpace S] → ℕ → ℕ → ℕ) : Prop :=
  ∀ (S S' : Type) [TopologicalSpace S] [TopologicalSpace S'] (p z : ℕ),
    IsSurface S → ConnectedSpace S → IsSurface S' → ConnectedSpace S' →
    Nonempty (S ≃ₜ S') → σ S p z = σ S' p z

/-! ## 10. Tangle in the 1-Skeleton (Section 14, Pages 207–209) -/

open Classical in
/-- Given a tangle $\mathcal{T}$ in a hypergraph $G$ and $\theta^* \ge 1$, $\mathcal{T}^*$ is the
set of all separations $(A', B')$ of the 1-skeleton $G^*$ of order $< \theta^*$ such that there
exists $(A, B) \in \mathcal{T}$ with $V(A) = V(A')$ and $V(B) = V(B')$.
Graph Minors XVII, Section 14, (14.1) (page 207). -/
def oneSkeletonTangle {α : Type u} {β : Type v}
    (G : Hypergraph α β) (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (θ_star : ℕ) :
    Set (Hypergraph α (Sym2 α) × Hypergraph α (Sym2 α)) :=
  {p | (oneSkeletonHypergraph G).IsSeparation p.1 p.2 ∧
    separationOrder p.1 p.2 < θ_star ∧
    ∃ q ∈ 𝒯, q.1.vertexSet = p.1.vertexSet ∧ q.2.vertexSet = p.2.vertexSet}

end GraphMinor.GM17
