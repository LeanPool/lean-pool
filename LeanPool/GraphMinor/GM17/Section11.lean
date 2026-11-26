/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section10
import LeanPool.GraphMinor.GM17.PasteCuff
import LeanPool.GraphMinor.GM17.ArcDisc
import LeanPool.GraphMinor.GM17.MarkCross
import LeanPool.GraphMinor.GM17.ReplaceDisc
import LeanPool.GraphMinor.GM17.RegionDisc
import LeanPool.GraphMinor.GM17.CutArcPaint
import LeanPool.GraphMinor.GM17.PushNode

/-!
# Graph Minors XVII, Section 11: Surface Separations in a True Portrayal

This file formalizes Section 11 (pages 189–196) of N. Robertson and P. D. Seymour,
*Graph Minors. XVII. Taming a vortex*, J. Combin. Theory Ser. B 77 (1999), 162–210:
- **Graph Minors XVII, (11.1)** (`theorem_11_1`, pages 189–191): for any partition $I, J$ of
  $C(\Gamma)$ with $\gamma(I), \gamma(J) \ne \gamma(N(\Gamma))$ and
  $|\gamma(I) \cap \gamma(J)| \le 3$, $|\gamma(I) \cap \gamma(J)| = 3$ and there is a disc
  $\Delta \subseteq \Sigma$ whose cells are $I$ or $J$, with $\alpha(\Delta)$ small and bounded by
  a $\Gamma$-normal $O$-arc or a $\Gamma$-normal $I$-arc and $\operatorname{bd}(\Sigma)$.
- **Graph Minors XVII, (11.2)** (`theorem_11_2`, pages 191–192): characterization of separations
  $(A, B) \in \mathcal{T}$ of order $< \operatorname{ord}(\mathcal{T}) - 4p - 3$ with
  $\alpha(c_0) \subseteq A$, $\gamma(I) \subseteq V(A)$, $\gamma(J) \subseteq V(B)$, and
  $|\{n \in N(\Gamma) : \gamma(n) \in V(A \cap B)\}| \le |\tilde{c}_0|$.
- **Graph Minors XVII, (11.3)** (`theorem_11_3`, pages 192–193): for a $\Gamma$-normal $I$-arc $F$
  with $F \cap N(\Gamma) = \{n_1, n_2, n_3\}$ and ends $n_1, n_2$, if $\Delta$ contains a cell $c_0$
  with $|\tilde{c}_0| = 3$, either $\tilde{c}_0 = \Delta \cap N(\Gamma)$ or no separation $(A_1,
  A_2)$
  of $\alpha(\Delta)$ has $V(A_1 \cap A_2) = \{\gamma(n_1), \gamma(n_2)\}$, $\gamma(n_3) \in
  V(A_1)$,
  and $\beta(n_1) \cup \beta(n_2) \subseteq V(A_2)$.
- **Graph Minors XVII, (11.4)** (`theorem_11_4`, pages 193–194): for any separation $(A, B)$ of $G$
  and $d \in D(A, B)$, $V(A \cap B) \cap (V(\alpha(d)) \setminus (S \cup V(\alpha(-d)))) \ne
  \emptyset$.
- **Graph Minors XVII, (11.5)** (`theorem_11_5`, page 194):
  $|D(A, B)| \le |V(A \cap B) \setminus (S \cup \gamma(N(\Gamma)))|$.
- **Graph Minors XVII, (11.6)** (`theorem_11_6`, pages 194–195):
  $|V(A \cap B) \setminus S| \le |\tilde{c}_0|$, and equality implies
  $|V(A \cap B) \cap S| = |V(\alpha(c_0) \cap \alpha(-c_0)) \cap S|$.
- **Graph Minors XVII, (11.7)** (`theorem_11_7`, pages 195–196):
  $|V(A \cap B)| = |V(\alpha(c_0) \cap \alpha(-c_0))|$.
The portrayal deductions that use painting results are proved in `Section11Proved`.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Function Topology Metric
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Basic Lemmas on `tildeOfCells` and `gammaOfCells` -/

theorem Painting.tildeOfCells_subset_N {S : Type} [TopologicalSpace S]
    (Γ : Painting S) {I : Set (Set S)} (hI : I ⊆ Γ.C) :
    Γ.tildeOfCells I ⊆ Γ.N := by
  intro n hn
  unfold Painting.tildeOfCells at hn
  rw [mem_iUnion₂] at hn
  rcases hn with ⟨c, hcI, hnc⟩
  exact Γ.tilde_subset_N (hI hcI) hnc

theorem Painting.tildeOfCells_finite {S : Type} [TopologicalSpace S]
    (Γ : Painting S) {I : Set (Set S)} (hI : I ⊆ Γ.C) :
    (Γ.tildeOfCells I).Finite :=
  Γ.finite_N.subset (Γ.tildeOfCells_subset_N hI)

theorem Painting.tildeOfCells_mono {S : Type} [TopologicalSpace S]
    (Γ : Painting S) {I₁ I₂ : Set (Set S)} (h : I₁ ⊆ I₂) :
    Γ.tildeOfCells I₁ ⊆ Γ.tildeOfCells I₂ :=
  biUnion_mono h fun _ _ => Subset.rfl

theorem Painting.tildeOfCells_union {S : Type} [TopologicalSpace S]
    (Γ : Painting S) (I J : Set (Set S)) :
    Γ.tildeOfCells (I ∪ J) = Γ.tildeOfCells I ∪ Γ.tildeOfCells J := by
  unfold Painting.tildeOfCells
  exact biUnion_union _ _ _

theorem Painting.tildeOfCells_eq_N {S : Type} [TopologicalSpace S]
    (Γ : Painting S) (hnode : ∀ n ∈ Γ.N, ∃ c ∈ Γ.C, n ∈ tilde c) :
    Γ.tildeOfCells Γ.C = Γ.N := by
  refine Subset.antisymm (Γ.tildeOfCells_subset_N Subset.rfl) fun n hn => ?_
  obtain ⟨c, hc, hnc⟩ := hnode n hn
  exact mem_biUnion hc hnc

theorem Portrayal.gammaImage_eq_image_of_subset_N {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (hdom : π.domγ = π.Γ.N) {X : Set π.S} (hX : X ⊆ π.Γ.N) :
    π.gammaImage X = π.nodeVertex '' X := by
  unfold Portrayal.gammaImage
  rw [hdom, inter_eq_self_of_subset_left hX]

theorem Portrayal.gammaOfCells_eq_gammaImage_tildeOfCells {α : Type u} {β : Type v}
    {G : Hypergraph α β} (π : Portrayal G) (I : Set (Set π.S)) :
    π.gammaOfCells I = π.gammaImage (π.Γ.tildeOfCells I) := by
  ext v
  simp only [Portrayal.gammaOfCells, Portrayal.gammaImage, Painting.tildeOfCells,
    mem_iUnion, mem_image, mem_inter_iff]
  constructor
  · rintro ⟨c, hcI, n, ⟨hnc, hndom⟩, rfl⟩
    exact ⟨n, ⟨⟨c, hcI, hnc⟩, hndom⟩, rfl⟩
  · rintro ⟨n, ⟨⟨c, hcI, hnc⟩, hndom⟩, rfl⟩
    exact ⟨c, hcI, n, ⟨hnc, hndom⟩, rfl⟩

theorem Portrayal.gammaOfCells_eq_image_tildeOfCells {α : Type u} {β : Type v}
    {G : Hypergraph α β} (π : Portrayal G) (hdom : π.domγ = π.Γ.N)
    {I : Set (Set π.S)} (hI : I ⊆ π.Γ.C) :
    π.gammaOfCells I = π.nodeVertex '' (π.Γ.tildeOfCells I) := by
  rw [π.gammaOfCells_eq_gammaImage_tildeOfCells,
    π.gammaImage_eq_image_of_subset_N hdom (π.Γ.tildeOfCells_subset_N hI)]

theorem Portrayal.gammaOfCells_inter_eq_image {α : Type u} {β : Type v}
    {G : Hypergraph α β} (π : Portrayal G) (hdom : π.domγ = π.Γ.N)
    {I J : Set (Set π.S)} (hI : I ⊆ π.Γ.C) (hJ : J ⊆ π.Γ.C) :
    π.gammaOfCells I ∩ π.gammaOfCells J =
      π.nodeVertex '' (π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J) := by
  rw [π.gammaOfCells_eq_image_tildeOfCells hdom hI,
    π.gammaOfCells_eq_image_tildeOfCells hdom hJ]
  have hinj : InjOn π.nodeVertex π.Γ.N := hdom ▸ π.nodeVertex_injOn
  exact (hinj.image_inter (π.Γ.tildeOfCells_subset_N hI) (π.Γ.tildeOfCells_subset_N hJ)).symm

theorem Portrayal.ncard_gammaOfCells_inter {α : Type u} {β : Type v}
    {G : Hypergraph α β} (π : Portrayal G) (hdom : π.domγ = π.Γ.N)
    {I J : Set (Set π.S)} (hI : I ⊆ π.Γ.C) (hJ : J ⊆ π.Γ.C) :
    (π.gammaOfCells I ∩ π.gammaOfCells J).ncard =
      (π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J).ncard := by
  rw [π.gammaOfCells_inter_eq_image hdom hI hJ]
  have hinj : InjOn π.nodeVertex (π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J) :=
    (hdom ▸ π.nodeVertex_injOn).mono (inter_subset_left.trans (π.Γ.tildeOfCells_subset_N hI))
  exact hinj.ncard_image

/-! ## 2. Cell Partitions and Surface Separations: (11.1) and (11.2) (Pages 189–192) -/

/-- Pure surface-and-painting topological property for **Graph Minors XVII, (11.1)**
(pages 189–191, Claims (1)–(4)):
Given a painting $\Gamma$ in a connected surface $S$ satisfying the region and 2-node arc
properties of (8.1)–(8.5), for any partition $I, J$ of $C(\Gamma)$ with
$\tilde{I}, \tilde{J} \ne N(\Gamma)$ and $|\tilde{I} \cap \tilde{J}| \le 3$, we have
$|\tilde{I} \cap \tilde{J}| = 3$ and there is either:
(1) a $\Gamma$-normal $O$-arc $F \subseteq S$ with $N(\Gamma) \cap F = \tilde{I} \cap \tilde{J}$
    such that for every closed disc $\Delta \subseteq S$ with $\operatorname{bd}(\Delta) = F$,
    $\{c \in C(\Gamma) : c \subseteq \Delta\}$ is one of $I, J$; or
(2) a $\Gamma$-normal $I$-arc $F \subseteq S$ with $N(\Gamma) \cap F = \tilde{I} \cap \tilde{J}$
    such that for every closed disc $\Delta \subseteq S$ with
    $F \subseteq \operatorname{bd}(\Delta) \subseteq F \cup \operatorname{bd}(S)$,
    $\{c \in C(\Gamma) : c \subseteq \Delta\}$ is one of $I, J$. -/
def CellPartitionPaintingStatement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S],
    IsSurface S → ∀ (Γ : Painting S),
      (∀ R ∈ Γ.regions, IsOpenDisc R ∧ IsOArc (closure R \ R)) →
      (∀ c ∈ Γ.C, 2 ≤ (tilde c).ncard) →
      (∀ n ∈ Γ.N, ∃ c ∈ Γ.C, n ∈ tilde c) →
      (∀ F : Set S, IsLine F → Γ.IsNormal F → F ∩ bd S = lineEnds F →
        (F ∩ Γ.N).ncard = 2 →
        ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S ∧
          Δ ∩ Γ.N ⊆ F ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard = 1) →
      (∀ F : Set S, IsOArc F → Γ.IsNormal F → (F ∩ Γ.N).ncard = 2 →
        ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧
          Δ ∩ Γ.N ⊆ F ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard ≤ 1) →
      ∀ I J : Set (Set S),
        I ∪ J = Γ.C → Disjoint I J →
        Γ.tildeOfCells I ≠ Γ.N → Γ.tildeOfCells J ≠ Γ.N →
        (Γ.tildeOfCells I ∩ Γ.tildeOfCells J).ncard ≤ 3 →
        (Γ.tildeOfCells I ∩ Γ.tildeOfCells J).ncard = 3 ∧
        ((∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
            Γ.N ∩ F = Γ.tildeOfCells I ∩ Γ.tildeOfCells J ∧
            ∀ Δ : Set S, IsClosedDisc Δ → discBd Δ = F →
              {c ∈ Γ.C | c ⊆ Δ} = I ∨ {c ∈ Γ.C | c ⊆ Δ} = J) ∨
         (∃ F : Set S, ∃ n₁ n₂ : S, IsLineWithEnds F n₁ n₂ ∧ Γ.IsNormal F ∧
            F ∩ bd S = {n₁, n₂} ∧
            Γ.N ∩ F = Γ.tildeOfCells I ∩ Γ.tildeOfCells J ∧
            ∀ Δ : Set S, IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S →
              {c ∈ Γ.C | c ⊆ Δ} = I ∨ {c ∈ Γ.C | c ⊆ Δ} = J))

/-- Pure surface-and-painting topological property for **Graph Minors XVII, (11.3)**
(page 193):
Given a painting $\Gamma$ on a surface $S$, a $\Gamma$-normal $I$-arc $F$ with ends
$n_1, n_2 \in \operatorname{bd}(S)$ and $F \cap \Gamma.N = \{n_1, n_2, n_3\}$ of cardinality $3$,
and a closed disc $\Delta \subseteq S$ with $F \subseteq \operatorname{bd}(\Delta) \subseteq F \cup
\operatorname{bd}(S)$,
replacing $\Delta$ by two discs $\Delta_1, \Delta_2 \subseteq \Delta$ gives a painting
$\Gamma' = ((U(\Gamma) \setminus \Delta) \cup \Delta_1 \cup \Delta_2, (N(\Gamma) \setminus \Delta)
\cup \{n_1, n_2, n_3\})$
on $S$ with an internal cell $c_1 = \Delta_1 \setminus \{n_1, n_2, n_3\}$ ($\tilde{c}_1 = \{n_1,
n_2, n_3\}$),
a border cell $c_2 = \Delta_2 \setminus \{n_1, n_2\}$ ($\tilde{c}_2 = \{n_1, n_2\}$), and
$C(\Gamma') = \{c_1, c_2\} \cup \{c \in C(\Gamma) \mid c \subseteq S \setminus \Delta\}$. -/
def ThreeNodeIArcReplaceDiscPaintingStatement : Prop :=
  ∀ (S : Type) [TopologicalSpace S], IsSurface S →
    ∀ (Γ : Painting S) (n₁ n₂ n₃ : S) (F Δ : Set S),
      Γ.IsNormal F → IsLineWithEnds F n₁ n₂ →
      F ∩ bd S = {n₁, n₂} → F ∩ Γ.N = {n₁, n₂, n₃} → (F ∩ Γ.N).ncard = 3 →
      IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S →
      ∃ (Γ' : Painting S) (Θ c₁ c₂ : Set S),
        Γ'.N = (Γ.N \ Δ) ∪ {n₁, n₂, n₃} ∧
        Γ'.N ⊆ Γ.N ∧
        Θ ∈ cuffs S ∧
        n₁ ∈ Γ.N ∩ Θ ∧ n₂ ∈ Γ.N ∩ Θ ∧
        discBd Δ ⊆ F ∪ Θ ∧
        (∀ c ∈ Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ) ∧
        (∀ c ∈ Γ.C, c ⊆ Δᶜ → tilde c ⊆ Γ'.N) ∧
        c₁ ∈ Γ'.C ∧ ¬ (c₁ ∩ bd S).Nonempty ∧ tilde c₁ = {n₁, n₂, n₃} ∧
        c₂ ∈ Γ'.C ∧ (c₂ ∩ Θ).Nonempty ∧ tilde c₂ = {n₁, n₂} ∧
        c₁ ≠ c₂ ∧
        c₁ ∉ {c ∈ Γ.C | c ⊆ Δᶜ} ∧
        c₂ ∉ {c ∈ Γ.C | c ⊆ Δᶜ} ∧
        Γ'.C = insert c₁ (insert c₂ {c ∈ Γ.C | c ⊆ Δᶜ})

/-- A choice of cuff enumerations and standard linkages across all cuffs $\Theta \in
\text{cuffs}(\Sigma)$
of a portrayal $\pi$. Its vertex union `sys.S` formalizes $S$, "the union, over all border cells
$c$,
of the vertex set of the standard linkage in $\alpha(c)$"
(Graph Minors XVII, Section 11, page 193). -/
structure Portrayal.SystemOfStandardLinkages {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) where
  /-- Cyclic enumeration of each cuff $\Theta$. -/
  E : ∀ Θ ∈ cuffs π.S, π.Γ.CuffEnumeration Θ (π.Γ.N ∩ Θ).ncard
  /-- Standard linkages around each cuff $\Theta$. -/
  SL : ∀ Θ (hΘ : Θ ∈ cuffs π.S),
    CuffStandardLinkages π Θ (π.Γ.N ∩ Θ).ncard (π.warpAt Θ) (E Θ hΘ)

namespace Portrayal.SystemOfStandardLinkages

variable {α : Type u} {β : Type v} {G : Hypergraph α β} {π : Portrayal G}

/-- The vertex set of the standard linkage in the $i$-th border cell on cuff $\Theta$. -/
def cellSet (sys : π.SystemOfStandardLinkages) (Θ : Set π.S) (hΘ : Θ ∈ cuffs π.S)
    (i : Fin (π.Γ.N ∩ Θ).ncard) : Set α :=
  ⋃ j : Fin (π.warpAt Θ), {z | z ∈ ((sys.SL Θ hΘ).L i j).walk.support}

/-- The union of the vertex sets of the standard linkages over all border cells on cuff $\Theta$. -/
def cuffSet (sys : π.SystemOfStandardLinkages) (Θ : Set π.S) (hΘ : Θ ∈ cuffs π.S) : Set α :=
  ⋃ i : Fin (π.Γ.N ∩ Θ).ncard, sys.cellSet Θ hΘ i

/-- The union $S$, over all border cells $c$, of the vertex set of the standard linkage in
$\alpha(c)$
(Graph Minors XVII, Section 11, page 193). -/
def S (sys : π.SystemOfStandardLinkages) : Set α :=
  ⋃ (Θ : Set π.S) (hΘ : Θ ∈ cuffs π.S), sys.cuffSet Θ hΘ

theorem cellSet_subset_S (sys : π.SystemOfStandardLinkages) {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S)
    (i : Fin (π.Γ.N ∩ Θ).ncard) :
    sys.cellSet Θ hΘ i ⊆ sys.S :=
  fun _ hz => mem_iUnion₂.mpr ⟨Θ, hΘ, mem_iUnion.mpr ⟨i, hz⟩⟩

theorem cuffSet_subset_S (sys : π.SystemOfStandardLinkages) {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) :
    sys.cuffSet Θ hΘ ⊆ sys.S :=
  fun _ hz => mem_iUnion₂.mpr ⟨Θ, hΘ, hz⟩

end Portrayal.SystemOfStandardLinkages

/-- For any separation $(A, B)$ of $G$, if $x, y$ are adjacent in $G^*$ with $x \notin V(A)$ and
$y \in V(A)$, then $y \in V(A \cap B)$ (and symmetrically if $x \in V(A)$ and $y \notin V(A)$, then
$x \in V(A \cap B)$). -/
theorem mem_inter_of_adj_of_isSeparation {α : Type u} {β : Type v}
    {G A B : Hypergraph α β} (hsep : G.IsSeparation A B) {x y : α}
    (hadj : G.skeleton.Adj x y) (hx : x ∈ A.vertexSet) (hy : y ∉ A.vertexSet) :
    x ∈ (A ∩ B).vertexSet := by
  refine ⟨hx, ?_⟩
  rcases hadj with ⟨_, e, hincx, hincy⟩
  have heG : e ∈ G.edgeSet := G.edge_mem_of_inc hincx
  rw [← hsep.edgeSet_union] at heG
  rcases heG with heA | heB
  · have hyA : y ∈ A.vertexSet :=
      A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le heA).mpr hincy)
    exact (hy hyA).elim
  · exact B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le heB).mpr hincx)

/-- If $W$ is a walk in $G^*$ from $u_1 \notin V(A)$ to $u_2 \in V(A) \setminus V(B)$ where $(A, B)$
is a separation of $G$, then some internal vertex $v \in W.\text{support} \setminus \{u_1, u_2\}$
belongs to $V(A \cap B)$. -/
theorem exists_internal_mem_inter_of_walk_of_isSeparation {α : Type u} {β : Type v}
    {G A B : Hypergraph α β} (hsep : G.IsSeparation A B)
    {u₁ u₂ : α} (W : G.skeleton.Walk u₁ u₂)
    (hu₁ : u₁ ∉ A.vertexSet) (hu₂A : u₂ ∈ A.vertexSet) (hu₂B : u₂ ∉ B.vertexSet) :
    ∃ v ∈ W.support, v ≠ u₁ ∧ v ≠ u₂ ∧ v ∈ (A ∩ B).vertexSet := by
  have hex : ∃ v ∈ W.support, v ∈ (A ∩ B).vertexSet := by
    induction W with
    | nil => exact (hu₁ hu₂A).elim
    | @cons x y z hadj W' ih =>
      by_cases hyA : y ∈ A.vertexSet
      · exact ⟨y, List.mem_cons_of_mem x W'.start_mem_support,
          mem_inter_of_adj_of_isSeparation hsep hadj.symm hyA hu₁⟩
      · obtain ⟨v, hv_sup, hv_inter⟩ := ih hyA hu₂A hu₂B
        exact ⟨v, List.mem_cons_of_mem x hv_sup, hv_inter⟩
  obtain ⟨v, hv_sup, hv_inter⟩ := hex
  refine ⟨v, hv_sup, ?_, ?_, hv_inter⟩
  · rintro rfl; exact hu₁ hv_inter.1
  · rintro rfl; exact hu₂B hv_inter.2

/-- If $W$ is a walk in $G^*$ from $y \notin V(A)$ to $v \in V(A)$ where $(A, B)$ is a separation
of $G$, then some vertex $b \in W.\text{support}.\text{tail}$ belongs to $V(A \cap B)$, and
$v \in W.\text{support}.\text{tail}$. -/
theorem exists_tail_mem_inter_of_walk_of_notMem {α : Type u} {β : Type v}
    {G A B : Hypergraph α β} (hsep : G.IsSeparation A B)
    {y v : α} (W : G.skeleton.Walk y v)
    (hy : y ∉ A.vertexSet) (hv : v ∈ A.vertexSet) :
    (∃ b ∈ W.support.tail, b ∈ (A ∩ B).vertexSet) ∧ v ∈ W.support.tail := by
  have hne_nil : W.support.tail ≠ [] := by
    intro hnil
    exact hy (start_eq_end_of_support_tail_eq_nil W hnil ▸ hv)
  refine ⟨?_, end_mem_support_tail_of_support_tail_ne_nil W hne_nil⟩
  induction W with
  | nil => exact (hy hv).elim
  | @cons x y' z hadj W' ih =>
    rw [SimpleGraph.Walk.support_cons, List.tail_cons, ← W'.cons_tail_support]
    by_cases hy' : y' ∈ A.vertexSet
    · exact ⟨y', List.mem_cons_self,
        mem_inter_of_adj_of_isSeparation hsep hadj.symm hy' hy⟩
    · obtain ⟨b, hb_tail, hb_AB⟩ := ih hy' hv
        (fun hnil => hy' (start_eq_end_of_support_tail_eq_nil W' hnil ▸ hv))
      exact ⟨b, List.mem_cons_of_mem y' hb_tail, hb_AB⟩

/-- If $W$ is a walk in $G^*$ from $u \in V(A)$ to $v \in V(A)$ where $(A, B)$ is a separation of
$G$, and $W.\text{support}.\text{tail}$ contains a vertex outside $V(A)$, then
$W.\text{support}.\text{tail} = L_1 \mathbin{+\!+} m :: L_2$ where every vertex of $L_1$ is in
$V(A)$, $m \notin V(A)$, there is a vertex $a \in V(A \cap B)$ with $(L_1 = [] \land a = u) \lor
a \in L_1$, and there is a vertex $b \in V(A \cap B)$ with $b \in L_2$ and $v \in L_2$. -/
theorem walk_first_last_out_of_isSeparation {α : Type u} {β : Type v}
    {G A B : Hypergraph α β} (hsep : G.IsSeparation A B)
    {u v : α} (W : G.skeleton.Walk u v)
    (hu : u ∈ A.vertexSet) (hv : v ∈ A.vertexSet)
    (hex : ∃ z ∈ W.support.tail, z ∉ A.vertexSet) :
    ∃ (L₁ L₂ : List α) (m a b : α),
      W.support.tail = L₁ ++ m :: L₂ ∧
      (∀ x ∈ L₁, x ∈ A.vertexSet) ∧
      m ∉ A.vertexSet ∧
      a ∈ (A ∩ B).vertexSet ∧ ((L₁ = [] ∧ a = u) ∨ a ∈ L₁) ∧
      b ∈ (A ∩ B).vertexSet ∧ b ∈ L₂ ∧ v ∈ L₂ := by
  induction W with
  | nil =>
    rcases hex with ⟨z, hz, _⟩
    exact (List.not_mem_nil hz).elim
  | @cons x y z hadj W' ih =>
    rw [SimpleGraph.Walk.support_cons, List.tail_cons, ← W'.cons_tail_support] at hex ⊢
    by_cases hy : y ∈ A.vertexSet
    · have hex' : ∃ w ∈ W'.support.tail, w ∉ A.vertexSet := by
        rcases hex with ⟨w, hw, hw_notA⟩
        rcases List.mem_cons.mp hw with rfl | hw_tail
        · exact (hw_notA hy).elim
        · exact ⟨w, hw_tail, hw_notA⟩
      obtain ⟨L₁', L₂, m, a, b, hEq, hL₁', hm, ha_AB, ha_mem, hb_AB, hb_L₂, hv_L₂⟩ :=
        ih hy hv hex'
      refine ⟨y :: L₁', L₂, m, a, b, ?_, ?_, hm, ha_AB, ?_, hb_AB, hb_L₂, hv_L₂⟩
      · rw [List.cons_append, hEq]
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact hy
        · exact hL₁' w hw'
      · refine Or.inr ?_
        rcases ha_mem with ⟨_, rfl⟩ | ha_L₁'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem y ha_L₁'
    · obtain ⟨⟨b, hb_tail, hb_AB⟩, hv_tail⟩ :=
        exists_tail_mem_inter_of_walk_of_notMem hsep W' hy hv
      exact ⟨[], W'.support.tail, y, x, b, rfl,
        fun _ h => (List.not_mem_nil h).elim, hy,
        mem_inter_of_adj_of_isSeparation hsep hadj hu hy,
        Or.inl ⟨rfl, rfl⟩, hb_AB, hb_tail, hv_tail⟩

/-- The tail of the first step walk `(sys.SL Θ hΘ).stepWalk i₀ u` is a prefix of the tail of
`(sys.SL Θ hΘ).circWalk i₀ u k`. -/
theorem Portrayal.SystemOfStandardLinkages.exists_support_tail_circWalk_eq_append
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {π : Portrayal G} (sys : π.SystemOfStandardLinkages)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (i₀ : Fin (π.Γ.N ∩ Θ).ncard) (u : α) :
    ∃ rest : List α,
      ((sys.SL Θ hΘ).circWalk i₀ u (π.Γ.N ∩ Θ).ncard).support.tail =
        ((sys.SL Θ hΘ).stepWalk i₀ u).support.tail ++ rest := by
  have hind : ∀ m : ℕ, 1 ≤ m →
      ∃ rest : List α,
        ((sys.SL Θ hΘ).circWalk i₀ u m).support.tail =
          ((sys.SL Θ hΘ).stepWalk i₀ u).support.tail ++ rest := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases m with _ | m
      · refine ⟨[], ?_⟩
        rw [CuffStandardLinkages.support_tail_circWalk_succ, List.append_nil]
        change [] ++ ((sys.SL Θ hΘ).stepWalk (stepIdx (sys.E Θ hΘ).two_le i₀ 0) u).support.tail = _
        rw [List.nil_append, stepIdx_zero]
      · obtain ⟨rest, hrest⟩ := ih (by omega)
        rw [CuffStandardLinkages.support_tail_circWalk_succ, hrest, List.append_assoc]
        exact ⟨_, rfl⟩
  exact hind (π.Γ.N ∩ Θ).ncard (by have := (sys.E Θ hΘ).two_le; omega)

end GraphMinor.GM17
