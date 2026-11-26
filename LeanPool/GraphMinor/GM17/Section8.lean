/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section7
public import LeanPool.GraphMinor.GM20.Cited

import LeanPool.GraphMinor.Surface.Cuffs

/-!
# Graph Minors XVII, Section 8: The Painting of a True Portrayal

This file formalizes Section 8 (pages 181–183) of Robertson and Seymour, *Graph Minors. XVII.
Taming a Vortex*, J. Combin. Theory Ser. B 77 (1999), 162–210:

- **(8.1)** (`theorem_8_1`, page 181): Every region of $\Gamma$ is an open disc.
- **(8.2)** (`theorem_8_2`, pages 181–182): The boundary of every region is an $O$-arc, and in
  particular $|\tilde{c}| \ge 2$ for every cell $c \in C(\Gamma)$.
- **(8.3)** (`theorem_8_3` and `gm17_theorem_8_3`, page 182): For every $\Gamma$-normal $I$-arc
  $F$ with $|F \cap N(\Gamma)| = 2$, there is a disc $\Delta \subseteq \Sigma$ with
  $F \subseteq \operatorname{bd}(\Delta) \subseteq F \cup \operatorname{bd}(\Sigma)$ such that
  $\Delta \cap N(\Gamma) \subseteq F$ and $\Delta$ includes exactly one cell of $\Gamma$.
- **(8.4)** (`theorem_8_4`, page 182): $\operatorname{dom}(\gamma) = N(\Gamma)$.
- **(8.5)** (`theorem_8_5` and `gm17_theorem_8_5`, page 182): For every $\Gamma$-normal $O$-arc
  $F \subseteq \Sigma$ with $|F \cap N(\Gamma)| \le 3$, there is a disc $\Delta \subseteq \Sigma$
  with $F = \operatorname{bd}(\Delta)$ such that $\alpha(\Delta)$ is small, and either
  (i) $\Delta \cap N(\Gamma) \subseteq F$ and $\Delta$ includes at most one cell of $\Gamma$, or
  (ii) $|F \cap N(\Gamma)| = 3$ and $|\tilde{c}| = 2$ for every cell $c \subseteq \Delta$.
- **(8.6)** (`theorem_8_6`, page 182): If $c$ is an internal cell, then
  $|\bar{c} \cap \operatorname{bd}(\Sigma)| \le 2$, and if equality holds then $|\tilde{c}| = 3$
  and the two members of $\bar{c} \cap \operatorname{bd}(\Sigma)$ are consecutive on a cuff.
- **(8.7)** (`theorem_8_7`, pages 182–183): For every node $n \in N(\Gamma)$ there are at least
  two cells $c \in C^*(\Gamma)$ with $n \in \tilde{c}$, and if there are only two and
  $|\tilde{c}| = 2$ for one of them, then $c$ is a border cell.
- **(8.8)** (`theorem_8_8`, page 183): If $c_1, c_2 \in C(\Gamma)$ are distinct cells with
  $\tilde{c}_1 \subseteq \tilde{c}_2$, then $c_1$ is a border cell and $|\tilde{c}_2| = 3$.
The portrayal deductions that use painting results are proved in `Section8Proved`.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Preliminary Lemmas for True Portrayals -/

/-- If $z_1 \le z_2$ and $\pi$ is $z_2$-redundant, then $\pi$ is $z_1$-redundant. -/
theorem Portrayal.IsRedundant.mono {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ z₁ z₂ : ℕ} {π : Portrayal G}
    (hred : π.IsRedundant 𝒯 θ z₂) (hle : z₁ ≤ z₂) :
    π.IsRedundant 𝒯 θ z₁ :=
  ⟨ lt_of_le_of_lt hle hred.1,
    fun Z hZ hZ_le => hred.2 Z hZ (hZ_le.trans hle) ⟩

/-- In a $\mathcal{T}$-central portrayal $\pi$ of $G$, if $\Delta \subseteq \Sigma$ is a
$\Gamma$-normal closed disc such that $\alpha(\Delta)$ is small relative to $\mathcal{T}$, then
there exists a cell $c' \in C(\Gamma)$ with $c' \subseteq \Sigma \setminus \Delta$, chosen so that
$\tilde{c}' \cap \operatorname{discBd} \Delta \ne \emptyset$ whenever such a cell exists. -/
theorem Portrayal.exists_cell_outside_disc_of_small {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    {Δ : Set π.S} (hΔ : IsClosedDisc Δ) (hnorm : discBd Δ ∩ π.Γ.U ⊆ π.Γ.N)
    (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ)) :
    ∃ c' ∈ π.Γ.C, c' ⊆ Set.univ \ Δ ∧
      ((∃ c ∈ π.Γ.C, c ⊆ Set.univ \ Δ ∧ (tilde c ∩ discBd Δ).Nonempty) →
        (tilde c' ∩ discBd Δ).Nonempty) := by
  classical
  obtain ⟨hdich, _, _⟩ := normal_disc_cell_dichotomy π.isSurface π.Γ hΔ hnorm
  have hex_out : ∃ c₀ ∈ π.Γ.C, c₀ ⊆ Set.univ \ Δ := by
    by_contra hall
    push Not at hall
    have hV_ne : (π.areaGraph Δ).vertexSet ≠ G.vertexSet := hsmall.vertexSet_ne h𝒯
    apply hV_ne
    refine Subset.antisymm (π.cellsUnion_le _).vertexSet_subset ?_
    intro v hv
    obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv
    have hc_in : c ⊆ Δ := by
      rcases hdich c hc with h | h
      · exact h.trans sdiff_subset
      · exact False.elim (hall c hc h)
    exact mem_iUnion₂.mpr ⟨c, ⟨⟨hc, hc_in⟩, hc⟩, hvc⟩
  by_cases htouch : ∃ c ∈ π.Γ.C, c ⊆ Set.univ \ Δ ∧ (tilde c ∩ discBd Δ).Nonempty
  · obtain ⟨c', hc', hc'_out, hc'_touch⟩ := htouch
    exact ⟨c', hc', hc'_out, fun _ => hc'_touch⟩
  · obtain ⟨c₀, hc₀, hc₀_out⟩ := hex_out
    exact ⟨c₀, hc₀, hc₀_out, fun h => False.elim (htouch h)⟩

/-- By (4.3) (`theorem_4_3_proof`), in any $\mathcal{T}$-central portrayal $\pi$ of warp $\le p$,
the
number of nodes in $\operatorname{dom}(\gamma)$ (and hence in $N(\Gamma)$) is at least
$\theta - 2p$. In particular, when $\theta > 4p + 5$, we have $|\operatorname{dom}(\gamma)| \ge 6$
and $|N(\Gamma)| \ge 6$. -/
theorem Portrayal.sub_two_mul_warp_le_ncard_domγ {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
     (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G) (hcentral : π.IsCentral 𝒯) (hwarp : π.warp ≤ p) :
    θ - 2 * p ≤ π.domγ.ncard ∧ θ - 2 * p ≤ π.Γ.N.ncard := by
  have hfin_dom : π.domγ.Finite := π.Γ.finite_N.subset π.domγ_subset
  have hle_N : π.domγ.ncard ≤ π.Γ.N.ncard := ncard_le_ncard π.domγ_subset π.Γ.finite_N
  have hge : θ - 2 * p ≤ π.domγ.ncard := by
    by_contra hlt
    have hlt' : π.domγ.ncard < θ - 2 * p := lt_of_not_ge hlt
    let W : Set α := π.nodeVertex '' π.domγ
    have hW_sub : W ⊆ G.vertexSet := by
      rintro _ ⟨n, hn, rfl⟩
      exact π.nodeVertex_mem n hn
    have hW_fin : W.Finite := hfin_dom.image π.nodeVertex
    have hW_le : W.ncard ≤ π.domγ.ncard := ncard_image_le hfin_dom
    have hW_lt_θ : W.ncard < θ := by omega
    let A : Hypergraph α β := discreteSubhypergraph G W hW_sub
    have hA_small : IsSmallWrt 𝒯 A := ⟨G, IsTangle.discrete_mem h𝒯 hW_sub hW_lt_θ⟩
    have hatt_sub : attachments G A ⊆ W := fun _ hv => hv.1
    have hatt_lt : (attachments G A).ncard < θ - 2 * p :=
      (ncard_le_ncard hatt_sub hW_fin).trans_lt (hW_le.trans_lt hlt')
    exact theorem_4_3_proof h𝒯 π hcentral hwarp
      ⟨A, hA_small, hatt_lt, fun n hn => ⟨n, hn, rfl⟩⟩
  exact ⟨hge, hge.trans hle_N⟩

/-! ## 2. Every Region is an Open Disc with $O$-Arc Boundary: (8.1) and (8.2) (Pages 181–182) -/

/-- Topological statement for Graph Minors XVII, (8.1) (page 181):
In a connected surface $S$ with a painting $\Gamma$ having $\Gamma.U \ne \emptyset$, if every
$O$-arc $F \subseteq S$ disjoint from $\Gamma.U$ bounds a closed disc $\Delta \subseteq S$ with
$\operatorname{discBd} \Delta = F$ and $\Delta \cap \Gamma.U = \emptyset$, then every region
$r \in \Gamma.\text{regions}$ is an open disc. -/
@[expose] def RegionOpenDiscCriterionStatement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S], IsSurface S →
    ∀ (Γ : Painting S),
      Γ.U.Nonempty →
      (∀ F : Set S, IsOArc F → Disjoint F Γ.U →
        ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ Disjoint Δ Γ.U) →
      ∀ r ∈ Γ.regions, IsOpenDisc r

/-- Topological statement for Graph Minors XVII, (8.2) (pages 181–182), and the normal-arc pushoff
constructions along region boundaries used in (8.4), (8.6), (8.7), and (8.8) (pages 182–183):
In a connected surface $S$ with a painting $\Gamma$ having $|\Gamma.N| \ge 6$ whose regions are
open discs, if every $\Gamma$-normal $O$-arc $F \subseteq S$ with $|F \cap \Gamma.N| \le 1$ bounds
a closed disc $\Delta \subseteq S$ with $\operatorname{discBd} \Delta = F$ and
$\Delta \cap \Gamma.U \subseteq F$, then:
1. The boundary $\overline{r} \setminus r$ of every region $r \in \Gamma.\text{regions}$ is an
  $O$-arc;
2. Every cell $c \in \Gamma.C$ has $2 \le |\tilde{c}|$;
3. Every node $n \in \Gamma.N$ belongs to $\tilde{c}$ for some cell $c \in \Gamma.C$;
4. If a border node $n \in \Gamma.N \cap \operatorname{bd} S$ does not belong to $\tilde{c}$ for any
   internal cell $c \in \Gamma.C$, pushing off the two incident border cells in the adjacent region
   gives a $\Gamma$-normal $I$-arc $F$ with $|F \cap \Gamma.N| = 2$ that cannot bound a closed disc
   $\Delta$ with $F \subseteq \operatorname{discBd} \Delta \subseteq F \cup \operatorname{bd} S$,
   $\Delta \cap \Gamma.N \subseteq F$, and $\{c \in \Gamma.C \mid c \subseteq \Delta\}.\text{ncard}
   = 1$;
5. For every internal cell $c \in \Gamma.C$, any two distinct nodes $n_1, n_2 \in \bar{c} \cap
  \operatorname{bd} S$
   are joined by a $\Gamma$-normal $I$-arc $F$ with $F \cap \operatorname{bd} S = \{n_1, n_2\}$ and
   $F \cap \Gamma.N = \{n_1, n_2\}$, and if $\tilde{c} \subseteq \operatorname{bd} S$, pushing off
   $c$
   gives a $\Gamma$-normal $I$-arc with $|F \cap \Gamma.N| = 2$ that cannot bound a 1-cell normal
   disc;
6. If two distinct border cells $c_1, c_2 \in \Gamma.C$ have $\tilde{c}_1 = \tilde{c}_2$, pushing
  off
   $c_1$ and $c_2$ into their adjacent regions gives a $\Gamma$-normal $O$-arc $F$ with
   $|F \cap \Gamma.N| = 2$ that bounds no closed disc $\Delta$ with $\Delta \cap \Gamma.N \subseteq
   F$; and
7. If an internal node $n \in \Gamma.N \setminus \operatorname{bd} S$ is incident with at most one
   cell, or with two cells one of which has $|\tilde{c}_0| = 2$, encircling $n$ and its incident
   cells
   in the surrounding region(s) gives a $\Gamma$-normal $O$-arc $F$ with $|F \cap \Gamma.N| \le 3$
   such that any closed disc $\Delta$ bounded by $F$ either fails both alternatives of (8.5) or is
   the
   complementary disc covering $\Gamma.C \setminus \{c \in \Gamma.C \mid n \in \tilde{c}\}$. -/
@[expose] def RegionBoundaryOArcCriterionStatement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S], IsSurface S →
    ∀ (Γ : Painting S),
      6 ≤ Γ.N.ncard →
      (∀ r ∈ Γ.regions, IsOpenDisc r) →
      (∀ F : Set S, IsOArc F → Γ.IsNormal F → (F ∩ Γ.N).ncard ≤ 1 →
        ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F ∧ Δ ∩ Γ.U ⊆ F) →
      (∀ r ∈ Γ.regions, IsOArc (closure r \ r)) ∧
      (∀ c ∈ Γ.C, 2 ≤ (tilde c).ncard) ∧
      (∀ n ∈ Γ.N, ∃ c ∈ Γ.C, n ∈ tilde c) ∧
      (∀ n ∈ Γ.N ∩ bd S, (∀ c ∈ Γ.C, n ∈ tilde c → (c ∩ bd S).Nonempty) →
        ∃ F : Set S, IsLine F ∧ Γ.IsNormal F ∧ F ∩ bd S = lineEnds F ∧ (F ∩ Γ.N).ncard = 2 ∧
          ∀ Δ : Set S, IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S →
            ¬ (Δ ∩ Γ.N ⊆ F ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard = 1)) ∧
      (∀ c ∈ Γ.C, ¬ (c ∩ bd S).Nonempty →
        (∀ n₁ ∈ closure c ∩ bd S, ∀ n₂ ∈ closure c ∩ bd S, n₁ ≠ n₂ →
          ∃ F : Set S, IsLineWithEnds F n₁ n₂ ∧ Γ.IsNormal F ∧ F ∩ bd S = lineEnds F ∧
            F ∩ bd S = {n₁, n₂} ∧ F ∩ Γ.N = {n₁, n₂} ∧
            ∀ Δ : Set S, IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S →
              (Δ ∩ (bd S \ {n₁, n₂})).Nonempty ∧
              ∀ c₀ ∈ Γ.C, (c₀ ∩ Δ).Nonempty → c₀ ⊆ Δ) ∧
        (tilde c ⊆ bd S →
          ∃ F : Set S, IsLine F ∧ Γ.IsNormal F ∧ F ∩ bd S = lineEnds F ∧ (F ∩ Γ.N).ncard = 2 ∧
            ∀ Δ : Set S, IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S →
              ¬ (Δ ∩ Γ.N ⊆ F ∧ {d ∈ Γ.C | d ⊆ Δ}.ncard = 1))) ∧
      (∀ c₁ ∈ Γ.C, ∀ c₂ ∈ Γ.C, c₁ ≠ c₂ →
        (c₁ ∩ bd S).Nonempty → (c₂ ∩ bd S).Nonempty → tilde c₁ = tilde c₂ →
        ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧ (F ∩ Γ.N).ncard = 2 ∧
          ∀ Δ : Set S, IsClosedDisc Δ → discBd Δ = F → ¬ (Δ ∩ Γ.N ⊆ F)) ∧
      (∀ n ∈ Γ.N \ bd S,
        ({c ∈ Γ.C | n ∈ tilde c}.ncard ≤ 1 ∨
          ({c ∈ Γ.C | n ∈ tilde c}.ncard = 2 ∧
            ∃ c₀ ∈ Γ.C, n ∈ tilde c₀ ∧ (tilde c₀).ncard = 2)) →
        ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧ (F ∩ Γ.N).ncard ≤ 3 ∧
          ∀ Δ : Set S, IsClosedDisc Δ → discBd Δ = F →
            ((Δ ∩ Γ.N ⊆ F ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard ≤ 1) ∨
              ((F ∩ Γ.N).ncard = 3 ∧ ∀ c ∈ Γ.C, c ⊆ Δ → (tilde c).ncard = 2)) →
            ∃ d₁ ∈ Γ.C, ∃ d₂ ∈ Γ.C, Γ.C ⊆ {d₁, d₂} ∪ {c ∈ Γ.C | c ⊆ Δ})

/-- For any internal cell $c \in C(\Gamma)$ (`¬ (c ∩ bd S).Nonempty`),
$\bar{c} \cap \operatorname{bd} S = \tilde{c} \cap \operatorname{bd} S$. -/
theorem Painting.closure_cell_inter_bd_eq_tilde_inter_bd {S : Type} [TopologicalSpace S]
    {c : Set S} (hint : ¬ (c ∩ bd S).Nonempty) :
    closure c ∩ bd S = tilde c ∩ bd S := by
  ext x
  simp only [tilde, mem_inter_iff, mem_sdiff]
  exact ⟨fun ⟨hxcl, hxbd⟩ => ⟨⟨hxcl, fun hxc => hint ⟨x, hxc, hxbd⟩⟩, hxbd⟩,
    fun ⟨⟨hxcl, _⟩, hxbd⟩ => ⟨hxcl, hxbd⟩⟩

end GraphMinor.GM17
