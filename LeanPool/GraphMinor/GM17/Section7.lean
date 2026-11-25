/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section6
public import LeanPool.GraphMinor.Surface.DiscsInSurface

import LeanPool.GraphMinor.Surface.Cuffs

/-!
# Graph Minors XVII, Section 7: Some Constructions

This file formalizes Section 7 (pages 178–181) of Robertson and Seymour, *Graph Minors. XVII.
Taming a Vortex*, J. Combin. Theory Ser. B 77 (1999), 162–210:

- **Disc-in-surface painting lemmas**: For any closed disc $\Delta \subseteq \Sigma$ in a surface
  $\Sigma$, $\Delta \setminus \operatorname{bd}(\Delta)$ is open in $\Sigma$ and disjoint from
  $\operatorname{bd}(\Sigma)$. If $\operatorname{bd}(\Delta)$ is $\Gamma$-normal, every cell of
  $\Gamma$ lies either in $\Delta \setminus \operatorname{bd}(\Delta)$ or in $\Sigma \setminus
  \Delta$,
  every border cell lies in $\Sigma \setminus \Delta$, and every node in
  $\operatorname{bd}(\Delta) \cap N(\Gamma)$ lies in $\overline{\Sigma \setminus \Delta}$.
- **(7.1)** (`theorem_7_1`, page 178): Removing a disc $\Delta$ with $\operatorname{bd}(\Delta)$
  $\Gamma$-normal, $|\operatorname{bd}(\Delta) \cap N(\Gamma)| \le 1$, and $\alpha(\Delta)$ small,
  and merging $\alpha(\Delta)$ into a cell $c' \subseteq \Sigma \setminus \Delta$ chosen with
  $\tilde{c}' \cap \operatorname{bd}(\Delta) \ne \emptyset$ if possible, yields a
  $\mathcal{T}$-central
  portrayal $\pi'$ of $G$ resembling $\pi$.
- **(7.2)** (`theorem_7_2`, page 178): Replacing the interior of a disc $\Delta$ with
  $\operatorname{bd}(\Delta)$ $\Gamma$-normal, $|\operatorname{bd}(\Delta) \cap N(\Gamma)| \le 3$,
  and $\alpha(\Delta)$ small by a single internal cell $c' = \Delta \setminus
  (\operatorname{bd}(\Delta) \cap N(\Gamma))$
  with $\alpha'(c') = A$ yields a $\mathcal{T}$-central portrayal $\pi'$ of $G$ resembling $\pi$.
- **(7.3)** (`theorem_7_3`, pages 178–180): If $F \subseteq \Sigma$ is a $\Gamma$-normal $I$-arc
  with ends $n_1, n_2 \in \Theta$ and $F \cap N(\Gamma) = \{n_1, n_2\}$, $\Delta \subseteq \Sigma$
  is a disc with $F \subseteq \operatorname{bd}(\Delta) \subseteq F \cup \Theta$,
  $\beta(n_1+) \cap \beta(n_2+) \subseteq \beta(n+)$ for all $n \in N(\Gamma) \cap
  \operatorname{bd}(\Delta)$,
  $\pi$ has warp $\le p$ at $\Theta$, and $|\beta(n_1+)| = |\beta(n_2+)| = p + 1$, then every
  linkage in $\alpha(\Delta)$ from $\beta(n_1+)$ to $\beta(n_2+)$ pairs $\gamma(n_1)$ with
  $\gamma(n_2)$.
- **(7.4)** (`theorem_7_4`, pages 180–181): Replacing the interior of a disc $\Delta$ bounded by a
  $\Gamma$-normal $I$-arc $F$ with $|F \cap N(\Gamma)| = 2$ and $\Theta \cap
  \operatorname{bd}(\Delta)$
  by a single border cell $c' = \Delta \setminus (F \cap N(\Gamma))$ with $\alpha'(c') =
  \alpha(\Delta)$
  yields a $\mathcal{T}$-central portrayal $\pi'$ of $G$ resembling $\pi$.
The portrayal deductions that use painting results are proved in `Section7Proved`.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology Metric
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Discs and Normal Boundaries in Paintings -/

section DiscNormalLemmas

variable {S : Type} [TopologicalSpace S]

/-- In a surface $S$, for any closed disc $\Delta \subseteq S$, the interior
$\Delta \setminus \operatorname{discBd} \Delta$ is open in $S$ and consists of interior points of
$S$ (hence is disjoint from $\operatorname{bd} S$). -/
theorem isOpen_and_disjoint_bd_of_isClosedDisc (hS : IsSurface S) {Δ : Set S}
    (hΔ : IsClosedDisc Δ) :
    IsOpen (Δ \ discBd Δ) ∧ Disjoint (Δ \ discBd Δ) (bd S) ∧
    Δ ∩ bd S ⊆ discBd Δ ∧ Δ \ discBd Δ ⊆ interior Δ ∧ frontier Δ ⊆ discBd Δ := by
  have : T2Space S := hS.2.1
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  obtain ⟨hunion, hdisj⟩ := c.union_ball
  have hdiff_eq : Δ \ discBd Δ = g '' ball 0 1 := by
    ext x
    constructor
    · rintro ⟨hxΔ, hxbd⟩
      rw [← hunion] at hxΔ
      exact hxΔ.resolve_right hxbd
    · intro hx
      exact ⟨hunion ▸ Or.inl hx, Set.disjoint_left.mp hdisj hx⟩
  have hopen_ball : IsOpen (g '' ball 0 1) := c.isOpen_image_ball hS.2.2
  have hopen : IsOpen (Δ \ discBd Δ) := hdiff_eq ▸ hopen_ball
  obtain ⟨e₁, -⟩ := exists_homeomorph_image (c.gc.mono ball_subset_closedBall)
    (c.hc.mono (c.g_subset ball_subset_closedBall)) (c.hg.mono ball_subset_closedBall)
  obtain ⟨e₂⟩ := exists_homeomorph_ball (0 : ℂ) one_pos
  have hdisj_bd : Disjoint (Δ \ discBd Δ) (bd S) := by
    rw [hdiff_eq]
    exact Set.disjoint_left.mpr fun x hx hxbd =>
      hxbd ⟨g '' ball 0 1, hopen_ball, hx, ⟨e₁.symm.trans e₂⟩⟩
  have hbd_sub : Δ ∩ bd S ⊆ discBd Δ := fun x ⟨hxΔ, hxbd⟩ => by
    by_contra hx
    exact Set.disjoint_left.mp hdisj_bd ⟨hxΔ, hx⟩ hxbd
  have hint : Δ \ discBd Δ ⊆ interior Δ := interior_maximal sdiff_subset hopen
  have hcl : closure Δ = Δ := (isClosed_of_isClosedDisc hΔ).closure_eq
  have hfr : frontier Δ ⊆ discBd Δ := by
    intro x ⟨hxcl, hxint⟩
    rw [hcl] at hxcl
    by_contra hx
    exact hxint (hint ⟨hxcl, hx⟩)
  exact ⟨hopen, hdisj_bd, hbd_sub, hint, hfr⟩

/-- In a surface $S$, no point $x \in \operatorname{discBd} \Delta$ with $x \notin \operatorname{bd}
S$
lies in $\operatorname{interior} \Delta$; consequently $x \in \overline{S \setminus \Delta}$. -/
theorem mem_closure_compl_of_mem_discBd_not_bd {Δ : Set S}
    (hΔ : IsClosedDisc Δ) {x : S} (hx : x ∈ discBd Δ) (hxbd : x ∉ bd S) :
    x ∈ closure (Set.univ \ Δ) := by
  have hnot_int : x ∉ interior Δ := by
    intro hxint
    have hx' : IsInteriorPoint x := not_not.mp hxbd
    obtain ⟨W, hW_open, hxW, ⟨f⟩⟩ := hx'
    have : Nonempty S := ⟨x⟩
    obtain ⟨h, g, c⟩ := hΔ.exists_isChart
    obtain ⟨b⟩ := exists_homeomorph_ball (0 : ℂ) one_pos
    obtain ⟨a, a', h1, h2, h3, h4, h5, h6⟩ := exists_functions_of_homeomorph (b.trans f.symm)
    let U := W ∩ interior Δ
    have hU_open : IsOpen U := hW_open.inter isOpen_interior
    have hxU : x ∈ U := ⟨hxW, hxint⟩
    have hD : IsOpen (ball (0 : ℂ) 1 ∩ a ⁻¹' U) := h1.isOpen_inter_preimage isOpen_ball hU_open
    have haΔ : ∀ z ∈ ball (0 : ℂ) 1 ∩ a ⁻¹' U, a z ∈ Δ :=
      fun z hz => interior_subset hz.2.2
    have hG : ContinuousOn (h ∘ a) (ball (0 : ℂ) 1 ∩ a ⁻¹' U) :=
      c.hc.comp (h1.mono inter_subset_left) haΔ
    have hGi : InjOn (h ∘ a) (ball (0 : ℂ) 1 ∩ a ⁻¹' U) := fun z hz w hw he =>
      h5.injOn hz.1 hw.1 (c.gh.injOn (haΔ z hz) (haΔ w hw) he)
    have hopen := isOpen_image_of_injOn hD hG hGi
    have hsub_cb : (h ∘ a) '' (ball (0 : ℂ) 1 ∩ a ⁻¹' U) ⊆ closedBall (0 : ℂ) 1 := by
      rintro _ ⟨z, hz, rfl⟩
      exact c.hm (haΔ z hz)
    have hsub_int : (h ∘ a) '' (ball (0 : ℂ) 1 ∩ a ⁻¹' U) ⊆ interior (closedBall (0 : ℂ) 1) :=
      interior_maximal hsub_cb hopen
    rw [interior_closedBall (0 : ℂ) one_ne_zero] at hsub_int
    have hmem : h x ∈ (h ∘ a) '' (ball (0 : ℂ) 1 ∩ a ⁻¹' U) := by
      refine ⟨a' x, ⟨h4 hxW, ?_⟩, ?_⟩
      · change a (a' x) ∈ U
        rw [h6 hxW]
        exact hxU
      · change h (a (a' x)) = h x
        rw [h6 hxW]
    have hball : h x ∈ ball (0 : ℂ) 1 := hsub_int hmem
    have hsph : h x ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hx
    exact (mem_ball_zero_iff.mp hball).ne (mem_sphere_zero_iff_norm.mp hsph)
  have hcompl : Set.univ \ Δ = Δᶜ := by ext y; simp
  rw [hcompl, closure_compl]
  exact hnot_int

/-- For a painting $\Gamma$ in a surface $S$ and a closed disc $\Delta \subseteq S$ whose boundary
$\operatorname{discBd} \Delta$ is $\Gamma$-normal ($\operatorname{discBd} \Delta \cap \Gamma.U
\subseteq \Gamma.N$):
1. Every cell $c \in \Gamma.C$ satisfies either $c \subseteq \Delta \setminus \operatorname{discBd}
  \Delta$
   or $c \subseteq S \setminus \Delta$.
2. Every border cell $c \in \Gamma.C$ satisfies $c \subseteq S \setminus \Delta$.
3. Every node $x \in \operatorname{discBd} \Delta \cap \Gamma.N$ lies in $\overline{S \setminus
  \Delta}$. -/
theorem normal_disc_cell_dichotomy (hS : IsSurface S) (Γ : Painting S) {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hnorm : discBd Δ ∩ Γ.U ⊆ Γ.N) :
    (∀ c ∈ Γ.C, c ⊆ Δ \ discBd Δ ∨ c ⊆ Set.univ \ Δ) ∧
    (∀ c ∈ Γ.C, (c ∩ bd S).Nonempty → c ⊆ Set.univ \ Δ) ∧
    (discBd Δ ∩ Γ.N ⊆ closure (Set.univ \ Δ)) := by
  have : T2Space S := hS.2.1
  obtain ⟨hopen, _, hbd_sub, hint, hfr⟩ := isOpen_and_disjoint_bd_of_isClosedDisc hS hΔ
  have hcell_disj_bd : ∀ c ∈ Γ.C, Disjoint c (discBd Δ) := by
    intro c hc
    refine Set.disjoint_left.mpr fun x hxc hxbd => ?_
    have hxU : x ∈ Γ.U := Γ.cell_subset_U hc hxc
    have hxN : x ∈ Γ.N := hnorm ⟨hxbd, hxU⟩
    exact (Γ.cell_subset_diff hc hxc).2 hxN
  have h1 : ∀ c ∈ Γ.C, c ⊆ Δ \ discBd Δ ∨ c ⊆ Set.univ \ Δ := by
    intro c hc
    have hdisj := hcell_disj_bd c hc
    by_cases hsub : c ⊆ Set.univ \ Δ
    · exact Or.inr hsub
    · left
      have hne_in : (c ∩ Δ).Nonempty := by
        rw [Set.not_subset] at hsub
        rcases hsub with ⟨x, hxc, hx⟩
        simp only [mem_sdiff, mem_univ, true_and, not_not] at hx
        exact ⟨x, hxc, hx⟩
      have hc_sub_Δ : c ⊆ Δ := by
        by_contra hnot
        rw [Set.not_subset] at hnot
        rcases hnot with ⟨y, hyc, hyΔ⟩
        have hne_out : (c ∩ Δᶜ).Nonempty := ⟨y, hyc, hyΔ⟩
        obtain ⟨z, hzc, hzfr⟩ := inter_frontier_nonempty_of_isPreconnected
          (Γ.cell_isPathConnected hc).isConnected.isPreconnected hne_in hne_out
        exact Set.disjoint_left.mp hdisj hzc (hfr hzfr)
      exact fun x hxc => ⟨hc_sub_Δ hxc, Set.disjoint_left.mp hdisj hxc⟩
  have h2 : ∀ c ∈ Γ.C, (c ∩ bd S).Nonempty → c ⊆ Set.univ \ Δ := by
    intro c hc ⟨x, hxc, hxbd⟩
    rcases h1 c hc with hsub | hsub
    · exfalso
      have hxΔ : x ∈ Δ \ discBd Δ := hsub hxc
      exact hxΔ.2 (hbd_sub ⟨hxΔ.1, hxbd⟩)
    · exact hsub
  have h3 : discBd Δ ∩ Γ.N ⊆ closure (Set.univ \ Δ) := by
    rintro x ⟨hxbdΔ, hxN⟩
    by_cases hxbdS : x ∈ bd S
    · let Θ := connectedComponentIn (bd S) x
      have hΘ : Θ ∈ cuffs S := ⟨x, hxbdS, rfl⟩
      have hΘ_arc : IsOArc Θ := (cuff_statement S hS).2.2 Θ hΘ
      have hxΘ : x ∈ Γ.N ∩ Θ := ⟨hxN, mem_connectedComponentIn hxbdS⟩
      obtain ⟨E⟩ := Γ.exists_cuffEnumeration hΘ hΘ_arc
      have hx_range : x ∈ Set.range E.node := by rw [E.range_node]; exact hxΘ
      rcases hx_range with ⟨i, hi⟩
      have hc_range : E.cell i ∈ {c ∈ Γ.C | (c ∩ Θ).Nonempty} := by
        rw [← E.range_cell]; exact mem_range_self i
      have hbd_cell : (E.cell i ∩ bd S).Nonempty :=
        hc_range.2.mono (inter_subset_inter_right _ (connectedComponentIn_subset _ _))
      have hc_out : E.cell i ⊆ Set.univ \ Δ := h2 (E.cell i) hc_range.1 hbd_cell
      have hx_tilde : x ∈ tilde (E.cell i) := by
        rw [← hi, E.cell_tilde i]
        exact mem_insert _ _
      exact closure_mono hc_out hx_tilde.1
    · exact mem_closure_compl_of_mem_discBd_not_bd hΔ hxbdΔ hxbdS
  exact ⟨h1, h2, h3⟩

/-- If $\operatorname{discBd} \Delta$ is $\Gamma$-normal and $c \in \Gamma.C$ satisfies
$c \subseteq S \setminus \Delta$, then $\bar{c} \subseteq \overline{S \setminus \Delta}$ and
$\bar{c} \cap \Delta = \tilde{c} \cap \operatorname{discBd} \Delta \subseteq \Gamma.N \cap
\overline{S \setminus \Delta}$. -/
theorem closure_cell_inter_disc_of_subset_compl (hS : IsSurface S) (Γ : Painting S) {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hnorm : discBd Δ ∩ Γ.U ⊆ Γ.N) {c : Set S} (hc : c ∈ Γ.C)
    (hsub : c ⊆ Set.univ \ Δ) :
    closure c ⊆ closure (Set.univ \ Δ) ∧
    closure c ∩ Δ = tilde c ∩ discBd Δ := by
  have : T2Space S := hS.2.1
  obtain ⟨hopen, _, _, _, _⟩ := isOpen_and_disjoint_bd_of_isClosedDisc hS hΔ
  refine ⟨closure_mono hsub, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxcl, hxΔ⟩
    have hxbd : x ∈ discBd Δ := by
      by_contra hxnot
      have hx_in : x ∈ Δ \ discBd Δ := ⟨hxΔ, hxnot⟩
      obtain ⟨y, hy_open, hyc⟩ := _root_.mem_closure_iff.mp hxcl (Δ \ discBd Δ) hopen hx_in
      exact (hsub hyc).2 hy_open.1
    have hxU : x ∈ Γ.U := Γ.closure_cell_subset_U hc hxcl
    have hxN : x ∈ Γ.N := hnorm ⟨hxbd, hxU⟩
    rw [← Γ.closure_cell_inter_N hc]
    exact ⟨⟨hxcl, hxN⟩, hxbd⟩
  · rintro x ⟨hxt, hxbd⟩
    exact ⟨hxt.1, discBd_subset Δ hxbd⟩

end DiscNormalLemmas

/-! ## 2. Removing a Disc with $\le 1$ Boundary Node: (7.1) (Page 178) -/

section Theorem71

variable {S : Type} [TopologicalSpace S]

/-- The painting $\Gamma'$ of Graph Minors XVII, (7.1) (page 178):
if there is a cell $c \in \Gamma.C$ with $c \subseteq S \setminus \Delta$ and
$\tilde{c} \cap \operatorname{discBd} \Delta \ne \emptyset$, then
$\Gamma' = (U(\Gamma) \cap \overline{S \setminus \Delta}, N(\Gamma) \cap \overline{S \setminus
\Delta})$;
otherwise $\Gamma' = (U(\Gamma) \setminus \Delta, N(\Gamma) \setminus \Delta)$.
In both cases, $C(\Gamma') = \{c \in C(\Gamma) \mid c \subseteq S \setminus \Delta\}$. -/
noncomputable def Painting.removeDiscWithCells (hS : IsSurface S) (Γ : Painting S) (Δ : Set S)
    (hΔ : IsClosedDisc Δ) (hnorm : discBd Δ ∩ Γ.U ⊆ Γ.N) :
    {Γ' : Painting S // Γ'.C = {c ∈ Γ.C | c ⊆ Set.univ \ Δ}} := by
  classical
  have : T2Space S := hS.2.1
  obtain ⟨hopen, _, hbd_sub, _, _⟩ := isOpen_and_disjoint_bd_of_isClosedDisc hS hΔ
  obtain ⟨hdich, hbd_cells, hN_bd_cl⟩ := normal_disc_cell_dichotomy hS Γ hΔ hnorm
  set I₂ : Set (Set S) := {c ∈ Γ.C | c ⊆ Set.univ \ Δ}
  have hI₂_fin : I₂.Finite := Γ.finite_cells.subset fun _ h => h.1
  let hasTouch : Prop := ∃ c ∈ I₂, (tilde c ∩ discBd Δ).Nonempty
  let U' : Set S :=
    if hasTouch then Γ.U ∩ closure (Set.univ \ Δ) else Γ.U \ Δ
  let N' : Set S :=
    if hasTouch then Γ.N ∩ closure (Set.univ \ Δ) else Γ.N \ Δ
  have hN'_sub_N : N' ⊆ Γ.N := by
    dsimp only [N']
    split_ifs
    · exact inter_subset_left
    · exact sdiff_subset
  have hN'_sub_U' : N' ⊆ U' := by
    dsimp only [N', U']
    split_ifs
    · exact inter_subset_inter_left _ Γ.N_subset
    · exact sdiff_le_sdiff_right Γ.N_subset
  have hN'_fin : N'.Finite := Γ.finite_N.subset hN'_sub_N
  have htilde_sub_N' : ∀ c ∈ I₂, tilde c ⊆ N' := by
    intro c ⟨hc, hc_sub⟩
    have hcl_sub := (closure_cell_inter_disc_of_subset_compl hS Γ hΔ hnorm hc hc_sub).1
    have hcl_inter := (closure_cell_inter_disc_of_subset_compl hS Γ hΔ hnorm hc hc_sub).2
    dsimp only [N']
    split_ifs with ht
    · exact fun x hx => ⟨Γ.tilde_subset_N hc hx, hcl_sub hx.1⟩
    · intro x hx
      refine ⟨Γ.tilde_subset_N hc hx, fun hxΔ => ht ⟨c, ⟨hc, hc_sub⟩, x, ?_⟩⟩
      rw [← hcl_inter]
      exact ⟨hx.1, hxΔ⟩
  have hcl_sub_U' : ∀ c ∈ I₂, closure c ⊆ U' := by
    intro c ⟨hc, hc_sub⟩
    have hcl_sub := (closure_cell_inter_disc_of_subset_compl hS Γ hΔ hnorm hc hc_sub).1
    have hcl_inter := (closure_cell_inter_disc_of_subset_compl hS Γ hΔ hnorm hc hc_sub).2
    dsimp only [U']
    split_ifs with ht
    · exact fun x hx => ⟨Γ.closure_cell_subset_U hc hx, hcl_sub hx⟩
    · intro x hx
      refine ⟨Γ.closure_cell_subset_U hc hx, fun hxΔ => ht ⟨c, ⟨hc, hc_sub⟩, x, ?_⟩⟩
      rw [← hcl_inter]
      exact ⟨hx, hxΔ⟩
  have hU'_eq : U' = N' ∪ ⋃ c ∈ I₂, closure c := by
    refine Subset.antisymm ?_
      (union_subset hN'_sub_U' (iUnion₂_subset fun c hc => hcl_sub_U' c hc))
    intro x hxU'
    have hxU : x ∈ Γ.U := by
      dsimp only [U'] at hxU'
      split_ifs at hxU' <;> exact hxU'.1
    by_cases hxN : x ∈ Γ.N
    · left
      dsimp only [N', U'] at hxU' ⊢
      split_ifs at hxU' ⊢ with ht
      · exact ⟨hxN, hxU'.2⟩
      · exact ⟨hxN, hxU'.2⟩
    · right
      have hx_cells : x ∈ ⋃₀ Γ.C := by
        rw [Γ.sUnion_cells]
        exact ⟨hxU, hxN⟩
      rcases hx_cells with ⟨c, hc, hxc⟩
      rcases hdich c hc with hc_in | hc_out
      · exfalso
        have hx_open : x ∈ Δ \ discBd Δ := hc_in hxc
        dsimp only [U'] at hxU'
        split_ifs at hxU' with ht
        · obtain ⟨y, hy_open, hy_out⟩ :=
            _root_.mem_closure_iff.mp hxU'.2 (Δ \ discBd Δ) hopen hx_open
          exact hy_out.2 hy_open.1
        · exact hxU'.2 hx_open.1
      · exact mem_iUnion₂.mpr ⟨c, ⟨hc, hc_out⟩, subset_closure hxc⟩
  have hU'_closed : IsClosed U' := by
    rw [hU'_eq]
    exact hN'_fin.isClosed.union (hI₂_fin.isClosed_biUnion fun c _ => isClosed_closure)
  have hbd_N_eq : N' ∩ bd S = Γ.N ∩ bd S := by
    refine Subset.antisymm (inter_subset_inter_left _ hN'_sub_N) ?_
    rintro x ⟨hxN, hxbd⟩
    refine ⟨?_, hxbd⟩
    dsimp only [N']
    split_ifs with ht
    · by_cases hxΔ : x ∈ Δ
      · exact ⟨hxN, hN_bd_cl ⟨hbd_sub ⟨hxΔ, hxbd⟩, hxN⟩⟩
      · exact ⟨hxN, subset_closure ⟨trivial, hxΔ⟩⟩
    · refine ⟨hxN, fun hxΔ => ?_⟩
      have hx_bdΔ : x ∈ discBd Δ := hbd_sub ⟨hxΔ, hxbd⟩
      let Θ := connectedComponentIn (bd S) x
      have hΘ : Θ ∈ cuffs S := ⟨x, hxbd, rfl⟩
      have hΘ_arc : IsOArc Θ := (cuff_statement S hS).2.2 Θ hΘ
      obtain ⟨E⟩ := Γ.exists_cuffEnumeration hΘ hΘ_arc
      have hx_range : x ∈ Set.range E.node := by
        rw [E.range_node]; exact ⟨hxN, mem_connectedComponentIn hxbd⟩
      rcases hx_range with ⟨i, hi⟩
      have hc_range : E.cell i ∈ {c ∈ Γ.C | (c ∩ Θ).Nonempty} := by
        rw [← E.range_cell]; exact mem_range_self i
      have hbd_c : (E.cell i ∩ bd S).Nonempty :=
        hc_range.2.mono (inter_subset_inter_right _ (connectedComponentIn_subset _ _))
      have hc_I₂ : E.cell i ∈ I₂ := ⟨hc_range.1, hbd_cells (E.cell i) hc_range.1 hbd_c⟩
      have hx_tilde : x ∈ tilde (E.cell i) := by
        rw [← hi, E.cell_tilde i]
        exact mem_insert _ _
      exact ht ⟨E.cell i, hc_I₂, x, hx_tilde, hx_bdΔ⟩
  have hbd_sub_U' : bd S ⊆ U' := by
    intro x hxbd
    by_cases hxN : x ∈ Γ.N
    · have hxN' : x ∈ N' ∩ bd S := hbd_N_eq.symm ▸ ⟨hxN, hxbd⟩
      exact hN'_sub_U' hxN'.1
    · obtain ⟨c, ⟨hc, hxc⟩, _⟩ := Γ.exists_border_cell_of_mem_bd ⟨hxbd, hxN⟩
      have hc_I₂ : c ∈ I₂ := ⟨hc, hbd_cells c hc ⟨x, hxc, hxbd⟩⟩
      exact hcl_sub_U' c hc_I₂ (subset_closure hxc)
  have hcov : ⋃₀ I₂ = U' \ N' := by
    ext x
    constructor
    · rintro ⟨c, hcI₂, hxc⟩
      refine ⟨hcl_sub_U' c hcI₂ (subset_closure hxc), fun hxN' => ?_⟩
      exact (Γ.cell_subset_diff hcI₂.1 hxc).2 (hN'_sub_N hxN')
    · rintro ⟨hxU', hxN'⟩
      rw [hU'_eq] at hxU'
      rcases hxU' with hxN'2 | hxcl
      · exact False.elim (hxN' hxN'2)
      · rcases mem_iUnion₂.mp hxcl with ⟨c, hcI₂, hxcl_c⟩
        have hxN : x ∉ Γ.N := fun hxN =>
          hxN' (htilde_sub_N' c hcI₂ ((Γ.closure_cell_inter_N hcI₂.1).symm ▸ ⟨hxcl_c, hxN⟩))
        have hxc : x ∈ c := by
          rw [← Γ.closure_cell_diff_N hcI₂.1]
          exact ⟨hxcl_c, hxN⟩
        exact ⟨c, hcI₂, hxc⟩
  have hC_eq : arcComponentsIn (U' \ N') = I₂ := by
    apply arcComponentsIn_eq_of_finite_cover hI₂_fin hcov
    · intro c hcI₂
      exact Γ.cell_nonempty hcI₂.1
    · intro c hcI₂
      exact Γ.cell_isPathConnected hcI₂.1
    · intro c₁ hc₁ c₂ hc₂ hne
      exact Γ.cell_disjoint hc₁.1 hc₂.1 hne
    · intro c hcI₂
      refine Subset.antisymm ?_ (fun x hxc => ⟨subset_closure hxc, hcov ▸ ⟨c, hcI₂, hxc⟩⟩)
      rintro x ⟨hxcl, _, hxN'⟩
      have hxN : x ∉ Γ.N := fun hxN =>
        hxN' (htilde_sub_N' c hcI₂ ((Γ.closure_cell_inter_N hcI₂.1).symm ▸ ⟨hxcl, hxN⟩))
      rw [← Γ.closure_cell_diff_N hcI₂.1]
      exact ⟨hxcl, hxN⟩
  refine ⟨?_, ?_⟩
  · exact
      { U := U'
        N := N'
        isClosed_U := hU'_closed
        bd_subset := hbd_sub_U'
        N_subset := hN'_sub_U'
        finite_N := hN'_fin
        finite_cells := hC_eq ▸ hI₂_fin
        cell_disc := fun c hc => Γ.cell_disc c (hC_eq ▸ hc).1
        border_cell := fun c hc hbd => Γ.border_cell c (hC_eq ▸ hc).1 hbd }
  · exact hC_eq

/-- The painting obtained by removing a disc. -/
noncomputable def Painting.removeDisc (hS : IsSurface S) (Γ : Painting S) (Δ : Set S)
    (hΔ : IsClosedDisc Δ) (hnorm : discBd Δ ∩ Γ.U ⊆ Γ.N) : Painting S :=
  (Γ.removeDiscWithCells hS Δ hΔ hnorm).1

theorem Painting.removeDisc_C (hS : IsSurface S) (Γ : Painting S) (Δ : Set S)
    (hΔ : IsClosedDisc Δ) (hnorm : discBd Δ ∩ Γ.U ⊆ Γ.N) :
    (Γ.removeDisc hS Δ hΔ hnorm).C = {c ∈ Γ.C | c ⊆ Set.univ \ Δ} :=
  (Γ.removeDiscWithCells hS Δ hΔ hnorm).2

theorem Painting.removeDisc_N_subset (hS : IsSurface S) (Γ : Painting S) (Δ : Set S)
    (hΔ : IsClosedDisc Δ) (hnorm : discBd Δ ∩ Γ.U ⊆ Γ.N) :
    (Γ.removeDisc hS Δ hΔ hnorm).N ⊆ Γ.N \ (Δ \ discBd Δ) := by
  classical
  have : T2Space S := hS.2.1
  obtain ⟨hopen, _, _, _, _⟩ := isOpen_and_disjoint_bd_of_isClosedDisc hS hΔ
  intro x hx
  change x ∈ if (∃ c ∈ {c ∈ Γ.C | c ⊆ Set.univ \ Δ}, (tilde c ∩ discBd Δ).Nonempty)
    then Γ.N ∩ closure (Set.univ \ Δ) else Γ.N \ Δ at hx
  split_ifs at hx with ht
  · refine ⟨hx.1, fun hx_open => ?_⟩
    obtain ⟨y, hy_open, hy_out⟩ :=
      _root_.mem_closure_iff.mp hx.2 (Δ \ discBd Δ) hopen hx_open
    exact hy_out.2 hy_open.1
  · exact ⟨hx.1, fun hx_open => hx.2 hx_open.1⟩

theorem Painting.removeDisc_N_inter_bd (hS : IsSurface S) (Γ : Painting S) (Δ : Set S)
    (hΔ : IsClosedDisc Δ) (hnorm : discBd Δ ∩ Γ.U ⊆ Γ.N) :
    (Γ.removeDisc hS Δ hΔ hnorm).N ∩ bd S = Γ.N ∩ bd S := by
  classical
  have : T2Space S := hS.2.1
  obtain ⟨_, _, hbd_sub, _, _⟩ := isOpen_and_disjoint_bd_of_isClosedDisc hS hΔ
  obtain ⟨_, hbd_cells, hN_bd_cl⟩ := normal_disc_cell_dichotomy hS Γ hΔ hnorm
  set I₂ : Set (Set S) := {c ∈ Γ.C | c ⊆ Set.univ \ Δ}
  let hasTouch : Prop := ∃ c ∈ I₂, (tilde c ∩ discBd Δ).Nonempty
  refine Subset.antisymm
    (inter_subset_inter_left _ ((Γ.removeDisc_N_subset hS Δ hΔ hnorm).trans sdiff_subset)) ?_
  rintro x ⟨hxN, hxbd⟩
  refine ⟨?_, hxbd⟩
  change x ∈ if hasTouch then Γ.N ∩ closure (Set.univ \ Δ) else Γ.N \ Δ
  split_ifs with ht
  · by_cases hxΔ : x ∈ Δ
    · exact ⟨hxN, hN_bd_cl ⟨hbd_sub ⟨hxΔ, hxbd⟩, hxN⟩⟩
    · exact ⟨hxN, subset_closure ⟨trivial, hxΔ⟩⟩
  · refine ⟨hxN, fun hxΔ => ?_⟩
    have hx_bdΔ : x ∈ discBd Δ := hbd_sub ⟨hxΔ, hxbd⟩
    let Θ := connectedComponentIn (bd S) x
    have hΘ : Θ ∈ cuffs S := ⟨x, hxbd, rfl⟩
    have hΘ_arc : IsOArc Θ := (cuff_statement S hS).2.2 Θ hΘ
    obtain ⟨E⟩ := Γ.exists_cuffEnumeration hΘ hΘ_arc
    have hx_range : x ∈ Set.range E.node := by
      rw [E.range_node]; exact ⟨hxN, mem_connectedComponentIn hxbd⟩
    rcases hx_range with ⟨i, hi⟩
    have hc_range : E.cell i ∈ {c ∈ Γ.C | (c ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact mem_range_self i
    have hbd_c : (E.cell i ∩ bd S).Nonempty :=
      hc_range.2.mono (inter_subset_inter_right _ (connectedComponentIn_subset _ _))
    have hc_I₂ : E.cell i ∈ I₂ := ⟨hc_range.1, hbd_cells (E.cell i) hc_range.1 hbd_c⟩
    have hx_tilde : x ∈ tilde (E.cell i) := by
      rw [← hi, E.cell_tilde i]
      exact mem_insert _ _
    exact ht ⟨E.cell i, hc_I₂, x, hx_tilde, hx_bdΔ⟩

/-- If $H = H_1 \cup H_2$ is a union of two subhypergraphs whose vertex sets share at most one
vertex ($|V(H_1) \cap V(H_2)| \le 1$), then any simple path in $H^*$ with both endpoints in
$V(H_1)$ lies entirely in $H_1^*$. -/
private theorem walk_in_left_of_ncard_inter_le_one {α : Type u} {β : Type v}
    {G H₁ H₂ : Hypergraph α β}
    (hH₁ : H₁ ≤ G) (hH₂ : H₂ ≤ G)
    (hcard : (H₁.vertexSet ∩ H₂.vertexSet).ncard ≤ 1)
    {u v : α} (hu : u ∈ H₁.vertexSet) (hv : v ∈ H₁.vertexSet)
    (w : (H₁ ∪ H₂).skeleton.Walk u v) (hp : w.IsPath) :
    ∀ z ∈ w.support, z ∈ H₁.vertexSet := by
  classical
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨z, hz_sup, hz_not₁⟩
  -- Split `w` at `z`: `w = w₁.append w₂` where `w₁ : Walk u z` and `w₂ : Walk z v`
  obtain ⟨w₁, w₂, hw_eq⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hz_sup
  -- Along `w₁` (from `u ∈ V(H₁)` to `z ∉ V(H₁)`), there is an edge with one endpoint in `V(H₁)`
  -- and the other outside `V(H₁)`, hence in `V(H₁) ∩ V(H₂)`
  have hex_cut : ∀ {a b : α} (p : (H₁ ∪ H₂).skeleton.Walk a b),
      a ∈ H₁.vertexSet → b ∉ H₁.vertexSet →
      ∃ x ∈ p.support, x ≠ b ∧ x ∈ H₁.vertexSet ∩ H₂.vertexSet := by
    intro a b p
    induction p with
    | nil => intro ha hb; exact False.elim (hb ha)
    | @cons x y c hadj p ih =>
      intro hx hc
      by_cases hy : y ∈ H₁.vertexSet
      · obtain ⟨w₀, hw₀_sup, hw₀_ne, hw₀_mem⟩ := ih hy hc
        exact ⟨w₀, List.mem_cons_of_mem x hw₀_sup, hw₀_ne, hw₀_mem⟩
      · refine ⟨x, SimpleGraph.Walk.start_mem_support _, fun h => hc (h ▸ hx), hx, ?_⟩
        rcases hadj with ⟨_, e, hincx, hincy⟩
        rcases hincy with hincy₁ | hincy₂
        · exact False.elim (hy (H₁.vertex_mem_of_inc hincy₁))
        · rcases hincx with hincx₁ | hincx₂
          · have he₂ : e ∈ H₂.edgeSet := H₂.edge_mem_of_inc hincy₂
            have hincxG : G.Inc e x := (inc_iff_of_le hH₁ (H₁.edge_mem_of_inc hincx₁)).mp hincx₁
            have hincx₂ : H₂.Inc e x := (inc_iff_of_le hH₂ he₂).mpr hincxG
            exact H₂.vertex_mem_of_inc hincx₂
          · exact H₂.vertex_mem_of_inc hincx₂
  obtain ⟨x₁, hx₁_sup, _, hx₁_inter⟩ := hex_cut w₁ hu hz_not₁
  obtain ⟨x₂, hx₂_sup, hx₂_ne_z, hx₂_inter⟩ := hex_cut w₂.reverse hv hz_not₁
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx₂_sup
  have hx₁_eq_x₂ : x₁ = x₂ := by
    by_contra hne
    have hpair : ({x₁, x₂} : Set α) ⊆ H₁.vertexSet ∩ H₂.vertexSet := by
      rintro y (rfl | rfl) <;> assumption
    have hfin : (H₁.vertexSet ∩ H₂.vertexSet).Finite := H₁.vertexSet_finite.subset inter_subset_left
    have h2 : 2 ≤ (H₁.vertexSet ∩ H₂.vertexSet).ncard := by
      rw [← ncard_pair hne]
      exact ncard_le_ncard hpair hfin
    omega
  rw [← hx₁_eq_x₂] at hx₂_sup
  have hnodup := hw_eq ▸ hp.support_nodup
  rw [SimpleGraph.Walk.support_append] at hnodup
  have hdisj := List.nodup_append.mp hnodup
  cases w₂ with
  | nil => exact hx₂_ne_z (hx₁_eq_x₂.symm.trans (List.mem_singleton.mp hx₂_sup))
  | cons hadj p' =>
    have hx₁_in_tail : x₁ ∈ p'.support := by
      rcases List.mem_cons.mp hx₂_sup with rfl | htail
      · exact False.elim (hx₂_ne_z hx₁_eq_x₂.symm)
      · exact htail
    exact hdisj.2.2 x₁ hx₁_sup x₁ hx₁_in_tail rfl

/-- Given a path `P : PathFromTo (H₁ ∪ H₂).skeleton S₁ S₂` with `S₁, S₂ ⊆ H₁.vertexSet`,
`Disjoint H₁.edgeSet H₂.edgeSet`, and `(H₁.vertexSet ∩ H₂.vertexSet).ncard ≤ 1`, `P` restricts
to a path in `H₁.skeleton` with the same vertex support. -/
private noncomputable def restrictPathFromToLeft {α : Type u} {β : Type v}
    {G H₁ H₂ : Hypergraph α β}
    (hH₁ : H₁ ≤ G) (hH₂ : H₂ ≤ G)
    (hcard : (H₁.vertexSet ∩ H₂.vertexSet).ncard ≤ 1)
    {S₁ S₂ : Set α} (hS₁ : S₁ ⊆ H₁.vertexSet) (hS₂ : S₂ ⊆ H₁.vertexSet)
    (P : PathFromTo (H₁ ∪ H₂).skeleton S₁ S₂) :
    {Q : PathFromTo H₁.skeleton S₁ S₂ //
      Q.first = P.first ∧ Q.last = P.last ∧
      ∀ z, z ∈ Q.walk.support ↔ z ∈ P.walk.support} := by
  classical
  have hsup : ∀ z ∈ P.walk.support, z ∈ H₁.vertexSet :=
    walk_in_left_of_ncard_inter_le_one hH₁ hH₂ hcard (hS₁ P.first_mem) (hS₂ P.last_mem)
      P.walk P.isPath
  have hadj : ∀ {x y : α}, x ∈ H₁.vertexSet → y ∈ H₁.vertexSet →
      (H₁ ∪ H₂).skeleton.Adj x y → H₁.skeleton.Adj x y := by
    rintro x y hx hy ⟨hne, e, hincx, hincy⟩
    have he₁_or_₂ : e ∈ H₁.edgeSet ∨ e ∈ H₂.edgeSet := by
      rcases hincx with h | h
      · exact Or.inl (H₁.edge_mem_of_inc h)
      · exact Or.inr (H₂.edge_mem_of_inc h)
    rcases he₁_or_₂ with he₁ | he₂
    · have hincxG : G.Inc e x := by
        rcases hincx with h | h
        · exact (inc_iff_of_le hH₁ (H₁.edge_mem_of_inc h)).mp h
        · exact (inc_iff_of_le hH₂ (H₂.edge_mem_of_inc h)).mp h
      have hincyG : G.Inc e y := by
        rcases hincy with h | h
        · exact (inc_iff_of_le hH₁ (H₁.edge_mem_of_inc h)).mp h
        · exact (inc_iff_of_le hH₂ (H₂.edge_mem_of_inc h)).mp h
      exact ⟨hne, e, (inc_iff_of_le hH₁ he₁).mpr hincxG, (inc_iff_of_le hH₁ he₁).mpr hincyG⟩
    · exfalso
      have hincxG : G.Inc e x := by
        rcases hincx with h | h
        · exact (inc_iff_of_le hH₁ (H₁.edge_mem_of_inc h)).mp h
        · exact (inc_iff_of_le hH₂ (H₂.edge_mem_of_inc h)).mp h
      have hincyG : G.Inc e y := by
        rcases hincy with h | h
        · exact (inc_iff_of_le hH₁ (H₁.edge_mem_of_inc h)).mp h
        · exact (inc_iff_of_le hH₂ (H₂.edge_mem_of_inc h)).mp h
      have hincx₂ : H₂.Inc e x := (inc_iff_of_le hH₂ he₂).mpr hincxG
      have hincy₂ : H₂.Inc e y := (inc_iff_of_le hH₂ he₂).mpr hincyG
      have hx_inter : x ∈ H₁.vertexSet ∩ H₂.vertexSet := ⟨hx, H₂.vertex_mem_of_inc hincx₂⟩
      have hy_inter : y ∈ H₁.vertexSet ∩ H₂.vertexSet := ⟨hy, H₂.vertex_mem_of_inc hincy₂⟩
      have hpair : ({x, y} : Set α) ⊆ H₁.vertexSet ∩ H₂.vertexSet := by
        rintro z (rfl | rfl) <;> assumption
      have hfin : (H₁.vertexSet ∩ H₂.vertexSet).Finite := H₁.vertexSet_finite.subset
        inter_subset_left
      have h2 : 2 ≤ (H₁.vertexSet ∩ H₂.vertexSet).ncard := by
        rw [← ncard_pair hne]
        exact ncard_le_ncard hpair hfin
      omega
  have hwalk : ∀ {a b : α} (w : (H₁ ∪ H₂).skeleton.Walk a b),
      (∀ z ∈ w.support, z ∈ H₁.vertexSet) →
      {w' : H₁.skeleton.Walk a b // w'.support = w.support} := by
    intro a b w
    induction w with
    | nil => intro _; exact ⟨.nil, rfl⟩
    | @cons x y c hadj_xy p ih =>
      intro hmem
      have hx : x ∈ H₁.vertexSet := hmem x (SimpleGraph.Walk.start_mem_support _)
      have hy : y ∈ H₁.vertexSet :=
        hmem y (List.mem_cons_of_mem x (SimpleGraph.Walk.start_mem_support _))
      obtain ⟨p', hp'⟩ := ih fun z hz => hmem z (List.mem_cons_of_mem x hz)
      refine ⟨.cons (hadj hx hy hadj_xy) p', ?_⟩
      simp [hp']
  obtain ⟨w', hw'_sup⟩ := hwalk P.walk hsup
  have hp' : w'.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hw'_sup]
    exact P.isPath.support_nodup
  refine ⟨⟨P.first, P.last, w', hp', P.first_mem, P.last_mem⟩, rfl, rfl, fun z => ?_⟩
  rw [hw'_sup]

private def discInsideCells {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Δ : Set π.S) : Set (Set π.S) :=
  {c ∈ π.Γ.C | c ⊆ Δ}

private def discOutsideCells {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Δ : Set π.S) : Set (Set π.S) :=
  {c ∈ π.Γ.C | c ⊆ univ \ Δ}

private noncomputable abbrev removeDiscPortrayal
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G)
    (Δ : Set π.S)
    (c' : Set π.S)
    (hc' : c' ∈ π.Γ.C)
    (hdich : ∀ c ∈ π.Γ.C, c ⊆ Δ \ discBd Δ ∨ c ⊆ univ \ Δ)
    (Γ' : Painting π.S)
    (hN'_sub : Γ'.N ⊆ π.Γ.N \ (Δ \ discBd Δ))
    (hN'_bd : Γ'.N ∩ bd π.S = π.Γ.N ∩ bd π.S)
    (hc'_mem : c' ∈ Γ'.C)
    (hC' : Γ'.C = (discOutsideCells π Δ))
    (hdisj_I : Disjoint (discInsideCells π Δ) (discOutsideCells π Δ))
    (hI₁_le : π.areaGraph Δ ≤ G)
    (hinter_sub_c' : (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion (discOutsideCells π Δ)).vertexSet ⊆
      (π.cellGraph c').vertexSet)
    (htilde_sub_N' : ∀ c ∈ Γ'.C, tilde c ⊆ Γ'.N)
    : Portrayal G := open Classical in
  let cellG : Set π.S → Hypergraph α β := fun c =>
    if c = c' then π.cellGraph c' ∪ π.areaGraph Δ else π.cellGraph c
  { S := π.S
    isSurface := π.isSurface
    connected := π.connected
    Γ := Γ'
    cellGraph := cellG
    borderSet := π.borderSet
    domγ := π.domγ ∩ Γ'.N
    nodeVertex := π.nodeVertex
    cellGraph_le := fun c hc => by
      rw [hC'] at hc
      dsimp only [cellG]
      split_ifs with hcc'
      · exact union_le (π.cellGraph_le c' hc') hI₁_le
      · exact π.cellGraph_le c hc.1
    borderSet_subset := fun n hn => π.borderSet_subset n (hN'_bd ▸ hn)
    domγ_subset := fun _ hn => hn.2
    nodeVertex_mem := fun n hn => π.nodeVertex_mem n hn.1
    nodeVertex_injOn := π.nodeVertex_injOn.mono inter_subset_left
    p1_vertex := fun v hv => by
      rcases π.p1_vertex v hv with ⟨c, hc, hvc⟩
      rcases hdich c hc with hc_in | hc_out
      · refine ⟨c', hc'_mem, ?_⟩
        change v ∈ (if c' = c' then π.cellGraph c' ∪ π.areaGraph Δ else π.cellGraph c').vertexSet
        simp only [↓reduceIte]
        right
        exact mem_iUnion₂.mpr ⟨c, ⟨⟨hc, hc_in.trans sdiff_subset⟩, hc⟩, hvc⟩
      · refine ⟨c, hC'.symm ▸ ⟨hc, hc_out⟩, ?_⟩
        dsimp only [cellG]
        split_ifs with hcc'
        · rw [← hcc']; exact Or.inl hvc
        · exact hvc
    p1_edge := fun e he => by
      rcases π.p1_edge e he with ⟨c, hc, hec⟩
      rcases hdich c hc with hc_in | hc_out
      · refine ⟨c', hc'_mem, ?_⟩
        change e ∈ (if c' = c' then π.cellGraph c' ∪ π.areaGraph Δ else π.cellGraph c').edgeSet
        simp only [↓reduceIte]
        right
        exact mem_iUnion₂.mpr ⟨c, ⟨⟨hc, hc_in.trans sdiff_subset⟩, hc⟩, hec⟩
      · refine ⟨c, hC'.symm ▸ ⟨hc, hc_out⟩, ?_⟩
        dsimp only [cellG]
        split_ifs with hcc'
        · rw [← hcc']; exact Or.inl hec
        · exact hec
    p1_disjoint := fun c₁ hc₁ c₂ hc₂ hne => by
      rw [hC'] at hc₁ hc₂
      dsimp only [cellG]
      split_ifs with h1 h2 h2
      · exact False.elim (hne (h1.trans h2.symm))
      · rw [← h1]
        refine Disjoint.union_left (π.p1_disjoint c₁ hc₁.1 c₂ hc₂.1 hne) ?_
        rw [Set.disjoint_left]
        intro e he₁ he₂
        rcases mem_iUnion₂.mp he₁ with ⟨c₀, hc₀, hec₀⟩
        have hc₀_ne : c₀ ≠ c₂ := fun h =>
          Set.disjoint_left.mp hdisj_I hc₀.1 (h ▸ hc₂)
        exact Set.disjoint_left.mp (π.p1_disjoint c₀ hc₀.2 c₂ hc₂.1 hc₀_ne) hec₀ he₂
      · rw [← h2]
        refine Disjoint.union_right (π.p1_disjoint c₁ hc₁.1 c₂ hc₂.1 hne) ?_
        rw [Set.disjoint_left]
        intro e he₁ he₂
        rcases mem_iUnion₂.mp he₂ with ⟨c₀, hc₀, hec₀⟩
        have hc₁_ne : c₁ ≠ c₀ := fun h =>
          Set.disjoint_left.mp hdisj_I hc₀.1 (h ▸ hc₁)
        exact Set.disjoint_left.mp (π.p1_disjoint c₁ hc₁.1 c₀ hc₀.2 hc₁_ne) he₁ hec₀
      · exact π.p1_disjoint c₁ hc₁.1 c₂ hc₂.1 hne
    p2 := fun c hc n hn => by
      rw [hC'] at hc
      have hvm : π.nodeVertex n ∈ (π.cellGraph c).vertexSet :=
        π.p2 c hc.1 n ⟨hn.1, hn.2.1⟩
      dsimp only [cellG]
      split_ifs with hcc'
      · rw [← hcc']; exact Or.inl hvm
      · exact hvm
    p3_notMem := fun n hn => π.p3_notMem n ⟨hn.1.1, hn.2⟩
    p3_subset := fun c hc hbd n hnt v hv => by
      rw [hC'] at hc
      have hvm := π.p3_subset c hc.1 hbd n hnt hv
      dsimp only [cellG]
      split_ifs with hcc'
      · rw [← hcc']; exact Or.inl hvm
      · exact hvm
    p4_disjoint := fun Θ₁ hΘ₁ Θ₂ hΘ₂ hne n₁ hn₁ n₂ hn₂ =>
      π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne n₁ ⟨(hN'_sub hn₁.1).1, hn₁.2⟩ n₂ ⟨(hN'_sub hn₂.1).1, hn₂.2⟩
    p4_notMem := fun Θ hΘ n₁ hn₁ n₂ hn₂ hnot =>
      π.p4_notMem Θ hΘ n₁ ⟨(hN'_sub hn₁.1).1, hn₁.2⟩ n₂ hn₂.1 hnot
    p5 := fun c hc hbd v hv hex => by
      rw [hC'] at hc
      rcases hex with ⟨d, hd, hne, hvd⟩
      rw [hC'] at hd
      have hvc : v ∈ (π.cellGraph c).vertexSet := by
        dsimp only [cellG] at hv hvd
        split_ifs at hv with hcc'
        · rcases hv with hvc' | hvΔ
          · rwa [hcc']
          · have hvd_d : v ∈ (π.cellGraph d).vertexSet := by
              split_ifs at hvd with hdc'
              · exact False.elim (hne (hdc'.trans hcc'.symm))
              · exact hvd
            rw [hcc']
            exact hinter_sub_c' ⟨hvΔ, mem_iUnion₂.mpr ⟨d, ⟨hd, hd.1⟩, hvd_d⟩⟩
        · exact hv
      have hvd' : ∃ d' ∈ π.Γ.C, d' ≠ c ∧ v ∈ (π.cellGraph d').vertexSet := by
        dsimp only [cellG] at hvd
        split_ifs at hvd with hdc'
        · rcases hvd with hvc' | hvΔ
          · exact ⟨d, hd.1, hne, hdc'.symm ▸ hvc'⟩
          · exact ⟨d, hd.1, hne, hdc'.symm ▸ hinter_sub_c' ⟨hvΔ, mem_iUnion₂.mpr ⟨c, ⟨hc,
              hc.1⟩, hvc⟩⟩⟩
        · exact ⟨d, hd.1, hne, hvd⟩
      obtain ⟨n, ⟨hnt, hndom⟩, rfl⟩ := π.p5 c hc.1 hbd v hvc hvd'
      exact ⟨n, ⟨hnt, hndom, htilde_sub_N' c (hC'.symm ▸ hc) hnt⟩, rfl⟩
    p6 := fun c hc hbd v hv hex => by
      rw [hC'] at hc
      rcases hex with ⟨d, hd, hne, hvd⟩
      rw [hC'] at hd
      have hvc : v ∈ (π.cellGraph c).vertexSet := by
        dsimp only [cellG] at hv hvd
        split_ifs at hv with hcc'
        · rcases hv with hvc' | hvΔ
          · rwa [hcc']
          · have hvd_d : v ∈ (π.cellGraph d).vertexSet := by
              split_ifs at hvd with hdc'
              · exact False.elim (hne (hdc'.trans hcc'.symm))
              · exact hvd
            rw [hcc']
            exact hinter_sub_c' ⟨hvΔ, mem_iUnion₂.mpr ⟨d, ⟨hd, hd.1⟩, hvd_d⟩⟩
        · exact hv
      have hvd' : ∃ d' ∈ π.Γ.C, d' ≠ c ∧ v ∈ (π.cellGraph d').vertexSet := by
        dsimp only [cellG] at hvd
        split_ifs at hvd with hdc'
        · rcases hvd with hvc' | hvΔ
          · exact ⟨d, hd.1, hne, hdc'.symm ▸ hvc'⟩
          · exact ⟨d, hd.1, hne, hdc'.symm ▸ hinter_sub_c' ⟨hvΔ, mem_iUnion₂.mpr ⟨c, ⟨hc,
              hc.1⟩, hvc⟩⟩⟩
        · exact ⟨d, hd.1, hne, hvd⟩
      obtain ⟨n, hnt, hmem | ⟨hndom, rfl⟩⟩ := π.p6 c hc.1 hbd v hvc hvd'
      · exact ⟨n, hnt, Or.inl hmem⟩
      · exact ⟨n, hnt, Or.inr ⟨⟨hndom, htilde_sub_N' c (hC'.symm ▸ hc) hnt⟩, rfl⟩⟩
    p7 := fun Θ hΘ n₁ hn₁ n₂ hn₂ n₃ hn₃ n₄ hn₄ hord v hv₁ hv₃ => by
      have hv₁' : v ∈ π.borderPlus n₁ := by
        rcases hv₁ with h | ⟨h, rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨h.1, rfl⟩
      have hv₃' : v ∈ π.borderPlus n₃ := by
        rcases hv₃ with h | ⟨h, rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨h.1, rfl⟩
      rcases π.p7 Θ hΘ n₁ ⟨(hN'_sub hn₁.1).1, hn₁.2⟩ n₂ ⟨(hN'_sub hn₂.1).1, hn₂.2⟩
        n₃ ⟨(hN'_sub hn₃.1).1, hn₃.2⟩ n₄ ⟨(hN'_sub hn₄.1).1, hn₄.2⟩ hord v hv₁' hv₃' with
        (h2 | ⟨h2, rfl⟩) | (h4 | ⟨h4, rfl⟩)
      · exact Or.inl (Or.inl h2)
      · exact Or.inl (Or.inr ⟨⟨h2, hn₂.1⟩, rfl⟩)
      · exact Or.inr (Or.inl h4)
      · exact Or.inr (Or.inr ⟨⟨h4, hn₄.1⟩, rfl⟩) }

private theorem removeDiscWarpAt
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G)
    (Δ : Set π.S)
    (c' : Set π.S)
    (hc' : c' ∈ π.Γ.C)
    (hdich : ∀ c ∈ π.Γ.C, c ⊆ Δ \ discBd Δ ∨ c ⊆ univ \ Δ)
    (Γ' : Painting π.S)
    (hN'_sub : Γ'.N ⊆ π.Γ.N \ (Δ \ discBd Δ))
    (hN'_bd : Γ'.N ∩ bd π.S = π.Γ.N ∩ bd π.S)
    (hc'_mem : c' ∈ Γ'.C)
    (hC' : Γ'.C = (discOutsideCells π Δ))
    (hdisj_I : Disjoint (discInsideCells π Δ) (discOutsideCells π Δ))
    (hI₁_le : π.areaGraph Δ ≤ G)
    (hinter_sub_c' : (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion (discOutsideCells π Δ)).vertexSet ⊆
      (π.cellGraph c').vertexSet)
    (htilde_sub_N' : ∀ c ∈ Γ'.C, tilde c ⊆ Γ'.N)
    (hcard : (discBd Δ ∩ π.Γ.N).ncard ≤ 1)
    (hbd_cells : ∀ c ∈ π.Γ.C, (c ∩ bd π.S).Nonempty → c ⊆ univ \ Δ)
    (hinter_sub : (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion (discOutsideCells π Δ)).vertexSet ⊆
      π.nodeVertex '' (tilde c' ∩ discBd Δ ∩ π.domγ)) :
  let π' := removeDiscPortrayal π Δ c' hc' hdich Γ' hN'_sub hN'_bd hc'_mem hC' hdisj_I hI₁_le
    hinter_sub_c' htilde_sub_N'
  ∀ Θ ∈ cuffs π.S, π'.warpAt Θ = π.warpAt Θ := by
  classical
  intro π'
  let I₂ := discOutsideCells π Δ
  let cellG : Set π.S → Hypergraph α β := fun c =>
    if c = c' then π.cellGraph c' ∪ π.areaGraph Δ else π.cellGraph c
  have hborderPlus_eq : ∀ n ∈ π.Γ.N ∩ bd π.S, π'.borderPlus n = π.borderPlus n := by
    intro n hn
    have hn' : n ∈ Γ'.N := (hN'_bd.symm ▸ hn).1
    ext v
    simp only [Portrayal.borderPlus, π', removeDiscPortrayal, mem_ofPred_eq, mem_inter_iff]
    exact ⟨fun h => h.elim Or.inl (fun ⟨⟨h1, _⟩, h2⟩ => Or.inr ⟨h1, h2⟩),
      fun h => h.elim Or.inl (fun ⟨h1, h2⟩ => Or.inr ⟨⟨h1, hn'⟩, h2⟩)⟩
  intro Θ hΘ
  have hΘ_sub : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x, _, rfl⟩
    exact connectedComponentIn_subset _ _
  have hcell_iff : ∀ (c : Set π.S) (q : ℕ), c ∈ Γ'.C → (c ∩ Θ).Nonempty →
      (π'.CellWarpLE c q ↔ π.CellWarpLE c q) := by
    intro c q hc hne_Θ
    rw [hC'] at hc
    have hbd_c : (c ∩ bd π.S).Nonempty := hne_Θ.mono (inter_subset_inter_right c hΘ_sub)
    have htilde_bd : tilde c ⊆ π.Γ.N ∩ bd π.S := by
      obtain ⟨_, _, _, htilde_sub, _⟩ := π.Γ.border_cell_subset_cuff hc.1 hΘ hne_Θ
      exact htilde_sub.trans (inter_subset_inter_right _ hΘ_sub)
    change (∀ n₁ ∈ tilde c, ∀ n₂ ∈ tilde c, n₁ ≠ n₂ →
      (π.borderSet n₁).ncard ≤ q ∧ (π.borderSet n₂).ncard ≤ q ∧
      ((π'.borderPlus n₁).ncard = q + 1 → (π'.borderPlus n₂).ncard = q + 1 →
        Portrayal.LinkagePairs (cellG c).skeleton (π'.borderPlus n₁) (π'.borderPlus n₂) (q + 1)
          (π.nodeVertex n₁) (π.nodeVertex n₂))) ↔
      π.CellWarpLE c q
    dsimp only [cellG]
    split_ifs with hcc'
    · rw [hcc'] at hc hbd_c htilde_bd ⊢
      have hcard_inter : ((π.cellGraph c').vertexSet ∩ (π.areaGraph Δ).vertexSet).ncard ≤ 1 := by
        have hsub_img : (π.cellGraph c').vertexSet ∩ (π.areaGraph Δ).vertexSet ⊆
            π.nodeVertex '' (discBd Δ ∩ π.Γ.N) := by
          intro v ⟨hvc', hvΔ⟩
          have hv_inter : v ∈ (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion I₂).vertexSet :=
            ⟨hvΔ, mem_iUnion₂.mpr ⟨c', ⟨hc, hc.1⟩, hvc'⟩⟩
          rcases hinter_sub hv_inter with ⟨n, ⟨⟨_, hnbd⟩, hdom⟩, rfl⟩
          exact ⟨n, ⟨hnbd, π.domγ_subset hdom⟩, rfl⟩
        have hfin_N : (discBd Δ ∩ π.Γ.N).Finite := π.Γ.finite_N.subset inter_subset_right
        calc ((π.cellGraph c').vertexSet ∩ (π.areaGraph Δ).vertexSet).ncard
          _ ≤ (π.nodeVertex '' (discBd Δ ∩ π.Γ.N)).ncard :=
            ncard_le_ncard hsub_img (hfin_N.image _)
          _ ≤ (discBd Δ ∩ π.Γ.N).ncard := ncard_image_le hfin_N
          _ ≤ 1 := hcard
      constructor
      · intro h n₁ hn₁ n₂ hn₂ hne
        obtain ⟨h1, h2, h3⟩ := h n₁ hn₁ n₂ hn₂ hne
        refine ⟨h1, h2, fun hb₁ hb₂ P hP => ?_⟩
        have hb₁' : (π'.borderPlus n₁).ncard = q + 1 := by
          rwa [hborderPlus_eq n₁ (htilde_bd hn₁)]
        have hb₂' : (π'.borderPlus n₂).ncard = q + 1 := by
          rwa [hborderPlus_eq n₂ (htilde_bd hn₂)]
        have hskel_le : (π.cellGraph c').skeleton ≤
            (π.cellGraph c' ∪ π.areaGraph Δ).skeleton :=
          fun x y ⟨hne, e, hx, hy⟩ => ⟨hne, e, Or.inl hx, Or.inl hy⟩
        let P' : Fin (q + 1) →
            PathFromTo (π.cellGraph c' ∪ π.areaGraph Δ).skeleton
              (π'.borderPlus n₁) (π'.borderPlus n₂) := fun i =>
          { first := (P i).first
            last := (P i).last
            walk := (P i).walk.map (SimpleGraph.Hom.ofLE hskel_le)
            isPath := by
              simpa [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_map] using
                (P i).isPath.support_nodup
            first_mem := by rw [hborderPlus_eq n₁ (htilde_bd hn₁)]; exact (P i).first_mem
            last_mem := by rw [hborderPlus_eq n₂ (htilde_bd hn₂)]; exact (P i).last_mem }
        have hP' : Pairwise fun i j =>
            Disjoint {z | z ∈ (P' i).walk.support} {z | z ∈ (P' j).walk.support} := by
          intro i j hij
          simpa [P', SimpleGraph.Walk.support_map] using hP hij
        exact h3 hb₁' hb₂' P' hP'
      · intro h n₁ hn₁ n₂ hn₂ hne
        obtain ⟨h1, h2, h3⟩ := h n₁ hn₁ n₂ hn₂ hne
        refine ⟨h1, h2, fun hb₁' hb₂' P hP => ?_⟩
        have hb₁ : (π.borderPlus n₁).ncard = q + 1 := by
          rwa [← hborderPlus_eq n₁ (htilde_bd hn₁)]
        have hb₂ : (π.borderPlus n₂).ncard = q + 1 := by
          rwa [← hborderPlus_eq n₂ (htilde_bd hn₂)]
        have hS₁ : π'.borderPlus n₁ ⊆ (π.cellGraph c').vertexSet := by
          rw [hborderPlus_eq n₁ (htilde_bd hn₁)]
          exact π.borderPlus_subset_cellGraph hc' hbd_c hn₁
        have hS₂ : π'.borderPlus n₂ ⊆ (π.cellGraph c').vertexSet := by
          rw [hborderPlus_eq n₂ (htilde_bd hn₂)]
          exact π.borderPlus_subset_cellGraph hc' hbd_c hn₂
        let Q : Fin (q + 1) →
            PathFromTo (π.cellGraph c').skeleton (π.borderPlus n₁) (π.borderPlus n₂) := fun i =>
          let R := (restrictPathFromToLeft (π.cellGraph_le c' hc') hI₁_le hcard_inter
            hS₁ hS₂ (P i)).1
          { first := R.first
            last := R.last
            walk := R.walk
            isPath := R.isPath
            first_mem := by rw [← hborderPlus_eq n₁ (htilde_bd hn₁)]; exact R.first_mem
            last_mem := by rw [← hborderPlus_eq n₂ (htilde_bd hn₂)]; exact R.last_mem }
        have hQ : Pairwise fun i j =>
            Disjoint {z | z ∈ (Q i).walk.support} {z | z ∈ (Q j).walk.support} := by
          intro i j hij
          have hsup_i := (restrictPathFromToLeft (π.cellGraph_le c' hc') hI₁_le hcard_inter
            hS₁ hS₂ (P i)).2.2.2
          have hsup_j := (restrictPathFromToLeft (π.cellGraph_le c' hc') hI₁_le hcard_inter
            hS₁ hS₂ (P j)).2.2.2
          refine Set.disjoint_left.mpr fun z hzi hzj => ?_
          exact Set.disjoint_left.mp (hP hij) ((hsup_i z).mp hzi) ((hsup_j z).mp hzj)
        obtain ⟨i, hi3, hi4⟩ := h3 hb₁ hb₂ Q hQ
        have hfi := (restrictPathFromToLeft (π.cellGraph_le c' hc') hI₁_le hcard_inter
          hS₁ hS₂ (P i)).2.1
        have hli := (restrictPathFromToLeft (π.cellGraph_le c' hc') hI₁_le hcard_inter
          hS₁ hS₂ (P i)).2.2.1
        exact ⟨i, hfi.symm.trans hi3, hli.symm.trans hi4⟩
    · constructor
      · intro h n₁ hn₁ n₂ hn₂ hne
        obtain ⟨h1, h2, h3⟩ := h n₁ hn₁ n₂ hn₂ hne
        refine ⟨h1, h2, fun hb₁ hb₂ P hP => ?_⟩
        have hb₁' : (π'.borderPlus n₁).ncard = q + 1 := by
          rwa [hborderPlus_eq n₁ (htilde_bd hn₁)]
        have hb₂' : (π'.borderPlus n₂).ncard = q + 1 := by
          rwa [hborderPlus_eq n₂ (htilde_bd hn₂)]
        let P' : Fin (q + 1) →
            PathFromTo (π.cellGraph c).skeleton (π'.borderPlus n₁) (π'.borderPlus n₂) := fun i =>
          { first := (P i).first
            last := (P i).last
            walk := (P i).walk
            isPath := (P i).isPath
            first_mem := by rw [hborderPlus_eq n₁ (htilde_bd hn₁)]; exact (P i).first_mem
            last_mem := by rw [hborderPlus_eq n₂ (htilde_bd hn₂)]; exact (P i).last_mem }
        exact h3 hb₁' hb₂' P' hP
      · intro h n₁ hn₁ n₂ hn₂ hne
        obtain ⟨h1, h2, h3⟩ := h n₁ hn₁ n₂ hn₂ hne
        refine ⟨h1, h2, fun hb₁' hb₂' P hP => ?_⟩
        have hb₁ : (π.borderPlus n₁).ncard = q + 1 := by
          rwa [← hborderPlus_eq n₁ (htilde_bd hn₁)]
        have hb₂ : (π.borderPlus n₂).ncard = q + 1 := by
          rwa [← hborderPlus_eq n₂ (htilde_bd hn₂)]
        let P' : Fin (q + 1) →
            PathFromTo (π.cellGraph c).skeleton (π.borderPlus n₁) (π.borderPlus n₂) := fun i =>
          { first := (P i).first
            last := (P i).last
            walk := (P i).walk
            isPath := (P i).isPath
            first_mem := by rw [← hborderPlus_eq n₁ (htilde_bd hn₁)]; exact (P i).first_mem
            last_mem := by rw [← hborderPlus_eq n₂ (htilde_bd hn₂)]; exact (P i).last_mem }
        exact h3 hb₁ hb₂ P' hP
  have hcellWarp_eq : ∀ c ∈ Γ'.C, (c ∩ Θ).Nonempty → π'.cellWarp c = π.cellWarp c := by
    intro c hc hne_Θ
    change sInf {q : ℕ | π'.CellWarpLE c q} = sInf {q : ℕ | π.CellWarpLE c q}
    congr 1
    ext q
    exact hcell_iff c q hc hne_Θ
  have hset_eq : {p : ℕ | ∃ c ∈ Γ'.C, (c ∩ Θ).Nonempty ∧ p = π'.cellWarp c} =
      {p : ℕ | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c} := by
    ext p
    constructor
    · rintro ⟨c, hc, hne_Θ, rfl⟩
      exact ⟨c, (hC' ▸ hc).1, hne_Θ, hcellWarp_eq c hc hne_Θ⟩
    · rintro ⟨c, hc, hne_Θ, rfl⟩
      have hbd_c : (c ∩ bd π.S).Nonempty := hne_Θ.mono (inter_subset_inter_right c hΘ_sub)
      have hc' : c ∈ Γ'.C := by
        rw [hC']
        exact ⟨hc, hbd_cells c hc hbd_c⟩
      exact ⟨c, hc', hne_Θ, (hcellWarp_eq c hc' hne_Θ).symm⟩
  change sSup {p : ℕ | ∃ c ∈ Γ'.C, (c ∩ Θ).Nonempty ∧ p = π'.cellWarp c} =
    sSup {p : ℕ | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c}
  rw [hset_eq]

private theorem removeDiscTruth
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G)
    (Δ : Set π.S)
    (c' : Set π.S)
    (hc' : c' ∈ π.Γ.C)
    (hdich : ∀ c ∈ π.Γ.C, c ⊆ Δ \ discBd Δ ∨ c ⊆ univ \ Δ)
    (Γ' : Painting π.S)
    (hN'_sub : Γ'.N ⊆ π.Γ.N \ (Δ \ discBd Δ))
    (hN'_bd : Γ'.N ∩ bd π.S = π.Γ.N ∩ bd π.S)
    (hc'_mem : c' ∈ Γ'.C)
    (hC' : Γ'.C = (discOutsideCells π Δ))
    (hdisj_I : Disjoint (discInsideCells π Δ) (discOutsideCells π Δ))
    (hI₁_le : π.areaGraph Δ ≤ G)
    (hinter_sub_c' : (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion (discOutsideCells π Δ)).vertexSet ⊆
      (π.cellGraph c').vertexSet)
    (htilde_sub_N' : ∀ c ∈ Γ'.C, tilde c ⊆ Γ'.N)
    (hbd_sub : Δ ∩ bd π.S ⊆ discBd Δ)
    (hbd_cells : ∀ c ∈ π.Γ.C, (c ∩ bd π.S).Nonempty → c ⊆ univ \ Δ) :
  let π' := removeDiscPortrayal π Δ c' hc' hdich Γ' hN'_sub hN'_bd hc'_mem hC' hdisj_I hI₁_le
    hinter_sub_c' htilde_sub_N'
  ¬(Δ \ discBd Δ ∩ π.Γ.U).Nonempty ∨ π'.IsTruer π := by
  classical
  intro π'
  let I₁ := discInsideCells π Δ
  by_cases hne_U : ((Δ \ discBd Δ) ∩ π.Γ.U).Nonempty
  · right
    by_cases hI₁_ne : I₁.Nonempty
    · have hsub_τ : ∀ j : Fin 4,
          {c ∈ Γ'.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - j.1} ⊆
          {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - j.1} := by
        intro j c hc
        rw [hC'] at hc
        exact ⟨hc.1.1, hc.2⟩
      have hex_nat : ∃ k : ℕ, k < 4 ∧ ∃ c ∈ I₁, (tilde c).ncard = 3 - k := by
        rcases hI₁_ne with ⟨c, hc⟩
        have hle3 : (tilde c).ncard ≤ 3 := π.Γ.ncard_tilde_cell_le hc.1
        exact ⟨3 - (tilde c).ncard, by omega, c, hc, by omega⟩
      let k₀ := Nat.find hex_nat
      have hk₀_lt : k₀ < 4 := (Nat.find_spec hex_nat).1
      obtain ⟨c₀, hc₀, hc₀_card⟩ := (Nat.find_spec hex_nat).2
      refine ⟨⟨k₀, by omega⟩, fun i hi => ?_, ?_⟩
      · have hi_lt : i.1 < k₀ := hi
        have hnot : ¬ (i.1 < 4 ∧ ∃ c ∈ I₁, (tilde c).ncard = 3 - i.1) := Nat.find_min hex_nat hi_lt
        have hno_c : ¬ ∃ c ∈ I₁, (tilde c).ncard = 3 - i.1 := fun h => hnot ⟨by omega, h⟩
        have hset_eq : {c ∈ Γ'.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - i.1} =
            {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - i.1} := by
          refine Subset.antisymm (hsub_τ ⟨i.1, by omega⟩) ?_
          rintro c ⟨hc, hint, hcard_c⟩
          rw [hC']
          rcases hdich c hc with hc_in | hc_out
          · exact False.elim (hno_c ⟨c, ⟨hc, hc_in.trans sdiff_subset⟩, hcard_c⟩)
          · exact ⟨⟨hc, hc_out⟩, hint, hcard_c⟩
        have hi4 : i.1 < 4 := by omega
        simp only [Portrayal.truth, π', removeDiscPortrayal, hi4, ↓reduceIte, hset_eq]
      · have hc₀_int : ¬ (c₀ ∩ bd π.S).Nonempty := fun hbd =>
          Set.disjoint_left.mp hdisj_I hc₀ ⟨hc₀.1, hbd_cells c₀ hc₀.1 hbd⟩
        have hc₀_in_old : c₀ ∈ {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀} :=
          ⟨hc₀.1, hc₀_int, hc₀_card⟩
        have hc₀_not_new : c₀ ∉ {c ∈ Γ'.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀}
          := by
          rw [hC']
          intro h
          exact Set.disjoint_left.mp hdisj_I hc₀ h.1
        have hssub : {c ∈ Γ'.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀} ⊂
            {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀} :=
          ⟨hsub_τ ⟨k₀, hk₀_lt⟩, fun h => hc₀_not_new (h hc₀_in_old)⟩
        have hfin_old : {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀}.Finite :=
          π.Γ.finite_cells.subset fun _ h => h.1
        have hlt_ncard := ncard_lt_ncard hssub hfin_old
        simp only [Portrayal.truth, π', removeDiscPortrayal, hk₀_lt, ↓reduceIte]
        exact hlt_ncard
    · have hC_same : Γ'.C = π.Γ.C := by
        rw [hC']
        refine Subset.antisymm (fun _ h => h.1) fun c hc => ⟨hc, ?_⟩
        rcases hdich c hc with hc_in | hc_out
        · exfalso; exact hI₁_ne ⟨c, hc, hc_in.trans sdiff_subset⟩
        · exact hc_out
      rcases hne_U with ⟨n₀, hn₀_open, hn₀_U⟩
      have hn₀_N : n₀ ∈ π.Γ.N := by
        by_contra hn₀_notN
        have : n₀ ∈ ⋃₀ π.Γ.C := by rw [π.Γ.sUnion_cells]; exact ⟨hn₀_U, hn₀_notN⟩
        rcases this with ⟨c, hc, hnc⟩
        have hc_out : c ⊆ Set.univ \ Δ := by
          have : c ∈ Γ'.C := hC_same.symm ▸ hc
          rw [hC'] at this
          exact this.2
        exact (hc_out hnc).2 hn₀_open.1
      have hn₀_not_bd : n₀ ∉ bd π.S := fun h => hn₀_open.2 (hbd_sub ⟨hn₀_open.1, h⟩)
      have hn₀_not_N' : n₀ ∉ Γ'.N := fun h => (hN'_sub h).2 hn₀_open
      refine ⟨⟨4, by decide⟩, fun i hi => ?_, ?_⟩
      · have hi4 : i.1 < 4 := hi
        simp only [Portrayal.truth, π', removeDiscPortrayal, hi4, ↓reduceIte, hC_same]
      · have hssub : Γ'.N \ bd π.S ⊂ π.Γ.N \ bd π.S :=
          ⟨sdiff_le_sdiff_right (hN'_sub.trans sdiff_subset),
            fun h => hn₀_not_N' (h ⟨hn₀_N, hn₀_not_bd⟩).1⟩
        simp only [Portrayal.truth, π', removeDiscPortrayal]
        exact ncard_lt_ncard hssub (π.Γ.finite_N.subset sdiff_subset)
  · exact Or.inl hne_U

/-- **Graph Minors XVII, (7.1)** (page 178):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $\mathcal{T}$-central portrayal of a
hypergraph $G$. Let $\Delta \subseteq \Sigma$ be a disc with $bd(\Delta)$ $\Gamma$-normal and
$|bd(\Delta) \cap N(\Gamma)| \le 1$, such that $\alpha(\Delta)$ is small. Let $c' \in C(\Gamma)$
with $c' \subseteq \Sigma - \Delta$, chosen with $\tilde{c}' \cap bd(\Delta) \ne \emptyset$ if
possible. If $\tilde{c}' \cap bd(\Delta) \ne \emptyset$, let $\Gamma' = (U(\Gamma) \cap
\overline{\Sigma - \Delta}, N(\Gamma) \cap \overline{\Sigma - \Delta})$. If $\tilde{c}' \cap
bd(\Delta) = \emptyset$, let $\Gamma' = (U(\Gamma) - \Delta, N(\Gamma) - \Delta)$. Define
$$ \begin{aligned} \alpha'(c') &= \alpha(c') \cup \alpha(\Delta) \\ \alpha'(c) &= \alpha(c) \quad (c
\in C(\Gamma') - \{c'\}) \\ \gamma' &= \gamma \mid N(\Gamma'). \end{aligned} $$
Then $\pi' = (\Sigma, \Gamma', \alpha', \beta, \gamma')$ is a $\mathcal{T}$-central portrayal of
$G$ resembling $\pi$." -/
theorem theorem_7_1_proof {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G) (hcentral : π.IsCentral 𝒯)
    {Δ : Set π.S} (hΔ : IsClosedDisc Δ) (hnorm : discBd Δ ∩ π.Γ.U ⊆ π.Γ.N)
    (hcard : (discBd Δ ∩ π.Γ.N).ncard ≤ 1)
    (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ))
    {c' : Set π.S} (hc' : c' ∈ π.Γ.C) (hc'_out : c' ⊆ Set.univ \ Δ)
    (hchoice : (∃ c ∈ π.Γ.C, c ⊆ Set.univ \ Δ ∧ (tilde c ∩ discBd Δ).Nonempty) →
      (tilde c' ∩ discBd Δ).Nonempty) :
    ∃ π' : Portrayal G,
      π'.S = π.S ∧
      π'.IsCentral 𝒯 ∧
      π'.Resembles π ∧
      ((¬ ((Δ \ discBd Δ) ∩ π.Γ.U).Nonempty) ∨ π'.IsTruer π) := by
  classical
  have hS : IsSurface π.S := π.isSurface
  have : T2Space π.S := hS.2.1
  obtain ⟨hopen, _, hbd_sub, _, _⟩ := isOpen_and_disjoint_bd_of_isClosedDisc hS hΔ
  obtain ⟨hdich, hbd_cells, hN_bd_cl⟩ := normal_disc_cell_dichotomy hS π.Γ hΔ hnorm
  set Γ' : Painting π.S := π.Γ.removeDisc hS Δ hΔ hnorm
  have hC' : Γ'.C = {c ∈ π.Γ.C | c ⊆ Set.univ \ Δ} :=
    π.Γ.removeDisc_C hS Δ hΔ hnorm
  have hN'_sub : Γ'.N ⊆ π.Γ.N \ (Δ \ discBd Δ) :=
    π.Γ.removeDisc_N_subset hS Δ hΔ hnorm
  have hN'_bd : Γ'.N ∩ bd π.S = π.Γ.N ∩ bd π.S :=
    π.Γ.removeDisc_N_inter_bd hS Δ hΔ hnorm
  have hc'_mem : c' ∈ Γ'.C := by
    rw [hC']
    exact ⟨hc', hc'_out⟩
  set I₁ : Set (Set π.S) := {c ∈ π.Γ.C | c ⊆ Δ}
  set I₂ : Set (Set π.S) := {c ∈ π.Γ.C | c ⊆ Set.univ \ Δ}
  have hpart : I₁ ∪ I₂ = π.Γ.C := by
    ext c
    simp only [I₁, I₂, mem_union, mem_sep_iff]
    refine ⟨fun h => h.elim And.left And.left, fun hc => ?_⟩
    rcases hdich c hc with h | h
    · exact Or.inl ⟨hc, h.trans sdiff_subset⟩
    · exact Or.inr ⟨hc, h⟩
  have hdisj_I : Disjoint I₁ I₂ := by
    refine Set.disjoint_left.mpr fun c ⟨hc, hc₁⟩ ⟨_, hc₂⟩ => ?_
    obtain ⟨x, hxc⟩ := π.Γ.cell_nonempty hc
    exact (hc₂ hxc).2 (hc₁ hxc)
  have hI₁_eq : π.areaGraph Δ = π.cellsUnion I₁ := by
    have h1 : π.areaGraph Δ ≤ G := hsmall.le_G h𝒯
    have h2 : π.cellsUnion I₁ ≤ G := π.cellsUnion_le I₁
    apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2
    · ext v; simp [Portrayal.areaGraph, Portrayal.cellsUnion, I₁]
    · ext e; simp [Portrayal.areaGraph, Portrayal.cellsUnion, I₁]
  have hI₁_le : π.areaGraph Δ ≤ G := hsmall.le_G h𝒯
  -- Key separation property from (2.1): any vertex in `V(α(Δ)) ∩ ⋃_{c ∈ I₂} V(α(c))`
  -- lies in `γ(tilde c' ∩ discBd Δ ∩ domγ) ⊆ V(α(c'))`
  have hinter_sub : (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion I₂).vertexSet ⊆
      π.nodeVertex '' (tilde c' ∩ discBd Δ ∩ π.domγ) := by
    have hv_inter := theorem_2_1_claim_3 π hpart hdisj_I
    intro v hv
    have hv' : v ∈ (π.cellsUnion I₁ ∩ π.cellsUnion I₂).vertexSet := by
      change v ∈ (π.cellsUnion I₁).vertexSet ∩ (π.cellsUnion I₂).vertexSet
      rwa [← hI₁_eq]
    rcases hv_inter hv' with ⟨n, ⟨⟨hX₁, hX₂⟩, hdom⟩, rfl⟩ | hY
    · rw [mem_iUnion₂] at hX₁ hX₂
      rcases hX₁ with ⟨c₁, hc₁, hnc₁⟩
      rcases hX₂ with ⟨c₂, hc₂, hnc₂⟩
      have hcl_Δ : closure Δ = Δ := (isClosed_of_isClosedDisc hΔ).closure_eq
      have hnΔ : n ∈ Δ := hcl_Δ ▸ closure_mono hc₁.2 hnc₁.1
      have hcl := (closure_cell_inter_disc_of_subset_compl hS π.Γ hΔ hnorm hc₂.1 hc₂.2).2
      have hnbdΔ : n ∈ discBd Δ := by
        have : n ∈ closure c₂ ∩ Δ := ⟨hnc₂.1, hnΔ⟩
        rw [hcl] at this
        exact this.2
      have hex_touch : ∃ c ∈ π.Γ.C, c ⊆ Set.univ \ Δ ∧ (tilde c ∩ discBd Δ).Nonempty :=
        ⟨c₂, hc₂.1, hc₂.2, n, hnc₂, hnbdΔ⟩
      obtain ⟨n', hn'_t, hn'_bd⟩ := hchoice hex_touch
      have hn_eq : n = n' := by
        by_contra hne
        have hpair : ({n, n'} : Set π.S) ⊆ discBd Δ ∩ π.Γ.N := by
          rintro z (rfl | rfl)
          · exact ⟨hnbdΔ, π.domγ_subset hdom⟩
          · exact ⟨hn'_bd, π.Γ.tilde_subset_N hc' hn'_t⟩
        have hfin : (discBd Δ ∩ π.Γ.N).Finite := π.Γ.finite_N.subset inter_subset_right
        have h2 : 2 ≤ (discBd Δ ∩ π.Γ.N).ncard := by
          rw [← ncard_pair hne]
          exact ncard_le_ncard hpair hfin
        omega
      subst hn_eq
      exact ⟨n, ⟨⟨hn'_t, hnbdΔ⟩, hdom⟩, rfl⟩
    · exfalso
      rw [mem_iUnion₂] at hY
      rcases hY with ⟨n, ⟨hY₁, _⟩, _⟩
      rw [mem_iUnion₂] at hY₁
      rcases hY₁ with ⟨c₁, ⟨hc₁, hbd₁⟩, _⟩
      exact Set.disjoint_left.mp hdisj_I hc₁ ⟨hc₁.1, hbd_cells c₁ hc₁.1 hbd₁⟩
  have hinter_sub_c' : (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion I₂).vertexSet ⊆
      (π.cellGraph c').vertexSet := by
    intro v hv
    rcases hinter_sub hv with ⟨n, ⟨⟨hnt, _⟩, hdom⟩, rfl⟩
    exact π.p2 c' hc' n ⟨hnt, hdom⟩
  have htilde_sub_N' : ∀ c ∈ Γ'.C, tilde c ⊆ Γ'.N :=
    fun c hc => Γ'.tilde_subset_N hc
  -- Define `π'`
  let cellG : Set π.S → Hypergraph α β := fun c =>
    if c = c' then π.cellGraph c' ∪ π.areaGraph Δ else π.cellGraph c
  let π' := removeDiscPortrayal π Δ c' hc' hdich Γ' hN'_sub hN'_bd hc'_mem hC' hdisj_I hI₁_le
    hinter_sub_c' htilde_sub_N'
  -- Check that `π'` is `𝒯`-central
  have hcentral' : π'.IsCentral 𝒯 := by
    intro c hc
    change IsSmallWrt 𝒯 (cellG c)
    rw [hC'] at hc
    dsimp only [cellG]
    split_ifs with hcc'
    · obtain ⟨B₁, hB₁⟩ := hcentral c' hc'
      have hord_B₁ : separationOrder (π.cellGraph c') B₁ < θ := h𝒯.order_lt hB₁
      have hatt_sub : attachments G (π.cellGraph c' ∪ π.areaGraph Δ) ⊆
          (π.cellGraph c').vertexSet ∩ B₁.vertexSet := by
        rintro v ⟨hv_union, e, ⟨heG, he_not⟩, hinc⟩
        rcases π.p1_edge e heG with ⟨d, hd, hed⟩
        have hd_I₂ : d ∈ I₂ ∧ d ≠ c' := by
          rcases hdich d hd with hd_in | hd_out
          · exfalso
            apply he_not
            right
            exact mem_iUnion₂.mpr ⟨d, ⟨⟨hd, hd_in.trans sdiff_subset⟩, hd⟩, hed⟩
          · refine ⟨⟨hd, hd_out⟩, fun h => he_not (Or.inl (h ▸ hed))⟩
        have hvd : v ∈ (π.cellGraph d).vertexSet :=
          (π.cellGraph d).vertex_mem_of_inc ((inc_iff_of_le (π.cellGraph_le d hd) hed).mpr hinc)
        have hvc' : v ∈ (π.cellGraph c').vertexSet := by
          rcases hv_union with hvc' | hvΔ
          · exact hvc'
          · exact hinter_sub_c' ⟨hvΔ, mem_iUnion₂.mpr ⟨d, ⟨hd_I₂.1, hd_I₂.1.1⟩, hvd⟩⟩
        have he_not_c' : e ∉ (π.cellGraph c').edgeSet := fun h => he_not (Or.inl h)
        have hsep₁ := h𝒯.isSeparation hB₁
        have heB₁ : e ∈ B₁.edgeSet := by
          have h_union : e ∈ (π.cellGraph c' ∪ B₁).edgeSet := by
            rw [hsep₁.union_eq]; exact heG
          exact h_union.resolve_left he_not_c'
        exact ⟨hvc', B₁.vertex_mem_of_inc ((inc_iff_of_le hsep₁.right_le heB₁).mpr hinc)⟩
      have hfin_B₁ : ((π.cellGraph c').vertexSet ∩ B₁.vertexSet).Finite :=
        (π.cellGraph c').vertexSet_finite.subset inter_subset_left
      have hatt_lt : (attachments G (π.cellGraph c' ∪ π.areaGraph Δ)).ncard < θ :=
        lt_of_le_of_lt (ncard_le_ncard hatt_sub hfin_B₁) hord_B₁
      exact IsSmallWrt.union h𝒯 (hcentral c' hc') hsmall hatt_lt
    · exact hcentral c hc.1
  -- Check that `π'` has the same warp as `π` at every cuff `Θ`
  have hwarp_eq :=
    removeDiscWarpAt π Δ c' hc' hdich Γ' hN'_sub hN'_bd hc'_mem hC' hdisj_I hI₁_le hinter_sub_c'
      htilde_sub_N' hcard hbd_cells hinter_sub
  have hresembles : π'.Resembles π := by
    refine ⟨Homeomorph.refl π.S, fun Θ hΘ => ?_⟩
    have himg : (Homeomorph.refl π.S : π.S → π.S) '' Θ = Θ := image_id Θ
    rw [himg]
    exact hwarp_eq Θ hΘ
  -- Check trueness when `((Δ \ discBd Δ) ∩ π.Γ.U).Nonempty`
  refine ⟨π', rfl, hcentral', hresembles, ?_⟩
  exact removeDiscTruth π Δ c' hc' hdich Γ' hN'_sub hN'_bd hc'_mem hC' hdisj_I hI₁_le hinter_sub_c'
    htilde_sub_N' hbd_sub hbd_cells

end Theorem71

/-! ## 3. Replacing a Normal Disc with at Most Three Boundary Nodes ((7.2), Page 178) -/

section Theorem72

variable {S : Type} [TopologicalSpace S]

/-- For a closed disc $\Delta \subseteq S$ in a Hausdorff space $S$ and any subset
$F \subseteq \operatorname{discBd} \Delta$, the difference $\Delta \setminus F$ is nonempty,
path-connected, and has closure $\overline{\Delta \setminus F} = \Delta$. -/
theorem isClosedDisc_sdiff_subset_discBd [T2Space S] {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hF : F ⊆ discBd Δ) :
    (Δ \ F).Nonempty ∧ IsPathConnected (Δ \ F) ∧ closure (Δ \ F) = Δ := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  have hball_sub : g '' ball 0 1 ⊆ Δ \ F := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨c.gm (ball_subset_closedBall hz), fun hxF => ?_⟩
    exact Set.disjoint_left.mp c.union_ball.2 ⟨z, hz, rfl⟩ (hF hxF)
  have h0_mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self zero_lt_one
  have hx₀ : g 0 ∈ Δ \ F := hball_sub ⟨0, h0_mem, rfl⟩
  have hpc : IsPathConnected (Δ \ F) := by
    refine ⟨g 0, hx₀, fun {y} hy => ?_⟩
    let z : ℂ := h y
    have hz_cb : z ∈ closedBall (0 : ℂ) 1 := c.hm hy.1
    have hgz : g z = y := c.gh hy.1
    let φ : unitInterval → ℂ := fun t => (t : ℝ) • z
    have hφ_cont : Continuous φ := continuous_subtype_val.smul continuous_const
    have hφ_mem : ∀ t : unitInterval, φ t ∈ closedBall (0 : ℂ) 1 := by
      intro t
      rw [mem_closedBall_zero_iff] at hz_cb ⊢
      change ‖(t : ℝ) • z‖ ≤ 1
      rw [norm_smul, Real.norm_of_nonneg t.2.1]
      calc (t : ℝ) * ‖z‖ ≤ (t : ℝ) * 1 := mul_le_mul_of_nonneg_left hz_cb t.2.1
        _ ≤ 1 := by linarith [t.2.2]
    let γ : Path (g 0) y :=
      { toFun := g ∘ φ
        continuous_toFun := c.gc.comp_continuous hφ_cont hφ_mem
        source' := by change g ((0 : ℝ) • z) = g 0; simp
        target' := by change g ((1 : ℝ) • z) = y; simp [hgz] }
    refine ⟨γ, fun t => ?_⟩
    by_cases ht1 : (t : ℝ) = 1
    · have : γ t = y := by
        change g ((t : ℝ) • z) = y
        rw [ht1, one_smul, hgz]
      rw [this]
      exact hy
    · have ht_lt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht1
      have hφ_ball : φ t ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]
        rw [mem_closedBall_zero_iff] at hz_cb
        change ‖(t : ℝ) • z‖ < 1
        rw [norm_smul, Real.norm_of_nonneg t.2.1]
        calc (t : ℝ) * ‖z‖ ≤ (t : ℝ) * 1 := mul_le_mul_of_nonneg_left hz_cb t.2.1
          _ < 1 := by linarith
      exact hball_sub ⟨φ t, hφ_ball, rfl⟩
  have hcl : closure (Δ \ F) = Δ := by
    refine Subset.antisymm (closure_minimal sdiff_subset hΔ.isCompact.isClosed) ?_
    intro x hx
    have hzx : h x ∈ closure (ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) one_ne_zero]
      exact c.hm hx
    have hgc_cl : ContinuousOn g (closure (ball (0 : ℂ) 1)) := by
      rw [closure_ball (0 : ℂ) one_ne_zero]
      exact c.gc
    have hg_cl : g (h x) ∈ closure (g '' ball 0 1) :=
      hgc_cl.image_closure ⟨h x, hzx, rfl⟩
    rw [c.gh hx] at hg_cl
    exact closure_mono hball_sub hg_cl
  exact ⟨⟨g 0, hx₀⟩, hpc, hcl⟩

/-- The modified painting $\Gamma' = (U(\Gamma) \cup \Delta, N(\Gamma) \cap \overline{\Sigma
\setminus \Delta})$
in Graph Minors XVII, (7.2) (page 178), replacing the interior of a $\Gamma$-normal closed disc
$\Delta$ with $|\operatorname{discBd} \Delta \cap N(\Gamma)| \le 3$ by a single internal cell
$c' = \Delta \setminus (\operatorname{discBd} \Delta \cap N(\Gamma))$. -/
noncomputable def Painting.replaceDiscWithCells (hS : IsSurface S) (Γ : Painting S) (Δ : Set S)
    (hΔ : IsClosedDisc Δ) (hnorm : discBd Δ ∩ Γ.U ⊆ Γ.N)
    (hcard : (discBd Δ ∩ Γ.N).ncard ≤ 3) :
    {Γ' : Painting S // Γ'.C = insert (Δ \ (discBd Δ ∩ Γ.N)) {c ∈ Γ.C | c ⊆ Set.univ \ Δ}} := by
  classical
  have : T2Space S := hS.2.1
  obtain ⟨hopen, hdisj_bd, hbd_sub, _, _⟩ := isOpen_and_disjoint_bd_of_isClosedDisc hS hΔ
  obtain ⟨hdich, hbd_cells, hN_bd_cl⟩ := normal_disc_cell_dichotomy hS Γ hΔ hnorm
  let U' : Set S := Γ.U ∪ Δ
  let N' : Set S := Γ.N ∩ closure (Set.univ \ Δ)
  let c' : Set S := Δ \ (discBd Δ ∩ Γ.N)
  set I₂ : Set (Set S) := {c ∈ Γ.C | c ⊆ Set.univ \ Δ}
  have hI₂_fin : I₂.Finite := Γ.finite_cells.subset fun _ h => h.1
  have hΔ_inter_N' : Δ ∩ N' = discBd Δ ∩ Γ.N := by
    refine Subset.antisymm ?_ (fun x hx => ⟨discBd_subset Δ hx.1, hx.2, hN_bd_cl hx⟩)
    rintro x ⟨hxΔ, hxN, hxcl⟩
    refine ⟨?_, hxN⟩
    by_contra hx_not_bd
    have hx_open : x ∈ Δ \ discBd Δ := ⟨hxΔ, hx_not_bd⟩
    have hdisj : Disjoint (Δ \ discBd Δ) (Set.univ \ Δ) :=
      Set.disjoint_left.mpr fun y hy₁ hy₂ => hy₂.2 hy₁.1
    exact Set.disjoint_left.mp (hdisj.closure_right hopen) hx_open hxcl
  have hc'_eq : c' = Δ \ N' := by
    change Δ \ (discBd Δ ∩ Γ.N) = Δ \ N'
    rw [← hΔ_inter_N']
    ext x; simp
  have hΔ_bd_sub : Δ ∩ bd S ⊆ discBd Δ ∩ Γ.N := fun x ⟨hxΔ, hxbd⟩ =>
    ⟨hbd_sub ⟨hxΔ, hxbd⟩, hnorm ⟨hbd_sub ⟨hxΔ, hxbd⟩, Γ.bd_subset hxbd⟩⟩
  have hc'_disj_bd : Disjoint c' (bd S) :=
    Set.disjoint_left.mpr fun x ⟨hxΔ, hxnot⟩ hxbd => hxnot (hΔ_bd_sub ⟨hxΔ, hxbd⟩)
  obtain ⟨hc'_ne, hc'_pc, hc'_cl⟩ :=
    isClosedDisc_sdiff_subset_discBd hΔ (inter_subset_left : discBd Δ ∩ Γ.N ⊆ discBd Δ)
  have htilde_c' : tilde c' = discBd Δ ∩ Γ.N := by
    change closure c' \ c' = _
    rw [hc'_cl]
    change Δ \ (Δ \ (discBd Δ ∩ Γ.N)) = _
    rw [Set.sdiff_sdiff_right_self, inter_eq_right.mpr (inter_subset_left.trans (discBd_subset Δ))]
  have hcov : ⋃₀ insert c' I₂ = U' \ N' := by
    ext x
    simp only [sUnion_insert, mem_union, mem_sUnion, mem_sdiff]
    constructor
    · rintro (hxc' | ⟨c, ⟨hc, hc_sub⟩, hxc⟩)
      · rw [hc'_eq] at hxc'
        exact ⟨Or.inr hxc'.1, hxc'.2⟩
      · refine ⟨Or.inl (Γ.cell_subset_U hc hxc), fun hxN' => ?_⟩
        exact (Γ.cell_subset_diff hc hxc).2 hxN'.1
    · rintro ⟨hxU | hxΔ, hxN'⟩
      · by_cases hxΔ : x ∈ Δ
        · left
          rw [hc'_eq]
          exact ⟨hxΔ, hxN'⟩
        · right
          have hx_compl : x ∈ Set.univ \ Δ := ⟨ trivial, hxΔ ⟩
          have hxN : x ∉ Γ.N := fun hxN => hxN' ⟨hxN, subset_closure hx_compl⟩
          have hx_sUnion : x ∈ ⋃₀ Γ.C := by rw [Γ.sUnion_cells]; exact ⟨hxU, hxN⟩
          rcases hx_sUnion with ⟨c, hc, hxc⟩
          rcases hdich c hc with hc_in | hc_out
          · exact False.elim (hxΔ (hc_in hxc).1)
          · exact ⟨c, ⟨hc, hc_out⟩, hxc⟩
      · left
        rw [hc'_eq]
        exact ⟨hxΔ, hxN'⟩
  have hC_eq : arcComponentsIn (U' \ N') = insert c' I₂ := by
    apply arcComponentsIn_eq_of_finite_cover (hI₂_fin.insert c') hcov
    · rintro c (rfl | hcI₂)
      · exact hc'_ne
      · exact Γ.cell_nonempty hcI₂.1
    · rintro c (rfl | hcI₂)
      · exact hc'_pc
      · exact Γ.cell_isPathConnected hcI₂.1
    · rintro c₁ (rfl | hc₁) c₂ (rfl | hc₂) hne
      · exact (hne rfl).elim
      · exact Set.disjoint_left.mpr fun x hxc' hxc₂ => (hc₂.2 hxc₂).2 hxc'.1
      · exact Set.disjoint_left.mpr fun x hxc₁ hxc' => (hc₁.2 hxc₁).2 hxc'.1
      · exact Γ.cell_disjoint hc₁.1 hc₂.1 hne
    · rintro c (rfl | hcI₂)
      · refine Subset.antisymm ?_ (fun x hxc => ⟨subset_closure hxc,
          hcov ▸ mem_sUnion_of_mem hxc (mem_insert _ _)⟩)
        rintro x ⟨hxcl, _, hxN'⟩
        rw [hc'_cl] at hxcl
        rw [hc'_eq]
        exact ⟨hxcl, hxN'⟩
      · refine Subset.antisymm ?_ (fun x hxc => ⟨subset_closure hxc,
          hcov ▸ mem_sUnion_of_mem hxc (mem_insert_of_mem _ hcI₂)⟩)
        rintro x ⟨hxcl, _, hxN'⟩
        have hcl_sub := (closure_cell_inter_disc_of_subset_compl hS Γ hΔ hnorm hcI₂.1 hcI₂.2).1
        have hxN : x ∉ Γ.N := fun hxN => hxN' ⟨hxN, hcl_sub hxcl⟩
        rw [← Γ.closure_cell_diff_N hcI₂.1]
        exact ⟨hxcl, hxN⟩
  refine ⟨?_, ?_⟩
  · exact
      { U := U'
        N := N'
        isClosed_U := Γ.isClosed_U.union hΔ.isCompact.isClosed
        bd_subset := Γ.bd_subset.trans subset_union_left
        N_subset := (inter_subset_left.trans Γ.N_subset).trans subset_union_left
        finite_N := Γ.finite_N.subset inter_subset_left
        finite_cells := hC_eq ▸ hI₂_fin.insert c'
        cell_disc := fun c hc => by
          rw [hC_eq] at hc
          rcases hc with rfl | hcI₂
          · rw [hc'_cl, htilde_c']
            exact ⟨hΔ, inter_subset_left, Γ.finite_N.inter_of_right (discBd Δ), hcard⟩
          · exact Γ.cell_disc c hcI₂.1
        border_cell := fun c hc hbd => by
          rw [hC_eq] at hc
          rcases hc with rfl | hcI₂
          · exact False.elim (Set.not_nonempty_iff_eq_empty.mpr
              (Set.disjoint_iff_inter_eq_empty.mp hc'_disj_bd) hbd)
          · exact Γ.border_cell c hcI₂.1 hbd }
  · exact hC_eq

/-- The painting obtained by replacing a disc. -/
noncomputable def Painting.replaceDisc (hS : IsSurface S) (Γ : Painting S) (Δ : Set S)
    (hΔ : IsClosedDisc Δ) (hnorm : discBd Δ ∩ Γ.U ⊆ Γ.N)
    (hcard : (discBd Δ ∩ Γ.N).ncard ≤ 3) : Painting S :=
  (Γ.replaceDiscWithCells hS Δ hΔ hnorm hcard).1

theorem Painting.replaceDisc_C (hS : IsSurface S) (Γ : Painting S) (Δ : Set S)
    (hΔ : IsClosedDisc Δ) (hnorm : discBd Δ ∩ Γ.U ⊆ Γ.N)
    (hcard : (discBd Δ ∩ Γ.N).ncard ≤ 3) :
    (Γ.replaceDisc hS Δ hΔ hnorm hcard).C =
      insert (Δ \ (discBd Δ ∩ Γ.N)) {c ∈ Γ.C | c ⊆ Set.univ \ Δ} :=
  (Γ.replaceDiscWithCells hS Δ hΔ hnorm hcard).2

/-- Given a subhypergraph $H \le G$ and a vertex subset $W \subseteq V(G)$, the minimal
subhypergraph $A \le G$ with $H \le A$ and $W \subseteq V(A)$ is $H \cup \text{discrete}(W)$,
having vertex set $V(H) \cup W$ and edge set $E(H)$. -/
@[expose]
def addVerticesSubhypergraph {α : Type u} {β : Type v} (G H : Hypergraph α β) (W : Set α)
    (_hH : H ≤ G) (hW : W ⊆ G.vertexSet) : Hypergraph α β :=
  H ∪ discreteSubhypergraph G W hW

theorem addVerticesSubhypergraph_le {α : Type u} {β : Type v} {G H : Hypergraph α β} {W : Set α}
    (hH : H ≤ G) (hW : W ⊆ G.vertexSet) :
    addVerticesSubhypergraph G H W hH hW ≤ G :=
  union_le hH ⟨hW, empty_subset _, fun _ h => h.elim⟩

@[simp]
theorem addVerticesSubhypergraph_vertexSet {α : Type u} {β : Type v} {G H : Hypergraph α β}
    {W : Set α} (_hH : H ≤ G) (hW : W ⊆ G.vertexSet) :
    (addVerticesSubhypergraph G H W _hH hW).vertexSet = H.vertexSet ∪ W := rfl

@[simp]
theorem addVerticesSubhypergraph_edgeSet {α : Type u} {β : Type v} {G H : Hypergraph α β}
    {W : Set α} (_hH : H ≤ G) (hW : W ⊆ G.vertexSet) :
    (addVerticesSubhypergraph G H W _hH hW).edgeSet = H.edgeSet :=
  union_empty H.edgeSet

private def discBorderVertices {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Δ : Set π.S) : Set α :=
  π.nodeVertex '' (discBd Δ ∩ π.domγ)

private def replacementDiscGraph {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G) (Δ : Set π.S) (hle : π.areaGraph Δ ≤ G)
    (hsub : discBorderVertices π Δ ⊆ G.vertexSet) : Hypergraph α β :=
  addVerticesSubhypergraph G (π.areaGraph Δ) (discBorderVertices π Δ) hle hsub

private noncomputable abbrev replaceDiscPortrayal
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G)
    (Δ : Set π.S)
    (hnode : ∀ n ∈ discBd Δ ∩ π.domγ, ∃ d ∈ π.Γ.C, n ∈ tilde d)
    (hdich : ∀ c ∈ π.Γ.C, c ⊆ Δ \ discBd Δ ∨ c ⊆ univ \ Δ)
    (Γ' : Painting π.S)
    (c' : Set π.S)
    (hC' : Γ'.C = insert c' (discOutsideCells π Δ))
    (hc'_mem : c' ∈ Γ'.C)
    (htilde_c' : tilde c' = discBd Δ ∩ π.Γ.N)
    (hc'_not_bd : ¬(c' ∩ bd π.S).Nonempty)
    (hc'_not_I₂ : c' ∉ (discOutsideCells π Δ))
    (hN'_sub : Γ'.N ⊆ π.Γ.N \ (Δ \ discBd Δ))
    (hN'_bd : Γ'.N ∩ bd π.S = π.Γ.N ∩ bd π.S)
    (hdisj_I : Disjoint (discInsideCells π Δ) (discOutsideCells π Δ))
    (hI₁_le : π.areaGraph Δ ≤ G)
    (hW_bd_sub : (discBorderVertices π Δ) ⊆ G.vertexSet)
    (hA_le : (replacementDiscGraph π Δ hI₁_le hW_bd_sub) ≤ G)
    (hA_inter_I₂ : (replacementDiscGraph π Δ hI₁_le hW_bd_sub).vertexSet ∩ (π.cellsUnion
      (discOutsideCells π Δ)).vertexSet ⊆ (discBorderVertices π Δ))
    (htilde_sub_N' : ∀ c ∈ Γ'.C, tilde c ⊆ Γ'.N)
    : Portrayal G := open Classical in
  let I₂ := discOutsideCells π Δ
  let W_bd := discBorderVertices π Δ
  let A := replacementDiscGraph π Δ hI₁_le hW_bd_sub
  let cellG : Set π.S → Hypergraph α β := fun c =>
    if c = c' then A else π.cellGraph c
  { S := π.S
    top := π.top
    isSurface := π.isSurface
    connected := π.connected
    Γ := Γ'
    cellGraph := cellG
    borderSet := π.borderSet
    domγ := π.domγ ∩ Γ'.N
    nodeVertex := π.nodeVertex
    cellGraph_le := fun c hc => by
      rw [hC'] at hc
      dsimp only [cellG]
      split_ifs with hcc'
      · exact hA_le
      · exact π.cellGraph_le c (hc.resolve_left hcc').1
    borderSet_subset := fun n hn => by
      rw [hN'_bd] at hn
      exact π.borderSet_subset n hn
    domγ_subset := inter_subset_right
    nodeVertex_mem := fun n hn => π.nodeVertex_mem n hn.1
    nodeVertex_injOn := π.nodeVertex_injOn.mono inter_subset_left
    p1_vertex := fun v hv => by
      rcases π.p1_vertex v hv with ⟨c, hc, hvc⟩
      rcases hdich c hc with hc_in | hc_out
      · refine ⟨c', hc'_mem, ?_⟩
        change v ∈ (if c' = c' then A else π.cellGraph c').vertexSet
        simp only [↓reduceIte, A, replacementDiscGraph, addVerticesSubhypergraph_vertexSet]
        left
        exact mem_iUnion₂.mpr ⟨c, ⟨⟨hc, hc_in.trans sdiff_subset⟩, hc⟩, hvc⟩
      · refine ⟨c, hC'.symm ▸ mem_insert_of_mem c' ⟨hc, hc_out⟩, ?_⟩
        have hne : c ≠ c' := fun h => hc'_not_I₂ (h ▸ ⟨hc, hc_out⟩)
        dsimp only [cellG]
        rw [ite_eq_right hne]
        exact hvc
    p1_edge := fun e he => by
      rcases π.p1_edge e he with ⟨c, hc, hec⟩
      rcases hdich c hc with hc_in | hc_out
      · refine ⟨c', hc'_mem, ?_⟩
        change e ∈ (if c' = c' then A else π.cellGraph c').edgeSet
        simp only [↓reduceIte, A, replacementDiscGraph, addVerticesSubhypergraph_edgeSet]
        exact mem_iUnion₂.mpr ⟨c, ⟨⟨hc, hc_in.trans sdiff_subset⟩, hc⟩, hec⟩
      · refine ⟨c, hC'.symm ▸ mem_insert_of_mem c' ⟨hc, hc_out⟩, ?_⟩
        have hne : c ≠ c' := fun h => hc'_not_I₂ (h ▸ ⟨hc, hc_out⟩)
        dsimp only [cellG]
        rw [ite_eq_right hne]
        exact hec
    p1_disjoint := fun c₁ hc₁ c₂ hc₂ hne => by
      rw [hC'] at hc₁ hc₂
      dsimp only [cellG]
      split_ifs with h1 h2 h2
      · exact False.elim (hne (h1.trans h2.symm))
      · dsimp only [A, replacementDiscGraph]
        rw [addVerticesSubhypergraph_edgeSet]
        have hc₂' : c₂ ∈ I₂ := hc₂.resolve_left h2
        rw [Set.disjoint_left]
        intro e he₁ he₂
        rcases mem_iUnion₂.mp he₁ with ⟨c₀, hc₀, hec₀⟩
        have hc₀_ne : c₀ ≠ c₂ := fun h =>
          Set.disjoint_left.mp hdisj_I hc₀.1 (h ▸ hc₂')
        exact Set.disjoint_left.mp (π.p1_disjoint c₀ hc₀.2 c₂ hc₂'.1 hc₀_ne) hec₀ he₂
      · dsimp only [A, replacementDiscGraph]
        rw [addVerticesSubhypergraph_edgeSet]
        have hc₁' : c₁ ∈ I₂ := hc₁.resolve_left h1
        rw [Set.disjoint_left]
        intro e he₁ he₂
        rcases mem_iUnion₂.mp he₂ with ⟨c₀, hc₀, hec₀⟩
        have hc₁_ne : c₁ ≠ c₀ := fun h =>
          Set.disjoint_left.mp hdisj_I hc₀.1 (h ▸ hc₁')
        exact Set.disjoint_left.mp (π.p1_disjoint c₁ hc₁'.1 c₀ hc₀.2 hc₁_ne) he₁ hec₀
      · exact π.p1_disjoint c₁ (hc₁.resolve_left h1).1 c₂ (hc₂.resolve_left h2).1 hne
    p2 := fun c hc n hn => by
      rw [hC'] at hc
      dsimp only [cellG]
      split_ifs with hcc'
      · subst c
        rw [htilde_c'] at hn
        simp only [A, replacementDiscGraph, addVerticesSubhypergraph_vertexSet]
        exact Or.inr ⟨n, ⟨hn.1.1, hn.2.1⟩, rfl⟩
      · exact π.p2 c (hc.resolve_left hcc').1 n ⟨hn.1, hn.2.1⟩
    p3_notMem := fun n hn => π.p3_notMem n ⟨hn.1.1, hn.2⟩
    p3_subset := fun c hc hbd n hnt v hv => by
      rw [hC'] at hc
      have hne : c ≠ c' := fun h => hc'_not_bd (h ▸ hbd)
      dsimp only [cellG]
      rw [ite_eq_right hne]
      exact π.p3_subset c (hc.resolve_left hne).1 hbd n hnt hv
    p4_disjoint := fun Θ₁ hΘ₁ Θ₂ hΘ₂ hne n₁ hn₁ n₂ hn₂ =>
      π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne n₁ ⟨(hN'_sub hn₁.1).1, hn₁.2⟩ n₂ ⟨(hN'_sub hn₂.1).1, hn₂.2⟩
    p4_notMem := fun Θ hΘ n₁ hn₁ n₂ hn₂ hnot =>
      π.p4_notMem Θ hΘ n₁ ⟨(hN'_sub hn₁.1).1, hn₁.2⟩ n₂ hn₂.1 hnot
    p5 := fun c hc hint v hvc hex => by
      rcases hex with ⟨d', hd', hne, hvd'⟩
      by_cases hcc' : c = c'
      · subst c
        have hd'_ne : d' ≠ c' := hne
        have hd'_I₂ : d' ∈ I₂ := (hC' ▸ hd').resolve_left hd'_ne
        dsimp only [cellG] at hvc hvd'
        simp only [↓reduceIte] at hvc
        rw [ite_eq_right hd'_ne] at hvd'
        have hv₂ : v ∈ (π.cellsUnion I₂).vertexSet :=
          mem_iUnion₂.mpr ⟨d', ⟨hd'_I₂, hd'_I₂.1⟩, hvd'⟩
        rcases hA_inter_I₂ ⟨hvc, hv₂⟩ with ⟨n, ⟨hn_bd, hnγ⟩, rfl⟩
        have hn_tilde : n ∈ tilde c' := by
          rw [htilde_c']
          exact ⟨hn_bd, π.domγ_subset hnγ⟩
        exact ⟨n, ⟨hn_tilde, hnγ, htilde_sub_N' c' hc hn_tilde⟩, rfl⟩
      · have hc_I₂ : c ∈ I₂ := (hC' ▸ hc).resolve_left hcc'
        dsimp only [cellG] at hvc hvd'
        rw [ite_eq_right hcc'] at hvc
        have hv_or : (∃ d₀ ∈ π.Γ.C, d₀ ≠ c ∧ v ∈ (π.cellGraph d₀).vertexSet) ∨ v ∈ W_bd := by
          split_ifs at hvd' with hd'_eq
          · rcases hvd' with hvΔ | hvW
            · rcases mem_iUnion₂.mp hvΔ with ⟨c₀, hc₀, hvc₀⟩
              have hc₀_ne : c₀ ≠ c := fun h =>
                Set.disjoint_left.mp hdisj_I hc₀.1 (h ▸ hc_I₂)
              exact Or.inl ⟨c₀, hc₀.2, hc₀_ne, hvc₀⟩
            · exact Or.inr hvW
          · have hd'_I₂ : d' ∈ I₂ := (hC' ▸ hd').resolve_left hd'_eq
            exact Or.inl ⟨d', hd'_I₂.1, hne, hvd'⟩
        rcases hv_or with hv_o | ⟨n, ⟨hn_bd, hnγ⟩, rfl⟩
        · rcases π.p5 c hc_I₂.1 hint v hvc hv_o with ⟨n, ⟨hn_t, hnγ⟩, rfl⟩
          exact ⟨n, ⟨hn_t, hnγ, htilde_sub_N' c hc hn_t⟩, rfl⟩
        · obtain ⟨d₀, hd₀, hnd₀⟩ := hnode n ⟨hn_bd, hnγ⟩
          by_cases hd₀_c : d₀ = c
          · subst hd₀_c
            exact ⟨n, ⟨hnd₀, hnγ, htilde_sub_N' d₀ hc hnd₀⟩, rfl⟩
          · have hvd₀ := π.p2 d₀ hd₀ n ⟨hnd₀, hnγ⟩
            rcases π.p5 c hc_I₂.1 hint (π.nodeVertex n) hvc ⟨d₀, hd₀, hd₀_c, hvd₀⟩ with
              ⟨m, ⟨hm_t, hmγ⟩, hmv⟩
            exact ⟨m, ⟨hm_t, hmγ, htilde_sub_N' c hc hm_t⟩, hmv⟩
    p6 := fun c hc hbd v hvc hex => by
      rcases hex with ⟨d', hd', hne, hvd'⟩
      have hne_c' : c ≠ c' := fun h => hc'_not_bd (h ▸ hbd)
      have hc_I₂ : c ∈ I₂ := (hC' ▸ hc).resolve_left hne_c'
      dsimp only [cellG] at hvc hvd'
      rw [ite_eq_right hne_c'] at hvc
      have hv_or : (∃ d₀ ∈ π.Γ.C, d₀ ≠ c ∧ v ∈ (π.cellGraph d₀).vertexSet) ∨ v ∈ W_bd := by
        split_ifs at hvd' with hd'_eq
        · rcases hvd' with hvΔ | hvW
          · rcases mem_iUnion₂.mp hvΔ with ⟨c₀, hc₀, hvc₀⟩
            have hc₀_ne : c₀ ≠ c := fun h =>
              Set.disjoint_left.mp hdisj_I hc₀.1 (h ▸ hc_I₂)
            exact Or.inl ⟨c₀, hc₀.2, hc₀_ne, hvc₀⟩
          · exact Or.inr hvW
        · have hd'_I₂ : d' ∈ I₂ := (hC' ▸ hd').resolve_left hd'_eq
          exact Or.inl ⟨d', hd'_I₂.1, hne, hvd'⟩
      have hv_in : ∃ n ∈ tilde c, v ∈ π.borderSet n ∨ (n ∈ π.domγ ∧ v = π.nodeVertex n) := by
        rcases hv_or with hv_o | ⟨n, ⟨hn_bd, hnγ⟩, rfl⟩
        · exact π.p6 c hc_I₂.1 hbd v hvc hv_o
        · obtain ⟨d₀, hd₀, hnd₀⟩ := hnode n ⟨hn_bd, hnγ⟩
          by_cases hd₀_c : d₀ = c
          · subst hd₀_c
            exact ⟨n, hnd₀, Or.inr ⟨hnγ, rfl⟩⟩
          · have hvd₀ := π.p2 d₀ hd₀ n ⟨hnd₀, hnγ⟩
            exact π.p6 c hc_I₂.1 hbd (π.nodeVertex n) hvc ⟨d₀, hd₀, hd₀_c, hvd₀⟩
      rcases hv_in with ⟨n, hn_tilde, hvn_bs | ⟨hnγ, rfl⟩⟩
      · exact ⟨n, hn_tilde, Or.inl hvn_bs⟩
      · exact ⟨n, hn_tilde, Or.inr ⟨⟨hnγ, htilde_sub_N' c hc hn_tilde⟩, rfl⟩⟩
    p7 := fun Θ hΘ n₁ hn₁ n₂ hn₂ n₃ hn₃ n₄ hn₄ hord v hv₁ hv₃ => by
      have hv₁' : v ∈ π.borderPlus n₁ := by
        rcases hv₁ with h | ⟨h, rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨h.1, rfl⟩
      have hv₃' : v ∈ π.borderPlus n₃ := by
        rcases hv₃ with h | ⟨h, rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨h.1, rfl⟩
      rcases π.p7 Θ hΘ n₁ ⟨(hN'_sub hn₁.1).1, hn₁.2⟩ n₂ ⟨(hN'_sub hn₂.1).1, hn₂.2⟩
        n₃ ⟨(hN'_sub hn₃.1).1, hn₃.2⟩ n₄ ⟨(hN'_sub hn₄.1).1, hn₄.2⟩ hord v hv₁' hv₃' with
        (h2 | ⟨h2, rfl⟩) | (h4 | ⟨h4, rfl⟩)
      · exact Or.inl (Or.inl h2)
      · exact Or.inl (Or.inr ⟨⟨h2, hn₂.1⟩, rfl⟩)
      · exact Or.inr (Or.inl h4)
      · exact Or.inr (Or.inr ⟨⟨h4, hn₄.1⟩, rfl⟩) }

private theorem replaceDiscWarpAt
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G)
    (Δ : Set π.S)
    (hnode : ∀ n ∈ discBd Δ ∩ π.domγ, ∃ d ∈ π.Γ.C, n ∈ tilde d)
    (hdich : ∀ c ∈ π.Γ.C, c ⊆ Δ \ discBd Δ ∨ c ⊆ univ \ Δ)
    (Γ' : Painting π.S)
    (c' : Set π.S)
    (hC' : Γ'.C = insert c' (discOutsideCells π Δ))
    (hc'_mem : c' ∈ Γ'.C)
    (htilde_c' : tilde c' = discBd Δ ∩ π.Γ.N)
    (hc'_not_bd : ¬(c' ∩ bd π.S).Nonempty)
    (hc'_not_I₂ : c' ∉ (discOutsideCells π Δ))
    (hN'_sub : Γ'.N ⊆ π.Γ.N \ (Δ \ discBd Δ))
    (hN'_bd : Γ'.N ∩ bd π.S = π.Γ.N ∩ bd π.S)
    (hdisj_I : Disjoint (discInsideCells π Δ) (discOutsideCells π Δ))
    (hI₁_le : π.areaGraph Δ ≤ G)
    (hW_bd_sub : (discBorderVertices π Δ) ⊆ G.vertexSet)
    (hA_le : (replacementDiscGraph π Δ hI₁_le hW_bd_sub) ≤ G)
    (hA_inter_I₂ : (replacementDiscGraph π Δ hI₁_le hW_bd_sub).vertexSet ∩ (π.cellsUnion
      (discOutsideCells π Δ)).vertexSet ⊆ (discBorderVertices π Δ))
    (htilde_sub_N' : ∀ c ∈ Γ'.C, tilde c ⊆ Γ'.N)
    (hbd_cells : ∀ c ∈ π.Γ.C, (c ∩ bd π.S).Nonempty → c ⊆ univ \ Δ) :
  let π' := replaceDiscPortrayal π Δ hnode hdich Γ' c' hC' hc'_mem htilde_c' hc'_not_bd hc'_not_I₂
    hN'_sub hN'_bd hdisj_I hI₁_le hW_bd_sub hA_le hA_inter_I₂ htilde_sub_N'
  ∀ Θ ∈ cuffs π.S, π'.warpAt Θ = π.warpAt Θ := by
  classical
  intro π'
  let I₂ := discOutsideCells π Δ
  let A := replacementDiscGraph π Δ hI₁_le hW_bd_sub
  let cellG : Set π.S → Hypergraph α β := fun c =>
    if c = c' then A else π.cellGraph c
  have hborderPlus_eq : ∀ n ∈ π.Γ.N ∩ bd π.S, π'.borderPlus n = π.borderPlus n := by
    intro n hn
    have hn' : n ∈ Γ'.N := (hN'_bd.symm ▸ hn).1
    ext v
    simp only [Portrayal.borderPlus, π', replaceDiscPortrayal, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => h.elim Or.inl (fun ⟨⟨h1, _⟩, h2⟩ => Or.inr ⟨h1, h2⟩),
      fun h => h.elim Or.inl (fun ⟨h1, h2⟩ => Or.inr ⟨⟨h1, hn'⟩, h2⟩)⟩
  intro Θ hΘ
  have hΘ_sub : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x
  have hcell_iff : ∀ (c : Set π.S) (q : ℕ), c ∈ Γ'.C → (c ∩ Θ).Nonempty →
      (π'.CellWarpLE c q ↔ π.CellWarpLE c q) := by
    intro c q hc hne_Θ
    rw [hC'] at hc
    have hne_c' : c ≠ c' := fun h =>
      hc'_not_bd (h ▸ hne_Θ.mono (inter_subset_inter_right _ hΘ_sub))
    have hc_I₂ : c ∈ I₂ := hc.resolve_left hne_c'
    have hbd_c : (c ∩ bd π.S).Nonempty := hne_Θ.mono (inter_subset_inter_right _ hΘ_sub)
    have htilde_bd : tilde c ⊆ π.Γ.N ∩ bd π.S := by
      obtain ⟨u, w, _, htilde_uw, _, _, hu, hw⟩ := π.Γ.border_cell_exists_ends hc_I₂.1 hbd_c
      rw [htilde_uw]
      rintro x (rfl | rfl) <;> assumption
    change (∀ n₁ ∈ tilde c, ∀ n₂ ∈ tilde c, n₁ ≠ n₂ →
        (π.borderSet n₁).ncard ≤ q ∧ (π.borderSet n₂).ncard ≤ q ∧
        ((π'.borderPlus n₁).ncard = q + 1 → (π'.borderPlus n₂).ncard = q + 1 →
          Portrayal.LinkagePairs (cellG c).skeleton (π'.borderPlus n₁) (π'.borderPlus n₂)
            (q + 1) (π.nodeVertex n₁) (π.nodeVertex n₂))) ↔
      (∀ n₁ ∈ tilde c, ∀ n₂ ∈ tilde c, n₁ ≠ n₂ →
        (π.borderSet n₁).ncard ≤ q ∧ (π.borderSet n₂).ncard ≤ q ∧
        ((π.borderPlus n₁).ncard = q + 1 → (π.borderPlus n₂).ncard = q + 1 →
          Portrayal.LinkagePairs (π.cellGraph c).skeleton (π.borderPlus n₁) (π.borderPlus n₂)
            (q + 1) (π.nodeVertex n₁) (π.nodeVertex n₂)))
    have hcellG_c : cellG c = π.cellGraph c := ite_eq_right hne_c'
    rw [hcellG_c]
    constructor <;> intro h n₁ hn₁ n₂ hn₂ hne
    · obtain ⟨h1, h2, h3⟩ := h n₁ hn₁ n₂ hn₂ hne
      refine ⟨h1, h2, fun hb₁ hb₂ P hP => ?_⟩
      have hb₁' : (π'.borderPlus n₁).ncard = q + 1 := by
        rwa [hborderPlus_eq n₁ (htilde_bd hn₁)]
      have hb₂' : (π'.borderPlus n₂).ncard = q + 1 := by
        rwa [hborderPlus_eq n₂ (htilde_bd hn₂)]
      let P' : Fin (q + 1) →
          PathFromTo (π.cellGraph c).skeleton (π'.borderPlus n₁) (π'.borderPlus n₂) := fun i =>
        { first := (P i).first
          last := (P i).last
          walk := (P i).walk
          isPath := (P i).isPath
          first_mem := by rw [hborderPlus_eq n₁ (htilde_bd hn₁)]; exact (P i).first_mem
          last_mem := by rw [hborderPlus_eq n₂ (htilde_bd hn₂)]; exact (P i).last_mem }
      exact h3 hb₁' hb₂' P' hP
    · obtain ⟨h1, h2, h3⟩ := h n₁ hn₁ n₂ hn₂ hne
      refine ⟨h1, h2, fun hb₁' hb₂' P hP => ?_⟩
      have hb₁ : (π.borderPlus n₁).ncard = q + 1 := by
        rwa [← hborderPlus_eq n₁ (htilde_bd hn₁)]
      have hb₂ : (π.borderPlus n₂).ncard = q + 1 := by
        rwa [← hborderPlus_eq n₂ (htilde_bd hn₂)]
      let P' : Fin (q + 1) →
          PathFromTo (π.cellGraph c).skeleton (π.borderPlus n₁) (π.borderPlus n₂) := fun i =>
        { first := (P i).first
          last := (P i).last
          walk := (P i).walk
          isPath := (P i).isPath
          first_mem := by rw [← hborderPlus_eq n₁ (htilde_bd hn₁)]; exact (P i).first_mem
          last_mem := by rw [← hborderPlus_eq n₂ (htilde_bd hn₂)]; exact (P i).last_mem }
      exact h3 hb₁ hb₂ P' hP
  have hcellWarp_eq : ∀ c ∈ Γ'.C, (c ∩ Θ).Nonempty → π'.cellWarp c = π.cellWarp c := by
    intro c hc hne_Θ
    change sInf {q : ℕ | π'.CellWarpLE c q} = sInf {q : ℕ | π.CellWarpLE c q}
    congr 1
    ext q
    exact hcell_iff c q hc hne_Θ
  have hset_eq : {p : ℕ | ∃ c ∈ Γ'.C, (c ∩ Θ).Nonempty ∧ p = π'.cellWarp c} =
      {p : ℕ | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c} := by
    ext p
    constructor
    · rintro ⟨c, hc, hne_Θ, rfl⟩
      have hne_c' : c ≠ c' := fun h =>
        hc'_not_bd (h ▸ hne_Θ.mono (inter_subset_inter_right _ hΘ_sub))
      exact ⟨c, ((hC' ▸ hc).resolve_left hne_c').1, hne_Θ, hcellWarp_eq c hc hne_Θ⟩
    · rintro ⟨c, hc, hne_Θ, rfl⟩
      have hbd_c : (c ∩ bd π.S).Nonempty := hne_Θ.mono (inter_subset_inter_right c hΘ_sub)
      have hc' : c ∈ Γ'.C := hC'.symm ▸ mem_insert_of_mem c' ⟨hc, hbd_cells c hc hbd_c⟩
      exact ⟨c, hc', hne_Θ, (hcellWarp_eq c hc' hne_Θ).symm⟩
  change sSup {p : ℕ | ∃ c ∈ Γ'.C, (c ∩ Θ).Nonempty ∧ p = π'.cellWarp c} =
    sSup {p : ℕ | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c}
  rw [hset_eq]

private theorem replaceDiscTruth
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    (π : Portrayal G)
    (Δ : Set π.S)
    (hnode : ∀ n ∈ discBd Δ ∩ π.domγ, ∃ d ∈ π.Γ.C, n ∈ tilde d)
    (hdich : ∀ c ∈ π.Γ.C, c ⊆ Δ \ discBd Δ ∨ c ⊆ univ \ Δ)
    (Γ' : Painting π.S)
    (c' : Set π.S)
    (hC' : Γ'.C = insert c' (discOutsideCells π Δ))
    (hc'_mem : c' ∈ Γ'.C)
    (htilde_c' : tilde c' = discBd Δ ∩ π.Γ.N)
    (hc'_not_bd : ¬(c' ∩ bd π.S).Nonempty)
    (hc'_not_I₂ : c' ∉ (discOutsideCells π Δ))
    (hN'_sub : Γ'.N ⊆ π.Γ.N \ (Δ \ discBd Δ))
    (hN'_bd : Γ'.N ∩ bd π.S = π.Γ.N ∩ bd π.S)
    (hdisj_I : Disjoint (discInsideCells π Δ) (discOutsideCells π Δ))
    (hI₁_le : π.areaGraph Δ ≤ G)
    (hW_bd_sub : (discBorderVertices π Δ) ⊆ G.vertexSet)
    (hA_le : (replacementDiscGraph π Δ hI₁_le hW_bd_sub) ≤ G)
    (hA_inter_I₂ : (replacementDiscGraph π Δ hI₁_le hW_bd_sub).vertexSet ∩ (π.cellsUnion
      (discOutsideCells π Δ)).vertexSet ⊆ (discBorderVertices π Δ))
    (htilde_sub_N' : ∀ c ∈ Γ'.C, tilde c ⊆ Γ'.N)
    (hbd_sub : Δ ∩ bd π.S ⊆ discBd Δ)
    (hbd_cells : ∀ c ∈ π.Γ.C, (c ∩ bd π.S).Nonempty → c ⊆ univ \ Δ)
    (c₀ : Set π.S)
    (hc₀_C : c₀ ∈ π.Γ.C)
    (hc₀_Δ : c₀ ⊆ Δ)
    (hcard_le_c₀ : (discBd Δ ∩ π.Γ.N).ncard ≤ (tilde c₀).ncard) :
  let π' := replaceDiscPortrayal π Δ hnode hdich Γ' c' hC' hc'_mem htilde_c' hc'_not_bd hc'_not_I₂
    hN'_sub hN'_bd hdisj_I hI₁_le hW_bd_sub hA_le hA_inter_I₂ htilde_sub_N'
  π'.IsTruer π ∨ Δ ∩ π.Γ.N ⊆ discBd Δ ∧ ∃ c₀ ∈ π.Γ.C, (discInsideCells π Δ) = {c₀} := by
  classical
  intro π'
  let I₁ := discInsideCells π Δ
  let I₂ := discOutsideCells π Δ
  let A_set : ℕ → Set (Set π.S) := fun i => {c ∈ I₁ | (tilde c).ncard = 3 - i}
  let B_set : ℕ → Set (Set π.S) := fun i =>
    {c ∈ I₂ | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - i}
  have hA_fin : ∀ i, (A_set i).Finite := fun i =>
    π.Γ.finite_cells.subset fun _ h => h.1.1
  have hB_fin : ∀ i, (B_set i).Finite := fun i =>
    π.Γ.finite_cells.subset fun _ h => h.1.1
  have hdisj_AB : ∀ i, Disjoint (A_set i) (B_set i) := fun i =>
    hdisj_I.mono (fun _ h => h.1) (fun _ h => h.1)
  let t_old : ℕ → ℕ := fun n => (A_set n).ncard + (B_set n).ncard
  let t_new : ℕ → ℕ := fun n => (if (tilde c').ncard = 3 - n then 1 else 0) + (B_set n).ncard
  have hτ_old : ∀ n (hn4 : n < 4) (hn6 : n < 6), π.truth ⟨n, hn6⟩ = t_old n := by
    intro n hn4 hn6
    simp only [Portrayal.truth, hn4, ↓reduceIte, t_old]
    have hset_eq : {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - n} =
        A_set n ∪ B_set n := by
      ext c
      simp only [A_set, B_set, mem_ofPred_eq, mem_union]
      constructor
      · rintro ⟨hc, hint, hcard_c⟩
        rcases hdich c hc with hc_in | hc_out
        · exact Or.inl ⟨⟨hc, hc_in.trans sdiff_subset⟩, hcard_c⟩
        · exact Or.inr ⟨⟨hc, hc_out⟩, hint, hcard_c⟩
      · rintro (⟨hc₁, hcard_c⟩ | ⟨hc₂, hint, hcard_c⟩)
        · have hint : ¬ (c ∩ bd π.S).Nonempty := fun hbd =>
            Set.disjoint_left.mp hdisj_I hc₁ ⟨hc₁.1, hbd_cells c hc₁.1 hbd⟩
          exact ⟨hc₁.1, hint, hcard_c⟩
        · exact ⟨hc₂.1, hint, hcard_c⟩
    rw [hset_eq, ncard_union_eq (hdisj_AB n) (hA_fin n) (hB_fin n)]
  have hτ_new : ∀ n (hn4 : n < 4) (hn6 : n < 6), π'.truth ⟨n, hn6⟩ = t_new n := by
    intro n hn4 hn6
    simp only [Portrayal.truth, π', replaceDiscPortrayal, hn4, ↓reduceIte, t_new]
    split_ifs with hcard_c'
    · have hset_eq : {c ∈ Γ'.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - n} =
          insert c' (B_set n) := by
        ext c
        rw [mem_ofPred_eq, hC', mem_insert_iff, mem_insert_iff]
        constructor
        · rintro ⟨rfl | hc₂, hint, hcard_c⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hc₂, hint, hcard_c⟩
        · rintro (rfl | ⟨hc₂, hint, hcard_c⟩)
          · exact ⟨Or.inl rfl, hc'_not_bd, hcard_c'⟩
          · exact ⟨Or.inr hc₂, hint, hcard_c⟩
      have hc'_not_B : c' ∉ B_set n := fun h => hc'_not_I₂ h.1
      rw [hset_eq, ncard_insert_of_notMem hc'_not_B (hB_fin n), Nat.add_comm]
    · have hset_eq : {c ∈ Γ'.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - n} =
          B_set n := by
        ext c
        rw [mem_ofPred_eq, hC', mem_insert_iff]
        constructor
        · rintro ⟨rfl | hc₂, hint, hcard_c⟩
          · exact False.elim (hcard_c' hcard_c)
          · exact ⟨hc₂, hint, hcard_c⟩
        · rintro ⟨hc₂, hint, hcard_c⟩
          exact ⟨Or.inr hc₂, hint, hcard_c⟩
      rw [hset_eq, Nat.zero_add]
  have hc₀_le3 : (tilde c₀).ncard ≤ 3 := (π.Γ.cell_disc c₀ hc₀_C).2.2.2
  have hc'_le_c₀ : (tilde c').ncard ≤ (tilde c₀).ncard := by
    rwa [htilde_c']
  set k₀ : ℕ := 3 - (tilde c₀).ncard
  set k' : ℕ := 3 - (tilde c').ncard
  have hk₀_lt4 : k₀ < 4 := by omega
  have hk'_lt4 : k' < 4 := by omega
  have hk₀_le_k' : k₀ ≤ k' := by omega
  have hc₀_mem_Ak₀ : c₀ ∈ A_set k₀ := ⟨⟨hc₀_C, hc₀_Δ⟩, by omega⟩
  have hAk₀_pos : 1 ≤ (A_set k₀).ncard := by
    have hne : (A_set k₀).Nonempty := ⟨c₀, hc₀_mem_Ak₀⟩
    exact (ncard_pos (hA_fin k₀)).mpr hne
  by_cases hex_ne : ∃ n < 4, t_new n ≠ t_old n
  · left
    set m := Nat.find hex_ne
    have hm_spec : m < 4 ∧ t_new m ≠ t_old m := Nat.find_spec hex_ne
    obtain ⟨hm_lt4, hm_ne⟩ := hm_spec
    have hm_min : ∀ j < m, j < 4 → t_new j = t_old j := by
      intro j hj hj4
      by_contra hne
      exact Nat.find_min hex_ne hj ⟨hj4, hne⟩
    refine ⟨⟨m, by omega⟩, fun i hi => ?_, ?_⟩
    · have hi_lt_m : i.1 < m := hi
      have hi4 : i.1 < 4 := by omega
      rw [hτ_new i.1 hi4 i.2, hτ_old i.1 hi4 i.2]
      exact hm_min i.1 hi_lt_m hi4
    · rw [hτ_new m hm_lt4 (by omega), hτ_old m hm_lt4 (by omega)]
      dsimp only [t_new, t_old] at hm_ne ⊢
      split_ifs at hm_ne ⊢ with hcard_m
      · have hmk' : m = k' := by omega
        have hk₀_eq_m : k₀ = m := by
          by_contra hne_k₀
          have hk₀_lt_m : k₀ < m := by omega
          have heq_k₀ := hm_min k₀ hk₀_lt_m hk₀_lt4
          dsimp only [t_new, t_old] at heq_k₀
          have hnot_k₀ : (tilde c').ncard ≠ 3 - k₀ := by omega
          rw [ite_eq_right hnot_k₀] at heq_k₀
          omega
        have hAm_pos : 1 ≤ (A_set m).ncard := hk₀_eq_m ▸ hAk₀_pos
        have hBm : (B_set m).ncard = (B_set m).ncard := rfl
        omega
      · omega
  · push Not at hex_ne
    have hA_eq : ∀ n < 4,
        (A_set n).ncard = if (tilde c').ncard = 3 - n then 1 else 0 := by
      intro n hn4
      have heq := hex_ne n hn4
      dsimp only [t_new, t_old] at heq
      omega
    have hk₀_eq_k' : k₀ = k' := by
      by_contra hne
      have h1 := hA_eq k₀ hk₀_lt4
      have hnot : (tilde c').ncard ≠ 3 - k₀ := by omega
      rw [ite_eq_right hnot] at h1
      omega
    have hAk'_card : (A_set k').ncard = 1 := by
      have h1 := hA_eq k' hk'_lt4
      have hpos : (tilde c').ncard = 3 - k' := by omega
      rwa [ite_eq_left hpos] at h1
    have hI₁_eq_c₀ : I₁ = {c₀} := by
      refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨hc₀_C, hc₀_Δ⟩)
      intro c hc₁
      have hc_le3 : (tilde c).ncard ≤ 3 := (π.Γ.cell_disc c hc₁.1).2.2.2
      set kc : ℕ := 3 - (tilde c).ncard
      have hkc_lt4 : kc < 4 := by omega
      have hc_Akc : c ∈ A_set kc := ⟨hc₁, by omega⟩
      have hkc_eq_k' : kc = k' := by
        by_contra hne
        have h1 := hA_eq kc hkc_lt4
        have hnot : (tilde c').ncard ≠ 3 - kc := by omega
        rw [ite_eq_right hnot] at h1
        have hne_set : (A_set kc).Nonempty := ⟨c, hc_Akc⟩
        have hpos := (ncard_pos (hA_fin kc)).mpr hne_set
        omega
      have hc_Ak' : c ∈ A_set k' := hkc_eq_k' ▸ hc_Akc
      have hc₀_Ak' : c₀ ∈ A_set k' := hk₀_eq_k' ▸ hc₀_mem_Ak₀
      obtain ⟨d, hd⟩ := ncard_eq_one.mp hAk'_card
      rw [hd] at hc_Ak' hc₀_Ak'
      rw [mem_singleton_iff.mp hc_Ak', mem_singleton_iff.mp hc₀_Ak']
      exact mem_singleton d
    by_cases hne_N : ((Δ \ discBd Δ) ∩ π.Γ.N).Nonempty
    · left
      rcases hne_N with ⟨n₀, hn₀_open, hn₀_N⟩
      have hn₀_not_bd : n₀ ∉ bd π.S := fun h => hn₀_open.2 (hbd_sub ⟨hn₀_open.1, h⟩)
      have hn₀_not_N' : n₀ ∉ Γ'.N := fun h => (hN'_sub h).2 hn₀_open
      refine ⟨⟨4, by decide⟩, fun i hi => ?_, ?_⟩
      · have hi4 : i.1 < 4 := hi
        rw [hτ_new i.1 hi4 i.2, hτ_old i.1 hi4 i.2]
        exact hex_ne i.1 hi4
      · have hssub : Γ'.N \ bd π.S ⊂ π.Γ.N \ bd π.S :=
          ⟨sdiff_le_sdiff_right (hN'_sub.trans sdiff_subset),
            fun h => hn₀_not_N' (h ⟨hn₀_N, hn₀_not_bd⟩).1⟩
        simp only [Portrayal.truth, π', replaceDiscPortrayal]
        exact ncard_lt_ncard hssub (π.Γ.finite_N.subset sdiff_subset)
    · right
      refine ⟨?_, c₀, hc₀_C, hI₁_eq_c₀⟩
      rintro x ⟨hxΔ, hxN⟩
      by_contra hx_not_bd
      exact hne_N ⟨x, ⟨hxΔ, hx_not_bd⟩, hxN⟩

/-- The construction of (7.2) (`theorem_7_2_proof`), with what it does to the disc: the new cell
contains `V(α(Δ))` and the images of the nodes of `bd(Δ)`, `β` does not change, and `γ` is
restricted to the new nodes. -/
theorem theorem_7_2_cell {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 3 < θ) (π : Portrayal G) (hcentral : π.IsCentral 𝒯)
    {Δ : Set π.S} (hΔ : IsClosedDisc Δ)
    (hnorm : discBd Δ ∩ π.Γ.U ⊆ π.Γ.N)
    (hcard : (discBd Δ ∩ π.Γ.N).ncard ≤ 3)
    (hnode : ∀ n ∈ discBd Δ ∩ π.domγ, ∃ d ∈ π.Γ.C, n ∈ tilde d)
    (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ)) :
    ∃ π' : Portrayal G,
      π'.S = π.S ∧
      π'.IsCentral 𝒯 ∧
      π'.Resembles π ∧
      (∃ c ∈ π'.Γ.C, (π.areaGraph Δ).vertexSet ∪ π.nodeVertex '' (discBd Δ ∩ π.domγ) ⊆
        (π'.cellGraph c).vertexSet) ∧
      ((∀ n ∈ π.Γ.N ∩ bd π.S, Disjoint (π.borderSet n) (π.nodeVertex '' π.domγ)) →
        ∀ n ∈ π'.Γ.N ∩ bd π'.S, Disjoint (π'.borderSet n) (π'.nodeVertex '' π'.domγ)) ∧
      ((∃ c₀ ∈ π.Γ.C, c₀ ⊆ Δ ∧ (discBd Δ ∩ π.Γ.N).ncard ≤ (tilde c₀).ncard) →
        π'.IsTruer π ∨
        (Δ ∩ π.Γ.N ⊆ discBd Δ ∧ ∃ c₀ ∈ π.Γ.C, {c ∈ π.Γ.C | c ⊆ Δ} = {c₀})) := by
  classical
  have hS : IsSurface π.S := π.isSurface
  have : T2Space π.S := hS.2.1
  obtain ⟨hopen, hdisj_bd, hbd_sub, _, _⟩ := isOpen_and_disjoint_bd_of_isClosedDisc hS hΔ
  obtain ⟨hdich, hbd_cells, hN_bd_cl⟩ := normal_disc_cell_dichotomy hS π.Γ hΔ hnorm
  let Γ' : Painting π.S := π.Γ.replaceDisc hS Δ hΔ hnorm hcard
  let c' : Set π.S := Δ \ (discBd Δ ∩ π.Γ.N)
  set I₁ : Set (Set π.S) := {c ∈ π.Γ.C | c ⊆ Δ}
  set I₂ : Set (Set π.S) := {c ∈ π.Γ.C | c ⊆ Set.univ \ Δ}
  have hC' : Γ'.C = insert c' I₂ := π.Γ.replaceDisc_C hS Δ hΔ hnorm hcard
  have hc'_mem : c' ∈ Γ'.C := hC'.symm ▸ mem_insert c' I₂
  obtain ⟨hc'_ne, hc'_pc, hc'_cl⟩ :=
    isClosedDisc_sdiff_subset_discBd hΔ (inter_subset_left : discBd Δ ∩ π.Γ.N ⊆ discBd Δ)
  have htilde_c' : tilde c' = discBd Δ ∩ π.Γ.N := by
    change closure c' \ c' = _
    rw [hc'_cl]
    change Δ \ (Δ \ (discBd Δ ∩ π.Γ.N)) = _
    rw [Set.sdiff_sdiff_right_self, inter_eq_right.mpr (inter_subset_left.trans (discBd_subset Δ))]
  have hΔ_bd_sub : Δ ∩ bd π.S ⊆ discBd Δ ∩ π.Γ.N := fun x ⟨hxΔ, hxbd⟩ =>
    ⟨hbd_sub ⟨hxΔ, hxbd⟩, hnorm ⟨hbd_sub ⟨hxΔ, hxbd⟩, π.Γ.bd_subset hxbd⟩⟩
  have hc'_disj_bd : Disjoint c' (bd π.S) :=
    Set.disjoint_left.mpr fun x ⟨hxΔ, hxnot⟩ hxbd => hxnot (hΔ_bd_sub ⟨hxΔ, hxbd⟩)
  have hc'_not_bd : ¬ (c' ∩ bd π.S).Nonempty :=
    Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp hc'_disj_bd)
  have hc'_not_I₂ : c' ∉ I₂ := by
    rintro ⟨_, hc'_out⟩
    obtain ⟨x, hx⟩ := hc'_ne
    exact (hc'_out hx).2 hx.1
  have hN'_eq : Γ'.N = π.Γ.N ∩ closure (Set.univ \ Δ) := rfl
  have hN'_sub : Γ'.N ⊆ π.Γ.N \ (Δ \ discBd Δ) := by
    rintro x ⟨hxN, hxcl⟩
    refine ⟨hxN, fun hx_open => ?_⟩
    have hdisj : Disjoint (Δ \ discBd Δ) (Set.univ \ Δ) :=
      Set.disjoint_left.mpr fun y hy₁ hy₂ => hy₂.2 hy₁.1
    exact Set.disjoint_left.mp (hdisj.closure_right hopen) hx_open hxcl
  have hN'_bd : Γ'.N ∩ bd π.S = π.Γ.N ∩ bd π.S := by
    refine Subset.antisymm (inter_subset_inter_left _ inter_subset_left) ?_
    rintro x ⟨hxN, hxbd⟩
    refine ⟨⟨hxN, ?_⟩, hxbd⟩
    by_cases hxΔ : x ∈ Δ
    · exact hN_bd_cl (hΔ_bd_sub ⟨hxΔ, hxbd⟩)
    · exact subset_closure ⟨trivial, hxΔ⟩
  have hpart : I₁ ∪ I₂ = π.Γ.C := by
    refine Subset.antisymm (union_subset (fun _ h => h.1) (fun _ h => h.1)) fun c hc => ?_
    rcases hdich c hc with hc_in | hc_out
    · exact Or.inl ⟨hc, hc_in.trans sdiff_subset⟩
    · exact Or.inr ⟨hc, hc_out⟩
  have hdisj_I : Disjoint I₁ I₂ := by
    rw [Set.disjoint_left]
    intro c hc₁ hc₂
    obtain ⟨x, hx⟩ := π.Γ.cell_nonempty hc₁.1
    exact (hc₂.2 hx).2 (hc₁.2 hx)
  have hI₁_eq : π.areaGraph Δ = π.cellsUnion I₁ := rfl
  have hI₁_le : π.areaGraph Δ ≤ G := π.cellsUnion_le I₁
  let W_bd : Set α := π.nodeVertex '' (discBd Δ ∩ π.domγ)
  have hW_bd_sub : W_bd ⊆ G.vertexSet := by
    rintro _ ⟨n, ⟨_, hnγ⟩, rfl⟩
    exact π.nodeVertex_mem n hnγ
  have hW_bd_card : W_bd.ncard ≤ 3 := by
    have hsub : discBd Δ ∩ π.domγ ⊆ discBd Δ ∩ π.Γ.N :=
      inter_subset_inter_right _ π.domγ_subset
    have hfin : (discBd Δ ∩ π.domγ).Finite :=
      (π.Γ.finite_N.inter_of_right (discBd Δ)).subset hsub
    exact (ncard_image_le hfin).trans ((ncard_le_ncard hsub
      (π.Γ.finite_N.inter_of_right (discBd Δ))).trans hcard)
  have hinter_sub : (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion I₂).vertexSet ⊆ W_bd := by
    have hv_inter := theorem_2_1_claim_3 π hpart hdisj_I
    intro v hv
    rcases hv_inter hv with ⟨n, ⟨⟨hX₁, hX₂⟩, hdom⟩, rfl⟩ | hY
    · rw [mem_iUnion₂] at hX₁ hX₂
      rcases hX₁ with ⟨c₁, hc₁, hnc₁⟩
      rcases hX₂ with ⟨c₂, hc₂, hnc₂⟩
      have hnΔ : n ∈ Δ := closure_minimal hc₁.2 hΔ.isCompact.isClosed hnc₁.1
      have hcl := (closure_cell_inter_disc_of_subset_compl hS π.Γ hΔ hnorm hc₂.1 hc₂.2).2
      have hnbdΔ : n ∈ discBd Δ := by
        have : n ∈ closure c₂ ∩ Δ := ⟨hnc₂.1, hnΔ⟩
        rw [hcl] at this
        exact this.2
      exact ⟨n, ⟨hnbdΔ, hdom⟩, rfl⟩
    · exfalso
      rw [mem_iUnion₂] at hY
      rcases hY with ⟨n, ⟨hY₁, _⟩, _⟩
      rw [mem_iUnion₂] at hY₁
      rcases hY₁ with ⟨c₁, ⟨hc₁, hbd₁⟩, _⟩
      exact Set.disjoint_left.mp hdisj_I hc₁ ⟨hc₁.1, hbd_cells c₁ hc₁.1 hbd₁⟩
  let A : Hypergraph α β := addVerticesSubhypergraph G (π.areaGraph Δ) W_bd hI₁_le hW_bd_sub
  have hA_le : A ≤ G := addVerticesSubhypergraph_le hI₁_le hW_bd_sub
  have hA_inter_I₂ : A.vertexSet ∩ (π.cellsUnion I₂).vertexSet ⊆ W_bd := by
    rintro v ⟨hvΔ | hvW, hv₂⟩
    · exact hinter_sub ⟨hvΔ, hv₂⟩
    · exact hvW
  have hA_small : IsSmallWrt 𝒯 A := by
    have hdisc_small : IsSmallWrt 𝒯 (discreteSubhypergraph G W_bd hW_bd_sub) :=
      ⟨G, IsTangle.discrete_mem h𝒯 hW_bd_sub (by omega)⟩
    have hatt_sub : attachments G A ⊆ W_bd := by
      rintro v ⟨hvA, e, ⟨heG, he_notΔ⟩, hinc⟩
      rw [addVerticesSubhypergraph_edgeSet] at he_notΔ
      obtain ⟨c₂, hc₂, hec₂⟩ := π.p1_edge e heG
      have hc₂_I₂ : c₂ ∈ I₂ := by
        rcases hdich c₂ hc₂ with hc_in | hc_out
        · exact False.elim (he_notΔ (mem_iUnion₂.mpr ⟨c₂, ⟨⟨hc₂, hc_in.trans sdiff_subset⟩, hc₂⟩,
            hec₂⟩))
        · exact ⟨hc₂, hc_out⟩
      have hvc₂ : v ∈ (π.cellGraph c₂).vertexSet := by
        have hends := (π.cellGraph_le c₂ hc₂).3 e hec₂
        exact (π.cellGraph c₂).vertex_mem_of_inc
          (by change v ∈ (π.cellGraph c₂).ends e; rw [← hends]; exact hinc)
      exact hA_inter_I₂ ⟨hvA, mem_iUnion₂.mpr ⟨c₂, ⟨hc₂_I₂, hc₂⟩, hvc₂⟩⟩
    have hfin_W : W_bd.Finite := G.vertexSet_finite.subset hW_bd_sub
    have hatt_lt : (attachments G A).ncard < θ :=
      ((ncard_le_ncard hatt_sub hfin_W).trans hW_bd_card).trans_lt hθ
    exact hsmall.union h𝒯 hdisc_small hatt_lt
  have htilde_sub_N' : ∀ c ∈ Γ'.C, tilde c ⊆ Γ'.N := by
    intro c hc
    rw [hC'] at hc
    rcases hc with rfl | ⟨hc, hc_out⟩
    · rw [htilde_c']
      exact fun x hx => ⟨hx.2, hN_bd_cl hx⟩
    · have hcl_sub := (closure_cell_inter_disc_of_subset_compl hS π.Γ hΔ hnorm hc hc_out).1
      exact fun x hx => ⟨π.Γ.tilde_subset_N hc hx, hcl_sub hx.1⟩
  let cellG : Set π.S → Hypergraph α β := fun c =>
    if c = c' then A else π.cellGraph c
  let π' := replaceDiscPortrayal π Δ hnode hdich Γ' c' hC' hc'_mem htilde_c' hc'_not_bd hc'_not_I₂
    hN'_sub hN'_bd hdisj_I hI₁_le hW_bd_sub hA_le hA_inter_I₂ htilde_sub_N'
  have hcentral' : π'.IsCentral 𝒯 := by
    intro c hc
    rw [hC'] at hc
    change IsSmallWrt 𝒯 (cellG c)
    dsimp only [cellG]
    split_ifs with hcc'
    · exact hA_small
    · exact hcentral c (hc.resolve_left hcc').1
  have hwarp_eq :=
    replaceDiscWarpAt π Δ hnode hdich Γ' c' hC' hc'_mem htilde_c' hc'_not_bd hc'_not_I₂ hN'_sub
      hN'_bd hdisj_I hI₁_le hW_bd_sub hA_le hA_inter_I₂ htilde_sub_N' hbd_cells
  have hres : π'.Resembles π := by
    refine ⟨Homeomorph.refl π.S, fun Θ hΘ => ?_⟩
    have himg : (Homeomorph.refl π.S : π.S → π.S) '' Θ = Θ := image_id Θ
    rw [himg]
    exact hwarp_eq Θ hΘ
  refine ⟨π', rfl, hcentral', hres, ⟨c', hc'_mem, ?_⟩, ?_, fun ⟨c₀, hc₀_C, hc₀_Δ,
    hcard_le_c₀⟩ => ?_⟩
  · intro v hv
    have hA : cellG c' = A := ite_eq_left rfl
    change v ∈ (cellG c').vertexSet
    rw [hA]
    exact hv
  · rintro hd n ⟨hn, hnb⟩
    exact (hd n ⟨hN'_sub hn |>.1, hnb⟩).mono_right (image_mono inter_subset_left)
  exact replaceDiscTruth π Δ hnode hdich Γ' c' hC' hc'_mem htilde_c' hc'_not_bd hc'_not_I₂ hN'_sub
    hN'_bd hdisj_I hI₁_le hW_bd_sub hA_le hA_inter_I₂ htilde_sub_N' hbd_sub hbd_cells c₀ hc₀_C hc₀_Δ
    hcard_le_c₀

end Theorem72

/-! ## 4. Normal $1$-Arc Disc Replacement ((7.3) and (7.4), Pages 178–181) -/

section Theorem73And74

/-- **Graph Minors XVII, (7.2)** (page 178):
"Let $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ be a $\mathcal{T}$-central portrayal of a
hypergraph $G$. Let $\Delta \subseteq \Sigma$ be a disc, with $bd(\Delta)$ $\Gamma$-normal and
$|bd(\Delta) \cap N(\Gamma)| \le 3$, such that $\alpha(\Delta)$ is small. Define $\Gamma' =
(U(\Gamma) \cup \Delta, N(\Gamma) \cap \overline{\Sigma - \Delta})$; thus $c' = \Delta - (bd(\Delta)
\cap N(\Gamma))$ is a cell of $\Gamma'$. Let $A \subseteq G$ be minimal such that $\alpha(\Delta)
\subseteq A$ and $\gamma(N(\Gamma) \cap bd(\Delta)) \subseteq V(A)$. Define
$$ \begin{aligned} \alpha'(c') &= A \\ \alpha'(c) &= \alpha(c) \quad (c \in C(\Gamma') - \{c'\}) \\
\gamma' &= \gamma \mid N(\Gamma'). \end{aligned} $$
Then $\pi' = (\Sigma, \Gamma', \alpha', \beta, \gamma')$ is a $\mathcal{T}$-central portrayal of
$G$ resembling $\pi$."

Moreover, if there is a cell $c_0 \in C(\Gamma)$ with $c_0 \subseteq \Delta$ and
$|\operatorname{bd}(\Delta) \cap N(\Gamma)| \le |\tilde{c}_0|$ (and $\operatorname{ord}(\mathcal{T})
> 3$),
then either $\pi'$ is truer than $\pi$ (`π'.IsTruer π`), or
$\Delta \cap N(\Gamma) \subseteq \operatorname{bd}(\Delta)$ and $\{c \in C(\Gamma) \mid c \subseteq
\Delta\} = \{c_0\}$. -/
theorem theorem_7_2_proof {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 3 < θ) (π : Portrayal G) (hcentral : π.IsCentral 𝒯)
    {Δ : Set π.S} (hΔ : IsClosedDisc Δ)
    (hnorm : discBd Δ ∩ π.Γ.U ⊆ π.Γ.N)
    (hcard : (discBd Δ ∩ π.Γ.N).ncard ≤ 3)
    (hnode : ∀ n ∈ discBd Δ ∩ π.domγ, ∃ d ∈ π.Γ.C, n ∈ tilde d)
    (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ)) :
    ∃ π' : Portrayal G,
      π'.S = π.S ∧
      π'.IsCentral 𝒯 ∧
      π'.Resembles π ∧
      ((∃ c₀ ∈ π.Γ.C, c₀ ⊆ Δ ∧ (discBd Δ ∩ π.Γ.N).ncard ≤ (tilde c₀).ncard) →
        π'.IsTruer π ∨
        (Δ ∩ π.Γ.N ⊆ discBd Δ ∧ ∃ c₀ ∈ π.Γ.C, {c ∈ π.Γ.C | c ⊆ Δ} = {c₀})) := by
  obtain ⟨π', h1, h2, h3, -, -, h4⟩ := theorem_7_2_cell h𝒯 hθ π hcentral hΔ hnorm hcard hnode hsmall
  exact ⟨π', h1, h2, h3, h4⟩

/-- If $w$ is a path from $u$ to $v$ in $(H_1 \cup H_2).\text{skeleton}$ (where $H_1$ and $H_2$ are
edge-disjoint) such that no internal vertex $z \in w.\text{support} \setminus \{u, v\}$ belongs to
$V(H_1) \cap V(H_2)$, then $w$ lifts either to a walk in $H_1.\text{skeleton}$ or to a walk in
$H_2.\text{skeleton}$ with the same support. -/
theorem walk_in_left_or_right_of_internal_disjoint {α : Type u} {β : Type v}
    {H₁ H₂ : Hypergraph α β} (hdisjE : Disjoint H₁.edgeSet H₂.edgeSet) {u v : α}
    (w : (H₁ ∪ H₂).skeleton.Walk u v) (hp : w.IsPath)
    (hint : ∀ z ∈ w.support, z ≠ u → z ≠ v → z ∉ H₁.vertexSet ∩ H₂.vertexSet) :
    (∃ w₁ : H₁.skeleton.Walk u v, w₁.support = w.support) ∨
    (∃ w₂ : H₂.skeleton.Walk u v, w₂.support = w.support) := by
  have hstay : ∀ {K₁ K₂ : Hypergraph α β}, Disjoint K₁.edgeSet K₂.edgeSet →
      ∀ {a b : α} (p : (K₁ ∪ K₂).skeleton.Walk a b),
      p.IsPath → a ∈ K₁.vertexSet →
      (∀ z ∈ p.support, z ≠ b → z ∉ K₁.vertexSet ∩ K₂.vertexSet) →
      ∃ p₁ : K₁.skeleton.Walk a b, p₁.support = p.support := by
    intro K₁ K₂ hdisjK a b p hp_p ha₁ hno
    induction p with
    | nil => exact ⟨.nil, rfl⟩
    | @cons a c b hadj tail ih =>
      have hp_tail : tail.IsPath := hp_p.of_cons
      have ha_not_tail : a ∉ tail.support :=
        (SimpleGraph.Walk.cons_isPath_iff hadj tail).mp hp_p |>.2
      have ha_ne_b : a ≠ b := fun h => ha_not_tail (h ▸ tail.end_mem_support)
      have ha_not_K₂ : a ∉ K₂.vertexSet := fun ha₂ =>
        hno a (SimpleGraph.Walk.start_mem_support _) ha_ne_b ⟨ha₁, ha₂⟩
      rcases hadj with ⟨hne, e, hinc_a, hinc_c⟩
      have hinc_a₁ : K₁.Inc e a :=
        hinc_a.resolve_right fun h => ha_not_K₂ (K₂.vertex_mem_of_inc h)
      have he₁ : e ∈ K₁.edgeSet := K₁.edge_mem_of_inc hinc_a₁
      have hinc_c₁ : K₁.Inc e c :=
        hinc_c.resolve_right fun h =>
          Set.disjoint_left.mp hdisjK he₁ (K₂.edge_mem_of_inc h)
      have hc₁ : c ∈ K₁.vertexSet := K₁.vertex_mem_of_inc hinc_c₁
      have hno_tail : ∀ z ∈ tail.support, z ≠ b → z ∉ K₁.vertexSet ∩ K₂.vertexSet :=
        fun z hz => hno z (List.mem_cons_of_mem a hz)
      obtain ⟨tail₁, hsup⟩ := ih hp_tail hc₁ hno_tail
      have hadj₁ : K₁.skeleton.Adj a c := ⟨hne, e, hinc_a₁, hinc_c₁⟩
      refine ⟨.cons hadj₁ tail₁, ?_⟩
      dsimp [SimpleGraph.Walk.support]
      rw [hsup]
  cases w with
  | nil => exact Or.inl ⟨.nil, rfl⟩
  | @cons u c v hadj tail =>
    have hp_tail : tail.IsPath := hp.of_cons
    have hu_not_tail : u ∉ tail.support :=
      (SimpleGraph.Walk.cons_isPath_iff hadj tail).mp hp |>.2
    rcases hadj with ⟨hne, e, hinc_u, hinc_c⟩
    rcases hinc_u with hinc_u₁ | hinc_u₂
    · left
      have he₁ : e ∈ H₁.edgeSet := H₁.edge_mem_of_inc hinc_u₁
      have hinc_c₁ : H₁.Inc e c :=
        hinc_c.resolve_right fun h =>
          Set.disjoint_left.mp hdisjE he₁ (H₂.edge_mem_of_inc h)
      have hc₁ : c ∈ H₁.vertexSet := H₁.vertex_mem_of_inc hinc_c₁
      have hno_tail : ∀ z ∈ tail.support, z ≠ v → z ∉ H₁.vertexSet ∩ H₂.vertexSet :=
        fun z hz hzv => hint z (List.mem_cons_of_mem u hz) (fun hzu => hu_not_tail (hzu ▸ hz)) hzv
      obtain ⟨tail₁, hsup⟩ := hstay hdisjE tail hp_tail hc₁ hno_tail
      have hadj₁ : H₁.skeleton.Adj u c := ⟨hne, e, hinc_u₁, hinc_c₁⟩
      refine ⟨.cons hadj₁ tail₁, ?_⟩
      dsimp [SimpleGraph.Walk.support]
      rw [hsup]
    · right
      have he₂ : e ∈ H₂.edgeSet := H₂.edge_mem_of_inc hinc_u₂
      have hinc_c₂ : H₂.Inc e c :=
        hinc_c.resolve_left fun h =>
          Set.disjoint_left.mp hdisjE (H₁.edge_mem_of_inc h) he₂
      have hc₂ : c ∈ H₂.vertexSet := H₂.vertex_mem_of_inc hinc_c₂
      have hstay₂ : ∀ {a b : α} (p : (H₁ ∪ H₂).skeleton.Walk a b),
          p.IsPath → a ∈ H₂.vertexSet →
          (∀ z ∈ p.support, z ≠ b → z ∉ H₁.vertexSet ∩ H₂.vertexSet) →
          ∃ p₂ : H₂.skeleton.Walk a b, p₂.support = p.support := by
        intro a b p hp_p ha₂ hno
        induction p with
        | nil => exact ⟨.nil, rfl⟩
        | @cons a d b hadj' tail' ih =>
          have hp_tail' : tail'.IsPath := hp_p.of_cons
          have ha_not_tail' : a ∉ tail'.support :=
            (SimpleGraph.Walk.cons_isPath_iff hadj' tail').mp hp_p |>.2
          have ha_ne_b : a ≠ b := fun h => ha_not_tail' (h ▸ tail'.end_mem_support)
          have ha_not_H₁ : a ∉ H₁.vertexSet := fun ha₁ =>
            hno a (SimpleGraph.Walk.start_mem_support _) ha_ne_b ⟨ha₁, ha₂⟩
          rcases hadj' with ⟨hne', e', hinc_a, hinc_d⟩
          have hinc_a₂ : H₂.Inc e' a :=
            hinc_a.resolve_left fun h => ha_not_H₁ (H₁.vertex_mem_of_inc h)
          have he'₂ : e' ∈ H₂.edgeSet := H₂.edge_mem_of_inc hinc_a₂
          have hinc_d₂ : H₂.Inc e' d :=
            hinc_d.resolve_left fun h =>
              Set.disjoint_left.mp hdisjE (H₁.edge_mem_of_inc h) he'₂
          have hd₂ : d ∈ H₂.vertexSet := H₂.vertex_mem_of_inc hinc_d₂
          obtain ⟨tail₂, hsup⟩ := ih hp_tail' hd₂ (fun z hz => hno z (List.mem_cons_of_mem a hz))
          have hadj₂ : H₂.skeleton.Adj a d := ⟨hne', e', hinc_a₂, hinc_d₂⟩
          refine ⟨.cons hadj₂ tail₂, ?_⟩
          dsimp [SimpleGraph.Walk.support]
          rw [hsup]
      have hno_tail : ∀ z ∈ tail.support, z ≠ v → z ∉ H₁.vertexSet ∩ H₂.vertexSet :=
        fun z hz hzv => hint z (List.mem_cons_of_mem u hz) (fun hzu => hu_not_tail (hzu ▸ hz)) hzv
      obtain ⟨tail₂, hsup⟩ := hstay₂ tail hp_tail hc₂ hno_tail
      have hadj₂ : H₂.skeleton.Adj u c := ⟨hne, e, hinc_u₂, hinc_c₂⟩
      refine ⟨.cons hadj₂ tail₂, ?_⟩
      dsimp [SimpleGraph.Walk.support]
      rw [hsup]

/-- If $w : H.\text{skeleton}.\text{Walk } u\; v$ is a walk between distinct vertices $u \ne v$,
then both $u$ and $v$ belong to $H.\text{vertexSet}$. -/
theorem walk_endpoints_mem_vertexSet_of_ne {α : Type u} {β : Type v}
    {H : Hypergraph α β} {u v : α} (w : H.skeleton.Walk u v) (hne : u ≠ v) :
    u ∈ H.vertexSet ∧ v ∈ H.vertexSet := by
  have hstart : ∀ {a b : α} (p : H.skeleton.Walk a b), a ≠ b → a ∈ H.vertexSet := by
    intro a b p hab
    cases p with
    | nil => exact (hab rfl).elim
    | cons hadj _ =>
      rcases hadj with ⟨_, e, hinc, _⟩
      exact H.vertex_mem_of_inc hinc
  exact ⟨hstart w hne, hstart w.reverse hne.symm⟩

/-- If $H = H_1 \cup H_2$ is a union of two subhypergraphs of $G$, $u, v \in V(H_1)$, and
$w : (H_1 \cup H_2).\text{skeleton}.\text{Walk } u\; v$ is a simple path whose support contains at
most one vertex of $V(H_1) \cap V(H_2)$, then every vertex in $w.\text{support}$ belongs to
$V(H_1)$. -/
theorem walk_in_left_of_ncard_support_inter_le_one {α : Type u} {β : Type v}
    {G H₁ H₂ : Hypergraph α β} (hH₁ : H₁ ≤ G) (hH₂ : H₂ ≤ G)
    {u v : α} (hu : u ∈ H₁.vertexSet) (hv : v ∈ H₁.vertexSet)
    (w : (H₁ ∪ H₂).skeleton.Walk u v) (hp : w.IsPath)
    (hcard : ({z ∈ w.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet}).ncard ≤ 1) :
    ∀ z ∈ w.support, z ∈ H₁.vertexSet := by
  classical
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨z, hz_sup, hz_not₁⟩
  obtain ⟨w₁, w₂, hw_eq⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hz_sup
  have hex_cut : ∀ {a b : α} (p : (H₁ ∪ H₂).skeleton.Walk a b),
      a ∈ H₁.vertexSet → b ∉ H₁.vertexSet →
      ∃ x ∈ p.support, x ≠ b ∧ x ∈ H₁.vertexSet ∩ H₂.vertexSet := by
    intro a b p
    induction p with
    | nil => intro ha hb; exact False.elim (hb ha)
    | @cons x y c hadj p ih =>
      intro hx hc
      by_cases hy : y ∈ H₁.vertexSet
      · obtain ⟨w₀, hw₀_sup, hw₀_ne, hw₀_mem⟩ := ih hy hc
        exact ⟨w₀, List.mem_cons_of_mem x hw₀_sup, hw₀_ne, hw₀_mem⟩
      · refine ⟨x, SimpleGraph.Walk.start_mem_support _, fun h => hc (h ▸ hx), hx, ?_⟩
        rcases hadj with ⟨_, e, hincx, hincy⟩
        rcases hincy with hincy₁ | hincy₂
        · exact False.elim (hy (H₁.vertex_mem_of_inc hincy₁))
        · rcases hincx with hincx₁ | hincx₂
          · have he₂ : e ∈ H₂.edgeSet := H₂.edge_mem_of_inc hincy₂
            have hincxG : G.Inc e x := (inc_iff_of_le hH₁ (H₁.edge_mem_of_inc hincx₁)).mp hincx₁
            have hincx₂ : H₂.Inc e x := (inc_iff_of_le hH₂ he₂).mpr hincxG
            exact H₂.vertex_mem_of_inc hincx₂
          · exact H₂.vertex_mem_of_inc hincx₂
  obtain ⟨x₁, hx₁_sup, _, hx₁_inter⟩ := hex_cut w₁ hu hz_not₁
  obtain ⟨x₂, hx₂_sup, hx₂_ne_z, hx₂_inter⟩ := hex_cut w₂.reverse hv hz_not₁
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx₂_sup
  have hx₁_w : x₁ ∈ w.support :=
    hw_eq ▸ SimpleGraph.Walk.support_subset_support_append_left w₁ w₂ hx₁_sup
  have hx₂_w : x₂ ∈ w.support :=
    hw_eq ▸ SimpleGraph.Walk.support_subset_support_append_right w₁ w₂ hx₂_sup
  have hx₁_eq_x₂ : x₁ = x₂ := by
    by_contra hne
    have hpair : ({x₁, x₂} : Set α) ⊆ {y ∈ w.support | y ∈ H₁.vertexSet ∩ H₂.vertexSet} := by
      rintro y (rfl | rfl)
      · exact ⟨hx₁_w, hx₁_inter⟩
      · exact ⟨hx₂_w, hx₂_inter⟩
    have hfin : ({y ∈ w.support | y ∈ H₁.vertexSet ∩ H₂.vertexSet}).Finite :=
      H₁.vertexSet_finite.subset fun _ hy => hy.2.1
    have h2 : 2 ≤ ({y ∈ w.support | y ∈ H₁.vertexSet ∩ H₂.vertexSet}).ncard := by
      rw [← ncard_pair hne]
      exact ncard_le_ncard hpair hfin
    omega
  rw [← hx₁_eq_x₂] at hx₂_sup
  have hnodup := hw_eq ▸ hp.support_nodup
  rw [SimpleGraph.Walk.support_append] at hnodup
  have hdisj := List.nodup_append.mp hnodup
  cases w₂ with
  | nil => exact hx₂_ne_z (hx₁_eq_x₂.symm.trans (List.mem_singleton.mp hx₂_sup))
  | cons hadj p' =>
    have hx₁_in_tail : x₁ ∈ p'.support := by
      rcases List.mem_cons.mp hx₂_sup with rfl | htail
      · exact False.elim (hx₂_ne_z hx₁_eq_x₂.symm)
      · exact htail
    exact hdisj.2.2 x₁ hx₁_sup x₁ hx₁_in_tail rfl

/-- Given a path `P : PathFromTo K B₁ B₂`, there exists a minimal subpath `Q : PathFromTo K B₁ B₂`
whose vertex support is a subset of `P.walk.support` such that no internal vertex of `Q` belongs to
`B₁ ∪ B₂`, and if `Q.first ≠ Q.last`, no vertex of `Q` belongs to `B₁ ∩ B₂`. -/
theorem exists_minimal_subpath_from_to {α : Type u} {K : SimpleGraph α} {B₁ B₂ : Set α}
    (P : PathFromTo K B₁ B₂) :
    ∃ Q : PathFromTo K B₁ B₂,
      {z | z ∈ Q.walk.support} ⊆ {z | z ∈ P.walk.support} ∧
      (∀ z ∈ Q.walk.support, z ≠ Q.first → z ≠ Q.last → z ∉ B₁ ∪ B₂) ∧
      (Q.first ≠ Q.last → ∀ z ∈ Q.walk.support, z ∉ B₁ ∩ B₂) := by
  suffices hmain : ∀ n : ℕ, ∀ {u v : α} (w : K.Walk u v), w.length ≤ n →
      w.IsPath → u ∈ B₁ → v ∈ B₂ →
      ∃ Q : PathFromTo K B₁ B₂,
        {z | z ∈ Q.walk.support} ⊆ {z | z ∈ w.support} ∧
        (∀ z ∈ Q.walk.support, z ≠ Q.first → z ≠ Q.last → z ∉ B₁ ∪ B₂) ∧
        (Q.first ≠ Q.last → ∀ z ∈ Q.walk.support, z ∉ B₁ ∩ B₂) by
    exact hmain P.walk.length P.walk le_rfl P.isPath P.first_mem P.last_mem
  intro n
  induction n with
  | zero =>
    intro u v w hlen hp hu hv
    cases w with
    | nil =>
      refine ⟨⟨u, u, .nil, SimpleGraph.Walk.IsPath.nil, hu, hv⟩, subset_rfl, ?_, ?_⟩
      · intro z hz hne _
        exact (hne (List.mem_singleton.mp hz)).elim
      · intro hne; exact (hne rfl).elim
    | cons _ _ => simp [SimpleGraph.Walk.length_cons] at hlen
  | succ n ih =>
    intro u v w hlen hp hu hv
    by_cases hex : ∃ z ∈ w.support, z ≠ u ∧ z ≠ v ∧ z ∈ B₁ ∪ B₂
    · obtain ⟨z, hz_sup, hzu, hzv, hzB⟩ := hex
      obtain ⟨w₁, w₂, hp₁, hp₂, hw_eq⟩ := hp.mem_support_iff_exists_append.mp hz_sup
      have hw₁_pos : 1 ≤ w₁.length := by
        cases w₁ with
        | nil => exact (hzu rfl).elim
        | cons _ _ => simp [SimpleGraph.Walk.length_cons]
      have hw₂_pos : 1 ≤ w₂.length := by
        cases w₂ with
        | nil => exact (hzv rfl).elim
        | cons _ _ => simp [SimpleGraph.Walk.length_cons]
      have hlen_eq : w.length = w₁.length + w₂.length := by
        rw [hw_eq, SimpleGraph.Walk.length_append]
      rcases hzB with hzB₁ | hzB₂
      · obtain ⟨Q, hQ_sub, hQ_int, hQ_inter⟩ := ih w₂ (by omega) hp₂ hzB₁ hv
        refine ⟨Q, hQ_sub.trans ?_, hQ_int, hQ_inter⟩
        intro x hx
        exact hw_eq ▸ SimpleGraph.Walk.support_subset_support_append_right w₁ w₂ hx
      · obtain ⟨Q, hQ_sub, hQ_int, hQ_inter⟩ := ih w₁ (by omega) hp₁ hu hzB₂
        refine ⟨Q, hQ_sub.trans ?_, hQ_int, hQ_inter⟩
        intro x hx
        exact hw_eq ▸ SimpleGraph.Walk.support_subset_support_append_left w₁ w₂ hx
    · push Not at hex
      by_cases hu₂ : u ∈ B₂
      · refine ⟨⟨u, u, .nil, SimpleGraph.Walk.IsPath.nil, hu, hu₂⟩, ?_, ?_, ?_⟩
        · intro x hx
          exact (List.mem_singleton.mp hx) ▸ SimpleGraph.Walk.start_mem_support w
        · intro z hz hne _
          exact (hne (List.mem_singleton.mp hz)).elim
        · intro hne; exact (hne rfl).elim
      · by_cases hv₁ : v ∈ B₁
        · refine ⟨⟨v, v, .nil, SimpleGraph.Walk.IsPath.nil, hv₁, hv⟩, ?_, ?_, ?_⟩
          · intro x hx
            exact (List.mem_singleton.mp hx) ▸ SimpleGraph.Walk.end_mem_support w
          · intro z hz hne _
            exact (hne (List.mem_singleton.mp hz)).elim
          · intro hne; exact (hne rfl).elim
        · refine ⟨⟨u, v, w, hp, hu, hv⟩, subset_rfl, hex, ?_⟩
          intro _ z hz ⟨hz₁, hz₂⟩
          by_cases hzu : z = u
          · exact hu₂ (hzu ▸ hz₂)
          · by_cases hzv : z = v
            · exact hv₁ (hzv ▸ hz₁)
            · exact hex z hz hzu hzv (Or.inl hz₁)

/-- Pure surface-and-painting topological region-separation statement for the proof of (7.3)
(Graph Minors XVII, page 179):
given a painting $\Gamma$ in a surface $\Sigma$, a cuff $\Theta$ of $\Sigma$, distinct nodes
$n_1, n_2 \in N(\Gamma) \cap \Theta$, a $\Gamma$-normal $I$-arc $F \subseteq \Sigma$ with ends
$n_1, n_2$ and $F \cap N(\Gamma) = \{n_1, n_2\}$, a closed disc $\Delta \subseteq \Sigma$ with
$F \subseteq \operatorname{bd}(\Delta) \subseteq F \cup \Theta$, an assignment $e(c'') \subseteq
\tilde{c}''$ of size $0$, $2$, or $3$ for each internal cell $c'' \subseteq \Delta$ (representing
the drawing $H$ of $M \cap \Delta$ in $\Delta$), and a marking predicate $P_{\text{mark}}$ on nodes
that holds at $n_1$, fails at $n_2$, and is constant on each $e(c'')$:
letting $R$ be the region of $H$ in $\Delta$ whose closure includes $F$ and $m_1, \dots, m_k$ be
the nodes of $N(\Gamma) \cap I$ ($I = \Theta \cap \operatorname{bd}(\Delta)$) in $\bar{R}$ in order
along $I$, choosing $i$ maximum with $P_{\text{mark}}(m_i)$ gives consecutive nodes
$m_i, m_{i+1} \in N(\Gamma) \cap I$ and a border cell $c \subseteq \Delta$ with
$\tilde{c} = \{m_i, m_{i+1}\}$ whose boundary segment $S = \bar{c} \cap I$ splits $I$ into $I_1$
(between $n_1$ and $m_i$) and $I_2$ (between $m_{i+1}$ and $n_2$) and separates the components of
$H$ in $\Delta$. -/
@[expose] def NormalIArcDiscRegionStatement : Prop :=
  ∀ (S : Type) [TopologicalSpace S], IsSurface S →
    ∀ (Γ : Painting S) (Θ : Set S) (n₁ n₂ : S) (F Δ : Set S)
      (e : Set S → Set S) (P_mark : S → Prop),
      Θ ∈ cuffs S → n₁ ∈ Γ.N ∩ Θ → n₂ ∈ Γ.N ∩ Θ → n₁ ≠ n₂ →
      Γ.IsNormal F → IsLineWithEnds F n₁ n₂ → F ∩ bd S = {n₁, n₂} → F ∩ Γ.N = {n₁, n₂} →
      IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ Θ →
      (∀ d ∈ Γ.C, d ⊆ Δ → ¬ (d ∩ bd S).Nonempty →
        e d ⊆ tilde d ∧ (e d = ∅ ∨ 2 ≤ (e d).ncard) ∧
        ∀ x ∈ e d, ∀ y ∈ e d, P_mark x → P_mark y) →
      P_mark n₁ → ¬ P_mark n₂ →
      ∃ (m₁ m₂ : S) (c I₁ I₂ N₁ N₂ : Set S),
        m₁ ∈ Γ.N ∩ (Θ ∩ discBd Δ) ∧ m₂ ∈ Γ.N ∩ (Θ ∩ discBd Δ) ∧ m₁ ≠ m₂ ∧
        P_mark m₁ ∧ ¬ P_mark m₂ ∧
        c ∈ Γ.C ∧ c ⊆ Δ ∧ (c ∩ Θ).Nonempty ∧ tilde c = {m₁, m₂} ∧
        I₁ ⊆ Θ ∩ discBd Δ ∧ I₂ ⊆ Θ ∩ discBd Δ ∧ Disjoint I₁ I₂ ∧
        n₁ ∈ I₁ ∧ m₁ ∈ I₁ ∧ m₂ ∈ I₂ ∧ n₂ ∈ I₂ ∧
        N₁ ⊆ (Γ.N ∩ Δ) \ bd S ∧ N₂ ⊆ (Γ.N ∩ Δ) \ bd S ∧ Disjoint N₁ N₂ ∧
        (∀ n ∈ I₁ ∩ Γ.N, ∀ n' ∈ I₂ ∩ Γ.N,
          (n ≠ n₁ → n ≠ m₁ → GM19.InOrderOn Θ n₁ n m₁ n') ∧
          (m₁ ≠ n₁ → n' ≠ n₂ → GM19.InOrderOn Θ n₁ m₁ n' n₂) ∧
          (n' ≠ m₂ → n' ≠ n₂ → GM19.InOrderOn Θ n m₂ n' n₂) ∧
          (n ≠ n₁ → m₂ ≠ n₂ → GM19.InOrderOn Θ n₁ n m₂ n₂)) ∧
        (∀ d ∈ Γ.C, d ⊆ Δ → (d ∩ bd S).Nonempty → d ≠ c →
          tilde d ⊆ I₁ ∨ tilde d ⊆ I₂) ∧
        (∀ d ∈ Γ.C, d ⊆ Δ → ¬ (d ∩ bd S).Nonempty →
          e d ⊆ N₁ ∪ I₁ ∨ e d ⊆ N₂ ∪ I₂) ∧
        (∃ c₁ ∈ Γ.C, c₁ ⊆ Δ ∧ (c₁ ∩ bd S).Nonempty ∧ n₁ ∈ tilde c₁) ∧
        (∃ c₂ ∈ Γ.C, c₂ ⊆ Δ ∧ (c₂ ∩ bd S).Nonempty ∧ n₂ ∈ tilde c₂)

/-- Topological statement for Graph Minors XVII, (7.4) (pages 180–181):
Given a painting $\Gamma$ on a surface $S$, a $\Gamma$-normal $1$-arc $F$ with ends
$n_1, n_2 \in \operatorname{bd}(S)$ and $F \cap \Gamma.N = \{n_1, n_2\}$, and a closed disc
$\Delta \subseteq S$ with $F \subseteq \operatorname{bd}(\Delta) \subseteq F \cup
\operatorname{bd}(S)$,
replacing the interior of $\Delta$ by a single border cell $c' = \Delta \setminus \{n_1, n_2\}$
gives a painting $\Gamma'$ on $S$ with $U(\Gamma') = U(\Gamma) \cup \Delta$,
$N(\Gamma') = N(\Gamma) \cap \overline{S \setminus \Delta} = (N(\Gamma) \setminus \Delta) \cup
\{n_1, n_2\}$,
and $C(\Gamma') = \{c'\} \cup \{c \in C(\Gamma) \mid c \subseteq S \setminus \Delta\}$. -/
@[expose] def NormalIArcReplaceDiscPaintingStatement : Prop :=
  ∀ (S : Type) [TopologicalSpace S], IsSurface S →
    ∀ (Γ : Painting S) (n₁ n₂ : S) (F Δ : Set S),
      Γ.IsNormal F → IsLineWithEnds F n₁ n₂ →
      F ∩ bd S = {n₁, n₂} → F ∩ Γ.N = {n₁, n₂} →
      IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S →
      ∃ (Γ' : Painting S) (Θ F'' : Set S),
        let c' := Δ \ {n₁, n₂}
        let F' := discBd Δ ∩ Θ
        Γ'.U = Γ.U ∪ Δ ∧
        Γ'.N = Γ.N ∩ closure (Δᶜ) ∧
        Γ'.N = (Γ.N \ Δ) ∪ {n₁, n₂} ∧
        Θ ∈ cuffs S ∧
        n₁ ∈ Γ.N ∩ Θ ∧ n₂ ∈ Γ.N ∩ Θ ∧
        discBd Δ ⊆ F ∪ Θ ∧
        Δ ∩ bd S = F' ∧
        IsLineWithEnds F' n₁ n₂ ∧
        F'' ⊆ Θ ∧ IsLineWithEnds F'' n₁ n₂ ∧
        F' ∪ F'' = Θ ∧ F' ∩ F'' = {n₁, n₂} ∧
        (∀ c ∈ Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ) ∧
        (∀ c ∈ Γ.C, c ⊆ Δᶜ → tilde c ⊆ Γ'.N) ∧
        c' ∈ Γ'.C ∧ (c' ∩ Θ).Nonempty ∧ tilde c' = {n₁, n₂} ∧
        Γ'.C = insert c' {c ∈ Γ.C | c ⊆ Δᶜ} ∧
        c' ∉ {c ∈ Γ.C | c ⊆ Δᶜ} ∧
        (∃ c₁ ∈ Γ.C, c₁ ⊆ Δ ∧ (c₁ ∩ bd S).Nonempty ∧ n₁ ∈ tilde c₁) ∧
        (∃ c₂ ∈ Γ.C, c₂ ⊆ Δ ∧ (c₂ ∩ bd S).Nonempty ∧ n₂ ∈ tilde c₂)

end Theorem73And74

end GraphMinor.GM17
