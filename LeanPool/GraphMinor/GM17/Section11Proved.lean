/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section11
import LeanPool.GraphMinor.GM17.Section5Proved
import LeanPool.GraphMinor.GM17.Section6Proved
import LeanPool.GraphMinor.GM17.Section7Proved
import LeanPool.GraphMinor.GM17.Section8Proved
import LeanPool.GraphMinor.GM17.Section9Proved
import LeanPool.GraphMinor.GM17.Section9bProved
import LeanPool.GraphMinor.GM17.Section10Proved

public import LeanPool.GraphMinor.GM17.Section10
import LeanPool.GraphMinor.GM17.PasteCuff
import LeanPool.GraphMinor.GM17.ArcDisc
import LeanPool.GraphMinor.GM17.MarkCross
import LeanPool.GraphMinor.GM17.ReplaceDisc
import LeanPool.GraphMinor.GM17.RegionDisc
import LeanPool.GraphMinor.GM17.CutArcPaint
import LeanPool.GraphMinor.GM17.PushNode

import LeanPool.GraphMinor.GM17.CellPartitionMain

import LeanPool.GraphMinor.GM17.IndentMain

import LeanPool.GraphMinor.GM17.RegionBoundary

import LeanPool.GraphMinor.GM17.ThreeNodeReplace
import LeanPool.GraphMinor.GM17.CellLinkage

/-!
# Graph Minors XVII: proved deductions of Section11

The portrayal deductions use the existing painting proofs. The definitions and
independent geometric lemmas are imported from `Section11`.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Function Topology Metric
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Basic Lemmas on `tildeOfCells` and `gammaOfCells` -/

/-- **Graph Minors XVII, (11.1)** (page 189):
"Let $I, J$ be a partition of $C(\Gamma)$ with $\gamma(I), \gamma(J) \ne N(\Gamma)$ and
$|\gamma(I) \cap \gamma(J)| \le 3$. Then $|\gamma(I) \cap \gamma(J)| = 3$ and there is a
disc $\Delta \subseteq \Sigma$ such that* (i) *$\{c \in C(\Gamma) \colon c \subseteq
\Delta\}$ is one of $I, J$,* (ii) *$\alpha(\Delta)$ is small, and* (iii) *either
$\operatorname{bd}(\Delta)$ is a $\Gamma$-normal $O$-arc in $\Sigma$ and $N(\Gamma) \cap
\operatorname{bd}(\Delta) = \gamma(I) \cap \gamma(J)$, or $F \subseteq
\operatorname{bd}(\Delta) \subseteq F \cup \operatorname{bd}(\Sigma)$ and $N(\Gamma) \cap F
= \gamma(I) \cap \gamma(J)$ for some $\Gamma$-normal $I$-arc $F$." -/
theorem theorem_11_1_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 4))
    (hwarp : π.warp ≤ p)
    (hθ : 6 * p + 8 < θ)
    {I J : Set (Set π.S)}
    (hcov : I ∪ J = π.Γ.C) (hdisj : Disjoint I J)
    (hI_ne : π.Γ.tildeOfCells I ≠ π.Γ.N)
    (hJ_ne : π.Γ.tildeOfCells J ≠ π.Γ.N)
    (hcard_le : (π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J).ncard ≤ 3) :
    (π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J).ncard = 3 ∧
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧
      ({c ∈ π.Γ.C | c ⊆ Δ} = I ∨ {c ∈ π.Γ.C | c ⊆ Δ} = J) ∧
      IsSmallWrt 𝒯 (π.areaGraph Δ) ∧
      ((IsOArc (discBd Δ) ∧ π.Γ.IsNormal (discBd Δ) ∧
          π.Γ.N ∩ discBd Δ = π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J) ∨
       (∃ F : Set π.S, ∃ n₁ n₂ : π.S,
          IsLineWithEnds F n₁ n₂ ∧ π.Γ.IsNormal F ∧ F ∩ bd π.S = {n₁, n₂} ∧
          F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧
          π.Γ.N ∩ F = π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J)) := by
  have : ConnectedSpace π.S := π.connected
  have hp_pos : 1 ≤ p := π.one_le_warp.trans hwarp
  have hred3 : π.IsRedundant 𝒯 θ (2 * p + 3) := hred.mono (by omega)
  have hθ3 : 4 * p + 5 < θ := by omega
  obtain ⟨h82_oarc, h82_card, h82_node⟩ :=
    theorem_8_2_proof
      h𝒯 π htrue hred3 hwarp hθ3
  have hreg : ∀ R ∈ π.Γ.regions, IsOpenDisc R ∧ IsOArc (closure R \ R) :=
    fun R hR => ⟨theorem_8_1_proof
      h𝒯 π htrue hred3 hwarp hθ3 hR, h82_oarc R hR⟩
  have h83 : ∀ F : Set π.S, IsLine F → π.Γ.IsNormal F → F ∩ bd π.S = lineEnds F →
      (F ∩ π.Γ.N).ncard = 2 →
      ∃ Δ : Set π.S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧
        Δ ∩ π.Γ.N ⊆ F ∧ {c ∈ π.Γ.C | c ⊆ Δ}.ncard = 1 :=
    fun _ hL hnorm hFbd hcard =>
      theorem_8_3_proof h𝒯 π htrue hred3 hwarp hθ3 hL hnorm hFbd hcard
  have h85_two : ∀ F : Set π.S, IsOArc F → π.Γ.IsNormal F → (F ∩ π.Γ.N).ncard = 2 →
      ∃ Δ : Set π.S, IsClosedDisc Δ ∧ discBd Δ = F ∧
        Δ ∩ π.Γ.N ⊆ F ∧ {c ∈ π.Γ.C | c ⊆ Δ}.ncard ≤ 1 := by
    intro F hO hnorm hcard2
    obtain ⟨Δ, hΔ, hbd, _, hcases⟩ :=
      theorem_8_5_proof
        h𝒯 π htrue hred3 hwarp hθ3 hO hnorm (by omega)
    rcases hcases with ⟨hΔ_N, hΔ_c⟩ | ⟨hcard3, _⟩
    · exact ⟨Δ, hΔ, hbd, hΔ_N, hΔ_c⟩
    · omega
  obtain ⟨hcard_eq3, hcases⟩ :=
    GraphMinor.GM17.cellPartitionPainting π.S π.isSurface π.Γ hreg h82_card h82_node h83 h85_two I J
      hcov hdisj hI_ne hJ_ne hcard_le
  refine ⟨hcard_eq3, ?_⟩
  have hθ_6 : (2 * p + 4) + max 3 (2 * p + 2) < θ := by omega
  rcases hcases with ⟨F, hO, hnorm, hNF, hΔ_cells⟩ | ⟨F, n₁, n₂, hF, hnorm, hFbd, hNF, hΔ_cells⟩
  · -- Case 1: `F` is a `Γ`-normal `O`-arc in `Σ`.
    have hFγ_le : (F ∩ π.domγ).ncard ≤ 2 * p + 4 := by
      have hsub : F ∩ π.domγ ⊆ π.Γ.N ∩ F := fun x hx => ⟨π.domγ_subset hx.2, hx.1⟩
      have hfin : (π.Γ.N ∩ F).Finite := π.Γ.finite_N.inter_of_left F
      have hle3 : (F ∩ π.domγ).ncard ≤ 3 := by
        calc (F ∩ π.domγ).ncard
          _ ≤ (π.Γ.N ∩ F).ncard := ncard_le_ncard hsub hfin
          _ = 3 := by rw [hNF, hcard_eq3]
      omega
    obtain ⟨Δ, hΔ, hbd, hsmall⟩ :=
      theorem_6_4_proof h𝒯 π htrue.1 hwarp hred hθ_6 hO hnorm hFγ_le
    refine ⟨Δ, hΔ, hΔ_cells Δ hΔ hbd, hsmall, Or.inl ?_⟩
    rw [hbd]
    exact ⟨hO, hnorm, hNF⟩
  · -- Case 2: `F` is a `Γ`-normal `I`-arc in `Σ`.
    have hFγ_le : 2 * p ≤ 2 * p + 4 ∧ (F ∩ π.domγ).ncard ≤ (2 * p + 4) - 2 * p := by
      have hsub : F ∩ π.domγ ⊆ π.Γ.N ∩ F := fun x hx => ⟨π.domγ_subset hx.2, hx.1⟩
      have hfin : (π.Γ.N ∩ F).Finite := π.Γ.finite_N.inter_of_left F
      have hle3 : (F ∩ π.domγ).ncard ≤ 3 := by
        calc (F ∩ π.domγ).ncard
          _ ≤ (π.Γ.N ∩ F).ncard := ncard_le_ncard hsub hfin
          _ = 3 := by rw [hNF, hcard_eq3]
      omega
    obtain ⟨Δ, hΔ, hF_bd, hbd_sub, hsmall⟩ :=
      theorem_6_3_proof h𝒯 π htrue.1 hwarp hred hθ_6
        hnorm hF hFbd hFγ_le
    exact ⟨Δ, hΔ, hΔ_cells Δ hΔ hF_bd hbd_sub, hsmall,
      Or.inr ⟨F, n₁, n₂, hF, hnorm, hFbd, hF_bd, hbd_sub, hNF⟩⟩

/-- Attachment bound for `π.areaGraph Δ` when `Δ` is bounded either by a `Γ`-normal `O$-arc with
$3$ nodes or by a `Γ`-normal $I$-arc $F$ with $3$ nodes and $\operatorname{bd}(\Sigma)$:
in either case, $\alpha(\Delta)$ has at most $2p + 3$ attachments in $G$. -/
private theorem ncard_attachments_areaGraph_le
    {α : Type u} {β : Type v} {G : Hypergraph α β} {p : ℕ}
    (π : Portrayal G) (hwarp : π.warp ≤ p)
    {Δ : Set π.S} (hΔ : IsClosedDisc Δ)
    (hbd_cases :
      (IsOArc (discBd Δ) ∧ π.Γ.IsNormal (discBd Δ) ∧ (π.Γ.N ∩ discBd Δ).ncard = 3) ∨
      (∃ F : Set π.S, ∃ n₁ n₂ : π.S,
        IsLineWithEnds F n₁ n₂ ∧ π.Γ.IsNormal F ∧ F ∩ bd π.S = {n₁, n₂} ∧
        F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧ (π.Γ.N ∩ F).ncard = 3)) :
    (attachments G (π.areaGraph Δ)).ncard ≤ 2 * p + 3 := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have : ConnectedSpace π.S := π.connected
  let I₁ : Set (Set π.S) := {c ∈ π.Γ.C | c ⊆ Δ}
  let I₂ : Set (Set π.S) := {c ∈ π.Γ.C | ¬ c ⊆ Δ}
  have hcov : I₁ ∪ I₂ = π.Γ.C := by
    ext c
    simp only [I₁, I₂, mem_union, mem_sep_iff]
    refine ⟨fun h => h.elim And.left And.left, ?_⟩
    intro hc
    by_cases h : c ⊆ Δ
    · exact Or.inl ⟨hc, h⟩
    · exact Or.inr ⟨hc, h⟩
  have hdisj : Disjoint I₁ I₂ := by
    rw [Set.disjoint_left]
    exact fun _ h₁ h₂ => h₂.2 h₁.2
  have hsep : G.IsSeparation (π.cellsUnion I₁) (π.cellsUnion I₂) :=
    π.isSeparation_cellsUnion hcov hdisj
  have hatt_sub_inter : attachments G (π.areaGraph Δ) ⊆
      (π.cellsUnion I₁ ∩ π.cellsUnion I₂).vertexSet :=
    attachments_subset_inter_of_isSeparation hsep
  have h21 := (theorem_2_1_proof π hcov hdisj).2
  rcases hbd_cases with ⟨_, hnorm, hcard3⟩ | ⟨F, n₁, n₂, hF, hnorm, hFbd, hF_bd, hbd_sub, hcard3⟩
  · -- Case 1: `discBd Δ` is a `Γ`-normal `O`-arc with `3` nodes.
    obtain ⟨hdich, hno_bd, _⟩ := normal_disc_cell_dichotomy π.isSurface π.Γ hΔ hnorm
    have hsub_nv : attachments G (π.areaGraph Δ) ⊆ π.nodeVertex '' (π.Γ.N ∩ discBd Δ) := by
      intro v hv
      have hv_inter := hatt_sub_inter hv
      rw [h21] at hv_inter
      rcases hv_inter with hγ | hbs
      · rw [mem_iUnion₂] at hγ
        rcases hγ with ⟨c₁, hc₁, hγ⟩
        rw [mem_iUnion₂] at hγ
        rcases hγ with ⟨c₂, hc₂, hγ⟩
        rw [← π.gammaImage_inter, Portrayal.mem_gammaImage_iff] at hγ
        rcases hγ with ⟨n, ⟨hnc₁, hndom⟩, rfl⟩
        have hc₂_out : c₂ ⊆ Set.univ \ Δ :=
          (hdich c₂ hc₂.1).resolve_left fun h => hc₂.2 (h.trans sdiff_subset)
        have hcl_inter :=
          (closure_cell_inter_disc_of_subset_compl π.isSurface π.Γ hΔ hnorm hc₂.1 hc₂_out).2
        have hn_Δ : n ∈ Δ := (isClosed_of_isClosedDisc hΔ).closure_subset_iff.mpr hc₁.2 hnc₁.1.1
        have hn_bdΔ : n ∈ discBd Δ := by
          have : n ∈ closure c₂ ∩ Δ := ⟨hnc₁.2.1, hn_Δ⟩
          rw [hcl_inter] at this
          exact this.2
        exact ⟨n, ⟨π.domγ_subset hndom, hn_bdΔ⟩, rfl⟩
      · rw [mem_iUnion₂] at hbs
        rcases hbs with ⟨n, ⟨c₁, hc₁, hbd₁, _⟩, _⟩
        have hc₁_out : c₁ ⊆ Set.univ \ Δ := hno_bd c₁ hc₁.1 hbd₁
        rcases hbd₁ with ⟨x, hxc₁, _⟩
        exact ((hc₁_out hxc₁).2 (hc₁.2 hxc₁)).elim
    have hfin : (π.Γ.N ∩ discBd Δ).Finite := π.Γ.finite_N.inter_of_left _
    have hle : (attachments G (π.areaGraph Δ)).ncard ≤ (π.Γ.N ∩ discBd Δ).ncard :=
      (ncard_le_ncard hsub_nv (hfin.image _)).trans (ncard_image_le hfin)
    omega
  · -- Case 2: `F` is a `Γ`-normal `I`-arc with ends `n₁, n₂` and `3` nodes.
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hnb⟩ :=
      arc_disc_data π.isSurface hF hFbd hΔ hF_bd hbd_sub
    have hsep_F : ∀ c₁ ∈ I₁, ∀ c₂ ∈ I₂, tilde c₁ ∩ tilde c₂ ⊆ F := by
      intro c₁ hc₁ c₂ hc₂ x ⟨hx₁, hx₂⟩
      by_contra hxF
      have hxΔ : x ∈ Δ := closure_minimal hc₁.2 hΔ.isClosed hx₁.1
      obtain ⟨y, hyΔ, hyc₂⟩ := mem_closure_iff_nhds.mp hx₂.1 Δ (hnb x ⟨hxΔ, hxF⟩)
      exact (cell_side hc₂.1 hnorm hΔ hnb).resolve_left hc₂.2 hyc₂ hyΔ
    have hatt_sub : attachments G (π.areaGraph Δ) ⊆
        π.borderSet n₁ ∪ π.borderSet n₂ ∪ π.nodeVertex '' (π.Γ.N ∩ F) := by
      intro v hv
      have hv_inter := hatt_sub_inter hv
      rw [h21] at hv_inter
      rcases hv_inter with hγ | hbs
      · rw [mem_iUnion₂] at hγ
        rcases hγ with ⟨c₁, hc₁, hγ⟩
        rw [mem_iUnion₂] at hγ
        rcases hγ with ⟨c₂, hc₂, hγ⟩
        rw [← π.gammaImage_inter, Portrayal.mem_gammaImage_iff] at hγ
        rcases hγ with ⟨n, ⟨hnd, hndom⟩, rfl⟩
        exact Or.inr ⟨n, ⟨π.domγ_subset hndom, hsep_F c₁ hc₁ c₂ hc₂ hnd⟩, rfl⟩
      · rw [mem_iUnion₂] at hbs
        rcases hbs with ⟨n, ⟨c₁, hc₁, hbd₁, c₂, hc₂, _, hnd⟩, hvn⟩
        have hnF : n ∈ F := hsep_F c₁ hc₁ c₂ hc₂ hnd
        obtain ⟨u₁, v₁, _, htilde₁, _, _, hu₁, hv₁⟩ := π.Γ.border_cell_exists_ends hc₁.1 hbd₁
        have hn_uv : n ∈ ({u₁, v₁} : Set π.S) := htilde₁ ▸ hnd.1
        have hnbd : n ∈ bd π.S := by rcases hn_uv with rfl | rfl <;> [exact hu₁.2; exact hv₁.2]
        have hn_pair : n ∈ ({n₁, n₂} : Set π.S) := hFbd ▸ ⟨hnF, hnbd⟩
        rcases hn_pair with rfl | rfl
        · exact Or.inl (Or.inl hvn)
        · exact Or.inl (Or.inr hvn)
    have hn₁_mem : n₁ ∈ F ∩ bd π.S := hFbd ▸ mem_insert _ _
    have hn₂_mem : n₂ ∈ F ∩ bd π.S := hFbd ▸ mem_insert_of_mem _ (mem_singleton _)
    have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S :=
      ⟨hnorm ⟨hn₁_mem.1, π.Γ.bd_subset hn₁_mem.2⟩, hn₁_mem.2⟩
    have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S :=
      ⟨hnorm ⟨hn₂_mem.1, π.Γ.bd_subset hn₂_mem.2⟩, hn₂_mem.2⟩
    have hn₁_card : (π.borderSet n₁).ncard ≤ p :=
      (π.ncard_borderSet_le_warp hn₁_bd).trans hwarp
    have hn₂_card : (π.borderSet n₂).ncard ≤ p :=
      (π.ncard_borderSet_le_warp hn₂_bd).trans hwarp
    have hNF_fin : (π.Γ.N ∩ F).Finite := π.Γ.finite_N.inter_of_left F
    have hfin_u : (π.borderSet n₁ ∪ π.borderSet n₂ ∪ π.nodeVertex '' (π.Γ.N ∩ F)).Finite :=
      ((π.borderSet_finite hn₁_bd).union (π.borderSet_finite hn₂_bd)).union (hNF_fin.image _)
    have h0 := ncard_le_ncard hatt_sub hfin_u
    have h1 := ncard_union_le (π.borderSet n₁ ∪ π.borderSet n₂) (π.nodeVertex '' (π.Γ.N ∩ F))
    have h2 := ncard_union_le (π.borderSet n₁) (π.borderSet n₂)
    have h3 := ncard_image_le (f := π.nodeVertex) hNF_fin
    omega

private theorem nontrivial_cell_partition_determines_disc_side
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {θ : ℕ}
    {p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 4))
    (hwarp : π.warp ≤ p)
    (hθ : 6 * p + 8 < θ)
    {A : Hypergraph α β}
    {B : Hypergraph α β}
    (hord : A.separationOrder B + 4 * p + 3 < θ)
    {c₀ : Set π.S}
    (hc₀ : c₀ ∈ π.Γ.C)
    {I : Set (Set π.S)}
    {J : Set (Set π.S)}
    (hcov : I ∪ J = π.Γ.C)
    (hdisj : Disjoint I J)
    (hc₀I : c₀ ∈ I)
    [this : T2Space π.S]
    (hθ3 : 4 * p + 5 < θ)
    (h82_node : ∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c)
    (hXY_eq : ({n | n ∈ π.Γ.N ∧ π.nodeVertex n ∈ A.vertexSet}) ∩ ({n | n ∈ π.Γ.N ∧ π.nodeVertex n
      ∈ B.vertexSet}) = {n | n ∈ π.Γ.N ∧ π.nodeVertex n ∈ (A ∩ B).vertexSet})
    (hXY_fin : (({n | n ∈ π.Γ.N ∧ π.nodeVertex n ∈ A.vertexSet}) ∩ ({n | n ∈ π.Γ.N ∧ π.nodeVertex
      n ∈ B.vertexSet})).Finite)
    (hJ_sub : J ⊆ π.Γ.C)
    (htI_sub_X : π.Γ.tildeOfCells I ⊆ ({n | n ∈ π.Γ.N ∧ π.nodeVertex n ∈ A.vertexSet}))
    (htJ_sub_Y : π.Γ.tildeOfCells J ⊆ ({n | n ∈ π.Γ.N ∧ π.nodeVertex n ∈ B.vertexSet}))
    (htIJ_union : π.Γ.tildeOfCells I ∪ π.Γ.tildeOfCells J = π.Γ.N)
    (hc₀_le3 : (tilde c₀).ncard ≤ 3)
    (hXY_le : (({n | n ∈ π.Γ.N ∧ π.nodeVertex n ∈ A.vertexSet}) ∩ ({n | n ∈ π.Γ.N ∧ π.nodeVertex n
      ∈ B.vertexSet})).ncard ≤ (tilde c₀).ncard)
    (htIJ_sub_XY : π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J ⊆ ({n | n ∈ π.Γ.N ∧ π.nodeVertex n ∈
      A.vertexSet}) ∩ ({n | n ∈ π.Γ.N ∧ π.nodeVertex n ∈ B.vertexSet}))
    (htIJ_le : (π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J).ncard ≤ (({n | n ∈ π.Γ.N ∧ π.nodeVertex n
      ∈ A.vertexSet}) ∩ ({n | n ∈ π.Γ.N ∧ π.nodeVertex n ∈ B.vertexSet})).ncard)
    (hA_small : IsSmallWrt 𝒯 A)
    (hatt_A : (attachments G A).ncard ≤ A.separationOrder B)
    (htI_ne_N : π.Γ.tildeOfCells I ≠ π.Γ.N)
    (htJ_ne_N : ¬π.Γ.tildeOfCells J = π.Γ.N) :
    {n | n ∈ π.Γ.N ∧ π.nodeVertex n ∈ (A ∩ B).vertexSet}.ncard = (tilde c₀).ncard ∧ (({n | n ∈
      π.Γ.N ∧ π.nodeVertex n ∈ A.vertexSet} = tilde c₀ ∧ ∀ n ∈ π.Γ.N, π.nodeVertex n ∈
      B.vertexSet) ∨ (tilde c₀).ncard = 3 ∧ ∃ (F Δ : Set π.S) (n₁ n₂ : π.S), IsLineWithEnds F n₁
      n₂ ∧ π.Γ.IsNormal F ∧ F ∩ bd π.S = {n₁, n₂} ∧ IsClosedDisc Δ ∧ IsSmallWrt 𝒯 (π.areaGraph Δ)
      ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧ I = {c | c ∈ π.Γ.C ∧ c ⊆ Δ} ∧ ∀ n ∈ π.Γ.N,
      (π.nodeVertex n ∈ A.vertexSet ↔ n ∈ Δ) ∧ (π.nodeVertex n ∈ B.vertexSet ↔ n ∈ closure (univ \
      Δ)) ∧ (π.nodeVertex n ∈ B.vertexSet ↔ n ∈ univ \ Δ ∪ F)) := by
  let X := {n | n ∈ π.Γ.N ∧ π.nodeVertex n ∈ A.vertexSet}
  let Y := {n | n ∈ π.Γ.N ∧ π.nodeVertex n ∈ B.vertexSet}
  -- Case `π.Γ.tildeOfCells J ≠ π.Γ.N`: apply (11.1).
  obtain ⟨htIJ_eq3, Δ, hΔ, hΔ_cells, hΔ_small, hΔ_cases⟩ :=
    theorem_11_1_proof h𝒯 π htrue hred hwarp hθ
      hcov hdisj htI_ne_N htJ_ne_N (by omega)
  have hXY_eq3 : (X ∩ Y).ncard = 3 :=
    Nat.le_antisymm (hXY_le.trans hc₀_le3) (htIJ_eq3 ▸ htIJ_le)
  have hc₀_eq3 : (tilde c₀).ncard = 3 := by omega
  have hcard_eq : {n ∈ π.Γ.N | π.nodeVertex n ∈ (A ∩ B).vertexSet}.ncard = (tilde c₀).ncard := by
    rw [← hXY_eq, hXY_eq3, hc₀_eq3]
  have htIJ_eq_XY : π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J = X ∩ Y :=
    eq_of_subset_of_ncard_le htIJ_sub_XY (by omega) hXY_fin
  have hX_eq_tI : X = π.Γ.tildeOfCells I := by
    refine Subset.antisymm (fun n hnX => ?_) htI_sub_X
    rcases htIJ_union ▸ hnX.1 with hnI | hnJ
    · exact hnI
    · have hnXY : n ∈ X ∩ Y := ⟨hnX, htJ_sub_Y hnJ⟩
      rw [← htIJ_eq_XY] at hnXY
      exact hnXY.1
  have hY_eq_tJ : Y = π.Γ.tildeOfCells J := by
    refine Subset.antisymm (fun n hnY => ?_) htJ_sub_Y
    rcases htIJ_union ▸ hnY.1 with hnI | hnJ
    · have hnXY : n ∈ X ∩ Y := ⟨htI_sub_X hnI, hnY⟩
      rw [← htIJ_eq_XY] at hnXY
      exact hnXY.2
    · exact hnJ
  -- Show `{c ∈ π.Γ.C | c ⊆ Δ} = I` using (4.3) applied to `A ∪ π.areaGraph Δ`.
  have hbd_card :
      (IsOArc (discBd Δ) ∧ π.Γ.IsNormal (discBd Δ) ∧ (π.Γ.N ∩ discBd Δ).ncard = 3) ∨
      (∃ F : Set π.S, ∃ n₁ n₂ : π.S,
        IsLineWithEnds F n₁ n₂ ∧ π.Γ.IsNormal F ∧ F ∩ bd π.S = {n₁, n₂} ∧
        F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧ (π.Γ.N ∩ F).ncard = 3) := by
    rcases hΔ_cases with ⟨hO, hnorm, hNF⟩ | ⟨F, n₁, n₂, hF, hnorm, hFbd, hF_bd, hbd_sub, hNF⟩
    · exact Or.inl ⟨hO, hnorm, by rw [hNF, htIJ_eq3]⟩
    · exact Or.inr ⟨F, n₁, n₂, hF, hnorm, hFbd, hF_bd, hbd_sub, by rw [hNF, htIJ_eq3]⟩
  have hatt_Δ : (attachments G (π.areaGraph Δ)).ncard ≤ 2 * p + 3 :=
    ncard_attachments_areaGraph_le π hwarp hΔ hbd_card
  have hatt_union : (attachments G (A ∪ π.areaGraph Δ)).ncard + 2 * p < θ := by
    have hsub : attachments G (A ∪ π.areaGraph Δ) ⊆
        attachments G A ∪ attachments G (π.areaGraph Δ) :=
      fun _ hv => attachments_union_subset hv
    have hle : (attachments G (A ∪ π.areaGraph Δ)).ncard ≤
        (attachments G A).ncard + (attachments G (π.areaGraph Δ)).ncard :=
      (ncard_le_ncard hsub (attachments_finite.union attachments_finite)).trans
        (ncard_union_le _ _)
    omega
  have hAΔ_small : IsSmallWrt 𝒯 (A ∪ π.areaGraph Δ) :=
    hA_small.union h𝒯 hΔ_small (by omega)
  have hex_n₀ : ∃ n₀ ∈ π.domγ, π.nodeVertex n₀ ∉ (A ∪ π.areaGraph Δ).vertexSet := by
    by_contra hnot
    push Not at hnot
    exact theorem_4_3_proof h𝒯 π htrue.1 hwarp
      ⟨A ∪ π.areaGraph Δ, hAΔ_small, by omega, hnot⟩
  obtain ⟨n₀, hn₀γ, hn₀_not⟩ := hex_n₀
  have hn₀N : n₀ ∈ π.Γ.N := π.domγ_subset hn₀γ
  have hn₀_notX : n₀ ∉ X := fun h => hn₀_not (Or.inl h.2)
  obtain ⟨c₁, hc₁, hn₀_c₁⟩ := h82_node n₀ hn₀N
  have hc₁_notI : c₁ ∉ I := by
    intro hc₁I
    exact hn₀_notX (htI_sub_X (mem_biUnion hc₁I hn₀_c₁))
  have hc₁J : c₁ ∈ J := (hcov ▸ hc₁).resolve_left hc₁_notI
  have hc₁_notΔ : ¬ c₁ ⊆ Δ := by
    intro hc₁Δ
    have hv_c₁ : π.nodeVertex n₀ ∈ (π.cellGraph c₁).vertexSet :=
      π.p2 c₁ hc₁ n₀ ⟨hn₀_c₁, hn₀γ⟩
    have hv_Δ : π.nodeVertex n₀ ∈ (π.areaGraph Δ).vertexSet :=
      mem_biUnion ⟨⟨hc₁, hc₁Δ⟩, hc₁⟩ hv_c₁
    exact hn₀_not (Or.inr hv_Δ)
  have hcells_eq_I : {c ∈ π.Γ.C | c ⊆ Δ} = I := by
    rcases hΔ_cells with hEq | hEq
    · exact hEq
    · exfalso
      have : c₁ ∈ {c ∈ π.Γ.C | c ⊆ Δ} := hEq.symm ▸ hc₁J
      exact hc₁_notΔ this.2
  -- Note that `c₀ ∈ I` since if `c₀ ∈ J`, then `tilde c₀ ⊆ X ∩ Y` so `tilde c₀ ⊆ tildeOfCells I`,
  -- which is fine, wait: if `c₀ ∈ J`, then `tilde c₀ ⊆ htJ_sub_Y` AND `tilde c₀ ⊆ X`,
  -- so `tilde c₀ ⊆ X ∩ Y = tildeOfCells I ∩ tildeOfCells J`.
  -- Wait: what if `discBd Δ` is a `Γ`-normal `O`-arc?
  rcases hΔ_cases with ⟨hO, hnorm, hNF⟩ | ⟨F, n₁, n₂, hF, hnorm, hFbd, hF_bd, hbd_sub, hNF⟩
  · -- Rule out the `Γ`-normal `O`-arc case using (8.5) / (7.2).
    exfalso
    have hc₀_Δ : c₀ ⊆ Δ := (hcells_eq_I.symm ▸ hc₀I).2
    have hFN_eq3 : (discBd Δ ∩ π.Γ.N).ncard = 3 := by
      rw [Set.inter_comm, hNF, htIJ_eq3]
    have hnode_bd : ∀ n ∈ discBd Δ ∩ π.domγ, ∃ d ∈ π.Γ.C, n ∈ tilde d :=
      fun n hn => h82_node n (π.domγ_subset hn.2)
    obtain ⟨π', _, hπ'_central, hπ'_res, h72⟩ :=
      theorem_7_2_proof h𝒯 (by omega) π htrue.1 hΔ hnorm (by omega) hnode_bd hΔ_small
    rcases h72 ⟨c₀, hc₀, hc₀_Δ, by omega⟩ with htruer | ⟨hΔ_N, _⟩
    · exact htrue.2.2 π' hπ'_central htruer hπ'_res
    · have htI_sub_tJ : π.Γ.tildeOfCells I ⊆ π.Γ.tildeOfCells J := by
        intro n hnI
        rw [← hcells_eq_I] at hnI
        rcases mem_iUnion₂.mp hnI with ⟨c, ⟨hcC, hcΔ⟩, hnc⟩
        have hnΔ : n ∈ Δ := closure_minimal hcΔ hΔ.isClosed hnc.1
        have hnN : n ∈ π.Γ.N := π.Γ.tilde_subset_N hcC hnc
        have hn_bd : n ∈ π.Γ.N ∩ discBd Δ := ⟨hnN, hΔ_N ⟨hnΔ, hnN⟩⟩
        rw [hNF] at hn_bd
        exact hn_bd.2
      have hJ_eq_N : π.Γ.tildeOfCells J = π.Γ.N := by
        rw [← htIJ_union, union_eq_self_of_subset_left htI_sub_tJ]
      exact htJ_ne_N hJ_eq_N
  · -- `F` is a `Γ`-normal `I`-arc with ends `n₁, n₂`.
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hnb⟩ :=
      arc_disc_data π.isSurface hF hFbd hΔ hF_bd hbd_sub
    refine ⟨hcard_eq, Or.inr ⟨hc₀_eq3, F, Δ, n₁, n₂, hF, hnorm, hFbd, hΔ, hΔ_small,
      hF_bd, hbd_sub, hcells_eq_I.symm, fun n hnN => ?_⟩⟩
    have hnA_iff_tI' : π.nodeVertex n ∈ A.vertexSet ↔ n ∈ π.Γ.tildeOfCells I := by
      calc π.nodeVertex n ∈ A.vertexSet
        _ ↔ n ∈ X := ⟨fun h => ⟨hnN, h⟩, fun h => h.2⟩
        _ ↔ n ∈ π.Γ.tildeOfCells I := by rw [hX_eq_tI]
    have hnB_iff_tJ : π.nodeVertex n ∈ B.vertexSet ↔ n ∈ π.Γ.tildeOfCells J := by
      calc π.nodeVertex n ∈ B.vertexSet
        _ ↔ n ∈ Y := ⟨fun h => ⟨hnN, h⟩, fun h => h.2⟩
        _ ↔ n ∈ π.Γ.tildeOfCells J := by rw [hY_eq_tJ]
    have htI_iff_Δ : n ∈ π.Γ.tildeOfCells I ↔ n ∈ Δ := by
      constructor
      · intro hnI
        rw [← hcells_eq_I] at hnI
        rcases mem_iUnion₂.mp hnI with ⟨c, ⟨_, hcΔ⟩, hnc⟩
        exact closure_minimal hcΔ hΔ.isClosed hnc.1
      · intro hnΔ
        by_cases hnF : n ∈ F
        · have hn_inter : n ∈ π.Γ.N ∩ F := ⟨hnN, hnF⟩
          rw [hNF] at hn_inter
          exact hn_inter.1
        · obtain ⟨c, hcC, hnc⟩ := h82_node n hnN
          obtain ⟨y, hyΔ, hyc⟩ := mem_closure_iff_nhds.mp hnc.1 Δ (hnb n ⟨hnΔ, hnF⟩)
          have hcΔ : c ⊆ Δ := (cell_side hcC hnorm hΔ hnb).resolve_right fun h => h hyc hyΔ
          have hcI : c ∈ I := hcells_eq_I ▸ ⟨hcC, hcΔ⟩
          exact mem_biUnion hcI hnc
    have htJ_imp_cl : n ∈ π.Γ.tildeOfCells J → n ∈ closure (Set.univ \ Δ) := by
      intro hnJ
      rcases mem_iUnion₂.mp hnJ with ⟨c, hcJ, hnc⟩
      have hcC : c ∈ π.Γ.C := hJ_sub hcJ
      have hc_notΔ : ¬ c ⊆ Δ := by
        intro hcΔ
        have hcI : c ∈ I := hcells_eq_I ▸ ⟨hcC, hcΔ⟩
        exact Set.disjoint_left.mp hdisj hcI hcJ
      have hc_compl : c ⊆ Set.univ \ Δ := by
        have := (cell_side hcC hnorm hΔ hnb).resolve_left hc_notΔ
        exact fun x hx => ⟨ trivial, this hx ⟩
      exact closure_mono hc_compl hnc.1
    have hcl_imp_union : n ∈ closure (Set.univ \ Δ) → n ∈ (Set.univ \ Δ) ∪ F := by
      intro hn_cl
      by_cases hnF : n ∈ F
      · exact Or.inr hnF
      · left
        refine ⟨trivial, fun hnΔ => ?_⟩
        obtain ⟨y, hyΔ, hy_compl⟩ := mem_closure_iff_nhds.mp hn_cl Δ (hnb n ⟨hnΔ, hnF⟩)
        exact hy_compl.2 hyΔ
    have hunion_imp_tJ : n ∈ (Set.univ \ Δ) ∪ F → n ∈ π.Γ.tildeOfCells J := by
      rintro (⟨_, hn_notΔ⟩ | hnF)
      · have hn_notI : n ∉ π.Γ.tildeOfCells I := mt htI_iff_Δ.mp hn_notΔ
        exact (htIJ_union ▸ hnN).resolve_left hn_notI
      · have hn_inter : n ∈ π.Γ.N ∩ F := ⟨hnN, hnF⟩
        rw [hNF] at hn_inter
        exact hn_inter.2
    refine ⟨hnA_iff_tI'.trans htI_iff_Δ,
      hnB_iff_tJ.trans ⟨htJ_imp_cl, fun h => hunion_imp_tJ (hcl_imp_union h)⟩,
      hnB_iff_tJ.trans ⟨fun h => hcl_imp_union (htJ_imp_cl h), hunion_imp_tJ⟩⟩

/-- **Graph Minors XVII, (11.2)** (pages 191–192):
"Let $(A, B) \in \mathscr{T}$ have order $< ord(\mathscr{T}) - 4p - 3$, let $c_0 \in C(\Gamma)$
with $\alpha(c_0) \subseteq A$, let $I, J$ be a partition of $C(\Gamma)$ so that $\gamma(I)
\subseteq V(A)$ and $\gamma(J) \subseteq V(B)$ and let
$$|\{n \in N(\Gamma) : \gamma(n) \in V(A \cap B)\}| \le |\tilde{c}_0|.$$
Then equality holds, and either
(i) $\{n \in N(\Gamma) : \gamma(n) \in V(A)\} = \tilde{c}_0$ and $\gamma(n) \in V(B)$ for all $n
\in N(\Gamma)$, or
(ii) $|\tilde{c}_0| = 3$, and there is a $\Gamma$-normal $I$-arc $F$ and a disc $\Delta \subseteq
\Sigma$ with $\alpha(\Delta)$ small and with $F \subseteq bd(\Delta) \subseteq F \cup bd(\Sigma)$,
such that $I = \{c \in C(\Gamma) : c \subseteq \Delta\}$ and for all $n \in N(\Gamma)$, $\gamma(n)
\in V(A)$ if and only if $n \in \Delta$, and $\gamma(n) \in V(B)$ if and only if..."

We also record the equivalent condition $n \in (\Sigma \setminus \Delta) \cup F$ for
$\gamma(n) \in V(B)$ in (ii). -/
theorem theorem_11_2_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 4))
    (hwarp : π.warp ≤ p)
    (hθ : 6 * p + 8 < θ)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯)
    (hord : separationOrder A B + 4 * p + 3 < θ)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hc₀A : π.cellGraph c₀ ≤ A)
    {I J : Set (Set π.S)} (hcov : I ∪ J = π.Γ.C) (hdisj : Disjoint I J)
    (hc₀I : c₀ ∈ I)
    (hI_A : π.gammaOfCells I ⊆ A.vertexSet)
    (hJ_B : π.gammaOfCells J ⊆ B.vertexSet)
    (hcard_le : {n ∈ π.Γ.N | π.nodeVertex n ∈ (A ∩ B).vertexSet}.ncard ≤ (tilde c₀).ncard) :
    {n ∈ π.Γ.N | π.nodeVertex n ∈ (A ∩ B).vertexSet}.ncard = (tilde c₀).ncard ∧
    (({n ∈ π.Γ.N | π.nodeVertex n ∈ A.vertexSet} = tilde c₀ ∧
        ∀ n ∈ π.Γ.N, π.nodeVertex n ∈ B.vertexSet) ∨
     ((tilde c₀).ncard = 3 ∧
      ∃ F Δ : Set π.S, ∃ n₁ n₂ : π.S,
        IsLineWithEnds F n₁ n₂ ∧ π.Γ.IsNormal F ∧ F ∩ bd π.S = {n₁, n₂} ∧
        IsClosedDisc Δ ∧ IsSmallWrt 𝒯 (π.areaGraph Δ) ∧
        F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧
        I = {c ∈ π.Γ.C | c ⊆ Δ} ∧
        (∀ n ∈ π.Γ.N,
          (π.nodeVertex n ∈ A.vertexSet ↔ n ∈ Δ) ∧
          (π.nodeVertex n ∈ B.vertexSet ↔ n ∈ closure (Set.univ \ Δ)) ∧
          (π.nodeVertex n ∈ B.vertexSet ↔ n ∈ (Set.univ \ Δ) ∪ F)))) := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have : ConnectedSpace π.S := π.connected
  have hred3 : π.IsRedundant 𝒯 θ (2 * p + 3) := hred.mono (by omega)
  have hθ3 : 4 * p + 5 < θ := by omega
  obtain ⟨_, h82_card, h82_node⟩ :=
    theorem_8_2_proof
      h𝒯 π htrue hred3 hwarp hθ3
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof
      h𝒯 π htrue hred3 hwarp hθ3
  have hsep : G.IsSeparation A B := h𝒯.isSeparation hAB
  let X : Set π.S := {n ∈ π.Γ.N | π.nodeVertex n ∈ A.vertexSet}
  let Y : Set π.S := {n ∈ π.Γ.N | π.nodeVertex n ∈ B.vertexSet}
  have hXY_eq : X ∩ Y = {n ∈ π.Γ.N | π.nodeVertex n ∈ (A ∩ B).vertexSet} := by
    ext n
    simp only [X, Y, mem_inter_iff, mem_ofPred_eq, inter_vertexSet]
    tauto
  have hX_fin : X.Finite := π.Γ.finite_N.subset fun _ hn => hn.1
  have hY_fin : Y.Finite := π.Γ.finite_N.subset fun _ hn => hn.1
  have hXY_fin : (X ∩ Y).Finite := hX_fin.inter_of_left Y
  have hc₀_sub_X : tilde c₀ ⊆ X := by
    intro n hn
    refine ⟨π.Γ.tilde_subset_N hc₀ hn, hc₀A.1 ?_⟩
    exact π.p2 c₀ hc₀ n ⟨hn, hdom ▸ π.Γ.tilde_subset_N hc₀ hn⟩
  have hI_sub : I ⊆ π.Γ.C := hcov ▸ subset_union_left
  have hJ_sub : J ⊆ π.Γ.C := hcov ▸ subset_union_right
  have htI_sub_X : π.Γ.tildeOfCells I ⊆ X := by
    intro n hn
    refine ⟨π.Γ.tildeOfCells_subset_N hI_sub hn, hI_A ?_⟩
    rw [π.gammaOfCells_eq_image_tildeOfCells hdom hI_sub]
    exact mem_image_of_mem _ hn
  have htJ_sub_Y : π.Γ.tildeOfCells J ⊆ Y := by
    intro n hn
    refine ⟨π.Γ.tildeOfCells_subset_N hJ_sub hn, hJ_B ?_⟩
    rw [π.gammaOfCells_eq_image_tildeOfCells hdom hJ_sub]
    exact mem_image_of_mem _ hn
  have htIJ_union : π.Γ.tildeOfCells I ∪ π.Γ.tildeOfCells J = π.Γ.N := by
    rw [← π.Γ.tildeOfCells_union, hcov, π.Γ.tildeOfCells_eq_N h82_node]
  have hXY_union : X ∪ Y = π.Γ.N := by
    refine Subset.antisymm (union_subset (fun _ h => h.1) (fun _ h => h.1)) ?_
    rw [← htIJ_union]
    exact union_subset_union htI_sub_X htJ_sub_Y
  have hc₀_le3 : (tilde c₀).ncard ≤ 3 := π.Γ.ncard_tilde_cell_le hc₀
  have hXY_le : (X ∩ Y).ncard ≤ (tilde c₀).ncard := by rwa [hXY_eq]
  have htIJ_sub_XY : π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J ⊆ X ∩ Y :=
    inter_subset_inter htI_sub_X htJ_sub_Y
  have htIJ_le : (π.Γ.tildeOfCells I ∩ π.Γ.tildeOfCells J).ncard ≤ (X ∩ Y).ncard :=
    ncard_le_ncard htIJ_sub_XY hXY_fin
  -- By (4.3), `X ≠ π.Γ.N`, hence `π.Γ.tildeOfCells I ≠ π.Γ.N`.
  have hA_small : IsSmallWrt 𝒯 A := ⟨B, hAB⟩
  have hatt_A : (attachments G A).ncard ≤ separationOrder A B :=
    ncard_le_ncard (attachments_subset_inter_of_isSeparation hsep)
      (G.vertexSet_finite.subset (inter_subset_left.trans hsep.1.1))
  have hX_ne_N : X ≠ π.Γ.N := by
    intro hXN
    apply theorem_4_3_proof h𝒯 π htrue.1 hwarp
    refine ⟨A, hA_small, by omega, fun n hnγ => ?_⟩
    have hnX : n ∈ X := hXN.symm ▸ π.domγ_subset hnγ
    exact hnX.2
  have htI_ne_N : π.Γ.tildeOfCells I ≠ π.Γ.N := by
    intro hIN
    exact hX_ne_N (Subset.antisymm (fun _ h => h.1) (hIN ▸ htI_sub_X))
  by_cases htJ_ne_N : π.Γ.tildeOfCells J = π.Γ.N
  · -- Case `π.Γ.tildeOfCells J = π.Γ.N`: then `Y = π.Γ.N` and `X = tilde c₀`, giving (i).
    have hYN : Y = π.Γ.N := Subset.antisymm (fun _ h => h.1) (htJ_ne_N ▸ htJ_sub_Y)
    have hXY_eq_X : X ∩ Y = X := by
      have hX_N : X ⊆ π.Γ.N := fun _ h => h.1
      rw [hYN, inter_eq_self_of_subset_left hX_N]
    have hX_eq_c₀ : X = tilde c₀ := by
      apply (eq_of_subset_of_ncard_le hc₀_sub_X ?_ hX_fin).symm
      rw [← hXY_eq_X]
      exact hXY_le
    refine ⟨?_, Or.inl ⟨hX_eq_c₀, fun n hn => ?_⟩⟩
    · rw [← hXY_eq, hXY_eq_X, hX_eq_c₀]
    · have hnY : n ∈ Y := hYN.symm ▸ hn
      exact hnY.2
  · exact nontrivial_cell_partition_determines_disc_side (α := α) (β := β) (G := G) (𝒯 := 𝒯) (θ :=
      θ) (p := p) h𝒯 π htrue hred hwarp hθ (A := A) (B := B) hord (c₀ := c₀) hc₀ (I := I) (J := J)
      hcov hdisj hc₀I hθ3 h82_node hXY_eq hXY_fin hJ_sub htI_sub_X htJ_sub_Y htIJ_union hc₀_le3
      hXY_le htIJ_sub_XY htIJ_le hA_small hatt_A htI_ne_N htJ_ne_N
/-! ## 3. Three-Node Normal $I$-Arc Disc Separation: (11.3) (Pages 192–193) -/

private theorem opposite_side_cells_disjoint
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (hΘ_bd : Θ ⊆ bd π.S)
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (activeFor : Set π.S → Fin (p + 1) → Prop)
    (hactive : ∀ d j, activeFor d j ↔
      2 ≤ {v | v ∈ (P j).walk.support ∧ v ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard)
    (e : Set π.S → Set π.S)
    (he : e = fun d => {n | n ∈ tilde d ∩ π.domγ ∧
      ∃ l, activeFor d l ∧ π.nodeVertex n ∈ (P l).walk.support})
    (c : Set π.S)
    (I₁ : Set π.S)
    (I₂ : Set π.S)
    (N₁ : Set π.S)
    (N₂ : Set π.S)
    (hI₁_sub : I₁ ⊆ Θ ∩ discBd Δ)
    (hI₂_sub : I₂ ⊆ Θ ∩ discBd Δ)
    (hdisj_I : Disjoint I₁ I₂)
    (hN₁_sub : N₁ ⊆ (π.Γ.N ∩ Δ) \ bd π.S)
    (hN₂_sub : N₂ ⊆ (π.Γ.N ∩ Δ) \ bd π.S)
    (hdisj_N : Disjoint N₁ N₂)
    (j : Fin (p + 1)) :
    let I_Δ : Set (Set π.S) := {d | d ∈ π.Γ.C ∧ d ⊆ Δ}
    let D₁ : Set (Set π.S) := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₁ ∨ ¬(d ∩
      bd π.S).Nonempty ∧ activeFor d j ∧ e d ⊆ N₁ ∪ I₁)}
    let D₂ : Set (Set π.S) := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂ ∨ ¬(d ∩
      bd π.S).Nonempty ∧ activeFor d j ∧ e d ⊆ N₂ ∪ I₂)}
    Disjoint D₁ D₂ := by
  subst e
  let e (d : Set π.S) : Set π.S := {n | n ∈ tilde d ∩ π.domγ ∧
    ∃ l, activeFor d l ∧ π.nodeVertex n ∈ (P l).walk.support}
  intro I_Δ D₁ D₂
  rw [Set.disjoint_left]
  rintro d ⟨hd_I, h₁⟩ ⟨_, h₂⟩
  rcases h₁ with ⟨hbd, _, ht₁⟩ | ⟨hint, hact, he₁⟩
  · rcases h₂ with ⟨_, _, ht₂⟩ | ⟨hint₂, _, _⟩
    · obtain ⟨u₀, _, _, htilde_d, _, _, _⟩ := π.Γ.border_cell_exists_ends hd_I.1 hbd
      have hu₀ : u₀ ∈ tilde d := htilde_d ▸ mem_insert _ _
      exact Set.disjoint_left.mp hdisj_I (ht₁ hu₀) (ht₂ hu₀)
    · exact hint₂ hbd
  · rcases h₂ with ⟨hbd, _, _⟩ | ⟨_, _, he₂⟩
    · exact hint hbd
    · have hsub_ed : {z ∈ (P j).walk.support |
          z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)} ⊆ π.nodeVertex '' e d := by
        rintro z ⟨hz_sup, n, hn_td, rfl⟩
        exact ⟨n, ⟨hn_td, j, hact, hz_sup⟩, rfl⟩
      have hfin_ed : (e d).Finite := (π.Γ.finite_tilde_cell hd_I.1).subset fun _ hn => hn.1.1
      have hcard_ed : 2 ≤ (e d).ncard := by
        have hle₁ := ncard_le_ncard hsub_ed (hfin_ed.image _)
        have hle₂ := ncard_image_le (f := π.nodeVertex) hfin_ed
        have hcard := (hactive d j).mp hact
        omega
      obtain ⟨n₀, hn₀⟩ : (e d).Nonempty := (ncard_pos hfin_ed).mp (by omega)
      have hdisj_NI : Disjoint (N₁ ∪ I₁) (N₂ ∪ I₂) := by
        refine Disjoint.union_left (Disjoint.union_right hdisj_N ?_)
          (Disjoint.union_right ?_ hdisj_I)
        · rw [Set.disjoint_left]
          exact fun x hx₁ hx₂ => (hN₁_sub hx₁).2 (hΘ_bd (hI₂_sub hx₂).1)
        · rw [Set.disjoint_left]
          exact fun x hx₁ hx₂ => (hN₂_sub hx₂).2 (hΘ_bd (hI₁_sub hx₁).1)
      exact Set.disjoint_left.mp hdisj_NI (he₁ hn₀) (he₂ hn₀)

private theorem left_area_edges_disjoint_from_right_and_middle
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    (c : Set π.S)
    (hc_C : c ∈ π.Γ.C)
    (D₁ : Set (Set π.S))
    (D₂ : Set (Set π.S)) :
    let H₁ : Hypergraph α β := π.cellsUnion D₁
    let H₂ : Hypergraph α β := π.cellsUnion D₂
    let Hc : Hypergraph α β := π.cellGraph c
    (Disjoint D₁ D₂) →
    (c ∉ D₁) →
    Disjoint H₁.edgeSet (H₂ ∪ Hc).edgeSet := by
  intro H₁ H₂ Hc hdisj_D₁_D₂ hc_not_D₁
  rw [union_edgeSet]
  refine Disjoint.union_right ?_ ?_
  · rw [Set.disjoint_left]
    intro e₀ he₁ he₂
    change e₀ ∈ ⋃ d ∈ _, _ at he₁ he₂
    rw [mem_iUnion₂] at he₁ he₂
    rcases he₁ with ⟨d₁, ⟨hd₁, hd₁_C⟩, he₁⟩
    rcases he₂ with ⟨d₂, ⟨hd₂, hd₂_C⟩, he₂⟩
    exact Set.disjoint_left.mp
      (π.p1_disjoint d₁ hd₁_C d₂ hd₂_C (fun h => Set.disjoint_left.mp hdisj_D₁_D₂ hd₁
        (h ▸ hd₂)))
      he₁ he₂
  · rw [Set.disjoint_left]
    intro e₀ he₁ hec
    change e₀ ∈ ⋃ d ∈ _, _ at he₁
    rw [mem_iUnion₂] at he₁
    rcases he₁ with ⟨d₁, ⟨hd₁, hd₁_C⟩, he₁⟩
    exact Set.disjoint_left.mp
      (π.p1_disjoint d₁ hd₁_C c hc_C (fun h => hc_not_D₁ (h ▸ hd₁))) he₁ hec

private theorem left_area_shared_vertices_on_left_boundary
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (hΘ_bd : Θ ⊆ bd π.S)
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (activeFor : Set π.S → Fin (p + 1) → Prop)
    (e : Set π.S → Set π.S)
    (he : e = fun d => {n | n ∈ tilde d ∩ π.domγ ∧
      ∃ l, activeFor d l ∧ π.nodeVertex n ∈ (P l).walk.support})
    (c : Set π.S)
    (I₁ : Set π.S)
    (I₂ : Set π.S)
    (N₁ : Set π.S)
    (N₂ : Set π.S)
    (hc_C : c ∈ π.Γ.C)
    (hI₂_sub : I₂ ⊆ Θ ∩ discBd Δ)
    (hdisj_I : Disjoint I₁ I₂)
    (hN₁_sub : N₁ ⊆ (π.Γ.N ∩ Δ) \ bd π.S)
    (hdisj_N : Disjoint N₁ N₂)
    (hc_bd : (c ∩ bd π.S).Nonempty) :
    let B₁ : Set α := ⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n
    let B₂ : Set α := ⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n
    (∀ {n : π.S}, n ∈ π.Γ.N ∩ bd π.S → ∃ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty ∧ n
      ∈ tilde d) →
    (∀ {d : Set π.S}, d ∈ π.Γ.C → (d ∩ bd π.S).Nonempty → tilde d ⊆ π.Γ.N ∩ bd
      π.S) →
    (∀ {n m : π.S}, n ∉ bd π.S → n ∈ π.domγ → m ∈ π.Γ.N ∩ bd π.S →
      π.nodeVertex n ∉ π.borderPlus m) →
    ∀ (j : Fin (p + 1)),
    ∀ (Q : PathFromTo (π.areaGraph Δ).skeleton B₁ B₂),
    ({z | z ∈ Q.walk.support} ⊆ {z | z ∈ (P j).walk.support}) →
    let I_Δ : Set (Set π.S) := {d | d ∈ π.Γ.C ∧ d ⊆ Δ}
    let D₁ : Set (Set π.S) := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₁ ∨ ¬(d ∩
      bd π.S).Nonempty ∧ activeFor d j ∧ e d ⊆ N₁ ∪ I₁)}
    let D₂ : Set (Set π.S) := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂ ∨ ¬(d ∩
      bd π.S).Nonempty ∧ activeFor d j ∧ e d ⊆ N₂ ∪ I₂)}
    let H₁ : Hypergraph α β := π.cellsUnion D₁
    let H₂ : Hypergraph α β := π.cellsUnion D₂
    let Hc : Hypergraph α β := π.cellGraph c
    (Disjoint D₁ D₂) →
    (c ∉ D₁) →
    ∀ z ∈ Q.walk.support, z ∈ H₁.vertexSet → z ∈ (H₂ ∪ Hc).vertexSet ∨ z ∈ B₂ → z ∈ B₁ := by
  subst e
  let e (d : Set π.S) : Set π.S := {n | n ∈ tilde d ∩ π.domγ ∧
    ∃ l, activeFor d l ∧ π.nodeVertex n ∈ (P l).walk.support}
  intro B₁ B₂ hex_border_cell htilde_bd_sub hnot_bp_of_not_bd j Q hQ_sub I_Δ D₁ D₂ H₁ H₂ Hc
    hdisj_D₁_D₂ hc_not_D₁
    z hz_Q hz_H₁ hz_other
  have hz_P : z ∈ (P j).walk.support := hQ_sub hz_Q
  change z ∈ ⋃ d ∈ _, _ at hz_H₁
  rw [mem_iUnion₂] at hz_H₁
  rcases hz_H₁ with ⟨d₁, ⟨hd₁, hd₁_C⟩, hzd₁⟩
  have hex_d₂ : ∃ d₂ ∈ π.Γ.C, d₂ ≠ d₁ ∧ z ∈ (π.cellGraph d₂).vertexSet ∧
      (d₂ ∈ D₂ ∨ (d₂ ∩ bd π.S).Nonempty) := by
    rcases hz_other with (hz_H₂ | hz_Hc) | hz_B₂
    · change z ∈ ⋃ d ∈ _, _ at hz_H₂
      rw [mem_iUnion₂] at hz_H₂
      rcases hz_H₂ with ⟨d₂, ⟨hd₂, hd₂_C⟩, hzd₂⟩
      exact ⟨d₂, hd₂_C, fun h => Set.disjoint_left.mp hdisj_D₁_D₂ hd₁ (h ▸ hd₂),
        hzd₂, Or.inl hd₂⟩
    · exact ⟨c, hc_C, fun h => hc_not_D₁ (h ▸ hd₁), hz_Hc, Or.inr hc_bd⟩
    · rw [mem_iUnion₂] at hz_B₂
      rcases hz_B₂ with ⟨m', hm'_I₂, hzm'⟩
      have hm'_bd : m' ∈ π.Γ.N ∩ bd π.S := ⟨hm'_I₂.2, hΘ_bd (hI₂_sub hm'_I₂.1).1⟩
      obtain ⟨d₂, hd₂_C, hd₂_bd, hm'_d₂⟩ := hex_border_cell hm'_bd
      have hzd₂ : z ∈ (π.cellGraph d₂).vertexSet :=
        π.borderPlus_subset_cellGraph hd₂_C hd₂_bd hm'_d₂ hzm'
      have hd₂_ne : d₂ ≠ d₁ := by
        intro hEq
        rcases hd₁.2 with ⟨_, _, ht₁⟩ | ⟨hint, _, _⟩
        · exact Set.disjoint_left.mp hdisj_I (ht₁ (hEq ▸ hm'_d₂)) hm'_I₂.1
        · exact hint (hEq ▸ hd₂_bd)
      exact ⟨d₂, hd₂_C, hd₂_ne, hzd₂, Or.inr hd₂_bd⟩
  obtain ⟨d₂, hd₂_C, hd₂_ne, hzd₂, hd₂_kind⟩ := hex_d₂
  rcases hd₁.2 with ⟨hbd₁, _, ht₁⟩ | ⟨hint₁, hact₁, he₁⟩
  · obtain ⟨n, hn_t₁, hzn⟩ := π.p6_borderPlus hd₁_C hbd₁ hzd₁ ⟨d₂, hd₂_C, hd₂_ne, hzd₂⟩
    exact mem_biUnion ⟨ht₁ hn_t₁, π.Γ.tilde_subset_N hd₁_C hn_t₁⟩ hzn
  · obtain ⟨n, ⟨hn_t₁, hn_dom⟩, rfl⟩ :=
      π.p5 d₁ hd₁_C hint₁ z hzd₁ ⟨d₂, hd₂_C, hd₂_ne, hzd₂⟩
    have hn_ed₁ : n ∈ e d₁ := ⟨⟨hn_t₁, hn_dom⟩, j, hact₁, hz_P⟩
    rcases he₁ hn_ed₁ with hn_N₁ | hn_I₁
    · exfalso
      have hn_not_bd : n ∉ bd π.S := (hN₁_sub hn_N₁).2
      rcases hd₂_kind with hd₂_D₂ | hd₂_bd
      · rcases hd₂_D₂.2 with ⟨hbd₂, _, _⟩ | ⟨hint₂, hact₂, he₂⟩
        · obtain ⟨m', hm'_t₂, hnm'⟩ :=
            π.p6_borderPlus hd₂_C hbd₂ hzd₂ ⟨d₁, hd₁_C, hd₂_ne.symm, hzd₁⟩
          exact hnot_bp_of_not_bd hn_not_bd hn_dom
            (htilde_bd_sub hd₂_C hbd₂ hm'_t₂) hnm'
        · obtain ⟨n', ⟨hn'_t₂, hn'_dom⟩, hEq_nv⟩ :=
            π.p5 d₂ hd₂_C hint₂ (π.nodeVertex n) hzd₂ ⟨d₁, hd₁_C, hd₂_ne.symm, hzd₁⟩
          have hn_eq : n' = n := π.nodeVertex_injOn hn'_dom hn_dom hEq_nv
          have hn_ed₂ : n ∈ e d₂ := ⟨⟨hn_eq ▸ hn'_t₂, hn_dom⟩, j, hact₂, hz_P⟩
          rcases he₂ hn_ed₂ with hn_N₂ | hn_I₂
          · exact Set.disjoint_left.mp hdisj_N hn_N₁ hn_N₂
          · exact hn_not_bd (hΘ_bd (hI₂_sub hn_I₂).1)
      · obtain ⟨m', hm'_t₂, hnm'⟩ :=
          π.p6_borderPlus hd₂_C hd₂_bd hzd₂ ⟨d₁, hd₁_C, hd₂_ne.symm, hzd₁⟩
        exact hnot_bp_of_not_bd hn_not_bd hn_dom
          (htilde_bd_sub hd₂_C hd₂_bd hm'_t₂) hnm'
    · exact mem_biUnion ⟨hn_I₁, π.Γ.tilde_subset_N hd₁_C hn_t₁⟩ (Or.inr ⟨hn_dom, rfl⟩)

private theorem right_area_shared_vertices_on_right_boundary
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (hΘ_bd : Θ ⊆ bd π.S)
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (activeFor : Set π.S → Fin (p + 1) → Prop)
    (e : Set π.S → Set π.S)
    (he : e = fun d => {n | n ∈ tilde d ∩ π.domγ ∧
      ∃ l, activeFor d l ∧ π.nodeVertex n ∈ (P l).walk.support})
    (c : Set π.S)
    (I₁ : Set π.S)
    (I₂ : Set π.S)
    (N₂ : Set π.S)
    (hc_C : c ∈ π.Γ.C)
    (hI₁_sub : I₁ ⊆ Θ ∩ discBd Δ)
    (hdisj_I : Disjoint I₁ I₂)
    (hN₂_sub : N₂ ⊆ (π.Γ.N ∩ Δ) \ bd π.S)
    (hc_bd : (c ∩ bd π.S).Nonempty) :
    let B₁ : Set α := ⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n
    let B₂ : Set α := ⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n
    (∀ {n : π.S}, n ∈ π.Γ.N ∩ bd π.S → ∃ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty ∧ n
      ∈ tilde d) →
    (∀ {d : Set π.S}, d ∈ π.Γ.C → (d ∩ bd π.S).Nonempty → tilde d ⊆ π.Γ.N ∩ bd
      π.S) →
    (∀ {n m : π.S}, n ∉ bd π.S → n ∈ π.domγ → m ∈ π.Γ.N ∩ bd π.S →
      π.nodeVertex n ∉ π.borderPlus m) →
    ∀ (j : Fin (p + 1)),
    ∀ (Q : PathFromTo (π.areaGraph Δ).skeleton B₁ B₂),
    ({z | z ∈ Q.walk.support} ⊆ {z | z ∈ (P j).walk.support}) →
    let I_Δ : Set (Set π.S) := {d | d ∈ π.Γ.C ∧ d ⊆ Δ}
    let D₂ : Set (Set π.S) := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂ ∨ ¬(d ∩
      bd π.S).Nonempty ∧ activeFor d j ∧ e d ⊆ N₂ ∪ I₂)}
    let H₂ : Hypergraph α β := π.cellsUnion D₂
    let Hc : Hypergraph α β := π.cellGraph c
    (c ∉ D₂) →
    ∀ z ∈ Q.walk.support, z ∈ H₂.vertexSet → z ∈ Hc.vertexSet ∨ z ∈ B₁ → z ∈ B₂ := by
  subst e
  let e (d : Set π.S) : Set π.S := {n | n ∈ tilde d ∩ π.domγ ∧
    ∃ l, activeFor d l ∧ π.nodeVertex n ∈ (P l).walk.support}
  intro B₁ B₂ hex_border_cell htilde_bd_sub hnot_bp_of_not_bd j Q hQ_sub I_Δ D₂ H₂ Hc hc_not_D₂
    z hz_Q hz_H₂ hz_other
  have hz_P : z ∈ (P j).walk.support := hQ_sub hz_Q
  change z ∈ ⋃ d ∈ _, _ at hz_H₂
  rw [mem_iUnion₂] at hz_H₂
  rcases hz_H₂ with ⟨d₂, ⟨hd₂, hd₂_C⟩, hzd₂⟩
  have hex_d₁ : ∃ d₁ ∈ π.Γ.C, d₁ ≠ d₂ ∧ z ∈ (π.cellGraph d₁).vertexSet ∧
      (d₁ ∩ bd π.S).Nonempty := by
    rcases hz_other with hz_Hc | hz_B₁
    · exact ⟨c, hc_C, fun h => hc_not_D₂ (h ▸ hd₂), hz_Hc, hc_bd⟩
    · rw [mem_iUnion₂] at hz_B₁
      rcases hz_B₁ with ⟨m', hm'_I₁, hzm'⟩
      have hm'_bd : m' ∈ π.Γ.N ∩ bd π.S := ⟨hm'_I₁.2, hΘ_bd (hI₁_sub hm'_I₁.1).1⟩
      obtain ⟨d₁, hd₁_C, hd₁_bd, hm'_d₁⟩ := hex_border_cell hm'_bd
      have hzd₁ : z ∈ (π.cellGraph d₁).vertexSet :=
        π.borderPlus_subset_cellGraph hd₁_C hd₁_bd hm'_d₁ hzm'
      have hd₁_ne : d₁ ≠ d₂ := by
        intro hEq
        rcases hd₂.2 with ⟨_, _, ht₂⟩ | ⟨hint, _, _⟩
        · exact Set.disjoint_left.mp hdisj_I hm'_I₁.1 (ht₂ (hEq ▸ hm'_d₁))
        · exact hint (hEq ▸ hd₁_bd)
      exact ⟨d₁, hd₁_C, hd₁_ne, hzd₁, hd₁_bd⟩
  obtain ⟨d₁, hd₁_C, hd₁_ne, hzd₁, hd₁_bd⟩ := hex_d₁
  rcases hd₂.2 with ⟨hbd₂, _, ht₂⟩ | ⟨hint₂, hact₂, he₂⟩
  · obtain ⟨n, hn_t₂, hzn⟩ := π.p6_borderPlus hd₂_C hbd₂ hzd₂ ⟨d₁, hd₁_C, hd₁_ne, hzd₁⟩
    exact mem_biUnion ⟨ht₂ hn_t₂, π.Γ.tilde_subset_N hd₂_C hn_t₂⟩ hzn
  · obtain ⟨n, ⟨hn_t₂, hn_dom⟩, rfl⟩ :=
      π.p5 d₂ hd₂_C hint₂ z hzd₂ ⟨d₁, hd₁_C, hd₁_ne, hzd₁⟩
    have hn_ed₂ : n ∈ e d₂ := ⟨⟨hn_t₂, hn_dom⟩, j, hact₂, hz_P⟩
    rcases he₂ hn_ed₂ with hn_N₂ | hn_I₂
    · exfalso
      have hn_not_bd : n ∉ bd π.S := (hN₂_sub hn_N₂).2
      obtain ⟨m', hm'_t₁, hnm'⟩ :=
        π.p6_borderPlus hd₁_C hd₁_bd hzd₁ ⟨d₂, hd₂_C, hd₁_ne.symm, hzd₂⟩
      exact hnot_bp_of_not_bd hn_not_bd hn_dom
        (htilde_bd_sub hd₁_C hd₁_bd hm'_t₁) hnm'
    · exact mem_biUnion ⟨hn_I₂, π.Γ.tilde_subset_N hd₂_C hn_t₂⟩ (Or.inr ⟨hn_dom, rfl⟩)

private theorem boundary_subwalk_avoids_left_area
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    (B₁ : Set α)
    (B₂ : Set α)
    (Q : PathFromTo (π.areaGraph Δ).skeleton B₁ B₂)
    (hst : ¬Q.first = Q.last)
    (hQ_no_inter : ∀ z ∈ Q.walk.support, z ∉ B₁ ∩ B₂)
    (H₁ : Hypergraph α β)
    (H₂ : Hypergraph α β)
    (Hc : Hypergraph α β)
    (hdisjE_1_2c : Disjoint H₁.edgeSet (H₂ ∪ Hc).edgeSet)
    (w₀ : (H₁ ∪ (H₂ ∪ Hc)).skeleton.Walk Q.first Q.last)
    (hw₀_sup : w₀.support = Q.walk.support)
    (hw₀_path : w₀.IsPath)
    (hH₁_boundary : ∀ z ∈ Q.walk.support, z ∈ H₁.vertexSet → z ∈ (H₂ ∪ Hc).vertexSet ∨ z ∈ B₂ → z
      ∈ B₁)
    (hint_w₀ : ∀ z ∈ w₀.support, z ≠ Q.first → z ≠ Q.last → z ∉ H₁.vertexSet ∩ (H₂ ∪
      Hc).vertexSet) :
    ∃ w₂c : (H₂ ∪ Hc).skeleton.Walk Q.first Q.last, w₂c.support = Q.walk.support := by
  rcases walk_in_left_or_right_of_internal_disjoint hdisjE_1_2c w₀ hw₀_path hint_w₀ with
    ⟨w₁, _⟩ | ⟨w₂c, hw₂c_sup⟩
  · exfalso
    have ht_H₁ : Q.last ∈ H₁.vertexSet :=
      (walk_endpoints_mem_vertexSet_of_ne w₁ hst).2
    have ht_B₁ : Q.last ∈ B₁ :=
      hH₁_boundary Q.last (SimpleGraph.Walk.end_mem_support Q.walk) ht_H₁
        (Or.inr Q.last_mem)
    exact hQ_no_inter Q.last (SimpleGraph.Walk.end_mem_support Q.walk) ⟨ht_B₁, Q.last_mem⟩
  · exact ⟨w₂c, hw₂c_sup.trans hw₀_sup⟩

private theorem boundary_subwalk_lies_in_middle_cell
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    (B₁ : Set α)
    (B₂ : Set α)
    (Q : PathFromTo (π.areaGraph Δ).skeleton B₁ B₂)
    (hst : ¬Q.first = Q.last)
    (hQ_no_inter : ∀ z ∈ Q.walk.support, z ∉ B₁ ∩ B₂)
    (H₂ : Hypergraph α β)
    (Hc : Hypergraph α β)
    (hdisjE_2_c : Disjoint H₂.edgeSet Hc.edgeSet)
    (hH₂_boundary : ∀ z ∈ Q.walk.support, z ∈ H₂.vertexSet → z ∈ Hc.vertexSet ∨ z ∈ B₁ → z ∈ B₂)
    (w₂c : (H₂ ∪ Hc).skeleton.Walk Q.first Q.last)
    (hw₂c_sup : w₂c.support = Q.walk.support)
    (hw₂c_path : w₂c.IsPath)
    (hint_w₂c : ∀ z ∈ w₂c.support, z ≠ Q.first → z ≠ Q.last → z ∉ H₂.vertexSet ∩ Hc.vertexSet) :
    ∃ wc : Hc.skeleton.Walk Q.first Q.last, wc.support = Q.walk.support := by
  rcases walk_in_left_or_right_of_internal_disjoint hdisjE_2_c w₂c hw₂c_path hint_w₂c with
    ⟨w₂, _⟩ | ⟨wc, hwc_sup⟩
  · exfalso
    have hs_H₂ : Q.first ∈ H₂.vertexSet :=
      (walk_endpoints_mem_vertexSet_of_ne w₂ hst).1
    have hs_B₂ : Q.first ∈ B₂ :=
      hH₂_boundary Q.first (SimpleGraph.Walk.start_mem_support Q.walk) hs_H₂
        (Or.inr Q.first_mem)
    exact hQ_no_inter Q.first (SimpleGraph.Walk.start_mem_support Q.walk) ⟨Q.first_mem, hs_B₂⟩
  · exact ⟨wc, hwc_sup.trans hw₂c_sup⟩

private theorem boundary_paths_restrict_to_middle_cell
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (hΘ : Θ ∈ cuffs π.S)
    (hn₁ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂ : n₂ ∈ π.Γ.N ∩ Θ)
    (hinter_sub : ∀ n ∈ π.Γ.N ∩ (Θ ∩ discBd Δ), π.borderPlus n₁ ∩ π.borderPlus n₂ ⊆ π.borderPlus
      n)
    (hΘ_bd : Θ ⊆ bd π.S)
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂)) :
    let activeFor : Set π.S → Fin (p + 1) → Prop := fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z
      ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard
    let e : Set π.S → Set π.S := fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, activeFor d l ∧
      π.nodeVertex n ∈ (P l).walk.support}
    ∀ (P_mark : π.S → Prop),
    ∀ (m₁ : π.S),
    ∀ (m₂ : π.S),
    ∀ (c : Set π.S),
    ∀ (I₁ : Set π.S),
    ∀ (I₂ : Set π.S),
    ∀ (N₁ : Set π.S),
    ∀ (N₂ : Set π.S),
    (m₁ ∈ π.Γ.N ∩ (Θ ∩ discBd Δ)) →
    (m₂ ∈ π.Γ.N ∩ (Θ ∩ discBd Δ)) →
    (m₁ ≠ m₂) →
    (P_mark m₁) →
    (¬P_mark m₂) →
    (c ∈ π.Γ.C) →
    (c ⊆ Δ) →
    ((c ∩ Θ).Nonempty) →
    (tilde c = {m₁, m₂}) →
    (I₁ ⊆ Θ ∩ discBd Δ) →
    (I₂ ⊆ Θ ∩ discBd Δ) →
    (Disjoint I₁ I₂) →
    (m₁ ∈ I₁) →
    (m₂ ∈ I₂) →
    (N₁ ⊆ (π.Γ.N ∩ Δ) \ bd π.S) →
    (N₂ ⊆ (π.Γ.N ∩ Δ) \ bd π.S) →
    (Disjoint N₁ N₂) →
    (∀ n ∈ I₁ ∩ π.Γ.N, ∀ n' ∈ I₂ ∩ π.Γ.N, (n ≠ n₁ → n ≠ m₁ → GM19.InOrderOn Θ n₁ n m₁
      n') ∧ (m₁ ≠ n₁ → n' ≠ n₂ → GM19.InOrderOn Θ n₁ m₁ n' n₂) ∧ (n' ≠ m₂ → n' ≠ n₂ →
      GM19.InOrderOn Θ n m₂ n' n₂) ∧ (n ≠ n₁ → m₂ ≠ n₂ → GM19.InOrderOn Θ n₁ n m₂ n₂)) →
    (∀ d ∈ π.Γ.C, d ⊆ Δ → (d ∩ bd π.S).Nonempty → d ≠ c → tilde d ⊆ I₁ ∨ tilde d
      ⊆ I₂) →
    (∀ d ∈ π.Γ.C, d ⊆ Δ → ¬(d ∩ bd π.S).Nonempty → e d ⊆ N₁ ∪ I₁ ∨ e d ⊆ N₂ ∪ I₂) →
    ∀ (c₁_end : Set π.S),
    (c₁_end ∈ π.Γ.C) →
    (c₁_end ⊆ Δ) →
    ((c₁_end ∩ bd π.S).Nonempty) →
    (n₁ ∈ tilde c₁_end) →
    ∀ (c₂_end : Set π.S),
    (c₂_end ∈ π.Γ.C) →
    (c₂_end ⊆ Δ) →
    ((c₂_end ∩ bd π.S).Nonempty) →
    (n₂ ∈ tilde c₂_end) →
    ((c ∩ bd π.S).Nonempty) →
    (π.borderPlus n₁ ⊆ (⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n)) →
    (π.borderPlus n₂ ⊆ (⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n)) →
    (π.borderPlus m₁ ⊆ (⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n)) →
    (π.borderPlus m₂ ⊆ (⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n)) →
    (∀ {n : π.S}, n ∈ π.Γ.N ∩ bd π.S → ∃ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty ∧ n
      ∈ tilde d) →
    (∀ {d : Set π.S}, d ∈ π.Γ.C → (d ∩ bd π.S).Nonempty → tilde d ⊆ π.Γ.N ∩ bd
      π.S) →
    (∀ {n m : π.S}, n ∉ bd π.S → n ∈ π.domγ → m ∈ π.Γ.N ∩ bd π.S →
      π.nodeVertex n ∉ π.borderPlus m) →
    ∀ j : Fin (p + 1), ∃ Q' : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus
      m₂), {z | z ∈ Q'.walk.support} ⊆ {z | z ∈ (P j).walk.support} ∧ Q'.first ∈ (⋃ n ∈ I₁ ∩
      π.Γ.N, π.borderPlus n) ∧ Q'.last ∈ (⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n) := by
  intro activeFor e P_mark m₁ m₂ c I₁ I₂ N₁ N₂ hm₁_mem hm₂_mem hm_ne hP_m₁ hP_m₂ hc_C hc_Δ hc_Θ
    htilde_c hI₁_sub hI₂_sub hdisj_I hm₁_I₁ hm₂_I₂ hN₁_sub hN₂_sub hdisj_N hord_I hborder_split
    hint_split c₁_end hc₁_C hc₁_Δ hc₁_bd hn₁_c₁ c₂_end hc₂_C hc₂_Δ hc₂_bd hn₂_c₂ hc_bd hbp₁_sub_B₁
    hbp₂_sub_B₂ hbp_m₁_sub_B₁ hbp_m₂_sub_B₂ hex_border_cell htilde_bd_sub hnot_bp_of_not_bd
  let B₁ := ⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n
  let B₂ := ⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n
  intro j
  let Pj_B : PathFromTo (π.areaGraph Δ).skeleton B₁ B₂ :=
    ⟨(P j).first, (P j).last, (P j).walk, (P j).isPath,
     hbp₁_sub_B₁ (P j).first_mem, hbp₂_sub_B₂ (P j).last_mem⟩
  obtain ⟨Q, hQ_sub, hQ_int, hQ_inter⟩ := exists_minimal_subpath_from_to Pj_B
  by_cases hst : Q.first = Q.last
  · exact common_boundary_vertex_yields_trivial_path (α := α) (β := β) (G := G) π (Θ := Θ) (Δ :=
      Δ) (n₁ := n₁) (n₂ := n₂) (p := p) hΘ hn₁ hn₂ hinter_sub P m₁ m₂ c I₁ I₂ hm₁_mem hm₂_mem
      hI₁_sub hI₂_sub hord_I j Q hQ_sub hst
  · have hQ_no_inter : ∀ z ∈ Q.walk.support, z ∉ B₁ ∩ B₂ := hQ_inter hst
    let I_Δ : Set (Set π.S) := {d ∈ π.Γ.C | d ⊆ Δ}
    have hcell_active : ∀ {d : Set π.S}, d ∈ I_Δ → ¬ (d ∩ bd π.S).Nonempty →
        ∀ {x y : α}, x ∈ (P j).walk.support → y ∈ (P j).walk.support → x ≠ y →
        ∀ {e₀ : β}, (π.cellGraph d).Inc e₀ x → (π.cellGraph d).Inc e₀ y →
        activeFor d j := by
      intro d
      exact interior_cell_active_of_path_edge (α := α) (β := β) (G := G) π (Δ :=
        Δ) (n₁ := n₁) (n₂ := n₂) (p := p) P c₁_end hc₁_C hc₁_Δ hc₁_bd hn₁_c₁ c₂_end
        hc₂_C hc₂_Δ hc₂_bd hn₂_c₂ j (d := d)
    let D₁ : Set (Set π.S) :=
      {d ∈ I_Δ | ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₁) ∨
        (¬ (d ∩ bd π.S).Nonempty ∧ activeFor d j ∧ e d ⊆ N₁ ∪ I₁)}
    let D₂ : Set (Set π.S) :=
      {d ∈ I_Δ | ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂) ∨
        (¬ (d ∩ bd π.S).Nonempty ∧ activeFor d j ∧ e d ⊆ N₂ ∪ I₂)}
    let H₁ := π.cellsUnion D₁
    let H₂ := π.cellsUnion D₂
    let Hc := π.cellGraph c
    have hdisj_D₁_D₂ : Disjoint D₁ D₂ := by
      exact opposite_side_cells_disjoint (α := α) (β := β) (G := G) π (Θ := Θ) (Δ := Δ) (n₁ :=
        n₁) (n₂ := n₂) (p := p) hΘ_bd P activeFor (fun _ _ => Iff.rfl) e rfl c I₁ I₂ N₁ N₂ hI₁_sub
          hI₂_sub hdisj_I
        hN₁_sub hN₂_sub hdisj_N j
    have hc_not_D₁ : c ∉ D₁ := by
      rintro ⟨_, ⟨_, hne_c, _⟩ | ⟨hint, _, _⟩⟩
      · exact hne_c rfl
      · exact hint hc_bd
    have hc_not_D₂ : c ∉ D₂ := by
      rintro ⟨_, ⟨_, hne_c, _⟩ | ⟨hint, _, _⟩⟩
      · exact hne_c rfl
      · exact hint hc_bd
    have hdisjE_1_2c : Disjoint H₁.edgeSet (H₂ ∪ Hc).edgeSet := by
      exact left_area_edges_disjoint_from_right_and_middle (α := α) (β := β) (G := G) π c hc_C
        D₁ D₂    hdisj_D₁_D₂ hc_not_D₁
    have hdisjE_2_c : Disjoint H₂.edgeSet Hc.edgeSet := by
      rw [Set.disjoint_left]
      intro e₀ he₂ hec
      change e₀ ∈ ⋃ d ∈ _, _ at he₂
      rw [mem_iUnion₂] at he₂
      rcases he₂ with ⟨d₂, ⟨hd₂, hd₂_C⟩, he₂⟩
      exact Set.disjoint_left.mp
        (π.p1_disjoint d₂ hd₂_C c hc_C (fun h => hc_not_D₂ (h ▸ hd₂))) he₂ hec
    have hQ_lift_all : ∃ w₀ : (H₁ ∪ (H₂ ∪ Hc)).skeleton.Walk Q.first Q.last,
        w₀.support = Q.walk.support := by
      exact walk_lifts_to_three_areas π (fun d ↦ activeFor d j) e hborder_split hint_split
        Q.walk hQ_sub hcell_active
    obtain ⟨w₀, hw₀_sup⟩ := hQ_lift_all
    have hw₀_path : w₀.IsPath := by
      rw [SimpleGraph.Walk.isPath_def, hw₀_sup]
      exact Q.isPath.support_nodup
    have hH₁_boundary : ∀ z ∈ Q.walk.support, z ∈ H₁.vertexSet →
        (z ∈ (H₂ ∪ Hc).vertexSet ∨ z ∈ B₂) → z ∈ B₁ := by
      exact left_area_shared_vertices_on_left_boundary (α := α) (β := β) (G := G) π (Θ := Θ) (Δ
        := Δ) (n₁ := n₁) (n₂ := n₂) (p := p) hΘ_bd P activeFor e rfl c I₁ I₂ N₁ N₂ hc_C hI₂_sub
        hdisj_I hN₁_sub hdisj_N hc_bd   hex_border_cell htilde_bd_sub hnot_bp_of_not_bd j
        Q hQ_sub       hdisj_D₁_D₂ hc_not_D₁
    have hH₂_boundary : ∀ z ∈ Q.walk.support, z ∈ H₂.vertexSet →
        (z ∈ Hc.vertexSet ∨ z ∈ B₁) → z ∈ B₂ := by
      exact right_area_shared_vertices_on_right_boundary (α := α) (β := β) (G := G) π (Θ := Θ)
        (Δ := Δ) (n₁ := n₁) (n₂ := n₂) (p := p) hΘ_bd P activeFor e rfl c I₁ I₂ N₂ hc_C hI₁_sub
        hdisj_I hN₂_sub hc_bd   hex_border_cell htilde_bd_sub hnot_bp_of_not_bd j Q
        hQ_sub     hc_not_D₂
    have hint_w₀ : ∀ z ∈ w₀.support, z ≠ Q.first → z ≠ Q.last →
        z ∉ H₁.vertexSet ∩ (H₂ ∪ Hc).vertexSet := by
      intro z hz hzf hzl ⟨hz₁, hz₂⟩
      exact hQ_int z (hw₀_sup ▸ hz) hzf hzl
        (Or.inl (hH₁_boundary z (hw₀_sup ▸ hz) hz₁ (Or.inl hz₂)))
    have hw_2c : ∃ w₂c : (H₂ ∪ Hc).skeleton.Walk Q.first Q.last,
        w₂c.support = Q.walk.support := by
      exact boundary_subwalk_avoids_left_area (α := α) (β := β) (G := G) π (Δ := Δ) B₁ B₂ Q hst
        hQ_no_inter H₁ H₂ Hc hdisjE_1_2c w₀ hw₀_sup hw₀_path hH₁_boundary hint_w₀
    obtain ⟨w₂c, hw₂c_sup⟩ := hw_2c
    have hw₂c_path : w₂c.IsPath := by
      rw [SimpleGraph.Walk.isPath_def, hw₂c_sup]
      exact Q.isPath.support_nodup
    have hint_w₂c : ∀ z ∈ w₂c.support, z ≠ Q.first → z ≠ Q.last →
        z ∉ H₂.vertexSet ∩ Hc.vertexSet := by
      intro z hz hzf hzl ⟨hz₂, hzc⟩
      exact hQ_int z (hw₂c_sup ▸ hz) hzf hzl
        (Or.inr (hH₂_boundary z (hw₂c_sup ▸ hz) hz₂ (Or.inl hzc)))
    have hwc : ∃ wc : Hc.skeleton.Walk Q.first Q.last, wc.support = Q.walk.support := by
      exact boundary_subwalk_lies_in_middle_cell (α := α) (β := β) (G := G) π (Δ := Δ) B₁ B₂ Q
        hst hQ_no_inter H₂ Hc hdisjE_2_c hH₂_boundary w₂c hw₂c_sup hw₂c_path hint_w₂c
    obtain ⟨wc, hwc_sup⟩ := hwc
    have hwc_path : wc.IsPath := by
      rw [SimpleGraph.Walk.isPath_def, hwc_sup]
      exact Q.isPath.support_nodup
    obtain ⟨hs_Hc, ht_Hc⟩ := walk_endpoints_mem_vertexSet_of_ne wc hst
    have hs_m₁ : Q.first ∈ π.borderPlus m₁ := by
      have hs_B₁ := Q.first_mem
      rw [mem_iUnion₂] at hs_B₁
      rcases hs_B₁ with ⟨n, hn_I₁, hsn⟩
      by_cases hnm₁ : n = m₁
      · exact hnm₁ ▸ hsn
      · have hn_bd : n ∈ π.Γ.N ∩ bd π.S := ⟨hn_I₁.2, hΘ_bd (hI₁_sub hn_I₁.1).1⟩
        obtain ⟨d₁, hd₁_C, hd₁_bd, hn_d₁⟩ := hex_border_cell hn_bd
        have hsd₁ : Q.first ∈ (π.cellGraph d₁).vertexSet :=
          π.borderPlus_subset_cellGraph hd₁_C hd₁_bd hn_d₁ hsn
        have hd₁_ne_c : d₁ ≠ c := by
          intro hEq
          have hn_tc : n ∈ ({m₁, m₂} : Set π.S) := htilde_c ▸ hEq ▸ hn_d₁
          rcases hn_tc with rfl | rfl
          · exact hnm₁ rfl
          · exact Set.disjoint_left.mp hdisj_I hn_I₁.1 hm₂_I₂
        obtain ⟨m', hm'_tc, hsm'⟩ :=
          π.p6_borderPlus hc_C hc_bd hs_Hc ⟨d₁, hd₁_C, hd₁_ne_c, hsd₁⟩
        rw [htilde_c] at hm'_tc
        rcases hm'_tc with rfl | rfl
        · exact hsm'
        · exfalso
          exact hQ_no_inter Q.first (SimpleGraph.Walk.start_mem_support Q.walk)
            ⟨Q.first_mem, hbp_m₂_sub_B₂ hsm'⟩
    have ht_m₂ : Q.last ∈ π.borderPlus m₂ := by
      have ht_B₂ := Q.last_mem
      rw [mem_iUnion₂] at ht_B₂
      rcases ht_B₂ with ⟨n', hn'_I₂, htn'⟩
      by_cases hn'm₂ : n' = m₂
      · exact hn'm₂ ▸ htn'
      · have hn'_bd : n' ∈ π.Γ.N ∩ bd π.S := ⟨hn'_I₂.2, hΘ_bd (hI₂_sub hn'_I₂.1).1⟩
        obtain ⟨d₂, hd₂_C, hd₂_bd, hn'_d₂⟩ := hex_border_cell hn'_bd
        have htd₂ : Q.last ∈ (π.cellGraph d₂).vertexSet :=
          π.borderPlus_subset_cellGraph hd₂_C hd₂_bd hn'_d₂ htn'
        have hd₂_ne_c : d₂ ≠ c := by
          intro hEq
          have hn'_tc : n' ∈ ({m₁, m₂} : Set π.S) := htilde_c ▸ hEq ▸ hn'_d₂
          rcases hn'_tc with rfl | rfl
          · exact Set.disjoint_left.mp hdisj_I hm₁_I₁ hn'_I₂.1
          · exact hn'm₂ rfl
        obtain ⟨m', hm'_tc, htm'⟩ :=
          π.p6_borderPlus hc_C hc_bd ht_Hc ⟨d₂, hd₂_C, hd₂_ne_c, htd₂⟩
        rw [htilde_c] at hm'_tc
        rcases hm'_tc with rfl | rfl
        · exfalso
          exact hQ_no_inter Q.last (SimpleGraph.Walk.end_mem_support Q.walk)
            ⟨hbp_m₁_sub_B₁ htm', Q.last_mem⟩
        · exact htm'
    refine ⟨⟨Q.first, Q.last, wc, hwc_path, hs_m₁, ht_m₂⟩, ?_, Q.first_mem, Q.last_mem⟩
    intro z hz
    exact hQ_sub (hwc_sup ▸ hz)

private theorem interior_cell_active_for_unique_path
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (hP_disj : Pairwise fun i j => Disjoint {z | z ∈ (P i).walk.support} {z | z ∈ (P
      j).walk.support}) :
    let activeFor : Set π.S → Fin (p + 1) → Prop := fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z
      ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard
    ∀ {d : Set π.S}, d ∈ π.Γ.C → ∀ {l₁ l₂ : Fin (p + 1)}, activeFor d l₁ → activeFor d l₂ → l₁ =
      l₂ := by
  intro activeFor d hd l₁ l₂ h₁ h₂
  by_contra hne_l
  let S₁ := {z ∈ (P l₁).walk.support | z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}
  let S₂ := {z ∈ (P l₂).walk.support | z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}
  have hdisj_S : Disjoint S₁ S₂ :=
    (hP_disj hne_l).mono (fun _ hz => hz.1) (fun _ hz => hz.1)
  have hfin_img : (π.nodeVertex '' (tilde d ∩ π.domγ)).Finite :=
    ((π.Γ.finite_tilde_cell hd).inter_of_left _).image _
  have hsub_S : S₁ ∪ S₂ ⊆ π.nodeVertex '' (tilde d ∩ π.domγ) := by
    rintro z (hz | hz) <;> exact hz.2
  have h1 : (S₁ ∪ S₂).ncard = S₁.ncard + S₂.ncard :=
    ncard_union_eq hdisj_S (hfin_img.subset fun _ hz => hz.2) (hfin_img.subset fun _ hz => hz.2)
  have h2 : (S₁ ∪ S₂).ncard ≤ (π.nodeVertex '' (tilde d ∩ π.domγ)).ncard :=
    ncard_le_ncard hsub_S hfin_img
  have h3 : (π.nodeVertex '' (tilde d ∩ π.domγ)).ncard ≤ (tilde d ∩ π.domγ).ncard :=
    ncard_image_le ((π.Γ.finite_tilde_cell hd).inter_of_left _)
  have h4 : (tilde d ∩ π.domγ).ncard ≤ (tilde d).ncard :=
    ncard_le_ncard inter_subset_left (π.Γ.finite_tilde_cell hd)
  have h5 : (tilde d).ncard ≤ 3 := π.Γ.ncard_tilde_cell_le hd
  change 2 ≤ S₁.ncard at h₁
  change 2 ≤ S₂.ncard at h₂
  omega

private theorem assigned_cell_nodes_preserve_path_membership
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (hP_disj : Pairwise fun i j => Disjoint {z | z ∈ (P i).walk.support} {z | z ∈ (P
      j).walk.support})
    (j₀ : Fin (p + 1)) :
    let activeFor : Set π.S → Fin (p + 1) → Prop := fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z
      ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}.ncard
    let e : Set π.S → Set π.S := fun d => {n | n ∈ tilde d ∩ π.domγ ∧ ∃ l, activeFor d l ∧
      π.nodeVertex n ∈ (P l).walk.support}
    let P_mark : π.S → Prop := fun m => m ∈ π.domγ ∧ π.nodeVertex m ∈ (P j₀).walk.support
    (∀ {d : Set π.S}, d ∈ π.Γ.C → ∀ {l₁ l₂ : Fin (p + 1)}, activeFor d l₁ →
      activeFor d l₂ → l₁ = l₂) →
    ∀ d ∈ π.Γ.C, d ⊆ Δ → ¬(d ∩ bd π.S).Nonempty → e d ⊆ tilde d ∧ (e d = ∅ ∨ 2 ≤ (e d).ncard) ∧ ∀
      x ∈ e d, ∀ y ∈ e d, P_mark x → P_mark y := by
  intro activeFor e P_mark hact_unique d hd _ _
  refine ⟨fun _ hn => hn.1.1, ?_, ?_⟩
  · by_cases hne_e : (e d).Nonempty
    · right
      rcases hne_e with ⟨n₀, _, l, hact_l, _⟩
      have hsub_img : {z ∈ (P l).walk.support | z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)} ⊆
          π.nodeVertex '' e d := by
        rintro z ⟨hz_sup, n, hn_td, rfl⟩
        exact ⟨n, ⟨hn_td, l, hact_l, hz_sup⟩, rfl⟩
      have hfin_ed : (e d).Finite := (π.Γ.finite_tilde_cell hd).subset fun _ hn => hn.1.1
      have hle₁ := ncard_le_ncard hsub_img (hfin_ed.image _)
      have hle₂ := ncard_image_le (f := π.nodeVertex) hfin_ed
      change 2 ≤ ({z ∈ (P l).walk.support | z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}).ncard
        at hact_l
      omega
    · exact Or.inl (not_nonempty_iff_eq_empty.mp hne_e)
  · rintro x ⟨_, l₁, hact₁, hx_l₁⟩ y ⟨⟨_, hy_dom⟩, l₂, hact₂, hy_l₂⟩ ⟨_, hx_j₀⟩
    have hl₁_eq : l₁ = l₂ := hact_unique hd hact₁ hact₂
    have hl₁_j₀ : l₁ = j₀ := by
      by_contra hne_l
      exact Set.disjoint_left.mp (hP_disj hne_l) hx_l₁ hx_j₀
    exact ⟨hy_dom, hl₁_j₀ ▸ hl₁_eq ▸ hy_l₂⟩

/-- Graph Minors XVII, (7.3) without the hypothesis $F \cap N(\Gamma) = \{n_1, n_2\}$ (using
`normalIArcDiscRegion_of_boundary`). Used in the proof of (11.3) on page 193. -/
private theorem theorem_7_3_no_FN
    {α : Type u} {β : Type v} {G : Hypergraph α β} (π : Portrayal G)
    {Θ F Δ : Set π.S} {n₁ n₂ : π.S} {p : ℕ}
    (hΘ : Θ ∈ cuffs π.S) (hn₁ : n₁ ∈ π.Γ.N ∩ Θ) (hn₂ : n₂ ∈ π.Γ.N ∩ Θ) (hne : n₁ ≠ n₂)
    (hnorm : π.Γ.IsNormal F) (hF : IsLineWithEnds F n₁ n₂)
    (hFbd : F ∩ bd π.S = {n₁, n₂})
    (hΔ : IsClosedDisc Δ) (hF_bd : F ⊆ discBd Δ) (hbd_sub : discBd Δ ⊆ F ∪ Θ)
    (hinter_sub : ∀ n ∈ π.Γ.N ∩ (Θ ∩ discBd Δ),
      π.borderPlus n₁ ∩ π.borderPlus n₂ ⊆ π.borderPlus n)
    (hwarp : π.warpAt Θ ≤ p)
    (hcard₁ : (π.borderPlus n₁).ncard = p + 1)
    (hcard₂ : (π.borderPlus n₂).ncard = p + 1) :
    Portrayal.LinkagePairs (π.areaGraph Δ).skeleton
      (π.borderPlus n₁) (π.borderPlus n₂) (p + 1)
      (π.nodeVertex n₁) (π.nodeVertex n₂) := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S := ⟨hn₁.1, hΘ_bd hn₁.2⟩
  have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S := ⟨hn₂.1, hΘ_bd hn₂.2⟩
  have hbs_le_warpAt : ∀ {n : π.S}, n ∈ π.Γ.N ∩ Θ → (π.borderSet n).ncard ≤ π.warpAt Θ := by
    intro n hn
    obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
    have hn_range : n ∈ Set.range E.node := by rw [E.range_node]; exact hn
    rcases hn_range with ⟨i, rfl⟩
    have hc_range : E.cell i ∈ {d ∈ π.Γ.C | (d ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact mem_range_self i
    have hbd_c : (E.cell i ∩ bd π.S).Nonempty :=
      hc_range.2.mono (inter_subset_inter_right _ hΘ_bd)
    have hn_t : E.node i ∈ tilde (E.cell i) := by
      rw [E.cell_tilde i]; exact mem_insert _ _
    exact (π.ncard_borderSet_le_cellWarp hc_range.1 hbd_c hn_t).trans
      (π.cellWarp_le_warpAt hc_range.1 hc_range.2)
  have hbs₁_le : (π.borderSet n₁).ncard ≤ p := (hbs_le_warpAt hn₁).trans hwarp
  have hbs₂_le : (π.borderSet n₂).ncard ≤ p := (hbs_le_warpAt hn₂).trans hwarp
  have hn₁_dom : n₁ ∈ π.domγ := by
    by_contra hn₁_not
    have hbp_eq : π.borderPlus n₁ = π.borderSet n₁ := by
      ext v; simp [Portrayal.borderPlus, hn₁_not]
    rw [hbp_eq] at hcard₁
    omega
  have hn₂_dom : n₂ ∈ π.domγ := by
    by_contra hn₂_not
    have hbp_eq : π.borderPlus n₂ = π.borderSet n₂ := by
      ext v; simp [Portrayal.borderPlus, hn₂_not]
    rw [hbp_eq] at hcard₂
    omega
  intro P hP_disj
  have hinj_first : Function.Injective (fun j => (P j).first) := by
    intro i j hij
    change (P i).first = (P j).first at hij
    by_contra hne_ij
    have hi_mem : (P j).first ∈ {z | z ∈ (P i).walk.support} :=
      hij ▸ SimpleGraph.Walk.start_mem_support (P i).walk
    exact Set.disjoint_left.mp (hP_disj hne_ij) hi_mem
      (SimpleGraph.Walk.start_mem_support (P j).walk)
  have hinj_last : Function.Injective (fun j => (P j).last) := by
    intro i j hij
    change (P i).last = (P j).last at hij
    by_contra hne_ij
    have hi_mem : (P j).last ∈ {z | z ∈ (P i).walk.support} :=
      hij ▸ SimpleGraph.Walk.end_mem_support (P i).walk
    exact Set.disjoint_left.mp (hP_disj hne_ij) hi_mem
      (SimpleGraph.Walk.end_mem_support (P j).walk)
  have hmem_range : ∀ {X : Set α}, X.Finite → X.ncard = p + 1 →
      ∀ {f : Fin (p + 1) → α}, (∀ i, f i ∈ X) → Function.Injective f →
      ∀ {x : α}, x ∈ X → ∃ i, f i = x := by
    intro X hfin hcard f hmem hinj x hx
    have hsub : Set.range f ⊆ X := by rintro _ ⟨i, rfl⟩; exact hmem i
    have hrange_card : (Set.range f).ncard = p + 1 := by
      rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hEq : Set.range f = X :=
      eq_of_subset_of_ncard_le hsub (by rw [hrange_card, hcard]) hfin
    rw [← hEq] at hx
    exact hx
  obtain ⟨j₀, hj₀_first⟩ := hmem_range
    (π.borderPlus_finite hn₁_bd) hcard₁ (fun j => (P j).first_mem) hinj_first
    (Or.inr ⟨hn₁_dom, rfl⟩)
  refine ⟨j₀, hj₀_first, ?_⟩
  by_contra hj₀_last_ne
  obtain ⟨j₂, hj₂_last⟩ := hmem_range
    (π.borderPlus_finite hn₂_bd) hcard₂ (fun j => (P j).last_mem) hinj_last
    (Or.inr ⟨hn₂_dom, rfl⟩)
  have hj₀_ne_j₂ : j₀ ≠ j₂ := fun h => hj₀_last_ne (h ▸ hj₂_last)
  have hn₂_not_P₀ : π.nodeVertex n₂ ∉ (P j₀).walk.support := fun hmem =>
    Set.disjoint_left.mp (hP_disj hj₀_ne_j₂) hmem
      (hj₂_last ▸ SimpleGraph.Walk.end_mem_support (P j₂).walk)
  let activeFor (d : Set π.S) (l : Fin (p + 1)) : Prop :=
    2 ≤ ({z ∈ (P l).walk.support | z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}).ncard
  let e : Set π.S → Set π.S := fun d =>
    {n ∈ tilde d ∩ π.domγ | ∃ l : Fin (p + 1),
      activeFor d l ∧ π.nodeVertex n ∈ (P l).walk.support}
  let P_mark : π.S → Prop := fun m =>
    m ∈ π.domγ ∧ π.nodeVertex m ∈ (P j₀).walk.support
  have hact_unique : ∀ {d : Set π.S}, d ∈ π.Γ.C → ∀ {l₁ l₂ : Fin (p + 1)},
      activeFor d l₁ → activeFor d l₂ → l₁ = l₂ := by
    exact interior_cell_active_for_unique_path (α := α) (β := β) (G := G) π (Δ := Δ) (n₁
      := n₁) (n₂ := n₂) (p := p) P hP_disj
  have he_props : ∀ d ∈ π.Γ.C, d ⊆ Δ → ¬ (d ∩ bd π.S).Nonempty →
      e d ⊆ tilde d ∧ (e d = ∅ ∨ 2 ≤ (e d).ncard) ∧
      ∀ x ∈ e d, ∀ y ∈ e d, P_mark x → P_mark y := by
    exact assigned_cell_nodes_preserve_path_membership (α := α) (β := β) (G := G) π (Δ :=
      Δ) (n₁ := n₁) (n₂ := n₂) (p := p) P hP_disj j₀    hact_unique
  have hP_n₁ : P_mark n₁ :=
    ⟨hn₁_dom, hj₀_first ▸ SimpleGraph.Walk.start_mem_support (P j₀).walk⟩
  have hP_n₂ : ¬ P_mark n₂ := fun h => hn₂_not_P₀ h.2
  obtain ⟨m₁, m₂, c, I₁, I₂, N₁, N₂,
      hm₁_mem, hm₂_mem, hm_ne, hP_m₁, hP_m₂,
      hc_C, hc_Δ, hc_Θ, htilde_c,
      hI₁_sub, hI₂_sub, hdisj_I,
      hn₁_I₁, hm₁_I₁, hm₂_I₂, hn₂_I₂,
      hN₁_sub, hN₂_sub, hdisj_N,
      hord_I, hborder_split, hint_split,
      ⟨c₁_end, hc₁_C, hc₁_Δ, hc₁_bd, hn₁_c₁⟩,
      ⟨c₂_end, hc₂_C, hc₂_Δ, hc₂_bd, hn₂_c₂⟩⟩ :=
    normalIArcDiscRegion_of_boundary π.S π.isSurface π.Γ Θ n₁ n₂ F Δ e P_mark
      hΘ hn₁ hn₂ hne hnorm hF hFbd hΔ hF_bd hbd_sub he_props hP_n₁ hP_n₂
  have hc_bd : (c ∩ bd π.S).Nonempty := hc_Θ.mono (inter_subset_inter_right _ hΘ_bd)
  let B₁ : Set α := ⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n
  let B₂ : Set α := ⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n
  have hbp₁_sub_B₁ : π.borderPlus n₁ ⊆ B₁ :=
    subset_biUnion_of_mem (x := n₁) ⟨hn₁_I₁, hn₁.1⟩
  have hbp₂_sub_B₂ : π.borderPlus n₂ ⊆ B₂ :=
    subset_biUnion_of_mem (x := n₂) ⟨hn₂_I₂, hn₂.1⟩
  have hbp_m₁_sub_B₁ : π.borderPlus m₁ ⊆ B₁ :=
    subset_biUnion_of_mem (x := m₁) ⟨hm₁_I₁, hm₁_mem.1⟩
  have hbp_m₂_sub_B₂ : π.borderPlus m₂ ⊆ B₂ :=
    subset_biUnion_of_mem (x := m₂) ⟨hm₂_I₂, hm₂_mem.1⟩
  have hex_border_cell : ∀ {n : π.S}, n ∈ π.Γ.N ∩ bd π.S →
      ∃ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty ∧ n ∈ tilde d := by
    intro n hn
    let Θ' := connectedComponentIn (bd π.S) n
    have hΘ' : Θ' ∈ cuffs π.S := ⟨n, hn.2, rfl⟩
    have hΘ'_bd : Θ' ⊆ bd π.S := connectedComponentIn_subset (bd π.S) n
    have hΘ'_arc : IsOArc Θ' := (cuff_statement.{0} π.S π.isSurface).2.2 Θ' hΘ'
    obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ' hΘ'_arc
    have hn_range : n ∈ Set.range E.node := by
      rw [E.range_node]; exact ⟨hn.1, mem_connectedComponentIn hn.2⟩
    rcases hn_range with ⟨i, hi⟩
    have hc_range : E.cell i ∈ {d ∈ π.Γ.C | (d ∩ Θ').Nonempty} := by
      rw [← E.range_cell]; exact mem_range_self i
    exact ⟨E.cell i, hc_range.1, hc_range.2.mono (inter_subset_inter_right _ hΘ'_bd),
      hi ▸ (E.cell_tilde i) ▸ mem_insert _ _⟩
  have htilde_bd_sub : ∀ {d : Set π.S}, d ∈ π.Γ.C → (d ∩ bd π.S).Nonempty →
      tilde d ⊆ π.Γ.N ∩ bd π.S := by
    intro d hd hbd
    obtain ⟨u, v, _, htilde, _, _, hu, hv⟩ := π.Γ.border_cell_exists_ends hd hbd
    rw [htilde]
    rintro x (rfl | rfl) <;> assumption
  have hnot_bp_of_not_bd : ∀ {n m : π.S}, n ∉ bd π.S → n ∈ π.domγ →
      m ∈ π.Γ.N ∩ bd π.S → π.nodeVertex n ∉ π.borderPlus m := by
    intro n m hn_not_bd hn_dom hm_bd
    let Θ' := connectedComponentIn (bd π.S) m
    have hΘ' : Θ' ∈ cuffs π.S := ⟨m, hm_bd.2, rfl⟩
    have hΘ'_bd : Θ' ⊆ bd π.S := connectedComponentIn_subset (bd π.S) m
    have hm_Θ' : m ∈ π.Γ.N ∩ Θ' := ⟨hm_bd.1, mem_connectedComponentIn hm_bd.2⟩
    have hn_not_Θ' : n ∉ Θ' := fun h => hn_not_bd (hΘ'_bd h)
    rintro (hmem_bs | ⟨hm_dom, hEq⟩)
    · exact π.p4_notMem Θ' hΘ' m hm_Θ' n hn_dom hn_not_Θ' hmem_bs
    · have hnm : n = m := π.nodeVertex_injOn hn_dom hm_dom hEq
      exact hn_not_bd (hnm ▸ hm_bd.2)
  have hclaim : ∀ j : Fin (p + 1),
      ∃ Q' : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂),
        {z | z ∈ Q'.walk.support} ⊆ {z | z ∈ (P j).walk.support} ∧
        Q'.first ∈ B₁ ∧ Q'.last ∈ B₂ := by
    exact boundary_paths_restrict_to_middle_cell (α := α) (β := β) (G := G) π (Θ := Θ) (Δ := Δ)
      (n₁ := n₁) (n₂ := n₂) (p := p) hΘ hn₁ hn₂ hinter_sub hΘ_bd P   P_mark m₁ m₂ c I₁
      I₂ N₁ N₂ hm₁_mem hm₂_mem hm_ne hP_m₁ hP_m₂ hc_C hc_Δ hc_Θ htilde_c hI₁_sub hI₂_sub hdisj_I
      hm₁_I₁ hm₂_I₂ hN₁_sub hN₂_sub hdisj_N hord_I hborder_split hint_split c₁_end hc₁_C hc₁_Δ
      hc₁_bd hn₁_c₁ c₂_end hc₂_C hc₂_Δ hc₂_bd hn₂_c₂ hc_bd hbp₁_sub_B₁ hbp₂_sub_B₂ hbp_m₁_sub_B₁
      hbp_m₂_sub_B₂ hex_border_cell htilde_bd_sub hnot_bp_of_not_bd
  exact no_partial_middle_cell_linkage π (fun j ↦ {z | z ∈ (P j).walk.support}) hP_disj hwarp
    ⟨hm₁_mem.1, hΘ_bd hm₁_mem.2.1⟩ ⟨hm₂_mem.1, hΘ_bd hm₂_mem.2.1⟩ hm_ne hc_C hc_Θ hc_bd
    htilde_c hP_m₁.2 hP_m₂ (fun j ↦ (hclaim j).imp fun _ h ↦ h.1)

private noncomputable abbrev portrayal_after_two_cell_replacement
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {F : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {n₃ : π.S}
    (hF : IsLineWithEnds F n₁ n₂)
    (hFbd : F ∩ bd π.S = {n₁, n₂})
    (hFN : F ∩ π.Γ.N = {n₁, n₂, n₃})
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.areaGraph Δ).IsSeparation A₁ A₂)
    (hinter_V : (A₁ ∩ A₂).vertexSet = {π.nodeVertex n₁, π.nodeVertex n₂})
    (hn₃_A₁ : π.nodeVertex n₃ ∈ A₁.vertexSet)
    (hbs_A₂ : π.borderSet n₁ ∪ π.borderSet n₂ ⊆ A₂.vertexSet)
    (Γ' : Painting π.S)
    (Θ : Set π.S)
    (c₁ : Set π.S)
    (c₂ : Set π.S)
    (hN'_eq : Γ'.N = π.Γ.N \ Δ ∪ {n₁, n₂, n₃})
    (hN'_sub : Γ'.N ⊆ π.Γ.N)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hdich : ∀ c ∈ π.Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ)
    (htilde_I₂ : ∀ c ∈ π.Γ.C, c ⊆ Δᶜ → tilde c ⊆ Γ'.N)
    (hc₁_mem : c₁ ∈ Γ'.C)
    (hc₁_int : ¬(c₁ ∩ bd π.S).Nonempty)
    (htilde_c₁ : tilde c₁ = {n₁, n₂, n₃})
    (hc₂_mem : c₂ ∈ Γ'.C)
    (hc₂_Θ : (c₂ ∩ Θ).Nonempty)
    (htilde_c₂ : tilde c₂ = {n₁, n₂})
    (hc₁_ne_c₂ : c₁ ≠ c₂)
    (hc₁_not_I₂ : c₁ ∉ {c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ})
    (hc₂_not_I₂ : c₂ ∉ {c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ})
    (hC' : Γ'.C = insert c₁ (insert c₂ {c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ}))
    (hc₂_bd : (c₂ ∩ bd π.S).Nonempty)
    (hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S)
    (hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S)
    (hn₃_FN : n₃ ∈ F ∩ π.Γ.N)
    (hn₁_dom : n₁ ∈ π.domγ)
    (hn₂_dom : n₂ ∈ π.domγ)
    (hn₃_dom : n₃ ∈ π.domγ)
    (hne₁₂ : n₁ ≠ n₂)
    (hne₃₁ : n₃ ≠ n₁)
    (hne₃₂ : n₃ ≠ n₂)
    (hn₁_A₁A₂ : π.nodeVertex n₁ ∈ (A₁ ∩ A₂).vertexSet)
    (hn₂_A₁A₂ : π.nodeVertex n₂ ∈ (A₁ ∩ A₂).vertexSet)
    (hn₃_not_A₂ : π.nodeVertex n₃ ∉ A₂.vertexSet)
    (hbp_c₂_sub_A₂ : ∀ {n : π.S}, n ∈ tilde c₂ → π.borderPlus n ⊆ A₂.vertexSet)
    (htilde_c₂_N' : tilde c₂ ⊆ Γ'.N ∩ bd π.S)
    (htilde_c₁_N' : tilde c₁ ⊆ Γ'.N)
    (hdisj_I : Disjoint ({c : Set π.S | c ∈ π.Γ.C ∧ c ⊆ Δ}) ({c : Set π.S | c ∈ π.Γ.C ∧ c ⊆ Δᶜ}))
    (hinter_I₁_I₂ : (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion ({c : Set π.S | c ∈ π.Γ.C
      ∧ c ⊆ Δᶜ})).vertexSet ⊆ π.borderSet n₁ ∪
      π.borderSet n₂ ∪ {π.nodeVertex n₁, π.nodeVertex n₂, π.nodeVertex n₃})
    (cellG : Set π.S → Hypergraph α β)
    (hcellG_c₁ : cellG c₁ = A₁)
    (hcellG_c₂ : cellG c₂ = A₂)
    (hcellG_I₂ : ∀ {c : Set π.S}, c ∈ ({c : Set π.S | c ∈ π.Γ.C ∧ c ⊆ Δᶜ}) → cellG c
      = π.cellGraph c)
    (hA₁_le_G : A₁ ≤ G)
    (hA₂_le_G : A₂ ≤ G) :
    Portrayal G := by
  let I₁ := {c : Set π.S | c ∈ π.Γ.C ∧ c ⊆ Δ}
  let I₂ := {c : Set π.S | c ∈ π.Γ.C ∧ c ⊆ Δᶜ}
  classical
  exact
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
        rcases hC' ▸ hc with rfl | rfl | hc_I₂
        · rw [hcellG_c₁]; exact hA₁_le_G
        · rw [hcellG_c₂]; exact hA₂_le_G
        · rw [hcellG_I₂ hc_I₂]; exact π.cellGraph_le c hc_I₂.1
      borderSet_subset := fun n hn => π.borderSet_subset n ⟨hN'_sub hn.1, hn.2⟩
      domγ_subset := inter_subset_right
      nodeVertex_mem := fun n hn => π.nodeVertex_mem n hn.1
      nodeVertex_injOn := π.nodeVertex_injOn.mono inter_subset_left
      p1_vertex := fun v hv => by
        rcases π.p1_vertex v hv with ⟨c, hc, hvc⟩
        rcases hdich c hc with hc_in | hc_out
        · have hv_Δ : v ∈ (π.areaGraph Δ).vertexSet :=
            mem_biUnion ⟨⟨hc, hc_in⟩, hc⟩ hvc
          rw [← hsep.vertexSet_union] at hv_Δ
          rcases hv_Δ with hv₁ | hv₂
          · exact ⟨c₁, hc₁_mem, hcellG_c₁ ▸ hv₁⟩
          · exact ⟨c₂, hc₂_mem, hcellG_c₂ ▸ hv₂⟩
        · refine ⟨c, hC'.symm ▸ Or.inr (Or.inr ⟨hc, hc_out⟩), ?_⟩
          rw [hcellG_I₂ ⟨hc, hc_out⟩]; exact hvc
      p1_edge := fun e he => by
        rcases π.p1_edge e he with ⟨c, hc, hec⟩
        rcases hdich c hc with hc_in | hc_out
        · have he_Δ : e ∈ (π.areaGraph Δ).edgeSet :=
            mem_biUnion ⟨⟨hc, hc_in⟩, hc⟩ hec
          rw [← hsep.edgeSet_union] at he_Δ
          rcases he_Δ with he₁ | he₂
          · exact ⟨c₁, hc₁_mem, hcellG_c₁ ▸ he₁⟩
          · exact ⟨c₂, hc₂_mem, hcellG_c₂ ▸ he₂⟩
        · refine ⟨c, hC'.symm ▸ Or.inr (Or.inr ⟨hc, hc_out⟩), ?_⟩
          rw [hcellG_I₂ ⟨hc, hc_out⟩]; exact hec
      p1_disjoint := fun d₁ hd₁ d₂ hd₂ hne_d => by
        have hdisj_Δ_I₂ : ∀ {d : Set π.S}, d ∈ I₂ →
            Disjoint (π.areaGraph Δ).edgeSet (π.cellGraph d).edgeSet := by
          intro d hd
          rw [Set.disjoint_left]
          intro e heΔ hed
          change e ∈ ⋃ c₀ ∈ _, _ at heΔ
          rw [mem_iUnion₂] at heΔ
          rcases heΔ with ⟨c₀, hc₀, hec₀⟩
          have hc₀_ne : c₀ ≠ d := fun h => Set.disjoint_left.mp hdisj_I hc₀.1 (h ▸ hd)
          exact Set.disjoint_left.mp (π.p1_disjoint c₀ hc₀.2 d hd.1 hc₀_ne) hec₀ hed
        rcases hC' ▸ hd₁ with rfl | rfl | hd₁_I₂ <;>
          rcases hC' ▸ hd₂ with rfl | rfl | hd₂_I₂
        · exact False.elim (hne_d rfl)
        · rw [hcellG_c₁, hcellG_c₂]; exact hsep.disjoint_edgeSet
        · rw [hcellG_c₁, hcellG_I₂ hd₂_I₂]
          exact (hdisj_Δ_I₂ hd₂_I₂).mono_left hsep.left_le.edgeSet_subset
        · rw [hcellG_c₂, hcellG_c₁]; exact hsep.disjoint_edgeSet.symm
        · exact False.elim (hne_d rfl)
        · rw [hcellG_c₂, hcellG_I₂ hd₂_I₂]
          exact (hdisj_Δ_I₂ hd₂_I₂).mono_left hsep.right_le.edgeSet_subset
        · rw [hcellG_I₂ hd₁_I₂, hcellG_c₁]
          exact ((hdisj_Δ_I₂ hd₁_I₂).mono_left hsep.left_le.edgeSet_subset).symm
        · rw [hcellG_I₂ hd₁_I₂, hcellG_c₂]
          exact ((hdisj_Δ_I₂ hd₁_I₂).mono_left hsep.right_le.edgeSet_subset).symm
        · rw [hcellG_I₂ hd₁_I₂, hcellG_I₂ hd₂_I₂]
          exact π.p1_disjoint d₁ hd₁_I₂.1 d₂ hd₂_I₂.1 hne_d
      p2 := fun c hc n hn => by
        rcases hC' ▸ hc with rfl | rfl | hc_I₂
        · rw [hcellG_c₁]
          rcases (htilde_c₁ ▸ hn.1 : n ∈ ({n₁, n₂, n₃} : Set π.S)) with rfl | rfl | rfl
          · exact hn₁_A₁A₂.1
          · exact hn₂_A₁A₂.1
          · exact hn₃_A₁
        · rw [hcellG_c₂]
          exact hbp_c₂_sub_A₂ hn.1 (Or.inr ⟨hn.2.1, rfl⟩)
        · rw [hcellG_I₂ hc_I₂]
          exact π.p2 c hc_I₂.1 n ⟨hn.1, hn.2.1⟩
      p3_notMem := fun n hn => π.p3_notMem n ⟨hn.1.1, hn.2⟩
      p3_subset := fun c hc hbd n hnt v hv => by
        rcases hC' ▸ hc with rfl | rfl | hc_I₂
        · exact False.elim (hc₁_int hbd)
        · rw [hcellG_c₂]
          exact hbp_c₂_sub_A₂ hnt (Or.inl hv)
        · rw [hcellG_I₂ hc_I₂]
          exact π.p3_subset c hc_I₂.1 hbd n hnt hv
      p4_disjoint := fun Θ₁ hΘ₁ Θ₂ hΘ₂ hne_Θ u₁ hu₁ u₂ hu₂ =>
        π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne_Θ u₁ ⟨hN'_sub hu₁.1, hu₁.2⟩ u₂ ⟨hN'_sub hu₂.1, hu₂.2⟩
      p4_notMem := fun Θ' hΘ' u₁ hu₁ u₂ hu₂ hnot =>
        π.p4_notMem Θ' hΘ' u₁ ⟨hN'_sub hu₁.1, hu₁.2⟩ u₂ hu₂.1 hnot
      p5 := fun c hc hint v hvc hex => by
        rcases hex with ⟨d', hd', hd'_ne, hvd'⟩
        rcases hC' ▸ hc with h1 | h2 | hc_I₂
        · rw [h1, hcellG_c₁] at hvc
          have hv_triple : v ∈ ({π.nodeVertex n₁, π.nodeVertex n₂, π.nodeVertex n₃} : Set α) := by
            rcases hC' ▸ hd' with hd'₁ | hd'₂ | hd'_I₂
            · exact False.elim (hd'_ne (hd'₁.trans h1.symm))
            · rw [hd'₂, hcellG_c₂] at hvd'
              have hv_inter : v ∈ (A₁ ∩ A₂).vertexSet := ⟨hvc, hvd'⟩
              rw [hinter_V] at hv_inter
              rcases hv_inter with rfl | rfl <;> simp
            · rw [hcellG_I₂ hd'_I₂] at hvd'
              have hv_Δ : v ∈ (π.areaGraph Δ).vertexSet := hsep.left_le.vertexSet_subset hvc
              have hv_I₂ : v ∈ (π.cellsUnion I₂).vertexSet :=
                mem_biUnion ⟨hd'_I₂, hd'_I₂.1⟩ hvd'
              rcases hinter_I₁_I₂ ⟨hv_Δ, hv_I₂⟩ with hv_bs | hv_tr
              · have hv_A₂ : v ∈ A₂.vertexSet := hbs_A₂ hv_bs
                have hv_inter : v ∈ (A₁ ∩ A₂).vertexSet := ⟨hvc, hv_A₂⟩
                rw [hinter_V] at hv_inter
                rcases hv_inter with rfl | rfl <;> simp
              · exact hv_tr
          rw [h1]
          rcases hv_triple with rfl | rfl | rfl
          · have hn₁_t : n₁ ∈ tilde c₁ := htilde_c₁ ▸ Or.inl rfl
            exact ⟨n₁, ⟨hn₁_t, hn₁_dom, htilde_c₁_N' hn₁_t⟩, rfl⟩
          · have hn₂_t : n₂ ∈ tilde c₁ := htilde_c₁ ▸ Or.inr (Or.inl rfl)
            exact ⟨n₂, ⟨hn₂_t, hn₂_dom, htilde_c₁_N' hn₂_t⟩, rfl⟩
          · have hn₃_t : n₃ ∈ tilde c₁ := htilde_c₁ ▸ Or.inr (Or.inr rfl)
            exact ⟨n₃, ⟨hn₃_t, hn₃_dom, htilde_c₁_N' hn₃_t⟩, rfl⟩
        · exact False.elim (hint (h2 ▸ hc₂_bd))
        · rw [hcellG_I₂ hc_I₂] at hvc
          have hex_π : ∃ d₀ ∈ π.Γ.C, d₀ ≠ c ∧ v ∈ (π.cellGraph d₀).vertexSet := by
            rcases hC' ▸ hd' with hd'₁ | hd'₂ | hd'_I₂
            · rw [hd'₁, hcellG_c₁] at hvd'
              have hv_Δ : v ∈ (π.areaGraph Δ).vertexSet := hsep.left_le.vertexSet_subset hvd'
              change v ∈ ⋃ d₀ ∈ _, _ at hv_Δ
              rw [mem_iUnion₂] at hv_Δ
              rcases hv_Δ with ⟨d₀, hd₀, hvd₀⟩
              exact ⟨d₀, hd₀.2, fun h => Set.disjoint_left.mp hdisj_I hd₀.1 (h ▸ hc_I₂), hvd₀⟩
            · rw [hd'₂, hcellG_c₂] at hvd'
              have hv_Δ : v ∈ (π.areaGraph Δ).vertexSet := hsep.right_le.vertexSet_subset hvd'
              change v ∈ ⋃ d₀ ∈ _, _ at hv_Δ
              rw [mem_iUnion₂] at hv_Δ
              rcases hv_Δ with ⟨d₀, hd₀, hvd₀⟩
              exact ⟨d₀, hd₀.2, fun h => Set.disjoint_left.mp hdisj_I hd₀.1 (h ▸ hc_I₂), hvd₀⟩
            · rw [hcellG_I₂ hd'_I₂] at hvd'
              exact ⟨d', hd'_I₂.1, hd'_ne, hvd'⟩
          obtain ⟨n, ⟨hnt, hndom⟩, hnv⟩ := π.p5 c hc_I₂.1 hint v hvc hex_π
          exact ⟨n, ⟨hnt, hndom, htilde_I₂ c hc_I₂.1 hc_I₂.2 hnt⟩, hnv⟩
      p6 := fun c hc hbd v hvc hex => by
        rcases hex with ⟨d', hd', hd'_ne, hvd'⟩
        rcases hC' ▸ hc with h1 | h2 | hc_I₂
        · exact False.elim (hc₁_int (h1 ▸ hbd))
        · rw [h2, hcellG_c₂] at hvc
          have hv_bp : v ∈ π.borderSet n₁ ∪ π.borderSet n₂ ∪
              {π.nodeVertex n₁, π.nodeVertex n₂} := by
            rcases hC' ▸ hd' with hd'₁ | hd'₂ | hd'_I₂
            · rw [hd'₁, hcellG_c₁] at hvd'
              have hv_inter : v ∈ (A₁ ∩ A₂).vertexSet := ⟨hvd', hvc⟩
              rw [hinter_V] at hv_inter
              exact Or.inr hv_inter
            · exact False.elim (hd'_ne (hd'₂.trans h2.symm))
            · rw [hcellG_I₂ hd'_I₂] at hvd'
              have hv_Δ : v ∈ (π.areaGraph Δ).vertexSet := hsep.right_le.vertexSet_subset hvc
              have hv_I₂ : v ∈ (π.cellsUnion I₂).vertexSet :=
                mem_biUnion ⟨hd'_I₂, hd'_I₂.1⟩ hvd'
              rcases hinter_I₁_I₂ ⟨hv_Δ, hv_I₂⟩ with hv_bs | (rfl | rfl | rfl)
              · exact Or.inl hv_bs
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
              · exact False.elim (hn₃_not_A₂ hvc)
          rw [h2]
          have hn₁_t : n₁ ∈ tilde c₂ := htilde_c₂ ▸ Or.inl rfl
          have hn₂_t : n₂ ∈ tilde c₂ := htilde_c₂ ▸ Or.inr rfl
          rcases hv_bp with (hv_bs₁ | hv_bs₂) | (rfl | rfl)
          · exact ⟨n₁, hn₁_t, Or.inl hv_bs₁⟩
          · exact ⟨n₂, hn₂_t, Or.inl hv_bs₂⟩
          · exact ⟨n₁, hn₁_t, Or.inr ⟨⟨hn₁_dom, (htilde_c₂_N' hn₁_t).1⟩, rfl⟩⟩
          · exact ⟨n₂, hn₂_t, Or.inr ⟨⟨hn₂_dom, (htilde_c₂_N' hn₂_t).1⟩, rfl⟩⟩
        · rw [hcellG_I₂ hc_I₂] at hvc
          have hex_π : ∃ d₀ ∈ π.Γ.C, d₀ ≠ c ∧ v ∈ (π.cellGraph d₀).vertexSet := by
            rcases hC' ▸ hd' with hd'₁ | hd'₂ | hd'_I₂
            · rw [hd'₁, hcellG_c₁] at hvd'
              have hv_Δ : v ∈ (π.areaGraph Δ).vertexSet := hsep.left_le.vertexSet_subset hvd'
              change v ∈ ⋃ d₀ ∈ _, _ at hv_Δ
              rw [mem_iUnion₂] at hv_Δ
              rcases hv_Δ with ⟨d₀, hd₀, hvd₀⟩
              exact ⟨d₀, hd₀.2, fun h => Set.disjoint_left.mp hdisj_I hd₀.1 (h ▸ hc_I₂), hvd₀⟩
            · rw [hd'₂, hcellG_c₂] at hvd'
              have hv_Δ : v ∈ (π.areaGraph Δ).vertexSet := hsep.right_le.vertexSet_subset hvd'
              change v ∈ ⋃ d₀ ∈ _, _ at hv_Δ
              rw [mem_iUnion₂] at hv_Δ
              rcases hv_Δ with ⟨d₀, hd₀, hvd₀⟩
              exact ⟨d₀, hd₀.2, fun h => Set.disjoint_left.mp hdisj_I hd₀.1 (h ▸ hc_I₂), hvd₀⟩
            · rw [hcellG_I₂ hd'_I₂] at hvd'
              exact ⟨d', hd'_I₂.1, hd'_ne, hvd'⟩
          obtain ⟨n, hnt, hvn⟩ := π.p6 c hc_I₂.1 hbd v hvc hex_π
          have hn_N' : n ∈ Γ'.N := htilde_I₂ c hc_I₂.1 hc_I₂.2 hnt
          refine ⟨n, hnt, ?_⟩
          rcases hvn with hv_bs | ⟨hn_dom, hnv⟩
          · exact Or.inl hv_bs
          · exact Or.inr ⟨⟨hn_dom, hn_N'⟩, hnv⟩
      p7 := fun Θ' hΘ' u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ hord v hv₁ hv₃ => by
        have hv₁' : v ∈ π.borderPlus u₁ := hv₁.imp id (fun ⟨h, hv⟩ => ⟨h.1, hv⟩)
        have hv₃' : v ∈ π.borderPlus u₃ := hv₃.imp id (fun ⟨h, hv⟩ => ⟨h.1, hv⟩)
        rcases π.p7 Θ' hΘ' u₁ ⟨hN'_sub hu₁.1, hu₁.2⟩ u₂ ⟨hN'_sub hu₂.1, hu₂.2⟩
          u₃ ⟨hN'_sub hu₃.1, hu₃.2⟩ u₄ ⟨hN'_sub hu₄.1, hu₄.2⟩ hord v hv₁' hv₃' with h₂ | h₄
        · exact Or.inl (h₂.imp id (fun ⟨h, hv⟩ => ⟨⟨h, hu₂.1⟩, hv⟩))
        · exact Or.inr (h₄.imp id (fun ⟨h, hv⟩ => ⟨⟨h, hu₄.1⟩, hv⟩)) }

private theorem area_cells_share_only_frontier_vertices
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {F : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {n₃ : π.S}
    (hF : IsLineWithEnds F n₁ n₂)
    (hFbd : F ∩ bd π.S = {n₁, n₂})
    (hFN : F ∩ π.Γ.N = {n₁, n₂, n₃})
    (hΔ : IsClosedDisc Δ)
    [T2Space π.S]
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hinter_V : (A₁ ∩ A₂).vertexSet = {π.nodeVertex n₁, π.nodeVertex n₂})
    (hn₃_A₁ : π.nodeVertex n₃ ∈ A₁.vertexSet)
    (hbs_A₂ : π.borderSet n₁ ∪ π.borderSet n₂ ⊆ A₂.vertexSet)
    (Γ' : Painting π.S)
    (Θ : Set π.S)
    (c₁ : Set π.S)
    (c₂ : Set π.S)
    (hN'_eq : Γ'.N = π.Γ.N \ Δ ∪ {n₁, n₂, n₃})
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (htilde_I₂ : ∀ c ∈ π.Γ.C, c ⊆ Δᶜ → tilde c ⊆ Γ'.N)
    (htilde_c₁ : tilde c₁ = {n₁, n₂, n₃})
    (htilde_c₂ : tilde c₂ = {n₁, n₂})
    (hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S)
    (hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S)
    (hn₃_FN : n₃ ∈ F ∩ π.Γ.N)
    (hn₁_dom : n₁ ∈ π.domγ)
    (hn₂_dom : n₂ ∈ π.domγ)
    (hn₃_dom : n₃ ∈ π.domγ)
    (hne₁₂ : n₁ ≠ n₂)
    (hne₃₁ : n₃ ≠ n₁)
    (hne₃₂ : n₃ ≠ n₂)
    (hn₁_A₁A₂ : π.nodeVertex n₁ ∈ (A₁ ∩ A₂).vertexSet)
    (hn₂_A₁A₂ : π.nodeVertex n₂ ∈ (A₁ ∩ A₂).vertexSet)
    (hn₃_not_A₂ : π.nodeVertex n₃ ∉ A₂.vertexSet)
    (hpart : ({c : Set π.S | c ∈ π.Γ.C ∧ c ⊆ Δ}) ∪ ({c : Set π.S | c ∈ π.Γ.C ∧ c ⊆ Δᶜ}) = π.Γ.C)
    (hdisj_I : Disjoint ({c : Set π.S | c ∈ π.Γ.C ∧ c ⊆ Δ}) ({c : Set π.S | c ∈ π.Γ.C ∧ c ⊆ Δᶜ})) :
    (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion ({c : Set π.S | c ∈ π.Γ.C
      ∧ c ⊆ Δᶜ})).vertexSet ⊆ π.borderSet n₁ ∪ π.borderSet n₂ ∪
      {π.nodeVertex n₁, π.nodeVertex n₂, π.nodeVertex n₃} := by
  let I₁ := {c : Set π.S | c ∈ π.Γ.C ∧ c ⊆ Δ}
  let I₂ := {c : Set π.S | c ∈ π.Γ.C ∧ c ⊆ Δᶜ}
  have hv_inter := theorem_2_1_claim_3 π hpart hdisj_I
  have hX_inter : (⋃ c ∈ I₁, tilde c) ∩ (⋃ c ∈ I₂, tilde c) ⊆ {n₁, n₂, n₃} := by
    rintro n ⟨hX₁, hX₂⟩
    rw [mem_iUnion₂] at hX₁ hX₂
    rcases hX₁ with ⟨d₁, hd₁, hnd₁⟩
    rcases hX₂ with ⟨d₂, hd₂, hnd₂⟩
    have hnΔ : n ∈ Δ := closure_minimal hd₁.2 hΔ.isClosed hnd₁.1
    have hnN' : n ∈ Γ'.N := htilde_I₂ d₂ hd₂.1 hd₂.2 hnd₂
    rw [hN'_eq] at hnN'
    rcases hnN' with ⟨_, hn_notΔ⟩ | hn_triple
    · exact False.elim (hn_notΔ hnΔ)
    · exact hn_triple
  intro v hv
  rcases hv_inter hv with ⟨n, ⟨hX, _⟩, rfl⟩ | hY
  · right
    rcases hX_inter hX with rfl | rfl | rfl <;> simp
  · rw [mem_iUnion₂] at hY
    rcases hY with ⟨n, ⟨hY₁, hY₂⟩, hvn⟩
    rw [mem_iUnion₂] at hY₁ hY₂
    rcases hY₁ with ⟨d₁, ⟨hd₁, hbd₁⟩, hnd₁⟩
    rcases hY₂ with ⟨d₂, ⟨hd₂, _⟩, hnd₂⟩
    have hn_triple : n ∈ ({n₁, n₂, n₃} : Set π.S) :=
      hX_inter ⟨mem_biUnion hd₁ hnd₁, mem_biUnion hd₂ hnd₂⟩
    obtain ⟨u₁, v₁, _, htilde₁, _, _, hu₁, hv₁⟩ := π.Γ.border_cell_exists_ends hd₁.1 hbd₁
    have hnbd : n ∈ bd π.S := by
      rcases (htilde₁ ▸ hnd₁ : n ∈ ({u₁, v₁} : Set π.S)) with rfl | rfl <;>
        [exact hu₁.2; exact hv₁.2]
    have hn_pair : n ∈ ({n₁, n₂} : Set π.S) := by
      rcases hn_triple with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact hFbd ▸ ⟨hn₃_FN.1, hnbd⟩
    rcases hn_pair with rfl | rfl
    · exact Or.inl (Or.inl hvn)
    · exact Or.inl (Or.inr hvn)

private theorem replacement_border_linkage
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G) (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 4)) (hwarp : π.warp ≤ p) (hθ : 6 * p + 8 < θ)
    {F Δ Θ c₂ : Set π.S} {n₁ n₂ : π.S}
    (hnorm : π.Γ.IsNormal F) (hF : IsLineWithEnds F n₁ n₂) (hFbd : F ∩ bd π.S = {n₁, n₂})
    (hFN_card : (F ∩ π.Γ.N).ncard = 3) (hΔ : IsClosedDisc Δ)
    (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ)) (hF_bd : F ⊆ discBd Δ)
    (hbd_sub : discBd Δ ⊆ F ∪ bd π.S) {A₂ : Hypergraph α β} (hA₂_le : A₂ ≤ π.areaGraph Δ)
    (hdom : π.domγ = π.Γ.N) (hΘ : Θ ∈ cuffs π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ) (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ) (hbd_Θ : discBd Δ ⊆ F ∪ Θ)
    (htilde_c₂ : tilde c₂ = {n₁, n₂}) (hΘ_bd : Θ ⊆ bd π.S)
    (hbs_le_q : ∀ {n : π.S}, n ∈ π.Γ.N ∩ Θ → (π.borderSet n).ncard ≤ π.warpAt Θ) :
    ∀ u₁ ∈ tilde c₂, ∀ u₂ ∈ tilde c₂, u₁ ≠ u₂ →
      (π.borderSet u₁).ncard ≤ π.warpAt Θ ∧ (π.borderSet u₂).ncard ≤ π.warpAt Θ ∧
      ((π.borderPlus u₁).ncard = π.warpAt Θ + 1 → (π.borderPlus u₂).ncard = π.warpAt Θ + 1 →
        Portrayal.LinkagePairs A₂.skeleton (π.borderPlus u₁) (π.borderPlus u₂)
          (π.warpAt Θ + 1) (π.nodeVertex u₁) (π.nodeVertex u₂)) := by
  let q := π.warpAt Θ
  intro u₁ hu₁ u₂ hu₂ hu_ne
  have hu₁_pair : u₁ = n₁ ∨ u₁ = n₂ := by
    have h : u₁ ∈ ({n₁, n₂} : Set π.S) := htilde_c₂ ▸ hu₁
    exact h
  have hu₂_pair : u₂ = n₁ ∨ u₂ = n₂ := by
    have h : u₂ ∈ ({n₁, n₂} : Set π.S) := htilde_c₂ ▸ hu₂
    exact h
  have hu₁_Θ : u₁ ∈ π.Γ.N ∩ Θ := by
    rcases hu₁_pair with h | h <;> rw [h] <;> assumption
  have hu₂_Θ : u₂ ∈ π.Γ.N ∩ Θ := by
    rcases hu₂_pair with h | h <;> rw [h] <;> assumption
  have hu₁_bd : u₁ ∈ π.Γ.N ∩ bd π.S := ⟨hu₁_Θ.1, hΘ_bd hu₁_Θ.2⟩
  have hu₂_bd : u₂ ∈ π.Γ.N ∩ bd π.S := ⟨hu₂_Θ.1, hΘ_bd hu₂_Θ.2⟩
  refine ⟨hbs_le_q hu₁_Θ, hbs_le_q hu₂_Θ, fun hcard₁ hcard₂ => ?_⟩
  by_cases hq0 : q = 0
  · have hbs₁_le : (π.borderSet u₁).ncard ≤ 0 := hq0 ▸ hbs_le_q hu₁_Θ
    have hbs₂_le : (π.borderSet u₂).ncard ≤ 0 := hq0 ▸ hbs_le_q hu₂_Θ
    have hbs₁_emp : π.borderSet u₁ = ∅ :=
      (ncard_eq_zero (hs := π.borderSet_finite hu₁_bd)).mp (Nat.eq_zero_of_le_zero hbs₁_le)
    have hbs₂_emp : π.borderSet u₂ = ∅ :=
      (ncard_eq_zero (hs := π.borderSet_finite hu₂_bd)).mp (Nat.eq_zero_of_le_zero hbs₂_le)
    have hu₁_dom : u₁ ∈ π.domγ := hdom ▸ hu₁_Θ.1
    have hu₂_dom : u₂ ∈ π.domγ := hdom ▸ hu₂_Θ.1
    have hbp₁_eq : π.borderPlus u₁ = {π.nodeVertex u₁} := by
      ext v; simp [Portrayal.borderPlus, hbs₁_emp, hu₁_dom]
    have hbp₂_eq : π.borderPlus u₂ = {π.nodeVertex u₂} := by
      ext v; simp [Portrayal.borderPlus, hbs₂_emp, hu₂_dom]
    intro L _
    exact ⟨0, mem_singleton_iff.mp (hbp₁_eq ▸ (L 0).first_mem),
      mem_singleton_iff.mp (hbp₂_eq ▸ (L 0).last_mem)⟩
  · have hq_le_p : q ≤ p := (π.warpAt_le_warp hΘ).trans hwarp
    have hθ_67 : (2 * p + 4) + max 3 (2 * p + 2) < θ := by omega
    have hpair_eq : ({u₁, u₂} : Set π.S) = {n₁, n₂} := by
      rcases hu₁_pair with h1 | h1 <;> rcases hu₂_pair with h2 | h2
      · exact False.elim (hu_ne (h1.trans h2.symm))
      · rw [h1, h2]
      · rw [h1, h2]; exact pair_comm n₂ n₁
      · exact False.elim (hu_ne (h1.trans h2.symm))
    have hF_u : IsLineWithEnds F u₁ u₂ := by
      rcases hu₁_pair with h1 | h1 <;> rcases hu₂_pair with h2 | h2
      · exact False.elim (hu_ne (h1.trans h2.symm))
      · rw [h1, h2]; exact hF
      · rw [h1, h2]; exact isLineWithEnds_symm hF
      · exact False.elim (hu_ne (h1.trans h2.symm))
    have hFbd_u : F ∩ bd π.S = {u₁, u₂} := hFbd.trans hpair_eq.symm
    have hFγ_le : 2 * p + 1 ≤ 2 * p + 4 ∧ (F ∩ π.domγ).ncard ≤ (2 * p + 4) - 2 * p - 1 := by
      rw [hdom, hFN_card]
      omega
    have hinter_bd : ∀ n ∈ π.Γ.N ∩ (Θ ∩ discBd Δ),
        π.borderPlus u₁ ∩ π.borderPlus u₂ ⊆ π.borderPlus n := by
      rintro n ⟨hnN, hnΘ, hnbd⟩
      have hnΔ : n ∈ Δ := discBd_subset Δ hnbd
      have hn_bdS : n ∈ bd π.S := hΘ_bd hnΘ
      exact theorem_6_7_proof
        h𝒯 π htrue.1 hwarp hred hθ_67
        hnorm hF_u hFbd_u hFγ_le hΔ hF_bd hbd_sub hsmall
        ⟨⟨hnN, hnΔ⟩, hn_bdS⟩
    have hlink_Δ : Portrayal.LinkagePairs (π.areaGraph Δ).skeleton
        (π.borderPlus u₁) (π.borderPlus u₂) (q + 1)
        (π.nodeVertex u₁) (π.nodeVertex u₂) :=
      theorem_7_3_no_FN π hΘ hu₁_Θ hu₂_Θ hu_ne hnorm hF_u hFbd_u
        hΔ hF_bd hbd_Θ hinter_bd le_rfl hcard₁ hcard₂
    intro L hL_disj
    have hstep_A₂ : ∀ {a b : α}, A₂.skeleton.Adj a b → (π.areaGraph Δ).skeleton.Adj a b := by
      rintro a b ⟨hab, e, hinca, hincb⟩
      have he_A₂ : e ∈ A₂.edgeSet := A₂.edge_mem_of_inc hinca
      have he_Δ : e ∈ (π.areaGraph Δ).edgeSet := hA₂_le.edgeSet_subset he_A₂
      have hinca_Δ : (π.areaGraph Δ).Inc e a :=
        (inc_iff_of_le hA₂_le he_A₂).mp hinca
      have hincb_Δ : (π.areaGraph Δ).Inc e b :=
        (inc_iff_of_le hA₂_le he_A₂).mp hincb
      exact ⟨hab, e, hinca_Δ, hincb_Δ⟩
    have hlift_A₂ : ∀ {a b : α} (w : A₂.skeleton.Walk a b),
        ∃ w' : (π.areaGraph Δ).skeleton.Walk a b, w'.support = w.support := by
      intro a b w
      induction w with
      | nil => exact ⟨.nil, rfl⟩
      | @cons a x b hadj tail ih =>
        obtain ⟨tail', hsup⟩ := ih
        refine ⟨.cons (hstep_A₂ hadj) tail', ?_⟩
        dsimp [SimpleGraph.Walk.support]
        rw [hsup]
    let L' : Fin (q + 1) →
        PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus u₁) (π.borderPlus u₂) := fun i =>
      let w' := Classical.choose (hlift_A₂ (L i).walk)
      have hw'_sup : w'.support = (L i).walk.support :=
        Classical.choose_spec (hlift_A₂ (L i).walk)
      { first := (L i).first
        last := (L i).last
        walk := w'
        isPath := by
          rw [SimpleGraph.Walk.isPath_def, hw'_sup]
          exact (L i).isPath.support_nodup
        first_mem := (L i).first_mem
        last_mem := (L i).last_mem }
    have hL'_disj : Pairwise fun i j =>
        Disjoint {z | z ∈ (L' i).walk.support} {z | z ∈ (L' j).walk.support} := by
      intro i j hij
      have hi : (L' i).walk.support = (L i).walk.support :=
        Classical.choose_spec (hlift_A₂ (L i).walk)
      have hj : (L' j).walk.support = (L j).walk.support :=
        Classical.choose_spec (hlift_A₂ (L j).walk)
      simpa only [hi, hj] using hL_disj hij
    exact hlink_Δ L' hL'_disj

private theorem replacement_does_not_increase_internal_cells
    {S : Type} [TopologicalSpace S] (Γ Γ' : Painting S)
    {Δ c₀ c₁ c₂ : Set S} (hc₀ : c₀ ∈ Γ.C) (hc₀_int : ¬ (c₀ ∩ bd S).Nonempty)
    (hc₀_card : (tilde c₀).ncard = 3) (hc₁_int : ¬ (c₁ ∩ bd S).Nonempty)
    (hc₁_card : (tilde c₁).ncard = 3) (hc₂_bd : (c₂ ∩ bd S).Nonempty)
    (hc₀_not_I₂ : c₀ ∉ {c | c ∈ Γ.C ∧ c ⊆ Δᶜ})
    (hc₁_not_I₂ : c₁ ∉ {c | c ∈ Γ.C ∧ c ⊆ Δᶜ})
    (hC' : Γ'.C = insert c₁ (insert c₂ {c | c ∈ Γ.C ∧ c ⊆ Δᶜ})) :
    {c ∈ Γ'.C | ¬ (c ∩ bd S).Nonempty ∧ (tilde c).ncard = 3}.ncard ≤
      {c ∈ Γ.C | ¬ (c ∩ bd S).Nonempty ∧ (tilde c).ncard = 3}.ncard := by
  let I₂ := {c | c ∈ Γ.C ∧ c ⊆ Δᶜ}
  let B₀ := {c ∈ I₂ | ¬ (c ∩ bd S).Nonempty ∧ (tilde c).ncard = 3}
  have hB₀_fin : B₀.Finite := Γ.finite_cells.subset fun _ h => h.1.1
  have hset_new : {c ∈ Γ'.C | ¬ (c ∩ bd S).Nonempty ∧ (tilde c).ncard = 3} =
      insert c₁ B₀ := by
    ext c
    simp only [B₀, mem_ofPred_eq, hC', mem_insert_iff]
    constructor
    · rintro ⟨rfl | rfl | hc_I₂, hint, hcard_c⟩
      · exact Or.inl rfl
      · exact False.elim (hint hc₂_bd)
      · exact Or.inr ⟨hc_I₂, hint, hcard_c⟩
    · rintro (rfl | ⟨hc_I₂, hint, hcard_c⟩)
      · exact ⟨Or.inl rfl, hc₁_int, hc₁_card⟩
      · exact ⟨Or.inr (Or.inr hc_I₂), hint, hcard_c⟩
  have hc₁_not_B₀ : c₁ ∉ B₀ := fun h => hc₁_not_I₂ h.1
  have hsub_old : insert c₀ B₀ ⊆
      {c ∈ Γ.C | ¬ (c ∩ bd S).Nonempty ∧ (tilde c).ncard = 3} := by
    rintro c (rfl | ⟨hc_I₂, hint, hcard_c⟩)
    · exact ⟨hc₀, hc₀_int, hc₀_card⟩
    · exact ⟨hc_I₂.1, hint, hcard_c⟩
  have hc₀_not_B₀ : c₀ ∉ B₀ := fun h => hc₀_not_I₂ h.1
  rw [hset_new, ncard_insert_of_notMem hc₁_not_B₀ hB₀_fin]
  have hle_old := ncard_le_ncard hsub_old (Γ.finite_cells.subset fun _ h => h.1)
  rw [ncard_insert_of_notMem hc₀_not_B₀ hB₀_fin] at hle_old
  exact hle_old

private theorem replacement_preserves_truth_profile
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (π' : Portrayal G)
    (hπ'_central : π'.IsCentral 𝒯)
    (hπ'_resembles : π'.Resembles π)
    (htruth_le : ∀ (i : Fin 6), π'.truth i ≤ π.truth i) :
    ∀ (i : Fin 6), π'.truth i = π.truth i := by
  intro i
  refine le_antisymm (htruth_le i) ?_
  by_contra hlt
  have hex_lt : ∃ k : Fin 6, π'.truth k < π.truth k := ⟨i, lt_of_not_ge hlt⟩
  have hex_nat : ∃ n, ∃ hn : n < 6, π'.truth ⟨n, hn⟩ < π.truth ⟨n, hn⟩ := by
    rcases hex_lt with ⟨⟨n, hn⟩, h⟩
    exact ⟨n, hn, h⟩
  let m := Nat.find hex_nat
  obtain ⟨hm6, hm_lt⟩ := Nat.find_spec hex_nat
  have htruer : π'.IsTruer π := by
    refine ⟨⟨m, hm6⟩, fun j hj => ?_, hm_lt⟩
    apply le_antisymm (htruth_le j)
    by_contra hlt_j
    exact Nat.find_min hex_nat hj ⟨j.2, lt_of_not_ge hlt_j⟩
  exact htrue.2.2 π' hπ'_central htruer hπ'_resembles

private theorem replacement_portrayal_keeps_all_disc_nodes
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {θ : ℕ}
    {p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 4))
    (hwarp : π.warp ≤ p)
    (hθ : 6 * p + 8 < θ)
    {F : Set π.S}
    {Δ : Set π.S}
    {c₀ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {n₃ : π.S}
    (hnorm : π.Γ.IsNormal F)
    (hF : IsLineWithEnds F n₁ n₂)
    (hFbd : F ∩ bd π.S = {n₁, n₂})
    (hFN : F ∩ π.Γ.N = {n₁, n₂, n₃})
    (hFN_card : (F ∩ π.Γ.N).ncard = 3)
    (hΔ : IsClosedDisc Δ)
    (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ))
    (hF_bd : F ⊆ discBd Δ)
    (hbd_sub : discBd Δ ⊆ F ∪ bd π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Δ : c₀ ⊆ Δ)
    (hc₀_card : (tilde c₀).ncard = 3)
    [T2Space π.S]
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.areaGraph Δ).IsSeparation A₁ A₂)
    (hinter_V : (A₁ ∩ A₂).vertexSet = {π.nodeVertex n₁, π.nodeVertex n₂})
    (hn₃_A₁ : π.nodeVertex n₃ ∈ A₁.vertexSet)
    (hbs_A₂ : π.borderSet n₁ ∪ π.borderSet n₂ ⊆ A₂.vertexSet)
    (hθ3 : 4 * p + 5 < θ)
    (hdom : π.domγ = π.Γ.N)
    (Γ' : Painting π.S)
    (Θ : Set π.S)
    (c₁ : Set π.S)
    (c₂ : Set π.S)
    (hN'_eq : Γ'.N = π.Γ.N \ Δ ∪ {n₁, n₂, n₃})
    (hN'_sub : Γ'.N ⊆ π.Γ.N)
    (hΘ : Θ ∈ cuffs π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hbd_Θ : discBd Δ ⊆ F ∪ Θ)
    (hdich : ∀ c ∈ π.Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ)
    (htilde_I₂ : ∀ c ∈ π.Γ.C, c ⊆ Δᶜ → tilde c ⊆ Γ'.N)
    (hc₁_mem : c₁ ∈ Γ'.C)
    (hc₁_int : ¬(c₁ ∩ bd π.S).Nonempty)
    (htilde_c₁ : tilde c₁ = {n₁, n₂, n₃})
    (hc₂_mem : c₂ ∈ Γ'.C)
    (hc₂_Θ : (c₂ ∩ Θ).Nonempty)
    (htilde_c₂ : tilde c₂ = {n₁, n₂})
    (hc₁_ne_c₂ : c₁ ≠ c₂)
    (hc₁_not_I₂ : c₁ ∉ {c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ})
    (hc₂_not_I₂ : c₂ ∉ {c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ})
    (hC' : Γ'.C = insert c₁ (insert c₂ {c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ}))
    (hΘ_bd : Θ ⊆ bd π.S)
    (hc₂_bd : (c₂ ∩ bd π.S).Nonempty)
    (hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S)
    (hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S)
    (hn₃_FN : n₃ ∈ F ∩ π.Γ.N)
    (hn₁_dom : n₁ ∈ π.domγ)
    (hn₂_dom : n₂ ∈ π.domγ)
    (hn₃_dom : n₃ ∈ π.domγ)
    (hne₁₂ : n₁ ≠ n₂)
    (hne₃₁ : n₃ ≠ n₁)
    (hne₃₂ : n₃ ≠ n₂)
    (hn₁_A₁A₂ : π.nodeVertex n₁ ∈ (A₁ ∩ A₂).vertexSet)
    (hn₂_A₁A₂ : π.nodeVertex n₂ ∈ (A₁ ∩ A₂).vertexSet)
    (hn₃_not_A₂ : π.nodeVertex n₃ ∉ A₂.vertexSet)
    (hbp_c₂_sub_A₂ : ∀ {n : π.S}, n ∈ tilde c₂ → π.borderPlus n ⊆ A₂.vertexSet)
    (htilde_c₂_N' : tilde c₂ ⊆ Γ'.N ∩ bd π.S)
    (htilde_c₁_N' : tilde c₁ ⊆ Γ'.N)
    (hdisj_I : Disjoint ({c | c ∈ π.Γ.C ∧ c ⊆ Δ}) ({c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ}))
    (hinter_I₁_I₂ : (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion ({c | c ∈ π.Γ.C ∧ c ⊆
      Δᶜ})).vertexSet ⊆ π.borderSet n₁ ∪ π.borderSet n₂ ∪ {π.nodeVertex n₁, π.nodeVertex n₂,
      π.nodeVertex n₃})
    (cellG : Set π.S → Hypergraph α β)
    (hcellG_c₁ : cellG c₁ = A₁)
    (hcellG_c₂ : cellG c₂ = A₂)
    (hcellG_I₂ : ∀ {c : Set π.S}, c ∈ ({c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ}) → cellG c = π.cellGraph c)
    (hA₁_le_G : A₁ ≤ G)
    (hA₂_le_G : A₂ ≤ G) :
    tilde c₀ = Δ ∩ π.Γ.N := by
  let I₁ := {c | c ∈ π.Γ.C ∧ c ⊆ Δ}
  let I₂ := {c | c ∈ π.Γ.C ∧ c ⊆ Δᶜ}
  let π' : Portrayal G :=
    portrayal_after_two_cell_replacement (α := α) (β := β) (G := G) π (F := F) (Δ := Δ)
      (n₁ := n₁) (n₂ := n₂) (n₃ := n₃) hF hFbd hFN A₁ A₂ hsep hinter_V hn₃_A₁ hbs_A₂ Γ' Θ c₁ c₂
      hN'_eq hN'_sub hn₁_Θ hn₂_Θ hdich htilde_I₂ hc₁_mem hc₁_int htilde_c₁ hc₂_mem hc₂_Θ
      htilde_c₂ hc₁_ne_c₂ hc₁_not_I₂ hc₂_not_I₂ hC' hc₂_bd hn₁_bd hn₂_bd hn₃_FN hn₁_dom
      hn₂_dom hn₃_dom hne₁₂ hne₃₁ hne₃₂ hn₁_A₁A₂ hn₂_A₁A₂ hn₃_not_A₂ hbp_c₂_sub_A₂ htilde_c₂_N'
      htilde_c₁_N' hdisj_I hinter_I₁_I₂ cellG hcellG_c₁ hcellG_c₂ hcellG_I₂ hA₁_le_G hA₂_le_G
  have hbp'_eq : ∀ {n : π.S}, n ∈ Γ'.N → π'.borderPlus n = π.borderPlus n := by
    intro n hn
    ext v
    change (v ∈ π.borderSet n ∨ n ∈ π.domγ ∩ Γ'.N ∧ v = π.nodeVertex n) ↔
      (v ∈ π.borderSet n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n)
    exact or_congr_right ⟨fun ⟨h, hv⟩ => ⟨h.1, hv⟩, fun ⟨h, hv⟩ => ⟨⟨h, hn⟩, hv⟩⟩
  have hcw_I₂ : ∀ {c : Set π.S}, c ∈ I₂ → (c ∩ bd π.S).Nonempty →
      π'.cellWarp c = π.cellWarp c := by
    intro c hc_I₂ _
    have hcg : π'.cellGraph c = π.cellGraph c := hcellG_I₂ hc_I₂
    have hnt_N' : ∀ {n : π.S}, n ∈ tilde c → n ∈ Γ'.N :=
      fun hn => htilde_I₂ c hc_I₂.1 hc_I₂.2 hn
    have hiff : ∀ q : ℕ, π'.CellWarpLE c q ↔ π.CellWarpLE c q := by
      intro q
      simp only [Portrayal.CellWarpLE, hcg]
      refine forall₂_congr fun u₁ hu₁ => forall₂_congr fun u₂ hu₂ =>
        forall_congr' fun _ => ?_
      rw [hbp'_eq (hnt_N' hu₁), hbp'_eq (hnt_N' hu₂)]
    change sInf {p | π'.CellWarpLE c p} = sInf {p | π.CellWarpLE c p}
    congr 1; ext p; exact hiff p
  let q := π.warpAt Θ
  have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hbs_le_q : ∀ {n : π.S}, n ∈ π.Γ.N ∩ Θ → (π.borderSet n).ncard ≤ q := by
    intro n hn_Θ
    obtain ⟨E⟩ := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
    have hn_range : n ∈ Set.range E.node := by rw [E.range_node]; exact hn_Θ
    rcases hn_range with ⟨i, rfl⟩
    have hc_range : E.cell i ∈ {d ∈ π.Γ.C | (d ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact mem_range_self i
    have hbd_c : (E.cell i ∩ bd π.S).Nonempty :=
      hc_range.2.mono (inter_subset_inter_right _ hΘ_bd)
    have hn_t : E.node i ∈ tilde (E.cell i) := by
      rw [E.cell_tilde i]; exact mem_insert _ _
    exact (π.ncard_borderSet_le_cellWarp hc_range.1 hbd_c hn_t).trans
      (π.cellWarp_le_warpAt hc_range.1 hc_range.2)
  have hcw_c₂ : π'.cellWarp c₂ ≤ q := by
    apply csInf_le (OrderBot.bddBelow _)
    intro u₁ hu₁ u₂ hu₂ hu_ne
    have hcg_c₂ : π'.cellGraph c₂ = A₂ := hcellG_c₂
    rw [hbp'_eq (htilde_c₂_N' hu₁).1, hbp'_eq (htilde_c₂_N' hu₂).1, hcg_c₂]
    exact replacement_border_linkage h𝒯 π htrue hred hwarp hθ hnorm hF hFbd hFN_card
      hΔ hsmall hF_bd hbd_sub hsep.right_le hdom hΘ hn₁_Θ hn₂_Θ hbd_Θ htilde_c₂ hΘ_bd
      hbs_le_q u₁ hu₁ u₂ hu₂ hu_ne
  have hwarpAt_le : ∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' ≤ π.warpAt Θ' := by
    intro Θ' hΘ'
    apply csSup_le'
    rintro r ⟨c, hc_mem, hc_Θ', rfl⟩
    have hΘ'_bd : Θ' ⊆ bd π.S := by
      rcases hΘ' with ⟨x₀, _, rfl⟩
      exact connectedComponentIn_subset (bd π.S) x₀
    have hbd_c : (c ∩ bd π.S).Nonempty := hc_Θ'.mono (inter_subset_inter_right _ hΘ'_bd)
    rcases hC' ▸ hc_mem with h1 | h2 | hc_I₂
    · exact False.elim (hc₁_int (h1 ▸ hbd_c))
    · have hΘ'_eq : Θ' = Θ :=
        (Γ'.border_cell_subset_cuff hc₂_mem hΘ hc₂_Θ).2.2.2.2 Θ' hΘ' (h2 ▸ hc_Θ')
      rw [h2, hΘ'_eq]
      exact hcw_c₂
    · rw [hcw_I₂ hc_I₂ hbd_c]
      exact π.cellWarp_le_warpAt hc_I₂.1 hc_Θ'
  have hwarp' : π'.warp ≤ p := by
    have hne_cuffs : (cuffs π'.S).Nonempty := ⟨Θ, hΘ⟩
    have hSup_bdd : ∀ r ∈ {r | ∃ Θ' ∈ cuffs π'.S, r = π'.warpAt Θ'}, r ≤ p := by
      rintro r ⟨Θ', hΘ', rfl⟩
      exact (hwarpAt_le Θ' hΘ').trans ((π.warpAt_le_warp hΘ').trans hwarp)
    unfold Portrayal.warp
    rw [ite_eq_left hne_cuffs]
    exact max_le (π.one_le_warp.trans hwarp) (csSup_le ⟨π'.warpAt Θ, Θ, hΘ, rfl⟩ hSup_bdd)
  have hπ'_central : π'.IsCentral 𝒯 := by
    intro c hc_mem
    have hatt_lt : (attachments G (π'.cellGraph c)).ncard < θ := by
      have hle := π'.ncard_attachments_cellGraph_le hwarp' hc_mem
      omega
    change IsSmallWrt 𝒯 (cellG c)
    change (attachments G (cellG c)).ncard < θ at hatt_lt
    rcases hC' ▸ hc_mem with h1 | h2 | hc_I₂
    · rw [h1, hcellG_c₁] at hatt_lt ⊢
      exact hsmall.mono h𝒯 hsep.left_le hatt_lt
    · rw [h2, hcellG_c₂] at hatt_lt ⊢
      exact hsmall.mono h𝒯 hsep.right_le hatt_lt
    · rw [hcellG_I₂ hc_I₂]
      exact htrue.1 c hc_I₂.1
  have hzero_red : π.IsZeroRedundant 𝒯 := hred.isZeroRedundant h𝒯
  have hwarpAt_eq : ∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' = π.warpAt Θ' := by
    intro Θ' hΘ'
    refine le_antisymm (hwarpAt_le Θ' hΘ') ?_
    by_contra hlt
    have hlt' : π'.warpAt Θ' < π.warpAt Θ' := lt_of_not_ge hlt
    have hsimpler : π'.IsSimpler π := by
      right
      refine ⟨Homeomorph.refl π.S, ?_, Θ', hΘ', ?_⟩
      · intro Θ'' hΘ''
        rw [Homeomorph.refl_apply, image_id]
        exact hwarpAt_le Θ'' hΘ''
      · rw [Homeomorph.refl_apply, image_id]
        exact hlt'
    exact hzero_red π' hπ'_central hsimpler
  have hπ'_resembles : π'.Resembles π := by
    refine ⟨Homeomorph.refl π.S, fun Θ' hΘ' => ?_⟩
    rw [Homeomorph.refl_apply, image_id]
    exact hwarpAt_eq Θ' hΘ'
  -- Compare `π'.truth` and `π.truth`.
  have hc₁_card : (tilde c₁).ncard = 3 := by
    rw [← hFN_card, hFN, htilde_c₁]
  have htruth_sub_pos : ∀ i : Fin 6, 0 < i.1 → i.1 < 4 →
      {c ∈ Γ'.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - i.1} ⊆
      {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - i.1} := by
    intro i hi_pos _ c ⟨hc_mem, hint, hcard_c⟩
    have hne₁ : c ≠ c₁ := by
      rintro rfl
      omega
    have hne₂ : c ≠ c₂ := fun h => hint (h ▸ hc₂_bd)
    exact ⟨(((hC' ▸ hc_mem).resolve_left hne₁).resolve_left hne₂).1, hint, hcard_c⟩
  have hc₀_int : ¬ (c₀ ∩ bd π.S).Nonempty := by
    intro hbd₀
    obtain ⟨u₀, v₀, hne_uv, htilde₀, _, _, _, _⟩ := π.Γ.border_cell_exists_ends hc₀ hbd₀
    have h2 : (tilde c₀).ncard = 2 := by rw [htilde₀, ncard_pair hne_uv]
    omega
  have htruth_le_0 : π'.truth 0 ≤ π.truth 0 := by
    simp only [Portrayal.truth, Fin.val_zero, Nat.sub_zero, show (0 : ℕ) < 4 by decide, ↓reduceIte]
    exact replacement_does_not_increase_internal_cells π.Γ Γ' hc₀ hc₀_int hc₀_card hc₁_int
      hc₁_card hc₂_bd (fun hc => Set.disjoint_left.mp hdisj_I ⟨hc₀, hc₀_Δ⟩ hc) hc₁_not_I₂ hC'
  have htruth_le : ∀ i : Fin 6, π'.truth i ≤ π.truth i := by
    intro i
    by_cases hi0 : i = 0
    · exact hi0 ▸ htruth_le_0
    · have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero (fun h => hi0 (Fin.ext h))
      simp only [Portrayal.truth]
      split_ifs with h4 h5
      · exact ncard_le_ncard (htruth_sub_pos i hi_pos h4)
          (π.Γ.finite_cells.subset fun _ h => h.1)
      · exact ncard_le_ncard (sdiff_subset_sdiff hN'_sub Subset.rfl)
          (π.Γ.finite_N.subset sdiff_subset)
      · exact ncard_le_ncard (inter_subset_inter_left _ hN'_sub)
          (π.Γ.finite_N.subset inter_subset_left)
  have htruth_eq : ∀ i : Fin 6, π'.truth i = π.truth i := by
    exact replacement_preserves_truth_profile (α := α) (β := β) (G := G) (𝒯 := 𝒯) π htrue π'
      hπ'_central hπ'_resembles htruth_le
  have hN_int_eq : Γ'.N \ bd π.S = π.Γ.N \ bd π.S := by
    apply eq_of_subset_of_ncard_le (sdiff_subset_sdiff hN'_sub Subset.rfl) _
      (π.Γ.finite_N.subset sdiff_subset)
    have htr := htruth_eq ⟨4, by decide⟩
    simp only [Portrayal.truth] at htr
    exact htr.ge
  have hN_bd_eq : Γ'.N ∩ bd π.S = π.Γ.N ∩ bd π.S := by
    apply eq_of_subset_of_ncard_le (inter_subset_inter_left _ hN'_sub) _
      (π.Γ.finite_N.subset inter_subset_left)
    have htr := htruth_eq ⟨5, by decide⟩
    simp only [Portrayal.truth] at htr
    exact htr.ge
  have hN_eq_all : Γ'.N = π.Γ.N := by
    refine Subset.antisymm hN'_sub fun x hx => ?_
    by_cases hxbd : x ∈ bd π.S
    · have hx' : x ∈ π.Γ.N ∩ bd π.S := ⟨hx, hxbd⟩
      rw [← hN_bd_eq] at hx'
      exact hx'.1
    · have hx' : x ∈ π.Γ.N \ bd π.S := ⟨hx, hxbd⟩
      rw [← hN_int_eq] at hx'
      exact hx'.1
  have hΔ_N_sub : Δ ∩ π.Γ.N ⊆ {n₁, n₂, n₃} := by
    rintro x ⟨hxΔ, hxN⟩
    have hxN' : x ∈ Γ'.N := hN_eq_all.symm ▸ hxN
    rw [hN'_eq] at hxN'
    rcases hxN' with ⟨_, hx_notΔ⟩ | hx_tr
    · exact False.elim (hx_notΔ hxΔ)
    · exact hx_tr
  have htc₀_sub : tilde c₀ ⊆ Δ ∩ π.Γ.N :=
    fun x hx => ⟨closure_minimal hc₀_Δ hΔ.isClosed hx.1, π.Γ.tilde_subset_N hc₀ hx⟩
  have hΔ_N_fin : (Δ ∩ π.Γ.N).Finite := π.Γ.finite_N.inter_of_right Δ
  have hΔ_N_le3 : (Δ ∩ π.Γ.N).ncard ≤ 3 := by
    have hfin_tr : ({n₁, n₂, n₃} : Set π.S).Finite := by
      rw [← hFN]; exact π.Γ.finite_N.inter_of_right F
    calc (Δ ∩ π.Γ.N).ncard
      _ ≤ ({n₁, n₂, n₃} : Set π.S).ncard := ncard_le_ncard hΔ_N_sub hfin_tr
      _ = 3 := by rw [← hFN, hFN_card]
  exact eq_of_subset_of_ncard_le htc₀_sub (by omega) hΔ_N_fin

/-- **Graph Minors XVII, (11.3)** (pages 192–193):
"Let $F \subseteq \Sigma$ be a $\Gamma$-normal $I$-arc with $F \cap N(\Gamma) = \{n_1, n_2, n_3\}$,
where $F$ has ends $n_1, n_2$, and let $\Delta \subseteq \Sigma$ be the disc with $\alpha(\Delta)$
small and $F \subseteq \operatorname{bd}(\Delta) \subseteq F \cup \operatorname{bd}(\Sigma)$.
Suppose that there is a cell $c_0 \subseteq \Delta$ with $|\tilde{c}_0| = 3$. Then either
(i) $\tilde{c}_0 = \Delta \cap N(\Gamma)$ or
(ii) there is no separation $(A_1, A_2)$ of $\alpha(\Delta)$ with
$V(A_1 \cap A_2) = \{\gamma(n_1), \gamma(n_2)\}$, $\gamma(n_3) \in V(A_1)$, and
$\beta(n_1) \cup \beta(n_2) \subseteq V(A_2)$." -/
theorem theorem_11_3_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 4))
    (hwarp : π.warp ≤ p)
    (hθ : 6 * p + 8 < θ)
    {F Δ c₀ : Set π.S} {n₁ n₂ n₃ : π.S}
    (hnorm : π.Γ.IsNormal F) (hF : IsLineWithEnds F n₁ n₂)
    (hFbd : F ∩ bd π.S = {n₁, n₂})
    (hFN : F ∩ π.Γ.N = {n₁, n₂, n₃}) (hFN_card : (F ∩ π.Γ.N).ncard = 3)
    (hΔ : IsClosedDisc Δ) (hsmall : IsSmallWrt 𝒯 (π.areaGraph Δ))
    (hF_bd : F ⊆ discBd Δ) (hbd_sub : discBd Δ ⊆ F ∪ bd π.S)
    (hc₀ : c₀ ∈ π.Γ.C) (hc₀_Δ : c₀ ⊆ Δ) (hc₀_card : (tilde c₀).ncard = 3) :
    tilde c₀ = Δ ∩ π.Γ.N ∨
    ¬ ∃ A₁ A₂ : Hypergraph α β,
        (π.areaGraph Δ).IsSeparation A₁ A₂ ∧
        (A₁ ∩ A₂).vertexSet = {π.nodeVertex n₁, π.nodeVertex n₂} ∧
        π.nodeVertex n₃ ∈ A₁.vertexSet ∧
        π.borderSet n₁ ∪ π.borderSet n₂ ⊆ A₂.vertexSet := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have : ConnectedSpace π.S := π.connected
  by_cases hex_sep : ∃ A₁ A₂ : Hypergraph α β,
      (π.areaGraph Δ).IsSeparation A₁ A₂ ∧
      (A₁ ∩ A₂).vertexSet = {π.nodeVertex n₁, π.nodeVertex n₂} ∧
      π.nodeVertex n₃ ∈ A₁.vertexSet ∧
      π.borderSet n₁ ∪ π.borderSet n₂ ⊆ A₂.vertexSet
  · left
    rcases hex_sep with ⟨A₁, A₂, hsep, hinter_V, hn₃_A₁, hbs_A₂⟩
    have hred3 : π.IsRedundant 𝒯 θ (2 * p + 3) := hred.mono (by omega)
    have hθ3 : 4 * p + 5 < θ := by omega
    have hdom : π.domγ = π.Γ.N :=
      theorem_8_4_proof
        h𝒯 π htrue hred3 hwarp hθ3
    obtain ⟨Γ', Θ, c₁, c₂,
        hN'_eq, hN'_sub, hΘ, hn₁_Θ, hn₂_Θ, hbd_Θ, hdich, htilde_I₂,
        hc₁_mem, hc₁_int, htilde_c₁,
        hc₂_mem, hc₂_Θ, htilde_c₂,
        hc₁_ne_c₂, hc₁_not_I₂, hc₂_not_I₂, hC'⟩ :=
      GraphMinor.GM17.threeNodeIArcReplaceDisc π.S π.isSurface π.Γ n₁ n₂ n₃ F Δ hnorm hF hFbd hFN
        hFN_card hΔ hF_bd hbd_sub
    let I₁ : Set (Set π.S) := {c ∈ π.Γ.C | c ⊆ Δ}
    let I₂ : Set (Set π.S) := {c ∈ π.Γ.C | c ⊆ Δᶜ}
    have hΘ_bd : Θ ⊆ bd π.S := by
      rcases hΘ with ⟨x₀, _, rfl⟩
      exact connectedComponentIn_subset (bd π.S) x₀
    have hc₂_bd : (c₂ ∩ bd π.S).Nonempty := hc₂_Θ.mono (inter_subset_inter_right _ hΘ_bd)
    have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S := ⟨hn₁_Θ.1, hΘ_bd hn₁_Θ.2⟩
    have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S := ⟨hn₂_Θ.1, hΘ_bd hn₂_Θ.2⟩
    have hn₃_FN : n₃ ∈ F ∩ π.Γ.N := hFN ▸ Or.inr (Or.inr rfl)
    have hn₁_dom : n₁ ∈ π.domγ := hdom ▸ hn₁_Θ.1
    have hn₂_dom : n₂ ∈ π.domγ := hdom ▸ hn₂_Θ.1
    have hn₃_dom : n₃ ∈ π.domγ := hdom ▸ hn₃_FN.2
    have hne₁₂ : n₁ ≠ n₂ := ne_of_isLineWithEnds hF
    have hne₃₁ : n₃ ≠ n₁ := by
      rintro rfl
      have hsub : F ∩ π.Γ.N ⊆ {n₃, n₂} := by
        rw [hFN]
        rintro x (rfl | rfl | rfl) <;> simp
      have hle : (F ∩ π.Γ.N).ncard ≤ 2 :=
        (ncard_le_ncard hsub ((finite_singleton n₂).insert n₃)).trans (ncard_pair hne₁₂).le
      omega
    have hne₃₂ : n₃ ≠ n₂ := by
      rintro rfl
      have hsub : F ∩ π.Γ.N ⊆ {n₁, n₃} := by
        rw [hFN]
        rintro x (rfl | rfl | rfl) <;> simp
      have hle : (F ∩ π.Γ.N).ncard ≤ 2 :=
        (ncard_le_ncard hsub ((finite_singleton n₃).insert n₁)).trans (ncard_pair hne₁₂).le
      omega
    have hn₁_A₁A₂ : π.nodeVertex n₁ ∈ (A₁ ∩ A₂).vertexSet :=
      hinter_V ▸ mem_insert _ _
    have hn₂_A₁A₂ : π.nodeVertex n₂ ∈ (A₁ ∩ A₂).vertexSet :=
      hinter_V ▸ mem_insert_of_mem _ rfl
    have hn₃_not_A₂ : π.nodeVertex n₃ ∉ A₂.vertexSet := by
      intro hn₃_A₂
      have hmem : π.nodeVertex n₃ ∈ ({π.nodeVertex n₁, π.nodeVertex n₂} : Set α) :=
        hinter_V ▸ ⟨hn₃_A₁, hn₃_A₂⟩
      rcases hmem with hEq | hEq
      · exact hne₃₁ (π.nodeVertex_injOn hn₃_dom hn₁_dom hEq)
      · exact hne₃₂ (π.nodeVertex_injOn hn₃_dom hn₂_dom hEq)
    have hbp_c₂_sub_A₂ : ∀ {n : π.S}, n ∈ tilde c₂ → π.borderPlus n ⊆ A₂.vertexSet := by
      intro n hn
      rw [htilde_c₂] at hn
      rcases hn with rfl | rfl
      · rintro v (hv | ⟨_, rfl⟩)
        · exact hbs_A₂ (Or.inl hv)
        · exact hn₁_A₁A₂.2
      · rintro v (hv | ⟨_, rfl⟩)
        · exact hbs_A₂ (Or.inr hv)
        · exact hn₂_A₁A₂.2
    have htilde_c₂_N' : tilde c₂ ⊆ Γ'.N ∩ bd π.S := by
      intro x hx
      rw [htilde_c₂] at hx
      rcases hx with rfl | rfl
      · exact ⟨hN'_eq ▸ Or.inr (Or.inl rfl), hn₁_bd.2⟩
      · exact ⟨hN'_eq ▸ Or.inr (Or.inr (Or.inl rfl)), hn₂_bd.2⟩
    have htilde_c₁_N' : tilde c₁ ⊆ Γ'.N := by
      intro x hx
      rw [htilde_c₁] at hx
      exact hN'_eq ▸ Or.inr hx
    have hpart : I₁ ∪ I₂ = π.Γ.C := by
      refine Subset.antisymm (union_subset (fun _ h => h.1) (fun _ h => h.1)) fun c hc => ?_
      rcases hdich c hc with hc_in | hc_out
      · exact Or.inl ⟨hc, hc_in⟩
      · exact Or.inr ⟨hc, hc_out⟩
    have hdisj_I : Disjoint I₁ I₂ := by
      rw [Set.disjoint_left]
      intro c hc₁ hc₂
      obtain ⟨x, hx⟩ := π.Γ.cell_nonempty hc₁.1
      exact hc₂.2 hx (hc₁.2 hx)
    have hinter_I₁_I₂ : (π.areaGraph Δ).vertexSet ∩ (π.cellsUnion I₂).vertexSet ⊆
        π.borderSet n₁ ∪ π.borderSet n₂ ∪
          {π.nodeVertex n₁, π.nodeVertex n₂, π.nodeVertex n₃} := by
      exact area_cells_share_only_frontier_vertices (α := α) (β := β) (G := G) π (F := F) (Δ := Δ)
        (n₁ := n₁) (n₂ := n₂) (n₃ := n₃) hF hFbd hFN hΔ A₁ A₂ hinter_V hn₃_A₁ hbs_A₂ Γ' Θ c₁ c₂
        hN'_eq hn₁_Θ hn₂_Θ htilde_I₂ htilde_c₁ htilde_c₂   hn₁_bd hn₂_bd hn₃_FN hn₁_dom
        hn₂_dom hn₃_dom hne₁₂ hne₃₁ hne₃₂ hn₁_A₁A₂ hn₂_A₁A₂ hn₃_not_A₂ hpart hdisj_I
    let cellG : Set π.S → Hypergraph α β := fun c =>
      if c = c₁ then A₁ else if c = c₂ then A₂ else π.cellGraph c
    have hcellG_c₁ : cellG c₁ = A₁ := by dsimp [cellG]; rw [ite_eq_left rfl]
    have hcellG_c₂ : cellG c₂ = A₂ := by
      dsimp [cellG]; rw [ite_eq_right hc₁_ne_c₂.symm, ite_eq_left rfl]
    have hcellG_I₂ : ∀ {c : Set π.S}, c ∈ I₂ → cellG c = π.cellGraph c := by
      intro c hc
      have h1 : c ≠ c₁ := by rintro rfl; exact hc₁_not_I₂ hc
      have h2 : c ≠ c₂ := by rintro rfl; exact hc₂_not_I₂ hc
      dsimp [cellG]; rw [ite_eq_right h1, ite_eq_right h2]
    have hA₁_le_G : A₁ ≤ G := hsep.left_le.trans (π.cellsUnion_le I₁)
    have hA₂_le_G : A₂ ≤ G := hsep.right_le.trans (π.cellsUnion_le I₁)
    have replacementForcesNodes : tilde c₀ = Δ ∩ π.Γ.N := by
      exact replacement_portrayal_keeps_all_disc_nodes (α := α) (β := β) (G := G) (𝒯 := 𝒯) (θ :=
        θ) (p := p) h𝒯 π htrue hred hwarp hθ (F := F) (Δ := Δ) (c₀ := c₀) (n₁ := n₁) (n₂ := n₂)
        (n₃ := n₃) hnorm hF hFbd hFN hFN_card hΔ hsmall hF_bd hbd_sub hc₀ hc₀_Δ hc₀_card A₁ A₂
        hsep hinter_V hn₃_A₁ hbs_A₂ hθ3 hdom Γ' Θ c₁ c₂ hN'_eq hN'_sub hΘ hn₁_Θ hn₂_Θ hbd_Θ hdich
        htilde_I₂ hc₁_mem hc₁_int htilde_c₁ hc₂_mem hc₂_Θ htilde_c₂ hc₁_ne_c₂ hc₁_not_I₂
        hc₂_not_I₂ hC' hΘ_bd hc₂_bd hn₁_bd hn₂_bd hn₃_FN hn₁_dom hn₂_dom hn₃_dom hne₁₂ hne₃₁ hne₃₂
        hn₁_A₁A₂ hn₂_A₁A₂ hn₃_not_A₂ hbp_c₂_sub_A₂ htilde_c₂_N' htilde_c₁_N' hdisj_I hinter_I₁_I₂
        cellG hcellG_c₁ hcellG_c₂ hcellG_I₂ hA₁_le_G hA₂_le_G
    exact replacementForcesNodes
  · exact Or.inr hex_sep

/-! ## 5. Standard Linkage Union $S$ and Crossing Cells $D(A, B)$: (11.4)–(11.7) (Pages 193–196) -/

namespace Portrayal.SystemOfStandardLinkages

variable {α : Type u} {β : Type v} {G : Hypergraph α β} {π : Portrayal G}

private lemma walk_support_subset_vertexSet {H : Hypergraph α β} {u v : α}
    (hu : u ∈ H.vertexSet) (W : H.skeleton.Walk u v) :
    {z | z ∈ W.support} ⊆ H.vertexSet :=
  fun _ hz => Hypergraph.skeleton_walk_support_subset_vertexSet W hu _ hz

theorem cellSet_subset_cellGraph (sys : π.SystemOfStandardLinkages)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (i : Fin (π.Γ.N ∩ Θ).ncard) :
    sys.cellSet Θ hΘ i ⊆ (π.cellGraph ((sys.E Θ hΘ).cell i)).vertexSet := by
  intro z hz
  rw [cellSet, mem_iUnion] at hz
  rcases hz with ⟨j, hzj⟩
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hbd_i : ((sys.E Θ hΘ).cell i ∩ bd π.S).Nonempty :=
    ((sys.E Θ hΘ).cell_inter_cuff_nonempty i).mono (inter_subset_inter_right _ hΘ_bd)
  have hfirst_mem : ((sys.SL Θ hΘ).L i j).first ∈ (π.cellGraph ((sys.E Θ hΘ).cell i)).vertexSet :=
    π.p3_subset ((sys.E Θ hΘ).cell i) ((sys.E Θ hΘ).cell_mem i) hbd_i ((sys.E Θ hΘ).node i)
      (((sys.E Θ hΘ).cell_tilde i) ▸ mem_insert _ _) (((sys.SL Θ hΘ).L i j).first_mem)
  exact walk_support_subset_vertexSet hfirst_mem ((sys.SL Θ hΘ).L i j).walk hzj

end Portrayal.SystemOfStandardLinkages

/-- Existence of a `SystemOfStandardLinkages` from (9.8) (`exists_cuffStandardLinkages`). -/
theorem exists_systemOfStandardLinkages
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) :
    Nonempty π.SystemOfStandardLinkages := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hexE : ∀ Θ ∈ cuffs π.S, Nonempty (π.Γ.CuffEnumeration Θ (π.Γ.N ∩ Θ).ncard) := by
    intro Θ hΘ
    have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
    exact π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  let E_fn : ∀ Θ ∈ cuffs π.S, π.Γ.CuffEnumeration Θ (π.Γ.N ∩ Θ).ncard :=
    fun Θ hΘ => Classical.choice (hexE Θ hΘ)
  let SL_fn : ∀ Θ (hΘ : Θ ∈ cuffs π.S),
      CuffStandardLinkages π Θ (π.Γ.N ∩ Θ).ncard (π.warpAt Θ) (E_fn Θ hΘ) :=
    fun Θ hΘ => Classical.choice
      (exists_cuffStandardLinkages h𝒯 π htrue hred hwarp hθ (E_fn Θ hΘ))
  exact ⟨⟨E_fn, SL_fn⟩⟩

/-- For every node $n \in N(\Gamma)$, $\gamma(n)$ belongs to at least two distinct cells of
$\Gamma$,
and hence $\gamma(n) \in V(\alpha(-c))$ for every $c \in C(\Gamma)$ and $n \in N(\Gamma)$. -/
theorem Portrayal.gammaImage_N_subset_otherVertices
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    (c : Set π.S) :
    π.gammaImage π.Γ.N ⊆ π.otherVertices c := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have : ConnectedSpace π.S := π.connected
  rintro v ⟨n, ⟨hnN, hndom⟩, rfl⟩
  have h87 := (theorem_8_7_proof
    h𝒯 π htrue hred hwarp hθ hnN).1
  have hfin : {d ∈ π.Γ.CStar | n ∈ tilde d}.Finite :=
    π.Γ.finite_cells.subset fun _ hd => hd.1.1
  have hsub_ne : ({d ∈ π.Γ.CStar | n ∈ tilde d} \ {c}).Nonempty := by
    by_contra hemp
    have hsub : {d ∈ π.Γ.CStar | n ∈ tilde d} ⊆ {c} :=
      fun d hd => by_contra fun hne => hemp ⟨d, hd, hne⟩
    have hle1 : {d ∈ π.Γ.CStar | n ∈ tilde d}.ncard ≤ 1 :=
      (ncard_le_ncard hsub (finite_singleton c)).trans (ncard_singleton c).le
    omega
  obtain ⟨d, ⟨hd_star, hnd⟩, hd_ne⟩ := hsub_ne
  exact ⟨d, hd_star.1, mem_singleton_iff.not.mp hd_ne, π.p2 d hd_star.1 n ⟨hnd, hndom⟩⟩

/-- Disjointness of $\gamma(N(\Gamma))$ and $S$: $\gamma(N(\Gamma)) \cap S = \emptyset$. -/
theorem Portrayal.SystemOfStandardLinkages.disjoint_gammaImage_N_S
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    (sys : π.SystemOfStandardLinkages) :
    Disjoint (π.gammaImage π.Γ.N) sys.S := by
  rw [Set.disjoint_left]
  rintro v ⟨n, ⟨hnN, hndom⟩, rfl⟩ hvS
  rw [Portrayal.SystemOfStandardLinkages.S, mem_iUnion₂] at hvS
  rcases hvS with ⟨Θ, hΘ, hv_cuff⟩
  rw [Portrayal.SystemOfStandardLinkages.cuffSet, mem_iUnion] at hv_cuff
  rcases hv_cuff with ⟨i, hv_cell⟩
  have hvc : π.nodeVertex n ∈ (π.cellGraph ((sys.E Θ hΘ).cell i)).vertexSet :=
    sys.cellSet_subset_cellGraph hΘ i hv_cell
  have hvo : π.nodeVertex n ∈ π.otherVertices ((sys.E Θ hΘ).cell i) :=
    π.gammaImage_N_subset_otherVertices h𝒯 htrue hred hwarp hθ ((sys.E Θ hΘ).cell i)
      ⟨n, ⟨hnN, hndom⟩, rfl⟩
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hbd_i : ((sys.E Θ hΘ).cell i ∩ bd π.S).Nonempty :=
    ((sys.E Θ hΘ).cell_inter_cuff_nonempty i).mono (inter_subset_inter_right _ hΘ_bd)
  obtain ⟨m, hm_t, hvm_bp⟩ := π.p6_borderPlus ((sys.E Θ hΘ).cell_mem i) hbd_i hvc hvo
  have hk_pos : 0 < (π.Γ.N ∩ Θ).ncard := by have := (sys.E Θ hΘ).two_le; omega
  have htilde_i := (sys.E Θ hΘ).cell_tilde i
  have hn₁_t : (sys.E Θ hΘ).node i ∈ tilde ((sys.E Θ hΘ).cell i) :=
    htilde_i ▸ mem_insert _ _
  have hn₂_t : (sys.E Θ hΘ).node (cyclicSucc hk_pos i) ∈ tilde ((sys.E Θ hΘ).cell i) :=
    htilde_i ▸ mem_insert_of_mem _ (mem_singleton _)
  have hne₁₂ : (sys.E Θ hΘ).node i ≠ (sys.E Θ hΘ).node (cyclicSucc hk_pos i) :=
    (sys.E Θ hΘ).injective_node.ne (cyclicSucc_ne_self (sys.E Θ hΘ).two_le i).symm
  have h98 := theorem_9_8_proof h𝒯 π htrue hred hwarp hθ hΘ
    ((sys.E Θ hΘ).cell_mem i) ((sys.E Θ hΘ).cell_inter_cuff_nonempty i) hn₁_t hn₂_t hne₁₂
  rw [Portrayal.SystemOfStandardLinkages.cellSet, mem_iUnion] at hv_cell
  rcases hv_cell with ⟨j, hzj⟩
  rw [htilde_i] at hm_t
  rcases hm_t with rfl | rfl
  · rcases hvm_bp with hv_bs | ⟨_, hEq⟩
    · exact Set.disjoint_left.mp h98.2.2.1 hv_bs ⟨n, hnN, rfl⟩
    · exact (((sys.SL Θ hΘ).isStandard i).2.1 j).1 (hEq ▸ hzj)
  · rcases hvm_bp with hv_bs | ⟨_, hEq⟩
    · exact Set.disjoint_left.mp h98.2.2.2.1 hv_bs ⟨n, hnN, rfl⟩
    · exact (((sys.SL Θ hΘ).isStandard i).2.1 j).2 (hEq ▸ hzj)

/-- For every cuff $\Theta$ and index $i$, $\beta(n_i) \cup \beta(n_{i+1}) \subseteq \text{cellSet }
\Theta\ i$. -/
theorem Portrayal.SystemOfStandardLinkages.borderSet_subset_cellSet
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    (sys : π.SystemOfStandardLinkages)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (i : Fin (π.Γ.N ∩ Θ).ncard) :
    let hk_pos : 0 < (π.Γ.N ∩ Θ).ncard := by have := (sys.E Θ hΘ).two_le; omega
    (∀ r : Fin (π.Γ.N ∩ Θ).ncard, (π.borderSet ((sys.E Θ hΘ).node r)).ncard = π.warpAt Θ) ∧
    π.borderSet ((sys.E Θ hΘ).node i) ⊆ sys.cellSet Θ hΘ i ∧
    π.borderSet ((sys.E Θ hΘ).node (cyclicSucc hk_pos i)) ⊆ sys.cellSet Θ hΘ i := by
  intro hk_pos
  have hcard : ∀ r : Fin (π.Γ.N ∩ Θ).ncard,
      (π.borderSet ((sys.E Θ hΘ).node r)).ncard = π.warpAt Θ := by
    intro r
    have htilde_r := (sys.E Θ hΘ).cell_tilde r
    have hn₁_t : (sys.E Θ hΘ).node r ∈ tilde ((sys.E Θ hΘ).cell r) :=
      htilde_r ▸ mem_insert _ _
    have hn₂_t : (sys.E Θ hΘ).node (cyclicSucc hk_pos r) ∈ tilde ((sys.E Θ hΘ).cell r) :=
      htilde_r ▸ mem_insert_of_mem _ (mem_singleton _)
    have hne₁₂ : (sys.E Θ hΘ).node r ≠ (sys.E Θ hΘ).node (cyclicSucc hk_pos r) :=
      (sys.E Θ hΘ).injective_node.ne (cyclicSucc_ne_self (sys.E Θ hΘ).two_le r).symm
    exact (theorem_9_8_proof h𝒯 π htrue hred hwarp hθ hΘ
      ((sys.E Θ hΘ).cell_mem r) ((sys.E Θ hΘ).cell_inter_cuff_nonempty r) hn₁_t hn₂_t hne₁₂).1
  refine ⟨hcard, ?_, ?_⟩
  · intro u hu
    obtain ⟨j, hj⟩ := (sys.SL Θ hΘ).exists_first_eq hcard i hu
    exact mem_iUnion.mpr ⟨j, hj ▸ ((sys.SL Θ hΘ).L i j).walk.start_mem_support⟩
  · intro u hu
    obtain ⟨j, hj⟩ := (sys.SL Θ hΘ).exists_last_eq hcard i hu
    exact mem_iUnion.mpr ⟨j, hj ▸ ((sys.SL Θ hΘ).L i j).walk.end_mem_support⟩

/-- For an internal cell $c_0 \in C(\Gamma)$:
(1) $V(\alpha(c_0) \cap \alpha(-c_0)) = \gamma(\tilde{c}_0)$, and
(2) $V(\alpha(c_0)) \cap S = \emptyset$. -/
theorem Portrayal.SystemOfStandardLinkages.internal_cell_properties
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    (sys : π.SystemOfStandardLinkages)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) (hint : ¬ (c₀ ∩ bd π.S).Nonempty) :
    (π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀ = π.gammaImage (tilde c₀) ∧
    Disjoint (π.cellGraph c₀).vertexSet sys.S := by
  have hinter_eq : (π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀ = π.gammaImage (tilde c₀) := by
    refine Subset.antisymm (fun v ⟨hvc, hvo⟩ => π.p5 c₀ hc₀ hint v hvc hvo) ?_
    rintro v ⟨n, ⟨hnt, hndom⟩, rfl⟩
    exact ⟨π.p2 c₀ hc₀ n ⟨hnt, hndom⟩,
      π.gammaImage_N_subset_otherVertices h𝒯 htrue hred hwarp hθ c₀
        ⟨n, ⟨π.Γ.tilde_subset_N hc₀ hnt, hndom⟩, rfl⟩⟩
  refine ⟨hinter_eq, ?_⟩
  rw [Set.disjoint_left]
  intro v hvc hvS
  rw [Portrayal.SystemOfStandardLinkages.S, mem_iUnion₂] at hvS
  rcases hvS with ⟨Θ, hΘ, hv_cuff⟩
  rw [Portrayal.SystemOfStandardLinkages.cuffSet, mem_iUnion] at hv_cuff
  rcases hv_cuff with ⟨i, hv_cell⟩
  have hvd : v ∈ (π.cellGraph ((sys.E Θ hΘ).cell i)).vertexSet :=
    sys.cellSet_subset_cellGraph hΘ i hv_cell
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hbd_i : ((sys.E Θ hΘ).cell i ∩ bd π.S).Nonempty :=
    ((sys.E Θ hΘ).cell_inter_cuff_nonempty i).mono (inter_subset_inter_right _ hΘ_bd)
  have hd_ne : (sys.E Θ hΘ).cell i ≠ c₀ := fun h => hint (h ▸ hbd_i)
  have hvo : v ∈ π.otherVertices c₀ := ⟨(sys.E Θ hΘ).cell i, (sys.E Θ hΘ).cell_mem i, hd_ne, hvd⟩
  have hv_γ : v ∈ π.gammaImage (tilde c₀) := hinter_eq ▸ ⟨hvc, hvo⟩
  have hv_γN : v ∈ π.gammaImage π.Γ.N := by
    rcases hv_γ with ⟨n, ⟨hnt, hndom⟩, rfl⟩
    exact ⟨n, ⟨π.Γ.tilde_subset_N hc₀ hnt, hndom⟩, rfl⟩
  exact Set.disjoint_left.mp
    (sys.disjoint_gammaImage_N_S h𝒯 π htrue hred hwarp hθ)
    hv_γN (sys.cellSet_subset_S hΘ i hv_cell)

/-- For a border cell $c_0 = E.\text{cell } i$ on cuff $\Theta$:
(1) $V(\alpha(c_0) \cap \alpha(-c_0)) = (\beta(n_i) \cup \beta(n_{i+1})) \cup \gamma(\tilde{c}_0)$,
(2) $V(\alpha(c_0) \cap \alpha(-c_0)) \cap S = \beta(n_i) \cup \beta(n_{i+1})$,
(3) $V(\alpha(c_0) \cap \alpha(-c_0)) \setminus S = \gamma(\tilde{c}_0)$, and
(4) $V(\alpha(c_0)) \setminus (S \cup V(\alpha(-c_0))) = V(\alpha(c_0)) \setminus (\text{cellSet }
\Theta\ i \cup V(\alpha(-c_0)))$. -/
theorem Portrayal.SystemOfStandardLinkages.border_cell_properties
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    (sys : π.SystemOfStandardLinkages)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (i : Fin (π.Γ.N ∩ Θ).ncard) :
    let hk_pos : 0 < (π.Γ.N ∩ Θ).ncard := by have := (sys.E Θ hΘ).two_le; omega
    let c₀ := (sys.E Θ hΘ).cell i
    let n₁ := (sys.E Θ hΘ).node i
    let n₂ := (sys.E Θ hΘ).node (cyclicSucc hk_pos i)
    (π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀ =
      (π.borderSet n₁ ∪ π.borderSet n₂) ∪ π.gammaImage (tilde c₀) ∧
    ((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀) ∩ sys.S =
      π.borderSet n₁ ∪ π.borderSet n₂ ∧
    ((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀) \ sys.S =
      π.gammaImage (tilde c₀) ∧
    (π.cellGraph c₀).vertexSet \ (sys.S ∪ π.otherVertices c₀) =
      (π.cellGraph c₀).vertexSet \ (sys.cellSet Θ hΘ i ∪ π.otherVertices c₀) := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  intro hk_pos c₀ n₁ n₂
  have hc₀ : c₀ ∈ π.Γ.C := (sys.E Θ hΘ).cell_mem i
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hbd_c₀ : (c₀ ∩ bd π.S).Nonempty :=
    ((sys.E Θ hΘ).cell_inter_cuff_nonempty i).mono (inter_subset_inter_right _ hΘ_bd)
  have htilde_c₀ : tilde c₀ = {n₁, n₂} := (sys.E Θ hΘ).cell_tilde i
  have hn₁_t : n₁ ∈ tilde c₀ := htilde_c₀ ▸ mem_insert _ _
  have hn₂_t : n₂ ∈ tilde c₀ := htilde_c₀ ▸ mem_insert_of_mem _ (mem_singleton _)
  have hinter_eq : (π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀ =
      (π.borderSet n₁ ∪ π.borderSet n₂) ∪ π.gammaImage (tilde c₀) := by
    refine Subset.antisymm ?_ ?_
    · rintro v ⟨hvc, hvo⟩
      obtain ⟨m, hm_t, hvm_bp⟩ := π.p6_borderPlus hc₀ hbd_c₀ hvc hvo
      rcases hvm_bp with hv_bs | ⟨hmdom, rfl⟩
      · rw [htilde_c₀] at hm_t
        rcases hm_t with rfl | rfl
        · exact Or.inl (Or.inl hv_bs)
        · exact Or.inl (Or.inr hv_bs)
      · exact Or.inr ⟨m, ⟨hm_t, hmdom⟩, rfl⟩
    · rintro v ((hv_bs₁ | hv_bs₂) | ⟨m, ⟨hm_t, hmdom⟩, rfl⟩)
      · refine ⟨π.p3_subset c₀ hc₀ hbd_c₀ n₁ hn₁_t hv_bs₁, ?_⟩
        obtain ⟨r, hr_lt, hr_eq⟩ :=
          stepIdx_surjective (sys.E Θ hΘ).two_le (cyclicSucc hk_pos i) i
        have hr_pos : 0 < r := by
          by_contra hr0
          have hr_zero : r = 0 := by omega
          rw [hr_zero, stepIdx_zero] at hr_eq
          exact cyclicSucc_ne_self (sys.E Θ hΘ).two_le i hr_eq
        let prev := stepIdx (sys.E Θ hΘ).two_le (cyclicSucc hk_pos i) (r - 1)
        have hsucc_prev : cyclicSucc hk_pos prev = i := by
          rw [← stepIdx_succ, Nat.sub_add_cancel hr_pos, hr_eq]
        have hprev_ne : prev ≠ i := by
          rw [← hsucc_prev]
          exact (cyclicSucc_ne_self (sys.E Θ hΘ).two_le prev).symm
        have hcell_ne : (sys.E Θ hΘ).cell prev ≠ c₀ :=
          (sys.E Θ hΘ).injective_cell.ne hprev_ne
        have hbd_prev : ((sys.E Θ hΘ).cell prev ∩ bd π.S).Nonempty :=
          ((sys.E Θ hΘ).cell_inter_cuff_nonempty prev).mono (inter_subset_inter_right _ hΘ_bd)
        have hn₁_prev : n₁ ∈ tilde ((sys.E Θ hΘ).cell prev) := by
          rw [(sys.E Θ hΘ).cell_tilde prev]
          change n₁ ∈ {(sys.E Θ hΘ).node prev, (sys.E Θ hΘ).node (cyclicSucc hk_pos prev)}
          rw [hsucc_prev]
          exact mem_insert_of_mem _ (mem_singleton _)
        exact ⟨(sys.E Θ hΘ).cell prev, (sys.E Θ hΘ).cell_mem prev, hcell_ne,
          π.p3_subset ((sys.E Θ hΘ).cell prev) ((sys.E Θ hΘ).cell_mem prev) hbd_prev n₁
            hn₁_prev hv_bs₁⟩
      · refine ⟨π.p3_subset c₀ hc₀ hbd_c₀ n₂ hn₂_t hv_bs₂, ?_⟩
        let next := cyclicSucc hk_pos i
        have hnext_ne : next ≠ i := cyclicSucc_ne_self (sys.E Θ hΘ).two_le i
        have hcell_ne : (sys.E Θ hΘ).cell next ≠ c₀ :=
          (sys.E Θ hΘ).injective_cell.ne hnext_ne
        have hbd_next : ((sys.E Θ hΘ).cell next ∩ bd π.S).Nonempty :=
          ((sys.E Θ hΘ).cell_inter_cuff_nonempty next).mono (inter_subset_inter_right _ hΘ_bd)
        have hn₂_next : n₂ ∈ tilde ((sys.E Θ hΘ).cell next) := by
          rw [(sys.E Θ hΘ).cell_tilde next]
          exact mem_insert _ _
        exact ⟨(sys.E Θ hΘ).cell next, (sys.E Θ hΘ).cell_mem next, hcell_ne,
          π.p3_subset ((sys.E Θ hΘ).cell next) ((sys.E Θ hΘ).cell_mem next) hbd_next n₂
            hn₂_next hv_bs₂⟩
      · exact ⟨π.p2 c₀ hc₀ m ⟨hm_t, hmdom⟩,
          π.gammaImage_N_subset_otherVertices h𝒯 htrue hred hwarp hθ c₀
            ⟨m, ⟨π.Γ.tilde_subset_N hc₀ hm_t, hmdom⟩, rfl⟩⟩
  obtain ⟨_, hbs₁_sub, hbs₂_sub⟩ :=
    sys.borderSet_subset_cellSet h𝒯 π htrue hred hwarp hθ hΘ i
  have hbs_sub_S : π.borderSet n₁ ∪ π.borderSet n₂ ⊆ sys.S :=
    union_subset (hbs₁_sub.trans (sys.cellSet_subset_S hΘ i))
      (hbs₂_sub.trans (sys.cellSet_subset_S hΘ i))
  have hγ_disj_S : Disjoint (π.gammaImage (tilde c₀)) sys.S := by
    refine (sys.disjoint_gammaImage_N_S h𝒯 π htrue hred hwarp hθ).mono_left ?_
    rintro v ⟨m, ⟨hm_t, hmdom⟩, rfl⟩
    exact ⟨m, ⟨π.Γ.tilde_subset_N hc₀ hm_t, hmdom⟩, rfl⟩
  refine ⟨hinter_eq, ?_, ?_, ?_⟩
  · rw [hinter_eq, union_inter_distrib_right,
      inter_eq_self_of_subset_left hbs_sub_S,
      hγ_disj_S.inter_eq, union_empty]
  · have hbs_sdiff : (π.borderSet n₁ ∪ π.borderSet n₂) \ sys.S = ∅ :=
      eq_empty_of_forall_notMem fun x hx => hx.2 (hbs_sub_S hx.1)
    rw [hinter_eq, union_sdiff_distrib, hbs_sdiff, empty_union,
      hγ_disj_S.sdiff_eq_left]
  · ext v
    simp only [mem_sdiff, mem_union, not_or]
    refine and_congr_right fun hvc => ⟨fun ⟨hnotS, hnotO⟩ => ⟨fun hcell => hnotS
      (sys.cellSet_subset_S hΘ i hcell), hnotO⟩, ?_⟩
    rintro ⟨hnot_cell, hnotO⟩
    refine ⟨fun hvS => ?_, hnotO⟩
    rw [Portrayal.SystemOfStandardLinkages.S, mem_iUnion₂] at hvS
    rcases hvS with ⟨Θ', hΘ', hv_cuff⟩
    rw [Portrayal.SystemOfStandardLinkages.cuffSet, mem_iUnion] at hv_cuff
    rcases hv_cuff with ⟨i', hv_cell⟩
    have hvd' : v ∈ (π.cellGraph ((sys.E Θ' hΘ').cell i')).vertexSet :=
      sys.cellSet_subset_cellGraph hΘ' i' hv_cell
    by_cases hcell_eq : (sys.E Θ' hΘ').cell i' = c₀
    · have hΘ'_eq : Θ' = Θ :=
        (π.Γ.border_cell_subset_cuff hc₀ hΘ ((sys.E Θ hΘ).cell_inter_cuff_nonempty i)).2.2.2.2
          Θ' hΘ' (hcell_eq ▸ (sys.E Θ' hΘ').cell_inter_cuff_nonempty i')
      rcases hΘ'_eq with rfl
      have hi'_eq : i' = i := (sys.E Θ' hΘ').injective_cell hcell_eq
      rcases hi'_eq with rfl
      exact hnot_cell hv_cell
    · exact hnotO ⟨(sys.E Θ' hΘ').cell i', (sys.E Θ' hΘ').cell_mem i', hcell_eq, hvd'⟩

/-- **Graph Minors XVII, (11.4)** (pages 193–194):
"For any separation $(A, B)$ of $G$, if $d \in D(A, B)$ then*
$$
V(A \cap B) \cap (V(\alpha(d)) - (S \cup V(\alpha(-d)))) \ne \emptyset.
$$" -/
theorem theorem_11_4_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    (sys : π.SystemOfStandardLinkages)
    {A B : Hypergraph α β} (hsep : G.IsSeparation A B)
    {d : Set π.S} (hd : d ∈ π.crossingCells A B) :
    ((A ∩ B).vertexSet ∩ ((π.cellGraph d).vertexSet \ (sys.S ∪ π.otherVertices d))).Nonempty := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have : ConnectedSpace π.S := π.connected
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof
      h𝒯 π htrue hred hwarp hθ
  rcases hd with ⟨⟨hdC, hd_max⟩, hnotA, hnotB⟩
  rw [Set.not_subset] at hnotA hnotB
  rcases hnotA with ⟨u₁, ⟨n₁, ⟨hn₁_t, hn₁_dom⟩, rfl⟩, hu₁_notA⟩
  rcases hnotB with ⟨u₂, ⟨n₂, ⟨hn₂_t, hn₂_dom⟩, rfl⟩, hu₂_notB⟩
  have hu₂_G : π.nodeVertex n₂ ∈ G.vertexSet := π.nodeVertex_mem n₂ hn₂_dom
  rw [← hsep.vertexSet_union] at hu₂_G
  have hu₂_A : π.nodeVertex n₂ ∈ A.vertexSet := hu₂_G.resolve_right hu₂_notB
  have hne₁₂ : n₁ ≠ n₂ := by
    rintro rfl
    exact hu₁_notA hu₂_A
  by_cases hbd : (d ∩ bd π.S).Nonempty
  · -- Border cell case: use the node path `L₀` from the standard linkage in `α(d)`.
    rcases hbd with ⟨x₀, hxd, hxbd⟩
    let Θ := connectedComponentIn (bd π.S) x₀
    have hΘ : Θ ∈ cuffs π.S := ⟨x₀, hxbd, rfl⟩
    have hdΘ : (d ∩ Θ).Nonempty := ⟨x₀, hxd, mem_connectedComponentIn hxbd⟩
    have hd_range : d ∈ Set.range (sys.E Θ hΘ).cell := by
      rw [(sys.E Θ hΘ).range_cell]; exact ⟨hdC, hdΘ⟩
    rcases hd_range with ⟨i, rfl⟩
    have hk_pos : 0 < (π.Γ.N ∩ Θ).ncard := by have := (sys.E Θ hΘ).two_le; omega
    have hstd := (sys.SL Θ hΘ).isStandard i
    rcases hstd.2.2 with ⟨L₀, hL₀_disj⟩ | ⟨c', hc'C, hint', _, hsub'⟩
    · have htilde_i : tilde ((sys.E Θ hΘ).cell i) =
          {(sys.E Θ hΘ).node i, (sys.E Θ hΘ).node (cyclicSucc hk_pos i)} :=
        (sys.E Θ hΘ).cell_tilde i
      have hn₁_pair : n₁ = (sys.E Θ hΘ).node i ∨ n₁ = (sys.E Θ hΘ).node (cyclicSucc hk_pos i) := by
        have h : n₁ ∈ ({(sys.E Θ hΘ).node i, (sys.E Θ hΘ).node (cyclicSucc hk_pos i)} : Set π.S) :=
          htilde_i ▸ hn₁_t
        exact h
      have hn₂_pair : n₂ = (sys.E Θ hΘ).node i ∨ n₂ = (sys.E Θ hΘ).node (cyclicSucc hk_pos i) := by
        have h : n₂ ∈ ({(sys.E Θ hΘ).node i, (sys.E Θ hΘ).node (cyclicSucc hk_pos i)} : Set π.S) :=
          htilde_i ▸ hn₂_t
        exact h
      have hbd_props := sys.border_cell_properties h𝒯 π htrue hred hwarp hθ hΘ i
      have hbs_props := sys.borderSet_subset_cellSet h𝒯 π htrue hred hwarp hθ hΘ i
      have hL₀_first : L₀.first = π.nodeVertex ((sys.E Θ hΘ).node i) :=
        mem_singleton_iff.mp L₀.first_mem
      have hL₀_last : L₀.last = π.nodeVertex ((sys.E Θ hΘ).node (cyclicSucc hk_pos i)) :=
        mem_singleton_iff.mp L₀.last_mem
      have hL₀_internal : ∀ v ∈ L₀.walk.support,
          v ≠ π.nodeVertex ((sys.E Θ hΘ).node i) →
          v ≠ π.nodeVertex ((sys.E Θ hΘ).node (cyclicSucc hk_pos i)) →
          v ∈ (π.cellGraph ((sys.E Θ hΘ).cell i)).vertexSet \
            (sys.S ∪ π.otherVertices ((sys.E Θ hΘ).cell i)) := by
        intro v hv_sup hne_first hne_last
        rw [hbd_props.2.2.2]
        have hfirst_c : L₀.first ∈ (π.cellGraph ((sys.E Θ hΘ).cell i)).vertexSet := by
          rw [hL₀_first]
          have hndom_i : (sys.E Θ hΘ).node i ∈ π.domγ := by
            rw [hdom]; exact ((sys.E Θ hΘ).node_mem i).1
          exact π.p2 ((sys.E Θ hΘ).cell i) hdC ((sys.E Θ hΘ).node i)
            ⟨htilde_i ▸ mem_insert _ _, hndom_i⟩
        have hvc : v ∈ (π.cellGraph ((sys.E Θ hΘ).cell i)).vertexSet :=
          Portrayal.SystemOfStandardLinkages.walk_support_subset_vertexSet hfirst_c L₀.walk hv_sup
        have hnot_cellSet : v ∉ sys.cellSet Θ hΘ i := by
          rw [Portrayal.SystemOfStandardLinkages.cellSet, mem_iUnion]
          rintro ⟨j, hzj⟩
          exact Set.disjoint_left.mp (hL₀_disj j) hv_sup hzj
        refine ⟨hvc, fun hmem => ?_⟩
        rcases hmem with hcell | hvo
        · exact hnot_cellSet hcell
        · have hv_inter : v ∈ (π.cellGraph ((sys.E Θ hΘ).cell i)).vertexSet ∩
              π.otherVertices ((sys.E Θ hΘ).cell i) := ⟨hvc, hvo⟩
          rw [hbd_props.1] at hv_inter
          rcases hv_inter with (hv_bs₁ | hv_bs₂) | ⟨m, ⟨hm_t, _⟩, rfl⟩
          · exact hnot_cellSet (hbs_props.2.1 hv_bs₁)
          · exact hnot_cellSet (hbs_props.2.2 hv_bs₂)
          · rw [htilde_i] at hm_t
            rcases hm_t with rfl | rfl
            · exact hne_first rfl
            · exact hne_last rfl
      have hex_W : ∃ W : (π.cellGraph ((sys.E Θ hΘ).cell i)).skeleton.Walk
          (π.nodeVertex n₁) (π.nodeVertex n₂),
          ∀ v ∈ W.support, v ∈ L₀.walk.support := by
        rcases hn₁_pair with h1 | h1 <;> rcases hn₂_pair with h2 | h2
        · exact (hne₁₂ (h1.trans h2.symm)).elim
        · refine ⟨L₀.walk.copy (hL₀_first.trans (congrArg π.nodeVertex h1.symm))
            (hL₀_last.trans (congrArg π.nodeVertex h2.symm)), ?_⟩
          intro v hv
          rwa [SimpleGraph.Walk.support_copy] at hv
        · refine ⟨L₀.walk.reverse.copy (hL₀_last.trans (congrArg π.nodeVertex h1.symm))
            (hL₀_first.trans (congrArg π.nodeVertex h2.symm)), ?_⟩
          intro v hv
          rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
            List.mem_reverse] at hv
          exact hv
        · exact (hne₁₂ (h1.trans h2.symm)).elim
      obtain ⟨W, hW_sub⟩ := hex_W
      let WG : G.skeleton.Walk (π.nodeVertex n₁) (π.nodeVertex n₂) :=
        W.map (SimpleGraph.Hom.ofLE (skeleton_le_of_le (π.cellGraph_le _ hdC)))
      obtain ⟨v, hv_sup, hv_ne₁, hv_ne₂, hv_AB⟩ :=
        exists_internal_mem_inter_of_walk_of_isSeparation hsep WG hu₁_notA hu₂_A hu₂_notB
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hv_sup
      rcases hv_sup with ⟨v', hv'_W, rfl⟩
      change v' ≠ π.nodeVertex n₁ at hv_ne₁
      change v' ≠ π.nodeVertex n₂ at hv_ne₂
      change v' ∈ (A ∩ B).vertexSet at hv_AB
      have hv'_L₀ : v' ∈ L₀.walk.support := hW_sub v' hv'_W
      have hne_i : v' ≠ π.nodeVertex ((sys.E Θ hΘ).node i) := by
        rcases hn₁_pair with h1 | h1 <;> rcases hn₂_pair with h2 | h2
        · exact (hne₁₂ (h1.trans h2.symm)).elim
        · rwa [← h1]
        · rwa [← h2]
        · exact (hne₁₂ (h1.trans h2.symm)).elim
      have hne_succ : v' ≠ π.nodeVertex ((sys.E Θ hΘ).node (cyclicSucc hk_pos i)) := by
        rcases hn₁_pair with h1 | h1 <;> rcases hn₂_pair with h2 | h2
        · exact (hne₁₂ (h1.trans h2.symm)).elim
        · rwa [← h2]
        · rwa [← h1]
        · exact (hne₁₂ (h1.trans h2.symm)).elim
      exact ⟨v', hv_AB, hL₀_internal v' hv'_L₀ hne_i hne_succ⟩
    · exfalso
      have hc'_ne : c' ≠ (sys.E Θ hΘ).cell i := fun h => hint' (h ▸ ⟨x₀, hxd, hxbd⟩)
      exact hd_max ⟨c', hc'C, hc'_ne, hsub'⟩
  · -- Internal cell case: use (9.1) (`theorem_9_1_proof`).
    obtain ⟨L₀, hL₀_int⟩ :=
      theorem_9_1_proof h𝒯 π htrue hred hwarp hθ hdC hbd hn₁_t hn₂_t hne₁₂
    have hint_props := sys.internal_cell_properties h𝒯 π htrue hred hwarp hθ hdC hbd
    have hL₀_first : L₀.first = π.nodeVertex n₁ := mem_singleton_iff.mp L₀.first_mem
    have hL₀_last : L₀.last = π.nodeVertex n₂ := mem_singleton_iff.mp L₀.last_mem
    let W : (π.cellGraph d).skeleton.Walk (π.nodeVertex n₁) (π.nodeVertex n₂) :=
      L₀.walk.copy hL₀_first hL₀_last
    let WG : G.skeleton.Walk (π.nodeVertex n₁) (π.nodeVertex n₂) :=
      W.map (SimpleGraph.Hom.ofLE (skeleton_le_of_le (π.cellGraph_le d hdC)))
    obtain ⟨v, hv_sup, hv_ne₁, hv_ne₂, hv_AB⟩ :=
      exists_internal_mem_inter_of_walk_of_isSeparation hsep WG hu₁_notA hu₂_A hu₂_notB
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hv_sup
    rcases hv_sup with ⟨v', hv'_W, rfl⟩
    change v' ≠ π.nodeVertex n₁ at hv_ne₁
    change v' ≠ π.nodeVertex n₂ at hv_ne₂
    change v' ∈ (A ∩ B).vertexSet at hv_AB
    have hv'_L₀ : v' ∈ L₀.walk.support := by
      dsimp only [W] at hv'_W
      rwa [SimpleGraph.Walk.support_copy] at hv'_W
    have hfirst_c : L₀.first ∈ (π.cellGraph d).vertexSet := by
      rw [hL₀_first]
      exact π.p2 d hdC n₁ ⟨hn₁_t, hn₁_dom⟩
    have hv'_c : v' ∈ (π.cellGraph d).vertexSet :=
      Portrayal.SystemOfStandardLinkages.walk_support_subset_vertexSet
        hfirst_c L₀.walk hv'_L₀
    refine ⟨v', hv_AB, hv'_c, ?_⟩
    rintro (hv'_S | hv'_O)
    · exact Set.disjoint_left.mp hint_props.2 hv'_c hv'_S
    · have hv'_γ : v' ∈ π.gammaImage (tilde d) := hint_props.1 ▸ ⟨hv'_c, hv'_O⟩
      have hv'_img : v' ∈ π.nodeVertex '' tilde d := by
        rcases hv'_γ with ⟨m, ⟨hm_t, _⟩, rfl⟩
        exact ⟨m, hm_t, rfl⟩
      rcases hL₀_int v' hv'_L₀ hv'_img with hEq₁ | hEq₂
      · exact hv_ne₁ hEq₁
      · exact hv_ne₂ hEq₂

/-- **Graph Minors XVII, (11.5)** (page 194):
"For any separation $(A, B)$ of $G$,*
$$|D(A, B)| \le |V(A \cap B) - (S \cup \gamma(N(\Gamma)))|.$$" -/
theorem theorem_11_5_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    (sys : π.SystemOfStandardLinkages)
    {A B : Hypergraph α β} (hsep : G.IsSeparation A B) :
    (π.crossingCells A B).ncard ≤
      ((A ∩ B).vertexSet \ (sys.S ∪ π.gammaImage π.Γ.N)).ncard := by
  classical
  by_cases hD_ne : (π.crossingCells A B).Nonempty
  · obtain ⟨d₀, hd₀⟩ := hD_ne
    have hex : ∀ d : π.crossingCells A B,
        ∃ v : α, v ∈ (A ∩ B).vertexSet ∧
          v ∈ (π.cellGraph d.1).vertexSet \ (sys.S ∪ π.otherVertices d.1) :=
      fun d => theorem_11_4_proof h𝒯 π htrue hred hwarp hθ sys hsep d.2
    choose v_fn hv_spec using hex
    let f : Set π.S → α := fun d =>
      if hd : d ∈ π.crossingCells A B then v_fn ⟨d, hd⟩ else v_fn ⟨d₀, hd₀⟩
    have hf_maps : f '' π.crossingCells A B ⊆
        (A ∩ B).vertexSet \ (sys.S ∪ π.gammaImage π.Γ.N) := by
      rintro _ ⟨d, hd, rfl⟩
      dsimp only [f]
      rw [dite_eq_left hd]
      obtain ⟨hv_AB, hvc, hv_not⟩ := hv_spec ⟨d, hd⟩
      refine ⟨hv_AB, fun hmem => hv_not ?_⟩
      rcases hmem with hv_S | hv_γN
      · exact Or.inl hv_S
      · exact Or.inr (π.gammaImage_N_subset_otherVertices h𝒯 htrue hred hwarp hθ d hv_γN)
    have hf_inj : InjOn f (π.crossingCells A B) := by
      intro d₁ hd₁ d₂ hd₂ hEq
      dsimp only [f] at hEq
      rw [dite_eq_left hd₁, dite_eq_left hd₂] at hEq
      by_contra hne
      obtain ⟨_, _, hv₁_not⟩ := hv_spec ⟨d₁, hd₁⟩
      obtain ⟨_, hvc₂, _⟩ := hv_spec ⟨d₂, hd₂⟩
      exact hv₁_not (Or.inr ⟨d₂, hd₂.1.1, Ne.symm hne, hEq ▸ hvc₂⟩)
    have hfin_target : ((A ∩ B).vertexSet \ (sys.S ∪ π.gammaImage π.Γ.N)).Finite :=
      (G.vertexSet_finite.subset (inter_subset_left.trans hsep.left_le.vertexSet_subset)).subset
        sdiff_subset
    rw [← hf_inj.ncard_image]
    exact ncard_le_ncard hf_maps hfin_target
  · rw [not_nonempty_iff_eq_empty.mp hD_ne, ncard_empty]
    exact Nat.zero_le _

/-! ## 5. Bounding and Determining $|V(A \cap B)|$: (11.6) and (11.7) (Pages 194–196) -/

/-- Every vertex in the support of `(sys.SL Θ hΘ).circWalk i₀ u k` belongs to `sys.S`. -/
theorem Portrayal.SystemOfStandardLinkages.support_circWalk_subset_S
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    (sys : π.SystemOfStandardLinkages)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (i₀ : Fin (π.Γ.N ∩ Θ).ncard)
    {u : α} (hu : u ∈ π.borderSet ((sys.E Θ hΘ).node i₀))
    {z : α} (hz : z ∈ ((sys.SL Θ hΘ).circWalk i₀ u (π.Γ.N ∩ Θ).ncard).support) :
    z ∈ sys.S := by
  obtain ⟨hcard, hbs₁_sub, _⟩ :=
    sys.borderSet_subset_cellSet h𝒯 π htrue hred hwarp hθ hΘ i₀
  rw [← ((sys.SL Θ hΘ).circWalk i₀ u (π.Γ.N ∩ Θ).ncard).cons_tail_support, List.mem_cons] at hz
  rcases hz with rfl | hz_tail
  · exact sys.cellSet_subset_S hΘ i₀ (hbs₁_sub hu)
  · rw [CuffStandardLinkages.mem_support_tail_circWalk_iff] at hz_tail
    rcases hz_tail with ⟨r, _, hzr⟩
    set idx := stepIdx (sys.E Θ hΘ).two_le i₀ r
    have hcur_bs : (sys.SL Θ hΘ).traceVertex i₀ u r ∈ π.borderSet ((sys.E Θ hΘ).node idx) :=
      (sys.SL Θ hΘ).traceVertex_mem_borderSet hcard i₀ hu r
    obtain ⟨j, _, _, _, hwalk_sup, _, _⟩ := (sys.SL Θ hΘ).step_spec_of_mem hcard idx hcur_bs
    have hz_j : z ∈ (((sys.SL Θ hΘ).L idx j).walk).support :=
      hwalk_sup ▸ List.mem_of_mem_tail hzr
    exact sys.cellSet_subset_S hΘ idx (mem_iUnion.mpr ⟨j, hz_j⟩)

/-- For every cell $c_0 \in C(\Gamma)$, $|V(\alpha(c_0) \cap \alpha(-c_0))| \le 2p + 2$. -/
theorem Portrayal.SystemOfStandardLinkages.ncard_inter_otherVertices_le
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    (sys : π.SystemOfStandardLinkages)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C) :
    ((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀).ncard ≤ 2 * p + 2 := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have hp_pos : 1 ≤ p := π.one_le_warp.trans hwarp
  have hγ_le : (π.gammaImage (tilde c₀)).ncard ≤ (tilde c₀).ncard := by
    have hsub : π.gammaImage (tilde c₀) ⊆ π.nodeVertex '' tilde c₀ := by
      rintro _ ⟨n, ⟨hnt, _⟩, rfl⟩
      exact ⟨n, hnt, rfl⟩
    exact (ncard_le_ncard hsub ((π.Γ.finite_tilde_cell hc₀).image π.nodeVertex)).trans
      (ncard_image_le (π.Γ.finite_tilde_cell hc₀))
  by_cases hbd : (c₀ ∩ bd π.S).Nonempty
  · rcases hbd with ⟨x₀, hxc₀, hxbd⟩
    let Θ := connectedComponentIn (bd π.S) x₀
    have hΘ : Θ ∈ cuffs π.S := ⟨x₀, hxbd, rfl⟩
    have hc₀Θ : (c₀ ∩ Θ).Nonempty := ⟨x₀, hxc₀, mem_connectedComponentIn hxbd⟩
    have hc₀_range : c₀ ∈ Set.range (sys.E Θ hΘ).cell := by
      rw [(sys.E Θ hΘ).range_cell]; exact ⟨hc₀, hc₀Θ⟩
    rcases hc₀_range with ⟨i₀, hi₀_eq⟩
    have hk_pos : 0 < (π.Γ.N ∩ Θ).ncard := by have := (sys.E Θ hΘ).two_le; omega
    have hbd_props := sys.border_cell_properties h𝒯 π htrue hred hwarp hθ hΘ i₀
    obtain ⟨hcard, _, _⟩ :=
      sys.borderSet_subset_cellSet h𝒯 π htrue hred hwarp hθ hΘ i₀
    have hq_le_p : π.warpAt Θ ≤ p := (π.warpAt_le_warp hΘ).trans hwarp
    have hbs₁_le : (π.borderSet ((sys.E Θ hΘ).node i₀)).ncard ≤ p :=
      (hcard i₀).trans_le hq_le_p
    have hbs₂_le : (π.borderSet ((sys.E Θ hΘ).node (cyclicSucc hk_pos i₀))).ncard ≤ p :=
      (hcard (cyclicSucc hk_pos i₀)).trans_le hq_le_p
    have htc₀_le2 : (tilde ((sys.E Θ hΘ).cell i₀)).ncard ≤ 2 := by
      rw [(sys.E Θ hΘ).cell_tilde i₀]
      exact (ncard_insert_le _ _).trans (by rw [ncard_singleton])
    have hγ_le2 : (π.gammaImage (tilde ((sys.E Θ hΘ).cell i₀))).ncard ≤ 2 := by
      rw [hi₀_eq]; exact hγ_le.trans (hi₀_eq ▸ htc₀_le2)
    rw [← hi₀_eq, hbd_props.1]
    have h1 := ncard_union_le
      (π.borderSet ((sys.E Θ hΘ).node i₀) ∪
        π.borderSet ((sys.E Θ hΘ).node (cyclicSucc hk_pos i₀)))
      (π.gammaImage (tilde ((sys.E Θ hΘ).cell i₀)))
    have h2 := ncard_union_le
      (π.borderSet ((sys.E Θ hΘ).node i₀))
      (π.borderSet ((sys.E Θ hΘ).node (cyclicSucc hk_pos i₀)))
    omega
  · have hint_props := sys.internal_cell_properties h𝒯 π htrue hred hwarp hθ hc₀ hbd
    rw [hint_props.1]
    have htc₀_le3 : (tilde c₀).ncard ≤ 3 := π.Γ.ncard_tilde_cell_le hc₀
    omega

private theorem circumnavigation_walk_crosses_separation
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {θ : ℕ}
    {p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    (sys : π.SystemOfStandardLinkages)
    {A : Hypergraph α β}
    {B : Hypergraph α β}
    (hAB : (A, B) ∈ 𝒯)
    (hsep : G.IsSeparation A B)
    (Θ : Set π.S)
    (hΘ : Θ ∈ cuffs π.S)
    (i₀ : Fin (π.Γ.N ∩ Θ).ncard)
    (hcard : ∀ (r : Fin (π.Γ.N ∩ Θ).ncard), (π.borderSet ((sys.E Θ hΘ).node r)).ncard = π.warpAt
      Θ)
    (hbs₁_sub_A : π.borderSet ((sys.E Θ hΘ).node i₀) ⊆ A.vertexSet)
    (hord_le : A.separationOrder B ≤ 2 * p + 3) :
    ∀ (u : ↑(π.borderSet ((sys.E Θ hΘ).node i₀))), ∃ (L₁ L₂ : List α) (m a b : α),
      ((sys.SL Θ hΘ).circWalk i₀ (↑u)
      (π.Γ.N ∩ Θ).ncard).support.tail = L₁ ++ m :: L₂ ∧ (∀ x ∈ L₁, x ∈ A.vertexSet) ∧ m ∉
      A.vertexSet ∧ a ∈ (A ∩ B).vertexSet ∧ (L₁ = [] ∧ a = ↑u ∨ a ∈ L₁) ∧ b ∈ (A ∩ B).vertexSet
        ∧ b ∈ L₂ ∧ (sys.SL Θ
      hΘ).traceVertex i₀ (↑u) (π.Γ.N ∩ Θ).ncard ∈ L₂ := by
  let n₁ := (sys.E Θ hΘ).node i₀
  intro u
  have hu_A : u.1 ∈ A.vertexSet := hbs₁_sub_A u.2
  have hv_bs₁ : (sys.SL Θ hΘ).traceVertex i₀ u.1 (π.Γ.N ∩ Θ).ncard ∈ π.borderSet n₁ := by
    have hmem := (sys.SL Θ hΘ).traceVertex_mem_borderSet hcard i₀ u.2 (π.Γ.N ∩ Θ).ncard
    rwa [stepIdx_self] at hmem
  have hv_A : (sys.SL Θ hΘ).traceVertex i₀ u.1 (π.Γ.N ∩ Θ).ncard ∈ A.vertexSet :=
    hbs₁_sub_A hv_bs₁
  have hnot_sub : ¬ ((sys.SL Θ hΘ).circumnavigationVertices i₀ u.1 ⊆ A.vertexSet) :=
    theorem_10_2_proof (sys.SL Θ hΘ) h𝒯 htrue.1 hwarp hred le_rfl (by omega) rfl hcard i₀ u.2
      hAB hord_le
  rw [← (sys.SL Θ hΘ).support_circWalk_eq_circumnavigationVertices i₀ u.1,
    Set.not_subset] at hnot_sub
  rcases hnot_sub with ⟨z, hz_sup, hz_notA⟩
  change z ∈ ((sys.SL Θ hΘ).circWalk i₀ u.1 (π.Γ.N ∩ Θ).ncard).support at hz_sup
  rw [← ((sys.SL Θ hΘ).circWalk i₀ u.1 (π.Γ.N ∩ Θ).ncard).cons_tail_support,
    List.mem_cons] at hz_sup
  have hz_tail : z ∈ ((sys.SL Θ hΘ).circWalk i₀ u.1 (π.Γ.N ∩ Θ).ncard).support.tail :=
    hz_sup.resolve_left fun hEq => hz_notA (hEq ▸ hu_A)
  exact walk_first_last_out_of_isSeparation hsep
    ((sys.SL Θ hΘ).circWalk i₀ u.1 (π.Γ.N ∩ Θ).ncard) hu_A hv_A ⟨z, hz_tail, hz_notA⟩

private theorem empty_prefix_starts_on_both_borders
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    (sys : π.SystemOfStandardLinkages)
    {c₀ : Set π.S}
    {A : Hypergraph α β}
    (hc₀A : π.cellGraph c₀ ≤ A)
    (X : Set α)
    (Θ : Set π.S)
    (hΘ : Θ ∈ cuffs π.S)
    (i₀ : Fin (π.Γ.N ∩ Θ).ncard)
    (hi₀_eq : (sys.E Θ hΘ).cell i₀ = c₀)
    (hcard : ∀ (r : Fin (π.Γ.N ∩ Θ).ncard), (π.borderSet ((sys.E Θ hΘ).node r)).ncard = π.warpAt
      Θ)
    (L₁_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → List α)
    (L₂_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → List α)
    (m_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → α)
    (a_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → α)
    (b_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → α)
    (hwalk_spec : ∀ (u : ↑(π.borderSet ((sys.E Θ hΘ).node i₀))), ((sys.SL Θ hΘ).circWalk i₀ (↑u)
      (π.Γ.N ∩
      Θ).ncard).support.tail = L₁_fn u ++ m_fn u :: L₂_fn u ∧ (∀ x ∈ L₁_fn u, x ∈ A.vertexSet) ∧
      m_fn u ∉ A.vertexSet ∧ a_fn u ∈ X ∧ (L₁_fn u = [] ∧ a_fn u = ↑u ∨ a_fn u ∈ L₁_fn u) ∧ b_fn u
      ∈ X ∧ b_fn u ∈ L₂_fn u ∧ (sys.SL Θ hΘ).traceVertex i₀ (↑u) (π.Γ.N ∩ Θ).ncard ∈ L₂_fn u) :
    ∀ (u : ↑(π.borderSet ((sys.E Θ hΘ).node i₀))), L₁_fn u = [] → a_fn u = ↑u ∧ ↑u ∈ π.borderSet
      ((sys.E Θ hΘ).node i₀) ∩ π.borderSet ((sys.E Θ hΘ).node (cyclicSucc (Nat.zero_lt_of_lt
        (sys.E Θ hΘ).two_le) i₀)) := by
  let n₁ := (sys.E Θ hΘ).node i₀
  intro u hnil
  obtain ⟨hEq, _, hm_notA, _, ha_cases, _, _, _⟩ := hwalk_spec u
  have ha_eq : a_fn u = u.1 := by
    rcases ha_cases with ⟨_, hEq_u⟩ | ha_L₁
    · exact hEq_u
    · rw [hnil] at ha_L₁; exact (List.not_mem_nil ha_L₁).elim
  refine ⟨ha_eq, u.2, ?_⟩
  obtain ⟨rest, hrest⟩ := sys.exists_support_tail_circWalk_eq_append hΘ i₀ u.1
  rw [hnil, List.nil_append] at hEq
  have hstep_nil : ((sys.SL Θ hΘ).stepWalk i₀ u.1).support.tail = [] := by
    rcases hstep_eq : ((sys.SL Θ hΘ).stepWalk i₀ u.1).support.tail with _ | ⟨hd, tl⟩
    · rfl
    · exfalso
      rw [hstep_eq, List.cons_append] at hrest
      have hhd_eq : hd = m_fn u := List.cons.inj (hrest.symm.trans hEq) |>.1
      have hhd_tail : hd ∈ ((sys.SL Θ hΘ).stepWalk i₀ u.1).support.tail :=
        hstep_eq ▸ List.mem_cons_self
      have hhd_c₀ : hd ∈ (π.cellGraph c₀).vertexSet := by
        rw [← hi₀_eq]
        exact (sys.SL Θ hΘ).mem_support_tail_subset_cellGraph hcard i₀ u.2 hhd_tail
      exact hm_notA (hhd_eq ▸ hc₀A.vertexSet_subset hhd_c₀)
  have hu_eq_step : u.1 = (sys.SL Θ hΘ).stepVertex i₀ u.1 :=
    start_eq_end_of_support_tail_eq_nil _ hstep_nil
  rw [hu_eq_step]
  exact ((sys.SL Θ hΘ).step_spec_of_mem hcard i₀ u.2).choose_spec.2.2.2.2.2

private theorem nonempty_prefix_has_distinct_interior_start
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    (sys : π.SystemOfStandardLinkages)
    {A : Hypergraph α β}
    (X : Set α)
    (Θ : Set π.S)
    (hΘ : Θ ∈ cuffs π.S)
    (i₀ : Fin (π.Γ.N ∩ Θ).ncard)
    (hcard : ∀ (r : Fin (π.Γ.N ∩ Θ).ncard), (π.borderSet ((sys.E Θ hΘ).node r)).ncard = π.warpAt
      Θ)
    (hne_nil : ∀ w ∈ π.borderSet ((sys.E Θ hΘ).node i₀), ((sys.SL Θ hΘ).circWalk i₀ w
      (π.Γ.N ∩ Θ).ncard).support.tail
      ≠ [])
    (L₁_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → List α)
    (L₂_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → List α)
    (m_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → α)
    (a_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → α)
    (b_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → α)
    (hwalk_spec : ∀ (u : ↑(π.borderSet ((sys.E Θ hΘ).node i₀))), ((sys.SL Θ hΘ).circWalk i₀ (↑u)
      (π.Γ.N ∩
      Θ).ncard).support.tail = L₁_fn u ++ m_fn u :: L₂_fn u ∧ (∀ x ∈ L₁_fn u, x ∈ A.vertexSet) ∧
      m_fn u ∉ A.vertexSet ∧ a_fn u ∈ X ∧ (L₁_fn u = [] ∧ a_fn u = ↑u ∨ a_fn u ∈ L₁_fn u) ∧ b_fn u
      ∈ X ∧ b_fn u ∈ L₂_fn u ∧ (sys.SL Θ hΘ).traceVertex i₀ (↑u) (π.Γ.N ∩ Θ).ncard ∈ L₂_fn u) :
    ∀ (u : ↑(π.borderSet ((sys.E Θ hΘ).node i₀))), L₁_fn u ≠ [] → a_fn u ∈
      ((sys.SL Θ hΘ).circWalk i₀ (↑u) (π.Γ.N ∩
      Θ).ncard).support.tail ∧ a_fn u ≠ b_fn u ∧ a_fn u ∉ π.borderSet ((sys.E Θ hΘ).node i₀) := by
  let n₁ := (sys.E Θ hΘ).node i₀
  intro u hne
  obtain ⟨hEq, _, _, _, ha_cases, _, hb_L₂, hv_L₂⟩ := hwalk_spec u
  have ha_L₁ : a_fn u ∈ L₁_fn u :=
    ha_cases.resolve_left fun h => hne h.1
  have hnodup : (L₁_fn u ++ m_fn u :: L₂_fn u).Nodup :=
    hEq ▸ (sys.SL Θ hΘ).nodup_support_tail_circWalk hcard i₀ u.2 le_rfl
  have hdisj_L₁_L₂ : List.Disjoint (L₁_fn u) (m_fn u :: L₂_fn u) :=
    fun x hx₁ hx₂ => (List.nodup_append.mp hnodup).2.2 x hx₁ x hx₂ rfl
  have ha_tail : a_fn u ∈ ((sys.SL Θ hΘ).circWalk i₀ u.1 (π.Γ.N ∩ Θ).ncard).support.tail :=
    hEq ▸ List.mem_append_left _ ha_L₁
  have ha_ne_b : a_fn u ≠ b_fn u := fun hEq_ab =>
    hdisj_L₁_L₂ ha_L₁ (hEq_ab ▸ List.mem_cons_of_mem _ hb_L₂)
  have ha_ne_v : a_fn u ≠ (sys.SL Θ hΘ).traceVertex i₀ u.1 (π.Γ.N ∩ Θ).ncard := fun hEq_av
    =>
    hdisj_L₁_L₂ ha_L₁ (hEq_av ▸ List.mem_cons_of_mem _ hv_L₂)
  have ha_not_bs₁ : a_fn u ∉ π.borderSet n₁ := by
    intro ha_bs₁
    have hEq_av := ((sys.SL Θ hΘ).mem_support_tail_circWalk_inter_borderSet_iff
      hcard i₀ hne_nil u.2 ha_bs₁).mp ha_tail
    exact ha_ne_v hEq_av
  exact ⟨ha_tail, ha_ne_b, ha_not_bs₁⟩

private theorem circumnavigation_prefix_map_injective
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    (sys : π.SystemOfStandardLinkages)
    (Θ : Set π.S)
    (hΘ : Θ ∈ cuffs π.S)
    (i₀ : Fin (π.Γ.N ∩ Θ).ncard)
    (n₂ : π.S)
    (hcard : ∀ (r : Fin (π.Γ.N ∩ Θ).ncard), (π.borderSet ((sys.E Θ hΘ).node r)).ncard = π.warpAt
      Θ)
    (L₁_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → List α)
    (a_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → α)
    (b_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → α)
    (a_map : α → α)
    (hmap_a : ∀ u (hu : u ∈ π.borderSet ((sys.E Θ hΘ).node i₀)),
      a_map u = a_fn ⟨u, hu⟩)
    (ha_nil_case : ∀ (u : ↑(π.borderSet ((sys.E Θ hΘ).node i₀))), L₁_fn u = [] → a_fn u = ↑u
      ∧ ↑u ∈ π.borderSet ((sys.E Θ hΘ).node i₀) ∩
      π.borderSet n₂)
    (ha_nonnil_case : ∀ (u : ↑(π.borderSet ((sys.E Θ hΘ).node i₀))), L₁_fn u ≠ [] → a_fn u ∈
      ((sys.SL Θ hΘ).circWalk
      i₀ (↑u) (π.Γ.N ∩ Θ).ncard).support.tail ∧ a_fn u ≠ b_fn u ∧ a_fn u ∉ π.borderSet
        ((sys.E Θ hΘ).node i₀)) :
    InjOn a_map (π.borderSet ((sys.E Θ hΘ).node i₀)) := by
  let n₁ := (sys.E Θ hΘ).node i₀
  intro u₁ hu₁ u₂ hu₂ hEq
  rw [hmap_a u₁ hu₁, hmap_a u₂ hu₂] at hEq
  by_contra hne
  by_cases h1 : L₁_fn ⟨u₁, hu₁⟩ = [] <;> by_cases h2 : L₁_fn ⟨u₂, hu₂⟩ = []
  · have h1_eq := (ha_nil_case ⟨u₁, hu₁⟩ h1).1
    have h2_eq := (ha_nil_case ⟨u₂, hu₂⟩ h2).1
    exact hne (h1_eq.symm.trans (hEq.trans h2_eq))
  · have h1_eq := (ha_nil_case ⟨u₁, hu₁⟩ h1).1
    have h2_not := (ha_nonnil_case ⟨u₂, hu₂⟩ h2).2.2
    exact h2_not (hEq ▸ h1_eq ▸ hu₁)
  · have h1_not := (ha_nonnil_case ⟨u₁, hu₁⟩ h1).2.2
    have h2_eq := (ha_nil_case ⟨u₂, hu₂⟩ h2).1
    exact h1_not (hEq.symm ▸ h2_eq ▸ hu₂)
  · have h1_tail := (ha_nonnil_case ⟨u₁, hu₁⟩ h1).1
    have h2_tail := (ha_nonnil_case ⟨u₂, hu₂⟩ h2).1
    exact (sys.SL Θ hΘ).disjoint_support_tail_circWalk hcard i₀ hu₁ hu₂ hne
      h1_tail (hEq ▸ h2_tail)

private theorem circumnavigation_image_intersection_on_both_borders
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    (sys : π.SystemOfStandardLinkages)
    (Θ : Set π.S)
    (hΘ : Θ ∈ cuffs π.S)
    (i₀ : Fin (π.Γ.N ∩ Θ).ncard)
    (n₂ : π.S)
    (hcard : ∀ (r : Fin (π.Γ.N ∩ Θ).ncard), (π.borderSet ((sys.E Θ hΘ).node r)).ncard = π.warpAt
      Θ)
    (L₁_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → List α)
    (a_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → α)
    (b_fn : ↑(π.borderSet ((sys.E Θ hΘ).node i₀)) → α)
    (a_map : α → α)
    (hmap_a : ∀ u (hu : u ∈ π.borderSet ((sys.E Θ hΘ).node i₀)),
      a_map u = a_fn ⟨u, hu⟩)
    (b_map : α → α)
    (hmap_b : ∀ u (hu : u ∈ π.borderSet ((sys.E Θ hΘ).node i₀)),
      b_map u = b_fn ⟨u, hu⟩)
    (hb_in_tail : ∀ (u : ↑(π.borderSet ((sys.E Θ hΘ).node i₀))), b_fn u ∈
      ((sys.SL Θ hΘ).circWalk i₀ (↑u) (π.Γ.N ∩
      Θ).ncard).support.tail)
    (ha_nil_case : ∀ (u : ↑(π.borderSet ((sys.E Θ hΘ).node i₀))), L₁_fn u = [] → a_fn u = ↑u
      ∧ ↑u ∈ π.borderSet ((sys.E Θ hΘ).node i₀) ∩
      π.borderSet n₂)
    (ha_nonnil_case : ∀ (u : ↑(π.borderSet ((sys.E Θ hΘ).node i₀))), L₁_fn u ≠ [] → a_fn u ∈
      ((sys.SL Θ hΘ).circWalk
      i₀ (↑u) (π.Γ.N ∩ Θ).ncard).support.tail ∧ a_fn u ≠ b_fn u ∧ a_fn u ∉ π.borderSet
        ((sys.E Θ hΘ).node i₀)) :
    a_map '' π.borderSet ((sys.E Θ hΘ).node i₀) ∩ b_map '' π.borderSet
      ((sys.E Θ hΘ).node i₀) ⊆ π.borderSet ((sys.E Θ hΘ).node i₀) ∩ π.borderSet n₂ := by
  let n₁ := (sys.E Θ hΘ).node i₀
  rintro z ⟨⟨u₁, hu₁, rfl⟩, ⟨u₂, hu₂, hEq⟩⟩
  have hEq' : a_fn ⟨u₁, hu₁⟩ = b_fn ⟨u₂, hu₂⟩ := by
    rw [hmap_a u₁ hu₁, hmap_b u₂ hu₂] at hEq
    exact hEq.symm
  by_cases h1 : L₁_fn ⟨u₁, hu₁⟩ = []
  · obtain ⟨ha_eq, hu₁_mem⟩ := ha_nil_case ⟨u₁, hu₁⟩ h1
    rw [hmap_a u₁ hu₁, ha_eq]
    exact hu₁_mem
  · exfalso
    obtain ⟨ha₁_tail, ha₁_ne_b₁, _⟩ := ha_nonnil_case ⟨u₁, hu₁⟩ h1
    have hb₂_tail := hb_in_tail ⟨u₂, hu₂⟩
    by_cases hu_eq : u₁ = u₂
    · subst hu_eq
      exact ha₁_ne_b₁ hEq'
    · exact (sys.SL Θ hΘ).disjoint_support_tail_circWalk hcard i₀ hu₁ hu₂ hu_eq
        ha₁_tail (hEq' ▸ hb₂_tail)

/-- **Graph Minors XVII, (11.6)** (page 194):
"$|V(A \cap B) - S| \le |\tilde{c}_0|$, and if equality holds then*
$$|V(A \cap B) \cap S| = |V(\alpha(c_0) \cap \alpha(-c_0)) \cap S|.$$" -/
theorem theorem_11_6_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    (sys : π.SystemOfStandardLinkages)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯)
    (hc₀A : π.cellGraph c₀ ≤ A)
    (hle : separationOrder A B ≤ ((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀).ncard) :
    ((A ∩ B).vertexSet \ sys.S).ncard ≤ (tilde c₀).ncard ∧
      (((A ∩ B).vertexSet \ sys.S).ncard = (tilde c₀).ncard →
        ((A ∩ B).vertexSet ∩ sys.S).ncard =
          (((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀) ∩ sys.S).ncard) := by
  classical
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have : ConnectedSpace π.S := π.connected
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof h𝒯 π htrue hred hwarp hθ
  have hsep : G.IsSeparation A B := h𝒯.isSeparation hAB
  set X := (A ∩ B).vertexSet
  set Y := (π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀
  have hX_fin : X.Finite := (A ∩ B).vertexSet_finite
  have hY_fin : Y.Finite := (π.cellGraph c₀).vertexSet_finite.subset inter_subset_left
  have hX_split : (X ∩ sys.S).ncard + (X \ sys.S).ncard = X.ncard :=
    ncard_inter_add_ncard_sdiff_eq_ncard X sys.S hX_fin
  have hY_split : (Y ∩ sys.S).ncard + (Y \ sys.S).ncard = Y.ncard :=
    ncard_inter_add_ncard_sdiff_eq_ncard Y sys.S hY_fin
  have hγ_card : (π.gammaImage (tilde c₀)).ncard = (tilde c₀).ncard := by
    have hsub_dom : tilde c₀ ⊆ π.domγ := hdom ▸ π.Γ.tilde_subset_N hc₀
    have himg : π.gammaImage (tilde c₀) = π.nodeVertex '' tilde c₀ := by
      ext v
      simp only [Portrayal.gammaImage, mem_image]
      exact ⟨fun ⟨n, ⟨hnt, _⟩, hEq⟩ => ⟨n, hnt, hEq⟩,
        fun ⟨n, hnt, hEq⟩ => ⟨n, ⟨hnt, hsub_dom hnt⟩, hEq⟩⟩
    rw [himg, (π.nodeVertex_injOn.mono hsub_dom).ncard_image]
  have hY_diff_card : (Y \ sys.S).ncard = (tilde c₀).ncard := by
    by_cases hbd : (c₀ ∩ bd π.S).Nonempty
    · rcases hbd with ⟨x₀, hxc₀, hxbd⟩
      let Θ := connectedComponentIn (bd π.S) x₀
      have hΘ : Θ ∈ cuffs π.S := ⟨x₀, hxbd, rfl⟩
      have hc₀Θ : (c₀ ∩ Θ).Nonempty := ⟨x₀, hxc₀, mem_connectedComponentIn hxbd⟩
      have hc₀_range : c₀ ∈ Set.range (sys.E Θ hΘ).cell := by
        rw [(sys.E Θ hΘ).range_cell]; exact ⟨hc₀, hc₀Θ⟩
      rcases hc₀_range with ⟨i₀, hi₀_eq⟩
      have hbd_props := sys.border_cell_properties h𝒯 π htrue hred hwarp hθ hΘ i₀
      have hdiff_eq : Y \ sys.S = π.gammaImage (tilde c₀) := by
        dsimp only [Y]
        rw [← hi₀_eq]
        exact hbd_props.2.2.1
      rw [hdiff_eq, hγ_card]
    · have hint_props := sys.internal_cell_properties h𝒯 π htrue hred hwarp hθ hc₀ hbd
      have hdiff_eq : Y \ sys.S = π.gammaImage (tilde c₀) := by
        dsimp only [Y]
        rw [(hint_props.2.mono_left inter_subset_left).sdiff_eq_left, hint_props.1]
      rw [hdiff_eq, hγ_card]
  have hinter_le : (Y ∩ sys.S).ncard ≤ (X ∩ sys.S).ncard := by
    by_cases hbd : (c₀ ∩ bd π.S).Nonempty
    · rcases hbd with ⟨x₀, hxc₀, hxbd⟩
      let Θ := connectedComponentIn (bd π.S) x₀
      have hΘ : Θ ∈ cuffs π.S := ⟨x₀, hxbd, rfl⟩
      have hc₀Θ : (c₀ ∩ Θ).Nonempty := ⟨x₀, hxc₀, mem_connectedComponentIn hxbd⟩
      have hc₀_range : c₀ ∈ Set.range (sys.E Θ hΘ).cell := by
        rw [(sys.E Θ hΘ).range_cell]; exact ⟨hc₀, hc₀Θ⟩
      rcases hc₀_range with ⟨i₀, hi₀_eq⟩
      have hk_pos : 0 < (π.Γ.N ∩ Θ).ncard := by have := (sys.E Θ hΘ).two_le; omega
      let n₁ := (sys.E Θ hΘ).node i₀
      let n₂ := (sys.E Θ hΘ).node (cyclicSucc hk_pos i₀)
      have hbd_props := sys.border_cell_properties h𝒯 π htrue hred hwarp hθ hΘ i₀
      obtain ⟨hcard, hbs₁_sub, _⟩ :=
        sys.borderSet_subset_cellSet h𝒯 π htrue hred hwarp hθ hΘ i₀
      have hY_inter : Y ∩ sys.S = π.borderSet n₁ ∪ π.borderSet n₂ := by
        dsimp only [Y]
        rw [← hi₀_eq]
        exact hbd_props.2.1
      have hΘ_bd : Θ ⊆ bd π.S := connectedComponentIn_subset (bd π.S) x₀
      have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S :=
        ⟨((sys.E Θ hΘ).node_mem i₀).1, hΘ_bd ((sys.E Θ hΘ).node_mem i₀).2⟩
      have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S :=
        ⟨((sys.E Θ hΘ).node_mem (cyclicSucc hk_pos i₀)).1,
          hΘ_bd ((sys.E Θ hΘ).node_mem (cyclicSucc hk_pos i₀)).2⟩
      have hbs₁_fin : (π.borderSet n₁).Finite := π.borderSet_finite hn₁_bd
      have hbs₂_fin : (π.borderSet n₂).Finite := π.borderSet_finite hn₂_bd
      have hc₀_bd : (c₀ ∩ bd π.S).Nonempty := ⟨x₀, hxc₀, hxbd⟩
      have htilde_i₀ : tilde c₀ = {n₁, n₂} := hi₀_eq ▸ (sys.E Θ hΘ).cell_tilde i₀
      have hn₁_t : n₁ ∈ tilde c₀ := htilde_i₀ ▸ mem_insert _ _
      have hbs₁_sub_A : π.borderSet n₁ ⊆ A.vertexSet :=
        (π.p3_subset c₀ hc₀ hc₀_bd n₁ hn₁_t).trans hc₀A.vertexSet_subset
      have hp_pos : 1 ≤ p := π.one_le_warp.trans hwarp
      have hY_le : Y.ncard ≤ 2 * p + 2 :=
        sys.ncard_inter_otherVertices_le h𝒯 π htrue hred hwarp hθ hc₀
      have hord_le : separationOrder A B ≤ 2 * p + 3 := by
        change X.ncard ≤ Y.ncard at hle
        change X.ncard ≤ 2 * p + 3
        omega
      have hne_nil : ∀ w ∈ π.borderSet n₁,
          ((sys.SL Θ hΘ).circWalk i₀ w (π.Γ.N ∩ Θ).ncard).support.tail ≠ [] :=
        fun w hw => (sys.SL Θ hΘ).support_tail_circWalk_ne_nil
          h𝒯 htrue.1 hwarp hred (by omega) (by omega) hcard i₀ hw
      have hex_walk : ∀ u : π.borderSet n₁,
          ∃ (L₁ L₂ : List α) (m a b : α),
            ((sys.SL Θ hΘ).circWalk i₀ u.1 (π.Γ.N ∩ Θ).ncard).support.tail = L₁ ++ m :: L₂ ∧
            (∀ x ∈ L₁, x ∈ A.vertexSet) ∧
            m ∉ A.vertexSet ∧
            a ∈ X ∧ ((L₁ = [] ∧ a = u.1) ∨ a ∈ L₁) ∧
            b ∈ X ∧ b ∈ L₂ ∧ (sys.SL Θ hΘ).traceVertex i₀ u.1 (π.Γ.N ∩ Θ).ncard ∈ L₂ := by
        exact circumnavigation_walk_crosses_separation (α := α) (β := β) (G := G) (𝒯 := 𝒯) (θ :=
          θ) (p := p) h𝒯 π htrue hred hwarp hθ sys (A := A) (B := B) hAB hsep   Θ hΘ
          i₀  hcard hbs₁_sub_A hord_le
      choose L₁_fn L₂_fn m_fn a_fn b_fn hwalk_spec using hex_walk
      by_cases hbs₁_ne : (π.borderSet n₁).Nonempty
      · obtain ⟨u₀, hu₀⟩ := hbs₁_ne
        let a_map : α → α := fun u => if hu : u ∈ π.borderSet n₁ then a_fn ⟨u, hu⟩ else a_fn ⟨u₀,
          hu₀⟩
        let b_map : α → α := fun u => if hu : u ∈ π.borderSet n₁ then b_fn ⟨u, hu⟩ else b_fn ⟨u₀,
          hu₀⟩
        have ha_mem_XS : ∀ u ∈ π.borderSet n₁, a_map u ∈ X ∩ sys.S := by
          intro u hu
          dsimp only [a_map]
          rw [dite_eq_left hu]
          obtain ⟨hEq, _, _, ha_X, ha_cases, _, _, _⟩ := hwalk_spec ⟨u, hu⟩
          refine ⟨ha_X, ?_⟩
          apply sys.support_circWalk_subset_S h𝒯 π htrue hred hwarp hθ hΘ i₀ hu
          rw [← ((sys.SL Θ hΘ).circWalk i₀ u (π.Γ.N ∩ Θ).ncard).cons_tail_support, List.mem_cons]
          rcases ha_cases with ⟨_, hEq_u⟩ | ha_L₁
          · exact Or.inl hEq_u
          · exact Or.inr (hEq ▸ List.mem_append_left _ ha_L₁)
        have hb_mem_XS : ∀ u ∈ π.borderSet n₁, b_map u ∈ X ∩ sys.S := by
          intro u hu
          dsimp only [b_map]
          rw [dite_eq_left hu]
          obtain ⟨hEq, _, _, _, _, hb_X, hb_L₂, _⟩ := hwalk_spec ⟨u, hu⟩
          refine ⟨hb_X, ?_⟩
          apply sys.support_circWalk_subset_S h𝒯 π htrue hred hwarp hθ hΘ i₀ hu
          rw [← ((sys.SL Θ hΘ).circWalk i₀ u (π.Γ.N ∩ Θ).ncard).cons_tail_support, List.mem_cons]
          exact Or.inr (hEq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hb_L₂))
        have hb_in_tail : ∀ u : π.borderSet n₁,
            b_fn u ∈ ((sys.SL Θ hΘ).circWalk i₀ u.1 (π.Γ.N ∩ Θ).ncard).support.tail := by
          intro u
          obtain ⟨hEq, _, _, _, _, _, hb_L₂, _⟩ := hwalk_spec u
          exact hEq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hb_L₂)
        have ha_nil_case : ∀ u : π.borderSet n₁, L₁_fn u = [] →
            a_fn u = u.1 ∧ u.1 ∈ π.borderSet n₁ ∩ π.borderSet n₂ := by
          exact empty_prefix_starts_on_both_borders (α := α) (β := β) (G := G) π sys (c₀ := c₀) (A
            := A) hc₀A X Θ hΘ i₀ hi₀_eq   hcard L₁_fn L₂_fn m_fn a_fn b_fn hwalk_spec
        have ha_nonnil_case : ∀ u : π.borderSet n₁, L₁_fn u ≠ [] →
            a_fn u ∈ ((sys.SL Θ hΘ).circWalk i₀ u.1 (π.Γ.N ∩ Θ).ncard).support.tail ∧
            a_fn u ≠ b_fn u ∧
            a_fn u ∉ π.borderSet n₁ := by
          exact nonempty_prefix_has_distinct_interior_start (α := α) (β := β) (G := G) π sys (A :=
            A) X Θ hΘ i₀  hcard hne_nil L₁_fn L₂_fn m_fn a_fn b_fn hwalk_spec
        have ha_inj : InjOn a_map (π.borderSet n₁) := by
          exact circumnavigation_prefix_map_injective (α := α) (β := β) (G := G) π sys Θ hΘ i₀
            n₂ hcard L₁_fn a_fn b_fn   a_map (fun _ h => dite_eq_left h) ha_nil_case ha_nonnil_case
        have hb_inj : InjOn b_map (π.borderSet n₁) := by
          intro u₁ hu₁ u₂ hu₂ hEq
          dsimp only [b_map] at hEq
          rw [dite_eq_left hu₁, dite_eq_left hu₂] at hEq
          by_contra hne
          exact (sys.SL Θ hΘ).disjoint_support_tail_circWalk hcard i₀ hu₁ hu₂ hne
            (hb_in_tail ⟨u₁, hu₁⟩) (hEq ▸ hb_in_tail ⟨u₂, hu₂⟩)
        have hinter_ab_sub :
            (a_map '' π.borderSet n₁) ∩ (b_map '' π.borderSet n₁) ⊆
              π.borderSet n₁ ∩ π.borderSet n₂ := by
          exact circumnavigation_image_intersection_on_both_borders (α := α) (β := β) (G := G) π
            sys Θ hΘ i₀  n₂ hcard L₁_fn a_fn b_fn   a_map (fun _ h => dite_eq_left h) b_map
              (fun _ h => dite_eq_left h) hb_in_tail ha_nil_case
            ha_nonnil_case
        set A_set := a_map '' π.borderSet n₁
        set B_set := b_map '' π.borderSet n₁
        have hA_fin : A_set.Finite := hbs₁_fin.image a_map
        have hB_fin : B_set.Finite := hbs₁_fin.image b_map
        have hA_card : A_set.ncard = π.warpAt Θ := by
          rw [ha_inj.ncard_image, hcard i₀]
        have hB_card : B_set.ncard = π.warpAt Θ := by
          rw [hb_inj.ncard_image, hcard i₀]
        have hbs₁_card : (π.borderSet n₁).ncard = π.warpAt Θ := hcard i₀
        have hbs₂_card : (π.borderSet n₂).ncard = π.warpAt Θ := hcard (cyclicSucc hk_pos i₀)
        have hinter_card_le : (A_set ∩ B_set).ncard ≤ (π.borderSet n₁ ∩ π.borderSet n₂).ncard :=
          ncard_le_ncard hinter_ab_sub (hbs₁_fin.subset inter_subset_left)
        have hunion_bs :
            (π.borderSet n₁ ∪ π.borderSet n₂).ncard + (π.borderSet n₁ ∩ π.borderSet n₂).ncard =
              π.warpAt Θ + π.warpAt Θ := by
          rw [ncard_union_add_ncard_inter _ _ hbs₁_fin hbs₂_fin, hbs₁_card, hbs₂_card]
        have hunion_AB :
            (A_set ∪ B_set).ncard + (A_set ∩ B_set).ncard = π.warpAt Θ + π.warpAt Θ := by
          rw [ncard_union_add_ncard_inter _ _ hA_fin hB_fin]
          exact congrArg₂ (· + ·) hA_card hB_card
        have hbs_le_AB : (π.borderSet n₁ ∪ π.borderSet n₂).ncard ≤ (A_set ∪ B_set).ncard := by
          omega
        have hAB_sub_XS : A_set ∪ B_set ⊆ X ∩ sys.S := by
          rintro z (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
          · exact ha_mem_XS u hu
          · exact hb_mem_XS u hu
        rw [hY_inter]
        exact hbs_le_AB.trans (ncard_le_ncard hAB_sub_XS (hX_fin.subset inter_subset_left))
      · have hq0 : π.warpAt Θ = 0 := by
          have h1 := hcard i₀
          rw [not_nonempty_iff_eq_empty.mp hbs₁_ne, ncard_empty] at h1
          exact h1.symm
        have hbs₂_empty : π.borderSet n₂ = ∅ := by
          have hcard2 : (π.borderSet n₂).ncard = 0 := (hcard (cyclicSucc hk_pos i₀)).trans hq0
          exact (ncard_eq_zero hbs₂_fin).mp hcard2
        rw [hY_inter, not_nonempty_iff_eq_empty.mp hbs₁_ne, hbs₂_empty, empty_union, ncard_empty]
        exact Nat.zero_le _
    · have hint_props := sys.internal_cell_properties h𝒯 π htrue hred hwarp hθ hc₀ hbd
      have hY_inter_empty : Y ∩ sys.S = ∅ :=
        (hint_props.2.mono_left inter_subset_left).inter_eq
      rw [hY_inter_empty, ncard_empty]
      exact Nat.zero_le _
  change X.ncard ≤ Y.ncard at hle
  omega

private theorem distinct_nodes_for_dual_vertices
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {A : Hypergraph α β}
    {B : Hypergraph α β}
    (hdom : π.domγ = π.Γ.N)
    (hsep : G.IsSeparation A B)
    :
    ∀ (d : π.crossingCells A B), ∃ n ∈ tilde ↑d, π.nodeVertex n ∉ (A ∩ B).vertexSet ∧ (π.gammaImage
      (tilde ↑d) ⊆
      insert (π.nodeVertex n) A.vertexSet ∨ π.gammaImage (tilde ↑d) ⊆ insert (π.nodeVertex n)
      B.vertexSet) := by
  intro ⟨d, ⟨hd_star, hnotA, hnotB⟩⟩
  have hdC : d ∈ π.Γ.C := hd_star.1
  let TA := {n ∈ tilde d | π.nodeVertex n ∉ A.vertexSet}
  let TB := {n ∈ tilde d | π.nodeVertex n ∉ B.vertexSet}
  have htd_fin : (tilde d).Finite := π.Γ.finite_tilde_cell hdC
  have hTA_fin : TA.Finite := htd_fin.subset fun _ h => h.1
  have hTB_fin : TB.Finite := htd_fin.subset fun _ h => h.1
  have hTA_ne : TA.Nonempty := by
    rw [Set.not_subset] at hnotA
    rcases hnotA with ⟨_, ⟨n, ⟨hnt, _⟩, rfl⟩, hn_notA⟩
    exact ⟨n, hnt, hn_notA⟩
  have hTB_ne : TB.Nonempty := by
    rw [Set.not_subset] at hnotB
    rcases hnotB with ⟨_, ⟨n, ⟨hnt, _⟩, rfl⟩, hn_notB⟩
    exact ⟨n, hnt, hn_notB⟩
  have hdisj_TAB : Disjoint TA TB := by
    rw [Set.disjoint_left]
    intro n hnA hnB
    have hndom : n ∈ π.domγ := hdom ▸ π.Γ.tilde_subset_N hdC hnA.1
    have hnG : π.nodeVertex n ∈ G.vertexSet := π.nodeVertex_mem n hndom
    rw [← hsep.vertexSet_union] at hnG
    rcases hnG with hA | hB
    · exact hnA.2 hA
    · exact hnB.2 hB
  have hTAB_le : TA.ncard + TB.ncard ≤ 3 := by
    rw [← ncard_union_eq hdisj_TAB hTA_fin hTB_fin]
    have hsub : TA ∪ TB ⊆ tilde d := union_subset (fun _ h => h.1) (fun _ h => h.1)
    exact (ncard_le_ncard hsub htd_fin).trans
      (π.Γ.ncard_tilde_cell_le hdC)
  have hTA_pos : 1 ≤ TA.ncard := hTA_ne.ncard_pos hTA_fin
  have hTB_pos : 1 ≤ TB.ncard := hTB_ne.ncard_pos hTB_fin
  have h1 : TA.ncard = 1 ∨ TB.ncard = 1 := by omega
  rcases h1 with hTA1 | hTB1
  · obtain ⟨n, hn_eq⟩ := ncard_eq_one.mp hTA1
    have hn_TA : n ∈ TA := hn_eq ▸ mem_singleton n
    refine ⟨n, hn_TA.1, fun hAB_mem => hn_TA.2 hAB_mem.1, Or.inl ?_⟩
    rintro _ ⟨m, ⟨hmt, _⟩, rfl⟩
    by_cases hmA : π.nodeVertex m ∈ A.vertexSet
    · exact Or.inr hmA
    · have hm_TA : m ∈ TA := ⟨hmt, hmA⟩
      rw [hn_eq, mem_singleton_iff] at hm_TA
      exact Or.inl (congrArg π.nodeVertex hm_TA)
  · obtain ⟨n, hn_eq⟩ := ncard_eq_one.mp hTB1
    have hn_TB : n ∈ TB := hn_eq ▸ mem_singleton n
    refine ⟨n, hn_TB.1, fun hAB_mem => hn_TB.2 hAB_mem.2, Or.inr ?_⟩
    rintro _ ⟨m, ⟨hmt, _⟩, rfl⟩
    by_cases hmB : π.nodeVertex m ∈ B.vertexSet
    · exact Or.inr hmB
    · have hm_TB : m ∈ TB := ⟨hmt, hmB⟩
      rw [hn_eq, mem_singleton_iff] at hm_TB
      exact Or.inl (congrArg π.nodeVertex hm_TB)

private theorem vertices_of_each_cell_lie_on_one_separation_side
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {θ : ℕ}
    {p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hwarp : π.warp ≤ p)
    {A : Hypergraph α β}
    {B : Hypergraph α β}
    (hred23 : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hθ45 : 4 * p + 5 < θ)
    (n_fn : ↑(π.crossingCells A B) → π.S)
    (hn_spec : ∀ (d : ↑(π.crossingCells A B)), n_fn d ∈ tilde ↑d ∧ π.nodeVertex (n_fn d) ∉
      (A ∩ B).vertexSet ∧
      (π.gammaImage (tilde ↑d) ⊆ insert (π.nodeVertex (n_fn d)) A.vertexSet ∨ π.gammaImage (tilde
      ↑d) ⊆ insert (π.nodeVertex (n_fn d)) B.vertexSet))
    (W_D : Set α)
    (hW_D : ∀ d, π.nodeVertex (n_fn d) ∈ W_D)
    (A' : Hypergraph α β)
    (B' : Hypergraph α β)
    (hA'_V : A'.vertexSet = A.vertexSet ∪ W_D)
    (hB'_V : B'.vertexSet = B.vertexSet ∪ W_D) :
    ∀ c ∈ π.Γ.C, π.gammaImage (tilde c) ⊆ A'.vertexSet ∨ π.gammaImage (tilde c) ⊆ B'.vertexSet := by
  let D := π.crossingCells A B
  have hstar_side : ∀ c' ∈ π.Γ.CStar,
      π.gammaImage (tilde c') ⊆ A'.vertexSet ∨ π.gammaImage (tilde c') ⊆ B'.vertexSet := by
    intro c' hc'
    by_cases hc'_D : c' ∈ D
    · rcases (hn_spec ⟨c', hc'_D⟩).2.2 with hsubA | hsubB
      · refine Or.inl (hsubA.trans ?_)
        rw [hA'_V]
        exact insert_subset (Or.inr (hW_D ⟨c', hc'_D⟩)) subset_union_left
      · refine Or.inr (hsubB.trans ?_)
        rw [hB'_V]
        exact insert_subset (Or.inr (hW_D ⟨c', hc'_D⟩)) subset_union_left
    · by_cases hA_sub : π.gammaImage (tilde c') ⊆ A.vertexSet
      · exact Or.inl (hA_sub.trans (hA'_V.symm ▸ subset_union_left))
      · have hB_sub : π.gammaImage (tilde c') ⊆ B.vertexSet := by
          by_contra hnotB
          exact hc'_D ⟨hc', hA_sub, hnotB⟩
        exact Or.inr (hB_sub.trans (hB'_V.symm ▸ subset_union_left))
  intro c hc
  obtain ⟨c', hc'_star, htilde_sub⟩ :=
    exists_mem_CStar_tilde_subset h𝒯 π htrue hred23 hwarp hθ45 hc
  rcases hstar_side c' hc'_star with hA' | hB'
  · exact Or.inl ((π.gammaImage_mono htilde_sub).trans hA')
  · exact Or.inr ((π.gammaImage_mono htilde_sub).trans hB')

private theorem separation_vertices_partition_off_linkages
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {θ : ℕ}
    {p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯)
    (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hwarp : π.warp ≤ p)
    {A : Hypergraph α β}
    {B : Hypergraph α β}
    (hred23 : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hθ45 : 4 * p + 5 < θ)
    (sys : π.SystemOfStandardLinkages) :
    ((A ∩ B).vertexSet ∩ π.gammaImage π.Γ.N).ncard + ((A ∩ B).vertexSet \ (sys.S ∪ π.gammaImage
      π.Γ.N)).ncard = ((A ∩ B).vertexSet \ sys.S).ncard := by
  have hdisj_γS : Disjoint (π.gammaImage π.Γ.N) sys.S :=
    sys.disjoint_gammaImage_N_S h𝒯 π htrue hred23 hwarp hθ45
  have h1 : (A ∩ B).vertexSet ∩ π.gammaImage π.Γ.N =
      ((A ∩ B).vertexSet \ sys.S) ∩ π.gammaImage π.Γ.N := by
    ext v
    simp only [mem_inter_iff, mem_sdiff]
    exact ⟨fun ⟨hvAB, hvγ⟩ => ⟨⟨hvAB, Set.disjoint_left.mp hdisj_γS hvγ⟩, hvγ⟩,
      fun ⟨⟨hvAB, _⟩, hvγ⟩ => ⟨hvAB, hvγ⟩⟩
  have h2 : (A ∩ B).vertexSet \ (sys.S ∪ π.gammaImage π.Γ.N) =
      ((A ∩ B).vertexSet \ sys.S) \ π.gammaImage π.Γ.N := by
    ext v
    simp only [mem_sdiff, mem_union, not_or, and_assoc]
  rw [h1, h2]
  exact ncard_inter_add_ncard_sdiff_eq_ncard
    ((A ∩ B).vertexSet \ sys.S) (π.gammaImage π.Γ.N)
    ((A ∩ B).vertexSet_finite.subset sdiff_subset)

/-- **Graph Minors XVII, (11.7)** (page 195):
"$|V(A \cap B)| = |V(\alpha(c_0) \cap \alpha(-c_0))|.$" -/
theorem theorem_11_7_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 4))
    (hwarp : π.warp ≤ p)
    (hθ : 6 * p + 8 < θ)
    {c₀ : Set π.S} (hc₀ : c₀ ∈ π.Γ.C)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯)
    (hc₀A : π.cellGraph c₀ ≤ A)
    (hle : separationOrder A B ≤ ((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀).ncard) :
    separationOrder A B = ((π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀).ncard := by
  have : CompactSpace π.S := π.isSurface.1
  have : T2Space π.S := π.isSurface.2.1
  have : ConnectedSpace π.S := π.connected
  have hp_pos : 1 ≤ p := π.one_le_warp.trans hwarp
  have hred23 : π.IsRedundant 𝒯 θ (2 * p + 3) := hred.mono (by omega)
  have hθ45 : 4 * p + 5 < θ := by omega
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof
      h𝒯 π htrue hred23 hwarp hθ45
  obtain ⟨sys⟩ := exists_systemOfStandardLinkages h𝒯 π htrue hred23 hwarp hθ45
  have hsep : G.IsSeparation A B := h𝒯.isSeparation hAB
  have h116 := theorem_11_6_proof h𝒯 π htrue hred23 hwarp hθ45 sys hc₀ hAB hc₀A hle
  have h115 := theorem_11_5_proof h𝒯 π htrue hred23 hwarp hθ45 sys hsep
  set D := π.crossingCells A B
  have hD_fin : D.Finite := π.Γ.finite_cells.subset fun _ hd => hd.1.1
  have hex_nd : ∀ d : D, ∃ n : π.S,
      n ∈ tilde d.1 ∧
      π.nodeVertex n ∉ (A ∩ B).vertexSet ∧
      (π.gammaImage (tilde d.1) ⊆ insert (π.nodeVertex n) A.vertexSet ∨
       π.gammaImage (tilde d.1) ⊆ insert (π.nodeVertex n) B.vertexSet) := by
    exact distinct_nodes_for_dual_vertices π hdom hsep
  choose n_fn hn_spec using hex_nd
  let N_D : Set π.S := {n : π.S | ∃ d : D, n_fn d = n}
  have hND_sub_N : N_D ⊆ π.Γ.N := by
    rintro _ ⟨d, rfl⟩
    exact π.Γ.tilde_subset_N d.2.1.1 (hn_spec d).1
  have hND_card_le : N_D.ncard ≤ D.ncard := by
    have : Finite D := hD_fin.to_subtype
    let f : D → N_D := fun d => ⟨n_fn d, ⟨d, rfl⟩⟩
    have hf : Function.Surjective f := by
      rintro ⟨_, ⟨d, rfl⟩⟩
      exact ⟨d, rfl⟩
    simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_surjective f hf
  let W_D : Set α := π.nodeVertex '' N_D
  have hWD_sub_G : W_D ⊆ G.vertexSet := by
    rintro _ ⟨n, hn, rfl⟩
    exact π.nodeVertex_mem n (hdom ▸ hND_sub_N hn)
  have hWD_card_le : W_D.ncard ≤ D.ncard :=
    (ncard_image_le (π.Γ.finite_N.subset hND_sub_N)).trans hND_card_le
  let E_D : Hypergraph α β := {
    vertexSet := W_D
    edgeSet := ∅
    Inc := fun _ _ => False
    vertex_mem_of_inc := fun _ _ h => h.elim
    edge_mem_of_inc := fun _ _ h => h.elim
    vertexSet_finite := G.vertexSet_finite.subset hWD_sub_G
    edgeSet_finite := finite_empty
  }
  have hED_le : E_D ≤ G := ⟨hWD_sub_G, empty_subset _, fun _ h => h.elim⟩
  let A' := A ∪ E_D
  let B' := B ∪ E_D
  have hA'_le : A' ≤ G := union_le hsep.left_le hED_le
  have hB'_le : B' ≤ G := union_le hsep.right_le hED_le
  have hA'_V : A'.vertexSet = A.vertexSet ∪ W_D := rfl
  have hB'_V : B'.vertexSet = B.vertexSet ∪ W_D := rfl
  have hA'_E : A'.edgeSet = A.edgeSet := union_empty A.edgeSet
  have hB'_E : B'.edgeSet = B.edgeSet := union_empty B.edgeSet
  have hsep' : G.IsSeparation A' B' := by
    rw [isSeparation_iff_of_le hA'_le hB'_le]
    refine ⟨?_, ?_, ?_⟩
    · rw [hA'_V, hB'_V, ← union_union_distrib_right, hsep.vertexSet_union,
        union_eq_self_of_subset_right hWD_sub_G]
    · rw [hA'_E, hB'_E, hsep.edgeSet_union]
    · rw [hA'_E, hB'_E]; exact hsep.edgeSet_inter_eq
  have hAB'_V : (A' ∩ B').vertexSet = (A ∩ B).vertexSet ∪ W_D := by
    change (A.vertexSet ∪ W_D) ∩ (B.vertexSet ∪ W_D) = A.vertexSet ∩ B.vertexSet ∪ W_D
    ext v; simp only [mem_inter_iff, mem_union]; tauto
  have hord_AB_le : separationOrder A B ≤ 2 * p + 2 :=
    hle.trans (sys.ncard_inter_otherVertices_le h𝒯 π htrue hred23 hwarp hθ45 hc₀)
  have hD_le_3 : D.ncard ≤ 3 := by
    have hsub1 : (A ∩ B).vertexSet \ (sys.S ∪ π.gammaImage π.Γ.N) ⊆ (A ∩ B).vertexSet \ sys.S :=
      sdiff_subset_sdiff Subset.rfl subset_union_left
    have hle1 : ((A ∩ B).vertexSet \ (sys.S ∪ π.gammaImage π.Γ.N)).ncard ≤
        ((A ∩ B).vertexSet \ sys.S).ncard :=
      ncard_le_ncard hsub1 ((A ∩ B).vertexSet_finite.subset sdiff_subset)
    exact (h115.trans hle1).trans (h116.1.trans (π.Γ.ncard_tilde_cell_le hc₀))
  have hord_A'B'_le : separationOrder A' B' ≤ 2 * p + 5 := by
    change (A' ∩ B').vertexSet.ncard ≤ 2 * p + 5
    rw [hAB'_V]
    have hle_sum := ncard_union_le (A ∩ B).vertexSet W_D
    have : W_D.ncard ≤ 3 := hWD_card_le.trans hD_le_3
    change (A ∩ B).vertexSet.ncard ≤ 2 * p + 2 at hord_AB_le
    omega
  have hA'B'_mem : (A', B') ∈ 𝒯 :=
    GM10.theorem_2_9_case_1 h𝒯 hAB hsep' (by omega) subset_union_left
  have hc₀A' : π.cellGraph c₀ ≤ A' := hc₀A.trans (le_union_left hsep.left_le hED_le)
  have hcell_side : ∀ c ∈ π.Γ.C,
      π.gammaImage (tilde c) ⊆ A'.vertexSet ∨ π.gammaImage (tilde c) ⊆ B'.vertexSet := by
    exact vertices_of_each_cell_lie_on_one_separation_side (α := α) (β := β) (G := G) (𝒯 := 𝒯) (θ
      := θ) (p := p) h𝒯 π htrue hwarp (A := A) (B := B) hred23 hθ45  n_fn hn_spec  W_D (fun d
        => ⟨n_fn d, ⟨d, rfl⟩, rfl⟩)  A'
      B' hA'_V hB'_V
  let I : Set (Set π.S) := {c ∈ π.Γ.C | c = c₀ ∨ ¬ (π.gammaImage (tilde c) ⊆ B'.vertexSet)}
  let J : Set (Set π.S) := π.Γ.C \ I
  have hIJ_union : I ∪ J = π.Γ.C := by
    ext c
    simp only [I, J, mem_union, mem_sdiff, mem_ofPred_eq]
    tauto
  have hIJ_disj : Disjoint I J := disjoint_sdiff_self_right
  have hc₀_γA : π.gammaImage (tilde c₀) ⊆ A'.vertexSet := by
    rintro _ ⟨n, ⟨hnt, hndom⟩, rfl⟩
    exact Or.inl (hc₀A.vertexSet_subset (π.p2 c₀ hc₀ n ⟨hnt, hndom⟩))
  have hγI : π.gammaOfCells I ⊆ A'.vertexSet := by
    unfold Portrayal.gammaOfCells
    refine iUnion₂_subset ?_
    rintro c ⟨hcC, rfl | hnotB'⟩
    · exact hc₀_γA
    · exact (hcell_side c hcC).resolve_right hnotB'
  have hγJ : π.gammaOfCells J ⊆ B'.vertexSet := by
    unfold Portrayal.gammaOfCells
    refine iUnion₂_subset ?_
    rintro c ⟨hcC, hnotI⟩
    by_contra hnotB'
    exact hnotI ⟨hcC, Or.inr hnotB'⟩
  have hN_A'B'_eq :
      {n ∈ π.Γ.N | π.nodeVertex n ∈ (A' ∩ B').vertexSet} =
        {n ∈ π.Γ.N | π.nodeVertex n ∈ (A ∩ B).vertexSet} ∪ N_D := by
    ext n
    simp only [mem_ofPred_eq, hAB'_V, mem_union]
    constructor
    · rintro ⟨hnN, hnAB | ⟨m, hm_ND, hEq⟩⟩
      · exact Or.inl ⟨hnN, hnAB⟩
      · have hm_eq : m = n :=
          π.nodeVertex_injOn (hdom ▸ hND_sub_N hm_ND) (hdom ▸ hnN) hEq
        exact Or.inr (hm_eq ▸ hm_ND)
    · rintro (⟨hnN, hnAB⟩ | hn_ND)
      · exact ⟨hnN, Or.inl hnAB⟩
      · exact ⟨hND_sub_N hn_ND, Or.inr ⟨n, hn_ND, rfl⟩⟩
  have hN_AB_card_eq :
      {n ∈ π.Γ.N | π.nodeVertex n ∈ (A ∩ B).vertexSet}.ncard =
        ((A ∩ B).vertexSet ∩ π.gammaImage π.Γ.N).ncard := by
    have himg : π.nodeVertex '' {n ∈ π.Γ.N | π.nodeVertex n ∈ (A ∩ B).vertexSet} =
        (A ∩ B).vertexSet ∩ π.gammaImage π.Γ.N := by
      ext v
      simp only [mem_image, mem_ofPred_eq, mem_inter_iff, Portrayal.gammaImage]
      exact ⟨fun ⟨n, ⟨hnN, hvAB⟩, hEq⟩ => ⟨hEq ▸ hvAB, n, ⟨hnN, hdom ▸ hnN⟩, hEq⟩,
        fun ⟨hvAB, n, ⟨hnN, _⟩, hEq⟩ => ⟨n, ⟨hnN, hEq.symm ▸ hvAB⟩, hEq⟩⟩
    have hsub : {n ∈ π.Γ.N | π.nodeVertex n ∈ (A ∩ B).vertexSet} ⊆ π.domγ :=
      fun _ h => hdom ▸ h.1
    rw [← himg, (π.nodeVertex_injOn.mono hsub).ncard_image]
  have hsplit_AB_diff_S :
      ((A ∩ B).vertexSet ∩ π.gammaImage π.Γ.N).ncard +
        ((A ∩ B).vertexSet \ (sys.S ∪ π.gammaImage π.Γ.N)).ncard =
      ((A ∩ B).vertexSet \ sys.S).ncard := by
    exact separation_vertices_partition_off_linkages (α := α) (β := β) (G := G) (𝒯 := 𝒯) (θ := θ)
      (p := p) h𝒯 π htrue hwarp (A := A) (B := B) hred23 hθ45 sys
  have hN_A'B'_le_diff :
      {n ∈ π.Γ.N | π.nodeVertex n ∈ (A' ∩ B').vertexSet}.ncard ≤
        ((A ∩ B).vertexSet \ sys.S).ncard := by
    rw [hN_A'B'_eq]
    have hle_u := ncard_union_le {n ∈ π.Γ.N | π.nodeVertex n ∈ (A ∩ B).vertexSet} N_D
    rw [hN_AB_card_eq] at hle_u
    omega
  have hN_A'B'_le_tc₀ :
      {n ∈ π.Γ.N | π.nodeVertex n ∈ (A' ∩ B').vertexSet}.ncard ≤ (tilde c₀).ncard :=
    hN_A'B'_le_diff.trans h116.1
  have h112 := (theorem_11_2_proof h𝒯 π htrue hred hwarp hθ
    hA'B'_mem (by omega) hc₀ hc₀A' hIJ_union hIJ_disj ⟨hc₀, Or.inl rfl⟩ hγI hγJ hN_A'B'_le_tc₀).1
  have hdiff_eq_tc₀ : ((A ∩ B).vertexSet \ sys.S).ncard = (tilde c₀).ncard := by omega
  have hinter_eq := h116.2 hdiff_eq_tc₀
  set X := (A ∩ B).vertexSet
  set Y := (π.cellGraph c₀).vertexSet ∩ π.otherVertices c₀
  have hX_split : (X ∩ sys.S).ncard + (X \ sys.S).ncard = X.ncard :=
    ncard_inter_add_ncard_sdiff_eq_ncard X sys.S (A ∩ B).vertexSet_finite
  have hY_split : (Y ∩ sys.S).ncard + (Y \ sys.S).ncard = Y.ncard :=
    ncard_inter_add_ncard_sdiff_eq_ncard Y sys.S
      ((π.cellGraph c₀).vertexSet_finite.subset inter_subset_left)
  have hγ_card : (π.gammaImage (tilde c₀)).ncard = (tilde c₀).ncard := by
    have hsub_dom : tilde c₀ ⊆ π.domγ := hdom ▸ π.Γ.tilde_subset_N hc₀
    have himg : π.gammaImage (tilde c₀) = π.nodeVertex '' tilde c₀ := by
      ext v
      simp only [Portrayal.gammaImage, mem_image]
      exact ⟨fun ⟨n, ⟨hnt, _⟩, hEq⟩ => ⟨n, hnt, hEq⟩,
        fun ⟨n, hnt, hEq⟩ => ⟨n, ⟨hnt, hsub_dom hnt⟩, hEq⟩⟩
    rw [himg, (π.nodeVertex_injOn.mono hsub_dom).ncard_image]
  have hY_diff_card : (Y \ sys.S).ncard = (tilde c₀).ncard := by
    by_cases hbd : (c₀ ∩ bd π.S).Nonempty
    · rcases hbd with ⟨x₀, hxc₀, hxbd⟩
      let Θ := connectedComponentIn (bd π.S) x₀
      have hΘ : Θ ∈ cuffs π.S := ⟨x₀, hxbd, rfl⟩
      have hc₀Θ : (c₀ ∩ Θ).Nonempty := ⟨x₀, hxc₀, mem_connectedComponentIn hxbd⟩
      have hc₀_range : c₀ ∈ Set.range (sys.E Θ hΘ).cell := by
        rw [(sys.E Θ hΘ).range_cell]; exact ⟨hc₀, hc₀Θ⟩
      rcases hc₀_range with ⟨i₀, hi₀_eq⟩
      have hbd_props := sys.border_cell_properties h𝒯 π htrue hred23 hwarp hθ45 hΘ i₀
      have hdiff_eq : Y \ sys.S = π.gammaImage (tilde c₀) := by
        dsimp only [Y]
        rw [← hi₀_eq]
        exact hbd_props.2.2.1
      rw [hdiff_eq, hγ_card]
    · have hint_props := sys.internal_cell_properties h𝒯 π htrue hred23 hwarp hθ45 hc₀ hbd
      have hdiff_eq : Y \ sys.S = π.gammaImage (tilde c₀) := by
        dsimp only [Y]
        rw [(hint_props.2.mono_left inter_subset_left).sdiff_eq_left, hint_props.1]
      rw [hdiff_eq, hγ_card]
  change X.ncard = Y.ncard
  omega

end GraphMinor.GM17
