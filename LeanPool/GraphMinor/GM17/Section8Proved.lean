/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section8
import LeanPool.GraphMinor.GM17.Section5Proved
import LeanPool.GraphMinor.GM17.Section6Proved
import LeanPool.GraphMinor.GM17.Section7Proved

public import LeanPool.GraphMinor.GM17.Section7
public import LeanPool.GraphMinor.GM20.Cited

import LeanPool.GraphMinor.Surface.Cuffs

import LeanPool.GraphMinor.GM17.ArcDisc

import LeanPool.GraphMinor.GM17.CutArcPaint

import LeanPool.GraphMinor.GM17.MarkCross

import LeanPool.GraphMinor.GM17.PasteCuff

import LeanPool.GraphMinor.GM17.PushNode

import LeanPool.GraphMinor.GM17.RegionBoundary

import LeanPool.GraphMinor.GM17.RegionDisc

import LeanPool.GraphMinor.GM17.ReplaceDisc

/-!
# Graph Minors XVII: proved deductions of Section8

The portrayal deductions use the existing painting proofs. The definitions and
independent geometric lemmas are imported from `Section8`.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Preliminary Lemmas for True Portrayals -/

/-- **Graph Minors XVII, (8.1)** (page 181):
"Every region of $\Gamma$ is an open disc." -/
theorem theorem_8_1_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {r : Set π.S} (hr : r ∈ π.Γ.regions) :
    IsOpenDisc r := by
  have : ConnectedSpace π.S := π.connected
  have hN_ge2 : 2 ≤ π.Γ.N.ncard := by
    have hge := (π.sub_two_mul_warp_le_ncard_domγ h𝒯 htrue.1 hwarp).2
    omega
  have hU_ne : π.Γ.U.Nonempty :=
    ((ncard_pos π.Γ.finite_N).mp (by omega)).mono π.Γ.N_subset
  apply GraphMinor.GM17.regionOpenDiscCriterion π.S π.isSurface π.Γ hU_ne _ r hr
  intro F hO hdisj
  have hnorm : π.Γ.IsNormal F := by
    intro x hx
    exact False.elim (Set.disjoint_left.mp hdisj hx.1 hx.2)
  have hFN_empty : F ∩ π.Γ.N = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxF, hxN⟩
    exact Set.disjoint_left.mp hdisj hxF (π.Γ.N_subset hxN)
  have hFγ_le : (F ∩ π.domγ).ncard ≤ 1 := by
    have hsub : F ∩ π.domγ ⊆ F ∩ π.Γ.N := inter_subset_inter_right F π.domγ_subset
    have hempty : F ∩ π.domγ = ∅ := eq_empty_of_subset hsub hFN_empty
    rw [hempty, ncard_empty]
    omega
  have hred_1 : π.IsRedundant 𝒯 θ 1 := hred.mono (by omega)
  have hθ_64 : 1 + max 3 (2 * p + 2) < θ := by omega
  obtain ⟨Δ, hΔ, hbd, hsmall⟩ :=
    theorem_6_4_proof h𝒯 π htrue.1 hwarp hred_1 hθ_64 hO hnorm hFγ_le
  have hcard : (discBd Δ ∩ π.Γ.N).ncard ≤ 1 := by
    rw [hbd, hFN_empty, ncard_empty]
    omega
  have hnorm_bd : discBd Δ ∩ π.Γ.U ⊆ π.Γ.N := hbd ▸ hnorm
  obtain ⟨c', hc', hc'_out, hchoice⟩ :=
    π.exists_cell_outside_disc_of_small h𝒯 hΔ hnorm_bd hsmall
  obtain ⟨π', _, hπ'_central, hπ'_res, hnot_ne | htruer⟩ :=
    theorem_7_1_proof h𝒯 π htrue.1 hΔ hnorm_bd hcard hsmall hc' hc'_out hchoice
  · refine ⟨Δ, hΔ, hbd, Set.disjoint_left.mpr fun x hxΔ hxU => ?_⟩
    by_cases hxF : x ∈ discBd Δ
    · exact Set.disjoint_left.mp hdisj (hbd ▸ hxF) hxU
    · exact hnot_ne ⟨x, ⟨hxΔ, hxF⟩, hxU⟩
  · exact False.elim (htrue.2.2 π' hπ'_central htruer hπ'_res)

private theorem region_boundary_props
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) :
    (∀ r ∈ π.Γ.regions, IsOArc (closure r \ r)) ∧
    (∀ c ∈ π.Γ.C, 2 ≤ (tilde c).ncard) ∧
    (∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c) ∧
    (∀ n ∈ π.Γ.N ∩ bd π.S, (∀ c ∈ π.Γ.C, n ∈ tilde c → (c ∩ bd π.S).Nonempty) →
      ∃ F : Set π.S, IsLine F ∧ π.Γ.IsNormal F ∧ F ∩ bd π.S = lineEnds F ∧ (F ∩ π.Γ.N).ncard = 2 ∧
        ∀ Δ : Set π.S, IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd π.S →
          ¬ (Δ ∩ π.Γ.N ⊆ F ∧ {c ∈ π.Γ.C | c ⊆ Δ}.ncard = 1)) ∧
    (∀ c ∈ π.Γ.C, ¬ (c ∩ bd π.S).Nonempty →
      (∀ n₁ ∈ closure c ∩ bd π.S, ∀ n₂ ∈ closure c ∩ bd π.S, n₁ ≠ n₂ →
        ∃ F : Set π.S, IsLineWithEnds F n₁ n₂ ∧ π.Γ.IsNormal F ∧ F ∩ bd π.S = lineEnds F ∧
          F ∩ bd π.S = {n₁, n₂} ∧ F ∩ π.Γ.N = {n₁, n₂} ∧
          ∀ Δ : Set π.S, IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd π.S →
            (Δ ∩ (bd π.S \ {n₁, n₂})).Nonempty ∧
            ∀ c₀ ∈ π.Γ.C, (c₀ ∩ Δ).Nonempty → c₀ ⊆ Δ) ∧
      (tilde c ⊆ bd π.S →
        ∃ F : Set π.S, IsLine F ∧ π.Γ.IsNormal F ∧ F ∩ bd π.S = lineEnds F ∧ (F ∩ π.Γ.N).ncard = 2 ∧
          ∀ Δ : Set π.S, IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd π.S →
            ¬ (Δ ∩ π.Γ.N ⊆ F ∧ {d ∈ π.Γ.C | d ⊆ Δ}.ncard = 1))) ∧
    (∀ c₁ ∈ π.Γ.C, ∀ c₂ ∈ π.Γ.C, c₁ ≠ c₂ →
      (c₁ ∩ bd π.S).Nonempty → (c₂ ∩ bd π.S).Nonempty → tilde c₁ = tilde c₂ →
      ∃ F : Set π.S, IsOArc F ∧ π.Γ.IsNormal F ∧ (F ∩ π.Γ.N).ncard = 2 ∧
        ∀ Δ : Set π.S, IsClosedDisc Δ → discBd Δ = F → ¬ (Δ ∩ π.Γ.N ⊆ F)) ∧
    (∀ n ∈ π.Γ.N \ bd π.S,
      ({c ∈ π.Γ.C | n ∈ tilde c}.ncard ≤ 1 ∨
        ({c ∈ π.Γ.C | n ∈ tilde c}.ncard = 2 ∧
          ∃ c₀ ∈ π.Γ.C, n ∈ tilde c₀ ∧ (tilde c₀).ncard = 2)) →
      ∃ F : Set π.S, IsOArc F ∧ π.Γ.IsNormal F ∧ (F ∩ π.Γ.N).ncard ≤ 3 ∧
        ∀ Δ : Set π.S, IsClosedDisc Δ → discBd Δ = F →
          ((Δ ∩ π.Γ.N ⊆ F ∧ {c ∈ π.Γ.C | c ⊆ Δ}.ncard ≤ 1) ∨
            ((F ∩ π.Γ.N).ncard = 3 ∧ ∀ c ∈ π.Γ.C, c ⊆ Δ → (tilde c).ncard = 2)) →
          ∃ d₁ ∈ π.Γ.C, ∃ d₂ ∈ π.Γ.C, π.Γ.C ⊆ {d₁, d₂} ∪ {c ∈ π.Γ.C | c ⊆ Δ}) := by
  have : ConnectedSpace π.S := π.connected
  have h81 : ∀ r ∈ π.Γ.regions, IsOpenDisc r :=
    fun r hr => theorem_8_1_proof h𝒯 π htrue hred hwarp hθ hr
  have hN_ge6 : 6 ≤ π.Γ.N.ncard := by
    have hge := (π.sub_two_mul_warp_le_ncard_domγ h𝒯 htrue.1 hwarp).2
    omega
  apply GraphMinor.GM17.regionBoundaryOArcCriterion π.S π.isSurface π.Γ hN_ge6 h81
  intro F hO hnorm hcard
  have hFγ_le : (F ∩ π.domγ).ncard ≤ 1 := by
    have hsub : F ∩ π.domγ ⊆ F ∩ π.Γ.N := inter_subset_inter_right F π.domγ_subset
    have hfin : (F ∩ π.Γ.N).Finite := π.Γ.finite_N.inter_of_right F
    exact (ncard_le_ncard hsub hfin).trans hcard
  have hred_1 : π.IsRedundant 𝒯 θ 1 := hred.mono (by omega)
  have hθ_64 : 1 + max 3 (2 * p + 2) < θ := by omega
  obtain ⟨Δ, hΔ, hbd, hsmall⟩ :=
    theorem_6_4_proof h𝒯 π htrue.1 hwarp hred_1 hθ_64 hO hnorm hFγ_le
  have hcard_bd : (discBd Δ ∩ π.Γ.N).ncard ≤ 1 := hbd.symm ▸ hcard
  have hnorm_bd : discBd Δ ∩ π.Γ.U ⊆ π.Γ.N := hbd ▸ hnorm
  obtain ⟨c', hc', hc'_out, hchoice⟩ :=
    π.exists_cell_outside_disc_of_small h𝒯 hΔ hnorm_bd hsmall
  obtain ⟨π', _, hπ'_central, hπ'_res, hnot_ne | htruer⟩ :=
    theorem_7_1_proof h𝒯 π htrue.1 hΔ hnorm_bd hcard_bd hsmall hc' hc'_out hchoice
  · refine ⟨Δ, hΔ, hbd, fun x ⟨hxΔ, hxU⟩ => ?_⟩
    by_contra hxF
    exact hnot_ne ⟨x, ⟨hxΔ, hbd.symm ▸ hxF⟩, hxU⟩
  · exact False.elim (htrue.2.2 π' hπ'_central htruer hπ'_res)

/-- **Graph Minors XVII, (8.2)** (page 181):
"The boundary of every region is an $O$-arc, and in particular, $|\tilde{c}| \ge 2$ for every
cell $c$." -/
theorem theorem_8_2_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) :
    (∀ r ∈ π.Γ.regions, IsOArc (closure r \ r)) ∧
    (∀ c ∈ π.Γ.C, 2 ≤ (tilde c).ncard) ∧
    (∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c) := by
  obtain ⟨h1, h2, h3, -⟩ :=
    region_boundary_props h𝒯 π htrue hred hwarp hθ
  exact ⟨h1, h2, h3⟩

/-! ## 3. Normal $I$-Arcs with Two Nodes: (8.3) (Page 182) -/

/-- **Graph Minors XVII, (8.3)** (page 182):
"For every $\Gamma$-normal $I$-arc $F$ with $|F \cap N(\Gamma)| = 2$, there is a disc
$\Delta \subseteq \Sigma$ with $F \subseteq \operatorname{bd}(\Delta) \subseteq F \cup
\operatorname{bd}(\Sigma)$
such that $\Delta \cap N(\Gamma) \subseteq F$ and $\Delta$ includes exactly one cell of $\Gamma$."
-/
theorem theorem_8_3_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {F : Set π.S} (hL : IsLine F) (hnorm : π.Γ.IsNormal F)
    (hFbd_ends : F ∩ bd π.S = lineEnds F)
    (hcard : (F ∩ π.Γ.N).ncard = 2) :
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd π.S ∧
      Δ ∩ π.Γ.N ⊆ F ∧ {c ∈ π.Γ.C | c ⊆ Δ}.ncard = 1 := by
  rcases hL with ⟨f⟩
  let n₁ : π.S := (f 0).1
  let n₂ : π.S := (f 1).1
  have hF : IsLineWithEnds F n₁ n₂ := ⟨f, rfl, rfl⟩
  have hne : n₁ ≠ n₂ := ne_of_isLineWithEnds hF
  have hends_sub_bd : ({n₁, n₂} : Set π.S) ⊆ F ∩ bd π.S := by
    rw [hFbd_ends]
    exact (ends_subset_of_isLineWithEnds hF).2
  have hbd_sub_FN : F ∩ bd π.S ⊆ F ∩ π.Γ.N :=
    fun x ⟨hxF, hxbd⟩ => ⟨hxF, hnorm ⟨hxF, π.Γ.bd_subset hxbd⟩⟩
  have hFN_fin : (F ∩ π.Γ.N).Finite := π.Γ.finite_N.inter_of_right F
  have hbd_fin : (F ∩ bd π.S).Finite := hFN_fin.subset hbd_sub_FN
  have hpair_card : ({n₁, n₂} : Set π.S).ncard = 2 := ncard_pair hne
  have hFN_eq : F ∩ π.Γ.N = {n₁, n₂} := by
    symm
    apply eq_of_subset_of_ncard_le (hends_sub_bd.trans hbd_sub_FN) _ hFN_fin
    omega
  have hFbd_eq : F ∩ bd π.S = {n₁, n₂} := by
    symm
    apply eq_of_subset_of_ncard_le hends_sub_bd _ hbd_fin
    have hle := ncard_le_ncard hbd_sub_FN hFN_fin
    omega
  have hred_63 : π.IsRedundant 𝒯 θ (2 * p + 2) := hred.mono (by omega)
  have hθ_63 : (2 * p + 2) + max 3 (2 * p + 2) < θ := by omega
  have hFγ_63 : 2 * p ≤ 2 * p + 2 ∧ (F ∩ π.domγ).ncard ≤ (2 * p + 2) - 2 * p := by
    refine ⟨by omega, ?_⟩
    have hsub : F ∩ π.domγ ⊆ F ∩ π.Γ.N := inter_subset_inter_right F π.domγ_subset
    have hle := (ncard_le_ncard hsub hFN_fin).trans hcard.le
    omega
  obtain ⟨Δ, hΔ, hF_bd, hbd_sub, hsmall⟩ :=
    theorem_6_3_proof h𝒯 π htrue.1 hwarp hred_63 hθ_63 hnorm hF hFbd_eq hFγ_63
  obtain ⟨π', hπ'_central, hπ'_res, htruer | ⟨hΔ_N, hΔ_card⟩⟩ :=
    theorem_7_4_proof h𝒯 π htrue.1 hred hwarp hθ
      hnorm hF hFbd_eq hFN_eq hΔ hF_bd hbd_sub hsmall
  · exact False.elim (htrue.2.2 π' hπ'_central htruer hπ'_res)
  · exact ⟨Δ, hΔ, hF_bd, hbd_sub, hΔ_N, hΔ_card⟩

/-- Proof of `GM20.GM17Theorem83Statement` in `GraphMinor/GM20/Cited.lean` (Graph Minors XVII,
(8.3), page 182). -/
theorem gm17_theorem_8_3
     :
    GM20.GM17Theorem83Statement.{u, v} := by
  intro α β G 𝒯 θ p π hstand F hL hnorm hFbd hcard
  exact theorem_8_3_proof
    hstand.isTangle π hstand.isTrue hstand.isRedundant hstand.warp_le hstand.lt
    hL hnorm hFbd hcard

/-! ## 4. Every Node is in $\operatorname{dom}(\gamma)$: (8.4) (Page 182) -/

/-- If an internal node $n_0 \in N(\Gamma) \setminus \operatorname{bd}(\Sigma)$ with
$n_0 \notin \operatorname{dom}(\gamma)$ does not belong to $\tilde{c}$ for any cell
$c \in C(\Gamma)$, then removing $n_0$ from $U(\Gamma)$ and $N(\Gamma)$ yields a truer
$\mathcal{T}$-central portrayal of $G$ resembling $\pi$. -/
private theorem exists_truer_of_isolated_internal_node
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (π : Portrayal G) (hcentral : π.IsCentral 𝒯)
    {n₀ : π.S} (hn₀_N : n₀ ∈ π.Γ.N) (hn₀_not_bd : n₀ ∉ bd π.S)
    (hn₀_not_dom : n₀ ∉ π.domγ)
    (hn₀_no_cell : ∀ c ∈ π.Γ.C, n₀ ∉ tilde c) :
    ∃ π' : Portrayal G, π'.IsCentral 𝒯 ∧ π'.Resembles π ∧ π'.IsTruer π := by
  classical
  have : T2Space π.S := π.isSurface.2.1
  have hn₀_not_cl : ∀ c ∈ π.Γ.C, n₀ ∉ closure c := by
    intro c hc hn₀_cl
    have hn₀_not_c : n₀ ∉ c := (π.Γ.cell_subset_diff hc · |>.2 hn₀_N)
    exact hn₀_no_cell c hc ⟨hn₀_cl, hn₀_not_c⟩
  let U' : Set π.S := π.Γ.U \ {n₀}
  let N' : Set π.S := π.Γ.N \ {n₀}
  have hU'_eq : U' = N' ∪ ⋃ c ∈ π.Γ.C, closure c := by
    ext x
    simp only [U', N', mem_sdiff, mem_singleton_iff, mem_union, mem_iUnion]
    constructor
    · rintro ⟨hxU, hne⟩
      rw [π.Γ.U_eq_N_union_biUnion_closure] at hxU
      rcases hxU with hxN | hcl
      · exact Or.inl ⟨hxN, hne⟩
      · rw [mem_iUnion₂] at hcl
        exact Or.inr hcl
    · rintro (⟨hxN, hne⟩ | ⟨c, hc, hxcl⟩)
      · exact ⟨π.Γ.N_subset hxN, hne⟩
      · exact ⟨π.Γ.closure_cell_subset_U hc hxcl, fun h => hn₀_not_cl c hc (h ▸ hxcl)⟩
  have hN'_fin : N'.Finite := π.Γ.finite_N.subset sdiff_subset
  have hU'_closed : IsClosed U' := by
    rw [hU'_eq]
    exact hN'_fin.isClosed.union (π.Γ.finite_cells.isClosed_biUnion fun _ _ => isClosed_closure)
  have hdiff_eq : U' \ N' = π.Γ.U \ π.Γ.N := by
    ext x
    simp only [U', N', mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨⟨hxU, hne⟩, hnotN⟩ => ⟨hxU, fun hxN => hnotN ⟨hxN, hne⟩⟩,
      fun ⟨hxU, hxN⟩ => ⟨⟨hxU, fun h => hxN (h ▸ hn₀_N)⟩, fun ⟨h, _⟩ => hxN h⟩⟩
  have hC'_eq : arcComponentsIn (U' \ N') = π.Γ.C := by
    rw [hdiff_eq]; rfl
  have hN'_bd : N' ∩ bd π.S = π.Γ.N ∩ bd π.S := by
    ext x
    simp only [N', mem_inter_iff, mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨⟨hxN, _⟩, hxbd⟩ => ⟨hxN, hxbd⟩,
      fun ⟨hxN, hxbd⟩ => ⟨⟨hxN, fun h => hn₀_not_bd (h ▸ hxbd)⟩, hxbd⟩⟩
  let Γ' : Painting π.S :=
    { U := U'
      N := N'
      isClosed_U := hU'_closed
      finite_N := hN'_fin
      N_subset := sdiff_subset_sdiff π.Γ.N_subset Subset.rfl
      finite_cells := hC'_eq ▸ π.Γ.finite_cells
      cell_disc := fun c hc => π.Γ.cell_disc c (by rwa [hdiff_eq] at hc)
      bd_subset := fun x hxbd => ⟨π.Γ.bd_subset hxbd, fun h => hn₀_not_bd (h ▸ hxbd)⟩
      border_cell := fun c hc hbd => π.Γ.border_cell c (by rwa [hdiff_eq] at hc) hbd }
  have hΓ'_C : Γ'.C = π.Γ.C := hC'_eq
  let π' : Portrayal G :=
    { S := π.S
      top := π.top
      isSurface := π.isSurface
      connected := π.connected
      Γ := Γ'
      cellGraph := π.cellGraph
      borderSet := π.borderSet
      domγ := π.domγ
      nodeVertex := π.nodeVertex
      cellGraph_le := fun c hc => π.cellGraph_le c (hΓ'_C ▸ hc)
      borderSet_subset := fun n hn => π.borderSet_subset n (hN'_bd ▸ hn)
      domγ_subset := fun n hn => ⟨π.domγ_subset hn, fun h => hn₀_not_dom (h ▸ hn)⟩
      nodeVertex_mem := π.nodeVertex_mem
      nodeVertex_injOn := π.nodeVertex_injOn
      p1_vertex := fun v hv => by
        obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv
        exact ⟨c, hΓ'_C.symm ▸ hc, hvc⟩
      p1_edge := fun e he => by
        obtain ⟨c, hc, hec⟩ := π.p1_edge e he
        exact ⟨c, hΓ'_C.symm ▸ hc, hec⟩
      p1_disjoint := fun c₁ hc₁ c₂ hc₂ hne =>
        π.p1_disjoint c₁ (hΓ'_C ▸ hc₁) c₂ (hΓ'_C ▸ hc₂) hne
      p2 := fun c hc n hn => π.p2 c (hΓ'_C ▸ hc) n hn
      p3_notMem := fun n hn => π.p3_notMem n ⟨hn.1, hn.2⟩
      p3_subset := fun c hc hbd n hn => π.p3_subset c (hΓ'_C ▸ hc) hbd n hn
      p4_disjoint := fun Θ₁ hΘ₁ Θ₂ hΘ₂ hne n₁ hn₁ n₂ hn₂ =>
        π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne n₁ ⟨hn₁.1.1, hn₁.2⟩ n₂ ⟨hn₂.1.1, hn₂.2⟩
      p4_notMem := fun Θ hΘ n₁ hn₁ n₂ hn₂ hnot =>
        π.p4_notMem Θ hΘ n₁ ⟨hn₁.1.1, hn₁.2⟩ n₂ hn₂ hnot
      p5 := fun c hc hint v hvc ⟨d, hd, hne, hvd⟩ =>
        π.p5 c (hΓ'_C ▸ hc) hint v hvc ⟨d, hΓ'_C ▸ hd, hne, hvd⟩
      p6 := fun c hc hbd v hvc ⟨d, hd, hne, hvd⟩ =>
        π.p6 c (hΓ'_C ▸ hc) hbd v hvc ⟨d, hΓ'_C ▸ hd, hne, hvd⟩
      p7 := fun Θ hΘ n₁ hn₁ n₂ hn₂ n₃ hn₃ n₄ hn₄ =>
        π.p7 Θ hΘ n₁ ⟨hn₁.1.1, hn₁.2⟩ n₂ ⟨hn₂.1.1, hn₂.2⟩
          n₃ ⟨hn₃.1.1, hn₃.2⟩ n₄ ⟨hn₄.1.1, hn₄.2⟩ }
  have hπ'_central : π'.IsCentral 𝒯 := fun c hc => hcentral c (hΓ'_C ▸ hc)
  have hπ'_res : π'.Resembles π := by
    refine ⟨Homeomorph.refl π.S, fun Θ _ => ?_⟩
    rw [Homeomorph.refl_apply, image_id]
    change sSup {p | ∃ c ∈ Γ'.C, (c ∩ Θ).Nonempty ∧ p = π'.cellWarp c} =
      sSup {p | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c}
    have hcw : ∀ c, π'.cellWarp c = π.cellWarp c := fun _ => rfl
    simp only [hΓ'_C, hcw]
  have hπ'_truer : π'.IsTruer π := by
    refine ⟨⟨4, by omega⟩, fun i hi => ?_, ?_⟩
    · have hi4 : i.1 < 4 := hi
      simp only [Portrayal.truth, π', hi4, ↓reduceIte, hΓ'_C]
    · simp only [Portrayal.truth, π']
      have hssub : N' \ bd π.S ⊂ π.Γ.N \ bd π.S :=
        ⟨sdiff_subset_sdiff sdiff_subset Subset.rfl,
          fun h => (h ⟨hn₀_N, hn₀_not_bd⟩).1.2 rfl⟩
      exact ncard_lt_ncard hssub (π.Γ.finite_N.subset sdiff_subset)
  exact ⟨π', hπ'_central, hπ'_res, hπ'_truer⟩

/-- **Graph Minors XVII, (8.4)** (page 182):
"$\operatorname{dom}(\gamma) = N(\Gamma)$." -/
theorem theorem_8_4_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ) :
    π.domγ = π.Γ.N := by
  have : T2Space π.S := π.isSurface.2.1
  refine Subset.antisymm π.domγ_subset fun n hn_N => ?_
  by_contra hn_not_dom
  -- If `n ∈ tilde c` for some internal cell `c`, shrinking `c` from `n` by `(5.2)` gives a truer
  -- portrayal.
  have hno_int : ∀ c ∈ π.Γ.C, n ∈ tilde c → (c ∩ bd π.S).Nonempty := by
    intro c hc hn_tc
    by_contra hint
    obtain ⟨Δ, Γ', hsh, hπ'_central, hπ'_res, hπ'_truer⟩ :=
      theorem_5_2_proof π ⟨hc, hint⟩ hn_tc (fun hnγ => False.elim (hn_not_dom hnγ))
    exact htrue.2.2 (π.shrinkCell Γ' c n Δ hsh (fun hnγ => False.elim (hn_not_dom hnγ)))
      (hπ'_central 𝒯 htrue.1) hπ'_truer hπ'_res
  -- Hence `n` must be a border node (otherwise `n` is in no `tilde c`, giving a truer portrayal).
  have hn_bd : n ∈ bd π.S := by
    by_contra hn_not_bd
    have hn_no_cell : ∀ c ∈ π.Γ.C, n ∉ tilde c := by
      intro c hc hn_tc
      have hbd_c := hno_int c hc hn_tc
      obtain ⟨u, w, _, htilde_c, _, _, hu_bd, hw_bd⟩ := π.Γ.border_cell_exists_ends hc hbd_c
      rcases (htilde_c ▸ hn_tc : n ∈ ({u, w} : Set π.S)) with rfl | rfl
      · exact hn_not_bd hu_bd.2
      · exact hn_not_bd hw_bd.2
    obtain ⟨π', hπ'_central, hπ'_res, hπ'_truer⟩ :=
      exists_truer_of_isolated_internal_node π htrue.1 hn_N hn_not_bd hn_not_dom hn_no_cell
    exact htrue.2.2 π' hπ'_central hπ'_truer hπ'_res
  -- Pushing off the two border cells at `n` gives a normal `I`-arc violating `(8.3)`.
  obtain ⟨-, -, -, hBdInt, -⟩ :=
    region_boundary_props h𝒯 π htrue hred hwarp hθ
  obtain ⟨F, hL, hnorm, hFbd, hcard, hno_disc⟩ := hBdInt n ⟨hn_N, hn_bd⟩ hno_int
  obtain ⟨Δ, hΔ, hF_bd, hbd_sub, hΔ_N, hΔ_card⟩ :=
    theorem_8_3_proof h𝒯 π htrue hred hwarp hθ hL hnorm hFbd hcard
  exact hno_disc Δ hΔ hF_bd hbd_sub ⟨hΔ_N, hΔ_card⟩

/-! ## 5. Normal $O$-Arcs with at Most Three Nodes: (8.5) (Page 182) -/

/-- **Graph Minors XVII, (8.5)** (page 182):
"For every $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with $|F \cap N(\Gamma)| \le 3$, there is
a disc $\Delta \subseteq \Sigma$ with $F = \operatorname{bd}(\Delta)$ such that $\alpha(\Delta)$ is
small, and either
(i) $\Delta \cap N(\Gamma) \subseteq F$ and $\Delta$ includes at most one cell of $\Gamma$, or
(ii) $|F \cap N(\Gamma)| = 3$, and $|\tilde{c}| = 2$ for every cell $c \subseteq \Delta$." -/
theorem theorem_8_5_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {F : Set π.S} (hO : IsOArc F) (hnorm : π.Γ.IsNormal F)
    (hcard : (F ∩ π.Γ.N).ncard ≤ 3) :
    ∃ Δ : Set π.S, IsClosedDisc Δ ∧ discBd Δ = F ∧
      IsSmallWrt 𝒯 (π.areaGraph Δ) ∧
      ((Δ ∩ π.Γ.N ⊆ F ∧ {c ∈ π.Γ.C | c ⊆ Δ}.ncard ≤ 1) ∨
        ((F ∩ π.Γ.N).ncard = 3 ∧ ∀ c ∈ π.Γ.C, c ⊆ Δ → (tilde c).ncard = 2)) := by
  have : T2Space π.S := π.isSurface.2.1
  obtain ⟨_, h82_card, h82_node⟩ :=
    theorem_8_2_proof h𝒯 π htrue hred hwarp hθ
  have hFN_fin : (F ∩ π.Γ.N).Finite := π.Γ.finite_N.inter_of_right F
  have hFγ_le : (F ∩ π.domγ).ncard ≤ 2 * p + 3 := by
    have hsub : F ∩ π.domγ ⊆ F ∩ π.Γ.N := inter_subset_inter_right F π.domγ_subset
    have hle3 : (F ∩ π.domγ).ncard ≤ 3 := (ncard_le_ncard hsub hFN_fin).trans hcard
    omega
  have hp_pos : 1 ≤ p := π.one_le_warp.trans hwarp
  have hθ_64 : (2 * p + 3) + max 3 (2 * p + 2) < θ := by omega
  obtain ⟨Δ, hΔ, hbd, hsmall⟩ :=
    theorem_6_4_proof h𝒯 π htrue.1 hwarp hred hθ_64 hO hnorm hFγ_le
  refine ⟨Δ, hΔ, hbd, hsmall, ?_⟩
  have hnorm_bd : discBd Δ ∩ π.Γ.U ⊆ π.Γ.N := hbd ▸ hnorm
  obtain ⟨hdich, _, _⟩ := normal_disc_cell_dichotomy π.isSurface π.Γ hΔ hnorm_bd
  by_cases hex_c : ({c ∈ π.Γ.C | c ⊆ Δ}).Nonempty
  · by_cases hex_ge : ∃ c₀ ∈ π.Γ.C, c₀ ⊆ Δ ∧ (discBd Δ ∩ π.Γ.N).ncard ≤ (tilde c₀).ncard
    · -- Apply `(7.2)` (`theorem_7_2_proof`): since `π` is true, `π'` cannot be truer, so (i) holds.
      have hcard_bd : (discBd Δ ∩ π.Γ.N).ncard ≤ 3 := hbd.symm ▸ hcard
      have hnode_bd : ∀ n ∈ discBd Δ ∩ π.domγ, ∃ d ∈ π.Γ.C, n ∈ tilde d :=
        fun n hn => h82_node n (π.domγ_subset hn.2)
      obtain ⟨π', _, hπ'_central, hπ'_res, h72⟩ :=
        theorem_7_2_proof h𝒯 (by omega) π htrue.1 hΔ hnorm_bd hcard_bd hnode_bd hsmall
      rcases h72 hex_ge with htruer | ⟨hΔ_N, c₀, _, hset_eq⟩
      · exact False.elim (htrue.2.2 π' hπ'_central htruer hπ'_res)
      · left
        refine ⟨hbd ▸ hΔ_N, ?_⟩
        rw [hset_eq, ncard_singleton]
    · -- Every cell `c ⊆ Δ` has `2 ≤ (tilde c).ncard < (F ∩ π.Γ.N).ncard ≤ 3`, so (ii) holds.
      right
      push Not at hex_ge
      rcases hex_c with ⟨c₁, hc₁_C, hc₁_Δ⟩
      have h2_c₁ : 2 ≤ (tilde c₁).ncard := h82_card c₁ hc₁_C
      have hlt_c₁ : (tilde c₁).ncard < (F ∩ π.Γ.N).ncard := hbd ▸ hex_ge c₁ hc₁_C hc₁_Δ
      have hFN_eq3 : (F ∩ π.Γ.N).ncard = 3 := by omega
      refine ⟨hFN_eq3, fun c hc_C hc_Δ => ?_⟩
      have h2_c : 2 ≤ (tilde c).ncard := h82_card c hc_C
      have hlt_c : (tilde c).ncard < (F ∩ π.Γ.N).ncard := hbd ▸ hex_ge c hc_C hc_Δ
      omega
  · -- When `{c ∈ π.Γ.C | c ⊆ Δ} = ∅`, (i) holds by `(8.2)`.
    left
    have hempty : {c ∈ π.Γ.C | c ⊆ Δ} = ∅ := not_nonempty_iff_eq_empty.mp hex_c
    refine ⟨fun n ⟨hnΔ, hnN⟩ => ?_, by rw [hempty, ncard_empty]; omega⟩
    obtain ⟨c, hc_C, hn_tc⟩ := h82_node n hnN
    have hc_out : c ⊆ Set.univ \ Δ := by
      rcases hdich c hc_C with hc_in | hc_out
      · exact False.elim (hex_c ⟨c, hc_C, hc_in.trans sdiff_subset⟩)
      · exact hc_out
    have hcl_inter :=
      (closure_cell_inter_disc_of_subset_compl π.isSurface π.Γ hΔ hnorm_bd hc_C hc_out).2
    have hn_mem : n ∈ closure c ∩ Δ := ⟨hn_tc.1, hnΔ⟩
    rw [hcl_inter] at hn_mem
    exact hbd ▸ hn_mem.2

/-- Proof of `GM20.GM17Theorem85Statement` in `GraphMinor/GM20/Cited.lean`
(Graph Minors XVII, (8.5), page 182). -/
theorem gm17_theorem_8_5
     :
    GM20.GM17Theorem85Statement.{u, v} := by
  intro α β G 𝒯 θ p π hstand F hO hnorm hcard
  obtain ⟨Δ, hΔ, hbd, ⟨B, hAB⟩, hdisj_cases⟩ :=
    theorem_8_5_proof
      hstand.isTangle π hstand.isTrue hstand.isRedundant hstand.warp_le hstand.lt
      hO hnorm hcard
  have hsub : {c ∈ π.Γ.C | c ⊆ Δ} ⊆ π.Γ.C := fun _ hc => hc.1
  refine ⟨Δ, hΔ, hbd, ⟨π.areaGraph Δ, B, hAB, ?_, ?_⟩, hdisj_cases⟩
  · change (⋃ c ∈ {c ∈ π.Γ.C | c ⊆ Δ} ∩ π.Γ.C, (π.cellGraph c).vertexSet) =
      ⋃ c ∈ {c ∈ π.Γ.C | c ⊆ Δ}, (π.cellGraph c).vertexSet
    rw [inter_eq_left.mpr hsub]
  · change (⋃ c ∈ {c ∈ π.Γ.C | c ⊆ Δ} ∩ π.Γ.C, (π.cellGraph c).edgeSet) =
      ⋃ c ∈ {c ∈ π.Γ.C | c ⊆ Δ}, (π.cellGraph c).edgeSet
    rw [inter_eq_left.mpr hsub]

/-! ## 6. Internal Cells Meeting the Boundary: (8.6) (Page 182) -/

/-- **Graph Minors XVII, (8.6)** (page 182):
"If $c$ is an internal cell, then $|\bar{c} \cap \operatorname{bd}(\Sigma)| \le 2$, and if equality
holds then $|\tilde{c}| = 3$ and the two members of $\bar{c} \cap \operatorname{bd}(\Sigma)$ are
consecutive." -/
theorem theorem_8_6_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {c : Set π.S} (hc : c ∈ π.Γ.C) (hint : ¬ (c ∩ bd π.S).Nonempty) :
    (closure c ∩ bd π.S).ncard ≤ 2 ∧
    ((closure c ∩ bd π.S).ncard = 2 →
      (tilde c).ncard = 3 ∧
      ∀ n₁ ∈ closure c ∩ bd π.S, ∀ n₂ ∈ closure c ∩ bd π.S, n₁ ≠ n₂ →
        ∃ c₀ ∈ π.Γ.C, (c₀ ∩ bd π.S).Nonempty ∧ tilde c₀ = {n₁, n₂}) := by
  have : T2Space π.S := π.isSurface.2.1
  obtain ⟨-, h82_card, -, -, hIntArcs, -⟩ :=
    region_boundary_props h𝒯 π htrue hred hwarp hθ
  obtain ⟨hI_pair, hI_viol⟩ := hIntArcs c hc hint
  -- First show `¬ (tilde c ⊆ bd π.S)`, since otherwise pushing off `c` violates `(8.3)`.
  have hnot_sub_bd : ¬ (tilde c ⊆ bd π.S) := by
    intro hsub_bd
    obtain ⟨F, hL, hnorm, hFbd, hcard, hno_disc⟩ := hI_viol hsub_bd
    obtain ⟨Δ, hΔ, hF_bd, hbd_sub, hΔ_N, hΔ_card⟩ :=
      theorem_8_3_proof h𝒯 π htrue hred hwarp hθ hL hnorm hFbd hcard
    exact hno_disc Δ hΔ hF_bd hbd_sub ⟨hΔ_N, hΔ_card⟩
  have hcl_eq : closure c ∩ bd π.S = tilde c ∩ bd π.S :=
    Painting.closure_cell_inter_bd_eq_tilde_inter_bd hint
  have hcl_sub_tc : closure c ∩ bd π.S ⊆ tilde c := by
    rw [hcl_eq]; exact inter_subset_left
  have htc_fin : (tilde c).Finite := π.Γ.finite_tilde_cell hc
  have htc_le3 : (tilde c).ncard ≤ 3 := π.Γ.ncard_tilde_cell_le hc
  have htc_ge2 : 2 ≤ (tilde c).ncard := h82_card c hc
  have hcl_le_tc : (closure c ∩ bd π.S).ncard ≤ (tilde c).ncard :=
    ncard_le_ncard hcl_sub_tc htc_fin
  have hcl_lt_tc : (closure c ∩ bd π.S).ncard < (tilde c).ncard := by
    by_contra hge
    have heq : closure c ∩ bd π.S = tilde c :=
      eq_of_subset_of_ncard_le hcl_sub_tc (not_lt.mp hge) htc_fin
    exact hnot_sub_bd (heq ▸ inter_subset_right)
  refine ⟨by omega, fun hcl_eq2 => ⟨by omega, fun n₁ hn₁ n₂ hn₂ hne => ?_⟩⟩
  obtain ⟨F, hF_ends, hnorm, hFbd_ends, hFbd, hFN, hΔ_bd_ne⟩ := hI_pair n₁ hn₁ n₂ hn₂ hne
  have hL : IsLine F := by rcases hF_ends with ⟨f, _, _⟩; exact ⟨f⟩
  have hcard : (F ∩ π.Γ.N).ncard = 2 := by
    rw [hFN, ncard_pair hne]
  obtain ⟨Δ, hΔ, hF_bd, hbd_sub, hΔ_N, _⟩ :=
    theorem_8_3_proof h𝒯 π htrue hred hwarp hθ
      hL hnorm hFbd_ends hcard
  obtain ⟨⟨x, hx_Δ, hx_bd, hx_ne_pair⟩, hΔ_dich⟩ := hΔ_bd_ne Δ hΔ hF_bd hbd_sub
  have hx_not_N : x ∉ π.Γ.N := by
    intro hx_N
    have hx_FN : x ∈ F ∩ π.Γ.N := ⟨hΔ_N ⟨hx_Δ, hx_N⟩, hx_N⟩
    rw [hFN] at hx_FN
    exact hx_ne_pair hx_FN
  have hx_U : x ∈ π.Γ.U := π.Γ.bd_subset hx_bd
  have hx_diff : x ∈ π.Γ.U \ π.Γ.N := ⟨hx_U, hx_not_N⟩
  rw [← π.Γ.sUnion_cells] at hx_diff
  rcases mem_sUnion.mp hx_diff with ⟨c₀, hc₀_C, hx_c₀⟩
  have hc₀_bd : (c₀ ∩ bd π.S).Nonempty := ⟨x, hx_c₀, hx_bd⟩
  have hc₀_Δ : c₀ ⊆ Δ := hΔ_dich c₀ hc₀_C ⟨x, hx_c₀, hx_Δ⟩
  refine ⟨c₀, hc₀_C, hc₀_bd, ?_⟩
  have : T2Space π.S := π.isSurface.2.1
  have htc₀_sub : tilde c₀ ⊆ {n₁, n₂} := by
    intro x hx_tc₀
    have hx_Δ : x ∈ Δ := (isClosed_of_isClosedDisc hΔ).closure_subset_iff.mpr hc₀_Δ hx_tc₀.1
    have hx_N : x ∈ π.Γ.N := π.Γ.tilde_subset_N hc₀_C hx_tc₀
    have hx_F : x ∈ F := hΔ_N ⟨hx_Δ, hx_N⟩
    have hx_FN : x ∈ F ∩ π.Γ.N := ⟨hx_F, hx_N⟩
    rwa [hFN] at hx_FN
  obtain ⟨u, w, huw_ne, htilde_c₀, _, _, _, _⟩ := π.Γ.border_cell_exists_ends hc₀_C hc₀_bd
  have htc₀_card : (tilde c₀).ncard = 2 := by rw [htilde_c₀, ncard_pair huw_ne]
  have hpair_card : ({n₁, n₂} : Set π.S).ncard = 2 := ncard_pair hne
  exact eq_of_subset_of_ncard_le htc₀_sub (by omega) (by simp)

/-! ## 7. Inclusion of $\tilde{c}_1 \subseteq \tilde{c}_2$ for Distinct Cells: (8.8) (Page 183) -/

/-- Removing an internal cell $c_1 \in C(\Gamma)$ from $U(\Gamma)$ produces a painting
$\Gamma' = (U(\Gamma) \setminus c_1, N(\Gamma))$ with $C(\Gamma') = C(\Gamma) \setminus \{c_1\}$.
Graph Minors XVII, proof of (8.8) (page 183). -/
private noncomputable def Painting.removeInternalCell {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : Painting S) {c₁ : Set S} (hc₁ : c₁ ∈ Γ.C) (hint₁ : ¬ (c₁ ∩ bd S).Nonempty) :
    Painting S := by
  classical
  let U' : Set S := Γ.U \ c₁
  let I : Set (Set S) := Γ.C \ {c₁}
  have hI_fin : I.Finite := Γ.finite_cells.subset sdiff_subset
  have hcl_sub : ∀ c ∈ I, closure c ⊆ U' := by
    rintro c ⟨hc, hne⟩ x hxcl
    refine ⟨Γ.closure_cell_subset_U hc hxcl, fun hxc₁ => ?_⟩
    by_cases hxc : x ∈ c
    · exact Set.disjoint_left.mp (Γ.cell_disjoint hc hc₁ hne) hxc hxc₁
    · have hx_tc : x ∈ tilde c := ⟨hxcl, hxc⟩
      exact (Γ.cell_subset_diff hc₁ hxc₁).2 (Γ.tilde_subset_N hc hx_tc)
  have hU'_eq : U' = Γ.N ∪ ⋃ c ∈ I, closure c := by
    ext x
    simp only [U', I, mem_sdiff, mem_union, mem_iUnion]
    constructor
    · rintro ⟨hxU, hx_not_c₁⟩
      rw [Γ.U_eq_N_union_biUnion_closure] at hxU
      rcases hxU with hxN | hcl
      · exact Or.inl hxN
      · rw [mem_iUnion₂] at hcl
        rcases hcl with ⟨c, hc, hxcl⟩
        by_cases hcc₁ : c = c₁
        · subst hcc₁
          exact Or.inl (Γ.tilde_subset_N hc₁ ⟨hxcl, hx_not_c₁⟩)
        · exact Or.inr ⟨c, ⟨hc, hcc₁⟩, hxcl⟩
    · rintro (hxN | ⟨c, hcI, hxcl⟩)
      · exact ⟨Γ.N_subset hxN, fun hxc₁ => (Γ.cell_subset_diff hc₁ hxc₁).2 hxN⟩
      · exact hcl_sub c hcI hxcl
  have hU'_closed : IsClosed U' := by
    rw [hU'_eq]
    exact Γ.finite_N.isClosed.union (hI_fin.isClosed_biUnion fun _ _ => isClosed_closure)
  have hcov : ⋃₀ I = U' \ Γ.N := by
    ext x
    constructor
    · rintro ⟨c, ⟨hc, hne⟩, hxc⟩
      exact ⟨⟨Γ.cell_subset_U hc hxc,
        Set.disjoint_left.mp (Γ.cell_disjoint hc hc₁ hne) hxc⟩,
        (Γ.cell_subset_diff hc hxc).2⟩
    · rintro ⟨⟨hxU, hx_not_c₁⟩, hx_not_N⟩
      have hx_cells : x ∈ ⋃₀ Γ.C := Γ.sUnion_cells.symm ▸ ⟨hxU, hx_not_N⟩
      rcases hx_cells with ⟨c, hc, hxc⟩
      have hne : c ≠ c₁ := fun h => hx_not_c₁ (h ▸ hxc)
      exact ⟨c, ⟨hc, hne⟩, hxc⟩
  have hC'_eq : arcComponentsIn (U' \ Γ.N) = I := by
    apply arcComponentsIn_eq_of_finite_cover hI_fin hcov
    · exact fun c hcI => Γ.cell_nonempty hcI.1
    · exact fun c hcI => Γ.cell_isPathConnected hcI.1
    · exact fun c hc c' hc' hne => Γ.cell_disjoint hc.1 hc'.1 hne
    · intro c hcI
      refine Subset.antisymm ?_ (fun x hxc => ⟨subset_closure hxc, hcov ▸ ⟨c, hcI, hxc⟩⟩)
      rintro x ⟨hxcl, _, hx_not_N⟩
      rw [← Γ.closure_cell_diff_N hcI.1]
      exact ⟨hxcl, hx_not_N⟩
  exact
    { U := U'
      N := Γ.N
      isClosed_U := hU'_closed
      finite_N := Γ.finite_N
      N_subset := fun x hxN => ⟨Γ.N_subset hxN, fun hxc₁ => (Γ.cell_subset_diff hc₁ hxc₁).2 hxN⟩
      finite_cells := hC'_eq ▸ hI_fin
      cell_disc := fun c hc => Γ.cell_disc c ((hC'_eq ▸ hc).1)
      bd_subset := fun x hxbd => ⟨Γ.bd_subset hxbd, fun hxc₁ => hint₁ ⟨x, hxc₁, hxbd⟩⟩
      border_cell := fun c hc hbd => Γ.border_cell c ((hC'_eq ▸ hc).1) hbd }

private theorem Painting.removeInternalCell_C {S : Type} [TopologicalSpace S] [T2Space S]
    (Γ : Painting S) {c₁ : Set S} (hc₁ : c₁ ∈ Γ.C) (hint₁ : ¬ (c₁ ∩ bd S).Nonempty) :
    (Γ.removeInternalCell hc₁ hint₁).C = Γ.C \ {c₁} := by
  classical
  let U' : Set S := Γ.U \ c₁
  let I : Set (Set S) := Γ.C \ {c₁}
  have hI_fin : I.Finite := Γ.finite_cells.subset sdiff_subset
  have hcov : ⋃₀ I = U' \ Γ.N := by
    ext x
    constructor
    · rintro ⟨c, ⟨hc, hne⟩, hxc⟩
      exact ⟨⟨Γ.cell_subset_U hc hxc,
        Set.disjoint_left.mp (Γ.cell_disjoint hc hc₁ hne) hxc⟩,
        (Γ.cell_subset_diff hc hxc).2⟩
    · rintro ⟨⟨hxU, hx_not_c₁⟩, hx_not_N⟩
      have hx_cells : x ∈ ⋃₀ Γ.C := Γ.sUnion_cells.symm ▸ ⟨hxU, hx_not_N⟩
      rcases hx_cells with ⟨c, hc, hxc⟩
      have hne : c ≠ c₁ := fun h => hx_not_c₁ (h ▸ hxc)
      exact ⟨c, ⟨hc, hne⟩, hxc⟩
  apply arcComponentsIn_eq_of_finite_cover hI_fin hcov
  · exact fun c hcI => Γ.cell_nonempty hcI.1
  · exact fun c hcI => Γ.cell_isPathConnected hcI.1
  · exact fun c hc c' hc' hne => Γ.cell_disjoint hc.1 hc'.1 hne
  · intro c hcI
    refine Subset.antisymm ?_ (fun x hxc => ⟨subset_closure hxc, hcov ▸ ⟨c, hcI, hxc⟩⟩)
    rintro x ⟨hxcl, _, hx_not_N⟩
    rw [← Γ.closure_cell_diff_N hcI.1]
    exact ⟨hxcl, hx_not_N⟩

private theorem removing_internal_cell_makes_portrayal_truer
    {α : Type u} {β : Type v} {G : Hypergraph α β} {π π' : Portrayal G}
    {c₁ : Set π.S} (hc₁ : c₁ ∈ π.Γ.C) (hint₁ : ¬ (c₁ ∩ bd π.S).Nonempty)
    (htruth : ∀ i : Fin 6, i.val < 4 →
      π'.truth i = {c ∈ π.Γ.C \ {c₁} |
        ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - i.val}.ncard) :
    π'.IsTruer π := by
  have hcard_le3 : (tilde c₁).ncard ≤ 3 := π.Γ.ncard_tilde_cell_le hc₁
  let k₀ : Fin 6 := ⟨3 - (tilde c₁).ncard, by omega⟩
  have hk₀_lt4 : k₀.1 < 4 := by dsimp [k₀]; omega
  refine ⟨k₀, fun i hi => ?_, ?_⟩
  · have hi_lt : i.1 < 3 - (tilde c₁).ncard := hi
    have hi4 : i.1 < 4 := by omega
    rw [htruth i hi4]
    simp only [Portrayal.truth, hi4, ↓reduceIte]
    congr 1; ext d
    simp only [mem_sep_iff, mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨⟨hd, _⟩, h⟩ => ⟨hd, h⟩,
      fun ⟨hd, hint_d, hcard_d⟩ => ⟨⟨hd, fun hEq => by subst hEq; omega⟩, hint_d, hcard_d⟩⟩
  · rw [htruth k₀ hk₀_lt4]
    simp only [Portrayal.truth, hk₀_lt4, ↓reduceIte]
    have hssub : {c ∈ π.Γ.C \ {c₁} | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} ⊂
        {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} := by
      refine ⟨fun d hd => ⟨hd.1.1, hd.2⟩, fun h => ?_⟩
      have hc₁_mem : c₁ ∈ {c ∈ π.Γ.C | ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 - k₀.1} :=
        ⟨hc₁, hint₁, by dsimp [k₀]; omega⟩
      exact (h hc₁_mem).1.2 rfl
    exact ncard_lt_ncard hssub (π.Γ.finite_cells.subset fun _ h => h.1)

/-- If $c_1, c_2 \in C(\Gamma)$ are distinct internal cells with $\tilde{c}_1 \subseteq
\tilde{c}_2$,
merging $\alpha(c_1)$ into $\alpha(c_2)$ on the painting $\Gamma' = (U(\Gamma) \setminus c_1,
N(\Gamma))$
produces a $\mathcal{T}$-central portrayal $\pi'$ of $G$ resembling $\pi$ and truer than $\pi$.
Graph Minors XVII, proof of (8.8) (page 183). -/
private theorem exists_truer_of_internal_tilde_subset
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 3 < θ)
    (π : Portrayal G) (hcentral : π.IsCentral 𝒯)
    {c₁ c₂ : Set π.S} (hc₁ : c₁ ∈ π.Γ.C) (hc₂ : c₂ ∈ π.Γ.C) (hne₁₂ : c₁ ≠ c₂)
    (hint₁ : ¬ (c₁ ∩ bd π.S).Nonempty) (hint₂ : ¬ (c₂ ∩ bd π.S).Nonempty)
    (htilde_sub : tilde c₁ ⊆ tilde c₂) :
    ∃ π' : Portrayal G, π'.IsCentral 𝒯 ∧ π'.Resembles π ∧ π'.IsTruer π := by
  classical
  have : T2Space π.S := π.isSurface.2.1
  let Γ' : Painting π.S := π.Γ.removeInternalCell hc₁ hint₁
  have hC' : Γ'.C = π.Γ.C \ {c₁} := π.Γ.removeInternalCell_C hc₁ hint₁
  have hc₂_C' : c₂ ∈ Γ'.C := hC'.symm ▸ ⟨hc₂, hne₁₂.symm⟩
  let cellG : Set π.S → Hypergraph α β := fun c =>
    if c = c₂ then π.cellGraph c₁ ∪ π.cellGraph c₂ else π.cellGraph c
  have hcellG_le : ∀ c ∈ Γ'.C, cellG c ≤ G := by
    intro c hc
    dsimp only [cellG]
    split_ifs with hcc₂
    · exact union_le (π.cellGraph_le c₁ hc₁) (π.cellGraph_le c₂ hc₂)
    · exact π.cellGraph_le c (hC' ▸ hc).1
  let π' : Portrayal G :=
    { S := π.S
      top := π.top
      isSurface := π.isSurface
      connected := π.connected
      Γ := Γ'
      cellGraph := cellG
      borderSet := π.borderSet
      domγ := π.domγ
      nodeVertex := π.nodeVertex
      cellGraph_le := hcellG_le
      borderSet_subset := π.borderSet_subset
      domγ_subset := π.domγ_subset
      nodeVertex_mem := π.nodeVertex_mem
      nodeVertex_injOn := π.nodeVertex_injOn
      p1_vertex := fun v hv => by
        obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv
        by_cases hcc₁ : c = c₁
        · subst hcc₁
          refine ⟨c₂, hc₂_C', ?_⟩
          dsimp only [cellG]
          rw [ite_eq_left rfl]
          exact Or.inl hvc
        · refine ⟨c, hC'.symm ▸ ⟨hc, hcc₁⟩, ?_⟩
          dsimp only [cellG]
          split_ifs with hcc₂
          · subst hcc₂; exact Or.inr hvc
          · exact hvc
      p1_edge := fun e he => by
        obtain ⟨c, hc, hec⟩ := π.p1_edge e he
        by_cases hcc₁ : c = c₁
        · subst hcc₁
          refine ⟨c₂, hc₂_C', ?_⟩
          dsimp only [cellG]
          rw [ite_eq_left rfl]
          exact Or.inl hec
        · refine ⟨c, hC'.symm ▸ ⟨hc, hcc₁⟩, ?_⟩
          dsimp only [cellG]
          split_ifs with hcc₂
          · subst hcc₂; exact Or.inr hec
          · exact hec
      p1_disjoint := fun d₁ hd₁ d₂ hd₂ hne => by
        have hd₁_C : d₁ ∈ π.Γ.C \ {c₁} := hC' ▸ hd₁
        have hd₂_C : d₂ ∈ π.Γ.C \ {c₁} := hC' ▸ hd₂
        dsimp only [cellG]
        by_cases h1 : d₁ = c₂ <;> by_cases h2 : d₂ = c₂
        · exact False.elim (hne (h1.trans h2.symm))
        · rw [ite_eq_left h1, ite_eq_right h2]
          exact (π.p1_disjoint c₁ hc₁ d₂ hd₂_C.1 (Ne.symm hd₂_C.2)).union_left
            (π.p1_disjoint c₂ hc₂ d₂ hd₂_C.1 (h1 ▸ hne))
        · rw [ite_eq_right h1, ite_eq_left h2]
          exact (π.p1_disjoint d₁ hd₁_C.1 c₁ hc₁ hd₁_C.2).union_right
            (π.p1_disjoint d₁ hd₁_C.1 c₂ hc₂ (h2 ▸ hne))
        · rw [ite_eq_right h1, ite_eq_right h2]
          exact π.p1_disjoint d₁ hd₁_C.1 d₂ hd₂_C.1 hne
      p2 := fun c hc n hn => by
        have hc_C : c ∈ π.Γ.C := (hC' ▸ hc).1
        dsimp only [cellG]
        split_ifs with hcc₂
        · exact Or.inr (π.p2 c₂ hc₂ n (hcc₂ ▸ hn))
        · exact π.p2 c hc_C n hn
      p3_notMem := π.p3_notMem
      p3_subset := fun c hc hbd n hn => by
        have hc_C : c ∈ π.Γ.C := (hC' ▸ hc).1
        have hne_c₂ : c ≠ c₂ := fun h => hint₂ (h ▸ hbd)
        dsimp only [cellG]
        rw [ite_eq_right hne_c₂]
        exact π.p3_subset c hc_C hbd n hn
      p4_disjoint := π.p4_disjoint
      p4_notMem := π.p4_notMem
      p5 := fun c hc hint v hvc ⟨d, hd, hne, hvd⟩ => by
        have hc_C : c ∈ π.Γ.C \ {c₁} := hC' ▸ hc
        have hd_C : d ∈ π.Γ.C \ {c₁} := hC' ▸ hd
        have hc_ne₁ : c₁ ≠ c := fun h => hc_C.2 (Set.mem_singleton_iff.mpr h.symm)
        have hd_ne₁ : d ≠ c₁ := fun h => hd_C.2 (Set.mem_singleton_iff.mpr h)
        dsimp only [cellG] at hvc hvd
        by_cases hcc₂ : c = c₂
        · rw [ite_eq_left hcc₂] at hvc
          have hdc₂ : d ≠ c₂ := hcc₂ ▸ hne
          rw [ite_eq_right hdc₂] at hvd
          rw [hcc₂]
          rcases hvc with hvc₁ | hvc₂
          · obtain ⟨n, ⟨hn_tc₁, hn_dom⟩, rfl⟩ :=
              π.p5 c₁ hc₁ hint₁ v hvc₁ ⟨d, hd_C.1, hd_ne₁, hvd⟩
            exact ⟨n, ⟨htilde_sub hn_tc₁, hn_dom⟩, rfl⟩
          · exact π.p5 c₂ hc₂ hint₂ v hvc₂ ⟨d, hd_C.1, hdc₂, hvd⟩
        · rw [ite_eq_right hcc₂] at hvc
          split_ifs at hvd with hdc₂
          · rcases hvd with hvc₁ | hvc₂
            · exact π.p5 c hc_C.1 hint v hvc ⟨c₁, hc₁, hc_ne₁, hvc₁⟩
            · exact π.p5 c hc_C.1 hint v hvc ⟨c₂, hc₂, Ne.symm hcc₂, hvc₂⟩
          · exact π.p5 c hc_C.1 hint v hvc ⟨d, hd_C.1, hne, hvd⟩
      p6 := fun c hc hbd v hvc ⟨d, hd, hne, hvd⟩ => by
        have hc_C : c ∈ π.Γ.C \ {c₁} := hC' ▸ hc
        have hd_C : d ∈ π.Γ.C \ {c₁} := hC' ▸ hd
        have hc_ne₁ : c₁ ≠ c := fun h => hc_C.2 (Set.mem_singleton_iff.mpr h.symm)
        have hcc₂ : c ≠ c₂ := fun h => hint₂ (h ▸ hbd)
        dsimp only [cellG] at hvc hvd
        rw [ite_eq_right hcc₂] at hvc
        split_ifs at hvd with hdc₂
        · rcases hvd with hvc₁ | hvc₂
          · exact π.p6 c hc_C.1 hbd v hvc ⟨c₁, hc₁, hc_ne₁, hvc₁⟩
          · exact π.p6 c hc_C.1 hbd v hvc ⟨c₂, hc₂, Ne.symm hcc₂, hvc₂⟩
        · exact π.p6 c hc_C.1 hbd v hvc ⟨d, hd_C.1, hne, hvd⟩
      p7 := π.p7 }
  have hπ'_central : π'.IsCentral 𝒯 := by
    intro c hc
    have hc_C : c ∈ π.Γ.C := (hC' ▸ hc).1
    change IsSmallWrt 𝒯 (cellG c)
    dsimp only [cellG]
    split_ifs with hcc₂
    · have hatt_sub : attachments G (π.cellGraph c₁ ∪ π.cellGraph c₂) ⊆
          π.nodeVertex '' (tilde c₂ ∩ π.domγ) := by
        rintro v ⟨hv_union, e, ⟨heG, he_not⟩, hinc⟩
        obtain ⟨d, hd_C, hed⟩ := π.p1_edge e heG
        have hd_ne₁ : d ≠ c₁ := fun h => he_not (Or.inl (h ▸ hed))
        have hd_ne₂ : d ≠ c₂ := fun h => he_not (Or.inr (h ▸ hed))
        have hvd : v ∈ (π.cellGraph d).vertexSet := by
          have hends := (π.cellGraph_le d hd_C).3 e hed
          exact (π.cellGraph d).vertex_mem_of_inc
            (by change v ∈ (π.cellGraph d).ends e; rw [← hends]; exact hinc)
        rcases hv_union with hvc₁ | hvc₂
        · obtain ⟨n, ⟨hn_tc₁, hn_dom⟩, rfl⟩ :=
            π.p5 c₁ hc₁ hint₁ v hvc₁ ⟨d, hd_C, hd_ne₁, hvd⟩
          exact ⟨n, ⟨htilde_sub hn_tc₁, hn_dom⟩, rfl⟩
        · exact π.p5 c₂ hc₂ hint₂ v hvc₂ ⟨d, hd_C, hd_ne₂, hvd⟩
      have hfin_tc₂ : (tilde c₂).Finite := π.Γ.finite_tilde_cell hc₂
      have hfin_dom : (tilde c₂ ∩ π.domγ).Finite := hfin_tc₂.inter_of_left _
      have hatt_lt : (attachments G (π.cellGraph c₁ ∪ π.cellGraph c₂)).ncard < θ := by
        have hle1 := ncard_le_ncard hatt_sub (hfin_dom.image π.nodeVertex)
        have hle2 := ncard_image_le (f := π.nodeVertex) hfin_dom
        have hle3 : (tilde c₂ ∩ π.domγ).ncard ≤ (tilde c₂).ncard :=
          ncard_le_ncard inter_subset_left hfin_tc₂
        have hle4 : (tilde c₂).ncard ≤ 3 := π.Γ.ncard_tilde_cell_le hc₂
        omega
      exact IsSmallWrt.union h𝒯 (hcentral c₁ hc₁) (hcentral c₂ hc₂) hatt_lt
    · exact hcentral c hc_C
  have hπ'_res : π'.Resembles π := by
    refine ⟨Homeomorph.refl π.S, fun Θ hΘ => ?_⟩
    rw [Homeomorph.refl_apply, image_id]
    have hΘ_bd : Θ ⊆ bd π.S := by
      rcases hΘ with ⟨x₀, _, rfl⟩
      exact connectedComponentIn_subset (bd π.S) x₀
    have hcw_eq : ∀ c ∈ π.Γ.C, (c ∩ Θ).Nonempty → π'.cellWarp c = π.cellWarp c := by
      intro c _ hcΘ
      have hbd_c : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
      have hcc₂ : c ≠ c₂ := fun h => hint₂ (h ▸ hbd_c)
      change sInf {q | π'.CellWarpLE c q} = sInf {q | π.CellWarpLE c q}
      congr 1; ext q
      change (∀ n₁ ∈ tilde c, ∀ n₂ ∈ tilde c, n₁ ≠ n₂ →
          (π.borderSet n₁).ncard ≤ q ∧ (π.borderSet n₂).ncard ≤ q ∧
          ((π.borderPlus n₁).ncard = q + 1 → (π.borderPlus n₂).ncard = q + 1 →
            Portrayal.LinkagePairs (cellG c).skeleton (π.borderPlus n₁) (π.borderPlus n₂)
              (q + 1) (π.nodeVertex n₁) (π.nodeVertex n₂))) ↔ _
      dsimp only [cellG]
      rw [ite_eq_right hcc₂]
      rfl
    change sSup {p | ∃ c ∈ Γ'.C, (c ∩ Θ).Nonempty ∧ p = π'.cellWarp c} =
      sSup {p | ∃ c ∈ π.Γ.C, (c ∩ Θ).Nonempty ∧ p = π.cellWarp c}
    congr 1; ext q
    constructor
    · rintro ⟨c, hc', hcΘ, rfl⟩
      have hc_C : c ∈ π.Γ.C := (hC' ▸ hc').1
      exact ⟨c, hc_C, hcΘ, hcw_eq c hc_C hcΘ⟩
    · rintro ⟨c, hc_C, hcΘ, rfl⟩
      have hbd_c : (c ∩ bd π.S).Nonempty := hcΘ.mono (inter_subset_inter_right _ hΘ_bd)
      have hcc₁ : c ≠ c₁ := fun h => hint₁ (h ▸ hbd_c)
      exact ⟨c, hC'.symm ▸ ⟨hc_C, hcc₁⟩, hcΘ, (hcw_eq c hc_C hcΘ).symm⟩
  have hmerged_truer : π'.IsTruer π := by
    refine removing_internal_cell_makes_portrayal_truer hc₁ hint₁ ?_
    intro i hi
    simp only [Portrayal.truth, π', hi, ↓reduceIte, hC']
  exact ⟨π', hπ'_central, hπ'_res, hmerged_truer⟩

/-- **Graph Minors XVII, (8.8)** (page 183):
"If $c_1, c_2$ are distinct cells with $\tilde{c}_1 \subseteq \tilde{c}_2$, then $c_1$ is a
border cell, and $|\tilde{c}_2| = 3$." -/
theorem theorem_8_8_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {c₁ c₂ : Set π.S} (hc₁ : c₁ ∈ π.Γ.C) (hc₂ : c₂ ∈ π.Γ.C) (hne : c₁ ≠ c₂)
    (htilde_sub : tilde c₁ ⊆ tilde c₂) :
    (c₁ ∩ bd π.S).Nonempty ∧ (tilde c₂).ncard = 3 := by
  have : T2Space π.S := π.isSurface.2.1
  obtain ⟨-, h82_card, -, -, -, hBdInj, -⟩ :=
    region_boundary_props h𝒯 π htrue hred hwarp hθ
  -- First show `c₁` is a border cell.
  have hbd₁ : (c₁ ∩ bd π.S).Nonempty := by
    by_contra hint₁
    -- If `c₂` is a border cell, `tilde c₁ = tilde c₂ ⊆ bd π.S` and `(tilde c₁).ncard = 2`,
    -- violating `(8.6)`.
    have hint₂ : ¬ (c₂ ∩ bd π.S).Nonempty := by
      intro hbd₂
      obtain ⟨u, w, huw_ne, htilde_c₂, _, _, hu_bd, hw_bd⟩ :=
        π.Γ.border_cell_exists_ends hc₂ hbd₂
      have hcard₂ : (tilde c₂).ncard = 2 := by rw [htilde_c₂, ncard_pair huw_ne]
      have hcard₁_ge2 : 2 ≤ (tilde c₁).ncard := h82_card c₁ hc₁
      have htc₁_eq : tilde c₁ = tilde c₂ :=
        eq_of_subset_of_ncard_le htilde_sub (by omega) (π.Γ.finite_tilde_cell hc₂)
      have htc₁_bd : tilde c₁ ⊆ bd π.S := by
        rw [htc₁_eq, htilde_c₂]
        rintro x (rfl | rfl) <;> [exact hu_bd.2; exact hw_bd.2]
      have hcl₁_bd : closure c₁ ∩ bd π.S = tilde c₁ := by
        rw [Painting.closure_cell_inter_bd_eq_tilde_inter_bd hint₁]
        exact inter_eq_left.mpr htc₁_bd
      have hcl₁_card : (closure c₁ ∩ bd π.S).ncard = 2 := by
        rw [hcl₁_bd, htc₁_eq, hcard₂]
      have h86 := (theorem_8_6_proof
        h𝒯 π htrue hred hwarp hθ hc₁ hint₁).2 hcl₁_card
      have hcard₁_eq3 : (tilde c₁).ncard = 3 := h86.1
      rw [htc₁_eq, hcard₂] at hcard₁_eq3
      omega
    -- Both `c₁` and `c₂` are internal cells, so merging `c₁` into `c₂` gives a truer portrayal.
    obtain ⟨π', hπ'_central, hπ'_res, hπ'_truer⟩ :=
      exists_truer_of_internal_tilde_subset h𝒯 (by omega) π htrue.1 hc₁ hc₂ hne hint₁ hint₂
        htilde_sub
    exact htrue.2.2 π' hπ'_central hπ'_truer hπ'_res
  refine ⟨hbd₁, ?_⟩
  -- Since `c₁` is a border cell, `tilde c₁ = {n₁, n₂} ⊆ bd π.S`.
  obtain ⟨n₁, n₂, hn_ne, htilde_c₁, _, _, hn₁_bd, hn₂_bd⟩ :=
    π.Γ.border_cell_exists_ends hc₁ hbd₁
  have hpair_bd : ({n₁, n₂} : Set π.S) ⊆ bd π.S := by
    rintro x (rfl | rfl) <;> [exact hn₁_bd.2; exact hn₂_bd.2]
  -- `c₂` cannot be a border cell, since otherwise `tilde c₁ = tilde c₂`, contradicting `(8.5)`.
  have hint₂ : ¬ (c₂ ∩ bd π.S).Nonempty := by
    intro hbd₂
    obtain ⟨u, w, huw_ne, htilde_c₂, _, _, _, _⟩ := π.Γ.border_cell_exists_ends hc₂ hbd₂
    have hcard₁ : (tilde c₁).ncard = 2 := by rw [htilde_c₁, ncard_pair hn_ne]
    have hcard₂ : (tilde c₂).ncard = 2 := by rw [htilde_c₂, ncard_pair huw_ne]
    have htc_eq : tilde c₁ = tilde c₂ :=
      eq_of_subset_of_ncard_le htilde_sub (by omega) (π.Γ.finite_tilde_cell hc₂)
    obtain ⟨F, hO, hnorm, hcardF, hno_disc⟩ := hBdInj c₁ hc₁ c₂ hc₂ hne hbd₁ hbd₂ htc_eq
    obtain ⟨Δ, hΔ, hbd, _, ⟨hΔ_N, _⟩ | ⟨hcard3, _⟩⟩ :=
      theorem_8_5_proof h𝒯 π htrue hred hwarp hθ hO hnorm (by omega)
    · exact hno_disc Δ hΔ hbd hΔ_N
    · omega
  -- Since `c₂` is internal and `{n₁, n₂} ⊆ closure c₂ ∩ bd π.S`, `(8.6)` gives `(tilde c₂).ncard =
  -- 3`.
  have hpair_sub_cl₂ : ({n₁, n₂} : Set π.S) ⊆ closure c₂ ∩ bd π.S := by
    rw [Painting.closure_cell_inter_bd_eq_tilde_inter_bd hint₂]
    exact subset_inter (htilde_c₁ ▸ htilde_sub) hpair_bd
  have hcl₂_fin : (closure c₂ ∩ bd π.S).Finite := by
    rw [Painting.closure_cell_inter_bd_eq_tilde_inter_bd hint₂]
    exact (π.Γ.finite_tilde_cell hc₂).inter_of_left _
  have hcl₂_ge2 : 2 ≤ (closure c₂ ∩ bd π.S).ncard := by
    rw [← ncard_pair hn_ne]
    exact ncard_le_ncard hpair_sub_cl₂ hcl₂_fin
  have h86 := theorem_8_6_proof
    h𝒯 π htrue hred hwarp hθ hc₂ hint₂
  have hcl₂_le2 : (closure c₂ ∩ bd π.S).ncard ≤ 2 := h86.1
  exact (h86.2 (le_antisymm hcl₂_le2 hcl₂_ge2)).1

/-- By (8.8), every internal cell $c \in C(\Gamma)$ belongs to $C^*(\Gamma)$. -/
theorem internal_cell_mem_CStar
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {c : Set π.S} (hc : c ∈ π.Γ.C) (hint : ¬ (c ∩ bd π.S).Nonempty) :
    c ∈ π.Γ.CStar := by
  refine ⟨hc, ?_⟩
  rintro ⟨c', hc', hne, hsub⟩
  have h88 := theorem_8_8_proof
    h𝒯 π htrue hred hwarp hθ hc hc' hne.symm hsub
  exact hint h88.1

/-- By (8.8), for every cell $c \in C(\Gamma)$, there exists $c' \in C^*(\Gamma)$ with
$\tilde{c} \subseteq \tilde{c}'$. -/
theorem exists_mem_CStar_tilde_subset
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {c : Set π.S} (hc : c ∈ π.Γ.C) :
    ∃ c' ∈ π.Γ.CStar, tilde c ⊆ tilde c' := by
  have : T2Space π.S := π.isSurface.2.1
  by_cases hc_star : c ∈ π.Γ.CStar
  · exact ⟨c, hc_star, Subset.rfl⟩
  · have hex : ∃ c' ∈ π.Γ.C, c' ≠ c ∧ tilde c ⊆ tilde c' := by
      by_contra hno
      exact hc_star ⟨hc, hno⟩
    rcases hex with ⟨c', hc', hne, hsub⟩
    have h88 := theorem_8_8_proof
      h𝒯 π htrue hred hwarp hθ hc hc' hne.symm hsub
    have hint_c' : ¬ (c' ∩ bd π.S).Nonempty := by
      intro hbd'
      obtain ⟨u, w, huw_ne, htilde_c', _, _, _, _⟩ := π.Γ.border_cell_exists_ends hc' hbd'
      have hcard2 : (tilde c').ncard = 2 := by rw [htilde_c', ncard_pair huw_ne]
      have hcard3 := h88.2
      omega
    exact ⟨c', internal_cell_mem_CStar h𝒯 π htrue hred hwarp hθ hc' hint_c', hsub⟩

/-! ## 8. Cells in $C^*(\Gamma)$ Incident with a Node: (8.7) (Pages 182–183) -/

/-- **Graph Minors XVII, (8.7)** (page 182):
"For every node $n$ there are at least two cells $c \in C^*(\Gamma)$ with $n \in \tilde{c}$, and
if there are only two and $|\tilde{c}| = 2$ for one of them, then $c$ is a border cell." -/
theorem theorem_8_7_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {n : π.S} (hn : n ∈ π.Γ.N) :
    2 ≤ {c ∈ π.Γ.CStar | n ∈ tilde c}.ncard ∧
    ({c ∈ π.Γ.CStar | n ∈ tilde c}.ncard = 2 →
      ∀ c ∈ π.Γ.CStar, n ∈ tilde c → (tilde c).ncard = 2 → (c ∩ bd π.S).Nonempty) := by
  have : T2Space π.S := π.isSurface.2.1
  obtain ⟨-, -, -, -, -, -, hIntNode⟩ :=
    region_boundary_props h𝒯 π htrue hred hwarp hθ
  have hfinite : π.Γ.CStar.Finite := π.Γ.finite_cells.subset fun _ h => h.1
  have hstar_fin : {c ∈ π.Γ.CStar | n ∈ tilde c}.Finite := hfinite.subset fun _ h => h.1
  by_cases hn_bd : n ∈ bd π.S
  · -- Case 1: `n` is a border node on some cuff `Θ`.
    let Θ := connectedComponentIn (bd π.S) n
    have hΘ : Θ ∈ cuffs π.S := ⟨n, hn_bd, rfl⟩
    have hΘ_arc : IsOArc Θ := (GraphMinor.Surface.cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
    set k := (π.Γ.N ∩ Θ).ncard
    obtain ⟨E⟩ : Nonempty (π.Γ.CuffEnumeration Θ k) := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
    have hn_Θ : n ∈ π.Γ.N ∩ Θ := ⟨hn, mem_connectedComponentIn hn_bd⟩
    rw [← E.range_node] at hn_Θ
    rcases hn_Θ with ⟨i, hi_eq⟩
    rw [← hi_eq] at hstar_fin ⊢
    have hk : 2 ≤ k := E.two_le
    have hk_pos : 0 < k := by omega
    let j : Fin k := cyclicPred hk_pos i
    have hij_ne : i ≠ j := by
      intro hEq
      have hval : i.1 = (i.1 + k - 1) % k := congrArg Fin.val hEq
      have hi_lt : i.1 < k := i.2
      by_cases hi0 : i.1 = 0
      · rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hval
        omega
      · have hmod : (i.1 + k - 1) % k = i.1 - 1 := by
          rw [show i.1 + k - 1 = (i.1 - 1) + k by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        omega
    let b₁ := E.cell i
    let b₂ := E.cell j
    have hb₁_ne_b₂ : b₁ ≠ b₂ := fun h => hij_ne (E.injective_cell h)
    have hb₁_mem : b₁ ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact ⟨i, rfl⟩
    have hb₂_mem : b₂ ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := by
      rw [← E.range_cell]; exact ⟨j, rfl⟩
    have hΘ_sub_bd : Θ ⊆ bd π.S := connectedComponentIn_subset (bd π.S) n
    have hb₁_bd : (b₁ ∩ bd π.S).Nonempty := hb₁_mem.2.mono (inter_subset_inter_right _ hΘ_sub_bd)
    have hb₂_bd : (b₂ ∩ bd π.S).Nonempty := hb₂_mem.2.mono (inter_subset_inter_right _ hΘ_sub_bd)
    have hn_b₁ : E.node i ∈ tilde b₁ := by
      rw [E.cell_tilde i]; exact Or.inl rfl
    have hj_succ : (⟨(j.1 + 1) % k, Nat.mod_lt _ hk_pos⟩ : Fin k) = i := by
      apply Fin.ext
      dsimp [j, cyclicPred]
      have hi_lt : i.1 < k := i.2
      by_cases hi0 : i.1 = 0
      · simp [hi0, Nat.sub_add_cancel hk_pos]
      · have hmod : (i.1 + k - 1) % k = i.1 - 1 := by
          rw [show i.1 + k - 1 = (i.1 - 1) + k by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        rw [hmod, Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hi_lt]
    have hn_b₂ : E.node i ∈ tilde b₂ := by
      rw [E.cell_tilde j, hj_succ]; exact Or.inr rfl
    obtain ⟨c₁, hc₁_star, hsub₁⟩ :=
      exists_mem_CStar_tilde_subset
        h𝒯 π htrue hred hwarp hθ hb₁_mem.1
    obtain ⟨c₂, hc₂_star, hsub₂⟩ :=
      exists_mem_CStar_tilde_subset
        h𝒯 π htrue hred hwarp hθ hb₂_mem.1
    have hc₁_ne_c₂ : c₁ ≠ c₂ := by
      intro hEq
      subst hEq
      let i' : Fin k := ⟨(i.1 + 1) % k, Nat.mod_lt _ hk_pos⟩
      have hi'_ne_i : i' ≠ i := by
        intro h
        have hval : (i.1 + 1) % k = i.1 := congrArg Fin.val h
        have hi_lt : i.1 < k := i.2
        by_cases hlast : i.1 + 1 = k
        · rw [hlast, Nat.mod_self] at hval; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega
      have hi'_ne_j : i' ≠ j := by
        intro h
        have htb_eq : tilde b₁ = tilde b₂ := by
          rw [E.cell_tilde i, E.cell_tilde j, hj_succ]
          change ({E.node i, E.node i'} : Set π.S) = {E.node j, E.node i}
          rw [h, Set.pair_comm]
        have h88 := theorem_8_8_proof
          h𝒯 π htrue hred hwarp hθ hb₁_mem.1 hb₂_mem.1 hb₁_ne_b₂ htb_eq.subset
        obtain ⟨u, w, huw_ne, htilde_b₂, _, _, _, _⟩ := π.Γ.border_cell_exists_ends hb₂_mem.1 hb₂_bd
        have hcard2 : (tilde b₂).ncard = 2 := by rw [htilde_b₂, ncard_pair huw_ne]
        omega
      have h3_sub_tc₁ : ({E.node i, E.node i', E.node j} : Set π.S) ⊆ tilde c₁ := by
        rintro x (rfl | rfl | rfl)
        · exact hsub₁ hn_b₁
        · exact hsub₁ (by rw [E.cell_tilde i]; exact Or.inr rfl)
        · exact hsub₂ (by rw [E.cell_tilde j]; exact Or.inl rfl)
      have h3_sub_bd : ({E.node i, E.node i', E.node j} : Set π.S) ⊆ bd π.S := by
        have hnode_bd : ∀ m : Fin k, E.node m ∈ bd π.S := fun m => by
          have hm : E.node m ∈ π.Γ.N ∩ Θ := E.range_node ▸ ⟨m, rfl⟩
          exact hΘ_sub_bd hm.2
        rintro x (rfl | rfl | rfl) <;> exact hnode_bd _
      have h3_card : ({E.node i, E.node i', E.node j} : Set π.S).ncard = 3 := by
        rw [ncard_insert_of_notMem, ncard_pair ( E.injective_node.ne hi'_ne_j )]
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨E.injective_node.ne hi'_ne_i.symm, E.injective_node.ne hij_ne⟩
      have htc₁_ge3 : 3 ≤ (tilde c₁).ncard := by
        rw [← h3_card]
        exact ncard_le_ncard h3_sub_tc₁ (π.Γ.finite_tilde_cell hc₁_star.1)
      have hint_c₁ : ¬ (c₁ ∩ bd π.S).Nonempty := by
        intro hbd_c₁
        obtain ⟨u, w, huw_ne, htilde_c₁, _, _, _, _⟩ := π.Γ.border_cell_exists_ends hc₁_star.1
          hbd_c₁
        have hcard2 : (tilde c₁).ncard = 2 := by rw [htilde_c₁, ncard_pair huw_ne]
        omega
      have h3_sub_cl : ({E.node i, E.node i', E.node j} : Set π.S) ⊆ closure c₁ ∩ bd π.S := by
        rw [Painting.closure_cell_inter_bd_eq_tilde_inter_bd hint_c₁]
        exact subset_inter h3_sub_tc₁ h3_sub_bd
      have hcl_fin : (closure c₁ ∩ bd π.S).Finite := by
        rw [Painting.closure_cell_inter_bd_eq_tilde_inter_bd hint_c₁]
        exact (π.Γ.finite_tilde_cell hc₁_star.1).inter_of_left _
      have hcl_ge3 : 3 ≤ (closure c₁ ∩ bd π.S).ncard := by
        rw [← h3_card]
        exact ncard_le_ncard h3_sub_cl hcl_fin
      have hcl_le2 := (theorem_8_6_proof
        h𝒯 π htrue hred hwarp hθ hc₁_star.1 hint_c₁).1
      omega
    have hpair_sub : ({c₁, c₂} : Set (Set π.S)) ⊆ {c ∈ π.Γ.CStar | E.node i ∈ tilde c} := by
      rintro c (rfl | rfl)
      · exact ⟨hc₁_star, hsub₁ hn_b₁⟩
      · exact ⟨hc₂_star, hsub₂ hn_b₂⟩
    have hge2 : 2 ≤ {c ∈ π.Γ.CStar | E.node i ∈ tilde c}.ncard := by
      rw [← ncard_pair hc₁_ne_c₂]
      exact ncard_le_ncard hpair_sub hstar_fin
    refine ⟨hge2, fun heq2 c hc_star hn_tc hcard_tc => ?_⟩
    have hset_eq : ({c₁, c₂} : Set (Set π.S)) = {d ∈ π.Γ.CStar | E.node i ∈ tilde d} :=
      eq_of_subset_of_ncard_le hpair_sub (by rw [heq2, ncard_pair hc₁_ne_c₂]) hstar_fin
    have hc_mem : c ∈ ({c₁, c₂} : Set (Set π.S)) := hset_eq.symm ▸ ⟨hc_star, hn_tc⟩
    rcases hc_mem with rfl | rfl
    · by_cases hcb₁ : c = b₁
      · exact hcb₁ ▸ hb₁_bd
      · have h88 := theorem_8_8_proof
          h𝒯 π htrue hred hwarp hθ hb₁_mem.1 hc_star.1 (Ne.symm hcb₁) hsub₁
        omega
    · by_cases hcb₂ : c = b₂
      · exact hcb₂ ▸ hb₂_bd
      · have h88 := theorem_8_8_proof
          h𝒯 π htrue hred hwarp hθ hb₂_mem.1 hc_star.1 (Ne.symm hcb₂) hsub₂
        omega
  · -- Case 2: `n` is an internal node (`n ∈ π.Γ.N \ bd π.S`).
    have hset_eq : {c ∈ π.Γ.CStar | n ∈ tilde c} = {c ∈ π.Γ.C | n ∈ tilde c} := by
      ext c
      simp only [mem_sep_iff]
      refine ⟨fun ⟨hc_star, hn_tc⟩ => ⟨hc_star.1, hn_tc⟩, fun ⟨hc_C, hn_tc⟩ => ⟨?_, hn_tc⟩⟩
      have hint_c : ¬ (c ∩ bd π.S).Nonempty := by
        intro hbd_c
        obtain ⟨u, w, _, htilde_c, _, _, hu_bd, hw_bd⟩ := π.Γ.border_cell_exists_ends hc_C hbd_c
        rcases (htilde_c ▸ hn_tc : n ∈ ({u, w} : Set π.S)) with rfl | rfl
        · exact hn_bd hu_bd.2
        · exact hn_bd hw_bd.2
      exact internal_cell_mem_CStar
        h𝒯 π htrue hred hwarp hθ hc_C hint_c
    rw [hset_eq]
    have hcontra : ¬ ({c ∈ π.Γ.C | n ∈ tilde c}.ncard ≤ 1 ∨
        ({c ∈ π.Γ.C | n ∈ tilde c}.ncard = 2 ∧
          ∃ c₀ ∈ π.Γ.C, n ∈ tilde c₀ ∧ (tilde c₀).ncard = 2)) := by
      intro hbad
      obtain ⟨F, hO, hnorm, hcardF, hF_disc⟩ := hIntNode n ⟨hn, hn_bd⟩ hbad
      obtain ⟨Δ, hΔ, hbd, ⟨B, hAB⟩, hcases⟩ :=
        theorem_8_5_proof h𝒯 π htrue hred hwarp hθ hO hnorm hcardF
      obtain ⟨d₁, hd₁_C, d₂, hd₂_C, hC_cov⟩ := hF_disc Δ hΔ hbd hcases
      obtain ⟨B₁, hB₁⟩ := htrue.1 d₁ hd₁_C
      obtain ⟨B₂, hB₂⟩ := htrue.1 d₂ hd₂_C
      apply h𝒯.axiom2 hB₁ hB₂ hAB
      have hU_le : π.cellGraph d₁ ∪ π.cellGraph d₂ ∪ π.areaGraph Δ ≤ G :=
        union_le (union_le (π.cellGraph_le d₁ hd₁_C) (π.cellGraph_le d₂ hd₂_C))
          (π.cellsUnion_le _)
      apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl
      · refine Subset.antisymm hU_le.vertexSet_subset fun v hv => ?_
        obtain ⟨c, hc_C, hvc⟩ := π.p1_vertex v hv
        rcases hC_cov hc_C with (rfl | rfl) | ⟨_, hc_Δ⟩
        · exact Or.inl (Or.inl hvc)
        · exact Or.inl (Or.inr hvc)
        · exact Or.inr (mem_iUnion₂.mpr ⟨c, ⟨⟨hc_C, hc_Δ⟩, hc_C⟩, hvc⟩)
      · refine Subset.antisymm hU_le.edgeSet_subset fun e he => ?_
        obtain ⟨c, hc_C, hec⟩ := π.p1_edge e he
        rcases hC_cov hc_C with (rfl | rfl) | ⟨_, hc_Δ⟩
        · exact Or.inl (Or.inl hec)
        · exact Or.inl (Or.inr hec)
        · exact Or.inr (mem_iUnion₂.mpr ⟨c, ⟨⟨hc_C, hc_Δ⟩, hc_C⟩, hec⟩)
    refine ⟨by omega, fun heq2 c hc_C hn_tc hcard2 => ?_⟩
    exact False.elim (hcontra (Or.inr ⟨heq2, c, hc_C.1, hn_tc, hcard2⟩))

end GraphMinor.GM17
