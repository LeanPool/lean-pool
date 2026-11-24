/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section9b
import LeanPool.GraphMinor.GM17.Section5Proved
import LeanPool.GraphMinor.GM17.Section6Proved
import LeanPool.GraphMinor.GM17.Section7Proved
import LeanPool.GraphMinor.GM17.Section8Proved
import LeanPool.GraphMinor.GM17.Section9Proved

public import LeanPool.GraphMinor.GM17.Section9
public import LeanPool.GraphMinor.GM17.ArcDisc
import LeanPool.GraphMinor.GM17.PasteCuff
import LeanPool.GraphMinor.GM17.MarkCross
import LeanPool.GraphMinor.GM17.ReplaceDisc
import LeanPool.GraphMinor.GM17.RegionDisc
import LeanPool.GraphMinor.GM17.CutArcPaint
import LeanPool.GraphMinor.GM17.PushNode

import LeanPool.GraphMinor.GM17.IndentMain

import LeanPool.GraphMinor.GM17.RegionBoundary

/-!
# Graph Minors XVII: proved deductions of Section9b

The portrayal deductions use the existing painting proofs. The definitions and
independent geometric lemmas are imported from `Section9b`.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology Metric
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

local notation "𝕀" => unitInterval

theorem indentedBorderPainting_props
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {Θ c₀ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hc₀ : c₀ ∈ π.Γ.C) (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ n₂ : π.S} (hne : n₁ ≠ n₂) (htc₀ : tilde c₀ = {n₁, n₂}) :
    ((¬ ∃ c ∈ π.Γ.C, ¬ (c ∩ bd π.S).Nonempty ∧ tilde c₀ ⊆ tilde c) →
      ∃ n₀ ∈ π.Γ.N \ bd π.S, ∃ Γ' : Painting π.S,
        IsIndentedBorderPainting π.Γ Θ c₀ n₁ n₂ n₀ {c₀} Γ') ∧
    (∀ c₃ ∈ π.Γ.C, ¬ (c₃ ∩ bd π.S).Nonempty → ∀ n₃ ∈ π.Γ.N \ bd π.S,
      tilde c₃ = {n₁, n₂, n₃} →
      ∃ Γ' : Painting π.S, IsIndentedBorderPainting π.Γ Θ c₀ n₁ n₂ n₃ {c₀, c₃} Γ') := by
  have : ConnectedSpace π.S := π.connected
  have hN_ge6 : 6 ≤ π.Γ.N.ncard := by
    have hge := (π.sub_two_mul_warp_le_ncard_domγ h𝒯 htrue.1 hwarp).2
    omega
  have h81 : ∀ r ∈ π.Γ.regions, IsOpenDisc r :=
    fun r hr => theorem_8_1_proof
      h𝒯 π htrue hred hwarp hθ hr
  obtain ⟨h82_1, h82_2, _⟩ :=
    theorem_8_2_proof
      h𝒯 π htrue hred hwarp hθ
  have h83 := fun (F : Set π.S) hL hnorm hFbd hcard =>
    theorem_8_3_proof h𝒯 π htrue hred hwarp hθ (F := F) hL hnorm hFbd hcard
  have h88 := fun (c₁ : Set π.S) hc₁ (c₂ : Set π.S) hc₂ hne_c hsub =>
    theorem_8_8_proof
      h𝒯 π htrue hred hwarp hθ (c₁ := c₁) (c₂ := c₂) hc₁ hc₂ hne_c hsub
  exact GraphMinor.GM17.indentedBorderPainting π.S π.isSurface π.Γ hN_ge6 h81 h82_1 h82_2 h83 h88 Θ
    hΘ c₀ hc₀ hc₀_Θ n₁ n₂ hne htc₀

private theorem decreased_warp_second_linkage
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    {n₂ : π.S}
    (hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (n₀ : π.S)
    (hn₀_not_c₀ : π.nodeVertex n₀ ∉ (π.cellGraph c₀).vertexSet)
    (A₁' : Hypergraph α β)
    (hn₀_mem_inter : π.nodeVertex n₀ ∈ A₁'.vertexSet ∩ (addVertexSubhypergraph A₂ (π.nodeVertex
      n₀)).vertexSet)
    (hinter_fin' : (A₁'.vertexSet ∩ (addVertexSubhypergraph A₂ (π.nodeVertex
      n₀)).vertexSet).Finite) :
    (π.borderPlus n₂).ncard = π.warpAt Θ + 1 → (A₁'.vertexSet ∩ (addVertexSubhypergraph A₂
      (π.nodeVertex n₀)).vertexSet).ncard = π.warpAt Θ + 1 → Portrayal.LinkagePairs
      (addVertexSubhypergraph A₂ (π.nodeVertex n₀)).skeleton (π.borderPlus n₂) (A₁'.vertexSet ∩
      (addVertexSubhypergraph A₂ (π.nodeVertex n₀)).vertexSet) (π.warpAt Θ + 1) (π.nodeVertex n₂)
      (π.nodeVertex n₀) := by
  let A₂' := addVertexSubhypergraph A₂ (π.nodeVertex n₀)
  intro _ hcard₂ P hdisj
  obtain ⟨i₀, hi₀_last⟩ := exists_last_eq_of_ncard_le hinter_fin' hcard₂.le P hdisj
    hn₀_mem_inter
  have hn₀_not_A₂ : π.nodeVertex n₀ ∉ A₂.vertexSet :=
    fun h => hn₀_not_c₀ (hsep.right_le.1 h)
  have hn₀_sup : π.nodeVertex n₀ ∈ (P i₀).walk.support :=
    (congrArg (fun z => z ∈ (P i₀).walk.support) hi₀_last).mp (P i₀).walk.end_mem_support
  obtain ⟨hfirst, _⟩ :=
    first_eq_last_of_mem_walk_not_mem_vertexSet A₂ hn₀_not_A₂ (P i₀).walk hn₀_sup
  exfalso
  apply hn₀_not_c₀
  apply hbp₂_sub
  rw [← hfirst]
  exact (P i₀).first_mem

private theorem edgeless_linkage_side_is_small
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (π : Portrayal G)
    {c₀ : Set π.S}
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (n₀ : π.S)
    (hsmall_aux : ∀ A ≤ π.cellGraph c₀, (∀ x ∈ A.vertexSet, (∃ e ∈ (π.cellGraph c₀).edgeSet \
      A.edgeSet, (π.cellGraph c₀).Inc e x) → x ∈ A₁.vertexSet ∩ A₂.vertexSet) → ∃ B,
      (addVertexSubhypergraph A (π.nodeVertex n₀), B) ∈ 𝒯) :
    ∃ B, (addVertexSubhypergraph A₁ (π.nodeVertex n₀), B) ∈ 𝒯 := by
  refine hsmall_aux A₁ hsep.left_le fun x hx₁ ⟨e, ⟨he₀, he_not₁⟩, hinc₀⟩ => ⟨hx₁, ?_⟩
  have he₂ : e ∈ A₂.edgeSet := (hsep.edgeSet_union ▸ he₀).resolve_left he_not₁
  have hinc₂ : A₂.Inc e x := (inc_iff_of_le hsep.right_le he₂).2 hinc₀
  exact A₂.vertex_mem_of_inc hinc₂

private theorem indented_cell_union_is_small
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (π : Portrayal G)
    {c₀ : Set π.S}
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (n₀ : π.S)
    (hsmall_aux : ∀ A ≤ π.cellGraph c₀, (∀ x ∈ A.vertexSet, (∃ e ∈ (π.cellGraph c₀).edgeSet \
      A.edgeSet, (π.cellGraph c₀).Inc e x) → x ∈ A₁.vertexSet ∩ A₂.vertexSet) → ∃ B,
      (addVertexSubhypergraph A (π.nodeVertex n₀), B) ∈ 𝒯) :
    ∃ B, ((addVertexSubhypergraph A₂ (π.nodeVertex n₀)), B) ∈ 𝒯 := by
  let A₂' := addVertexSubhypergraph A₂ (π.nodeVertex n₀)
  refine hsmall_aux A₂ hsep.right_le fun x hx₂ ⟨e, ⟨he₀, he_not₂⟩, hinc₀⟩ => ⟨?_, hx₂⟩
  have he₁ : e ∈ A₁.edgeSet := (hsep.edgeSet_union ▸ he₀).resolve_right he_not₂
  have hinc₁ : A₁.Inc e x := (inc_iff_of_le hsep.left_le he₁).2 hinc₀
  exact A₁.vertex_mem_of_inc hinc₁

private theorem cell_linkage_from_warp
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
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂)
    (hno_int : ¬∃ c ∈ π.Γ.C, ¬(c ∩ bd π.S).Nonempty ∧ tilde c₀ ⊆ tilde c)
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S)
    (hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S)
    (hbp₁_sub : π.borderPlus n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (hbs₁_le : (π.borderSet n₁).ncard ≤ π.warpAt Θ)
    (hbs₂_le : (π.borderSet n₂).ncard ≤ π.warpAt Θ)
    (hlinkage : (π.borderPlus n₁).ncard = π.warpAt Θ + 1 → (π.borderPlus n₂).ncard = π.warpAt Θ +
      1 → Portrayal.LinkagePairs (π.cellGraph c₀).skeleton (π.borderPlus n₁) (π.borderPlus n₂)
      (π.warpAt Θ + 1) (π.nodeVertex n₁) (π.nodeVertex n₂)) :
    HasDisjointPaths (π.cellGraph c₀).skeleton (π.borderPlus n₁) (π.borderPlus n₂) (π.warpAt Θ +
      1) := by
  rw [← GraphMinor.menger (π.cellGraph c₀) (π.borderPlus n₁) (π.borderPlus n₂) hbp₁_sub hbp₂_sub
    (π.warpAt Θ + 1)]
  intro A₁ A₂ hsep hbp₁ hbp₂
  by_contra hlt
  push Not at hlt
  have hsep_le : (A₁.vertexSet ∩ A₂.vertexSet).ncard ≤ π.warpAt Θ :=
    Nat.lt_succ_iff.mp hlt
  obtain ⟨n₀, hn₀, Γ', hind⟩ :=
    (indentedBorderPainting_props h𝒯 π htrue hred hwarp hθ
      hΘ hc₀ hc₀_Θ hne htc₀).1 hno_int
  obtain ⟨c_star, hc_star, hn₀_tc_star⟩ := hnode_cell n₀ hn₀.1
  have hn₀_in_c_star : π.nodeVertex n₀ ∈ (π.cellGraph c_star).vertexSet :=
    π.p2 c_star hc_star n₀ ⟨hn₀_tc_star, hdom ▸ hn₀.1⟩
  have hn₀_in_G : π.nodeVertex n₀ ∈ G.vertexSet :=
    (π.cellGraph_le c_star hc_star).1 hn₀_in_c_star
  have hn₀_not_c₀ : π.nodeVertex n₀ ∉ (π.cellGraph c₀).vertexSet := by
    rw [internal_nodeVertex_mem_cellGraph_iff π hdom hnode_cell hn₀ hc₀, htc₀]
    rintro (rfl | rfl)
    · exact hn₀.2 hn₁_bd.2
    · exact hn₀.2 hn₂_bd.2
  let A₁' := addVertexSubhypergraph A₁ (π.nodeVertex n₀)
  let A₂' := addVertexSubhypergraph A₂ (π.nodeVertex n₀)
  have hA₁_le_G : A₁ ≤ G := hsep.left_le.trans (π.cellGraph_le c₀ hc₀)
  have hA₂_le_G : A₂ ≤ G := hsep.right_le.trans (π.cellGraph_le c₀ hc₀)
  have hA₁'_le : A₁' ≤ G := addVertexSubhypergraph_le hA₁_le_G hn₀_in_G
  have hA₂'_le : A₂' ≤ G := addVertexSubhypergraph_le hA₂_le_G hn₀_in_G
  have hcells_c₀_V : (π.cellsUnion {c₀}).vertexSet = (π.cellGraph c₀).vertexSet := by
    ext x
    simp only [Portrayal.cellsUnion, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun ⟨c, ⟨hcEq, _⟩, hx⟩ => hcEq ▸ hx, fun hx => ⟨c₀, ⟨rfl, hc₀⟩, hx⟩⟩
  have hcells_c₀_E : (π.cellsUnion {c₀}).edgeSet = (π.cellGraph c₀).edgeSet := by
    ext e
    simp only [Portrayal.cellsUnion, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun ⟨c, ⟨hcEq, _⟩, he⟩ => hcEq ▸ he, fun he => ⟨c₀, ⟨rfl, hc₀⟩, he⟩⟩
  have hV_union : (π.cellsUnion {c₀}).vertexSet ⊆ A₁'.vertexSet ∪ A₂'.vertexSet := by
    rw [hcells_c₀_V, ← hsep.vertexSet_union]
    rintro x (hx₁ | hx₂)
    · exact Or.inl (Or.inl hx₁)
    · exact Or.inr (Or.inl hx₂)
  have hV_sub : A₁'.vertexSet ∪ A₂'.vertexSet ⊆
      (π.cellsUnion {c₀}).vertexSet ∪ {π.nodeVertex n₀} := by
    rw [hcells_c₀_V]
    rintro x ((hx₁ | rfl) | (hx₂ | rfl))
    · exact Or.inl (hsep.left_le.1 hx₁)
    · exact Or.inr rfl
    · exact Or.inl (hsep.right_le.1 hx₂)
    · exact Or.inr rfl
  have hE_union : A₁'.edgeSet ∪ A₂'.edgeSet = (π.cellsUnion {c₀}).edgeSet := by
    rw [hcells_c₀_E]
    exact hsep.edgeSet_union
  have hE_disj : Disjoint A₁'.edgeSet A₂'.edgeSet :=
    Set.disjoint_iff_inter_eq_empty.mpr hsep.edgeSet_inter_eq
  have hbp₁' : π.borderPlus n₁ ⊆ A₁'.vertexSet := fun x hx => Or.inl (hbp₁ hx)
  have hbp₂' : π.borderPlus n₂ ⊆ A₂'.vertexSet := fun x hx => Or.inl (hbp₂ hx)
  have hn₀_mem_inter : π.nodeVertex n₀ ∈ A₁'.vertexSet ∩ A₂'.vertexSet :=
    ⟨Or.inr rfl, Or.inr rfl⟩
  have hinter_sdiff : (A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n₀} =
      A₁.vertexSet ∩ A₂.vertexSet := by
    ext x
    simp only [A₁', A₂', addVertexSubhypergraph, mem_sdiff, mem_inter_iff, mem_union,
      mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx₁ | hEq₁, hx₂ | hEq₂⟩, hne₀⟩
      · exact ⟨hx₁, hx₂⟩
      · exact (hne₀ hEq₂).elim
      · exact (hne₀ hEq₁).elim
      · exact (hne₀ hEq₁).elim
    · rintro ⟨hx₁, hx₂⟩
      exact ⟨⟨Or.inl hx₁, Or.inl hx₂⟩, fun hEq => hn₀_not_c₀ (hEq ▸ hsep.left_le.1 hx₁)⟩
  have hbs_sub : (A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n₀} ⊆
      (π.cellGraph c₀).vertexSet := by
    rw [hinter_sdiff]
    exact inter_subset_left.trans hsep.left_le.1
  have hbs_star_le : ((A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n₀}).ncard ≤
      π.warpAt Θ := by
    rw [hinter_sdiff]
    exact hsep_le
  have hsmall_aux : ∀ A : Hypergraph α β, A ≤ π.cellGraph c₀ →
      (∀ x ∈ A.vertexSet, (∃ e ∈ (π.cellGraph c₀).edgeSet \ A.edgeSet,
        (π.cellGraph c₀).Inc e x) → x ∈ A₁.vertexSet ∩ A₂.vertexSet) →
      ∃ B, (addVertexSubhypergraph A (π.nodeVertex n₀), B) ∈ 𝒯 := by
    intro A hA_le hA_sep
    let A' := addVertexSubhypergraph A (π.nodeVertex n₀)
    have hle_union : A' ≤ π.cellGraph c₀ ∪ π.cellGraph c_star := by
      refine ⟨?_, hA_le.2.trans subset_union_left, fun e he => ?_⟩
      · rintro x (hxA | rfl)
        · exact Or.inl (hA_le.1 hxA)
        · exact Or.inr hn₀_in_c_star
      · ext x
        change (π.cellGraph c₀).Inc e x ∨ (π.cellGraph c_star).Inc e x ↔ A.Inc e x
        have he₀ : e ∈ (π.cellGraph c₀).edgeSet := hA_le.2 he
        have hinc₀ : (π.cellGraph c₀).Inc e x ↔ A.Inc e x := by
          have := congrArg (x ∈ ·) (hA_le.3 e he)
          exact this.to_iff
        refine ⟨fun h => h.elim hinc₀.mp (fun h_star => ?_), fun h => Or.inl (hinc₀.mpr h)⟩
        have he_star : e ∈ (π.cellGraph c_star).edgeSet :=
          (π.cellGraph c_star).edge_mem_of_inc h_star
        have hc₀_ne_star : c₀ ≠ c_star := fun hEq =>
          hn₀_not_c₀ (hEq ▸ hn₀_in_c_star)
        exact (Set.disjoint_left.mp (π.p1_disjoint c₀ hc₀ c_star hc_star hc₀_ne_star)
          he₀ he_star).elim
    have hatt_sub : attachments G A' ⊆
        (π.borderPlus n₁ ∪ π.borderPlus n₂) ∪ (A₁.vertexSet ∩ A₂.vertexSet) ∪
          {π.nodeVertex n₀} := by
      rintro x ⟨hxA | rfl, e, ⟨heG, he_not_A⟩, hinc⟩
      · by_cases he₀ : e ∈ (π.cellGraph c₀).edgeSet
        · have hinc₀ : (π.cellGraph c₀).Inc e x :=
            (inc_iff_of_le (π.cellGraph_le c₀ hc₀) he₀).2 hinc
          exact Or.inl (Or.inr (hA_sep x hxA ⟨e, ⟨he₀, he_not_A⟩, hinc₀⟩))
        · have hx_att₀ : x ∈ attachments G (π.cellGraph c₀) :=
            ⟨hA_le.1 hxA, e, ⟨heG, he₀⟩, hinc⟩
          have hx_ov := π.attachments_cellGraph_subset_otherVertices hc₀ hx_att₀
          rcases hx_ov.2 with ⟨d, hd, hdc₀, hxd⟩
          exact Or.inl (Or.inl (border_cell_vertex_mem_borderPlus_of_mem_other π
            hc₀ hbd₀ htc₀ hx_ov.1 hd hdc₀ hxd))
      · exact Or.inr rfl
    have hbp₁_fin : (π.borderPlus n₁).Finite :=
      (π.cellGraph c₀).vertexSet_finite.subset hbp₁_sub
    have hbp₂_fin : (π.borderPlus n₂).Finite :=
      (π.cellGraph c₀).vertexSet_finite.subset hbp₂_sub
    have hinter_fin : (A₁.vertexSet ∩ A₂.vertexSet).Finite :=
      A₁.vertexSet_finite.subset inter_subset_left
    have hfin_rhs : (((π.borderPlus n₁ ∪ π.borderPlus n₂) ∪
        (A₁.vertexSet ∩ A₂.vertexSet)) ∪ {π.nodeVertex n₀}).Finite :=
      ((hbp₁_fin.union hbp₂_fin).union hinter_fin).union (finite_singleton _)
    have hcard_att : (attachments G A').ncard < θ := by
      have h1 := ncard_le_ncard hatt_sub hfin_rhs
      have h2 := ncard_union_le ((π.borderPlus n₁ ∪ π.borderPlus n₂) ∪
        (A₁.vertexSet ∩ A₂.vertexSet)) {π.nodeVertex n₀}
      have h3 := ncard_union_le (π.borderPlus n₁ ∪ π.borderPlus n₂)
        (A₁.vertexSet ∩ A₂.vertexSet)
      have h4 := ncard_union_le (π.borderPlus n₁) (π.borderPlus n₂)
      have h5 := ncard_singleton (π.nodeVertex n₀)
      have hbp₁_c := ncard_borderPlus_le_warpAt_succ π hΘ hn₁_Θ
      have hbp₂_c := ncard_borderPlus_le_warpAt_succ π hΘ hn₂_Θ
      have hw_le : π.warpAt Θ ≤ p := (π.warpAt_le_warp hΘ).trans hwarp
      omega
    exact theorem_4_1_ii h𝒯 (htrue.1 c₀ hc₀) (htrue.1 c_star hc_star) hle_union hcard_att
  have hsmall₁ : ∃ B, (A₁', B) ∈ 𝒯 := by
    exact edgeless_linkage_side_is_small (α := α) (β := β) (G := G) (𝒯 := 𝒯) π (c₀ := c₀) A₁ A₂
      hsep n₀ hsmall_aux
  have hsmall₂ : ∃ B, (A₂', B) ∈ 𝒯 := by
    exact indented_cell_union_is_small (α := α) (β := β) (G := G) (𝒯 := 𝒯) π (c₀ := c₀) A₁ A₂ hsep
      n₀ hsmall_aux
  have hinter_fin' : (A₁'.vertexSet ∩ A₂'.vertexSet).Finite :=
    A₁'.vertexSet_finite.subset inter_subset_left
  have hlp₁ : (π.borderPlus n₁).ncard = π.warpAt Θ + 1 →
      (A₁'.vertexSet ∩ A₂'.vertexSet).ncard = π.warpAt Θ + 1 →
      Portrayal.LinkagePairs A₁'.skeleton (π.borderPlus n₁) (A₁'.vertexSet ∩ A₂'.vertexSet)
        (π.warpAt Θ + 1) (π.nodeVertex n₁) (π.nodeVertex n₀) := by
    intro _ hcard₂ P hdisj
    obtain ⟨i₀, hi₀_last⟩ := exists_last_eq_of_ncard_le hinter_fin' hcard₂.le P hdisj
      hn₀_mem_inter
    have hn₀_not_A₁ : π.nodeVertex n₀ ∉ A₁.vertexSet :=
      fun h => hn₀_not_c₀ (hsep.left_le.1 h)
    have hn₀_sup : π.nodeVertex n₀ ∈ (P i₀).walk.support :=
      hi₀_last ▸ (P i₀).walk.end_mem_support
    obtain ⟨hfirst, _⟩ :=
      first_eq_last_of_mem_walk_not_mem_vertexSet A₁ hn₀_not_A₁ (P i₀).walk hn₀_sup
    exfalso
    exact hn₀_not_c₀ (hbp₁_sub (hfirst ▸ (P i₀).first_mem))
  have hlp₂ : (π.borderPlus n₂).ncard = π.warpAt Θ + 1 →
      (A₁'.vertexSet ∩ A₂'.vertexSet).ncard = π.warpAt Θ + 1 →
      Portrayal.LinkagePairs A₂'.skeleton (π.borderPlus n₂) (A₁'.vertexSet ∩ A₂'.vertexSet)
        (π.warpAt Θ + 1) (π.nodeVertex n₂) (π.nodeVertex n₀) := by
    exact decreased_warp_second_linkage (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) (n₂ :=
      n₂) hbp₂_sub A₁ A₂ hsep n₀ hn₀_not_c₀ A₁' hn₀_mem_inter hinter_fin'
  exact not_indentedPortrayal π htrue hdom hnode_cell hΘ hc₀ hc₀_Θ hne htc₀ hn₀
    (mem_singleton c₀) (singleton_subset_iff.mpr hc₀) (fun c hc => Or.inl hc) hind
    hA₁'_le hA₂'_le hV_union hV_sub hE_union hE_disj hbp₁' hbp₂' hn₀_mem_inter
    hbs_sub hsmall₁ hsmall₂ hbs₁_le hbs₂_le hbs_star_le hlp₁ hlp₂

/-- **Graph Minors XVII, (9.3)** (page 184):
"Let $c_0$ be a cell bordering a cuff $\Theta$ with $\tilde{c}_0 = \{n_1, n_2\}$, and let
$\pi$ have warp $q$ at $\Theta$. Suppose that there is no internal cell $c$ with
$\tilde{c}_0 \subseteq \tilde{c}$. Then there are $q + 1$ mutually vertex-disjoint paths of
$\alpha(c_0)$ from $\beta(n_1 +)$ to $\beta(n_2 +)$, and in particular $|\beta(n_i)| = q$
$(i = 1, 2)$." -/
theorem theorem_9_3_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {Θ c₀ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hc₀ : c₀ ∈ π.Γ.C) (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ n₂ : π.S} (hn₁_tc : n₁ ∈ tilde c₀) (hn₂_tc : n₂ ∈ tilde c₀) (hne : n₁ ≠ n₂)
    (hno_int : ¬ ∃ c ∈ π.Γ.C, ¬ (c ∩ bd π.S).Nonempty ∧ tilde c₀ ⊆ tilde c) :
    HasDisjointPaths (π.cellGraph c₀).skeleton (π.borderPlus n₁) (π.borderPlus n₂)
      (π.warpAt Θ + 1) ∧
    (π.borderSet n₁).ncard = π.warpAt Θ ∧
    (π.borderSet n₂).ncard = π.warpAt Θ := by
  have : T2Space π.S := π.isSurface.2.1
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof
      h𝒯 π htrue hred hwarp hθ
  obtain ⟨_, _, hnode_cell⟩ :=
    theorem_8_2_proof
      h𝒯 π htrue hred hwarp hθ
  have hsub_cuff₀ := π.Γ.border_cell_subset_cuff hc₀ hΘ hc₀_Θ
  have hbd₀ : (c₀ ∩ bd π.S).Nonempty := hsub_cuff₀.2.1 ▸ hc₀_Θ
  obtain ⟨u₀, v₀, huv_ne, htc₀_uv, hL₀, hL₀_int, _, _⟩ := π.Γ.border_cell_exists_ends hc₀ hbd₀
  have htc₀ : tilde c₀ = {n₁, n₂} := by
    refine (eq_of_subset_of_ncard_le ?_ ?_ (π.Γ.finite_tilde_cell hc₀)).symm
    · rintro x (rfl | rfl) <;> assumption
    · rw [htc₀_uv, ncard_pair huv_ne, ncard_pair hne]
  have hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 hn₁_tc
  have hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 hn₂_tc
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S := ⟨hn₁_Θ.1, hΘ_bd hn₁_Θ.2⟩
  have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S := ⟨hn₂_Θ.1, hΘ_bd hn₂_Θ.2⟩
  have hbp₁_sub : π.borderPlus n₁ ⊆ (π.cellGraph c₀).vertexSet :=
    π.borderPlus_subset_cellGraph hc₀ hbd₀ hn₁_tc
  have hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet :=
    π.borderPlus_subset_cellGraph hc₀ hbd₀ hn₂_tc
  have hcw₀ : π.CellWarpLE c₀ (π.warpAt Θ) :=
    (π.cellWarp_le_iff hc₀ hbd₀).mp (π.cellWarp_le_warpAt hc₀ hc₀_Θ)
  obtain ⟨hbs₁_le, hbs₂_le, hlinkage⟩ := hcw₀ n₁ hn₁_tc n₂ hn₂_tc hne
  have hpaths : HasDisjointPaths (π.cellGraph c₀).skeleton (π.borderPlus n₁) (π.borderPlus n₂)
      (π.warpAt Θ + 1) := by
    exact cell_linkage_from_warp (α := α) (β := β) (G := G) (𝒯 := 𝒯) (θ := θ) (p := p) h𝒯 π htrue
      hred hwarp hθ (Θ := Θ) (c₀ := c₀) hΘ hc₀ hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne
      hno_int hdom hnode_cell hbd₀ htc₀ hn₁_Θ hn₂_Θ hn₁_bd hn₂_bd hbp₁_sub hbp₂_sub hbs₁_le
      hbs₂_le hlinkage
  refine ⟨hpaths, ?_, ?_⟩
  · rcases hpaths with ⟨P, hdisj⟩
    have hbp₁_fin : (π.borderPlus n₁).Finite :=
      (π.cellGraph c₀).vertexSet_finite.subset hbp₁_sub
    have hge := le_ncard_of_disjoint_paths_first hbp₁_fin P hdisj
    have hle := π.ncard_borderPlus_le hn₁_bd
    omega
  · rcases hpaths with ⟨P, hdisj⟩
    have hbp₂_fin : (π.borderPlus n₂).Finite :=
      (π.cellGraph c₀).vertexSet_finite.subset hbp₂_sub
    have hge := le_ncard_of_disjoint_paths_last hbp₂_fin P hdisj
    have hle := π.ncard_borderPlus_le hn₂_bd
    omega

private theorem linkage_crosses_to_third_node
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {n₁ : π.S}
    (hn₁ : n₁ ∈ π.Γ.N ∩ Θ)
    (hdom : π.domγ = π.Γ.N)
    (c₀ : Set π.S)
    (n₂ : π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (c₃ : Set π.S)
    (hc₃ : c₃ ∈ π.Γ.C)
    (hint₃ : ¬(c₃ ∩ bd π.S).Nonempty)
    (hc₀_ne_c₃ : c₀ ≠ c₃)
    (n₃ : π.S)
    (hn₁_ne_n₃ : n₁ ≠ n₃)
    (htc₃ : tilde c₃ = {n₁, n₂, n₃})
    (hn₃_N : n₃ ∈ π.Γ.N)
    (hbp₂_sub_c₀ : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₃_in_c₃ : π.nodeVertex n₃ ∈ (π.cellGraph c₃).vertexSet)
    (hn₃_not_c₀ : π.nodeVertex n₃ ∉ (π.cellGraph c₀).vertexSet)
    (hA₂'_eq : (π.cellsUnion {c₀, c₃}) = π.cellGraph c₀ ∪ π.cellGraph c₃)
    (A₁' : Hypergraph α β)
    (hinter_eq : A₁'.vertexSet ∩ (π.cellsUnion {c₀, c₃}).vertexSet = π.borderPlus n₁ ∪
      {π.nodeVertex n₃})
    (hn₃_mem_inter : π.nodeVertex n₃ ∈ A₁'.vertexSet ∩ (π.cellsUnion {c₀, c₃}).vertexSet)
    (hbp₂_fin : (π.borderPlus n₂).Finite)
    (hinter_fin' : (A₁'.vertexSet ∩ (π.cellsUnion {c₀, c₃}).vertexSet).Finite) :
    (π.borderPlus n₂).ncard = π.warpAt Θ + 1 → (A₁'.vertexSet ∩ (π.cellsUnion {c₀,
      c₃}).vertexSet).ncard = π.warpAt Θ + 1 → Portrayal.LinkagePairs (π.cellsUnion {c₀,
      c₃}).skeleton (π.borderPlus n₂) (A₁'.vertexSet ∩ (π.cellsUnion {c₀, c₃}).vertexSet)
      (π.warpAt Θ + 1) (π.nodeVertex n₂) (π.nodeVertex n₃) := by
  let A₂' := π.cellsUnion {c₀, c₃}
  intro hbp₂_eq hcard₂ P hdisj
  have hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁'.vertexSet ∩ A₂'.vertexSet :=
    hinter_eq ▸ Or.inl (Or.inr ⟨hdom ▸ hn₁.1, rfl⟩)
  have hn₂_mem_bp₂ : π.nodeVertex n₂ ∈ π.borderPlus n₂ :=
    Or.inr ⟨hdom ▸ hn₂_Θ.1, rfl⟩
  obtain ⟨i₀, hi₀_last⟩ := exists_last_eq_of_ncard_le hinter_fin' hcard₂.le P hdisj hn₃_mem_inter
  obtain ⟨i₁, hi₁_last⟩ := exists_last_eq_of_ncard_le hinter_fin' hcard₂.le P hdisj hn₁_mem_inter
  obtain ⟨i₂, hi₂_first⟩ := exists_first_eq_of_ncard_le hbp₂_fin hbp₂_eq.le P hdisj hn₂_mem_bp₂
  have hi₀_ne_i₁ : i₀ ≠ i₁ := by
    intro hEq
    have hv_eq : π.nodeVertex n₃ = π.nodeVertex n₁ :=
      hi₀_last.symm.trans (hEq ▸ hi₁_last)
    exact hn₁_ne_n₃ (π.nodeVertex_injOn (hdom ▸ hn₁.1) (hdom ▸ hn₃_N) hv_eq.symm)
  refine ⟨i₀, ?_, hi₀_last⟩
  by_contra hfirst_ne
  have hi₀_ne_i₂ : i₀ ≠ i₂ := fun hEq => hfirst_ne (hEq ▸ hi₂_first)
  have hsep_A₂' : A₂'.IsSeparation (π.cellGraph c₀) (π.cellGraph c₃) := by
    have hle₀ : π.cellGraph c₀ ≤ A₂' := by
      change _ ≤ π.cellsUnion {c₀, c₃}
      rw [hA₂'_eq]
      refine ⟨subset_union_left, subset_union_left, fun e he => ?_⟩
      ext x
      exact ⟨fun hx => hx.elim id (fun hx₃ => (Set.disjoint_left.mp
          (π.p1_disjoint c₀ hc₀ c₃ hc₃ hc₀_ne_c₃) he
          ((π.cellGraph c₃).edge_mem_of_inc hx₃)).elim),
        fun hx => Or.inl hx⟩
    have hle₃ : π.cellGraph c₃ ≤ A₂' := by
      change _ ≤ π.cellsUnion {c₀, c₃}
      rw [hA₂'_eq]
      refine ⟨subset_union_right, subset_union_right, fun e he => ?_⟩
      ext x
      exact ⟨fun hx => hx.elim (fun hx₀ => (Set.disjoint_left.mp
          (π.p1_disjoint c₀ hc₀ c₃ hc₃ hc₀_ne_c₃)
          ((π.cellGraph c₀).edge_mem_of_inc hx₀) he).elim) id,
        fun hx => Or.inr hx⟩
    exact ⟨hle₀, hle₃, hA₂'_eq.symm,
      Set.disjoint_iff_inter_eq_empty.mp (π.p1_disjoint c₀ hc₀ c₃ hc₃ hc₀_ne_c₃)⟩
  have hfirst_c₀ : (P i₀).first ∈ (π.cellGraph c₀).vertexSet :=
    hbp₂_sub_c₀ (P i₀).first_mem
  have hlast_c₃ : (P i₀).last ∈ (π.cellGraph c₃).vertexSet :=
    hi₀_last ▸ hn₃_in_c₃
  obtain ⟨z, hz_sup, hz_c₀, hz_c₃⟩ :=
    walk_meets_separation hsep_A₂' (P i₀).walk hfirst_c₀ hlast_c₃
  obtain ⟨m, ⟨hm_tc₃, _⟩, rfl⟩ :=
    π.p5 c₃ hc₃ hint₃ z hz_c₃ ⟨c₀, hc₀, hc₀_ne_c₃, hz_c₀⟩
  rw [htc₃] at hm_tc₃
  rcases hm_tc₃ with hEq | hEq | hEq
  · rw [hEq] at hz_sup
    have hz_i₁ : π.nodeVertex n₁ ∈ (P i₁).walk.support :=
      hi₁_last ▸ (P i₁).walk.end_mem_support
    exact Set.disjoint_left.mp (hdisj hi₀_ne_i₁) hz_sup hz_i₁
  · rw [hEq] at hz_sup
    have hz_i₂ : π.nodeVertex n₂ ∈ (P i₂).walk.support :=
      hi₂_first ▸ (P i₂).walk.start_mem_support
    exact Set.disjoint_left.mp (hdisj hi₀_ne_i₂) hz_sup hz_i₂
  · rw [hEq] at hz_c₀
    exact hn₃_not_c₀ hz_c₀

private theorem third_node_of_indented_cell_is_internal
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
    {Θ : Set π.S}
    {n₁ : π.S}
    (hn₁ : n₁ ∈ π.Γ.N ∩ Θ)
    (hbs₁_le : (π.borderSet n₁).ncard ≤ π.warpAt Θ)
    (hlt_bs₁ : (π.borderSet n₁).ncard < π.warpAt Θ)
    (k : ℕ)
    (E : π.Γ.CuffEnumeration Θ k)
    (idx : Fin k)
    (hidx_eq : E.node idx = n₁)
    (c₀ : Set π.S)
    (n₂ : π.S)
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hne₁₂ : n₁ ≠ n₂)
    (hn₁_tc₀ : n₁ ∈ tilde c₀)
    (hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S)
    (hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S)
    (c₃ : Set π.S)
    (hc₃ : c₃ ∈ π.Γ.C)
    (hint₃ : ¬(c₃ ∩ bd π.S).Nonempty)
    (hcard₃ : (tilde c₃).ncard = 3)
    (htc₃_fin : (tilde c₃).Finite)
    (n₃ : π.S)
    (hn₃_tc₃ : n₃ ∈ tilde c₃)
    (hn₃_not_pair : ¬n₃ = n₁ ∧ ¬n₃ = n₂)
    (hn₁_ne_n₃ : n₁ ≠ n₃)
    (hn₂_ne_n₃ : n₂ ≠ n₃)
    (htc₃ : tilde c₃ = {n₁, n₂, n₃})
    (hn₃_N : n₃ ∈ π.Γ.N) :
    n₃ ∉ bd π.S := by
  intro hn₃_bd
  have hsub_cl : ({n₁, n₂, n₃} : Set π.S) ⊆ closure c₃ ∩ bd π.S := by
    rw [Painting.closure_cell_inter_bd_eq_tilde_inter_bd hint₃, htc₃]
    rintro x (rfl | rfl | rfl)
    · exact ⟨Or.inl rfl, hn₁_bd.2⟩
    · exact ⟨Or.inr (Or.inl rfl), hn₂_bd.2⟩
    · exact ⟨Or.inr (Or.inr rfl), hn₃_bd⟩
  have hcl_fin : (closure c₃ ∩ bd π.S).Finite := by
    rw [Painting.closure_cell_inter_bd_eq_tilde_inter_bd hint₃]
    exact htc₃_fin.inter_of_left _
  have h3_card : ({n₁, n₂, n₃} : Set π.S).ncard = 3 := by rw [← htc₃, hcard₃]
  have hge3 : 3 ≤ (closure c₃ ∩ bd π.S).ncard := by
    rw [← h3_card]
    exact ncard_le_ncard hsub_cl hcl_fin
  have hle2 := (theorem_8_6_proof h𝒯 π htrue hred hwarp hθ hc₃ hint₃).1
  omega

private theorem two_cell_union_eq
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    (c₀ : Set π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (c₃ : Set π.S)
    (hc₃ : c₃ ∈ π.Γ.C)
    (hA₂'_le : (π.cellsUnion {c₀, c₃}) ≤ G) :
    (π.cellsUnion {c₀, c₃}) = π.cellGraph c₀ ∪ π.cellGraph c₃ := by
  let A₂' := π.cellsUnion {c₀, c₃}
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hA₂'_le
    (union_le (π.cellGraph_le c₀ hc₀) (π.cellGraph_le c₃ hc₃))
  · ext v
    simp only [Portrayal.cellsUnion, union_vertexSet, mem_union, mem_iUnion,
      mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨c, ⟨hEq | hEq, _⟩, hv⟩
      · exact Or.inl (hEq ▸ hv)
      · exact Or.inr (hEq ▸ hv)
    · rintro (hv | hv)
      · exact ⟨c₀, ⟨Or.inl rfl, hc₀⟩, hv⟩
      · exact ⟨c₃, ⟨Or.inr rfl, hc₃⟩, hv⟩
  · ext e
    simp only [Portrayal.cellsUnion, union_edgeSet, mem_union, mem_iUnion,
      mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨c, ⟨hEq | hEq, _⟩, he⟩
      · exact Or.inl (hEq ▸ he)
      · exact Or.inr (hEq ▸ he)
    · rintro (he | he)
      · exact ⟨c₀, ⟨Or.inl rfl, hc₀⟩, he⟩
      · exact ⟨c₃, ⟨Or.inr rfl, hc₃⟩, he⟩

private theorem three_node_cell_has_node_outside_pair
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {n₁ : π.S}
    (n₂ : π.S)
    (hne₁₂ : n₁ ≠ n₂)
    (c₃ : Set π.S)
    (hcard₃ : (tilde c₃).ncard = 3) :
    (tilde c₃ \ {n₁, n₂}).Nonempty := by
  by_contra hempty
  have hsub : tilde c₃ ⊆ {n₁, n₂} := sdiff_eq_empty.mp (not_nonempty_iff_eq_empty.mp hempty)
  have hle := ncard_le_ncard hsub (finite_singleton n₂ |>.insert n₁)
  rw [ncard_pair hne₁₂] at hle
  omega

private theorem three_node_cell_nodes_eq_insert
    {α β : Type*} {G : Hypergraph α β} (π : Portrayal G)
    {c₀ c₃ : Set π.S} {n₁ n₂ n₃ : π.S}
    (hne₁₂ : n₁ ≠ n₂) (hn₁_ne_n₃ : n₁ ≠ n₃) (hn₂_ne_n₃ : n₂ ≠ n₃)
    (hn₁_tc₀ : n₁ ∈ tilde c₀) (hn₂_tc₀ : n₂ ∈ tilde c₀)
    (htc₀_sub₃ : tilde c₀ ⊆ tilde c₃) (hn₃_tc₃ : n₃ ∈ tilde c₃)
    (hcard₃ : (tilde c₃).ncard = 3) (htc₃_fin : (tilde c₃).Finite) :
    tilde c₃ = {n₁, n₂, n₃} := by
  have hsub : ({n₁, n₂, n₃} : Set π.S) ⊆ tilde c₃ := by
    rintro x (rfl | rfl | rfl)
    · exact htc₀_sub₃ hn₁_tc₀
    · exact htc₀_sub₃ hn₂_tc₀
    · exact hn₃_tc₃
  have h3_card : ({n₁, n₂, n₃} : Set π.S).ncard = 3 := by
    rw [ncard_insert_of_notMem, ncard_pair hn₂_ne_n₃]
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hne₁₂, hn₁_ne_n₃⟩
  exact (eq_of_subset_of_ncard_le hsub (by omega) htc₃_fin).symm

private theorem enlarged_cell_contains_border_and_third_node
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {n₁ : π.S}
    (c₀ : Set π.S)
    (c₃ : Set π.S)
    (n₃ : π.S)
    (hbp₁_sub_c₀ : π.borderPlus n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₃_in_c₃ : π.nodeVertex n₃ ∈ (π.cellGraph c₃).vertexSet)
    (A₂' : Hypergraph α β)
    (hA₂'_eq : A₂' = π.cellGraph c₀ ∪ π.cellGraph c₃) :
    π.borderPlus n₁ ∪ {π.nodeVertex n₃} ⊆ A₂'.vertexSet := by
  rw [hA₂'_eq]
  rintro x (hx₁ | rfl)
  · exact Or.inl (hbp₁_sub_c₀ hx₁)
  · exact Or.inr hn₃_in_c₃

/-- **Graph Minors XVII, (9.4)** (page 185):
"Let $\pi$ have warp $q$ at a cuff $\Theta$; then $|\beta(n)| = q$ for all
$n \in N(\Gamma) \cap \Theta$."
Note: in the printed proof on page 185, the displayed definitions of
$\alpha'(c_1)$ and $\alpha'(c_2)$ are swapped relative to $\tilde{c}_1 = \{n_1, n_3\}$,
$\tilde{c}_2 = \{n_2, n_3\}$ and the verification on page 186; we assign the edgeless hypergraph
on $\beta(n_1+) \cup \{\gamma(n_3)\}$ to $c_1$ and $\alpha(c_0) \cup \alpha(c_3)$ to $c_2$, matching
the verification on page 186. -/
theorem theorem_9_4_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {Θ : Set π.S} (hΘ : Θ ∈ cuffs π.S) {n₁ : π.S} (hn₁ : n₁ ∈ π.Γ.N ∩ Θ) :
    (π.borderSet n₁).ncard = π.warpAt Θ := by
  have : T2Space π.S := π.isSurface.2.1
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof
      h𝒯 π htrue hred hwarp hθ
  obtain ⟨_, _, hnode_cell⟩ :=
    theorem_8_2_proof
      h𝒯 π htrue hred hwarp hθ
  have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hbs₁_le : (π.borderSet n₁).ncard ≤ π.warpAt Θ :=
    π.ncard_borderSet_le_warpAt hΘ hΘ_arc hn₁
  refine le_antisymm hbs₁_le ?_
  by_contra hlt_bs₁
  push Not at hlt_bs₁
  set k := (π.Γ.N ∩ Θ).ncard
  obtain ⟨E⟩ : Nonempty (π.Γ.CuffEnumeration Θ k) := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  have hn₁_range : n₁ ∈ range E.node := E.range_node ▸ hn₁
  rcases hn₁_range with ⟨idx, hidx_eq⟩
  have hk_ge2 : 2 ≤ k := E.two_le
  have hk_pos : 0 < k := by omega
  let idx' : Fin k := ⟨(idx.1 + 1) % k, Nat.mod_lt _ hk_pos⟩
  have hidx_ne : idx ≠ idx' := by
    intro hEq
    have hval : idx.1 = (idx.1 + 1) % k := congrArg Fin.val hEq
    have hi_lt : idx.1 < k := idx.2
    by_cases hlast : idx.1 + 1 = k
    · rw [hlast, Nat.mod_self] at hval; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega
  let c₀ := E.cell idx
  let n₂ := E.node idx'
  have hc₀_mem : c₀ ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := E.range_cell ▸ ⟨idx, rfl⟩
  have hc₀ : c₀ ∈ π.Γ.C := hc₀_mem.1
  have hc₀_Θ : (c₀ ∩ Θ).Nonempty := hc₀_mem.2
  have hbd₀ : (c₀ ∩ bd π.S).Nonempty := hc₀_Θ.mono (inter_subset_inter_right _ hΘ_bd)
  have htc₀ : tilde c₀ = {n₁, n₂} := by
    change tilde (E.cell idx) = {n₁, E.node idx'}
    rw [E.cell_tilde idx, hidx_eq]
  have hne₁₂ : n₁ ≠ n₂ := by
    rw [← hidx_eq]
    exact E.injective_node.ne hidx_ne
  have hn₁_tc₀ : n₁ ∈ tilde c₀ := htc₀ ▸ Or.inl rfl
  have hn₂_tc₀ : n₂ ∈ tilde c₀ := htc₀ ▸ Or.inr rfl
  have hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ := E.range_node ▸ ⟨idx', rfl⟩
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S := ⟨hn₁.1, hΘ_bd hn₁.2⟩
  have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S := ⟨hn₂_Θ.1, hΘ_bd hn₂_Θ.2⟩
  have hbs₂_le : (π.borderSet n₂).ncard ≤ π.warpAt Θ :=
    π.ncard_borderSet_le_warpAt hΘ hΘ_arc hn₂_Θ
  have hex_c₃ : ∃ c ∈ π.Γ.C, ¬ (c ∩ bd π.S).Nonempty ∧ tilde c₀ ⊆ tilde c := by
    by_contra hno_int
    have h93 := (theorem_9_3_proof h𝒯 π htrue hred hwarp hθ
      hΘ hc₀ hc₀_Θ hn₁_tc₀ hn₂_tc₀ hne₁₂ hno_int).2.1
    omega
  rcases hex_c₃ with ⟨c₃, hc₃, hint₃, htc₀_sub₃⟩
  have hc₀_ne_c₃ : c₀ ≠ c₃ := fun h => hint₃ (h ▸ hbd₀)
  have hcard₃ : (tilde c₃).ncard = 3 :=
    (theorem_8_8_proof
      h𝒯 π htrue hred hwarp hθ hc₀ hc₃ hc₀_ne_c₃ htc₀_sub₃).2
  have htc₃_fin : (tilde c₃).Finite := π.Γ.finite_tilde_cell hc₃
  obtain ⟨n₃, hn₃_tc₃, hn₃_not_pair⟩ :=
    three_node_cell_has_node_outside_pair π n₂ hne₁₂ c₃ hcard₃
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hn₃_not_pair
  have hn₁_ne_n₃ : n₁ ≠ n₃ := Ne.symm hn₃_not_pair.1
  have hn₂_ne_n₃ : n₂ ≠ n₃ := Ne.symm hn₃_not_pair.2
  have htc₃ : tilde c₃ = {n₁, n₂, n₃} :=
    three_node_cell_nodes_eq_insert π hne₁₂ hn₁_ne_n₃ hn₂_ne_n₃ hn₁_tc₀ hn₂_tc₀
      htc₀_sub₃ hn₃_tc₃ hcard₃ htc₃_fin
  have hn₃_N : n₃ ∈ π.Γ.N := π.Γ.tilde_subset_N hc₃ hn₃_tc₃
  have hn₃_not_bd : n₃ ∉ bd π.S := by
    exact third_node_of_indented_cell_is_internal (α := α) (β := β) (G := G) (𝒯 := 𝒯) (θ := θ) (p
      := p) h𝒯 π htrue hred hwarp hθ (Θ := Θ) (n₁ := n₁) hn₁ hbs₁_le hlt_bs₁ k E idx hidx_eq
      c₀ n₂ htc₀ hne₁₂ hn₁_tc₀ hn₁_bd hn₂_bd c₃ hc₃ hint₃ hcard₃ htc₃_fin n₃ hn₃_tc₃
      hn₃_not_pair hn₁_ne_n₃ hn₂_ne_n₃ htc₃ hn₃_N
  have hn₃ : n₃ ∈ π.Γ.N \ bd π.S := ⟨hn₃_N, hn₃_not_bd⟩
  obtain ⟨Γ', hind⟩ :=
    (indentedBorderPainting_props h𝒯 π htrue hred hwarp hθ
      hΘ hc₀ hc₀_Θ hne₁₂ htc₀).2 c₃ hc₃ hint₃ n₃ hn₃ htc₃
  have hbp₁_sub_c₀ : π.borderPlus n₁ ⊆ (π.cellGraph c₀).vertexSet :=
    π.borderPlus_subset_cellGraph hc₀ hbd₀ hn₁_tc₀
  have hbp₂_sub_c₀ : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet :=
    π.borderPlus_subset_cellGraph hc₀ hbd₀ hn₂_tc₀
  have hn₃_in_c₃ : π.nodeVertex n₃ ∈ (π.cellGraph c₃).vertexSet :=
    π.p2 c₃ hc₃ n₃ ⟨hn₃_tc₃, hdom ▸ hn₃_N⟩
  have hn₃_not_c₀ : π.nodeVertex n₃ ∉ (π.cellGraph c₀).vertexSet := by
    rw [internal_nodeVertex_mem_cellGraph_iff π hdom hnode_cell hn₃ hc₀, htc₀]
    rintro (hEq | hEq)
    · exact hn₁_ne_n₃ hEq.symm
    · exact hn₂_ne_n₃ hEq.symm
  let A₂' := π.cellsUnion {c₀, c₃}
  have hA₂'_le : A₂' ≤ G := π.cellsUnion_le {c₀, c₃}
  have hA₂'_eq : A₂' = π.cellGraph c₀ ∪ π.cellGraph c₃ := by
    exact two_cell_union_eq (α := α) (β := β) (G := G) π c₀ hc₀ c₃ hc₃ hA₂'_le
  have hbp₁_n₃_sub_A₂' : π.borderPlus n₁ ∪ {π.nodeVertex n₃} ⊆ A₂'.vertexSet := by
    exact enlarged_cell_contains_border_and_third_node (α := α) (β := β) (G := G) π (n₁ := n₁) c₀
      c₃ n₃ hbp₁_sub_c₀ hn₃_in_c₃ A₂' hA₂'_eq
  have hbp₁_n₃_sub_G : π.borderPlus n₁ ∪ {π.nodeVertex n₃} ⊆ G.vertexSet :=
    hbp₁_n₃_sub_A₂'.trans hA₂'_le.1
  let A₁' := edgelessSubhypergraph G (π.borderPlus n₁ ∪ {π.nodeVertex n₃}) hbp₁_n₃_sub_G
  have hA₁'_le : A₁' ≤ G := edgelessSubhypergraph_le G _ hbp₁_n₃_sub_G
  have hV_union : (π.cellsUnion {c₀, c₃}).vertexSet ⊆ A₁'.vertexSet ∪ A₂'.vertexSet :=
    subset_union_right
  have hV_sub : A₁'.vertexSet ∪ A₂'.vertexSet ⊆
      (π.cellsUnion {c₀, c₃}).vertexSet ∪ {π.nodeVertex n₃} :=
    (union_subset hbp₁_n₃_sub_A₂' Subset.rfl).trans subset_union_left
  have hE_union : A₁'.edgeSet ∪ A₂'.edgeSet = (π.cellsUnion {c₀, c₃}).edgeSet :=
    empty_union _
  have hE_disj : Disjoint A₁'.edgeSet A₂'.edgeSet := disjoint_bot_left
  have hbp₁' : π.borderPlus n₁ ⊆ A₁'.vertexSet := subset_union_left
  have hbp₂' : π.borderPlus n₂ ⊆ A₂'.vertexSet := by
    rw [hA₂'_eq]
    exact fun x hx => Or.inl (hbp₂_sub_c₀ hx)
  have hinter_eq : A₁'.vertexSet ∩ A₂'.vertexSet = π.borderPlus n₁ ∪ {π.nodeVertex n₃} :=
    inter_eq_left.mpr hbp₁_n₃_sub_A₂'
  have hn₃_mem_inter : π.nodeVertex n₃ ∈ A₁'.vertexSet ∩ A₂'.vertexSet :=
    hinter_eq ▸ Or.inr rfl
  have hinter_sdiff : (A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n₃} = π.borderPlus n₁ := by
    rw [hinter_eq, union_sdiff_distrib, sdiff_self, union_empty]
    exact sdiff_eq_self_iff_disjoint.mpr (disjoint_singleton_left.mpr
      (fun hm => hn₃_not_c₀ (hbp₁_sub_c₀ hm)))
  have hbs_sub : (A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n₃} ⊆
      (π.cellGraph c₀).vertexSet :=
    hinter_sdiff ▸ hbp₁_sub_c₀
  have hbp₁_le_q : (π.borderPlus n₁).ncard ≤ π.warpAt Θ := by
    have hle := π.ncard_borderPlus_le hn₁_bd
    omega
  have hbs_star_le : ((A₁'.vertexSet ∩ A₂'.vertexSet) \ {π.nodeVertex n₃}).ncard ≤ π.warpAt Θ :=
    hinter_sdiff ▸ hbp₁_le_q
  have hw_le : π.warpAt Θ ≤ p := (π.warpAt_le_warp hΘ).trans hwarp
  have hbp₁_fin : (π.borderPlus n₁).Finite :=
    (π.cellGraph c₀).vertexSet_finite.subset hbp₁_sub_c₀
  have hbp₂_fin : (π.borderPlus n₂).Finite :=
    (π.cellGraph c₀).vertexSet_finite.subset hbp₂_sub_c₀
  have hsmall₁ : ∃ B, (A₁', B) ∈ 𝒯 := by
    have hA₁'_le_union : A₁' ≤ π.cellGraph c₀ ∪ π.cellGraph c₃ := by
      rw [← hA₂'_eq]
      exact ⟨hbp₁_n₃_sub_A₂', empty_subset _, fun _ he => he.elim⟩
    have hatt_sub : attachments G A₁' ⊆ π.borderPlus n₁ ∪ {π.nodeVertex n₃} :=
      attachments_subset_vertexSet
    have hfin₁ : (π.borderPlus n₁ ∪ {π.nodeVertex n₃}).Finite :=
      hbp₁_fin.union (finite_singleton _)
    have hatt_lt : (attachments G A₁').ncard < θ := by
      have h1 := ncard_le_ncard hatt_sub hfin₁
      have h2 := ncard_union_le (π.borderPlus n₁) {π.nodeVertex n₃}
      have h3 := ncard_singleton (π.nodeVertex n₃)
      omega
    exact theorem_4_1_ii h𝒯 (htrue.1 c₀ hc₀) (htrue.1 c₃ hc₃) hA₁'_le_union hatt_lt
  have hsmall₂ : ∃ B, (A₂', B) ∈ 𝒯 := by
    rw [hA₂'_eq]
    have hatt_sub : attachments G (π.cellGraph c₀ ∪ π.cellGraph c₃) ⊆
        (π.borderPlus n₁ ∪ π.borderPlus n₂) ∪ {π.nodeVertex n₃} := by
      refine attachments_union_subset.trans ?_
      rintro x (hx₀ | hx₃)
      · have hx_ov := π.attachments_cellGraph_subset_otherVertices hc₀ hx₀
        rcases hx_ov.2 with ⟨d, hd, hdc₀, hxd⟩
        exact Or.inl (border_cell_vertex_mem_borderPlus_of_mem_other π hc₀ hbd₀ htc₀
          hx_ov.1 hd hdc₀ hxd)
      · have hx_ov := π.attachments_cellGraph_subset_otherVertices hc₃ hx₃
        obtain ⟨m, ⟨hm_tc₃, _⟩, rfl⟩ := π.p5 c₃ hc₃ hint₃ x hx_ov.1 hx_ov.2
        rw [htc₃] at hm_tc₃
        rcases hm_tc₃ with rfl | rfl | rfl
        · exact Or.inl (Or.inl (Or.inr ⟨hdom ▸ hn₁.1, rfl⟩))
        · exact Or.inl (Or.inr (Or.inr ⟨hdom ▸ hn₂_Θ.1, rfl⟩))
        · exact Or.inr rfl
    have hfin₂ : ((π.borderPlus n₁ ∪ π.borderPlus n₂) ∪ {π.nodeVertex n₃}).Finite :=
      (hbp₁_fin.union hbp₂_fin).union (finite_singleton _)
    have hatt_lt : (attachments G (π.cellGraph c₀ ∪ π.cellGraph c₃)).ncard < θ := by
      have h1 := ncard_le_ncard hatt_sub hfin₂
      have h2 := ncard_union_le (π.borderPlus n₁ ∪ π.borderPlus n₂) {π.nodeVertex n₃}
      have h3 := ncard_union_le (π.borderPlus n₁) (π.borderPlus n₂)
      have h4 := ncard_singleton (π.nodeVertex n₃)
      have hbp₂_c := ncard_borderPlus_le_warpAt_succ π hΘ hn₂_Θ
      omega
    exact theorem_4_1_ii h𝒯 (htrue.1 c₀ hc₀) (htrue.1 c₃ hc₃) le_rfl hatt_lt
  have hlp₁ : (π.borderPlus n₁).ncard = π.warpAt Θ + 1 →
      (A₁'.vertexSet ∩ A₂'.vertexSet).ncard = π.warpAt Θ + 1 →
      Portrayal.LinkagePairs A₁'.skeleton (π.borderPlus n₁) (A₁'.vertexSet ∩ A₂'.vertexSet)
        (π.warpAt Θ + 1) (π.nodeVertex n₁) (π.nodeVertex n₃) := by
    intro hbp₁_eq
    omega
  have hinter_fin' : (A₁'.vertexSet ∩ A₂'.vertexSet).Finite :=
    A₁'.vertexSet_finite.subset inter_subset_left
  have hlp₂_bridge : (π.borderPlus n₂).ncard = π.warpAt Θ + 1 →
      (A₁'.vertexSet ∩ A₂'.vertexSet).ncard = π.warpAt Θ + 1 →
      Portrayal.LinkagePairs A₂'.skeleton (π.borderPlus n₂) (A₁'.vertexSet ∩ A₂'.vertexSet)
        (π.warpAt Θ + 1) (π.nodeVertex n₂) (π.nodeVertex n₃) := by
    exact linkage_crosses_to_third_node (α := α) (β := β) (G := G) π (Θ := Θ) (n₁ := n₁) hn₁ hdom
      c₀ n₂ hc₀ hn₂_Θ c₃ hc₃ hint₃ hc₀_ne_c₃ n₃ hn₁_ne_n₃ htc₃ hn₃_N hbp₂_sub_c₀ hn₃_in_c₃
      hn₃_not_c₀ hA₂'_eq A₁' hinter_eq hn₃_mem_inter hbp₂_fin hinter_fin'
  have hR_sub : ({c₀, c₃} : Set (Set π.S)) ⊆ π.Γ.C := by
    rintro c (rfl | rfl) <;> assumption
  have hR_cases : ∀ c ∈ ({c₀, c₃} : Set (Set π.S)),
      c = c₀ ∨ (¬ (c ∩ bd π.S).Nonempty ∧ tilde c = {n₁, n₂, n₃}) := by
    rintro c (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨hint₃, htc₃⟩
  exact not_indentedPortrayal π htrue hdom hnode_cell hΘ hc₀ hc₀_Θ hne₁₂ htc₀ hn₃
    (Or.inl rfl) hR_sub hR_cases hind hA₁'_le hA₂'_le hV_union hV_sub hE_union hE_disj
    hbp₁' hbp₂' hn₃_mem_inter hbs_sub hsmall₁ hsmall₂ hbs₁_le hbs₂_le hbs_star_le hlp₁ hlp₂_bridge

private theorem other_cell_vertices_on_boundary
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hne : n₁ ≠ n₂)
    (hdom : π.domγ = π.Γ.N)
    (hsub_cuff₀ : closure c₀ ∩ bd π.S ⊆ Θ ∧ c₀ ∩ bd π.S = c₀ ∩ Θ ∧ closure c₀ ∩ bd π.S = closure
      c₀ ∩ Θ ∧ tilde c₀ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₀ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S)
    (hbs₁_sub : π.borderSet n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₁_in_c₀ : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hA₁_sub : π.borderSet n₁ ∪ {π.nodeVertex n₁} ⊆ A₁.vertexSet)
    (hA₂_sub : π.borderPlus n₂ ∪ {π.nodeVertex n₁} ⊆ A₂.vertexSet)
    (hlt_q : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).ncard < π.warpAt Θ)
    (hbp₁_A₁ : π.borderPlus n₁ ⊆ A₁.vertexSet)
    (hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet)
    (c₁ : Set π.S)
    (hc₁_Θ : (c₁ ∩ Θ).Nonempty)
    (n₃ : π.S)
    (hne₁₃ : n₁ ≠ n₃)
    (htc₁ : tilde c₁ = {n₁, n₃})
    (hd_iff : ∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty → (n₁ ∈ tilde d ↔ d = c₀ ∨ d = c₁))
    (hneighbors : ∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ → ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m → v ∈
      π.borderPlus n₂ ∨ v ∈ π.borderPlus n₃)
    (hsub_cuff₁ : closure c₁ ∩ bd π.S ⊆ Θ ∧ c₁ ∩ bd π.S = c₁ ∩ Θ ∧ closure c₁ ∩ bd π.S = closure
      c₁ ∩ Θ ∧ tilde c₁ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₁ ∩ Θ').Nonempty → Θ' = Θ)
    (hn₁_tc₁ : n₁ ∈ tilde c₁)
    (hn₃_Θ : n₃ ∈ π.Γ.N ∩ Θ)
    (bs' : π.S → Set α)
    (bp' : π.S → Set α)
    (hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁})
    (hbs'_other : ∀ (n : π.S), n ≠ n₁ → bs' n = π.borderSet n)
    (hbp'_n₁ : bp' n₁ = A₁.vertexSet ∩ A₂.vertexSet)
    (hbp'_other : ∀ (n : π.S), n ≠ n₁ → bp' n = π.borderPlus n) :
    ∀ w ∈ (π.cellGraph c₀).vertexSet, ∀ d ∈ π.Γ.C \ {c₀, c₁}, w ∈ (π.cellGraph d).vertexSet → w ∈
      bp' n₁ ∨ w ∈ π.borderPlus n₂ ∨ w ∈ π.borderPlus n₃ := by
  rintro w hw₀ d ⟨hd, hd_not⟩ hwd
  have hd_ne_c₀ : d ≠ c₀ := fun h => hd_not (Or.inl h)
  have hd_ne_c₁ : d ≠ c₁ := fun h => hd_not (Or.inr h)
  rcases border_cell_vertex_mem_borderPlus_of_mem_other π hc₀ hbd₀ htc₀ hw₀ hd hd_ne_c₀ hwd with
    hw_n₁ | hw_n₂
  · by_cases hbd_d : (d ∩ bd π.S).Nonempty
    · obtain ⟨m, hm_td, hwm⟩ := π.p6 d hd hbd_d w hwd ⟨c₀, hc₀, hd_ne_c₀.symm, hw₀⟩
      have hm_ne_n₁ : m ≠ n₁ := fun h =>
        hd_not ((hd_iff d hd hbd_d).mp (h ▸ hm_td))
      have hmN : m ∈ π.Γ.N := π.Γ.tilde_subset_N hd hm_td
      have hmbd : m ∈ bd π.S := tilde_border_cell_subset_bd π.Γ hd hbd_d hm_td
      let Θ' := connectedComponentIn (bd π.S) m
      have hΘ' : Θ' ∈ cuffs π.S := ⟨m, hmbd, rfl⟩
      have hm_Θ' : m ∈ π.Γ.N ∩ Θ' := ⟨hmN, mem_connectedComponentIn hmbd⟩
      have hΘ'_eq : Θ' = Θ := by
        by_contra hne_Θ
        rcases hw_n₁ with hbs₁ | ⟨_, rfl⟩
        · rcases hwm with hbs_m | ⟨_, rfl⟩
          · exact Set.disjoint_left.mp
              (π.p4_disjoint Θ hΘ Θ' hΘ' (Ne.symm hne_Θ) n₁ hn₁_Θ m hm_Θ') hbs₁ hbs_m
          · have hm_not_Θ : m ∉ Θ := by
              intro hm_in_Θ
              rcases hΘ with ⟨x₀, _, rfl⟩
              exact hne_Θ ((connectedComponentIn_eq hm_Θ'.2).trans
                (connectedComponentIn_eq hm_in_Θ).symm)
            exact π.p4_notMem Θ hΘ n₁ hn₁_Θ m (hdom ▸ hmN) hm_not_Θ hbs₁
        · rcases hwm with hbs_m | ⟨_, hEq⟩
          · have hn₁_not_Θ' : n₁ ∉ Θ' := by
              intro hn₁_in_Θ'
              rcases hΘ with ⟨x₀, _, rfl⟩
              exact hne_Θ ((connectedComponentIn_eq hn₁_in_Θ').trans
                (connectedComponentIn_eq hn₁_Θ.2).symm)
            exact π.p4_notMem Θ' hΘ' m hm_Θ' n₁ (hdom ▸ hn₁_Θ.1) hn₁_not_Θ' hbs_m
          · exact hm_ne_n₁ (π.nodeVertex_injOn (hdom ▸ hmN) (hdom ▸ hn₁_Θ.1) hEq.symm)
      have hm_Θ : m ∈ π.Γ.N ∩ Θ := hΘ'_eq ▸ hm_Θ'
      rcases hneighbors m hm_Θ hm_ne_n₁ w hw_n₁ hwm with hw_n₂ | hw_n₃
      · exact Or.inr (Or.inl hw_n₂)
      · exact Or.inr (Or.inr hw_n₃)
    · obtain ⟨m, ⟨hm_td, hm_dom⟩, rfl⟩ :=
        π.p5 d hd hbd_d w hwd ⟨c₀, hc₀, hd_ne_c₀.symm, hw₀⟩
      by_cases hm_n₁ : m = n₁
      · subst hm_n₁
        exact Or.inl (hbp'_n₁ ▸ hn₁_mem_inter)
      · have hm_Θ_mem : m ∈ Θ := by
          by_contra hm_not_Θ
          rcases hw_n₁ with hbs₁ | ⟨_, hEq⟩
          · exact π.p4_notMem Θ hΘ n₁ hn₁_Θ m hm_dom hm_not_Θ hbs₁
          · exact hm_n₁ (π.nodeVertex_injOn hm_dom (hdom ▸ hn₁_Θ.1) hEq)
        have hm_Θ : m ∈ π.Γ.N ∩ Θ := ⟨hdom ▸ hm_dom, hm_Θ_mem⟩
        have hwm : π.nodeVertex m ∈ π.borderPlus m := Or.inr ⟨hm_dom, rfl⟩
        rcases hneighbors m hm_Θ hm_n₁ (π.nodeVertex m) hw_n₁ hwm with hw_n₂ | hw_n₃
        · exact Or.inr (Or.inl hw_n₂)
        · exact Or.inr (Or.inr hw_n₃)
  · exact Or.inr (Or.inl hw_n₂)

open Classical in
private noncomputable abbrev split_adjacent_border_cells_portrayal
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂)
    [T2Space π.S]
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c)
    (hsub_cuff₀ : closure c₀ ∩ bd π.S ⊆ Θ ∧ c₀ ∩ bd π.S = c₀ ∩ Θ ∧ closure c₀ ∩ bd π.S = closure
      c₀ ∩ Θ ∧ tilde c₀ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₀ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (u₀ : π.S)
    (v₀ : π.S)
    (htc₀_uv : tilde c₀ = {u₀, v₀})
    (hL₀ : IsLineWithEnds (closure c₀ ∩ bd π.S) u₀ v₀)
    (hL₀_int : c₀ ∩ bd π.S = (closure c₀ ∩ bd π.S) \ {u₀, v₀})
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hbs₁_sub : π.borderSet n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₁_in_c₀ : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (hlt_q : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).ncard < π.warpAt Θ)
    (hbp₁_A₁ : π.borderPlus n₁ ⊆ A₁.vertexSet)
    (hbp₂_A₂ : π.borderPlus n₂ ⊆ A₂.vertexSet)
    (hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet)
    (c₁ : Set π.S)
    (hc₁ : c₁ ∈ π.Γ.C)
    (hc₁_Θ : (c₁ ∩ Θ).Nonempty)
    (hc₁_ne_c₀ : c₁ ≠ c₀)
    (n₃ : π.S)
    (hne₁₃ : n₁ ≠ n₃)
    (htc₁ : tilde c₁ = {n₁, n₃})
    (hd_iff : ∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty → (n₁ ∈ tilde d ↔ d = c₀ ∨ d = c₁))
    (hneighbors : ∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ → ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m → v ∈
      π.borderPlus n₂ ∨ v ∈ π.borderPlus n₃)
    (hsub_cuff₁ : closure c₁ ∩ bd π.S ⊆ Θ ∧ c₁ ∩ bd π.S = c₁ ∩ Θ ∧ closure c₁ ∩ bd π.S = closure
      c₁ ∩ Θ ∧ tilde c₁ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₁ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₁ : (c₁ ∩ bd π.S).Nonempty)
    (hn₁_tc₁ : n₁ ∈ tilde c₁)
    (hn₃_tc₁ : n₃ ∈ tilde c₁)
    (hn₃_Θ : n₃ ∈ π.Γ.N ∩ Θ)
    (cellG' : Set π.S → Hypergraph α β)
    (bs' : π.S → Set α)
    (bp' : π.S → Set α)
    (hbp_def : bp' = fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n})
    (hcellG'_c₀ : cellG' c₀ = A₂)
    (hcellG'_c₁ : cellG' c₁ = A₁ ∪ π.cellGraph c₁)
    (hcellG'_other : ∀ c ∈ π.Γ.C \ {c₀, c₁}, cellG' c = π.cellGraph c)
    (hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁})
    (hbs'_other : ∀ (n : π.S), n ≠ n₁ → bs' n = π.borderSet n)
    (hbp'_n₁ : bp' n₁ = A₁.vertexSet ∩ A₂.vertexSet)
    (hbp'_other : ∀ (n : π.S), n ≠ n₁ → bp' n = π.borderPlus n)
    (hA₁_le_G : A₁ ≤ G)
    (hcellG'_le : ∀ c ∈ π.Γ.C, cellG' c ≤ G)
    (hw_c₀_other : ∀ w ∈ (π.cellGraph c₀).vertexSet, ∀ d ∈ π.Γ.C \ {c₀, c₁}, w ∈ (π.cellGraph
      d).vertexSet → w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₂ ∨ w ∈ π.borderPlus n₃)
    (h_inOrder_eq : ∀ {Θ₁ : Set π.S} {a b d_n : π.S}, a ≠ b → d_n ≠ a → GM19.InOrderOn Θ₁ a b a
      d_n → False) : Portrayal G :=
  { S := π.S
    top := π.top
    isSurface := π.isSurface
    connected := π.connected
    Γ := π.Γ
    cellGraph := cellG'
    cellGraph_le := hcellG'_le
    borderSet := bs'
    borderSet_subset := fun n hn => by
      by_cases hn_n₁ : n = n₁
      · rw [hn_n₁, hbs'_n₁]
        exact sdiff_subset.trans (inter_subset_left.trans hA₁_le_G.1)
      · rw [hbs'_other n hn_n₁]
        exact π.borderSet_subset n hn
    domγ := π.domγ
    domγ_subset := π.domγ_subset
    nodeVertex := π.nodeVertex
    nodeVertex_mem := π.nodeVertex_mem
    nodeVertex_injOn := π.nodeVertex_injOn
    p1_vertex := fun v hv => by
      obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hv
      by_cases hc_c₀ : c = c₀
      · rw [hc_c₀, ← hsep.vertexSet_union] at hvc
        rcases hvc with hv₁ | hv₂
        · exact ⟨c₁, hc₁, hcellG'_c₁ ▸ Or.inl hv₁⟩
        · exact ⟨c₀, hc₀, hcellG'_c₀ ▸ hv₂⟩
      · by_cases hc_c₁ : c = c₁
        · exact ⟨c₁, hc₁, hcellG'_c₁ ▸ Or.inr (hc_c₁ ▸ hvc)⟩
        · refine ⟨c, hc, ?_⟩
          rw [hcellG'_other c ⟨hc, by rintro (rfl | rfl) <;> contradiction⟩]
          exact hvc
    p1_edge := fun e he => by
      obtain ⟨c, hc, hec⟩ := π.p1_edge e he
      by_cases hc_c₀ : c = c₀
      · rw [hc_c₀, ← hsep.edgeSet_union] at hec
        rcases hec with he₁ | he₂
        · exact ⟨c₁, hc₁, hcellG'_c₁ ▸ Or.inl he₁⟩
        · exact ⟨c₀, hc₀, hcellG'_c₀ ▸ he₂⟩
      · by_cases hc_c₁ : c = c₁
        · exact ⟨c₁, hc₁, hcellG'_c₁ ▸ Or.inr (hc_c₁ ▸ hec)⟩
        · refine ⟨c, hc, ?_⟩
          rw [hcellG'_other c ⟨hc, by rintro (rfl | rfl) <;> contradiction⟩]
          exact hec
    p1_disjoint := fun d₁ hd₁ d₂ hd₂ hne_d => by
      have hsub_E : ∀ d ∈ π.Γ.C, (cellG' d).edgeSet ⊆
          if d = c₀ then A₂.edgeSet else if d = c₁ then A₁.edgeSet ∪ (π.cellGraph c₁).edgeSet
          else (π.cellGraph d).edgeSet := by
        intro d hd
        by_cases hd₀ : d = c₀
        · simp [hd₀, hcellG'_c₀]
        · by_cases hd₁' : d = c₁
          · simp [hd₁', hc₁_ne_c₀, hcellG'_c₁]
          · simp [hd₀, hd₁', hcellG'_other d ⟨hd, by rintro (rfl | rfl) <;> contradiction⟩]
      refine Set.disjoint_left.mpr fun e he₁ he₂ => ?_
      have h1 := hsub_E d₁ hd₁ he₁
      have h2 := hsub_E d₂ hd₂ he₂
      revert h1 h2
      split_ifs <;> intro h1 h2
      · exact hne_d (by subst_vars; rfl)
      · rcases h2 with h2A₁ | h2c₁
        · exact Set.disjoint_left.mp
            (Set.disjoint_iff_inter_eq_empty.mpr hsep.edgeSet_inter_eq) h2A₁ h1
        · exact Set.disjoint_left.mp
            (π.p1_disjoint c₀ hc₀ c₁ hc₁ hc₁_ne_c₀.symm) (hsep.right_le.2 h1) h2c₁
      · exact Set.disjoint_left.mp
          (π.p1_disjoint c₀ hc₀ d₂ hd₂ (by subst_vars; exact Ne.symm ‹_›))
          (hsep.right_le.2 h1) h2
      · rcases h1 with h1A₁ | h1c₁
        · exact Set.disjoint_left.mp
            (Set.disjoint_iff_inter_eq_empty.mpr hsep.edgeSet_inter_eq) h1A₁ h2
        · exact Set.disjoint_left.mp
            (π.p1_disjoint c₁ hc₁ c₀ hc₀ hc₁_ne_c₀) h1c₁ (hsep.right_le.2 h2)
      · exact hne_d (by subst_vars; rfl)
      · rcases h1 with h1A₁ | h1c₁
        · exact Set.disjoint_left.mp
            (π.p1_disjoint c₀ hc₀ d₂ hd₂ (by subst_vars; exact Ne.symm ‹_›))
            (hsep.left_le.2 h1A₁) h2
        · exact Set.disjoint_left.mp
            (π.p1_disjoint c₁ hc₁ d₂ hd₂ (by subst_vars; exact Ne.symm ‹_›))
            h1c₁ h2
      · exact Set.disjoint_left.mp
          (π.p1_disjoint d₁ hd₁ c₀ hc₀ (by subst_vars; assumption))
          h1 (hsep.right_le.2 h2)
      · rcases h2 with h2A₁ | h2c₁
        · exact Set.disjoint_left.mp
            (π.p1_disjoint d₁ hd₁ c₀ hc₀ (by subst_vars; assumption))
            h1 (hsep.left_le.2 h2A₁)
        · exact Set.disjoint_left.mp
            (π.p1_disjoint d₁ hd₁ c₁ hc₁ (by subst_vars; assumption))
            h1 h2c₁
      · exact Set.disjoint_left.mp (π.p1_disjoint d₁ hd₁ d₂ hd₂ hne_d) h1 h2
    p2 := fun c hc n hn => by
      by_cases hc_c₀ : c = c₀
      · rw [hc_c₀] at hn ⊢
        rw [hcellG'_c₀]
        have hntc₀ : n ∈ ({n₁, n₂} : Set π.S) := htc₀ ▸ hn.1
        rcases hntc₀ with hEq | hEq
        · rw [hEq]; exact hn₁_mem_inter.2
        · rw [hEq]; exact hbp₂_A₂ (Or.inr ⟨hEq ▸ hn.2, rfl⟩)
      · by_cases hc_c₁ : c = c₁
        · rw [hc_c₁] at hn ⊢
          rw [hcellG'_c₁]
          exact Or.inr (π.p2 c₁ hc₁ n hn)
        · rw [hcellG'_other c ⟨hc, by rintro (h | h) <;> [exact hc_c₀ h; exact hc_c₁ h]⟩]
          exact π.p2 c hc n hn
    p3_notMem := fun n hn => by
      by_cases hn_n₁ : n = n₁
      · rw [hn_n₁, hbs'_n₁]
        exact fun h => h.2 rfl
      · rw [hbs'_other n hn_n₁]
        exact π.p3_notMem n hn
    p3_subset := fun c hc hbd_c n hn_tc => by
      by_cases hc_c₀ : c = c₀
      · rw [hc_c₀] at hn_tc ⊢
        rw [hcellG'_c₀]
        have hntc₀ : n ∈ ({n₁, n₂} : Set π.S) := htc₀ ▸ hn_tc
        rcases hntc₀ with hEq | hEq
        · rw [hEq, hbs'_n₁]; exact sdiff_subset.trans inter_subset_right
        · rw [hEq, hbs'_other n₂ hne.symm]
          exact fun x hx => hbp₂_A₂ (Or.inl hx)
      · by_cases hc_c₁ : c = c₁
        · rw [hc_c₁] at hn_tc ⊢
          rw [hcellG'_c₁]
          by_cases hn_n₁ : n = n₁
          · rw [hn_n₁, hbs'_n₁]
            exact (sdiff_subset.trans inter_subset_left).trans subset_union_left
          · rw [hbs'_other n hn_n₁]
            exact (π.p3_subset c₁ hc₁ hbd₁ n hn_tc).trans subset_union_right
        · have hc_diff : c ∈ π.Γ.C \ {c₀, c₁} :=
            ⟨hc, by rintro (h | h) <;> [exact hc_c₀ h; exact hc_c₁ h]⟩
          have hn_ne_n₁ : n ≠ n₁ := fun h =>
            hc_diff.2 ((hd_iff c hc hbd_c).mp (h ▸ hn_tc))
          rw [hcellG'_other c hc_diff, hbs'_other n hn_ne_n₁]
          exact π.p3_subset c hc hbd_c n hn_tc
    p4_disjoint := fun Θ₁ hΘ₁ Θ₂ hΘ₂ hne_Θ m₁ hm₁ m₂ hm₂ => by
      have hsub_bs : ∀ m ∈ π.Γ.N ∩ bd π.S,
          bs' m ⊆ if m = n₁ then (π.cellGraph c₀).vertexSet else π.borderSet m := by
        intro m _
        by_cases hm_n₁ : m = n₁
        · simp only [hm_n₁, ↓reduceIte, hbs'_n₁]
          exact sdiff_subset.trans (inter_subset_left.trans hsep.left_le.1)
        · simp [hm_n₁, hbs'_other m hm_n₁]
      refine Set.disjoint_left.mpr fun w hw₁ hw₂ => ?_
      by_cases hm₁_n₁ : m₁ = n₁
      · have hΘ₁_eq : Θ₁ = Θ := by
          rcases hΘ₁ with ⟨x₁, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
          exact (connectedComponentIn_eq (hm₁_n₁ ▸ hm₁.2)).trans
            (connectedComponentIn_eq hn₁_Θ.2).symm
        have hm₂_ne_n₁ : m₂ ≠ n₁ := fun h =>
          hne_Θ (hΘ₁_eq.trans (by
            rcases hΘ₂ with ⟨x₂, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
            exact (connectedComponentIn_eq hn₁_Θ.2).trans
              (connectedComponentIn_eq (h ▸ hm₂.2)).symm))
        rw [hm₁_n₁, hbs'_n₁] at hw₁
        rw [hbs'_other m₂ hm₂_ne_n₁] at hw₂
        have hw_c₀ : w ∈ (π.cellGraph c₀).vertexSet := hsep.left_le.1 hw₁.1.1
        have hΘ₂_bd : Θ₂ ⊆ bd π.S := by
          rcases hΘ₂ with ⟨x₂, _, rfl⟩; exact connectedComponentIn_subset _ x₂
        have hbp := border_cell_vertex_inter_borderPlus_subset π hc₀ hbd₀ htc₀
          ⟨hm₂.1, hΘ₂_bd hm₂.2⟩ hw_c₀ (Or.inl hw₂)
        rcases hbp with (hbs₁ | ⟨_, hEq⟩) | (hbs₂ | ⟨_, hEq⟩)
        · exact Set.disjoint_left.mp
            (π.p4_disjoint Θ hΘ Θ₂ hΘ₂ (hΘ₁_eq ▸ hne_Θ) n₁ hn₁_Θ m₂ hm₂) hbs₁ hw₂
        · have hn₁_not_Θ₂ : n₁ ∉ Θ₂ := fun h =>
            hne_Θ (hΘ₁_eq.trans (by
              rcases hΘ₂ with ⟨x₂, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
              exact (connectedComponentIn_eq hn₁_Θ.2).trans
                (connectedComponentIn_eq h).symm))
          exact π.p4_notMem Θ₂ hΘ₂ m₂ hm₂ n₁ (hdom ▸ hn₁_Θ.1) hn₁_not_Θ₂ (hEq ▸ hw₂)
        · exact Set.disjoint_left.mp
            (π.p4_disjoint Θ hΘ Θ₂ hΘ₂ (hΘ₁_eq ▸ hne_Θ) n₂ hn₂_Θ m₂ hm₂) hbs₂ hw₂
        · have hn₂_not_Θ₂ : n₂ ∉ Θ₂ := fun h =>
            hne_Θ (hΘ₁_eq.trans (by
              rcases hΘ₂ with ⟨x₂, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
              exact (connectedComponentIn_eq hn₂_Θ.2).trans
                (connectedComponentIn_eq h).symm))
          exact π.p4_notMem Θ₂ hΘ₂ m₂ hm₂ n₂ (hdom ▸ hn₂_Θ.1) hn₂_not_Θ₂ (hEq ▸ hw₂)
      · by_cases hm₂_n₁ : m₂ = n₁
        · have hΘ₂_eq : Θ₂ = Θ := by
            rcases hΘ₂ with ⟨x₂, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
            exact (connectedComponentIn_eq (hm₂_n₁ ▸ hm₂.2)).trans
              (connectedComponentIn_eq hn₁_Θ.2).symm
          rw [hbs'_other m₁ hm₁_n₁] at hw₁
          rw [hm₂_n₁, hbs'_n₁] at hw₂
          have hw_c₀ : w ∈ (π.cellGraph c₀).vertexSet := hsep.left_le.1 hw₂.1.1
          have hΘ₁_bd : Θ₁ ⊆ bd π.S := by
            rcases hΘ₁ with ⟨x₁, _, rfl⟩; exact connectedComponentIn_subset _ x₁
          have hbp := border_cell_vertex_inter_borderPlus_subset π hc₀ hbd₀ htc₀
            ⟨hm₁.1, hΘ₁_bd hm₁.2⟩ hw_c₀ (Or.inl hw₁)
          rcases hbp with (hbs₁ | ⟨_, hEq⟩) | (hbs₂ | ⟨_, hEq⟩)
          · exact Set.disjoint_left.mp
              (π.p4_disjoint Θ₁ hΘ₁ Θ hΘ (hΘ₂_eq ▸ hne_Θ) m₁ hm₁ n₁ hn₁_Θ) hw₁ hbs₁
          · have hn₁_not_Θ₁ : n₁ ∉ Θ₁ := fun h =>
              hne_Θ (by
                rcases hΘ₁ with ⟨x₁, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
                exact ((connectedComponentIn_eq h).trans
                  (connectedComponentIn_eq hn₁_Θ.2).symm).trans hΘ₂_eq.symm)
            exact π.p4_notMem Θ₁ hΘ₁ m₁ hm₁ n₁ (hdom ▸ hn₁_Θ.1) hn₁_not_Θ₁ (hEq ▸ hw₁)
          · exact Set.disjoint_left.mp
              (π.p4_disjoint Θ₁ hΘ₁ Θ hΘ (hΘ₂_eq ▸ hne_Θ) m₁ hm₁ n₂ hn₂_Θ) hw₁ hbs₂
          · have hn₂_not_Θ₁ : n₂ ∉ Θ₁ := fun h =>
              hne_Θ (by
                rcases hΘ₁ with ⟨x₁, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
                exact ((connectedComponentIn_eq h).trans
                  (connectedComponentIn_eq hn₂_Θ.2).symm).trans hΘ₂_eq.symm)
            exact π.p4_notMem Θ₁ hΘ₁ m₁ hm₁ n₂ (hdom ▸ hn₂_Θ.1) hn₂_not_Θ₁ (hEq ▸ hw₁)
        · rw [hbs'_other m₁ hm₁_n₁] at hw₁
          rw [hbs'_other m₂ hm₂_n₁] at hw₂
          exact Set.disjoint_left.mp (π.p4_disjoint Θ₁ hΘ₁ Θ₂ hΘ₂ hne_Θ m₁ hm₁ m₂ hm₂) hw₁ hw₂
    p4_notMem := fun Θ₁ hΘ₁ m₁ hm₁ m₂ hm₂ hnot => by
      by_cases hm₁_n₁ : m₁ = n₁
      · have hΘ₁_eq : Θ₁ = Θ := by
          rcases hΘ₁ with ⟨x₁, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
          exact (connectedComponentIn_eq (hm₁_n₁ ▸ hm₁.2)).trans
            (connectedComponentIn_eq hn₁_Θ.2).symm
        rw [hm₁_n₁, hbs'_n₁]
        intro hmem
        exact nodeVertex_notMem_border_cellGraph_of_notMem_cuff π hdom hnode_cell
          hΘ hc₀ hc₀_Θ htc₀ (hdom ▸ hm₂) (hΘ₁_eq ▸ hnot) (hsep.left_le.1 hmem.1.1)
      · rw [hbs'_other m₁ hm₁_n₁]
        exact π.p4_notMem Θ₁ hΘ₁ m₁ hm₁ m₂ hm₂ hnot
    p5 := fun d hd hint_d w hwd ⟨d', hd', hne_d, hwd'⟩ => by
      have hd_diff : d ∈ π.Γ.C \ {c₀, c₁} :=
        ⟨hd, by rintro (rfl | rfl) <;> [exact hint_d hbd₀; exact hint_d hbd₁]⟩
      rw [hcellG'_other d hd_diff] at hwd
      have hex_c' : ∃ c' ∈ π.Γ.C, c' ≠ d ∧ w ∈ (π.cellGraph c').vertexSet := by
        by_cases hd'_c₀ : d' = c₀
        · rw [hd'_c₀, hcellG'_c₀] at hwd'
          exact ⟨c₀, hc₀, Ne.symm ( fun h => hd_diff.2 (Or.inl h) ), hsep.right_le.1 hwd'⟩
        · by_cases hd'_c₁ : d' = c₁
          · rw [hd'_c₁, hcellG'_c₁] at hwd'
            rcases hwd' with hwA₁ | hwc₁
            · exact ⟨c₀, hc₀, Ne.symm (fun h => hd_diff.2 (Or.inl h)), hsep.left_le.1 hwA₁⟩
            · exact ⟨c₁, hc₁, Ne.symm (fun h => hd_diff.2 (Or.inr h)), hwc₁⟩
          · have hd'_diff : d' ∈ π.Γ.C \ {c₀, c₁} :=
              ⟨hd', by rintro (rfl | rfl) <;> contradiction⟩
            rw [hcellG'_other d' hd'_diff] at hwd'
            exact ⟨d', hd', hne_d, hwd'⟩
      exact π.p5 d hd hint_d w hwd hex_c'
    p6 := fun d hd hbd_d w hwd ⟨d', hd', hne_d, hwd'⟩ => by
      change ∃ n ∈ tilde d, w ∈ {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n}
      simp_rw [← congrFun hbp_def]
      by_cases hd_c₀ : d = c₀
      · rw [hd_c₀] at hwd hne_d ⊢
        rw [hcellG'_c₀] at hwd
        have hw_c₀ : w ∈ (π.cellGraph c₀).vertexSet := hsep.right_le.1 hwd
        have hw_cases : w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₂ := by
          by_cases hd'_c₁ : d' = c₁
          · rw [hd'_c₁, hcellG'_c₁] at hwd'
            rcases hwd' with hwA₁ | hwc₁
            · exact Or.inl (hbp'_n₁ ▸ ⟨hwA₁, hwd⟩)
            · rcases border_cell_vertex_mem_borderPlus_of_mem_other π hc₀ hbd₀ htc₀
                hw_c₀ hc₁ hc₁_ne_c₀ hwc₁ with hw_n₁ | hw_n₂
              · exact Or.inl (hbp'_n₁ ▸ ⟨hbp₁_A₁ hw_n₁, hwd⟩)
              · exact Or.inr hw_n₂
          · have hd'_diff : d' ∈ π.Γ.C \ {c₀, c₁} :=
              ⟨hd', by rintro (h | h) <;> [exact hne_d h; exact hd'_c₁ h]⟩
            rw [hcellG'_other d' hd'_diff] at hwd'
            rcases border_cell_vertex_mem_borderPlus_of_mem_other π hc₀ hbd₀ htc₀
              hw_c₀ hd' hne_d hwd' with hw_n₁ | hw_n₂
            · exact Or.inl (hbp'_n₁ ▸ ⟨hbp₁_A₁ hw_n₁, hwd⟩)
            · exact Or.inr hw_n₂
        rcases hw_cases with hw₁ | hw₂
        · exact ⟨n₁, htc₀ ▸ Or.inl rfl, hw₁⟩
        · exact ⟨n₂, htc₀ ▸ Or.inr rfl, (hbp'_other n₂ hne.symm) ▸ hw₂⟩
      · by_cases hd_c₁ : d = c₁
        · rw [hd_c₁] at hwd hne_d ⊢
          rw [hcellG'_c₁] at hwd
          have hw_cases : w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₃ := by
            by_cases hd'_c₀ : d' = c₀
            · rw [hd'_c₀, hcellG'_c₀] at hwd'
              rcases hwd with hwA₁ | hwc₁
              · exact Or.inl (hbp'_n₁ ▸ ⟨hwA₁, hwd'⟩)
              · rcases border_cell_vertex_mem_borderPlus_of_mem_other π hc₁ hbd₁ htc₁
                  hwc₁ hc₀ hc₁_ne_c₀.symm (hsep.right_le.1 hwd') with hw_n₁ | hw_n₃
                · exact Or.inl (hbp'_n₁ ▸ ⟨hbp₁_A₁ hw_n₁, hwd'⟩)
                · exact Or.inr hw_n₃
            · have hd'_diff : d' ∈ π.Γ.C \ {c₀, c₁} :=
                ⟨hd', by rintro (h | h) <;> [exact hd'_c₀ h; exact hne_d h]⟩
              rw [hcellG'_other d' hd'_diff] at hwd'
              rcases hwd with hwA₁ | hwc₁
              · rcases hw_c₀_other w (hsep.left_le.1 hwA₁) d' hd'_diff hwd' with
                  hw₁ | hw_n₂ | hw_n₃
                · exact Or.inl hw₁
                · exact Or.inl (hbp'_n₁ ▸ ⟨hwA₁, hbp₂_A₂ hw_n₂⟩)
                · exact Or.inr hw_n₃
              · rcases border_cell_vertex_mem_borderPlus_of_mem_other π hc₁ hbd₁ htc₁
                  hwc₁ hd' hne_d hwd' with hw_n₁ | hw_n₃
                · rcases hw_c₀_other w (hsep.left_le.1 (hbp₁_A₁ hw_n₁)) d' hd'_diff hwd' with
                    hw₁ | hw_n₂ | hw_n₃
                  · exact Or.inl hw₁
                  · exact Or.inl (hbp'_n₁ ▸ ⟨hbp₁_A₁ hw_n₁, hbp₂_A₂ hw_n₂⟩)
                  · exact Or.inr hw_n₃
                · exact Or.inr hw_n₃
          rcases hw_cases with hw₁ | hw₃
          · exact ⟨n₁, htc₁ ▸ Or.inl rfl, hw₁⟩
          · exact ⟨n₃, htc₁ ▸ Or.inr rfl, (hbp'_other n₃ hne₁₃.symm) ▸ hw₃⟩
        · have hd_diff : d ∈ π.Γ.C \ {c₀, c₁} :=
            ⟨hd, by rintro (rfl | rfl) <;> contradiction⟩
          rw [hcellG'_other d hd_diff] at hwd
          have hex_c' : ∃ c' ∈ π.Γ.C, c' ≠ d ∧ w ∈ (π.cellGraph c').vertexSet := by
            by_cases hd'_c₀ : d' = c₀
            · rw [hd'_c₀, hcellG'_c₀] at hwd'
              exact ⟨c₀, hc₀, Ne.symm hd_c₀, hsep.right_le.1 hwd'⟩
            · by_cases hd'_c₁ : d' = c₁
              · rw [hd'_c₁, hcellG'_c₁] at hwd'
                rcases hwd' with hwA₁ | hwc₁
                · exact ⟨c₀, hc₀, Ne.symm hd_c₀, hsep.left_le.1 hwA₁⟩
                · exact ⟨c₁, hc₁, Ne.symm hd_c₁, hwc₁⟩
              · have hd'_diff : d' ∈ π.Γ.C \ {c₀, c₁} :=
                  ⟨hd', by rintro (rfl | rfl) <;> contradiction⟩
                rw [hcellG'_other d' hd'_diff] at hwd'
                exact ⟨d', hd', hne_d, hwd'⟩
          obtain ⟨m, hm_td, hwm⟩ := π.p6 d hd hbd_d w hwd hex_c'
          have hm_ne_n₁ : m ≠ n₁ := fun h =>
            hd_diff.2 ((hd_iff d hd hbd_d).mp (h ▸ hm_td))
          exact ⟨m, hm_td, (hbp'_other m hm_ne_n₁) ▸ hwm⟩
    p7 := by
      intro Θ₁ hΘ₁ m₁ hm₁ m₂ hm₂ m₃ hm₃ m₄ hm₄ hord w hw₁ hw₃
      change w ∈ {v | v ∈ bs' m₂ ∨ m₂ ∈ π.domγ ∧ v = π.nodeVertex m₂} ∨
        w ∈ {v | v ∈ bs' m₄ ∨ m₄ ∈ π.domγ ∧ v = π.nodeVertex m₄}
      have hleft : w ∈ bp' m₁ := (congrFun hbp_def m₁).symm ▸ hw₁
      have hright : w ∈ bp' m₃ := (congrFun hbp_def m₃).symm ▸ hw₃
      simp_rw [← congrFun hbp_def]
      have hp7_aux : ∀ a b c d_n : π.S,
          a ∈ π.Γ.N ∩ Θ₁ → b ∈ π.Γ.N ∩ Θ₁ → c ∈ π.Γ.N ∩ Θ₁ → d_n ∈ π.Γ.N ∩ Θ₁ →
          a ≠ b → b ≠ c → c ≠ d_n → d_n ≠ a →
          GM19.InOrderOn Θ₁ a b c d_n →
          (a = n₁ ∨ b = n₁ ∨ (a ≠ n₁ ∧ b ≠ n₁ ∧ c ≠ n₁ ∧ d_n ≠ n₁)) →
          w ∈ bp' a → w ∈ bp' c →
          w ∈ bp' b ∨ w ∈ bp' d_n := by
        intro a b c d_n ha hb hc hd_n hab hbc hcd hda hord' hcases hwa hwc
        rcases hcases with ha_eq | hb_eq | ⟨ha_ne, hb_ne, hc_ne, hd_ne⟩
        · have hΘ₁_eq : Θ₁ = Θ := by
            rcases hΘ₁ with ⟨x₁, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
            exact (connectedComponentIn_eq (ha_eq ▸ ha.2)).trans
              (connectedComponentIn_eq hn₁_Θ.2).symm
          rw [ha_eq] at hab hda hord' hwa
          rw [hΘ₁_eq] at hb hc hd_n hord'
          have hb_ne : b ≠ n₁ := Ne.symm hab
          have hd_ne : d_n ≠ n₁ := hda
          have hc_ne : c ≠ n₁ := fun h => h_inOrder_eq hab hda (h ▸ hord')
          rw [hbp'_other b hb_ne, hbp'_other d_n hd_ne]
          rw [hbp'_other c hc_ne] at hwc
          rw [hbp'_n₁] at hwa
          have hw_c₀ : w ∈ (π.cellGraph c₀).vertexSet := hsep.left_le.1 hwa.1
          have hbp_u := border_cell_vertex_inter_borderPlus_subset π hc₀ hbd₀ htc₀
            ⟨hc.1, hΘ_bd hc.2⟩ hw_c₀ hwc
          have hn₁_cl : n₁ ∈ closure c₀ := (htc₀ ▸ Or.inl rfl : n₁ ∈ tilde c₀).1
          rcases hbp_u with hw_n₁ | hw_n₂
          · exact π.p7 Θ hΘ n₁ hn₁_Θ b hb c hc d_n hd_n hord' w hw_n₁ hwc
          · have hn₂_cl : n₂ ∈ closure c₀ ∩ Θ := ⟨(htc₀ ▸ Or.inr rfl : n₂ ∈ tilde c₀).1, hn₂_Θ.2⟩
            have hord₂ := inOrderOn_of_mem_closure_border_cell_left π.Γ hΘ hc₀ hc₀_Θ
              hab hbc hcd hda hb.1 hd_n.1 hn₁_cl hord' hn₂_cl
            exact π.p7 Θ hΘ n₂ hn₂_Θ b hb c hc d_n hd_n hord₂ w hw_n₂ hwc
        · have hΘ₁_eq : Θ₁ = Θ := by
            rcases hΘ₁ with ⟨x₁, _, rfl⟩; rcases hΘ with ⟨x₀, _, rfl⟩
            exact (connectedComponentIn_eq (hb_eq ▸ hb.2)).trans
              (connectedComponentIn_eq hn₁_Θ.2).symm
          rw [hb_eq] at hab hbc hord' ⊢
          rw [hΘ₁_eq] at ha hc hd_n hord'
          have ha_ne : a ≠ n₁ := hab
          have hc_ne : c ≠ n₁ := Ne.symm hbc
          have hd_ne : d_n ≠ n₁ := fun h =>
            h_inOrder_eq hbc ha_ne (h ▸ inOrderOn_cyclic hord')
          rw [hbp'_n₁, hbp'_other d_n hd_ne]
          rw [hbp'_other a ha_ne] at hwa
          rw [hbp'_other c hc_ne] at hwc
          have hn₁_cl : n₁ ∈ closure c₀ := (htc₀ ▸ Or.inl rfl : n₁ ∈ tilde c₀).1
          have hn₂_cl : n₂ ∈ closure c₀ ∩ Θ := ⟨(htc₀ ▸ Or.inr rfl : n₂ ∈ tilde c₀).1, hn₂_Θ.2⟩
          have hord₂ := inOrderOn_of_mem_closure_border_cell_mid π.Γ hΘ hc₀ hc₀_Θ
            hab hbc hcd hda ha.1 hc.1 hn₁_cl hord' hn₂_cl
          have hp₁ := π.p7 Θ hΘ a ha n₁ hn₁_Θ c hc d_n hd_n hord' w hwa hwc
          have hp₂ := π.p7 Θ hΘ a ha n₂ hn₂_Θ c hc d_n hd_n hord₂ w hwa hwc
          rcases hp₁ with hw_n₁ | hw_d
          · rcases hp₂ with hw_n₂ | hw_d
            · exact Or.inl ⟨hbp₁_A₁ hw_n₁, hbp₂_A₂ hw_n₂⟩
            · exact Or.inr hw_d
          · exact Or.inr hw_d
        · rw [hbp'_other b hb_ne, hbp'_other d_n hd_ne]
          rw [hbp'_other a ha_ne] at hwa
          rw [hbp'_other c hc_ne] at hwc
          exact π.p7 Θ₁ hΘ₁ a ha b hb c hc d_n hd_n hord' w hwa hwc
      by_cases h12 : m₁ = m₂
      · exact Or.inl (h12 ▸ hleft)
      by_cases h23 : m₂ = m₃
      · exact Or.inl (h23.symm ▸ hright)
      by_cases h34 : m₃ = m₄
      · exact Or.inr (h34 ▸ hright)
      by_cases h41 : m₄ = m₁
      · exact Or.inr (h41.symm ▸ hleft)
      by_cases hm₁_n₁ : m₁ = n₁
      · exact hp7_aux m₁ m₂ m₃ m₄ hm₁ hm₂ hm₃ hm₄ h12 h23 h34 h41 hord (Or.inl hm₁_n₁) hleft hright
      by_cases hm₂_n₁ : m₂ = n₁
      · exact hp7_aux m₁ m₂ m₃ m₄ hm₁ hm₂ hm₃ hm₄ h12 h23 h34 h41 hord
          (Or.inr (Or.inl hm₂_n₁)) hleft hright
      by_cases hm₃_n₁ : m₃ = n₁
      · exact (hp7_aux m₃ m₄ m₁ m₂ hm₃ hm₄ hm₁ hm₂ h34 h41 h12 h23
          (inOrderOn_cyclic2 hord) (Or.inl hm₃_n₁) hright hleft).symm
      by_cases hm₄_n₁ : m₄ = n₁
      · exact (hp7_aux m₃ m₄ m₁ m₂ hm₃ hm₄ hm₁ hm₂ h34 h41 h12 h23
          (inOrderOn_cyclic2 hord) (Or.inr (Or.inl hm₄_n₁)) hright hleft).symm
      exact hp7_aux m₁ m₂ m₃ m₄ hm₁ hm₂ hm₃ hm₄ h12 h23 h34 h41 hord
        (Or.inr (Or.inr ⟨hm₁_n₁, hm₂_n₁, hm₃_n₁, hm₄_n₁⟩)) hleft hright }

private theorem merged_border_cell_portrayal_is_central
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂)
    [T2Space π.S]
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c)
    (hsub_cuff₀ : closure c₀ ∩ bd π.S ⊆ Θ ∧ c₀ ∩ bd π.S = c₀ ∩ Θ ∧ closure c₀ ∩ bd π.S = closure
      c₀ ∩ Θ ∧ tilde c₀ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₀ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (u₀ : π.S)
    (v₀ : π.S)
    (htc₀_uv : tilde c₀ = {u₀, v₀})
    (hL₀ : IsLineWithEnds (closure c₀ ∩ bd π.S) u₀ v₀)
    (hL₀_int : c₀ ∩ bd π.S = (closure c₀ ∩ bd π.S) \ {u₀, v₀})
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hbs₁_sub : π.borderSet n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₁_in_c₀ : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (hlt_q : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).ncard < π.warpAt Θ)
    (hbp₁_A₁ : π.borderPlus n₁ ⊆ A₁.vertexSet)
    (hbp₂_A₂ : π.borderPlus n₂ ⊆ A₂.vertexSet)
    (hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet)
    (c₁ : Set π.S)
    (hc₁ : c₁ ∈ π.Γ.C)
    (hc₁_Θ : (c₁ ∩ Θ).Nonempty)
    (hc₁_ne_c₀ : c₁ ≠ c₀)
    (n₃ : π.S)
    (hne₁₃ : n₁ ≠ n₃)
    (htc₁ : tilde c₁ = {n₁, n₃})
    (hd_iff : ∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty → (n₁ ∈ tilde d ↔ d = c₀ ∨ d = c₁))
    (hneighbors : ∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ → ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m → v ∈
      π.borderPlus n₂ ∨ v ∈ π.borderPlus n₃)
    (hsub_cuff₁ : closure c₁ ∩ bd π.S ⊆ Θ ∧ c₁ ∩ bd π.S = c₁ ∩ Θ ∧ closure c₁ ∩ bd π.S = closure
      c₁ ∩ Θ ∧ tilde c₁ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₁ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₁ : (c₁ ∩ bd π.S).Nonempty)
    (hn₁_tc₁ : n₁ ∈ tilde c₁)
    (hn₃_tc₁ : n₃ ∈ tilde c₁)
    (hn₃_Θ : n₃ ∈ π.Γ.N ∩ Θ)
    (cellG' : Set π.S → Hypergraph α β)
    (bs' : π.S → Set α)
    (bp' : π.S → Set α)
    (hbp_def : bp' = fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n})
    (hcellG'_c₀ : cellG' c₀ = A₂)
    (hcellG'_c₁ : cellG' c₁ = A₁ ∪ π.cellGraph c₁)
    (hcellG'_other : ∀ c ∈ π.Γ.C \ {c₀, c₁}, cellG' c = π.cellGraph c)
    (hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁})
    (hbs'_other : ∀ (n : π.S), n ≠ n₁ → bs' n = π.borderSet n)
    (hbp'_n₁ : bp' n₁ = A₁.vertexSet ∩ A₂.vertexSet)
    (hbp'_other : ∀ (n : π.S), n ≠ n₁ → bp' n = π.borderPlus n)
    (hA₁_le_G : A₁ ≤ G)
    (hcellG'_le : ∀ c ∈ π.Γ.C, cellG' c ≤ G)
    (hw_c₀_other : ∀ w ∈ (π.cellGraph c₀).vertexSet, ∀ d ∈ π.Γ.C \ {c₀, c₁}, w ∈ (π.cellGraph
      d).vertexSet → w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₂ ∨ w ∈ π.borderPlus n₃)
    (h_inOrder_eq : ∀ {Θ₁ : Set π.S} {a b d_n : π.S}, a ≠ b → d_n ≠ a → GM19.InOrderOn Θ₁ a b a
      d_n → False)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    {θ : ℕ}
    {p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯)
    (htrue : π.IsTrue 𝒯)
    (hθ : 4 * p + 5 < θ) :
    let π' : Portrayal G :=
      split_adjacent_border_cells_portrayal (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
        hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀ htc₀_uv
        hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q hbp₁_A₁
        hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors hsub_cuff₁
        hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁ hcellG'_other
          hbs'_n₁
        hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other h_inOrder_eq
    ((π.borderPlus n₁).Finite) →
    ((π.borderPlus n₂).Finite) →
    ((π.borderPlus n₃).Finite) →
    ((A₁.vertexSet ∩ A₂.vertexSet).Finite) →
    ((A₁.vertexSet ∩ A₂.vertexSet).ncard ≤ π.warpAt Θ) →
    (π.warpAt Θ ≤ p) →
    π'.IsCentral 𝒯 := by
  intro π' hbp₁_fin hbp₂_fin hbp₃_fin hinter_fin hinter_le_q hw_le c hc
  by_cases hc_c₀ : c = c₀
  · rw [hc_c₀]
    change ∃ B, (cellG' c₀, B) ∈ 𝒯
    rw [hcellG'_c₀]
    have hatt_sub : attachments G A₂ ⊆
        (π.borderPlus n₁ ∪ π.borderPlus n₂) ∪ (A₁.vertexSet ∩ A₂.vertexSet) := by
      rintro x ⟨hx₂, e, ⟨heG, he_not₂⟩, hinc⟩
      by_cases he₀ : e ∈ (π.cellGraph c₀).edgeSet
      · have he₁ : e ∈ A₁.edgeSet := (hsep.edgeSet_union ▸ he₀).resolve_right he_not₂
        have hinc₀ : (π.cellGraph c₀).Inc e x :=
          (inc_iff_of_le (π.cellGraph_le c₀ hc₀) he₀).2 hinc
        have hinc₁ : A₁.Inc e x := (inc_iff_of_le hsep.left_le he₁).2 hinc₀
        exact Or.inr ⟨A₁.vertex_mem_of_inc hinc₁, hx₂⟩
      · have hx_att₀ : x ∈ attachments G (π.cellGraph c₀) :=
          ⟨hsep.right_le.1 hx₂, e, ⟨heG, he₀⟩, hinc⟩
        have hx_ov := π.attachments_cellGraph_subset_otherVertices hc₀ hx_att₀
        rcases hx_ov.2 with ⟨d, hd, hdc₀, hxd⟩
        exact Or.inl (border_cell_vertex_mem_borderPlus_of_mem_other π hc₀ hbd₀ htc₀
          hx_ov.1 hd hdc₀ hxd)
    have hfin_rhs : ((π.borderPlus n₁ ∪ π.borderPlus n₂) ∪ (A₁.vertexSet ∩ A₂.vertexSet)).Finite
      :=
      (hbp₁_fin.union hbp₂_fin).union hinter_fin
    have hatt_lt : (attachments G A₂).ncard < θ := by
      have h1 := ncard_le_ncard hatt_sub hfin_rhs
      have h2 := ncard_union_le (π.borderPlus n₁ ∪ π.borderPlus n₂) (A₁.vertexSet ∩ A₂.vertexSet)
      have h3 := ncard_union_le (π.borderPlus n₁) (π.borderPlus n₂)
      have hbp₁_c := ncard_borderPlus_le_warpAt_succ π hΘ hn₁_Θ
      have hbp₂_c := ncard_borderPlus_le_warpAt_succ π hΘ hn₂_Θ
      omega
    exact IsSmallWrt.mono h𝒯 (htrue.1 c₀ hc₀) hsep.right_le hatt_lt
  · by_cases hc_c₁ : c = c₁
    · rw [hc_c₁]
      change ∃ B, (cellG' c₁, B) ∈ 𝒯
      rw [hcellG'_c₁]
      have hatt_sub : attachments G (A₁ ∪ π.cellGraph c₁) ⊆
          ((π.borderPlus n₁ ∪ π.borderPlus n₂) ∪ π.borderPlus n₃) ∪
            (A₁.vertexSet ∩ A₂.vertexSet) := by
        refine attachments_union_subset.trans ?_
        rintro x (hxA₁ | hxc₁)
        · rcases hxA₁ with ⟨hx₁, e, ⟨heG, he_not₁⟩, hinc⟩
          by_cases he₀ : e ∈ (π.cellGraph c₀).edgeSet
          · have he₂ : e ∈ A₂.edgeSet := (hsep.edgeSet_union ▸ he₀).resolve_left he_not₁
            have hinc₀ : (π.cellGraph c₀).Inc e x :=
              (inc_iff_of_le (π.cellGraph_le c₀ hc₀) he₀).2 hinc
            have hinc₂ : A₂.Inc e x := (inc_iff_of_le hsep.right_le he₂).2 hinc₀
            exact Or.inr ⟨hx₁, A₂.vertex_mem_of_inc hinc₂⟩
          · have hx_att₀ : x ∈ attachments G (π.cellGraph c₀) :=
              ⟨hsep.left_le.1 hx₁, e, ⟨heG, he₀⟩, hinc⟩
            have hx_ov := π.attachments_cellGraph_subset_otherVertices hc₀ hx_att₀
            rcases hx_ov.2 with ⟨d, hd, hdc₀, hxd⟩
            exact Or.inl (Or.inl (border_cell_vertex_mem_borderPlus_of_mem_other π hc₀ hbd₀ htc₀
              hx_ov.1 hd hdc₀ hxd))
        · have hx_ov := π.attachments_cellGraph_subset_otherVertices hc₁ hxc₁
          rcases hx_ov.2 with ⟨d, hd, hdc₁, hxd⟩
          rcases border_cell_vertex_mem_borderPlus_of_mem_other π hc₁ hbd₁ htc₁
            hx_ov.1 hd hdc₁ hxd with hx_n₁ | hx_n₃
          · exact Or.inl (Or.inl (Or.inl hx_n₁))
          · exact Or.inl (Or.inr hx_n₃)
      have hfin_rhs : (((π.borderPlus n₁ ∪ π.borderPlus n₂) ∪ π.borderPlus n₃) ∪
          (A₁.vertexSet ∩ A₂.vertexSet)).Finite :=
        ((hbp₁_fin.union hbp₂_fin).union hbp₃_fin).union hinter_fin
      have hatt_lt : (attachments G (A₁ ∪ π.cellGraph c₁)).ncard < θ := by
        have h1 := ncard_le_ncard hatt_sub hfin_rhs
        have h2 := ncard_union_le ((π.borderPlus n₁ ∪ π.borderPlus n₂) ∪ π.borderPlus n₃)
          (A₁.vertexSet ∩ A₂.vertexSet)
        have h3 := ncard_union_le (π.borderPlus n₁ ∪ π.borderPlus n₂) (π.borderPlus n₃)
        have h4 := ncard_union_le (π.borderPlus n₁) (π.borderPlus n₂)
        have hbp₁_c := ncard_borderPlus_le_warpAt_succ π hΘ hn₁_Θ
        have hbp₂_c := ncard_borderPlus_le_warpAt_succ π hΘ hn₂_Θ
        have hbp₃_c := ncard_borderPlus_le_warpAt_succ π hΘ hn₃_Θ
        omega
      have hle_union : A₁ ∪ π.cellGraph c₁ ≤ π.cellGraph c₀ ∪ π.cellGraph c₁ :=
        (le_iff_of_le (union_le hA₁_le_G (π.cellGraph_le c₁ hc₁))
          (union_le (π.cellGraph_le c₀ hc₀) (π.cellGraph_le c₁ hc₁))).mpr
          ⟨union_subset_union_left _ hsep.left_le.1, union_subset_union_left _ hsep.left_le.2⟩
      exact theorem_4_1_ii h𝒯 (htrue.1 c₀ hc₀) (htrue.1 c₁ hc₁) hle_union hatt_lt
    · change ∃ B, (cellG' c, B) ∈ 𝒯
      rw [hcellG'_other c ⟨hc, by rintro (h | h) <;> [exact hc_c₀ h; exact hc_c₁ h]⟩]
      exact htrue.1 c hc

private theorem warp_bound_of_reduced_border_cell
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂)
    [T2Space π.S]
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c)
    (hsub_cuff₀ : closure c₀ ∩ bd π.S ⊆ Θ ∧ c₀ ∩ bd π.S = c₀ ∩ Θ ∧ closure c₀ ∩ bd π.S = closure
      c₀ ∩ Θ ∧ tilde c₀ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₀ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (u₀ : π.S)
    (v₀ : π.S)
    (htc₀_uv : tilde c₀ = {u₀, v₀})
    (hL₀ : IsLineWithEnds (closure c₀ ∩ bd π.S) u₀ v₀)
    (hL₀_int : c₀ ∩ bd π.S = (closure c₀ ∩ bd π.S) \ {u₀, v₀})
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hbs₁_sub : π.borderSet n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₁_in_c₀ : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (hlt_q : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).ncard < π.warpAt Θ)
    (hbp₁_A₁ : π.borderPlus n₁ ⊆ A₁.vertexSet)
    (hbp₂_A₂ : π.borderPlus n₂ ⊆ A₂.vertexSet)
    (hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet)
    (c₁ : Set π.S)
    (hc₁ : c₁ ∈ π.Γ.C)
    (hc₁_Θ : (c₁ ∩ Θ).Nonempty)
    (hc₁_ne_c₀ : c₁ ≠ c₀)
    (n₃ : π.S)
    (hne₁₃ : n₁ ≠ n₃)
    (htc₁ : tilde c₁ = {n₁, n₃})
    (hd_iff : ∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty → (n₁ ∈ tilde d ↔ d = c₀ ∨ d = c₁))
    (hneighbors : ∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ → ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m → v ∈
      π.borderPlus n₂ ∨ v ∈ π.borderPlus n₃)
    (hsub_cuff₁ : closure c₁ ∩ bd π.S ⊆ Θ ∧ c₁ ∩ bd π.S = c₁ ∩ Θ ∧ closure c₁ ∩ bd π.S = closure
      c₁ ∩ Θ ∧ tilde c₁ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₁ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₁ : (c₁ ∩ bd π.S).Nonempty)
    (hn₁_tc₁ : n₁ ∈ tilde c₁)
    (hn₃_tc₁ : n₃ ∈ tilde c₁)
    (hn₃_Θ : n₃ ∈ π.Γ.N ∩ Θ)
    (cellG' : Set π.S → Hypergraph α β)
    (bs' : π.S → Set α)
    (bp' : π.S → Set α)
    (hbp_def : bp' = fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n})
    (hcellG'_c₀ : cellG' c₀ = A₂)
    (hcellG'_c₁ : cellG' c₁ = A₁ ∪ π.cellGraph c₁)
    (hcellG'_other : ∀ c ∈ π.Γ.C \ {c₀, c₁}, cellG' c = π.cellGraph c)
    (hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁})
    (hbs'_other : ∀ (n : π.S), n ≠ n₁ → bs' n = π.borderSet n)
    (hbp'_n₁ : bp' n₁ = A₁.vertexSet ∩ A₂.vertexSet)
    (hbp'_other : ∀ (n : π.S), n ≠ n₁ → bp' n = π.borderPlus n)
    (hA₁_le_G : A₁ ≤ G)
    (hcellG'_le : ∀ c ∈ π.Γ.C, cellG' c ≤ G)
    (hw_c₀_other : ∀ w ∈ (π.cellGraph c₀).vertexSet, ∀ d ∈ π.Γ.C \ {c₀, c₁}, w ∈ (π.cellGraph
      d).vertexSet → w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₂ ∨ w ∈ π.borderPlus n₃)
    (h_inOrder_eq : ∀ {Θ₁ : Set π.S} {a b d_n : π.S}, a ≠ b → d_n ≠ a → GM19.InOrderOn Θ₁ a b a
      d_n → False) :
    let π' : Portrayal G :=
      split_adjacent_border_cells_portrayal (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
        hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀ htc₀_uv
        hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q hbp₁_A₁
        hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors hsub_cuff₁
        hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁ hcellG'_other
          hbs'_n₁
        hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other h_inOrder_eq
    ((π.borderSet n₂).ncard ≤ π.warpAt Θ) →
    ((bs' n₁).ncard ≤ π.warpAt Θ) →
    ((bp' n₁).ncard ≤ π.warpAt Θ) →
    π'.cellWarp c₀ ≤ π.warpAt Θ := by
  intro π' hbs₂_le hbs'₁_le hbp'₁_le
  subst bp'
  let bp' : π.S → Set α := fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n}
  have hbound : (bp' n₁).ncard ≤ π.warpAt Θ := hbp'₁_le
  refine csInf_le (OrderBot.bddBelow _) ?_
  intro u₁ hu₁ u₂ hu₂ hu_ne
  change (bs' u₁).ncard ≤ π.warpAt Θ ∧ (bs' u₂).ncard ≤ π.warpAt Θ ∧
    ((bp' u₁).ncard = π.warpAt Θ + 1 → (bp' u₂).ncard = π.warpAt Θ + 1 → _)
  rw [htc₀] at hu₁ hu₂
  rcases hu₁ with h1 | h1 <;> rcases hu₂ with h2 | h2
  · exact (hu_ne (h1.trans h2.symm)).elim
  · rw [h1, h2, hbs'_other n₂ hne.symm]
    refine ⟨hbs'₁_le, hbs₂_le, fun hbp1 _ => (Nat.not_succ_le_self _ (hbp1 ▸ hbound)).elim⟩
  · rw [h1, h2, hbs'_other n₂ hne.symm]
    refine ⟨hbs₂_le, hbs'₁_le, fun _ hbp2 => (Nat.not_succ_le_self _ (hbp2 ▸ hbound)).elim⟩
  · exact (hu_ne (h1.trans h2.symm)).elim

private theorem warp_bound_of_enlarged_border_cell
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂)
    [T2Space π.S]
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c)
    (hsub_cuff₀ : closure c₀ ∩ bd π.S ⊆ Θ ∧ c₀ ∩ bd π.S = c₀ ∩ Θ ∧ closure c₀ ∩ bd π.S = closure
      c₀ ∩ Θ ∧ tilde c₀ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₀ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (u₀ : π.S)
    (v₀ : π.S)
    (htc₀_uv : tilde c₀ = {u₀, v₀})
    (hL₀ : IsLineWithEnds (closure c₀ ∩ bd π.S) u₀ v₀)
    (hL₀_int : c₀ ∩ bd π.S = (closure c₀ ∩ bd π.S) \ {u₀, v₀})
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hbs₁_sub : π.borderSet n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₁_in_c₀ : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (hlt_q : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).ncard < π.warpAt Θ)
    (hbp₁_A₁ : π.borderPlus n₁ ⊆ A₁.vertexSet)
    (hbp₂_A₂ : π.borderPlus n₂ ⊆ A₂.vertexSet)
    (hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet)
    (c₁ : Set π.S)
    (hc₁ : c₁ ∈ π.Γ.C)
    (hc₁_Θ : (c₁ ∩ Θ).Nonempty)
    (hc₁_ne_c₀ : c₁ ≠ c₀)
    (n₃ : π.S)
    (hne₁₃ : n₁ ≠ n₃)
    (htc₁ : tilde c₁ = {n₁, n₃})
    (hd_iff : ∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty → (n₁ ∈ tilde d ↔ d = c₀ ∨ d = c₁))
    (hneighbors : ∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ → ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m → v ∈
      π.borderPlus n₂ ∨ v ∈ π.borderPlus n₃)
    (hsub_cuff₁ : closure c₁ ∩ bd π.S ⊆ Θ ∧ c₁ ∩ bd π.S = c₁ ∩ Θ ∧ closure c₁ ∩ bd π.S = closure
      c₁ ∩ Θ ∧ tilde c₁ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₁ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₁ : (c₁ ∩ bd π.S).Nonempty)
    (hn₁_tc₁ : n₁ ∈ tilde c₁)
    (hn₃_tc₁ : n₃ ∈ tilde c₁)
    (hn₃_Θ : n₃ ∈ π.Γ.N ∩ Θ)
    (cellG' : Set π.S → Hypergraph α β)
    (bs' : π.S → Set α)
    (bp' : π.S → Set α)
    (hbp_def : bp' = fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n})
    (hcellG'_c₀ : cellG' c₀ = A₂)
    (hcellG'_c₁ : cellG' c₁ = A₁ ∪ π.cellGraph c₁)
    (hcellG'_other : ∀ c ∈ π.Γ.C \ {c₀, c₁}, cellG' c = π.cellGraph c)
    (hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁})
    (hbs'_other : ∀ (n : π.S), n ≠ n₁ → bs' n = π.borderSet n)
    (hbp'_n₁ : bp' n₁ = A₁.vertexSet ∩ A₂.vertexSet)
    (hbp'_other : ∀ (n : π.S), n ≠ n₁ → bp' n = π.borderPlus n)
    (hA₁_le_G : A₁ ≤ G)
    (hcellG'_le : ∀ c ∈ π.Γ.C, cellG' c ≤ G)
    (hw_c₀_other : ∀ w ∈ (π.cellGraph c₀).vertexSet, ∀ d ∈ π.Γ.C \ {c₀, c₁}, w ∈ (π.cellGraph
      d).vertexSet → w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₂ ∨ w ∈ π.borderPlus n₃)
    (h_inOrder_eq : ∀ {Θ₁ : Set π.S} {a b d_n : π.S}, a ≠ b → d_n ≠ a → GM19.InOrderOn Θ₁ a b a
      d_n → False) :
    let π' : Portrayal G :=
      split_adjacent_border_cells_portrayal (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
        hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀ htc₀_uv
        hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q hbp₁_A₁
        hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors hsub_cuff₁
        hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁ hcellG'_other
          hbs'_n₁
        hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other h_inOrder_eq
    ((π.borderSet n₃).ncard ≤ π.warpAt Θ) →
    ((bs' n₁).ncard ≤ π.warpAt Θ) →
    ((bp' n₁).ncard ≤ π.warpAt Θ) →
    π'.cellWarp c₁ ≤ π.warpAt Θ := by
  intro π' hbs₃_le hbs'₁_le hbp'₁_le
  subst bp'
  let bp' : π.S → Set α := fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n}
  have hbound : (bp' n₁).ncard ≤ π.warpAt Θ := hbp'₁_le
  refine csInf_le (OrderBot.bddBelow _) ?_
  intro u₁ hu₁ u₂ hu₂ hu_ne
  change (bs' u₁).ncard ≤ π.warpAt Θ ∧ (bs' u₂).ncard ≤ π.warpAt Θ ∧
    ((bp' u₁).ncard = π.warpAt Θ + 1 → (bp' u₂).ncard = π.warpAt Θ + 1 → _)
  rw [htc₁] at hu₁ hu₂
  rcases hu₁ with h1 | h1 <;> rcases hu₂ with h2 | h2
  · exact (hu_ne (h1.trans h2.symm)).elim
  · rw [h1, h2, hbs'_other n₃ hne₁₃.symm]
    refine ⟨hbs'₁_le, hbs₃_le, fun hbp1 _ => (Nat.not_succ_le_self _ (hbp1 ▸ hbound)).elim⟩
  · rw [h1, h2, hbs'_other n₃ hne₁₃.symm]
    refine ⟨hbs₃_le, hbs'₁_le, fun _ hbp2 => (Nat.not_succ_le_self _ (hbp2 ▸ hbound)).elim⟩
  · exact (hu_ne (h1.trans h2.symm)).elim

private theorem warp_unchanged_away_from_merged_cells
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂)
    [T2Space π.S]
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c)
    (hsub_cuff₀ : closure c₀ ∩ bd π.S ⊆ Θ ∧ c₀ ∩ bd π.S = c₀ ∩ Θ ∧ closure c₀ ∩ bd π.S = closure
      c₀ ∩ Θ ∧ tilde c₀ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₀ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (u₀ : π.S)
    (v₀ : π.S)
    (htc₀_uv : tilde c₀ = {u₀, v₀})
    (hL₀ : IsLineWithEnds (closure c₀ ∩ bd π.S) u₀ v₀)
    (hL₀_int : c₀ ∩ bd π.S = (closure c₀ ∩ bd π.S) \ {u₀, v₀})
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hbs₁_sub : π.borderSet n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₁_in_c₀ : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (hlt_q : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).ncard < π.warpAt Θ)
    (hbp₁_A₁ : π.borderPlus n₁ ⊆ A₁.vertexSet)
    (hbp₂_A₂ : π.borderPlus n₂ ⊆ A₂.vertexSet)
    (hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet)
    (c₁ : Set π.S)
    (hc₁ : c₁ ∈ π.Γ.C)
    (hc₁_Θ : (c₁ ∩ Θ).Nonempty)
    (hc₁_ne_c₀ : c₁ ≠ c₀)
    (n₃ : π.S)
    (hne₁₃ : n₁ ≠ n₃)
    (htc₁ : tilde c₁ = {n₁, n₃})
    (hd_iff : ∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty → (n₁ ∈ tilde d ↔ d = c₀ ∨ d = c₁))
    (hneighbors : ∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ → ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m → v ∈
      π.borderPlus n₂ ∨ v ∈ π.borderPlus n₃)
    (hsub_cuff₁ : closure c₁ ∩ bd π.S ⊆ Θ ∧ c₁ ∩ bd π.S = c₁ ∩ Θ ∧ closure c₁ ∩ bd π.S = closure
      c₁ ∩ Θ ∧ tilde c₁ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₁ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₁ : (c₁ ∩ bd π.S).Nonempty)
    (hn₁_tc₁ : n₁ ∈ tilde c₁)
    (hn₃_tc₁ : n₃ ∈ tilde c₁)
    (hn₃_Θ : n₃ ∈ π.Γ.N ∩ Θ)
    (cellG' : Set π.S → Hypergraph α β)
    (bs' : π.S → Set α)
    (bp' : π.S → Set α)
    (hbp_def : bp' = fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n})
    (hcellG'_c₀ : cellG' c₀ = A₂)
    (hcellG'_c₁ : cellG' c₁ = A₁ ∪ π.cellGraph c₁)
    (hcellG'_other : ∀ c ∈ π.Γ.C \ {c₀, c₁}, cellG' c = π.cellGraph c)
    (hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁})
    (hbs'_other : ∀ (n : π.S), n ≠ n₁ → bs' n = π.borderSet n)
    (hbp'_n₁ : bp' n₁ = A₁.vertexSet ∩ A₂.vertexSet)
    (hbp'_other : ∀ (n : π.S), n ≠ n₁ → bp' n = π.borderPlus n)
    (hA₁_le_G : A₁ ≤ G)
    (hcellG'_le : ∀ c ∈ π.Γ.C, cellG' c ≤ G)
    (hw_c₀_other : ∀ w ∈ (π.cellGraph c₀).vertexSet, ∀ d ∈ π.Γ.C \ {c₀, c₁}, w ∈ (π.cellGraph
      d).vertexSet → w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₂ ∨ w ∈ π.borderPlus n₃)
    (h_inOrder_eq : ∀ {Θ₁ : Set π.S} {a b d_n : π.S}, a ≠ b → d_n ≠ a → GM19.InOrderOn Θ₁ a b a
      d_n → False) :
    let π' : Portrayal G :=
      split_adjacent_border_cells_portrayal (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
        hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀ htc₀_uv
        hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q hbp₁_A₁
        hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors hsub_cuff₁
        hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁ hcellG'_other
          hbs'_n₁
        hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other h_inOrder_eq
    ∀ d ∈ π.Γ.C \ {c₀, c₁}, (d ∩ bd π.S).Nonempty → π'.cellWarp d = π.cellWarp d := by
  intro π'
  subst bp'
  let bp' : π.S → Set α := fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n}
  rintro d ⟨hd, hd_not⟩ hbd_d
  change sInf {p | π'.CellWarpLE d p} = sInf {p | π.CellWarpLE d p}
  congr 1; ext q
  change (∀ u₁ ∈ tilde d, ∀ u₂ ∈ tilde d, u₁ ≠ u₂ → _) ↔
    (∀ u₁ ∈ tilde d, ∀ u₂ ∈ tilde d, u₁ ≠ u₂ → _)
  refine forall₂_congr fun u₁ hu₁ => forall₂_congr fun u₂ hu₂ => imp_congr_right fun _ => ?_
  have hu₁_ne : u₁ ≠ n₁ := fun h => hd_not ((hd_iff d hd hbd_d).mp (h ▸ hu₁))
  have hu₂_ne : u₂ ≠ n₁ := fun h => hd_not ((hd_iff d hd hbd_d).mp (h ▸ hu₂))
  change ((bs' u₁).ncard ≤ q ∧ (bs' u₂).ncard ≤ q ∧
    ((bp' u₁).ncard = q + 1 → (bp' u₂).ncard = q + 1 →
      Portrayal.LinkagePairs (cellG' d).skeleton (bp' u₁) (bp' u₂) (q + 1)
        (π.nodeVertex u₁) (π.nodeVertex u₂))) ↔ _
  have hbp₁ : bp' u₁ = π.borderPlus u₁ := hbp'_other u₁ hu₁_ne
  have hbp₂ : bp' u₂ = π.borderPlus u₂ := hbp'_other u₂ hu₂_ne
  rw [hbp₁, hbp₂, hbs'_other u₁ hu₁_ne, hbs'_other u₂ hu₂_ne, hcellG'_other d ⟨hd, hd_not⟩]

private theorem warp_does_not_increase_on_cuffs
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂)
    [T2Space π.S]
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c)
    (hsub_cuff₀ : closure c₀ ∩ bd π.S ⊆ Θ ∧ c₀ ∩ bd π.S = c₀ ∩ Θ ∧ closure c₀ ∩ bd π.S = closure
      c₀ ∩ Θ ∧ tilde c₀ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₀ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (u₀ : π.S)
    (v₀ : π.S)
    (htc₀_uv : tilde c₀ = {u₀, v₀})
    (hL₀ : IsLineWithEnds (closure c₀ ∩ bd π.S) u₀ v₀)
    (hL₀_int : c₀ ∩ bd π.S = (closure c₀ ∩ bd π.S) \ {u₀, v₀})
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hbs₁_sub : π.borderSet n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₁_in_c₀ : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (hlt_q : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).ncard < π.warpAt Θ)
    (hbp₁_A₁ : π.borderPlus n₁ ⊆ A₁.vertexSet)
    (hbp₂_A₂ : π.borderPlus n₂ ⊆ A₂.vertexSet)
    (hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet)
    (c₁ : Set π.S)
    (hc₁ : c₁ ∈ π.Γ.C)
    (hc₁_Θ : (c₁ ∩ Θ).Nonempty)
    (hc₁_ne_c₀ : c₁ ≠ c₀)
    (n₃ : π.S)
    (hne₁₃ : n₁ ≠ n₃)
    (htc₁ : tilde c₁ = {n₁, n₃})
    (hd_iff : ∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty → (n₁ ∈ tilde d ↔ d = c₀ ∨ d = c₁))
    (hneighbors : ∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ → ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m → v ∈
      π.borderPlus n₂ ∨ v ∈ π.borderPlus n₃)
    (hsub_cuff₁ : closure c₁ ∩ bd π.S ⊆ Θ ∧ c₁ ∩ bd π.S = c₁ ∩ Θ ∧ closure c₁ ∩ bd π.S = closure
      c₁ ∩ Θ ∧ tilde c₁ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₁ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₁ : (c₁ ∩ bd π.S).Nonempty)
    (hn₁_tc₁ : n₁ ∈ tilde c₁)
    (hn₃_tc₁ : n₃ ∈ tilde c₁)
    (hn₃_Θ : n₃ ∈ π.Γ.N ∩ Θ)
    (cellG' : Set π.S → Hypergraph α β)
    (bs' : π.S → Set α)
    (bp' : π.S → Set α)
    (hbp_def : bp' = fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n})
    (hcellG'_c₀ : cellG' c₀ = A₂)
    (hcellG'_c₁ : cellG' c₁ = A₁ ∪ π.cellGraph c₁)
    (hcellG'_other : ∀ c ∈ π.Γ.C \ {c₀, c₁}, cellG' c = π.cellGraph c)
    (hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁})
    (hbs'_other : ∀ (n : π.S), n ≠ n₁ → bs' n = π.borderSet n)
    (hbp'_n₁ : bp' n₁ = A₁.vertexSet ∩ A₂.vertexSet)
    (hbp'_other : ∀ (n : π.S), n ≠ n₁ → bp' n = π.borderPlus n)
    (hA₁_le_G : A₁ ≤ G)
    (hcellG'_le : ∀ c ∈ π.Γ.C, cellG' c ≤ G)
    (hw_c₀_other : ∀ w ∈ (π.cellGraph c₀).vertexSet, ∀ d ∈ π.Γ.C \ {c₀, c₁}, w ∈ (π.cellGraph
      d).vertexSet → w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₂ ∨ w ∈ π.borderPlus n₃)
    (h_inOrder_eq : ∀ {Θ₁ : Set π.S} {a b d_n : π.S}, a ≠ b → d_n ≠ a → GM19.InOrderOn Θ₁ a b a
      d_n → False) :
    let π' : Portrayal G :=
      split_adjacent_border_cells_portrayal (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
        hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀ htc₀_uv
        hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q hbp₁_A₁
        hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors hsub_cuff₁
        hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁ hcellG'_other
          hbs'_n₁
        hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other h_inOrder_eq
    (π'.cellWarp c₀ ≤ π.warpAt Θ) →
    (π'.cellWarp c₁ ≤ π.warpAt Θ) →
    (∀ d ∈ π.Γ.C \ {c₀, c₁}, (d ∩ bd π.S).Nonempty → π'.cellWarp d = π.cellWarp d) →
    ∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' ≤ π.warpAt Θ' := by
  intro π' hcw'_c₀ hcw'_c₁ hcw'_other Θ' hΘ'
  have hΘ'_bd : Θ' ⊆ bd π.S := by
    rcases hΘ' with ⟨x', _, rfl⟩; exact connectedComponentIn_subset _ x'
  rw [π'.warpAt_le_iff]
  intro d hd hd_Θ'
  by_cases hd_c₀ : d = c₀
  · rw [hd_c₀] at hd_Θ' ⊢
    have hΘ'_eq : Θ' = Θ := hsub_cuff₀.2.2.2.2 Θ' hΘ' hd_Θ'
    rw [hΘ'_eq]; exact hcw'_c₀
  · by_cases hd_c₁ : d = c₁
    · rw [hd_c₁] at hd_Θ' ⊢
      have hΘ'_eq : Θ' = Θ := hsub_cuff₁.2.2.2.2 Θ' hΘ' hd_Θ'
      rw [hΘ'_eq]; exact hcw'_c₁
    · have hd_diff : d ∈ π.Γ.C \ {c₀, c₁} :=
        ⟨hd, by rintro (h | h) <;> [exact hd_c₀ h; exact hd_c₁ h]⟩
      have hbd_d : (d ∩ bd π.S).Nonempty := hd_Θ'.mono (inter_subset_inter_right _ hΘ'_bd)
      rw [hcw'_other d hd_diff hbd_d]
      exact π.cellWarp_le_warpAt hd hd_Θ'

private theorem redundancy_forces_warp_preservation
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂)
    [T2Space π.S]
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c)
    (hsub_cuff₀ : closure c₀ ∩ bd π.S ⊆ Θ ∧ c₀ ∩ bd π.S = c₀ ∩ Θ ∧ closure c₀ ∩ bd π.S = closure
      c₀ ∩ Θ ∧ tilde c₀ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₀ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (u₀ : π.S)
    (v₀ : π.S)
    (htc₀_uv : tilde c₀ = {u₀, v₀})
    (hL₀ : IsLineWithEnds (closure c₀ ∩ bd π.S) u₀ v₀)
    (hL₀_int : c₀ ∩ bd π.S = (closure c₀ ∩ bd π.S) \ {u₀, v₀})
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hbs₁_sub : π.borderSet n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₁_in_c₀ : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (hlt_q : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).ncard < π.warpAt Θ)
    (hbp₁_A₁ : π.borderPlus n₁ ⊆ A₁.vertexSet)
    (hbp₂_A₂ : π.borderPlus n₂ ⊆ A₂.vertexSet)
    (hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet)
    (c₁ : Set π.S)
    (hc₁ : c₁ ∈ π.Γ.C)
    (hc₁_Θ : (c₁ ∩ Θ).Nonempty)
    (hc₁_ne_c₀ : c₁ ≠ c₀)
    (n₃ : π.S)
    (hne₁₃ : n₁ ≠ n₃)
    (htc₁ : tilde c₁ = {n₁, n₃})
    (hd_iff : ∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty → (n₁ ∈ tilde d ↔ d = c₀ ∨ d = c₁))
    (hneighbors : ∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ → ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m → v ∈
      π.borderPlus n₂ ∨ v ∈ π.borderPlus n₃)
    (hsub_cuff₁ : closure c₁ ∩ bd π.S ⊆ Θ ∧ c₁ ∩ bd π.S = c₁ ∩ Θ ∧ closure c₁ ∩ bd π.S = closure
      c₁ ∩ Θ ∧ tilde c₁ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₁ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₁ : (c₁ ∩ bd π.S).Nonempty)
    (hn₁_tc₁ : n₁ ∈ tilde c₁)
    (hn₃_tc₁ : n₃ ∈ tilde c₁)
    (hn₃_Θ : n₃ ∈ π.Γ.N ∩ Θ)
    (cellG' : Set π.S → Hypergraph α β)
    (bs' : π.S → Set α)
    (bp' : π.S → Set α)
    (hbp_def : bp' = fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n})
    (hcellG'_c₀ : cellG' c₀ = A₂)
    (hcellG'_c₁ : cellG' c₁ = A₁ ∪ π.cellGraph c₁)
    (hcellG'_other : ∀ c ∈ π.Γ.C \ {c₀, c₁}, cellG' c = π.cellGraph c)
    (hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁})
    (hbs'_other : ∀ (n : π.S), n ≠ n₁ → bs' n = π.borderSet n)
    (hbp'_n₁ : bp' n₁ = A₁.vertexSet ∩ A₂.vertexSet)
    (hbp'_other : ∀ (n : π.S), n ≠ n₁ → bp' n = π.borderPlus n)
    (hA₁_le_G : A₁ ≤ G)
    (hcellG'_le : ∀ c ∈ π.Γ.C, cellG' c ≤ G)
    (hw_c₀_other : ∀ w ∈ (π.cellGraph c₀).vertexSet, ∀ d ∈ π.Γ.C \ {c₀, c₁}, w ∈ (π.cellGraph
      d).vertexSet → w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₂ ∨ w ∈ π.borderPlus n₃)
    (h_inOrder_eq : ∀ {Θ₁ : Set π.S} {a b d_n : π.S}, a ≠ b → d_n ≠ a → GM19.InOrderOn Θ₁ a b a
      d_n → False)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (htrue : π.IsTrue 𝒯) :
    let π' : Portrayal G :=
      split_adjacent_border_cells_portrayal (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
        hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀ htc₀_uv
        hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q hbp₁_A₁
        hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors hsub_cuff₁
        hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁ hcellG'_other
          hbs'_n₁
        hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other h_inOrder_eq
    (π'.IsCentral 𝒯) →
    (∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' ≤ π.warpAt Θ') →
    ∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' = π.warpAt Θ' := by
  intro π' hπ'_central hwarpAt_le Θ' hΘ'
  refine le_antisymm (hwarpAt_le Θ' hΘ') ?_
  by_contra hlt
  have hsimpler : π'.IsSimpler π := by
    right
    refine ⟨Homeomorph.refl π.S, ?_, Θ', hΘ', ?_⟩
    · intro Θ'' hΘ''
      rw [Homeomorph.refl_apply, image_id]
      exact hwarpAt_le Θ'' hΘ''
    · rw [Homeomorph.refl_apply, image_id]
      exact lt_of_not_ge hlt
  exact htrue.2.1 π' hπ'_central hsimpler

private theorem preserved_cuff_warps_preserve_maximum
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂)
    [T2Space π.S]
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c)
    (hsub_cuff₀ : closure c₀ ∩ bd π.S ⊆ Θ ∧ c₀ ∩ bd π.S = c₀ ∩ Θ ∧ closure c₀ ∩ bd π.S = closure
      c₀ ∩ Θ ∧ tilde c₀ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₀ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (u₀ : π.S)
    (v₀ : π.S)
    (htc₀_uv : tilde c₀ = {u₀, v₀})
    (hL₀ : IsLineWithEnds (closure c₀ ∩ bd π.S) u₀ v₀)
    (hL₀_int : c₀ ∩ bd π.S = (closure c₀ ∩ bd π.S) \ {u₀, v₀})
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hbs₁_sub : π.borderSet n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₁_in_c₀ : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (hlt_q : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).ncard < π.warpAt Θ)
    (hbp₁_A₁ : π.borderPlus n₁ ⊆ A₁.vertexSet)
    (hbp₂_A₂ : π.borderPlus n₂ ⊆ A₂.vertexSet)
    (hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet)
    (c₁ : Set π.S)
    (hc₁ : c₁ ∈ π.Γ.C)
    (hc₁_Θ : (c₁ ∩ Θ).Nonempty)
    (hc₁_ne_c₀ : c₁ ≠ c₀)
    (n₃ : π.S)
    (hne₁₃ : n₁ ≠ n₃)
    (htc₁ : tilde c₁ = {n₁, n₃})
    (hd_iff : ∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty → (n₁ ∈ tilde d ↔ d = c₀ ∨ d = c₁))
    (hneighbors : ∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ → ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m → v ∈
      π.borderPlus n₂ ∨ v ∈ π.borderPlus n₃)
    (hsub_cuff₁ : closure c₁ ∩ bd π.S ⊆ Θ ∧ c₁ ∩ bd π.S = c₁ ∩ Θ ∧ closure c₁ ∩ bd π.S = closure
      c₁ ∩ Θ ∧ tilde c₁ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₁ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₁ : (c₁ ∩ bd π.S).Nonempty)
    (hn₁_tc₁ : n₁ ∈ tilde c₁)
    (hn₃_tc₁ : n₃ ∈ tilde c₁)
    (hn₃_Θ : n₃ ∈ π.Γ.N ∩ Θ)
    (cellG' : Set π.S → Hypergraph α β)
    (bs' : π.S → Set α)
    (bp' : π.S → Set α)
    (hbp_def : bp' = fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n})
    (hcellG'_c₀ : cellG' c₀ = A₂)
    (hcellG'_c₁ : cellG' c₁ = A₁ ∪ π.cellGraph c₁)
    (hcellG'_other : ∀ c ∈ π.Γ.C \ {c₀, c₁}, cellG' c = π.cellGraph c)
    (hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁})
    (hbs'_other : ∀ (n : π.S), n ≠ n₁ → bs' n = π.borderSet n)
    (hbp'_n₁ : bp' n₁ = A₁.vertexSet ∩ A₂.vertexSet)
    (hbp'_other : ∀ (n : π.S), n ≠ n₁ → bp' n = π.borderPlus n)
    (hA₁_le_G : A₁ ≤ G)
    (hcellG'_le : ∀ c ∈ π.Γ.C, cellG' c ≤ G)
    (hw_c₀_other : ∀ w ∈ (π.cellGraph c₀).vertexSet, ∀ d ∈ π.Γ.C \ {c₀, c₁}, w ∈ (π.cellGraph
      d).vertexSet → w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₂ ∨ w ∈ π.borderPlus n₃)
    (h_inOrder_eq : ∀ {Θ₁ : Set π.S} {a b d_n : π.S}, a ≠ b → d_n ≠ a → GM19.InOrderOn Θ₁ a b a
      d_n → False) :
    let π' : Portrayal G :=
      split_adjacent_border_cells_portrayal (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
        hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀ htc₀_uv
        hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q hbp₁_A₁
        hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors hsub_cuff₁
        hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁ hcellG'_other
          hbs'_n₁
        hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other h_inOrder_eq
    (∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' = π.warpAt Θ') →
    π'.warp = π.warp := by
  intro π' hwarpAt_eq
  classical
  change (if (cuffs π.S).Nonempty then max 1 (sSup {p | ∃ Θ' ∈ cuffs π.S, p
    = π'.warpAt Θ'}) else 1) =
    (if (cuffs π.S).Nonempty then max 1 (sSup {p | ∃ Θ' ∈ cuffs π.S, p = π.warpAt Θ'}) else 1)
  congr 2; congr 1; ext q
  exact exists_congr fun Θ' => and_congr_right fun hΘ' => by rw [hwarpAt_eq Θ' hΘ']

private theorem preserved_warp_preserves_simplicity
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂)
    [T2Space π.S]
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c)
    (hsub_cuff₀ : closure c₀ ∩ bd π.S ⊆ Θ ∧ c₀ ∩ bd π.S = c₀ ∩ Θ ∧ closure c₀ ∩ bd π.S = closure
      c₀ ∩ Θ ∧ tilde c₀ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₀ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (u₀ : π.S)
    (v₀ : π.S)
    (htc₀_uv : tilde c₀ = {u₀, v₀})
    (hL₀ : IsLineWithEnds (closure c₀ ∩ bd π.S) u₀ v₀)
    (hL₀_int : c₀ ∩ bd π.S = (closure c₀ ∩ bd π.S) \ {u₀, v₀})
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hbs₁_sub : π.borderSet n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₁_in_c₀ : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (hlt_q : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).ncard < π.warpAt Θ)
    (hbp₁_A₁ : π.borderPlus n₁ ⊆ A₁.vertexSet)
    (hbp₂_A₂ : π.borderPlus n₂ ⊆ A₂.vertexSet)
    (hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet)
    (c₁ : Set π.S)
    (hc₁ : c₁ ∈ π.Γ.C)
    (hc₁_Θ : (c₁ ∩ Θ).Nonempty)
    (hc₁_ne_c₀ : c₁ ≠ c₀)
    (n₃ : π.S)
    (hne₁₃ : n₁ ≠ n₃)
    (htc₁ : tilde c₁ = {n₁, n₃})
    (hd_iff : ∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty → (n₁ ∈ tilde d ↔ d = c₀ ∨ d = c₁))
    (hneighbors : ∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ → ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m → v ∈
      π.borderPlus n₂ ∨ v ∈ π.borderPlus n₃)
    (hsub_cuff₁ : closure c₁ ∩ bd π.S ⊆ Θ ∧ c₁ ∩ bd π.S = c₁ ∩ Θ ∧ closure c₁ ∩ bd π.S = closure
      c₁ ∩ Θ ∧ tilde c₁ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₁ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₁ : (c₁ ∩ bd π.S).Nonempty)
    (hn₁_tc₁ : n₁ ∈ tilde c₁)
    (hn₃_tc₁ : n₃ ∈ tilde c₁)
    (hn₃_Θ : n₃ ∈ π.Γ.N ∩ Θ)
    (cellG' : Set π.S → Hypergraph α β)
    (bs' : π.S → Set α)
    (bp' : π.S → Set α)
    (hbp_def : bp' = fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n})
    (hcellG'_c₀ : cellG' c₀ = A₂)
    (hcellG'_c₁ : cellG' c₁ = A₁ ∪ π.cellGraph c₁)
    (hcellG'_other : ∀ c ∈ π.Γ.C \ {c₀, c₁}, cellG' c = π.cellGraph c)
    (hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁})
    (hbs'_other : ∀ (n : π.S), n ≠ n₁ → bs' n = π.borderSet n)
    (hbp'_n₁ : bp' n₁ = A₁.vertexSet ∩ A₂.vertexSet)
    (hbp'_other : ∀ (n : π.S), n ≠ n₁ → bp' n = π.borderPlus n)
    (hA₁_le_G : A₁ ≤ G)
    (hcellG'_le : ∀ c ∈ π.Γ.C, cellG' c ≤ G)
    (hw_c₀_other : ∀ w ∈ (π.cellGraph c₀).vertexSet, ∀ d ∈ π.Γ.C \ {c₀, c₁}, w ∈ (π.cellGraph
      d).vertexSet → w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₂ ∨ w ∈ π.borderPlus n₃)
    (h_inOrder_eq : ∀ {Θ₁ : Set π.S} {a b d_n : π.S}, a ≠ b → d_n ≠ a → GM19.InOrderOn Θ₁ a b a
      d_n → False) :
    let π' : Portrayal G :=
      split_adjacent_border_cells_portrayal (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
        hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀ htc₀_uv
        hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q hbp₁_A₁
        hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors hsub_cuff₁
        hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁ hcellG'_other
          hbs'_n₁
        hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other h_inOrder_eq
    (∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' = π.warpAt Θ') →
    (π'.warp = π.warp) →
    ∀ {G' : Hypergraph α β} (π'' : Portrayal G'), π''.IsSimpler π' ↔ π''.IsSimpler π := by
  intro π' hwarpAt_eq hwarp'_eq G' π''
  change ((IsSimplerThan π''.S π.S ∧ π''.warp ≤ π'.warp) ∨
    ∃ ψ : π''.S ≃ₜ π.S, (∀ Θ' ∈ cuffs π''.S, π''.warpAt Θ' ≤ π'.warpAt (ψ '' Θ')) ∧
      ∃ Θ' ∈ cuffs π''.S, π''.warpAt Θ' < π'.warpAt (ψ '' Θ')) ↔
    ((IsSimplerThan π''.S π.S ∧ π''.warp ≤ π.warp) ∨
    ∃ ψ : π''.S ≃ₜ π.S, (∀ Θ' ∈ cuffs π''.S, π''.warpAt Θ' ≤ π.warpAt (ψ '' Θ')) ∧
      ∃ Θ' ∈ cuffs π''.S, π''.warpAt Θ' < π.warpAt (ψ '' Θ'))
  rw [hwarp'_eq]
  refine or_congr Iff.rfl (exists_congr fun ψ => ?_)
  have hψ_cuff : ∀ Θ' ∈ cuffs π''.S, ψ '' Θ' ∈ cuffs π.S :=
    fun Θ' hΘ' => image_cuff_mem_cuffs ψ hΘ'
  refine and_congr (forall₂_congr fun Θ' hΘ' => ?_)
    (exists_congr fun Θ' => and_congr_right fun hΘ' => ?_)
  · rw [hwarpAt_eq (ψ '' Θ') (hψ_cuff Θ' hΘ')]
  · rw [hwarpAt_eq (ψ '' Θ') (hψ_cuff Θ' hΘ')]

private theorem preserved_cuff_warp_preserves_resemblance
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {c₀ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S)
    (hc₀ : c₀ ∈ π.Γ.C)
    (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ : π.S}
    {n₂ : π.S}
    (hn₁_tc : n₁ ∈ tilde c₀)
    (hn₂_tc : n₂ ∈ tilde c₀)
    (hne : n₁ ≠ n₂)
    [T2Space π.S]
    (hdom : π.domγ = π.Γ.N)
    (hnode_cell : ∀ n ∈ π.Γ.N, ∃ c ∈ π.Γ.C, n ∈ tilde c)
    (hsub_cuff₀ : closure c₀ ∩ bd π.S ⊆ Θ ∧ c₀ ∩ bd π.S = c₀ ∩ Θ ∧ closure c₀ ∩ bd π.S = closure
      c₀ ∩ Θ ∧ tilde c₀ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₀ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₀ : (c₀ ∩ bd π.S).Nonempty)
    (u₀ : π.S)
    (v₀ : π.S)
    (htc₀_uv : tilde c₀ = {u₀, v₀})
    (hL₀ : IsLineWithEnds (closure c₀ ∩ bd π.S) u₀ v₀)
    (hL₀_int : c₀ ∩ bd π.S = (closure c₀ ∩ bd π.S) \ {u₀, v₀})
    (htc₀ : tilde c₀ = {n₁, n₂})
    (hΘ_bd : Θ ⊆ bd π.S)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ)
    (hbs₁_sub : π.borderSet n₁ ⊆ (π.cellGraph c₀).vertexSet)
    (hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet)
    (hn₁_in_c₀ : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hsep : (π.cellGraph c₀).IsSeparation A₁ A₂)
    (hlt_q : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).ncard < π.warpAt Θ)
    (hbp₁_A₁ : π.borderPlus n₁ ⊆ A₁.vertexSet)
    (hbp₂_A₂ : π.borderPlus n₂ ⊆ A₂.vertexSet)
    (hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet)
    (c₁ : Set π.S)
    (hc₁ : c₁ ∈ π.Γ.C)
    (hc₁_Θ : (c₁ ∩ Θ).Nonempty)
    (hc₁_ne_c₀ : c₁ ≠ c₀)
    (n₃ : π.S)
    (hne₁₃ : n₁ ≠ n₃)
    (htc₁ : tilde c₁ = {n₁, n₃})
    (hd_iff : ∀ d ∈ π.Γ.C, (d ∩ bd π.S).Nonempty → (n₁ ∈ tilde d ↔ d = c₀ ∨ d = c₁))
    (hneighbors : ∀ m ∈ π.Γ.N ∩ Θ, m ≠ n₁ → ∀ v ∈ π.borderPlus n₁, v ∈ π.borderPlus m → v ∈
      π.borderPlus n₂ ∨ v ∈ π.borderPlus n₃)
    (hsub_cuff₁ : closure c₁ ∩ bd π.S ⊆ Θ ∧ c₁ ∩ bd π.S = c₁ ∩ Θ ∧ closure c₁ ∩ bd π.S = closure
      c₁ ∩ Θ ∧ tilde c₁ ⊆ π.Γ.N ∩ Θ ∧ ∀ Θ' ∈ cuffs π.S, (c₁ ∩ Θ').Nonempty → Θ' = Θ)
    (hbd₁ : (c₁ ∩ bd π.S).Nonempty)
    (hn₁_tc₁ : n₁ ∈ tilde c₁)
    (hn₃_tc₁ : n₃ ∈ tilde c₁)
    (hn₃_Θ : n₃ ∈ π.Γ.N ∩ Θ)
    (cellG' : Set π.S → Hypergraph α β)
    (bs' : π.S → Set α)
    (bp' : π.S → Set α)
    (hbp_def : bp' = fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n})
    (hcellG'_c₀ : cellG' c₀ = A₂)
    (hcellG'_c₁ : cellG' c₁ = A₁ ∪ π.cellGraph c₁)
    (hcellG'_other : ∀ c ∈ π.Γ.C \ {c₀, c₁}, cellG' c = π.cellGraph c)
    (hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁})
    (hbs'_other : ∀ (n : π.S), n ≠ n₁ → bs' n = π.borderSet n)
    (hbp'_n₁ : bp' n₁ = A₁.vertexSet ∩ A₂.vertexSet)
    (hbp'_other : ∀ (n : π.S), n ≠ n₁ → bp' n = π.borderPlus n)
    (hA₁_le_G : A₁ ≤ G)
    (hcellG'_le : ∀ c ∈ π.Γ.C, cellG' c ≤ G)
    (hw_c₀_other : ∀ w ∈ (π.cellGraph c₀).vertexSet, ∀ d ∈ π.Γ.C \ {c₀, c₁}, w ∈ (π.cellGraph
      d).vertexSet → w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₂ ∨ w ∈ π.borderPlus n₃)
    (h_inOrder_eq : ∀ {Θ₁ : Set π.S} {a b d_n : π.S}, a ≠ b → d_n ≠ a → GM19.InOrderOn Θ₁ a b a
      d_n → False) :
    let π' : Portrayal G :=
      split_adjacent_border_cells_portrayal (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
        hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀ htc₀_uv
        hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q hbp₁_A₁
        hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors hsub_cuff₁
        hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁ hcellG'_other
          hbs'_n₁
        hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other h_inOrder_eq
    (∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' = π.warpAt Θ') →
    ∀ (π'' : Portrayal G), π''.Resembles π' ↔ π''.Resembles π := by
  intro π' hwarpAt_eq π''
  refine exists_congr fun ψ => forall₂_congr fun Θ' hΘ' => ?_
  rw [hwarpAt_eq (ψ '' Θ') (image_cuff_mem_cuffs ψ hΘ')]

private theorem reassigned_cell_graphs_le
    {α β : Type*} {G : Hypergraph α β} (π : Portrayal G)
    {c₀ c₁ : Set π.S} (hc₁ : c₁ ∈ π.Γ.C) {A₁ A₂ : Hypergraph α β}
    {cellG' : Set π.S → Hypergraph α β} (hcellG'_c₀ : cellG' c₀ = A₂)
    (hcellG'_c₁ : cellG' c₁ = A₁ ∪ π.cellGraph c₁)
    (hcellG'_other : ∀ c ∈ π.Γ.C \ {c₀, c₁}, cellG' c = π.cellGraph c)
    (hA₁_le_G : A₁ ≤ G) (hA₂_le_G : A₂ ≤ G) :
    ∀ c ∈ π.Γ.C, cellG' c ≤ G := by
  intro c hc
  by_cases hc_c₀ : c = c₀
  · rw [hc_c₀, hcellG'_c₀]; exact hA₂_le_G
  · by_cases hc_c₁ : c = c₁
    · rw [hc_c₁, hcellG'_c₁]; exact union_le hA₁_le_G (π.cellGraph_le c₁ hc₁)
    · rw [hcellG'_other c ⟨hc, by rintro (rfl | rfl) <;> contradiction⟩]
      exact π.cellGraph_le c hc

private theorem repeated_node_not_in_order
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G) :
    ∀ {Θ₁ : Set π.S} {a b d_n : π.S}, a ≠ b → d_n ≠ a → GM19.InOrderOn Θ₁ a b a d_n → False := by
  intro Θ₁ a b d_n hab hda hord
  obtain ⟨f, t₁, t₂, t₃, t₄, ht12, ht23, ht34, ht41, h1, h2, h3, h4⟩ := hord
  have hlt12 : t₁ < t₂ := lt_of_le_of_ne ht12 fun h => hab (h1.symm.trans (h ▸ h2))
  have hlt41 : t₄ < t₁ + 2 * Real.pi := lt_of_le_of_ne ht41 fun h =>
    hda (h4.symm.trans ((h ▸ cuffPoint_add_two_pi f t₁).trans h1))
  have h13 : GM19.cuffPoint f t₁ = GM19.cuffPoint f t₃ := h1.trans h3.symm
  have hEq := cuffPoint_injOn_Ico f t₁ ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ h13
  linarith

private theorem separator_size_le_warp
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {n₁ : π.S}
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hlt_q : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).ncard < π.warpAt Θ)
    (hinter_fin : (A₁.vertexSet ∩ A₂.vertexSet).Finite) :
    (A₁.vertexSet ∩ A₂.vertexSet).ncard ≤ π.warpAt Θ := by
  have hsub : A₁.vertexSet ∩ A₂.vertexSet ⊆
      insert (π.nodeVertex n₁) ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}) := by
    intro x hx
    by_cases hEq : x = π.nodeVertex n₁
    · exact Or.inl hEq
    · exact Or.inr ⟨hx, hEq⟩
  have hfin_diff : ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁}).Finite :=
    hinter_fin.subset sdiff_subset
  have h1 := ncard_le_ncard hsub (hfin_diff.insert _)
  have h2 := ncard_insert_le (π.nodeVertex n₁) ((A₁ ∩ A₂).vertexSet \ {π.nodeVertex n₁})
  omega

private theorem split_border_plus_eq_separator
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {n₁ : π.S}
    (hdom : π.domγ = π.Γ.N)
    (hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ)
    (A₁ : Hypergraph α β)
    (A₂ : Hypergraph α β)
    (hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet)
    (bs' : π.S → Set α)
    (hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁}) :
    (fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n}) n₁ = A₁.vertexSet ∩ A₂.vertexSet
      := by
  ext x
  simp only [hbs'_n₁, mem_ofPred_eq, mem_sdiff, mem_inter_iff, mem_singleton_iff,
    hdom ▸ hn₁_Θ.1, true_and]
  constructor
  · rintro (⟨hx, _⟩ | rfl)
    · exact hx
    · exact hn₁_mem_inter
  · intro hx
    by_cases hEq : x = π.nodeVertex n₁
    · exact Or.inr hEq
    · exact Or.inl ⟨hx, hEq⟩

theorem claim_9_6
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {Θ c₀ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hc₀ : c₀ ∈ π.Γ.C) (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ n₂ : π.S} (hn₁_tc : n₁ ∈ tilde c₀) (hn₂_tc : n₂ ∈ tilde c₀) (hne : n₁ ≠ n₂) :
    HasDisjointPathsAvoiding (π.cellGraph c₀) (π.borderSet n₁) (π.borderPlus n₂)
      {π.nodeVertex n₁} (π.warpAt Θ) := by
  classical
  have : T2Space π.S := π.isSurface.2.1
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof
      h𝒯 π htrue hred hwarp hθ
  obtain ⟨_, _, hnode_cell⟩ :=
    theorem_8_2_proof
      h𝒯 π htrue hred hwarp hθ
  have hsub_cuff₀ := π.Γ.border_cell_subset_cuff hc₀ hΘ hc₀_Θ
  have hbd₀ : (c₀ ∩ bd π.S).Nonempty := hsub_cuff₀.2.1 ▸ hc₀_Θ
  obtain ⟨u₀, v₀, huv_ne, htc₀_uv, hL₀, hL₀_int, _, _⟩ := π.Γ.border_cell_exists_ends hc₀ hbd₀
  have htc₀ : tilde c₀ = {n₁, n₂} := by
    refine (eq_of_subset_of_ncard_le ?_ ?_ (π.Γ.finite_tilde_cell hc₀)).symm
    · rintro x (rfl | rfl) <;> assumption
    · rw [htc₀_uv, ncard_pair huv_ne, ncard_pair hne]
  have hΘ_bd : Θ ⊆ bd π.S :=
    let ⟨x, _, heq⟩ := hΘ
    heq ▸ connectedComponentIn_subset (bd π.S) x
  have hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 hn₁_tc
  have hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 hn₂_tc
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S := ⟨hn₁_Θ.1, hΘ_bd hn₁_Θ.2⟩
  have hbs₁_sub : π.borderSet n₁ ⊆ (π.cellGraph c₀).vertexSet :=
    π.p3_subset c₀ hc₀ hbd₀ n₁ hn₁_tc
  have hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet :=
    π.borderPlus_subset_cellGraph hc₀ hbd₀ hn₂_tc
  have hn₁_in_c₀ : π.nodeVertex n₁ ∈ (π.cellGraph c₀).vertexSet :=
    π.p2 c₀ hc₀ n₁ ⟨hn₁_tc, hdom ▸ hn₁_Θ.1⟩
  rw [hasDisjointPathsAvoiding_iff_forall_isSeparation (π.cellGraph c₀)
    hbs₁_sub hbp₂_sub (singleton_subset_iff.mpr hn₁_in_c₀) (π.warpAt Θ)]
  intro A₁ A₂ hsep hA₁_sub hA₂_sub
  by_contra hlt_q
  push Not at hlt_q
  have hbp₁_A₁ : π.borderPlus n₁ ⊆ A₁.vertexSet := by
    rintro x (hx | ⟨_, rfl⟩)
    · exact hA₁_sub (Or.inl hx)
    · exact hA₁_sub (Or.inr rfl)
  have hbp₂_A₂ : π.borderPlus n₂ ⊆ A₂.vertexSet :=
    fun x hx => hA₂_sub (Or.inl hx)
  have hn₁_mem_inter : π.nodeVertex n₁ ∈ A₁.vertexSet ∩ A₂.vertexSet :=
    ⟨hA₁_sub (Or.inr rfl), hA₂_sub (Or.inr rfl)⟩
  obtain ⟨c₁, hc₁, hc₁_Θ, hc₁_ne_c₀, n₃, hne₁₃, htc₁, hd_iff, hneighbors⟩ :=
    exists_other_border_cell_of_mem_tilde π hΘ hc₀ hc₀_Θ hne htc₀
  have hsub_cuff₁ := π.Γ.border_cell_subset_cuff hc₁ hΘ hc₁_Θ
  have hbd₁ : (c₁ ∩ bd π.S).Nonempty := hsub_cuff₁.2.1 ▸ hc₁_Θ
  have hn₁_tc₁ : n₁ ∈ tilde c₁ := htc₁ ▸ Or.inl rfl
  have hn₃_tc₁ : n₃ ∈ tilde c₁ := htc₁ ▸ Or.inr rfl
  have hn₃_Θ : n₃ ∈ π.Γ.N ∩ Θ := hsub_cuff₁.2.2.2.1 hn₃_tc₁
  let cellG' : Set π.S → Hypergraph α β := fun c =>
    if c = c₀ then A₂ else if c = c₁ then A₁ ∪ π.cellGraph c₁ else π.cellGraph c
  let bs' : π.S → Set α := fun n =>
    if n = n₁ then (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁} else π.borderSet n
  let bp' : π.S → Set α := fun n =>
    {v | v ∈ bs' n ∨ (n ∈ π.domγ ∧ v = π.nodeVertex n)}
  have hbp_def : bp' = fun n => {v | v ∈ bs' n ∨ n ∈ π.domγ ∧ v = π.nodeVertex n} := rfl
  have hcellG'_c₀ : cellG' c₀ = A₂ := by simp [cellG']
  have hcellG'_c₁ : cellG' c₁ = A₁ ∪ π.cellGraph c₁ := by simp [cellG', hc₁_ne_c₀]
  have hcellG'_other : ∀ c ∈ π.Γ.C \ {c₀, c₁}, cellG' c = π.cellGraph c := by
    rintro c ⟨_, hc_not⟩
    have hc₀' : c ≠ c₀ := fun h => hc_not (Or.inl h)
    have hc₁' : c ≠ c₁ := fun h => hc_not (Or.inr h)
    simp [cellG', hc₀', hc₁']
  have hbs'_n₁ : bs' n₁ = (A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁} := by simp [bs']
  have hbs'_other : ∀ n ≠ n₁, bs' n = π.borderSet n := fun n hn => by simp [bs', hn]
  have hbp'_n₁ : bp' n₁ = A₁.vertexSet ∩ A₂.vertexSet :=
    split_border_plus_eq_separator π hdom hn₁_Θ A₁ A₂ hn₁_mem_inter bs' hbs'_n₁
  have hbp'_other : ∀ n ≠ n₁, bp' n = π.borderPlus n :=
    fun n hn => by simp [bp', Portrayal.borderPlus, hbs'_other n hn]
  have hA₁_le_G : A₁ ≤ G := hsep.left_le.trans (π.cellGraph_le c₀ hc₀)
  have hA₂_le_G : A₂ ≤ G := hsep.right_le.trans (π.cellGraph_le c₀ hc₀)
  have hcellG'_le : ∀ c ∈ π.Γ.C, cellG' c ≤ G :=
    reassigned_cell_graphs_le π hc₁ hcellG'_c₀ hcellG'_c₁ hcellG'_other hA₁_le_G hA₂_le_G
  have hw_c₀_other : ∀ w ∈ (π.cellGraph c₀).vertexSet,
      ∀ d ∈ π.Γ.C \ {c₀, c₁}, w ∈ (π.cellGraph d).vertexSet →
      w ∈ bp' n₁ ∨ w ∈ π.borderPlus n₂ ∨ w ∈ π.borderPlus n₃ := by
    exact other_cell_vertices_on_boundary (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
      hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hne hdom hsub_cuff₀ hbd₀ htc₀ hΘ_bd hn₁_Θ hn₂_Θ hn₁_bd
      hbs₁_sub hn₁_in_c₀ A₁ A₂ hA₁_sub hA₂_sub hlt_q hbp₁_A₁ hn₁_mem_inter c₁ hc₁_Θ n₃ hne₁₃ htc₁
      hd_iff hneighbors hsub_cuff₁ hn₁_tc₁ hn₃_Θ bs' bp' hbs'_n₁ hbs'_other hbp'_n₁ hbp'_other
  have h_inOrder_eq := @repeated_node_not_in_order α β G π
  let π' : Portrayal G :=
    split_adjacent_border_cells_portrayal (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
      hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀ htc₀_uv
      hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q hbp₁_A₁
      hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors hsub_cuff₁ hbd₁
      hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁ hcellG'_other hbs'_n₁
        hbs'_other
      hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other h_inOrder_eq
  have hbp₁_fin : (π.borderPlus n₁).Finite :=
    (π.cellGraph c₀).vertexSet_finite.subset (π.borderPlus_subset_cellGraph hc₀ hbd₀ hn₁_tc)
  have hbp₂_fin : (π.borderPlus n₂).Finite :=
    (π.cellGraph c₀).vertexSet_finite.subset hbp₂_sub
  have hbp₃_fin : (π.borderPlus n₃).Finite :=
    (π.cellGraph c₁).vertexSet_finite.subset (π.borderPlus_subset_cellGraph hc₁ hbd₁ hn₃_tc₁)
  have hinter_fin : (A₁.vertexSet ∩ A₂.vertexSet).Finite :=
    A₁.vertexSet_finite.subset inter_subset_left
  have hinter_le_q : (A₁.vertexSet ∩ A₂.vertexSet).ncard ≤ π.warpAt Θ := by
    exact separator_size_le_warp π A₁ A₂ hlt_q hinter_fin
  have hw_le : π.warpAt Θ ≤ p := (π.warpAt_le_warp hΘ).trans hwarp
  have hπ'_central : π'.IsCentral 𝒯 := by
    exact merged_border_cell_portrayal_is_central (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀)
      hΘ hc₀ hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀
      htc₀_uv hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q
      hbp₁_A₁ hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors
      hsub_cuff₁ hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁
      hcellG'_other hbs'_n₁ hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other
      h_inOrder_eq (𝒯 := 𝒯) (θ := θ) (p := p) h𝒯 htrue hθ hbp₁_fin hbp₂_fin hbp₃_fin hinter_fin
      hinter_le_q hw_le
  have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hbs₂_le : (π.borderSet n₂).ncard ≤ π.warpAt Θ :=
    π.ncard_borderSet_le_warpAt hΘ hΘ_arc hn₂_Θ
  have hbs₃_le : (π.borderSet n₃).ncard ≤ π.warpAt Θ :=
    π.ncard_borderSet_le_warpAt hΘ hΘ_arc hn₃_Θ
  have hbs'₁_le : (bs' n₁).ncard ≤ π.warpAt Θ := by
    rw [hbs'_n₁]
    change ((A₁.vertexSet ∩ A₂.vertexSet) \ {π.nodeVertex n₁}).ncard < π.warpAt Θ at hlt_q
    omega
  have hbp'₁_le : (bp' n₁).ncard ≤ π.warpAt Θ := by
    rw [hbp'_n₁]; exact hinter_le_q
  have hcw'_c₀ : π'.cellWarp c₀ ≤ π.warpAt Θ := by
    exact warp_bound_of_reduced_border_cell (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
      hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀ htc₀_uv
      hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q hbp₁_A₁
      hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors hsub_cuff₁ hbd₁
      hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁ hcellG'_other hbs'_n₁
      hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other h_inOrder_eq
      hbs₂_le hbs'₁_le hbp'₁_le
  have hcw'_c₁ : π'.cellWarp c₁ ≤ π.warpAt Θ := by
    exact warp_bound_of_enlarged_border_cell (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ
      hc₀ hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀
      htc₀_uv hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q
      hbp₁_A₁ hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors
      hsub_cuff₁ hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁
      hcellG'_other hbs'_n₁ hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other
      h_inOrder_eq hbs₃_le hbs'₁_le hbp'₁_le
  have hcw'_other : ∀ d ∈ π.Γ.C \ {c₀, c₁}, (d ∩ bd π.S).Nonempty →
      π'.cellWarp d = π.cellWarp d := by
    exact warp_unchanged_away_from_merged_cells (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ
      hc₀ hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀
      htc₀_uv hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q
      hbp₁_A₁ hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors
      hsub_cuff₁ hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁
      hcellG'_other hbs'_n₁ hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other
      h_inOrder_eq
  have hwarpAt_le : ∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' ≤ π.warpAt Θ' := by
    exact warp_does_not_increase_on_cuffs (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ hc₀
      hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀ htc₀_uv
      hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q hbp₁_A₁
      hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors hsub_cuff₁ hbd₁
      hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁ hcellG'_other hbs'_n₁
      hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other h_inOrder_eq hcw'_c₀ hcw'_c₁
      hcw'_other
  have hwarpAt_eq : ∀ Θ' ∈ cuffs π.S, π'.warpAt Θ' = π.warpAt Θ' := by
    exact redundancy_forces_warp_preservation (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ
      hc₀ hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀
      htc₀_uv hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q
      hbp₁_A₁ hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors
      hsub_cuff₁ hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁
      hcellG'_other hbs'_n₁ hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other
      h_inOrder_eq (𝒯 := 𝒯) htrue hπ'_central hwarpAt_le
  have hwarp'_eq : π'.warp = π.warp := by
    exact preserved_cuff_warps_preserve_maximum (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ
      hc₀ hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀
      htc₀_uv hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q
      hbp₁_A₁ hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors
      hsub_cuff₁ hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁
      hcellG'_other hbs'_n₁ hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other
      h_inOrder_eq hwarpAt_eq
  have hsimpler_iff : ∀ {G' : Hypergraph α β} (π'' : Portrayal G'),
      π''.IsSimpler π' ↔ π''.IsSimpler π := by
    exact preserved_warp_preserves_simplicity (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ := c₀) hΘ
      hc₀ hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀ v₀
      htc₀_uv hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q
      hbp₁_A₁ hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors
      hsub_cuff₁ hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁
      hcellG'_other hbs'_n₁ hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other
      h_inOrder_eq hwarpAt_eq hwarp'_eq
  have htruer_iff : ∀ π'' : Portrayal G, π''.IsTruer π' ↔ π''.IsTruer π := fun _ => Iff.rfl
  have hres_iff : ∀ π'' : Portrayal G, π''.Resembles π' ↔ π''.Resembles π := by
    exact preserved_cuff_warp_preserves_resemblance (α := α) (β := β) (G := G) π (Θ := Θ) (c₀ :=
      c₀) hΘ hc₀ hc₀_Θ (n₁ := n₁) (n₂ := n₂) hn₁_tc hn₂_tc hne hdom hnode_cell hsub_cuff₀ hbd₀ u₀
      v₀ htc₀_uv hL₀ hL₀_int htc₀ hΘ_bd hn₁_Θ hn₂_Θ hbs₁_sub hbp₂_sub hn₁_in_c₀ A₁ A₂ hsep hlt_q
      hbp₁_A₁ hbp₂_A₂ hn₁_mem_inter c₁ hc₁ hc₁_Θ hc₁_ne_c₀ n₃ hne₁₃ htc₁ hd_iff hneighbors
      hsub_cuff₁ hbd₁ hn₁_tc₁ hn₃_tc₁ hn₃_Θ cellG' bs' bp' hbp_def hcellG'_c₀ hcellG'_c₁
      hcellG'_other hbs'_n₁ hbs'_other hbp'_n₁ hbp'_other hA₁_le_G hcellG'_le hw_c₀_other
      h_inOrder_eq hwarpAt_eq
  have hπ'_true : π'.IsTrue 𝒯 :=
    ⟨hπ'_central,
      fun π'' hcent hsimp => htrue.2.1 π'' hcent ((hsimpler_iff π'').mp hsimp),
      fun π'' hcent htr hres =>
        htrue.2.2 π'' hcent ((htruer_iff π'').mp htr) ((hres_iff π'').mp hres)⟩
  have hπ'_red : π'.IsRedundant 𝒯 θ (2 * p + 3) :=
    ⟨hred.1, fun Z hZ hZ_le π'' hcent hsimp =>
      hred.2 Z hZ hZ_le π'' hcent ((hsimpler_iff π'').mp hsimp)⟩
  have hπ'_warp : π'.warp ≤ p := hwarp'_eq ▸ hwarp
  have h94 := theorem_9_4_proof h𝒯 π' hπ'_true hπ'_red hπ'_warp hθ hΘ hn₁_Θ
  change (bs' n₁).ncard = π'.warpAt Θ at h94
  rw [hbs'_n₁, hwarpAt_eq Θ hΘ] at h94
  exact hlt_q.ne h94

/-- **Graph Minors XVII, (9.6)** (page 186):
"Let $c_0$ be a cell bordering a cuff $\Theta$ with $\tilde{c}_0 = \{n_1, n_2\}$, and let $\pi$
have warp $q$ at $\Theta$. Then there are $q$ mutually vertex-disjoint paths of $\alpha(c_0)^*$
from $\beta(n_1)$ to $\beta(n_2)$, each containing neither $\gamma(n_1)$ nor $\gamma(n_2)$." -/
theorem theorem_9_6_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {Θ c₀ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hc₀ : c₀ ∈ π.Γ.C) (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ n₂ : π.S} (hn₁_tc : n₁ ∈ tilde c₀) (hn₂_tc : n₂ ∈ tilde c₀) (hne : n₁ ≠ n₂) :
    ∃ L : Fin (π.warpAt Θ) →
        PathFromTo (π.cellGraph c₀).skeleton (π.borderSet n₁) (π.borderSet n₂),
      (Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support}) ∧
      ∀ i, π.nodeVertex n₁ ∉ (L i).walk.support ∧ π.nodeVertex n₂ ∉ (L i).walk.support := by
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof
      h𝒯 π htrue hred hwarp hθ
  have hsub_cuff₀ := π.Γ.border_cell_subset_cuff hc₀ hΘ hc₀_Θ
  have hbd₀ : (c₀ ∩ bd π.S).Nonempty := hsub_cuff₀.2.1 ▸ hc₀_Θ
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 hn₁_tc
  have hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 hn₂_tc
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S := ⟨hn₁_Θ.1, hΘ_bd hn₁_Θ.2⟩
  have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S := ⟨hn₂_Θ.1, hΘ_bd hn₂_Θ.2⟩
  have hbs₁_eq : (π.borderSet n₁).ncard = π.warpAt Θ :=
    theorem_9_4_proof h𝒯 π htrue hred hwarp hθ hΘ hn₁_Θ
  have hbs₂_eq : (π.borderSet n₂).ncard = π.warpAt Θ :=
    theorem_9_4_proof h𝒯 π htrue hred hwarp hθ hΘ hn₂_Θ
  have hbp₁_sub : π.borderPlus n₁ ⊆ (π.cellGraph c₀).vertexSet :=
    π.borderPlus_subset_cellGraph hc₀ hbd₀ hn₁_tc
  have hbp₂_sub : π.borderPlus n₂ ⊆ (π.cellGraph c₀).vertexSet :=
    π.borderPlus_subset_cellGraph hc₀ hbd₀ hn₂_tc
  have hbs₁_sub_bp₁ : π.borderSet n₁ ⊆ π.borderPlus n₁ := fun _ h => Or.inl h
  have hbs₂_sub_bp₂ : π.borderSet n₂ ⊆ π.borderPlus n₂ := fun _ h => Or.inl h
  have hdiff₁ : π.borderPlus n₁ \ π.borderSet n₁ = {π.nodeVertex n₁} := by
    ext x
    simp only [Portrayal.borderPlus, mem_sdiff, mem_ofPred_eq, mem_singleton_iff,
      hdom ▸ hn₁_Θ.1, true_and]
    exact ⟨fun ⟨hx, hnot⟩ => hx.elim (fun h => (hnot h).elim) id,
      fun hEq => ⟨Or.inr hEq, hEq ▸ π.p3_notMem n₁ ⟨hdom ▸ hn₁_bd.1, hn₁_bd.2⟩⟩⟩
  have hdiff₂ : π.borderPlus n₂ \ π.borderSet n₂ = {π.nodeVertex n₂} := by
    ext x
    simp only [Portrayal.borderPlus, mem_sdiff, mem_ofPred_eq, mem_singleton_iff,
      hdom ▸ hn₂_Θ.1, true_and]
    exact ⟨fun ⟨hx, hnot⟩ => hx.elim (fun h => (hnot h).elim) id,
      fun hEq => ⟨Or.inr hEq, hEq ▸ π.p3_notMem n₂ ⟨hdom ▸ hn₂_bd.1, hn₂_bd.2⟩⟩⟩
  have hc₁ : HasDisjointPathsAvoiding (π.cellGraph c₀) (π.borderSet n₁) (π.borderPlus n₂)
      (π.borderPlus n₁ \ π.borderSet n₁) (π.warpAt Θ) := by
    rw [hdiff₁]
    exact claim_9_6 h𝒯 π htrue hred hwarp hθ hΘ hc₀ hc₀_Θ hn₁_tc hn₂_tc hne
  have hc₂ : HasDisjointPathsAvoiding (π.cellGraph c₀) (π.borderPlus n₁) (π.borderSet n₂)
      (π.borderPlus n₂ \ π.borderSet n₂) (π.warpAt Θ) := by
    rw [hdiff₂]
    exact hasDisjointPathsAvoiding_symm (π.cellGraph c₀) (π.borderSet n₂) (π.borderPlus n₁)
      {π.nodeVertex n₂} (π.warpAt Θ)
      (claim_9_6 h𝒯 π htrue hred hwarp hθ hΘ hc₀ hc₀_Θ hn₂_tc hn₁_tc hne.symm)
  rcases theorem_9_5_proof (π.cellGraph c₀) hbp₁_sub hbp₂_sub hbs₁_sub_bp₁ hbs₂_sub_bp₂
    hc₁ hc₂ with ⟨L, hdisj, havoid⟩ | hpaths
  · rw [hdiff₁, hdiff₂] at havoid
    refine ⟨L, hdisj, fun i => ?_⟩
    exact ⟨fun h1 => Set.disjoint_left.mp (havoid i) h1 (Or.inl rfl),
      fun h2 => Set.disjoint_left.mp (havoid i) h2 (Or.inr rfl)⟩
  · obtain ⟨L, hL_disj, hL_avoid, _⟩ :=
      extract_linkage_from_plus_linkage π hdom hΘ hc₀ hc₀_Θ hn₁_tc hn₂_tc hne
        hbs₁_eq hbs₂_eq hpaths
    exact ⟨L, hL_disj, hL_avoid⟩

/-- **Graph Minors XVII, (9.7)** (page 187):
"For every border node $n$, $\beta(n) \cap \gamma(N(\Gamma)) = \emptyset$." -/
theorem theorem_9_7_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {n : π.S} (hn : n ∈ π.Γ.N ∩ bd π.S) :
    Disjoint (π.borderSet n) (π.nodeVertex '' π.Γ.N) := by
  have : T2Space π.S := π.isSurface.2.1
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof
      h𝒯 π htrue hred hwarp hθ
  refine Set.disjoint_left.mpr ?_
  rintro v hvn ⟨n', hn'_N, rfl⟩
  let Θ := connectedComponentIn (bd π.S) n
  have hΘ : Θ ∈ cuffs π.S := ⟨n, hn.2, rfl⟩
  have hΘ_arc : IsOArc Θ := (cuff_statement.{0} π.S π.isSurface).2.2 Θ hΘ
  have hΘ_bd : Θ ⊆ bd π.S := connectedComponentIn_subset (bd π.S) n
  have hn_Θ : n ∈ π.Γ.N ∩ Θ := ⟨hn.1, mem_connectedComponentIn hn.2⟩
  have hn'_in_Θ : n' ∈ Θ := by
    by_contra hn'_not_Θ
    exact π.p4_notMem Θ hΘ n hn_Θ n' (hdom ▸ hn'_N) hn'_not_Θ hvn
  have hn'_Θ : n' ∈ π.Γ.N ∩ Θ := ⟨hn'_N, hn'_in_Θ⟩
  have hn'_bd : n' ∈ π.Γ.N ∩ bd π.S := ⟨hn'_N, hΘ_bd hn'_in_Θ⟩
  have hn_ne_n' : n ≠ n' := by
    rintro rfl
    exact π.p3_notMem n ⟨hdom ▸ hn.1, hn.2⟩ hvn
  set k := (π.Γ.N ∩ Θ).ncard
  obtain ⟨E⟩ : Nonempty (π.Γ.CuffEnumeration Θ k) := π.Γ.exists_cuffEnumeration hΘ hΘ_arc
  have hk_ge2 : 2 ≤ k := E.two_le
  have hk_pos : 0 < k := by omega
  have hn'_range : n' ∈ range E.node := E.range_node ▸ hn'_Θ
  rcases hn'_range with ⟨idx, hidx_eq⟩
  let idx' : Fin k := ⟨(idx.1 + 1) % k, Nat.mod_lt _ hk_pos⟩
  have hidx_ne : idx ≠ idx' := by
    intro hEq
    have hval : idx.1 = (idx.1 + 1) % k := congrArg Fin.val hEq
    have hi_lt : idx.1 < k := idx.2
    by_cases hlast : idx.1 + 1 = k
    · rw [hlast, Nat.mod_self] at hval; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega
  let c₀ := E.cell idx
  let n₂ := E.node idx'
  have hc₀_mem : c₀ ∈ {c ∈ π.Γ.C | (c ∩ Θ).Nonempty} := E.range_cell ▸ ⟨idx, rfl⟩
  have hc₀ : c₀ ∈ π.Γ.C := hc₀_mem.1
  have hc₀_Θ : (c₀ ∩ Θ).Nonempty := hc₀_mem.2
  have htc₀ : tilde c₀ = {n', n₂} := by
    change tilde (E.cell idx) = {n', E.node idx'}
    rw [E.cell_tilde idx, hidx_eq]
  have hne_n'₂ : n' ≠ n₂ := by
    rw [← hidx_eq]
    exact E.injective_node.ne hidx_ne
  obtain ⟨c₁, hc₁, hc₁_Θ, _, n₃, hne_n'₃, htc₁, _, hneighbors⟩ :=
    exists_other_border_cell_of_mem_tilde π hΘ hc₀ hc₀_Θ hne_n'₂ htc₀
  have hv_bp_n' : π.nodeVertex n' ∈ π.borderPlus n' := Or.inr ⟨hdom ▸ hn'_N, rfl⟩
  have hv_bp_n : π.nodeVertex n' ∈ π.borderPlus n := Or.inl hvn
  have hcell_contra : ∀ (d : Set π.S) (u : π.S),
      d ∈ π.Γ.C → (d ∩ Θ).Nonempty → n' ≠ u → tilde d = {n', u} →
      π.nodeVertex n' ∈ π.borderPlus u → False := by
    intro d u hd hd_Θ hne_u htd hv_u
    have hu_Θ : u ∈ π.Γ.N ∩ Θ :=
      (π.Γ.border_cell_subset_cuff hd hΘ hd_Θ).2.2.2.1 (htd ▸ Or.inr rfl)
    have hbd_d : (d ∩ bd π.S).Nonempty := hd_Θ.mono (inter_subset_inter_right _ hΘ_bd)
    have hv_bs_u : π.nodeVertex n' ∈ π.borderSet u := by
      rcases hv_u with hbs | ⟨_, hEq⟩
      · exact hbs
      · exfalso
        exact hne_u (π.nodeVertex_injOn (hdom ▸ hn'_N) (hdom ▸ hu_Θ.1) hEq)
    have hbs_u_eq : (π.borderSet u).ncard = π.warpAt Θ :=
      theorem_9_4_proof h𝒯 π htrue hred hwarp hθ hΘ hu_Θ
    have hbs_u_fin : (π.borderSet u).Finite :=
      (π.cellGraph d).vertexSet_finite.subset (π.p3_subset d hd hbd_d u (htd ▸ Or.inr rfl))
    obtain ⟨L, hL_disj, hL_avoid⟩ :=
      theorem_9_6_proof h𝒯 π htrue hred hwarp hθ hΘ hd hd_Θ
        (htd ▸ Or.inl rfl) (htd ▸ Or.inr rfl) hne_u
    obtain ⟨j, hj_last⟩ := exists_last_eq_of_ncard_le hbs_u_fin hbs_u_eq.le L hL_disj hv_bs_u
    have hv_sup : π.nodeVertex n' ∈ (L j).walk.support := by
      rw [← hj_last]
      exact (L j).walk.end_mem_support
    exact (hL_avoid j).1 hv_sup
  rcases hneighbors n hn_Θ hn_ne_n' (π.nodeVertex n') hv_bp_n' hv_bp_n with hv₂ | hv₃
  · exact hcell_contra c₀ n₂ hc₀ hc₀_Θ hne_n'₂ htc₀ hv₂
  · exact hcell_contra c₁ n₃ hc₁ hc₁_Θ hne_n'₃ htc₁ hv₃

/-- **Graph Minors XVII, (9.8)** (pages 187–188):
"Let $c_0$ be a border cell with $c_0 = \{n_1, n_2\}$. Then
(i) $|\beta(n_1)| = |\beta(n_2)| = q$ and
$\beta(n_1) \cap \gamma(N(\Gamma)), \beta(n_2) \cap \gamma(N(\Gamma)) = \emptyset$; ...
(ii) there is a linkage $\{P_1, \dots, P_q\}$ in $\alpha(c_0) \setminus \{\gamma(n_1),
\gamma(n_2)\}$
from $\beta(n_1)$ to $\beta(n_2)$ such that either there is a path $P_0$ such that
$\{P_0, P_1, \dots, P_q\}$ is a linkage in $\alpha(c_0)$ from $\beta(n_1 +)$ to $\beta(n_2 +)$,
or there is an internal cell $c$ with $|\tilde{c}| = 3$ and $\tilde{c}_0 \subseteq \tilde{c}$."
(The paper writes $c_0 = \{n_1, n_2\}$ for $\tilde{c}_0 = \{n_1, n_2\}$.) -/
theorem theorem_9_8_proof
    {α : Type u} {β : Type v} {G : Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}
    (h𝒯 : IsTangle G θ 𝒯) (π : Portrayal G)
    (htrue : π.IsTrue 𝒯)
    (hred : π.IsRedundant 𝒯 θ (2 * p + 3))
    (hwarp : π.warp ≤ p)
    (hθ : 4 * p + 5 < θ)
    {Θ c₀ : Set π.S} (hΘ : Θ ∈ cuffs π.S) (hc₀ : c₀ ∈ π.Γ.C) (hc₀_Θ : (c₀ ∩ Θ).Nonempty)
    {n₁ n₂ : π.S} (hn₁_tc : n₁ ∈ tilde c₀) (hn₂_tc : n₂ ∈ tilde c₀) (hne : n₁ ≠ n₂) :
    (π.borderSet n₁).ncard = π.warpAt Θ ∧
    (π.borderSet n₂).ncard = π.warpAt Θ ∧
    Disjoint (π.borderSet n₁) (π.nodeVertex '' π.Γ.N) ∧
    Disjoint (π.borderSet n₂) (π.nodeVertex '' π.Γ.N) ∧
    ∃ L : Fin (π.warpAt Θ) →
        PathFromTo (π.cellGraph c₀).skeleton (π.borderSet n₁) (π.borderSet n₂),
      (Pairwise fun i j ↦ Disjoint {z | z ∈ (L i).walk.support} {z | z ∈ (L j).walk.support}) ∧
      (∀ i, π.nodeVertex n₁ ∉ (L i).walk.support ∧ π.nodeVertex n₂ ∉ (L i).walk.support) ∧
      ((∃ L₀ : PathFromTo (π.cellGraph c₀).skeleton {π.nodeVertex n₁} {π.nodeVertex n₂},
          ∀ i, Disjoint {z | z ∈ L₀.walk.support} {z | z ∈ (L i).walk.support}) ∨
        ∃ c ∈ π.Γ.C, ¬ (c ∩ bd π.S).Nonempty ∧ (tilde c).ncard = 3 ∧ tilde c₀ ⊆ tilde c) := by
  have hdom : π.domγ = π.Γ.N :=
    theorem_8_4_proof
      h𝒯 π htrue hred hwarp hθ
  have hsub_cuff₀ := π.Γ.border_cell_subset_cuff hc₀ hΘ hc₀_Θ
  have hbd₀ : (c₀ ∩ bd π.S).Nonempty := hsub_cuff₀.2.1 ▸ hc₀_Θ
  have hΘ_bd : Θ ⊆ bd π.S := by
    rcases hΘ with ⟨x₀, _, rfl⟩
    exact connectedComponentIn_subset (bd π.S) x₀
  have hn₁_Θ : n₁ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 hn₁_tc
  have hn₂_Θ : n₂ ∈ π.Γ.N ∩ Θ := hsub_cuff₀.2.2.2.1 hn₂_tc
  have hn₁_bd : n₁ ∈ π.Γ.N ∩ bd π.S := ⟨hn₁_Θ.1, hΘ_bd hn₁_Θ.2⟩
  have hn₂_bd : n₂ ∈ π.Γ.N ∩ bd π.S := ⟨hn₂_Θ.1, hΘ_bd hn₂_Θ.2⟩
  have hbs₁_eq : (π.borderSet n₁).ncard = π.warpAt Θ :=
    theorem_9_4_proof h𝒯 π htrue hred hwarp hθ hΘ hn₁_Θ
  have hbs₂_eq : (π.borderSet n₂).ncard = π.warpAt Θ :=
    theorem_9_4_proof h𝒯 π htrue hred hwarp hθ hΘ hn₂_Θ
  have hdisj₁ : Disjoint (π.borderSet n₁) (π.nodeVertex '' π.Γ.N) :=
    theorem_9_7_proof h𝒯 π htrue hred hwarp hθ hn₁_bd
  have hdisj₂ : Disjoint (π.borderSet n₂) (π.nodeVertex '' π.Γ.N) :=
    theorem_9_7_proof h𝒯 π htrue hred hwarp hθ hn₂_bd
  refine ⟨hbs₁_eq, hbs₂_eq, hdisj₁, hdisj₂, ?_⟩
  by_cases hex : ∃ c ∈ π.Γ.C, ¬ (c ∩ bd π.S).Nonempty ∧ tilde c₀ ⊆ tilde c
  · rcases hex with ⟨c, hc, hint_c, hsub⟩
    have hc₀_ne_c : c₀ ≠ c := fun h => hint_c (h ▸ hbd₀)
    have hcard3 : (tilde c).ncard = 3 :=
      (theorem_8_8_proof
        h𝒯 π htrue hred hwarp hθ hc₀ hc hc₀_ne_c hsub).2
    obtain ⟨L, hL_disj, hL_avoid⟩ :=
      theorem_9_6_proof h𝒯 π htrue hred hwarp hθ hΘ hc₀ hc₀_Θ hn₁_tc hn₂_tc hne
    exact ⟨L, hL_disj, hL_avoid, Or.inr ⟨c, hc, hint_c, hcard3, hsub⟩⟩
  · obtain ⟨hpaths, _, _⟩ :=
      theorem_9_3_proof h𝒯 π htrue hred hwarp hθ hΘ hc₀ hc₀_Θ hn₁_tc hn₂_tc hne hex
    obtain ⟨L, hL_disj, hL_avoid, L₀, hL₀_disj⟩ :=
      extract_linkage_from_plus_linkage π hdom hΘ hc₀ hc₀_Θ hn₁_tc hn₂_tc hne
        hbs₁_eq hbs₂_eq hpaths
    exact ⟨L, hL_disj, hL_avoid, Or.inl ⟨L₀, hL₀_disj⟩⟩

end GraphMinor.GM17
