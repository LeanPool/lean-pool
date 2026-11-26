/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72CornerCaps
public import LeanPool.GraphMinor.GM12.Section72PatchHalves

/-!
# The two types of boundary arc in a mixed corner cap

A mixed corner in the local patch for XII (7.2) has one half-edge of
the old drawing and one of the circle. A small cap in this corner
meets the old drawing only in its old half-edge, and the circle only
in its circle half-edge. Normality gives both assertions.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- A mixed corner cap meets the old drawing and the circle on their
respective spokes, for the diversion at the vertex in XII (7.2), page 260. -/
theorem exists_mixed_corner_cap (hS : IsClosedSurface S)
    {Γ H : Drawing S} (hsub : Γ.IsSubdrawing H)
    {C : Set S} (hn : (PaintingOrDrawing.drawing Γ).IsNormal C)
    (hnew : ∀ e ∈ H.E, e ∉ Γ.E → e ⊆ C)
    {γ : Set S → I → S} (hγ : EdgePar H γ)
    {v : S} (hv : v ∈ Γ.V) (hvC : v ∈ C)
    {next : halfEdges H γ v → halfEdges H γ v}
    {ρ P Q : halfEdges H γ v → Set S} {W : Set S}
    {τ : halfEdges H γ v → I} (hsec : IsSectors H γ v next ρ P W Q τ)
    (hlocal : C ∩ W ⊆ H.U)
    (k g c : halfEdges H γ v) (hg : g.1.1 ∈ Γ.E) (hc : c.1.1 ∉ Γ.E)
    (hcorner : (g = k ∧ c = next k) ∨ (c = k ∧ g = next k)) :
    ∃ (tG tC : I) (D : Set S), 0 < tG ∧ tG < 1 ∧ 0 < tC ∧ tC < 1 ∧
      IsClosedDisc D ∧ D ⊆ W ∧ D ⊆ Q k ∧
      spoke γ g.1 '' Icc 0 tG ∪ spoke γ c.1 '' Icc 0 tC ⊆ discBd D ∧
      D ∩ H.U ⊆ spoke γ g.1 '' Icc 0 tG ∪ spoke γ c.1 '' Icc 0 tC ∧
      D ∩ Γ.U ⊆ spoke γ g.1 '' Icc 0 tG ∧
      D ∩ C ⊆ spoke γ c.1 '' Icc 0 tC := by
  have hvg : spoke γ g.1 0 = v := (spoke_zero γ g.1).trans g.2.2
  have hvc : spoke γ c.1 0 = v := (spoke_zero γ c.1).trans c.2.2
  have hG : ∀ t : I, spoke γ g.1 t ∈ Γ.U := by
    intro t
    by_cases ht : t = 0
    · rw [ht, hvg]
      exact Γ.V_subset_U hv
    · exact (hg.2.1 (spoke_mem_edge hγ g.2.1 (unitInterval.pos_iff_ne_zero.mpr ht))).1
  have hC : ∀ t : I, spoke γ c.1 t ∈ C := by
    intro t
    by_cases ht : t = 0
    · rwa [ht, hvc]
    · exact hnew c.1.1 c.2.1 hc (spoke_mem_edge hγ c.2.1 (unitInterval.pos_iff_ne_zero.mpr ht))
  have hGoff : ∀ t : I, spoke γ g.1 t ∈ C → spoke γ g.1 t = v := by
    intro t htC
    by_cases ht : t = 0
    · rwa [ht]
    · have he := spoke_mem_edge hγ g.2.1 (unitInterval.pos_iff_ne_zero.mpr ht)
      exact ((hg.2.1 he).2 (hn ⟨htC, hG t⟩)).elim
  have hCoff : ∀ t : I, spoke γ c.1 t ∈ Γ.U → spoke γ c.1 t = v := by
    intro t htΓ
    by_cases ht : t = 0
    · rwa [ht]
    · have he := spoke_mem_edge hγ c.2.1 (unitInterval.pos_iff_ne_zero.mpr ht)
      exact ((c.2.1.2.1 he).2 (hsub.1 (hn ⟨hC t, htΓ⟩))).elim
  obtain ⟨t₀, t₁, D, ht₀, ht₀1, ht₁, ht₁1, hD, hDW, hDQ, hDb, hDH⟩ := exists_corner_cap hS hγ hsec k
  have hchoose : ∃ tG tC : I, 0 < tG ∧ tG < 1 ∧ 0 < tC ∧ tC < 1 ∧
      spoke γ g.1 '' Icc 0 tG ∪ spoke γ c.1 '' Icc 0 tC ⊆ discBd D ∧
      D ∩ H.U ⊆ spoke γ g.1 '' Icc 0 tG ∪ spoke γ c.1 '' Icc 0 tC := by
    rcases hcorner with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨t₀, t₁, ht₀, ht₀1, ht₁, ht₁1, hDb, hDH⟩
    · exact ⟨t₁, t₀, ht₁, ht₁1, ht₀, ht₀1, by rwa [union_comm], by rwa [union_comm]⟩
  obtain ⟨tG, tC, htG, htG1, htC, htC1, hbdD, hDH'⟩ := hchoose
  have hvG : v ∈ spoke γ g.1 '' Icc 0 tG := ⟨0, ⟨le_rfl, htG.le⟩, hvg⟩
  have hvC' : v ∈ spoke γ c.1 '' Icc 0 tC := ⟨0, ⟨le_rfl, htC.le⟩, hvc⟩
  refine ⟨tG, tC, D, htG, htG1, htC, htC1, hD, hDW, hDQ, hbdD, hDH', ?_, ?_⟩
  · rintro x ⟨hxD, hxΓ⟩
    rcases hDH' ⟨hxD, hsub.U_subset hxΓ⟩ with hxG | ⟨t, _, htx⟩
    · exact hxG
    · have hxv : x = v := htx.symm.trans (hCoff t (htx.symm ▸ hxΓ))
      exact hxv.symm ▸ hvG
  · rintro x ⟨hxD, hxC⟩
    rcases hDH' ⟨hxD, hlocal ⟨hxC, hDW hxD⟩⟩ with ⟨t, _, htx⟩ | hxC'
    · have hxv : x = v := htx.symm.trans (hGoff t (htx.symm ▸ hxC))
      exact hxv.symm ▸ hvC'
    · exact hxC'

end GraphMinor.GM12
