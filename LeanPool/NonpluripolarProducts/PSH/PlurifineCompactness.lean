/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.PlurifineBasis

/-! Genuine compact neighborhoods inside arbitrary actual plurifine open sets. -/

@[expose] public section

namespace SGPT.PSH

open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.PlurifineSingleSuperlevelNeighborhoods
open SGPT.Foundations.Analysis.Pending.PlurifineEuclideanComparison
open SGPT.Foundations.Analysis.Pending.PlurifinePshTopology
open scoped Topology

variable {n : ℕ}

/-- SGPT cor:compactnhformbase: every actual fine-open neighborhood contains
an actual Euclidean compact fine-neighborhood. The fine-open set itself need
not be ordinary open or measurable. -/
theorem exists_compact_domainPlurifine_neighborhood (Ω : Opens (ComplexModel n))
    {S : Set Ω} (hS : IsOpen[domainPlurifineTopology Ω] S) {x : Ω} (hx : x ∈ S) :
    ∃ K : Set (ComplexModel n), IsCompact K ∧ K ⊆ Ω ∧
      x.val ∈ K ∧
      Subtype.val ⁻¹' K ∈ @nhds Ω (domainPlurifineTopology Ω) x ∧
      Subtype.val ⁻¹' K ⊆ S := by
  obtain ⟨O, g, hO, hxO, hg, hgx, hglo, hghi, hTf, hTS⟩ :=
    exists_bounded_single_superlevel hS hx
  obtain ⟨U, hU, hUΩ, hUO⟩ := exists_ambient_open_of_subtype_open Ω O hO
  have hm (z : Ω) : z.val ∈ U ↔ z ∈ O := by
    change z ∈ Subtype.val ⁻¹' U ↔ z ∈ O
    rw [hUO]
  have hxU := (hm x).mpr hxO
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hxU)
  let K : Set (ComplexModel n) := closedBall x.val r ∩ g ⁻¹' Ici (1 / 4)
  have hK : IsCompact K :=
    ((real_upperSemicontinuousOn_of_psh hg).mono (hrU.trans hUΩ)).isCompact_inter_preimage_Ici
      (isCompact_closedBall x.val r) (1 / 4)
  have hKΩ : K ⊆ Ω := fun z hz ↦ hUΩ (hrU hz.1)
  have hxK : x.val ∈ K := ⟨mem_closedBall_self hr.le, by
    change (1 / 4 : ℝ) ≤ g x.val
    rw [hgx]
    norm_num⟩
  let : TopologicalSpace Ω := domainPlurifineTopology Ω
  let N : Set Ω := (Subtype.val ⁻¹' ball x.val r) ∩ {z : Ω | (1 / 4 : ℝ) < g z.val}
  have hN : IsOpen N :=
    (isOpen_euclidean isOpen_ball).inter
      (isOpen_realPsh_superlevel hg (1 / 4))
  have hxN : x ∈ N := ⟨mem_ball_self hr, by
    change (1 / 4 : ℝ) < g x.val
    rw [hgx]
    norm_num⟩
  refine ⟨K, hK, hKΩ, hxK, mem_of_superset (hN.mem_nhds hxN) ?_, ?_⟩
  · intro z hz
    exact ⟨ball_subset_closedBall hz.1, by
      change (1 / 4 : ℝ) ≤ g z.val
      exact hz.2.le⟩
  · intro z hz
    apply hTS
    refine ⟨(hm z).mp (hrU hz.1), ?_⟩
    change (0 : ℝ) < g z.val
    have hh : (1 / 4 : ℝ) ≤ g z.val := hz.2
    linarith

end SGPT.PSH
