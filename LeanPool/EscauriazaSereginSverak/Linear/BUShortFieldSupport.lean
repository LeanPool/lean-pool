/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCompact
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeakProductBasis

/-!
# Support of the short-time cutoff field

The compact scalar cutoff gives compact support to the vector field and
keeps its topological support inside the half-space Carleman cylinder.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Pulling back a compact scalar cutoff through the parabolic coordinate
homeomorphism preserves its compact support and spatial-time support bound. -/
theorem bu_short_cutoff_field_support
    {scale R ε : ℝ} (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε)
    (v : ParabolicPoint → Vec3) :
    HasCompactSupport (buCutField (buShortFullCutoff scale R hR ε) v) ∧
      tsupport (buCutField (buShortFullCutoff scale R hR ε) v) ⊆
        spaceTimeSet {y : Vec3 | 1 < y 2} (Ioo (0 : ℝ) 1) := by
  let κ := buShortFullCutoff scale R hR ε
  obtain ⟨hκcompact, hκts⟩ :=
    buShortFullCutoff_compact_support hscale hscale1 hR hε
  let K : Set ParabolicPoint :=
    parabolicHomeomorph.symm '' tsupport κ
  have hKcompact : IsCompact K :=
    parabolicHomeomorph.symm.isCompact_image.mpr hκcompact.isCompact
  have hscalarCompact : HasCompactSupport (buCutScalar κ) := by
    apply HasCompactSupport.of_support_subset_isCompact hKcompact
    intro z hz
    have hκne : κ (parabolicHomeomorph z) ≠ 0 := by
      intro hzero
      exact hz (show buCutScalar κ z = 0 from hzero)
    exact ⟨parabolicHomeomorph z,
      subset_tsupport κ (Function.mem_support.mpr hκne),
      parabolicHomeomorph.symm_apply_apply z⟩
  have hscalarSupport : tsupport (buCutScalar κ) ⊆ K := by
    apply closure_minimal _ hKcompact.isClosed
    intro z hz
    have hκne : κ (parabolicHomeomorph z) ≠ 0 := by
      intro hzero
      exact hz (show buCutScalar κ z = 0 from hzero)
    exact ⟨parabolicHomeomorph z,
      subset_tsupport κ (Function.mem_support.mpr hκne),
      parabolicHomeomorph.symm_apply_apply z⟩
  have hfieldCompact : HasCompactSupport (buCutField κ v) := by
    change HasCompactSupport (buCutScalar κ • v)
    exact hscalarCompact.smul_right
  refine ⟨hfieldCompact, ?_⟩
  intro z hz
  have hscalar : z ∈ tsupport (buCutScalar κ) :=
    tsupport_smul_subset_left (buCutScalar κ) v hz
  obtain ⟨q, hq, hqz⟩ := hscalarSupport hscalar
  have hqdomain := hκts hq
  have hqeq : q = parabolicHomeomorph z := by
    rw [← hqz]
    exact (parabolicHomeomorph.apply_symm_apply q).symm
  rw [hqeq] at hqdomain
  rcases z with ⟨y, s⟩
  change 1 < y 2 ∧ s ∈ Ioo (1 / 2 : ℝ) 1 at hqdomain
  exact ⟨hqdomain.1, (by linarith only [hqdomain.2.1]), hqdomain.2.2⟩

end ESS
