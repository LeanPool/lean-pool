/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.Receding

/-!
# Boundedness of the receding-axis zoom fields on compact time rectangles

For the receding-axis rescaled radial and vertical fields `V_n`, `W_n` (and the swirl
source `S_n`) of `eq:aniso:zoom:fields`, the companion boundedness input — distinct from the
first-derivative/Lipschitz bound — that an eventual Arzelà–Ascoli extraction of `(V_n, W_n)` in
`C¹_loc` needs alongside the equicontinuity
modulus.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem exists_forall_abs_zoomVRec_le_of_isCompact {C h : ℝ} (hC : 0 ≤ C)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u) (rc zc : ℝ)
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : ∀ τ ∈ J, τ ≤ -1) :
    ∃ M : ℝ, ∀ lam : ℝ, 0 < lam → ∀ p : (ℝ × ℝ) × ℝ,
      zoomPointRec lam h rc zc p ∈ unitCylinder → p.2 ∈ J → |zoomVRec lam h rc zc u p| ≤ M := by
  rcases J.eq_empty_or_nonempty with (hne | hne)
  · refine ⟨0, fun lam hlam p hp hJmem => ?_⟩
    have hmem_empty : p.2 ∈ (∅ : Set ℝ) := by rwa [hne] at hJmem
    exfalso
    exact hmem_empty
  · have h_cont : ContinuousOn (fun (τ : ℝ) => (-τ) ^ (-(1 / 2 : ℝ))) J := by
      refine (continuousOn_neg).rpow_const fun τ hτ => ?_
      have hne_zero : -τ ≠ 0 := by
        have hτ' : τ ≤ -1 := hJsub τ hτ
        linarith only [hτ']
      exact Or.inl hne_zero
    obtain ⟨τstar, hτstarJ, hmax⟩ := hJ.exists_isMaxOn hne h_cont
    refine ⟨C * (-τstar) ^ (-(1 / 2 : ℝ)), fun lam hlam p hp hJmem => ?_⟩
    have hbound := abs_zoomVRec_le C h lam rc zc hlam u hb p hp
    have hexp : (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 0) = (-(1 / 2 : ℝ)) := by ring
    rw [hexp] at hbound
    have hmaxval : (-p.2) ^ (-(1 / 2 : ℝ)) ≤ (-τstar) ^ (-(1 / 2 : ℝ)) :=
      hmax hJmem
    calc
      |zoomVRec lam h rc zc u p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := hbound
      _ ≤ C * (-τstar) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmaxval hC

theorem exists_forall_abs_zoomWRec_add_abs_zoomSRec_le_of_isCompact {C h : ℝ} (hC : 0 ≤ C)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u) (rc zc : ℝ)
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : ∀ τ ∈ J, τ ≤ -1) :
    ∃ M : ℝ, ∀ lam : ℝ, 0 < lam → ∀ p : (ℝ × ℝ) × ℝ,
      zoomPointRec lam h rc zc p ∈ unitCylinder → p.2 ∈ J →
        |zoomWRec lam h rc zc u p| + |zoomSRec lam h rc zc u p| ≤ M := by
  rcases J.eq_empty_or_nonempty with (hne | hne)
  · refine ⟨0, fun lam hlam p hp hJmem => ?_⟩
    have hmem_empty : p.2 ∈ (∅ : Set ℝ) := by rwa [hne] at hJmem
    exfalso
    exact hmem_empty
  · have h_cont : ContinuousOn (fun (τ : ℝ) => (-τ) ^ (-(1 / 2 : ℝ) - h)) J := by
      refine (continuousOn_neg).rpow_const fun τ hτ => ?_
      have hne_zero : -τ ≠ 0 := by
        have hτ' : τ ≤ -1 := hJsub τ hτ
        linarith only [hτ']
      exact Or.inl hne_zero
    obtain ⟨τstar, hτstarJ, hmax⟩ := hJ.exists_isMaxOn hne h_cont
    refine ⟨C * (-τstar) ^ (-(1 / 2 : ℝ) - h), fun lam hlam p hp hJmem => ?_⟩
    have hbound := abs_zoomWRec_add_abs_zoomSRec_le C h lam rc zc hlam u hb p hp
    have hexp : (-(1 / 2 : ℝ) - h - 0 / 2 - (1 / 2 - h) * 0) = (-(1 / 2 : ℝ) - h) := by ring
    rw [hexp] at hbound
    have hmaxval : (-p.2) ^ (-(1 / 2 : ℝ) - h) ≤ (-τstar) ^ (-(1 / 2 : ℝ) - h) :=
      hmax hJmem
    calc
      |zoomWRec lam h rc zc u p| + |zoomSRec lam h rc zc u p|
          ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h) := hbound
      _ ≤ C * (-τstar) ^ (-(1 / 2 : ℝ) - h) :=
        mul_le_mul_of_nonneg_left hmaxval hC

theorem exists_forall_abs_zoomVRec_add_abs_zoomWRec_add_abs_zoomSRec_le_of_isCompact
    {C h : ℝ} (hC : 0 ≤ C) (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (rc zc : ℝ) {J : Set ℝ} (hJ : IsCompact J) (hJsub : ∀ τ ∈ J, τ ≤ -1) :
    ∃ M : ℝ, ∀ lam : ℝ, 0 < lam → ∀ p : (ℝ × ℝ) × ℝ,
      zoomPointRec lam h rc zc p ∈ unitCylinder → p.2 ∈ J →
        |zoomVRec lam h rc zc u p| + |zoomWRec lam h rc zc u p| + |zoomSRec lam h rc zc u p|
          ≤ M := by
  rcases J.eq_empty_or_nonempty with (hne | hne)
  · refine ⟨0, fun lam hlam p hp hJmem => ?_⟩
    have hmem_empty : p.2 ∈ (∅ : Set ℝ) := by rwa [hne] at hJmem
    exfalso
    exact hmem_empty
  · have h_cont_V : ContinuousOn (fun (τ : ℝ) => (-τ) ^ (-(1 / 2 : ℝ))) J := by
      refine (continuousOn_neg).rpow_const fun τ hτ => ?_
      have hne_zero : -τ ≠ 0 := by
        have hτ' : τ ≤ -1 := hJsub τ hτ
        linarith only [hτ']
      exact Or.inl hne_zero
    obtain ⟨τstarV, hτstarVJ, hmaxV⟩ := hJ.exists_isMaxOn hne h_cont_V
    have h_cont_WS : ContinuousOn (fun (τ : ℝ) => (-τ) ^ (-(1 / 2 : ℝ) - h)) J := by
      refine (continuousOn_neg).rpow_const fun τ hτ => ?_
      have hne_zero : -τ ≠ 0 := by
        have hτ' : τ ≤ -1 := hJsub τ hτ
        linarith only [hτ']
      exact Or.inl hne_zero
    obtain ⟨τstarWS, hτstarWSJ, hmaxWS⟩ := hJ.exists_isMaxOn hne h_cont_WS
    set M := C * (-τstarV) ^ (-(1 / 2 : ℝ)) + C * (-τstarWS) ^ (-(1 / 2 : ℝ) - h) with hM
    refine ⟨M, fun lam hlam p hp hJmem => ?_⟩
    have hboundV := abs_zoomVRec_le C h lam rc zc hlam u hb p hp
    have hexpV : (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 0) = (-(1 / 2 : ℝ)) := by ring
    rw [hexpV] at hboundV
    have hboundWS := abs_zoomWRec_add_abs_zoomSRec_le C h lam rc zc hlam u hb p hp
    have hexpWS : (-(1 / 2 : ℝ) - h - 0 / 2 - (1 / 2 - h) * 0) = (-(1 / 2 : ℝ) - h) := by ring
    rw [hexpWS] at hboundWS
    have hmaxVval : (-p.2) ^ (-(1 / 2 : ℝ)) ≤ (-τstarV) ^ (-(1 / 2 : ℝ)) := hmaxV hJmem
    have hmaxWSval : (-p.2) ^ (-(1 / 2 : ℝ) - h) ≤ (-τstarWS) ^ (-(1 / 2 : ℝ) - h) := hmaxWS hJmem
    have hV : |zoomVRec lam h rc zc u p| ≤ C * (-τstarV) ^ (-(1 / 2 : ℝ)) := by
      linarith only [hboundV, hmaxVval, mul_le_mul_of_nonneg_left hmaxVval hC]
    have hWS : |zoomWRec lam h rc zc u p| + |zoomSRec lam h rc zc u p|
        ≤ C * (-τstarWS) ^ (-(1 / 2 : ℝ) - h) := by
      linarith only [hboundWS, hmaxWSval, mul_le_mul_of_nonneg_left hmaxWSval hC]
    linarith only [hV, hWS, hM]

end CIV
