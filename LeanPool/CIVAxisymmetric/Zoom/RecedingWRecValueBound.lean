/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.VRecBoundedRectangle

/-!
# Value bound for the receding-axis vertical rescaled field `zoomWRec`

The value bound (order `(0,0)`) for `zoomWRec`, cleanly separated from the
nonnegative swirl source `zoomSRec` and normalized to the shared exponent `-1/2` exactly as its
second-derivative bounds are in `CIV/Zoom/RecedingSecondDerivativeBoundsW.lean`.  The companion
compact-time-rectangle
wrapper completes the pattern of `CIV.exists_forall_abs_zoomVRec_le_of_isCompact`
(`CIV/Zoom/VRecBoundedRectangle.lean`) for the vertical field.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem abs_zoomWRec_le_rpow_neg_half {C h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {p : (ℝ × ℝ) × ℝ}
    (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hτ : p.2 ≤ -1) :
    |zoomWRec lam h rc zc u p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hdrop : |zoomWRec lam h rc zc u p|
      ≤ |zoomWRec lam h rc zc u p| + |zoomSRec lam h rc zc u p| :=
    le_add_of_nonneg_right (abs_nonneg _)
  refine le_trans
    (le_trans hdrop (abs_zoomWRec_add_abs_zoomSRec_le C h lam rc zc hlam u hb p hp)) ?_
  refine mul_le_mul_of_nonneg_left ?_ hC
  have hτ0 : (1 : ℝ) ≤ -p.2 := by linarith only [hτ]
  have hexp : (-(1 / 2 : ℝ) - h - 0 / 2 - (1 / 2 - h) * 0) ≤ -(1 / 2 : ℝ) := by
    nlinarith only [hh0]
  exact Real.rpow_le_rpow_of_exponent_le hτ0 hexp

theorem exists_forall_abs_zoomWRec_le_of_isCompact {C h : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u) (rc zc : ℝ)
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : ∀ τ ∈ J, τ ≤ -1) :
    ∃ M : ℝ, ∀ lam : ℝ, 0 < lam → ∀ p : (ℝ × ℝ) × ℝ,
      zoomPointRec lam h rc zc p ∈ unitCylinder → p.2 ∈ J → |zoomWRec lam h rc zc u p| ≤ M := by
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
    have hbound := abs_zoomWRec_le_rpow_neg_half hlam hb hp hC hh0 (hJsub p.2 hJmem)
    have hmaxval : (-p.2) ^ (-(1 / 2 : ℝ)) ≤ (-τstar) ^ (-(1 / 2 : ℝ)) :=
      hmax hJmem
    calc
      |zoomWRec lam h rc zc u p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := hbound
      _ ≤ C * (-τstar) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmaxval hC

theorem exists_forall_abs_zoomVRec_le_and_abs_zoomWRec_le_of_isCompact {C h : ℝ} (hC : 0 ≤ C)
    (hh0 : 0 ≤ h) (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u) (rc zc : ℝ)
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : ∀ τ ∈ J, τ ≤ -1) :
    ∃ M : ℝ, ∀ lam : ℝ, 0 < lam → ∀ p : (ℝ × ℝ) × ℝ,
      zoomPointRec lam h rc zc p ∈ unitCylinder → p.2 ∈ J →
        |zoomVRec lam h rc zc u p| ≤ M ∧ |zoomWRec lam h rc zc u p| ≤ M := by
  obtain ⟨MV, hMV⟩ := exists_forall_abs_zoomVRec_le_of_isCompact hC u hb rc zc hJ hJsub
  obtain ⟨MW, hMW⟩ := exists_forall_abs_zoomWRec_le_of_isCompact hC hh0 u hb rc zc hJ hJsub
  refine ⟨max MV MW, fun lam hlam p hp hJmem =>
    ⟨le_trans (hMV lam hlam p hp hJmem) (le_max_left _ _),
     le_trans (hMW lam hlam p hp hJmem) (le_max_right _ _)⟩⟩

end CIV
