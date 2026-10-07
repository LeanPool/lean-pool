/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingForceBound
public import LeanPool.CIVAxisymmetric.Zoom.OmegaEquicontinuous

/-!
# Receding Force Pairing Bound

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

theorem force_term_pairing_bound
    {h rc zc : ℝ} (hh0 : 0 < h)
    (lam : ℕ → ℝ) (hlam_pos : ∀ n, 0 < lam n) (hlam_le : ∀ᶠ n in atTop, lam n ≤ 1)
    {f : ParabolicPoint → Vec3} (hMf : ForceC2Bounded f)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (τ : ℝ)
    (hmem : ∀ᶠ n in atTop, ∀ y ∈ K, zoomPointRec (lam n) h rc zc (y, τ) ∈ unitCylinder) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior K →
      ∀ B : ℝ, 0 ≤ B →
        (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
        ∀ᶠ n in atTop,
          |∫ y : ℝ × ℝ,
              (lam n ^ 4 * lam n ^ (2 * h) * curlComp f 1 (zoomPointRec (lam n) h rc zc (y, τ)))
                * ψ y| ≤ C₀ * B := by
  obtain ⟨M, hM⟩ := hMf
  have hMmax : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ max M 0 :=
    fun z hz i α hα => (hM z hz i α hα).trans (le_max_left _ _)
  have hMnn : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  refine ⟨2 * max M 0 * (volume K).toReal, by positivity, fun ψ hψ hψc hψU B hB hψB => ?_⟩
  filter_upwards [hlam_le, hmem] with n hlam_len hmem_n
  have h4nn : (0 : ℝ) ≤ lam n ^ 4 := pow_nonneg (hlam_pos n).le 4
  have h2hnn : (0 : ℝ) ≤ lam n ^ (2 * h) := Real.rpow_nonneg (hlam_pos n).le _
  have hApos : (0 : ℝ) ≤ lam n ^ 4 * lam n ^ (2 * h) := mul_nonneg h4nn h2hnn
  have hAle : lam n ^ 4 * lam n ^ (2 * h) ≤ 1 := by
    have h4 : lam n ^ 4 ≤ 1 :=
      pow_le_one₀ (hlam_pos n).le hlam_len
    have h2h : lam n ^ (2 * h) ≤ 1 :=
      Real.rpow_le_one (hlam_pos n).le hlam_len (by linarith only [hh0])
    calc lam n ^ 4 * lam n ^ (2 * h) ≤ 1 * 1 :=
          mul_le_mul h4 h2h h2hnn (by norm_num)
      _ = 1 := by norm_num
  have ha : ∀ y ∈ K, |lam n ^ 4 * lam n ^ (2 * h) *
      curlComp f 1 (zoomPointRec (lam n) h rc zc (y, τ))| ≤ 2 * max M 0 := by
    intro y hy
    have hp : zoomPointRec (lam n) h rc zc (y, τ) ∈ unitCylinder := hmem_n y hy
    have hbound := abs_recedingForce_le (lam := lam n) (h := h) (rc := rc) (zc := zc)
      (hlam_pos n) hMmax (p := (y, τ)) hp
    have hfactor : lam n ^ 4 * lam n ^ (2 * h) * (2 * max M 0) ≤ 1 * (2 * max M 0) :=
      mul_le_mul_of_nonneg_right hAle (by positivity)
    calc |lam n ^ 4 * lam n ^ (2 * h) *
            curlComp f 1 (zoomPointRec (lam n) h rc zc (y, τ))|
          ≤ 2 * max M 0 * (lam n ^ 4 * lam n ^ (2 * h)) := hbound
      _ = lam n ^ 4 * lam n ^ (2 * h) * (2 * max M 0) := by ring
      _ ≤ 1 * (2 * max M 0) := hfactor
      _ = 2 * max M 0 := by ring
  have hψBK : ∀ y, |ψ y| ≤ B := fun y => (hψB y).1
  have hψsub : tsupport ψ ⊆ K := hψU.trans interior_subset
  have hfinal := abs_integral_mul_le_of_tsupport_subset hK.measure_lt_top hψsub ha hψBK
  calc |∫ y : ℝ × ℝ,
        (lam n ^ 4 * lam n ^ (2 * h) * curlComp f 1 (zoomPointRec (lam n) h rc zc (y, τ)))
          * ψ y| ≤ 2 * max M 0 * B * (volume K).toReal := hfinal
    _ = 2 * max M 0 * (volume K).toReal * B := by ring

end CIV
