/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamStepOneDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineGamma0

/-!
# HomProviderBSeamClose

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: the seam base and the enlarged `Y`, prepared

## What this file supplies

The print-accurate `ã` chain runs at

```text
  sb = homSeamBase M hs = s/8      (the authorized re-pin),
  Y  = seamEnlargedY M m C_top Y₀  (the authorized index enlargement),
```

and this file supplies the three facts that base needs: the measurability of
the enlarged `Y` slot, the reciprocal-range arithmetic, and the a.e. finiteness
of the seam carrier `ethmB` there.  The Theorem-C edge is read at `2p` exactly
as `homY_moment_bound_of_gamma_le` states it, the `4p` boost being paid inside
the seam display.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Measurability of the enlarged `Y` -/

/-- The enlarged `Y` slot is measurable: a constant times the Theorem-C
minimal-scale factor times two of the own measurable observables. -/
theorem measurable_seamEnlargedY (M : ABKModel d) (m : ℤ) (Ctop : ℝ)
    {Y0 : Cutoff.CutoffSample d → ℝ≥0∞} (hY0 : Measurable Y0) :
    Measurable (seamEnlargedY M m Ctop Y0) := by
  have ht40 : (0 : ℝ) < 1 / 4 := by norm_num
  have hm4 : Measurable
      (fluxCorrectedTwoScaleErrorObservableSup M m m ⟨1 / 4 / 2, half_pos ht40⟩) :=
    measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) _
  have hm5 : Measurable
      (fluxCorrectedTwoScaleErrorObservableSup M m m ⟨1 / 4, ht40⟩) :=
    measurable_fluxCorrectedTwoScaleErrorObservableSup M (le_refl m) _
  have hEm : Measurable (stepTwoEnlargedY M m ht40) :=
    (measurable_const.add hm4).mul (measurable_const.add hm5)
  exact (hY0.mul hEm).const_mul _

/-! ## 3. The a.e. finiteness of the carrier at the seam base -/

/-- `p = 1` lies inside a reciprocal `p`-range once `γ ≤ (4C)⁻²`.  This is
`HomSpineFinalWitness`'s own step, isolated. -/
theorem one_le_reciprocal_range {C gam : ℝ} (hC : 0 < C) (hg : 0 < gam) (hg1 : gam < 1)
    (hL : (0 : ℝ) < |Real.log gam|) (hgC : gam ≤ ((4 * C)⁻¹) ^ (2 : ℕ)) :
    (1 : ℝ) ≤ C⁻¹ * gam⁻¹ * |Real.log gam|⁻¹ := by
  have h4 : (0 : ℝ) < 4 * C := by linarith only [hC]
  have hsqrtC : Real.sqrt gam ≤ (4 * C)⁻¹ := by
    have hpow : Real.sqrt gam ^ (2 : ℕ) ≤ ((4 * C)⁻¹) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt hg.le]; exact hgC
    exact le_of_pow_le_pow_left₀ (by norm_num) (inv_pos.mpr h4).le hpow
  have hprod : C * (gam * |Real.log gam|) ≤ 1 := by
    have hstep := gamma_mul_absLog_le hg hg1
    have hmul : C * (gam * |Real.log gam|) ≤ C * (4 * Real.sqrt gam) :=
      mul_le_mul_of_nonneg_left hstep hC.le
    have hfin : (4 * C) * Real.sqrt gam ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hsqrtC h4.le
      rwa [mul_inv_cancel₀ (ne_of_gt h4)] at h
    linarith only [hmul, hfin]
  have hppos : (0 : ℝ) < C * gam * |Real.log gam| := mul_pos (mul_pos hC hg) hL
  have hid : (C⁻¹ * gam⁻¹ * |Real.log gam|⁻¹) * (C * gam * |Real.log gam|) = 1 := by
    field_simp
  have hle : 1 * (C * gam * |Real.log gam|) ≤
      (C⁻¹ * gam⁻¹ * |Real.log gam|⁻¹) * (C * gam * |Real.log gam|) := by
    rw [hid, one_mul, mul_assoc]
    exact hprod
  exact le_of_mul_le_mul_right hle hppos

/-- **THE `EthmB(m)` CARRIER IS a.e. FINITE AT THE SEAM BASE AND THE ENLARGED
`Y`.**

The `p = 1` instance of the seam display.  This is the input of the `ã`
bundle's `hfin` slot that the residue cannot see (it needs the Theorem-C tail),
so it is produced here and threaded to the residue by the assembly. -/
theorem ae_ethmB_seam_ne_top (d : ℕ) [NeZero d] (cstar : ℝ) (hcstar : 0 < cstar)
    {Cst Cgap Ctop : ℝ} (hCst : 1 ≤ Cst) (hCgap : 0 ≤ Cgap) (hCtop : 0 ≤ Ctop) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ X : Cutoff.CutoffSample d → ℕ∞, Measurable X →
          (∀ N : ℕ,
            (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
              ENNReal.ofReal (Cst *
                Real.exp (-((1 - homAlpha M) ^ (2 : ℕ) * ((N : ℝ) - Cst)) /
                  (Cst * M.gamma)))) →
          ∀ (hs : 0 < homS M) (m : ℤ),
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ethmB M Cgap
                  (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
                  (homN M m) (homSeamBase M hs) omega ≠ ⊤ := by
  obtain ⟨g1, C0, hg1, hC0, hdisp⟩ :=
    exists_ethmB_seam_moment_bound d cstar hcstar (Cgate := homGateRangeConst Cst)
      hCtop (homGateRangeConst_pos hCst)
  have hC0pos : (0 : ℝ) < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hquad : (0 : ℝ) < ((4 * C0)⁻¹) ^ (2 : ℕ) :=
    pow_pos (inv_pos.mpr (by linarith only [hC0pos])) 2
  refine ⟨min g1 (min (homGamma0Gate Cst) (min (1 / 81) (((4 * C0)⁻¹) ^ (2 : ℕ)))),
    lt_min hg1 (lt_min (homGamma0Gate_pos hCst)
      (lt_min (by norm_num) hquad)), ?_⟩
  intro M hcs hgamma X hX htail hs m
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg_disp : M.gamma ≤ g1 := le_trans hgamma (min_le_left _ _)
  have hg_gate : M.gamma ≤ homGamma0Gate Cst :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hg_81 : M.gamma ≤ 1 / 81 :=
    le_trans hgamma
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hg_C : M.gamma ≤ ((4 * C0)⁻¹) ^ (2 : ℕ) :=
    le_trans hgamma
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hL4 : 4 ≤ |Real.log M.gamma| := four_le_absLog hgpos hg_81
  have hLpos : (0 : ℝ) < |Real.log M.gamma| := by linarith only [hL4]
  have hg1lt : M.gamma < 1 := by linarith only [hg_81]
  have hY0 : ∀ p : ℝ, 1 ≤ p →
      p ≤ (homGateRangeConst Cst)⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ w, homMinimalScaleFactor (1 - homAlpha M) X w ^ (2 * p)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal 2 ^ (2 * p) := by
    intro p hp hrange
    exact homY_moment_bound_of_gamma_le M hX hCst hp hL4 hg_gate hrange htail
  have hdispM := hdisp M hcs hg_disp hs m (homMinimalScaleFactor (1 - homAlpha M) X)
    (measurable_homMinimalScaleFactor _ hX).aemeasurable hY0 Cgap hCgap
  have hone : (1 : ℝ) ≤ C0⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ :=
    one_le_reciprocal_range hC0pos hgpos hg1lt hLpos hg_C
  have hmeas : Measurable (ethmB M Cgap
      (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
      (homN M m) (homSeamBase M hs)) :=
    measurable_ethmB M Cgap
      (measurable_seamEnlargedY M m Ctop (measurable_homMinimalScaleFactor _ hX))
      (homN_le M m) _
  have h1 := hdispM 1 le_rfl hone
  have hrw : (∫⁻ omega, ethmB M Cgap
        (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
        (homN M m) (homSeamBase M hs) omega
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫⁻ omega, ethmB M Cgap
          (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
          (homN M m) (homSeamBase M hs) omega ^ (1 : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    refine lintegral_congr fun omega => ?_
    rw [ENNReal.rpow_one]
  have hne : (∫⁻ omega, ethmB M Cgap
      (seamEnlargedY M m Ctop (homMinimalScaleFactor (1 - homAlpha M) X)) m
      (homN M m) (homSeamBase M hs) omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≠ ⊤ := by
    rw [hrw]
    refine ne_top_of_le_ne_top ?_ h1
    rw [ENNReal.rpow_one]
    exact ENNReal.ofReal_ne_top
  exact (ae_lt_top' hmeas.aemeasurable hne).mono fun omega homega => homega.ne

end

end Algsuperdiff.Section4.Provider.Homogenization
