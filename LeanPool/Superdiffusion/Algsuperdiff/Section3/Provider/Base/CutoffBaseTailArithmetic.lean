/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.CutoffResponseMass
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarPlusUpperBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Scales.Landmarks

/-!
# CutoffBaseTailArithmetic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Scalar amplitudes for the cutoff base-case tails

This module puts the plateau-plus-mass response estimate into the exact scalar
forms consumed by the three corrected Section 3.2 base-case error clauses.  It
first extracts dimension-only square-root constants for the deterministic
plateau and the weighted `Gamma_1` mass tail.  It then proves their all-scale
normal forms and specializes the common scale core at `m**` and `m*`.

## Main results

* `cutoffMassSqrtConst`, `cutoffPlateauSqrtConst`, and
  `cutoffBaseSqrtConst` are positive dimension-only constants.
* `sqrt_cutoffMassTailScale_le_allScale` and
  `sqrt_cutoffPlateauAmplitude_le_allScale` give the two all-scale
  square-root amplitudes.
* The corresponding `_le_mStarStar` results give the exact `m <= m**`
  amplitudes.
* `sqrt_cutoffMassTailScale_le_mStar` and
  `sqrt_cutoffPlateauAmplitude_le_one_of_le_mStar` give the random and
  deterministic parts of the shifted `m <= m*` estimate.
-/

namespace Algsuperdiff.Section3.Provider.Base

open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3.Provider.Scales

noncomputable section

variable {d : ℕ}

/-! ## Dimension-only constants -/

/-- Dimension-only square-root coefficient of the weighted `Gamma_1` mass
tail. -/
noncomputable def cutoffMassSqrtConst (d : ℕ) : ℝ :=
  Real.sqrt
    (gammaTriangleConst 1 * Stream.cutoffFrobeniusMassFiniteConst d)

/-- The weighted-mass square-root coefficient is strictly positive. -/
theorem cutoffMassSqrtConst_pos (d : ℕ) :
    0 < cutoffMassSqrtConst d := by
  exact Real.sqrt_pos_of_pos
    (mul_pos gammaTriangleConst_pos
      (Stream.cutoffFrobeniusMassFiniteConst_pos d))

/-- Dimension-only square-root envelope for the deterministic plateau. -/
noncomputable def cutoffPlateauSqrtConst (d : ℕ) : ℝ :=
  Real.sqrt (Disorder.cstarPlusUpperBound d)

/-- The deterministic-plateau square-root envelope is strictly positive. -/
theorem cutoffPlateauSqrtConst_pos (d : ℕ) :
    0 < cutoffPlateauSqrtConst d := by
  exact Real.sqrt_pos_of_pos (Disorder.cstarPlusUpperBound_pos d)

/-- Common dimension-only coefficient before the universal probabilistic
square-root conversion. -/
noncomputable def cutoffBaseSqrtConst (d : ℕ) : ℝ :=
  cutoffPlateauSqrtConst d + cutoffMassSqrtConst d

/-- The common cutoff base coefficient is strictly positive. -/
theorem cutoffBaseSqrtConst_pos (d : ℕ) :
    0 < cutoffBaseSqrtConst d := by
  exact add_pos (cutoffPlateauSqrtConst_pos d) (cutoffMassSqrtConst_pos d)

/-! ## Scalar square-root normal forms -/

private theorem rpow_half_sq (gamma : ℝ) (m : ℤ) :
    ((3 : ℝ) ^ (gamma * (m : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * gamma * (m : ℝ)) := by
  calc
    ((3 : ℝ) ^ (gamma * (m : ℝ))) ^ 2 =
        ((3 : ℝ) ^ (gamma * (m : ℝ))) ^ (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    _ = (3 : ℝ) ^ ((gamma * (m : ℝ)) * 2) :=
      (Real.rpow_mul (by norm_num) _ _).symm
    _ = (3 : ℝ) ^ (2 * gamma * (m : ℝ)) := by ring_nf

private theorem sqrt_inv_sq {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ ^ 2 = x⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hx]

private theorem one_lt_log_three : (1 : ℝ) < Real.log 3 :=
  (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
    (lt_trans Real.exp_one_lt_d9 (by norm_num))

private theorem landmark_starStar_core_sq_le
    {nu gamma c ell R : ℝ}
    (hnu : 0 < nu) (hgamma : 0 < gamma) (hgamma_one : gamma ≤ 1)
    (hc : 0 < c) (hell : 1 ≤ ell)
    (hR : R ≤ nu ^ 2 * gamma ^ 3 / (2 * ell * c)) :
    nu⁻¹ ^ 2 * gamma⁻¹ * R ≤ c⁻¹ * gamma := by
  have hden_pos : 0 < 2 * ell * c :=
    mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hell)) hc
  have hc_le_den : c ≤ 2 * ell * c := by
    have hone : (1 : ℝ) ≤ 2 * ell := by linarith only [hell]
    calc
      c = 1 * c := (one_mul c).symm
      _ ≤ (2 * ell) * c := mul_le_mul_of_nonneg_right hone hc.le
      _ = 2 * ell * c := by ring
  have hnum_nonneg : 0 ≤ nu ^ 2 * gamma ^ 3 := by positivity
  have hfrac :
      nu ^ 2 * gamma ^ 3 / (2 * ell * c) ≤
        nu ^ 2 * gamma ^ 3 / c := by
    rw [div_le_div_iff₀ hden_pos hc]
    exact mul_le_mul_of_nonneg_left hc_le_den hnum_nonneg
  have hmult := mul_le_mul_of_nonneg_left (hR.trans hfrac)
    (mul_nonneg (sq_nonneg nu⁻¹) (inv_nonneg.mpr hgamma.le))
  have hcollapse :
      (nu⁻¹ ^ 2 * gamma⁻¹) * (nu ^ 2 * gamma ^ 3 / c) =
        c⁻¹ * gamma ^ 2 := by
    field_simp [hnu.ne', hgamma.ne', hc.ne']
  have hgamma_sq : gamma ^ 2 ≤ gamma := by
    nlinarith only [hgamma.le, hgamma_one]
  calc
    nu⁻¹ ^ 2 * gamma⁻¹ * R =
        (nu⁻¹ ^ 2 * gamma⁻¹) * R := by ring
    _ ≤ (nu⁻¹ ^ 2 * gamma⁻¹) *
          (nu ^ 2 * gamma ^ 3 / c) := hmult
    _ = c⁻¹ * gamma ^ 2 := hcollapse
    _ ≤ c⁻¹ * gamma :=
      mul_le_mul_of_nonneg_left hgamma_sq (inv_nonneg.mpr hc.le)

private theorem landmark_star_core_sq_le
    {nu gamma c ell R : ℝ}
    (hnu : 0 < nu) (hgamma : 0 < gamma) (hc : 0 < c)
    (hell : 1 ≤ ell)
    (hR : R ≤ nu ^ 2 * gamma / (2 * ell * c)) :
    nu⁻¹ ^ 2 * gamma⁻¹ * R ≤ c⁻¹ := by
  have hden_pos : 0 < 2 * ell * c :=
    mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hell)) hc
  have hc_le_den : c ≤ 2 * ell * c := by
    have hone : (1 : ℝ) ≤ 2 * ell := by linarith only [hell]
    calc
      c = 1 * c := (one_mul c).symm
      _ ≤ (2 * ell) * c := mul_le_mul_of_nonneg_right hone hc.le
      _ = 2 * ell * c := by ring
  have hnum_nonneg : 0 ≤ nu ^ 2 * gamma := by positivity
  have hfrac : nu ^ 2 * gamma / (2 * ell * c) ≤ nu ^ 2 * gamma / c := by
    rw [div_le_div_iff₀ hden_pos hc]
    exact mul_le_mul_of_nonneg_left hc_le_den hnum_nonneg
  have hmult := mul_le_mul_of_nonneg_left (hR.trans hfrac)
    (mul_nonneg (sq_nonneg nu⁻¹) (inv_nonneg.mpr hgamma.le))
  calc
    nu⁻¹ ^ 2 * gamma⁻¹ * R =
        (nu⁻¹ ^ 2 * gamma⁻¹) * R := by ring
    _ ≤ (nu⁻¹ ^ 2 * gamma⁻¹) * (nu ^ 2 * gamma / c) := hmult
    _ = c⁻¹ := by
      field_simp [hnu.ne', hgamma.ne', hc.ne']

private theorem allScaleCore_le_mStarStar
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStarStar M) :
    M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) ≤
      (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hc : 0 < Disorder.cstarPlus M := Disorder.cstarPlus_pos M
  have hgamma_one : M.gamma ≤ 1 :=
    M.shellPrefix.gamma_le_quarter.trans (by norm_num)
  have hsq := landmark_starStar_core_sq_le M.nu_pos hgamma hgamma_one hc
    (le_of_lt one_lt_log_three)
    ((Provider.Scales.le_mStarStar_iff_rpow_le M m).mp hm)
  have hleft :
      0 ≤ M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr M.nu_pos.le)
        (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hright :
      0 ≤ (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
        Real.sqrt M.gamma := by positivity
  apply (sq_le_sq₀ hleft hright).mp
  rw [show
      (M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
          (3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2 =
        M.nu⁻¹ ^ 2 * ((Real.sqrt M.gamma)⁻¹ ^ 2) *
          (((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2) by ring,
    sqrt_inv_sq hgamma.le, rpow_half_sq,
    show
      ((Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma) ^ 2 =
        (Real.sqrt (Disorder.cstarPlus M))⁻¹ ^ 2 *
          (Real.sqrt M.gamma) ^ 2 by ring,
    sqrt_inv_sq hc.le, Real.sq_sqrt hgamma.le]
  exact hsq

private theorem allScaleCore_le_mStar
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStar M) :
    M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) ≤
      (Real.sqrt (Disorder.cstarPlus M))⁻¹ := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hc : 0 < Disorder.cstarPlus M := Disorder.cstarPlus_pos M
  have hsq := landmark_star_core_sq_le M.nu_pos hgamma hc
    (le_of_lt one_lt_log_three)
    ((Provider.Scales.le_mStar_iff_rpow_le M m).mp hm)
  have hleft :
      0 ≤ M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr M.nu_pos.le)
        (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hright : 0 ≤ (Real.sqrt (Disorder.cstarPlus M))⁻¹ := by positivity
  apply (sq_le_sq₀ hleft hright).mp
  rw [show
      (M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
          (3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2 =
        M.nu⁻¹ ^ 2 * ((Real.sqrt M.gamma)⁻¹ ^ 2) *
          (((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2) by ring,
    sqrt_inv_sq hgamma.le, rpow_half_sq,
    show ((Real.sqrt (Disorder.cstarPlus M))⁻¹) ^ 2 =
        (Real.sqrt (Disorder.cstarPlus M))⁻¹ ^ 2 by rfl,
    sqrt_inv_sq hc.le]
  exact hsq

private theorem sqrt_cutoffMassTailScale_eq_allScale
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    Real.sqrt
        (gammaTriangleConst 1 * cutoffMassLinearWeightedScale M m s) =
      cutoffMassSqrtConst d * M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) * Real.sqrt (baseLoss d s) := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hconst :
      0 ≤ gammaTriangleConst 1 * Stream.cutoffFrobeniusMassFiniteConst d :=
    mul_nonneg gammaTriangleConst_pos.le
      (Stream.cutoffFrobeniusMassFiniteConst_pos d).le
  have hloss : 0 ≤ baseLoss d s := (baseLoss_pos d s).le
  let R : ℝ :=
    cutoffMassSqrtConst d * M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
      (3 : ℝ) ^ (M.gamma * (m : ℝ)) * Real.sqrt (baseLoss d s)
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (cutoffMassSqrtConst_pos d).le
            (inv_nonneg.mpr M.nu_pos.le))
          (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        (Real.rpow_pos_of_pos (by norm_num) _).le)
      (Real.sqrt_nonneg _)
  have hRsq : R ^ 2 =
      gammaTriangleConst 1 * cutoffMassLinearWeightedScale M m s := by
    rw [show R ^ 2 =
        cutoffMassSqrtConst d ^ 2 * M.nu⁻¹ ^ 2 *
          ((Real.sqrt M.gamma)⁻¹ ^ 2) *
          (((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2) *
          (Real.sqrt (baseLoss d s)) ^ 2 by
      dsimp only [R]
      ring,
      cutoffMassSqrtConst, Real.sq_sqrt hconst,
      sqrt_inv_sq hgamma.le, rpow_half_sq,
      Real.sq_sqrt hloss, cutoffMassLinearWeightedScale]
    ring_nf
  calc
    Real.sqrt (gammaTriangleConst 1 * cutoffMassLinearWeightedScale M m s) =
        Real.sqrt (R ^ 2) := by rw [hRsq]
    _ = R := Real.sqrt_sq hR

/-- The square root of the weighted `Gamma_1` tail scale has the exact
all-scale `nu⁻¹ gamma⁻¹⁄² 3^(gamma m) sqrt(baseLoss)` form. -/
theorem sqrt_cutoffMassTailScale_le_allScale
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    Real.sqrt
        (gammaTriangleConst 1 * cutoffMassLinearWeightedScale M m s) ≤
      cutoffMassSqrtConst d * M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) * Real.sqrt (baseLoss d s) := by
  exact (sqrt_cutoffMassTailScale_eq_allScale M m s).le

private theorem cutoffPlateauAmplitude_le_allScale_sq
    (M : ABKModel d) (m : ℤ) :
    cutoffPlateauAmplitude M m ≤
      (cutoffPlateauSqrtConst d * M.nu⁻¹ *
        (Real.sqrt M.gamma)⁻¹ *
          (3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2 := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hc : 0 < Disorder.cstarPlus M := Disorder.cstarPlus_pos M
  have hU := Disorder.cstarPlus_le_cstarPlusUpperBound M
  have hcoef : (1 + 4 * M.gamma) / 2 ≤ 1 := by
    linarith only [M.shellPrefix.gamma_le_quarter]
  have hcoef_nonneg : 0 ≤ (1 + 4 * M.gamma) / 2 := by
    linarith only [hgamma]
  have hcore_nonneg :
      0 ≤ M.nu⁻¹ ^ 2 * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by positivity
  have hraw : cutoffPlateauAmplitude M m ≤
      Disorder.cstarPlusUpperBound d *
        (M.nu⁻¹ ^ 2 * M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
    have hrewrite : cutoffPlateauAmplitude M m =
        (Disorder.cstarPlus M *
          (M.nu⁻¹ ^ 2 * M.gamma⁻¹ *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) *
          ((1 + 4 * M.gamma) / 2) := by
      rw [cutoffPlateauAmplitude]
      field_simp [M.nu_pos.ne']
    rw [hrewrite]
    calc
      (Disorder.cstarPlus M *
          (M.nu⁻¹ ^ 2 * M.gamma⁻¹ *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) *
          ((1 + 4 * M.gamma) / 2)
          ≤ Disorder.cstarPlus M *
              (M.nu⁻¹ ^ 2 * M.gamma⁻¹ *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hcoef
              (mul_nonneg hc.le hcore_nonneg)
      _ ≤ Disorder.cstarPlusUpperBound d *
            (M.nu⁻¹ ^ 2 * M.gamma⁻¹ *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) :=
        mul_le_mul_of_nonneg_right hU hcore_nonneg
  calc
    cutoffPlateauAmplitude M m ≤
        Disorder.cstarPlusUpperBound d *
          (M.nu⁻¹ ^ 2 * M.gamma⁻¹ *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := hraw
    _ = (cutoffPlateauSqrtConst d * M.nu⁻¹ *
          (Real.sqrt M.gamma)⁻¹ *
            (3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2 := by
      rw [show
          (cutoffPlateauSqrtConst d * M.nu⁻¹ *
              (Real.sqrt M.gamma)⁻¹ *
                (3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2 =
            cutoffPlateauSqrtConst d ^ 2 * M.nu⁻¹ ^ 2 *
              ((Real.sqrt M.gamma)⁻¹ ^ 2) *
              (((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2) by ring,
        cutoffPlateauSqrtConst,
        Real.sq_sqrt (Disorder.cstarPlusUpperBound_nonneg d),
        sqrt_inv_sq hgamma.le, rpow_half_sq]
      ring

/-- The deterministic plateau has the same all-scale core as the weighted
mass, with a dimension-only coefficient. -/
theorem sqrt_cutoffPlateauAmplitude_le_allScale
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    Real.sqrt (cutoffPlateauAmplitude M m) ≤
      cutoffPlateauSqrtConst d * M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) * Real.sqrt (baseLoss d s) := by
  let R : ℝ := cutoffPlateauSqrtConst d * M.nu⁻¹ *
    (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (m : ℝ))
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (cutoffPlateauSqrtConst_pos d).le
          (inv_nonneg.mpr M.nu_pos.le))
        (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hroot : Real.sqrt (cutoffPlateauAmplitude M m) ≤ R := by
    exact Real.sqrt_le_iff.mpr
      ⟨hR, by simpa only [R] using cutoffPlateauAmplitude_le_allScale_sq M m⟩
  have hloss : 1 ≤ Real.sqrt (baseLoss d s) := by
    rw [Real.one_le_sqrt]
    exact one_le_baseLoss d s
  calc
    Real.sqrt (cutoffPlateauAmplitude M m) ≤ R := hroot
    _ = R * 1 := (mul_one R).symm
    _ ≤ R * Real.sqrt (baseLoss d s) := mul_le_mul_of_nonneg_left hloss hR
    _ = cutoffPlateauSqrtConst d * M.nu⁻¹ *
          (Real.sqrt M.gamma)⁻¹ *
            (3 : ℝ) ^ (M.gamma * (m : ℝ)) * Real.sqrt (baseLoss d s) := rfl

/-! ## Landmark specializations -/

/-- Below `m**`, the weighted-mass square root has the corrected base-case
`cstarPlus⁻¹⁄² gamma¹⁄² sqrt(baseLoss)` scale. -/
theorem sqrt_cutoffMassTailScale_le_mStarStar
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // s ∈ Set.Ioo 0 1})
    (hm : m ≤ mStarStar M) :
    Real.sqrt
        (gammaTriangleConst 1 * cutoffMassLinearWeightedScale M m s) ≤
      cutoffMassSqrtConst d * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
        Real.sqrt M.gamma * Real.sqrt (baseLoss d s) := by
  rw [sqrt_cutoffMassTailScale_eq_allScale M m s]
  have hconst : 0 ≤ cutoffMassSqrtConst d := (cutoffMassSqrtConst_pos d).le
  have hloss : 0 ≤ Real.sqrt (baseLoss d s) := Real.sqrt_nonneg _
  have hcore := allScaleCore_le_mStarStar M m hm
  calc
    cutoffMassSqrtConst d * M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)) * Real.sqrt (baseLoss d s) =
        cutoffMassSqrtConst d *
          (M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
            (3 : ℝ) ^ (M.gamma * (m : ℝ))) *
              Real.sqrt (baseLoss d s) := by ring
    _ ≤ cutoffMassSqrtConst d *
          ((Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma) *
            Real.sqrt (baseLoss d s) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcore hconst) hloss
    _ = cutoffMassSqrtConst d *
          (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
            Real.sqrt (baseLoss d s) := by ring

/-- Below `m**`, the deterministic plateau obeys the same corrected
base-case scale as the weighted mass. -/
theorem sqrt_cutoffPlateauAmplitude_le_mStarStar
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // s ∈ Set.Ioo 0 1})
    (hm : m ≤ mStarStar M) :
    Real.sqrt (cutoffPlateauAmplitude M m) ≤
      cutoffPlateauSqrtConst d * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
        Real.sqrt M.gamma * Real.sqrt (baseLoss d s) := by
  have hroot := sqrt_cutoffPlateauAmplitude_le_allScale M m s
  have hconst : 0 ≤ cutoffPlateauSqrtConst d :=
    (cutoffPlateauSqrtConst_pos d).le
  have hloss : 0 ≤ Real.sqrt (baseLoss d s) := Real.sqrt_nonneg _
  have hcore := allScaleCore_le_mStarStar M m hm
  calc
    Real.sqrt (cutoffPlateauAmplitude M m) ≤
        cutoffPlateauSqrtConst d * M.nu⁻¹ *
          (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (m : ℝ)) *
            Real.sqrt (baseLoss d s) := hroot
    _ = cutoffPlateauSqrtConst d *
          (M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
            (3 : ℝ) ^ (M.gamma * (m : ℝ))) *
              Real.sqrt (baseLoss d s) := by ring
    _ ≤ cutoffPlateauSqrtConst d *
          ((Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma) *
            Real.sqrt (baseLoss d s) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcore hconst) hloss
    _ = cutoffPlateauSqrtConst d *
          (Real.sqrt (Disorder.cstarPlus M))⁻¹ * Real.sqrt M.gamma *
            Real.sqrt (baseLoss d s) := by ring

/-- Below `m*`, the weighted-mass square root has the corrected shifted
base-case scale. -/
theorem sqrt_cutoffMassTailScale_le_mStar
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // s ∈ Set.Ioo 0 1})
    (hm : m ≤ mStar M) :
    Real.sqrt
        (gammaTriangleConst 1 * cutoffMassLinearWeightedScale M m s) ≤
      cutoffMassSqrtConst d * (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
        Real.sqrt (baseLoss d s) := by
  rw [sqrt_cutoffMassTailScale_eq_allScale M m s]
  have hconst : 0 ≤ cutoffMassSqrtConst d := (cutoffMassSqrtConst_pos d).le
  have hloss : 0 ≤ Real.sqrt (baseLoss d s) := Real.sqrt_nonneg _
  have hcore := allScaleCore_le_mStar M m hm
  calc
    cutoffMassSqrtConst d * M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)) * Real.sqrt (baseLoss d s) =
        cutoffMassSqrtConst d *
          (M.nu⁻¹ * (Real.sqrt M.gamma)⁻¹ *
            (3 : ℝ) ^ (M.gamma * (m : ℝ))) *
              Real.sqrt (baseLoss d s) := by ring
    _ ≤ cutoffMassSqrtConst d *
          (Real.sqrt (Disorder.cstarPlus M))⁻¹ *
            Real.sqrt (baseLoss d s) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcore hconst) hloss

private theorem cutoffPlateauAmplitude_le_one_of_le_mStar
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStar M) :
    cutoffPlateauAmplitude M m ≤ 1 := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hc : 0 < Disorder.cstarPlus M := Disorder.cstarPlus_pos M
  have hlog : 1 < Real.log 3 := one_lt_log_three
  have hpow := (Provider.Scales.le_mStar_iff_rpow_le M m).mp hm
  have hfactor_nonneg :
      0 ≤ Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
        (1 + 4 * M.gamma) := by positivity
  calc
    cutoffPlateauAmplitude M m =
        Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
          (1 + 4 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := rfl
    _ ≤ Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
          (1 + 4 * M.gamma) *
            (M.nu ^ 2 * M.gamma /
              (2 * Real.log 3 * Disorder.cstarPlus M)) :=
      mul_le_mul_of_nonneg_left hpow hfactor_nonneg
    _ = (1 + 4 * M.gamma) / (4 * Real.log 3) := by
      field_simp [M.nu_pos.ne', hgamma.ne', hc.ne', ne_of_gt (by linarith : 0 < Real.log 3)]
      ring
    _ ≤ 1 := by
      rw [div_le_one (by positivity : 0 < 4 * Real.log 3)]
      linarith only [M.shellPrefix.gamma_le_quarter, hlog]

/-- Below `m*`, the deterministic plateau has square root at most one, which
fits inside the frozen deterministic shift `2`. -/
theorem sqrt_cutoffPlateauAmplitude_le_one_of_le_mStar
    (M : ABKModel d) (m : ℤ) (hm : m ≤ mStar M) :
    Real.sqrt (cutoffPlateauAmplitude M m) ≤ 1 := by
  rw [Real.sqrt_le_one]
  exact cutoffPlateauAmplitude_le_one_of_le_mStar M m hm

end

end Algsuperdiff.Section3.Provider.Base
