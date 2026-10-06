/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.TerminalCarrierIdentification
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.CubeToBallArithmetic
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CubeVolume

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.BallTerminalBranchEstimates

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The two radius bands of the large-scale C¹ slope approximation's ball terminal

`ExactRootGaugeTerminal` asserts one decay estimate for **every** radius
`r ∈ Icc rStart R`.  The radius range necessarily splits at
`r = R / (108 √d)`:

* below the threshold (**far branch**) the canonical outer cube of `r` is at a
  generation `q ≤ m`, where `m` is the largest generation whose cube sits inside
  the ball of radius `R`, so the cube row applies and supplies the decay;
* above it (**near band**) `3 ^ q(r)` overshoots `3 ^ m`, the cube row is
  silent, and — because `2 ≤ d` forces `√d > 1` — the band is never empty: it
  always contains `r = R`.

This module renders both bands as standalone estimates over abstract data, so
that the assembly only has to supply the geometry.

The near band consumes one hypothesis this module could not discharge, the
**weighted-energy triangle inequality on the closed ball** (`htri` below).  It
is exactly Minkowski for `‖s^{1/2} ·‖_{L̲²(V)}`; the repository has it only for
`H1Function`s on triadic cubes (`weightedGradNorm_sub_le_add_sub_h1`), never for
a general set.  Its statement is passed in, never assumed globally.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The law-free geometric price of the far branch. -/
@[expose]
def farBranchConstant (d : ℕ) : ℝ :=
  ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (36 * Real.sqrt d) *
    ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)

/-- The law-free geometric price of the near band. -/
@[expose]
def nearBranchConstant (d : ℕ) (B Aslope : ℝ) : ℝ :=
  ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
      (1 + ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
        ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) *
    (108 * Real.sqrt d)

theorem farBranchConstant_pos [NeZero d] : 0 < farBranchConstant d := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  unfold farBranchConstant
  have h1 : (0 : ℝ) < ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have h2 : (0 : ℝ) < ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  positivity

/-! ## A volume-ratio bound, lifted to the `(1/2)`-power -/

private theorem rpow_half_ratio_le [NeZero d] {U V : Set (Vec d)} {C : ℝ}
    (hC : 0 < C) (h : volume V / volume U ≤ ENNReal.ofReal C) :
    (volume V / volume U) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (C ^ (1 / 2 : ℝ)) := by
  rw [← ENNReal.ofReal_rpow_of_pos hC]
  exact ENNReal.rpow_le_rpow h (by norm_num)

/-! ## The far branch -/

/-- **The far branch.**  Ball → canonical outer cube → cube row → inner cube →
ball, with the generation gap converted to a radius ratio. -/
theorem farBranch_estimate (d : ℕ) [NeZero d]
    {aIdentity : Book.Ch03.CoeffFamily d} {bRef : CoeffField d}
    (hcoeff : ∀ Q : TriadicCube d,
      bRef =ᵐ[volume] (aIdentity.coeffOn Q).toCoeffField)
    {eta A r R : ℝ} {q m : ℕ}
    (hetaNonneg : 0 ≤ eta) (hetaOne : eta ≤ 1) (hA : 0 < A)
    (hr : 0 < r) (hR : 0 < R) (hqm : q ≤ m)
    (hq3 : (3 : ℝ) ^ q ≤ 12 * r)
    (hcube : closedNormBall d r ⊆ openCubeSet (originCube d (q : ℤ)))
    (hratioIn : volume (openCubeSet (originCube d (q : ℤ))) /
      volume (closedNormBall d r) ≤ ENNReal.ofReal ((6 * Real.sqrt d) ^ d))
    (hmR : Real.sqrt d * (3 : ℝ) ^ m ≤ R)
    (hmRmax : R < 3 * (Real.sqrt d * (3 : ℝ) ^ m))
    (F G : Vec d → Vec d)
    (hrow : weightedGradNorm
        (aIdentity.coeffOn (originCube d (q : ℤ))).toCoeffField
        (openCubeSet (originCube d (q : ℤ))) F ≤
      ENNReal.ofReal (A * Real.rpow 3 (-eta * ((m - q : ℕ) : ℝ))) *
        weightedGradNorm
          (aIdentity.coeffOn (originCube d (m : ℤ))).toCoeffField
          (openCubeSet (originCube d (m : ℤ))) G) :
    weightedGradNorm bRef (closedNormBall d r) F ≤
      ENNReal.ofReal (farBranchConstant d * A * (r / R) ^ eta) *
        weightedGradNorm bRef (closedNormBall d R) G := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hin : (0 : ℝ) < (6 * Real.sqrt d) ^ d := by positivity
  have hout : (0 : ℝ) < (12 * Real.sqrt d) ^ d := by positivity
  -- ball → cube at generation `q`
  have hstep1 : weightedGradNorm bRef (closedNormBall d r) F =
      weightedGradNorm
        (aIdentity.coeffOn (originCube d (q : ℤ))).toCoeffField
        (closedNormBall d r) F :=
    weightedGradNorm_congr_coeff_ae_on F (ae_restrict_of_ae (hcoeff _))
  have hstep2 := weightedGradNorm_closedNormBall_le_cube hr hcube
    (volume_openCubeSet_ne_zero _) (volume_openCubeSet_ne_top _)
    (aIdentity.coeffOn (originCube d (q : ℤ))).toCoeffField F
  have hstep2' : weightedGradNorm
      (aIdentity.coeffOn (originCube d (q : ℤ))).toCoeffField
      (closedNormBall d r) F ≤
      ENNReal.ofReal (((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) *
        weightedGradNorm
          (aIdentity.coeffOn (originCube d (q : ℤ))).toCoeffField
          (openCubeSet (originCube d (q : ℤ))) F :=
    hstep2.trans (mul_le_mul_left (rpow_half_ratio_le hin hratioIn) _)
  -- cube at generation `m` → ball
  have hstep4 := weightedGradNorm_cube_le_closedNormBall hR
    (openCubeSet_originCube_subset_closedNormBall m hmR)
    (volume_openCubeSet_ne_zero _) (volume_openCubeSet_ne_top _)
    (aIdentity.coeffOn (originCube d (m : ℤ))).toCoeffField G
  have hstep4' : weightedGradNorm
      (aIdentity.coeffOn (originCube d (m : ℤ))).toCoeffField
      (openCubeSet (originCube d (m : ℤ))) G ≤
      ENNReal.ofReal (((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) *
        weightedGradNorm bRef (closedNormBall d R) G := by
    refine hstep4.trans ?_
    have hcoeffR : weightedGradNorm
        (aIdentity.coeffOn (originCube d (m : ℤ))).toCoeffField
        (closedNormBall d R) G =
        weightedGradNorm bRef (closedNormBall d R) G :=
      (weightedGradNorm_congr_coeff_ae_on G (ae_restrict_of_ae (hcoeff _))).symm
    rw [hcoeffR]
    exact mul_le_mul_left
      (rpow_half_ratio_le hout
        (closedNormBall_cube_volume_ratio_le m hmR hmRmax)) _
  -- the decay conversion
  have hdecay : A * Real.rpow 3 (-eta * ((m - q : ℕ) : ℝ)) ≤
      A * ((36 * Real.sqrt d) * (r / R) ^ eta) := by
    have hK₂ : (0 : ℝ) < (3 * Real.sqrt d)⁻¹ := by positivity
    have hmscale : (3 * Real.sqrt d)⁻¹ * R ≤ (3 : ℝ) ^ m := by
      rw [inv_mul_eq_div, div_le_iff₀ (by positivity : (0 : ℝ) < 3 * Real.sqrt d)]
      have : R < (3 : ℝ) ^ m * (3 * Real.sqrt d) := by
        have := hmRmax
        linarith only [this]
      linarith only [this]
    have hconv := triadicGap_le_radiusRatio (K₁ := (12 : ℝ))
      (K₂ := (3 * Real.sqrt d)⁻¹) hqm hetaNonneg (by norm_num) hK₂ hr hR
      hq3 hmscale
    have hfold : ((12 : ℝ) / (3 * Real.sqrt d)⁻¹) = 36 * Real.sqrt d := by
      field_simp
      ring
    rw [hfold] at hconv
    have hbase : (36 * Real.sqrt d) ^ eta ≤ 36 * Real.sqrt d := by
      have hone : (1 : ℝ) ≤ 36 * Real.sqrt d := by
        have hdnat : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
        have hdge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdnat
        have h1 : (1 : ℝ) ≤ Real.sqrt d := by
          have hsqle := Real.sqrt_le_sqrt hdge1
          rwa [Real.sqrt_one] at hsqle
        linarith only [h1]
      have hpow := Real.rpow_le_rpow_of_exponent_le hone hetaOne
      rwa [Real.rpow_one] at hpow
    have hratio0 : (0 : ℝ) ≤ (r / R) ^ eta :=
      Real.rpow_nonneg (by positivity) _
    have hstep : (36 * Real.sqrt d) ^ eta * (r / R) ^ eta ≤
        (36 * Real.sqrt d) * (r / R) ^ eta :=
      mul_le_mul_of_nonneg_right hbase hratio0
    exact mul_le_mul_of_nonneg_left (hconv.trans hstep) hA.le
  -- assemble
  have hcombine : weightedGradNorm bRef (closedNormBall d r) F ≤
      ENNReal.ofReal (((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) *
        (ENNReal.ofReal (A * ((36 * Real.sqrt d) * (r / R) ^ eta)) *
          (ENNReal.ofReal (((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) *
            weightedGradNorm bRef (closedNormBall d R) G)) := by
    rw [hstep1]
    refine hstep2'.trans ?_
    refine mul_le_mul' le_rfl ?_
    refine hrow.trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal hdecay) hstep4'
  refine hcombine.trans_eq ?_
  have hnn1 : (0 : ℝ) ≤ ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg hin.le _
  have hnn2 : (0 : ℝ) ≤ ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg hout.le _
  have hnn3 : (0 : ℝ) ≤ A * ((36 * Real.sqrt d) * (r / R) ^ eta) := by
    have : (0 : ℝ) ≤ (r / R) ^ eta := Real.rpow_nonneg (by positivity) _
    positivity
  rw [← mul_assoc, ← ENNReal.ofReal_mul hnn1, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  unfold farBranchConstant
  ring

/-! ## The near band -/

/-- **The near band.**  Ball → ball, then the triangle inequality, then the
corrector's own energy against the solution's. -/
theorem nearBranch_estimate (d : ℕ) [NeZero d]
    {aIdentity : Book.Ch03.CoeffFamily d} {bRef : CoeffField d}
    (hcoeff : ∀ Q : TriadicCube d,
      bRef =ᵐ[volume] (aIdentity.coeffOn Q).toCoeffField)
    {eta B Aslope r R : ℝ} {m J : ℕ} {e : Vec d}
    (_hetaNonneg : 0 ≤ eta) (hetaOne : eta ≤ 1)
    (hB : 0 < B) (hAslope : 0 < Aslope)
    (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (hnear : R < 108 * (Real.sqrt d * r))
    (hcubeJ : closedNormBall d R ⊆ openCubeSet (originCube d (J : ℤ)))
    (hratioJ : volume (openCubeSet (originCube d (J : ℤ))) /
      volume (closedNormBall d R) ≤ ENNReal.ofReal ((6 * Real.sqrt d) ^ d))
    (hmR : Real.sqrt d * (3 : ℝ) ^ m ≤ R)
    (hmRmax : R < 3 * (Real.sqrt d * (3 : ℝ) ^ m))
    (Du Cor : Vec d → Vec d)
    (htri : weightedGradNorm bRef (closedNormBall d R) (fun y ↦ Du y - Cor y) ≤
      weightedGradNorm bRef (closedNormBall d R) Du +
        weightedGradNorm bRef (closedNormBall d R) Cor)
    (hcorEnergy : weightedGradNorm
        (aIdentity.coeffOn (originCube d (J : ℤ))).toCoeffField
        (openCubeSet (originCube d (J : ℤ))) Cor ≤
      ENNReal.ofReal (B * euclideanNorm e))
    (hslope : ENNReal.ofReal (euclideanNorm e) ≤ ENNReal.ofReal Aslope *
      weightedGradNorm
        (aIdentity.coeffOn (originCube d (m : ℤ))).toCoeffField
        (openCubeSet (originCube d (m : ℤ))) Du) :
    weightedGradNorm bRef (closedNormBall d r) (fun y ↦ Du y - Cor y) ≤
      ENNReal.ofReal (nearBranchConstant d B Aslope * (r / R) ^ eta) *
        weightedGradNorm bRef (closedNormBall d R) Du := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hin : (0 : ℝ) < (6 * Real.sqrt d) ^ d := by positivity
  have hout : (0 : ℝ) < (12 * Real.sqrt d) ^ d := by positivity
  have hnearC : (0 : ℝ) < (216 * Real.sqrt d) ^ d := by positivity
  set NDu : ℝ≥0∞ := weightedGradNorm bRef (closedNormBall d R) Du with hNDu
  -- the corrector's energy on the big ball
  have hcorBall : weightedGradNorm bRef (closedNormBall d R) Cor ≤
      ENNReal.ofReal (((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
          ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) * NDu := by
    have hc1 : weightedGradNorm bRef (closedNormBall d R) Cor =
        weightedGradNorm
          (aIdentity.coeffOn (originCube d (J : ℤ))).toCoeffField
          (closedNormBall d R) Cor :=
      weightedGradNorm_congr_coeff_ae_on Cor (ae_restrict_of_ae (hcoeff _))
    have hc2 := weightedGradNorm_closedNormBall_le_cube hR hcubeJ
      (volume_openCubeSet_ne_zero _) (volume_openCubeSet_ne_top _)
      (aIdentity.coeffOn (originCube d (J : ℤ))).toCoeffField Cor
    have hc2' : weightedGradNorm
        (aIdentity.coeffOn (originCube d (J : ℤ))).toCoeffField
        (closedNormBall d R) Cor ≤
        ENNReal.ofReal (((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) *
          ENNReal.ofReal (B * euclideanNorm e) :=
      (hc2.trans (mul_le_mul_left (rpow_half_ratio_le hin hratioJ) _)).trans
        (mul_le_mul' le_rfl hcorEnergy)
    -- `B * ‖e‖` against the solution's energy on `Q_m`, then on the ball
    have hslopeBall : ENNReal.ofReal (B * euclideanNorm e) ≤
        ENNReal.ofReal (B * Aslope) *
          (ENNReal.ofReal (((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) * NDu) := by
      have hBe : ENNReal.ofReal (B * euclideanNorm e) =
          ENNReal.ofReal B * ENNReal.ofReal (euclideanNorm e) :=
        ENNReal.ofReal_mul hB.le
      have hmBall := weightedGradNorm_cube_le_closedNormBall hR
        (openCubeSet_originCube_subset_closedNormBall m hmR)
        (volume_openCubeSet_ne_zero _) (volume_openCubeSet_ne_top _)
        (aIdentity.coeffOn (originCube d (m : ℤ))).toCoeffField Du
      have hmBall' : weightedGradNorm
          (aIdentity.coeffOn (originCube d (m : ℤ))).toCoeffField
          (openCubeSet (originCube d (m : ℤ))) Du ≤
          ENNReal.ofReal (((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) * NDu := by
        refine hmBall.trans ?_
        have hcoeffR : weightedGradNorm
            (aIdentity.coeffOn (originCube d (m : ℤ))).toCoeffField
            (closedNormBall d R) Du = NDu :=
          (weightedGradNorm_congr_coeff_ae_on Du
            (ae_restrict_of_ae (hcoeff _))).symm
        rw [hcoeffR]
        exact mul_le_mul_left
          (rpow_half_ratio_le hout
            (closedNormBall_cube_volume_ratio_le m hmR hmRmax)) _
      calc ENNReal.ofReal (B * euclideanNorm e)
          = ENNReal.ofReal B * ENNReal.ofReal (euclideanNorm e) := hBe
        _ ≤ ENNReal.ofReal B * (ENNReal.ofReal Aslope *
              weightedGradNorm
                (aIdentity.coeffOn (originCube d (m : ℤ))).toCoeffField
                (openCubeSet (originCube d (m : ℤ))) Du) :=
            mul_le_mul' le_rfl hslope
        _ ≤ ENNReal.ofReal B * (ENNReal.ofReal Aslope *
              (ENNReal.ofReal (((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) *
                NDu)) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl hmBall')
        _ = ENNReal.ofReal (B * Aslope) *
              (ENNReal.ofReal (((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) *
                NDu) := by
            rw [ENNReal.ofReal_mul hB.le, mul_assoc]
    rw [hc1]
    refine (hc2'.trans (mul_le_mul' le_rfl hslopeBall)).trans_eq ?_
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  -- the ball-to-ball comparison and the triangle
  have hstep := weightedGradNorm_closedNormBall_le_of_near hr hR hrR hnear
    bRef (fun y ↦ Du y - Cor y)
  have hsum : weightedGradNorm bRef (closedNormBall d R) (fun y ↦ Du y - Cor y) ≤
      ENNReal.ofReal (1 + ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
        ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) * NDu := by
    refine htri.trans ?_
    have hone : NDu = ENNReal.ofReal (1 : ℝ) * NDu := by
      rw [ENNReal.ofReal_one, one_mul]
    calc NDu + weightedGradNorm bRef (closedNormBall d R) Cor
        ≤ ENNReal.ofReal (1 : ℝ) * NDu +
          ENNReal.ofReal (((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
            ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) * NDu :=
          add_le_add (le_of_eq hone) hcorBall
      _ = ENNReal.ofReal (1 + ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
            (B * Aslope) * ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) * NDu := by
          rw [← add_mul, ← ENNReal.ofReal_add zero_le_one (by positivity)]
  -- the radius ratio is bounded below on the near band
  have hratioLower : (1 : ℝ) ≤ (108 * Real.sqrt d) * (r / R) ^ eta := by
    have hrR1 : r / R ≤ 1 := (div_le_one hR).2 hrR
    have hrRpos : (0 : ℝ) < r / R := by positivity
    have hpow : r / R ≤ (r / R) ^ eta := by
      have h := Real.rpow_le_rpow_of_exponent_ge hrRpos hrR1 hetaOne
      rwa [Real.rpow_one] at h
    have hlow : 1 < (108 * Real.sqrt d) * (r / R) := by
      rw [← mul_div_assoc, lt_div_iff₀ hR, one_mul]
      linarith only [hnear]
    have hcoef : (0 : ℝ) ≤ 108 * Real.sqrt d := by positivity
    have := mul_le_mul_of_nonneg_left hpow hcoef
    linarith only [hlow, this]
  -- collect
  refine (hstep.trans (mul_le_mul' le_rfl hsum)).trans ?_
  have hCpos : (0 : ℝ) ≤ ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg hnearC.le _
  have hDpos : (0 : ℝ) ≤ 1 + ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
      (B * Aslope) * ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) := by positivity
  have hmerge : (ENNReal.ofReal ((216 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal (1 + ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
        (B * Aslope) * ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) * NDu) =
      ENNReal.ofReal (((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
        (1 + ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
          ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ))) * NDu := by
    rw [ENNReal.ofReal_rpow_of_pos hnearC, ← mul_assoc,
      ← ENNReal.ofReal_mul hCpos]
  rw [hmerge]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  unfold nearBranchConstant
  have hbase : (0 : ℝ) ≤ ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
      (1 + ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
        ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) := by positivity
  calc ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
        (1 + ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
          ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ))
      = (((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
          (1 + ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
            ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ))) * 1 := by ring
    _ ≤ (((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
          (1 + ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
            ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ))) *
          ((108 * Real.sqrt d) * (r / R) ^ eta) :=
        mul_le_mul_of_nonneg_left hratioLower hbase
    _ = ((216 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) *
          (1 + ((6 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ) * (B * Aslope) *
            ((12 * Real.sqrt d) ^ d) ^ (1 / 2 : ℝ)) *
          (108 * Real.sqrt d) * (r / R) ^ eta := by ring

end

end CorrectorComposition
end HighContrast
end HCPolySupport
