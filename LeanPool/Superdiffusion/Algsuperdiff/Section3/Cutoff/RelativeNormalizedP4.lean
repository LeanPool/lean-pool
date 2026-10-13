/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.RelativeNormalization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4Moments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4UpperLaw

/-!
# RelativeNormalizedP4

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# for the same-cutoff relative normalization

The relative law is an arbitrary integer triadic dilation, so CoarseGraining's
natural-depth transport cannot be applied directly.  This file proves the two
exact deterministic dilation identities at an arbitrary integer exponent and
transports the already established arbitrary-cube cutoff moments.
-/

namespace Algsuperdiff.Section3.Cutoff

open Filter MeasureTheory Set
open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The upper Chapter 4 multiscale observable shifts by an arbitrary integer
triadic dilation. -/
theorem LambdaSqCoeffField_dilateReg_of_aelocallyUniformlyElliptic
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (k : ℤ) (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent) :
    Ch04.LambdaSqCoeffField Q s q (dilateReg k a) =
      Ch04.LambdaSqCoeffField (Ch02.dilateCube (-k) Q) s q a := by
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let hk := aelocallyUniformlyEllipticField_dilateReg ha k
  let G : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField (dilateReg k a) hk
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate k F
  let Qsrc : TriadicCube d := Ch02.dilateCube (-k) Q
  have htarget : Ch02.dilateCube k Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_dilateCube_neg k Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F, hk] using triadicCoeffFamily_dilateReg_aeeq_dilate ha k
  have hAEEq := Ch02.LambdaSq_eq_ofAEEq hGB Q s q
  have hdilate :=
    Ch02.LambdaSq_dilate (Ch02.TriadicCoeffFamily.isDilation_dilate k F) Qsrc s q
  calc
    Ch04.LambdaSqCoeffField Q s q (dilateReg k a) = Ch02.LambdaSq Q s q G := by
      simp [Ch04.LambdaSqCoeffField, G, hk]
    _ = Ch02.LambdaSq Q s q B := hAEEq
    _ = Ch02.LambdaSq Qsrc s q F := by
      simpa [Qsrc, htarget, B] using hdilate
    _ = Ch04.LambdaSqCoeffField Qsrc s q a := by
      simp [Ch04.LambdaSqCoeffField, F, ha]

omit [NeZero d] in
/-- The lower Chapter 4 multiscale observable shifts by an arbitrary integer
triadic dilation. -/
theorem lambdaSqCoeffField_dilateReg_of_aelocallyUniformlyElliptic
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (k : ℤ) (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent) :
    Ch04.lambdaSqCoeffField Q s q (dilateReg k a) =
      Ch04.lambdaSqCoeffField (Ch02.dilateCube (-k) Q) s q a := by
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let hk := aelocallyUniformlyEllipticField_dilateReg ha k
  let G : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField (dilateReg k a) hk
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate k F
  let Qsrc : TriadicCube d := Ch02.dilateCube (-k) Q
  have htarget : Ch02.dilateCube k Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_dilateCube_neg k Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F, hk] using triadicCoeffFamily_dilateReg_aeeq_dilate ha k
  have hAEEq := Ch02.lambdaSq_eq_ofAEEq hGB Q s q
  have hdilate :=
    Ch02.lambdaSq_dilate (Ch02.TriadicCoeffFamily.isDilation_dilate k F) Qsrc s q
  calc
    Ch04.lambdaSqCoeffField Q s q (dilateReg k a) = Ch02.lambdaSq Q s q G := by
      simp [Ch04.lambdaSqCoeffField, G, hk]
    _ = Ch02.lambdaSq Q s q B := hAEEq
    _ = Ch02.lambdaSq Qsrc s q F := by
      simpa [Qsrc, htarget, B] using hdilate
    _ = Ch04.lambdaSqCoeffField Qsrc s q a := by
      simp [Ch04.lambdaSqCoeffField, F, ha]

theorem integrable_relativeNormalized_LambdaSqCoeffField_pow
    (M : ABKModel d) (m : ℤ) {s : ℝ} (hs : 0 < s) (xi : ℕ) :
    Integrable (fun a : RegCoeffField d =>
      (Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a) ^ xi)
      (relativeNormalizedCutoffLaw M m) := by
  let k : ℤ := -(m + (cutoffRelativeNormalizationShift d : ℤ))
  let hP : Ch04.RestrictionLawCarrier (relativeNormalizedCutoffLaw M m) :=
    relativeNormalizedCutoffLaw_lawCarrier M m
  have htarget_ae : AEStronglyMeasurable (fun a : RegCoeffField d =>
      (Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a) ^ xi)
      (relativeNormalizedCutoffLaw M m) :=
    ((hP.aemeasurable_LambdaSqCoeffField_finite_one
      (originCube d (0 : ℤ)) hs).pow_const xi).aestronglyMeasurable
  rw [relativeNormalizedCutoffLaw_eq_map_dilateReg] at htarget_ae ⊢
  apply (integrable_map_measure htarget_ae
    (measurable_dilateReg (d := d) k).aemeasurable).mpr
  refine (integrable_LambdaSqCoeffField_pow_cutoffLaw M m
    (Ch02.dilateCube (-k) (originCube d (0 : ℤ))) hs xi).congr ?_
  filter_upwards [(coefficientCutoffLaw_lawCarrier M m).ae_locallyUniformlyEllipticField]
    with a ha
  have hscale := LambdaSqCoeffField_dilateReg_of_aelocallyUniformlyElliptic
    ha k (originCube d (0 : ℤ)) s (.finite 1)
  simpa [k] using congrArg (fun x : ℝ => x ^ xi) hscale.symm

theorem integrable_relativeNormalized_lambdaSqCoeffField_inv_pow
    (M : ABKModel d) (m : ℤ) {s : ℝ} (hs : 0 < s) (xi : ℕ) :
    Integrable (fun a : RegCoeffField d =>
      ((Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a)⁻¹) ^ xi)
      (relativeNormalizedCutoffLaw M m) := by
  let k : ℤ := -(m + (cutoffRelativeNormalizationShift d : ℤ))
  let hP : Ch04.RestrictionLawCarrier (relativeNormalizedCutoffLaw M m) :=
    relativeNormalizedCutoffLaw_lawCarrier M m
  have htarget_ae : AEStronglyMeasurable (fun a : RegCoeffField d =>
      ((Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a)⁻¹) ^ xi)
      (relativeNormalizedCutoffLaw M m) :=
    ((hP.aemeasurable_lambdaSqCoeffField_finite_one_inv
      (originCube d (0 : ℤ)) hs).pow_const xi).aestronglyMeasurable
  rw [relativeNormalizedCutoffLaw_eq_map_dilateReg] at htarget_ae ⊢
  apply (integrable_map_measure htarget_ae
    (measurable_dilateReg (d := d) k).aemeasurable).mpr
  refine (integrable_lambdaSqCoeffField_inv_pow_cutoffLaw M m
    (Ch02.dilateCube (-k) (originCube d (0 : ℤ))) hs xi).congr ?_
  filter_upwards [(coefficientCutoffLaw_lawCarrier M m).ae_locallyUniformlyEllipticField]
    with a ha
  have hscale := lambdaSqCoeffField_dilateReg_of_aelocallyUniformlyElliptic
    ha k (originCube d (0 : ℤ)) s (.finite 1)
  simpa [k] using congrArg (fun x : ℝ => (x⁻¹) ^ xi) hscale.symm

end

noncomputable section

variable {d : ℕ}

/-- Exact evidence for the same-cutoff relative normalization. -/
noncomputable def relativeNormalizedCutoffLaw_quantitativeCoarseGrainedEllipticity
    (M : ABKModel d) (m : ℤ) :
    @Ch05.QuantitativeCoarseGrainedEllipticity d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
      (relativeNormalizedCutoffLaw M m) := by
  letI : NeZero d := ⟨Nat.ne_of_gt
    (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  refine {
    sUpper := (cutoffP4Params d M.shellPrefix.dimension).sUpper
    sLower := (cutoffP4Params d M.shellPrefix.dimension).sLower
    xi := (cutoffP4Params d M.shellPrefix.dimension).xi
    two_le_dim := (cutoffP4Params d M.shellPrefix.dimension).two_le_dim
    sUpper_nonneg := (cutoffP4Params d M.shellPrefix.dimension).sUpper_nonneg
    sUpper_lt_one := (cutoffP4Params d M.shellPrefix.dimension).sUpper_lt_one
    sLower_nonneg := (cutoffP4Params d M.shellPrefix.dimension).sLower_nonneg
    sLower_lt_one := (cutoffP4Params d M.shellPrefix.dimension).sLower_lt_one
    xi_gt_two_mul_dim := (cutoffP4Params d M.shellPrefix.dimension).xi_gt_two_mul_dim
    sum_lt_one := (cutoffP4Params d M.shellPrefix.dimension).sum_lt_one
    dim_div_xi_lt_min := (cutoffP4Params d M.shellPrefix.dimension).dim_div_xi_lt_min
    upper_moment_integrable := ?_
    lower_inv_moment_integrable := ?_ }
  · simpa only [cutoffP4Params_sUpper] using
      integrable_relativeNormalized_LambdaSqCoeffField_pow M m
        (by norm_num : (0 : ℝ) < 1 / 4)
        (cutoffP4Params d M.shellPrefix.dimension).xi
  · simpa only [cutoffP4Params_sLower] using
      integrable_relativeNormalized_lambdaSqCoeffField_inv_pow M m
        (by norm_num : (0 : ℝ) < 1 / 4)
        (cutoffP4Params d M.shellPrefix.dimension).xi

end


end Algsuperdiff.Section3.Cutoff
