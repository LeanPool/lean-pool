/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4UpperLaw
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.RangeNormalization

/-!
# NormalizedP4

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Exact normalized `(P4)` for the genuine cutoff

The normalized cutoff law is evaluated only at the canonical least depth
`cutoffNormalizationDepth`.  Its two moments are transported from arbitrary
original origin-cube scales through CoarseGraining's exact dilation law.
-/

namespace Algsuperdiff.Section3.Cutoff

open Filter MeasureTheory Set
open HCPolySupport HCPolySupport.Book

section

variable {d : ℕ} [NeZero d]

theorem integrable_scaleNormalized_LambdaSqCoeffField_pow
    (M : ABKModel d) (m : ℤ) (k : ℕ) {s : ℝ} (hs : 0 < s) (xi : ℕ) :
    Integrable (fun a : RegCoeffField d =>
      (Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a) ^ xi)
      (Ch04.restrictionScaleNormalizedLaw k (coefficientCutoffLaw M m)) := by
  let P := coefficientCutoffLaw M m
  let hP : Ch04.RestrictionLawCarrier P := coefficientCutoffLaw_lawCarrier M m
  let hnorm : Ch04.RestrictionLawCarrier
      (Ch04.restrictionScaleNormalizedLaw k P) := hP.scaleNormalized k
  have htarget_ae : AEStronglyMeasurable (fun a : RegCoeffField d =>
      (Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a) ^ xi)
      (Ch04.restrictionScaleNormalizedLaw k P) :=
    ((hnorm.aemeasurable_LambdaSqCoeffField_finite_one
      (originCube d (0 : ℤ)) hs).pow_const xi).aestronglyMeasurable
  apply (Ch04.integrable_restrictionScaleNormalizedLaw_iff k htarget_ae).mpr
  rw [← Ch04.rescaleReg_eq_dilateReg_neg_nat k]
  refine (integrable_LambdaSqCoeffField_pow_cutoffLaw M m
    (originCube d (k : ℤ)) hs xi).congr ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  have hscale :=
    Ch04.LambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k 0 s (.finite 1)
  simpa only [Nat.add_zero] using! congrArg (fun x : ℝ => x ^ xi) hscale.symm

theorem integrable_scaleNormalized_lambdaSqCoeffField_inv_pow
    (M : ABKModel d) (m : ℤ) (k : ℕ) {s : ℝ} (hs : 0 < s) (xi : ℕ) :
    Integrable (fun a : RegCoeffField d =>
      ((Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a)⁻¹) ^ xi)
      (Ch04.restrictionScaleNormalizedLaw k (coefficientCutoffLaw M m)) := by
  let P := coefficientCutoffLaw M m
  let hP : Ch04.RestrictionLawCarrier P := coefficientCutoffLaw_lawCarrier M m
  let hnorm : Ch04.RestrictionLawCarrier
      (Ch04.restrictionScaleNormalizedLaw k P) := hP.scaleNormalized k
  have htarget_ae : AEStronglyMeasurable (fun a : RegCoeffField d =>
      ((Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) s (.finite 1) a)⁻¹) ^ xi)
      (Ch04.restrictionScaleNormalizedLaw k P) :=
    ((hnorm.aemeasurable_lambdaSqCoeffField_finite_one_inv
      (originCube d (0 : ℤ)) hs).pow_const xi).aestronglyMeasurable
  apply (Ch04.integrable_restrictionScaleNormalizedLaw_iff k htarget_ae).mpr
  rw [← Ch04.rescaleReg_eq_dilateReg_neg_nat k]
  refine (integrable_lambdaSqCoeffField_inv_pow_cutoffLaw M m
    (originCube d (k : ℤ)) hs xi).congr ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  have hscale :=
    Ch04.lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k 0 s (.finite 1)
  simpa only [Nat.add_zero] using!
    congrArg (fun x : ℝ => (x⁻¹) ^ xi) hscale.symm

end

section

variable {d : ℕ}

/-- Exact `(P4)` evidence for the canonical range-normalized genuine cutoff law.
`QuantitativeCoarseGrainedEllipticity` is a `Type`-valued CoarseGraining
evidence record, so this must be a definition rather than a proposition-valued
theorem.  No unnormalized `(P4)` or structural law is assumed. -/
noncomputable def cutoffNormalizationQuantitativeCoarseGrainedEllipticity
    (M : ABKModel d) (m : ℤ) :
    @Ch05.QuantitativeCoarseGrainedEllipticity d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
      (Ch04.restrictionScaleNormalizedLaw (cutoffNormalizationDepth d m)
        (coefficientCutoffLaw M m)) := by
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
      integrable_scaleNormalized_LambdaSqCoeffField_pow M m
        (cutoffNormalizationDepth d m) (by norm_num : (0 : ℝ) < 1 / 4)
        (cutoffP4Params d M.shellPrefix.dimension).xi
  · simpa only [cutoffP4Params_sLower] using
      integrable_scaleNormalized_lambdaSqCoeffField_inv_pow M m
        (cutoffNormalizationDepth d m) (by norm_num : (0 : ℝ) < 1 / 4)
        (cutoffP4Params d M.shellPrefix.dimension).xi

end

end Algsuperdiff.Section3.Cutoff
