/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.CertificateProjections
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderEffectiveScale
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledMixingScaleDecay

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.RowCertificateRebase

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Reading the row's certificate off the root certificate

The undelayed exact-gauge row `Root.exists_printOrderUndelayedExactGaugeRow`
consumes a printed certificate whose amplitude is **exactly**
`correctorTargetAmplitude c kappa` for a smallness `c` below its own law-free
ceiling `cMax (d, g, eta)`.  The root certificate `rootGoodScaleAt d g cStar κ`
carries its certificate at the *source* amplitude and at the *source* scale
`X a`, together with the identity

```
x = commonQuantitativeAffineScale sourceAmplitude
      (correctorTargetAmplitude cStar κ) κ Caff overlinePi κ X a.
```

Which ceiling the large-scale C¹ slope approximation route imposes on `cStar`
was not settled earlier.  **It imposes
none.**  The `PrintOrderQuantitativeNormalizedReferenceCertificate.commonAffineScale`
rebases the same certificate to *any* positive target amplitude, at the
correspondingly enlarged common scale; lowering the target from
`correctorTargetAmplitude cStar κ` to `correctorTargetAmplitude c' κ` enlarges
the scale by at most `(cStar / c') ^ κ⁻¹`, a factor fixed before the matrix and
the sample.  The terminal's **own free delay `L`** absorbs exactly that factor,
because `triadicCeilingIndex` of a bounded multiple of `x` exceeds
`triadicCeilingIndex x` by at most `triadicCeilingIndex` of the multiple.

So the large-scale C¹ slope approximation clause smallness is chosen by the *consumer*, not
reconciled against
`cStar`: no sixth ceiling enters the five-ceiling reconciliation.  That is the
structural content of this module; everything in it is scale arithmetic.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## Lowering the target amplitude costs one explicit factor -/

/-- **The common affine scale is Lipschitz in the target amplitude.**  Lowering
the target from `T` to `T'` enlarges the scale by at most `(T / T') ^ κ⁻¹`. -/
theorem commonQuantitativeAffineScale_le_of_target_le
    {amplitude T T' kappaRate Caff overlinePi kappaCube : ℝ}
    {X : CoeffSpace d → ℝ} {a : CoeffSpace d}
    (hkappa : 0 < kappaRate) (hT' : 0 < T') (hT'T : T' ≤ T)
    (hX : 0 ≤ X a) :
    commonQuantitativeAffineScale amplitude T' kappaRate Caff overlinePi
        kappaCube X a ≤
      (T / T') ^ kappaRate⁻¹ *
        commonQuantitativeAffineScale amplitude T kappaRate Caff overlinePi
          kappaCube X a := by
  have hT : 0 < T := lt_of_lt_of_le hT' hT'T
  have hratio : (1 : ℝ) ≤ T / T' := (one_le_div hT').2 hT'T
  have hratio0 : (0 : ℝ) ≤ T / T' := le_trans zero_le_one hratio
  have hmaxT : (1 : ℝ) ≤ max 1 (amplitude / T) := le_max_left _ _
  have hmaxT0 : (0 : ℝ) ≤ max 1 (amplitude / T) := le_trans zero_le_one hmaxT
  have hmaxT'0 : (0 : ℝ) ≤ max 1 (amplitude / T') := le_trans zero_le_one (le_max_left _ _)
  have hkinv : (0 : ℝ) ≤ kappaRate⁻¹ := inv_nonneg.2 hkappa.le
  have hkey : max 1 (amplitude / T') ≤ (T / T') * max 1 (amplitude / T) := by
    refine max_le ?_ ?_
    · have h := mul_le_mul hratio hmaxT zero_le_one hratio0
      simpa only [one_mul] using h
    · have heq : amplitude / T' = (T / T') * (amplitude / T) := by
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) hratio0
  have hrpow : (max 1 (amplitude / T')) ^ kappaRate⁻¹ ≤
      (T / T') ^ kappaRate⁻¹ * (max 1 (amplitude / T)) ^ kappaRate⁻¹ := by
    have hstep : (max 1 (amplitude / T')) ^ kappaRate⁻¹ ≤
        ((T / T') * max 1 (amplitude / T)) ^ kappaRate⁻¹ :=
      Real.rpow_le_rpow hmaxT'0 hkey hkinv
    rwa [Real.mul_rpow hratio0 hmaxT0] at hstep
  have hmult : (0 : ℝ) ≤ roundedAffineMultiplier Caff overlinePi kappaCube :=
    le_trans zero_le_one (one_le_roundedAffineMultiplier Caff overlinePi kappaCube)
  simp only [commonQuantitativeAffineScale, roundedAffineEffectiveScale,
    targetedQuantitativeEffectiveScale, powerLossRandomScale,
    powerLossEffectiveScale, amplitudeReductionFactor]
  calc roundedAffineMultiplier Caff overlinePi kappaCube *
        ((max 1 (amplitude / T')) ^ kappaRate⁻¹ * X a)
      ≤ roundedAffineMultiplier Caff overlinePi kappaCube *
          (((T / T') ^ kappaRate⁻¹ * (max 1 (amplitude / T)) ^ kappaRate⁻¹) *
            X a) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hrpow hX) hmult
    _ = (T / T') ^ kappaRate⁻¹ *
        (roundedAffineMultiplier Caff overlinePi kappaCube *
          ((max 1 (amplitude / T)) ^ kappaRate⁻¹ * X a)) := by ring

/-- The target amplitude is monotone in the corrector smallness. -/
theorem correctorTargetAmplitude_le_of_le {c c' kappa : ℝ}
    (hkappa : 0 < kappa) (hcc : c' ≤ c) :
    correctorTargetAmplitude c' kappa ≤ correctorTargetAmplitude c kappa := by
  have hpow : (3 : ℝ) ^ (-kappa) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hkappa)
  have hfac : (0 : ℝ) ≤ 1 - (3 : ℝ) ^ (-kappa) := by linarith only [hpow]
  unfold correctorTargetAmplitude
  exact mul_le_mul_of_nonneg_right (by linarith only [hcc]) hfac

/-- The ratio of two target amplitudes is the ratio of the smallnesses. -/
theorem correctorTargetAmplitude_div_eq {c c' kappa : ℝ}
    (hkappa : 0 < kappa) (hc' : 0 < c') :
    correctorTargetAmplitude c kappa / correctorTargetAmplitude c' kappa =
      c / c' := by
  have hpow : (3 : ℝ) ^ (-kappa) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hkappa)
  have hfac : (0 : ℝ) < 1 - (3 : ℝ) ^ (-kappa) := by linarith only [hpow]
  unfold correctorTargetAmplitude
  field_simp

/-! ## The row's certificate -/

/-- **The row's certificate, read off the root certificate at the consumer's
own smallness.**  No ceiling is imposed on `cStar`: the scale paid is the
explicit factor `(cStar / c') ^ κ⁻¹`, which depends on `(cStar, c', κ)` alone
and therefore may be absorbed by the large-scale C¹ slope approximation terminal's free delay. -/
theorem exists_rowCertificate_of_rootGoodScaleAt (d : ℕ) [NeZero d]
    {g cStarg c' kappa : ℝ} (hkappa : 0 < kappa)
    (hc' : 0 < c') (hc'le : c' ≤ cStarg)
    {abar : Mat d} {a : CoeffSpace d} {x : ℝ}
    (h : rootGoodScaleAt d g cStarg kappa abar a x) :
    ∃ xRow : ℝ, 1 ≤ xRow ∧ xRow ≤ (cStarg / c') ^ kappa⁻¹ * x ∧
      PrintOrderQuantitativeNormalizedReferenceCertificate abar g
        (correctorTargetAmplitude c' kappa) kappa xRow a := by
  obtain ⟨sourceAmplitude, X, hCert, hxEq⟩ :=
    printOrderGoodScale_of_rootGoodScaleAt h
  have hT' : 0 < correctorTargetAmplitude c' kappa :=
    correctorTargetAmplitude_pos hc' hkappa
  have hTT' : correctorTargetAmplitude c' kappa ≤
      correctorTargetAmplitude cStarg kappa :=
    correctorTargetAmplitude_le_of_le hkappa hc'le
  have hXone : 1 ≤ X a := by
    obtain ⟨-, -, -, -, -, -, hXone, -, -⟩ := hCert
    exact hXone
  have hnew := hCert.commonAffineScale
    (target := correctorTargetAmplitude c' kappa)
    (Caff := Transport.roundedOuterResponseAffineConstant d)
    (overlinePi := specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
    (kappaCube := kappa) hT'
  refine ⟨commonQuantitativeAffineScale sourceAmplitude
      (correctorTargetAmplitude c' kappa) kappa
      (Transport.roundedOuterResponseAffineConstant d)
      (specBound (symmPart abar) * specBound (symmPart abar)⁻¹) kappa X a,
    ?_, ?_, hnew⟩
  · obtain ⟨-, -, -, -, -, -, hone, -, -⟩ := hnew
    exact hone
  · have hbound := commonQuantitativeAffineScale_le_of_target_le
      (amplitude := sourceAmplitude)
      (T := correctorTargetAmplitude cStarg kappa)
      (T' := correctorTargetAmplitude c' kappa)
      (Caff := Transport.roundedOuterResponseAffineConstant d)
      (overlinePi := specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
      (kappaCube := kappa) (X := X) (a := a) hkappa hT' hTT'
      (le_trans zero_le_one hXone)
    rw [hxEq]
    rwa [correctorTargetAmplitude_div_eq hkappa hc'] at hbound

/-! ## The delay that absorbs the rebasing factor -/

end

end CorrectorComposition
end HighContrast
end HCPolySupport
