/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootInterface.CommonScaleFactorBound

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RootInterface.SmallnessMonotone

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The rate-bearing certificate is increasing in the corrector smallness

`PrintOrderRateBearingCommonAffineGoodScale d g c κ abar a x` pins its scale by

```
x = commonQuantitativeAffineScale sourceAmplitude (correctorTargetAmplitude c κ)
      κ Caff overlinePi κ X a  =  M(c) · X a
```

and `M(c)` is **decreasing** in `c`, because the corrector target amplitude
`(c/2) · (1 - 3^(-κ))` is increasing in `c` and the amplitude reduction factor
`max 1 (sourceAmplitude / target)` is decreasing in the target.  Combined with
the certificate's upward closure in the scale, the predicate is therefore
**increasing in `c` at a fixed scale**: a certificate at a smaller corrector
smallness serves every larger one.

This is the fact the decay and Lipschitz adapters need: they demand the
certificate at their own chosen `c` (`canonicalCorrectorSmallness d g hg`
and `(2 * Crec)⁻¹` respectively), while the root instantiation fixes one `c` for
all five deterministic holes.
-/

namespace HCPolySupport
namespace HighContrast
namespace RootInterface

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The corrector target amplitude is increasing in the smallness parameter. -/
theorem correctorTargetAmplitude_mono {c c' kappa : ℝ} (hkappa : 0 < kappa)
    (hcc : c ≤ c') :
    correctorTargetAmplitude c kappa ≤ correctorTargetAmplitude c' kappa := by
  have hpow : (3 : ℝ) ^ (-kappa) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hkappa)
  unfold correctorTargetAmplitude
  exact mul_le_mul_of_nonneg_right (by linarith only [hcc])
    (by linarith only [hpow])

/-- **The rate-bearing certificate is increasing in the corrector smallness.** -/
theorem PrintOrderRateBearingCommonAffineGoodScale.mono_smallness [NeZero d]
    {g c c' kappaRate x : ℝ} {abar : Mat d} {a : CoeffSpace d}
    (h : PrintOrderRateBearingCommonAffineGoodScale d g c kappaRate abar a x)
    (hkappa : 0 < kappaRate) (hc : 0 < c) (hcc : c ≤ c') :
    PrintOrderRateBearingCommonAffineGoodScale d g c' kappaRate abar a x := by
  obtain ⟨sA, X, hcert, hx⟩ := h
  have hsA : 0 ≤ sA := by
    obtain ⟨-, -, -, -, hamp, -⟩ := hcert
    exact hamp
  have hXone : 1 ≤ X a := by
    obtain ⟨-, -, -, -, -, -, hx1, -⟩ := hcert
    exact hx1
  set t : ℝ := correctorTargetAmplitude c kappaRate with htdef
  set t' : ℝ := correctorTargetAmplitude c' kappaRate with ht'def
  have ht : 0 < t := correctorTargetAmplitude_pos hc hkappa
  have htt : t ≤ t' := correctorTargetAmplitude_mono hkappa hcc
  have ht' : 0 < t' := lt_of_lt_of_le ht htt
  set M : ℝ := commonAffineMultiplier d sA t kappaRate abar with hMdef
  set M' : ℝ := commonAffineMultiplier d sA t' kappaRate abar with hM'def
  have hM0 : 0 < M := commonAffineMultiplier_pos d hkappa abar
  have hM'0 : 0 < M' := commonAffineMultiplier_pos d hkappa abar
  have hMM : M' ≤ M := by
    have hdiv : sA / t' ≤ sA / t := div_le_div_of_nonneg_left hsA ht htt
    have hred : amplitudeReductionFactor sA t' ≤ amplitudeReductionFactor sA t := by
      unfold amplitudeReductionFactor
      exact max_le_max (le_refl (1 : ℝ)) hdiv
    have hrpow : (amplitudeReductionFactor sA t') ^ kappaRate⁻¹ ≤
        (amplitudeReductionFactor sA t) ^ kappaRate⁻¹ :=
      Real.rpow_le_rpow
        (le_trans zero_le_one (one_le_amplitudeReductionFactor sA t')) hred
        (inv_nonneg.mpr hkappa.le)
    rw [hMdef, hM'def]
    unfold commonAffineMultiplier
    exact mul_le_mul_of_nonneg_left hrpow
      (roundedAffineMultiplier_pos _ _ _).le
  -- the scale, re-expressed at the larger smallness
  have hxM : x = M * X a := by
    rw [hx, hMdef, commonQuantitativeAffineScale_eq_multiplier_mul]
  have hxpos : 0 < x := by
    rw [hxM]
    exact mul_pos hM0 (lt_of_lt_of_le zero_lt_one hXone)
  have hy : X a ≤ x / M' := by
    rw [le_div_iff₀ hM'0, hxM, mul_comm M (X a)]
    exact mul_le_mul_of_nonneg_left hMM (le_trans zero_le_one hXone)
  refine ⟨sA, fun _ => x / M', ?_, ?_⟩
  · exact PrintOrderQuantitativeNormalizedReferenceCertificate.mono hcert
      hkappa (le_refl kappaRate) hy
  · rw [commonQuantitativeAffineScale_eq_multiplier_mul, ← hM'def]
    field_simp

end

end RootInterface
end HighContrast
end HCPolySupport
