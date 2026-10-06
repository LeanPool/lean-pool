/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootInterface.CertificateMonotone

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.RootInterface.CommonScaleFactorBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The common affine scale is a law-free multiple of the fold factor

`PrintOrderRateBearingCommonAffineGoodScale d g c κ abar a x` forces

```
x = commonQuantitativeAffineScale sourceAmplitude target κ Caff overlinePi κ X a
```

which is `M · X a` for the multiplier

```
M = roundedAffineMultiplier Caff overlinePi κ *
      (amplitudeReductionFactor sourceAmplitude target) ^ κ⁻¹.
```

The certificate therefore does **not** live at the raw quenched scale `X a`; it
lives at `M · X a` and above.  This module bounds `M` by a law-free amplitude
times a power of the homogenized witness eccentricity, which is the shape the
root's polynomial-length clause can pay for.

Both of `M`'s factors carry the eccentricity: the affine multiplier through
`overlinePi = specBound (symmPart abar) * specBound (symmPart abar)⁻¹`, whose
square root **is** the witness eccentricity, and the amplitude reduction through
the enclosure generation `G`, which is bracketed by `1 + 3 · ecc · √d`.
-/

namespace HCPolySupport
namespace HighContrast
namespace RootInterface

open MeasureTheory
open RowSupply (eccentricityFoldFactor one_le_eccentricityFoldFactor
  witnessEccentricity_nonneg)

noncomputable section

variable {d : ℕ}

/-! ## The multiplier, named -/

/-- The multiplier inserted between the raw quenched scale and the common
affine scale that the rate-bearing certificate is read at. -/
@[expose]
def commonAffineMultiplier (d : ℕ) (amplitude target kappaRate : ℝ)
    (abar : Mat d) : ℝ :=
  roundedAffineMultiplier (Transport.roundedOuterResponseAffineConstant d)
      (specBound (symmPart abar) * specBound (symmPart abar)⁻¹) kappaRate *
    (amplitudeReductionFactor amplitude target) ^ kappaRate⁻¹

theorem one_le_commonAffineMultiplier (d : ℕ) {amplitude target kappaRate : ℝ}
    (hkappa : 0 < kappaRate) (abar : Mat d) :
    1 ≤ commonAffineMultiplier d amplitude target kappaRate abar := by
  refine one_le_mul_of_one_le_of_one_le
    (one_le_roundedAffineMultiplier _ _ _) ?_
  exact Real.one_le_rpow (one_le_amplitudeReductionFactor amplitude target)
    (inv_nonneg.mpr hkappa.le)

theorem commonAffineMultiplier_pos (d : ℕ) {amplitude target kappaRate : ℝ}
    (hkappa : 0 < kappaRate) (abar : Mat d) :
    0 < commonAffineMultiplier d amplitude target kappaRate abar :=
  lt_of_lt_of_le zero_lt_one (one_le_commonAffineMultiplier d hkappa abar)

/-- The common affine scale is exactly the multiplier times the raw scale. -/
theorem commonQuantitativeAffineScale_eq_multiplier_mul (d : ℕ)
    (amplitude target kappaRate : ℝ) (abar : Mat d)
    (X : CoeffSpace d → ℝ) (a : CoeffSpace d) :
    commonQuantitativeAffineScale amplitude target kappaRate
        (Transport.roundedOuterResponseAffineConstant d)
        (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
        kappaRate X a =
      commonAffineMultiplier d amplitude target kappaRate abar * X a := by
  unfold commonQuantitativeAffineScale commonAffineMultiplier
    roundedAffineEffectiveScale targetedQuantitativeEffectiveScale
    powerLossRandomScale powerLossEffectiveScale
  ring

/-! ## The affine leg -/

/-- The affine multiplier's own amplitude is the witness eccentricity. -/
theorem sqrt_overlinePi_eq_witnessEccentricity (abar : Mat d) :
    Real.sqrt (specBound (symmPart abar) * specBound (symmPart abar)⁻¹) =
      witnessEccentricity (symmPart abar) := rfl

theorem roundedAffineMultiplier_le_fold (d : ℕ) {kappaRate : ℝ}
    (hkappa : 0 < kappaRate) (abar : Mat d) :
    roundedAffineMultiplier (Transport.roundedOuterResponseAffineConstant d)
        (specBound (symmPart abar) * specBound (symmPart abar)⁻¹) kappaRate ≤
      max 1 (Transport.roundedOuterResponseAffineConstant d ^ kappaRate⁻¹) *
        eccentricityFoldFactor abar kappaRate⁻¹ := by
  have ht : (0 : ℝ) ≤ kappaRate⁻¹ := inv_nonneg.mpr hkappa.le
  have hCaff : (0 : ℝ) ≤ Transport.roundedOuterResponseAffineConstant d :=
    (Transport.roundedOuterResponseAffineConstant_pos d).le
  have hbase :
      roundedAffineLossAmplitude (Transport.roundedOuterResponseAffineConstant d)
          (specBound (symmPart abar) * specBound (symmPart abar)⁻¹) =
        Transport.roundedOuterResponseAffineConstant d *
          witnessEccentricity (symmPart abar) ^ (1 : ℝ) := by
    unfold roundedAffineLossAmplitude
    rw [sqrt_overlinePi_eq_witnessEccentricity, Real.rpow_one]
  unfold roundedAffineMultiplier
  rw [hbase, ← max_one_rpow
      (mul_nonneg hCaff (Real.rpow_nonneg (witnessEccentricity_nonneg _) _)) ht]
  have := max_one_mul_rpow_le_fold (abar := abar)
    (A := Transport.roundedOuterResponseAffineConstant d) (t := kappaRate⁻¹)
    (p := (1 : ℝ)) hCaff ht zero_le_one
  simpa only [one_mul] using this

/-! ## The amplitude leg -/

/-- The law-free half of the retained source amplitude. -/
@[expose]
def certAmplitudeBase (d : ℕ) (s rho : ℝ) : ℝ :=
  Real.sqrt (6 * (d : ℝ) * Real.sqrt d *
    ((1 + 3 * Real.sqrt d) * (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho))))))

theorem certAmplitudeBase_nonneg (d : ℕ) (s rho : ℝ) :
    0 ≤ certAmplitudeBase d s rho := Real.sqrt_nonneg _

private theorem sqrt_le_self_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    Real.sqrt u ≤ u := by
  have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu
  have hsq : u ≤ u * u := le_mul_of_one_le_left hu0 hu
  calc Real.sqrt u ≤ Real.sqrt (u * u) := Real.sqrt_le_sqrt hsq
    _ = u := Real.sqrt_mul_self hu0

/-- **The retained source amplitude is a law-free constant times one power of
the eccentricity fold factor.** -/
theorem normalizedReferencePowerAmplitude_le_fold {abar : Mat d}
    {s rho delta : ℝ} {G : ℕ}
    (_hrho : 0 < rho) (hrho1 : rho ≤ 1) (hgap : rho < 2 * s)
    (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1)
    (hG : (3 : ℝ) ^ (G : ℤ) ≤
      1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d)) :
    normalizedReferencePowerAmplitude d s rho delta G ≤
      certAmplitudeBase d s rho * eccentricityFoldFactor abar 1 := by
  have hecc : 0 ≤ witnessEccentricity (symmPart abar) :=
    witnessEccentricity_nonneg _
  have hd0 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  set E : ℝ := eccentricityFoldFactor abar 1 with hEdef
  have hE1 : (1 : ℝ) ≤ E := one_le_eccentricityFoldFactor abar 1
  have hE0 : (0 : ℝ) ≤ E := le_trans zero_le_one hE1
  have heccE : witnessEccentricity (symmPart abar) ≤ E := by
    rw [hEdef]
    simpa only [Real.rpow_one] using
      RowSupply.rpow_le_eccentricityFoldFactor abar 1
  -- the geometric gap is positive
  have hgapPos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(2 * s - rho)) := by
    have : (3 : ℝ) ^ (-(2 * s - rho)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (neg_neg_of_pos (by linarith only [hgap]))
    linarith only [this]
  have hinvPos : (0 : ℝ) < 1 / (1 - (3 : ℝ) ^ (-(2 * s - rho))) := by positivity
  -- the enclosure bracket, in fold form
  have hbracket : (3 : ℝ) ^ (G : ℤ) ≤ (1 + 3 * Real.sqrt d) * E := by
    have h2 : witnessEccentricity (symmPart abar) * Real.sqrt d ≤ E * Real.sqrt d :=
      mul_le_mul_of_nonneg_right heccE hd0
    have hstep : 1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d) ≤
        (1 + 3 * Real.sqrt d) * E := by
      have hexpand : (1 + 3 * Real.sqrt d) * E = E + 3 * (E * Real.sqrt d) := by
        ring
      rw [hexpand]
      linarith only [hE1, h2]
    exact hG.trans hstep
  -- the generation power
  have hGpow : (3 : ℝ) ^ (rho * (G : ℝ)) ≤ (1 + 3 * Real.sqrt d) * E := by
    have hGnonneg : (0 : ℝ) ≤ (3 : ℝ) ^ (G : ℤ) := by positivity
    have hbase1 : (1 : ℝ) ≤ (3 : ℝ) ^ (G : ℤ) :=
      one_le_zpow₀ (by norm_num) (Int.natCast_nonneg G)
    have hrewrite : (3 : ℝ) ^ (rho * (G : ℝ)) =
        ((3 : ℝ) ^ (G : ℤ)) ^ rho := by
      rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      rw [show ((G : ℝ)) = ((G : ℤ) : ℝ) by push_cast; ring,
        Real.rpow_intCast]
    rw [hrewrite]
    calc ((3 : ℝ) ^ (G : ℤ)) ^ rho ≤ ((3 : ℝ) ^ (G : ℤ)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase1 hrho1
      _ = (3 : ℝ) ^ (G : ℤ) := Real.rpow_one _
      _ ≤ (1 + 3 * Real.sqrt d) * E := hbracket
  -- the prefactor
  have hpre : normalizedReferencePowerPrefactor d s rho G ≤
      (6 * (d : ℝ) * Real.sqrt d *
        ((1 + 3 * Real.sqrt d) * (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho)))))) * E := by
    unfold normalizedReferencePowerPrefactor
    have hcoef : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d := by positivity
    have hstep : (3 : ℝ) ^ (rho * (G : ℝ)) *
          (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho)))) ≤
        ((1 + 3 * Real.sqrt d) * E) *
          (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho)))) :=
      mul_le_mul_of_nonneg_right hGpow hinvPos.le
    calc 6 * (d : ℝ) * Real.sqrt d *
            ((3 : ℝ) ^ (rho * (G : ℝ)) *
              (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho))))) ≤
          6 * (d : ℝ) * Real.sqrt d *
            (((1 + 3 * Real.sqrt d) * E) *
              (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho))))) :=
        mul_le_mul_of_nonneg_left hstep hcoef
      _ = (6 * (d : ℝ) * Real.sqrt d *
            ((1 + 3 * Real.sqrt d) *
              (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho)))))) * E := by ring
  -- take square roots and drop the delta half
  have hbase0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d *
      ((1 + 3 * Real.sqrt d) * (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho))))) := by
    positivity
  have hsqrtPre :
      Real.sqrt (normalizedReferencePowerPrefactor d s rho G) ≤
        certAmplitudeBase d s rho * E := by
    calc Real.sqrt (normalizedReferencePowerPrefactor d s rho G) ≤
          Real.sqrt ((6 * (d : ℝ) * Real.sqrt d *
            ((1 + 3 * Real.sqrt d) *
              (1 / (1 - (3 : ℝ) ^ (-(2 * s - rho)))))) * E) :=
        Real.sqrt_le_sqrt hpre
      _ = certAmplitudeBase d s rho * Real.sqrt E := by
        rw [Real.sqrt_mul hbase0]
        rfl
      _ ≤ certAmplitudeBase d s rho * E :=
        mul_le_mul_of_nonneg_left (sqrt_le_self_of_one_le hE1)
          (certAmplitudeBase_nonneg d s rho)
  have hsqrtDelta : Real.sqrt delta ≤ 1 := by
    have : Real.sqrt delta ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hdelta.2.le
    simpa only [Real.sqrt_one] using this
  unfold normalizedReferencePowerAmplitude
  calc Real.sqrt (normalizedReferencePowerPrefactor d s rho G) *
        Real.sqrt delta ≤
      Real.sqrt (normalizedReferencePowerPrefactor d s rho G) * 1 :=
        mul_le_mul_of_nonneg_left hsqrtDelta (Real.sqrt_nonneg _)
    _ = Real.sqrt (normalizedReferencePowerPrefactor d s rho G) := mul_one _
    _ ≤ certAmplitudeBase d s rho * E := hsqrtPre

/-- The amplitude leg of the multiplier, in fold form. -/
theorem amplitudeReductionFactor_rpow_le_fold {abar : Mat d}
    {amplitude target Amp kappaRate : ℝ}
    (hkappa : 0 < kappaRate) (hAmp : 0 ≤ Amp) (htarget : 0 < target)
    (hamp : amplitude ≤ Amp * eccentricityFoldFactor abar 1) :
    (amplitudeReductionFactor amplitude target) ^ kappaRate⁻¹ ≤
      (max 1 (Amp / target)) ^ kappaRate⁻¹ *
        eccentricityFoldFactor abar kappaRate⁻¹ := by
  have ht : (0 : ℝ) ≤ kappaRate⁻¹ := inv_nonneg.mpr hkappa.le
  have hE1 : (1 : ℝ) ≤ eccentricityFoldFactor abar 1 :=
    one_le_eccentricityFoldFactor abar 1
  have hE0 : (0 : ℝ) ≤ eccentricityFoldFactor abar 1 := le_trans zero_le_one hE1
  have hratio : amplitude / target ≤ (Amp / target) * eccentricityFoldFactor abar 1 := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right htarget]
    exact hamp
  have hstep : amplitudeReductionFactor amplitude target ≤
      max 1 (Amp / target) * eccentricityFoldFactor abar 1 := by
    unfold amplitudeReductionFactor
    refine (max_le_max (le_refl (1 : ℝ)) hratio).trans ?_
    refine (max_one_mul_le (div_nonneg (le_trans (by positivity) (le_refl _))
      htarget.le) hE0).trans ?_
    exact mul_le_mul_of_nonneg_left (le_of_eq (max_eq_right hE1))
      (le_trans zero_le_one (le_max_left _ _))
  have hpos : (0 : ℝ) ≤ amplitudeReductionFactor amplitude target :=
    le_trans zero_le_one (one_le_amplitudeReductionFactor amplitude target)
  have hmono := Real.rpow_le_rpow hpos hstep ht
  refine hmono.trans (le_of_eq ?_)
  rw [Real.mul_rpow (le_trans zero_le_one (le_max_left (1 : ℝ) (Amp / target)))
    hE0]
  congr 1
  rw [show eccentricityFoldFactor abar 1 =
      max 1 (witnessEccentricity (symmPart abar)) by
    unfold RowSupply.eccentricityFoldFactor
    rw [Real.rpow_one]]
  rw [max_one_rpow (witnessEccentricity_nonneg _) ht]
  rfl

/-! ## The full multiplier bound -/

/-- The law-free amplitude of the certificate's own length factor. -/
@[expose]
def rootCertAmplitude (d : ℕ) (s rho target kappaRate : ℝ) : ℝ :=
  max 1 (Transport.roundedOuterResponseAffineConstant d ^ kappaRate⁻¹) *
    (max 1 (certAmplitudeBase d s rho / target)) ^ kappaRate⁻¹

theorem one_le_rootCertAmplitude (d : ℕ) {s rho target kappaRate : ℝ}
    (hkappa : 0 < kappaRate) :
    1 ≤ rootCertAmplitude d s rho target kappaRate := by
  refine one_le_mul_of_one_le_of_one_le (le_max_left _ _) ?_
  exact Real.one_le_rpow (le_max_left _ _) (inv_nonneg.mpr hkappa.le)

/-- **The certificate's scale multiplier is a law-free amplitude times two
powers of the eccentricity fold factor.** -/
theorem commonAffineMultiplier_le_fold {abar : Mat d}
    {s rho delta target kappaRate : ℝ} {G : ℕ}
    (hkappa : 0 < kappaRate) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hgap : rho < 2 * s) (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1)
    (htarget : 0 < target)
    (hG : (3 : ℝ) ^ (G : ℤ) ≤
      1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d)) :
    commonAffineMultiplier d
        (normalizedReferencePowerAmplitude d s rho delta G) target
        kappaRate abar ≤
      rootCertAmplitude d s rho target kappaRate *
        eccentricityFoldFactor abar (2 * kappaRate⁻¹) := by
  have ht : (0 : ℝ) ≤ kappaRate⁻¹ := inv_nonneg.mpr hkappa.le
  have haffine := roundedAffineMultiplier_le_fold d hkappa abar
  have hamp := amplitudeReductionFactor_rpow_le_fold (abar := abar)
    (amplitude := normalizedReferencePowerAmplitude d s rho delta G)
    (target := target) (Amp := certAmplitudeBase d s rho) hkappa
    (certAmplitudeBase_nonneg d s rho) htarget
    (normalizedReferencePowerAmplitude_le_fold hrho hrho1 hgap hdelta hG)
  have haffine0 : (0 : ℝ) ≤
      roundedAffineMultiplier (Transport.roundedOuterResponseAffineConstant d)
        (specBound (symmPart abar) * specBound (symmPart abar)⁻¹) kappaRate :=
    (roundedAffineMultiplier_pos _ _ _).le
  have hamp0 : (0 : ℝ) ≤
      (amplitudeReductionFactor
        (normalizedReferencePowerAmplitude d s rho delta G) target) ^ kappaRate⁻¹ :=
    Real.rpow_nonneg
      (le_trans zero_le_one (one_le_amplitudeReductionFactor _ _)) _
  have hbig0 : (0 : ℝ) ≤
      max 1 (Transport.roundedOuterResponseAffineConstant d ^ kappaRate⁻¹) *
        eccentricityFoldFactor abar kappaRate⁻¹ :=
    le_trans zero_le_one
      (one_le_mul_of_one_le_of_one_le (le_max_left _ _)
        (one_le_eccentricityFoldFactor abar kappaRate⁻¹))
  have hfold := eccentricityFoldFactor_mul_le abar ht ht
  have hkey :
      commonAffineMultiplier d
          (normalizedReferencePowerAmplitude d s rho delta G) target
          kappaRate abar ≤
        (max 1 (Transport.roundedOuterResponseAffineConstant d ^ kappaRate⁻¹) *
            eccentricityFoldFactor abar kappaRate⁻¹) *
          ((max 1 (certAmplitudeBase d s rho / target)) ^ kappaRate⁻¹ *
            eccentricityFoldFactor abar kappaRate⁻¹) := by
    unfold commonAffineMultiplier
    exact mul_le_mul haffine hamp hamp0 hbig0
  refine hkey.trans ?_
  have hrewrite :
      (max 1 (Transport.roundedOuterResponseAffineConstant d ^ kappaRate⁻¹) *
          eccentricityFoldFactor abar kappaRate⁻¹) *
        ((max 1 (certAmplitudeBase d s rho / target)) ^ kappaRate⁻¹ *
          eccentricityFoldFactor abar kappaRate⁻¹) =
      rootCertAmplitude d s rho target kappaRate *
        (eccentricityFoldFactor abar kappaRate⁻¹ *
          eccentricityFoldFactor abar kappaRate⁻¹) := by
    unfold rootCertAmplitude
    ring
  rw [hrewrite]
  refine mul_le_mul_of_nonneg_left ?_
    (le_trans zero_le_one (one_le_rootCertAmplitude d hkappa))
  refine hfold.trans (le_of_eq ?_)
  congr 1
  ring

end

end RootInterface
end HighContrast
end HCPolySupport
