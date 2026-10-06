/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.TargetedGaugeSpine
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.AffineRateAbsorption
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.GaugeRepresentativeJoin
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusGrowth

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.GaugeFrameTerminalAtCertificate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The corrector-decay terminal at an arbitrary certificate

The corrector-decay terminal is stated here with the certificate as a parameter.
A version whose corrector-family premise and good-scale premise are both fixed at
`PrintOrderRateBearingCommonAffineGoodScale` would force the corrector family's
corrector-family hypothesis to be supplied at the print certificate, a per-sample predicate carrying
no translation-invariant block-row event, which the event-carrying certificate of
the root cannot discharge.

The proof uses the corrector-family hypothesis in exactly one place, `hfamily.normalizedJoint a x
hGood`, at the sample the theorem is applied to.  The corrector-family hypothesis is therefore taken
at an arbitrary `GoodScale`, together with the projection
`GoodScale abar a x → PrintOrderRateBearing… abar a x` that every consumer has.
Taking `GoodScale := PrintOrderRateBearing…` and `hproj := fun _ _ h ↦ h` recovers
the statement at the print certificate.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set
open scoped ENNReal

noncomputable section

private theorem affine_scaled_pair_le_physical_rate
    {d : ℕ} [NeZero d] (abar : Mat d) (hSRaw : (symmPart abar).PosDef)
    {kappa xRate r x : ℝ} {m : ℤ}
    (hKappa : 0 < kappa) (hxRate : 0 < xRate) (hr : 0 < r)
    (hrm : r ≤ (3 : ℝ) ^ m) (B : ℝ) (hB : 0 < B)
    (Cjoint : ℝ≥0∞) (hCjointTop : Cjoint < ⊤) (e : Vec d)
    (hxCommonEq : x = roundedAffineMultiplier
      (Transport.roundedOuterResponseAffineConstant d)
      (specBound (symmPart abar) * specBound (symmPart abar)⁻¹) kappa * xRate) :
    ENNReal.ofReal
        (Real.sqrt (h1AffineFactor (Selection.normalizedRoot (symmPart abar))) * B) *
      (Cjoint * ENNReal.ofReal
        (((((3 : ℝ) ^ m) / xRate) ^ (-kappa)) *
          euclideanNorm (matVecMul (matSqrt (symmPart abar)) e))) ≤
      ENNReal.ofReal
        (((Real.sqrt d / Transport.roundedOuterResponseAffineConstant d) * B *
          Cjoint.toReal) * Real.sqrt (vecDot e (matVecMul (symmPart abar) e)) *
          (r / x) ^ (-kappa)) := by
  let S : Mat d := symmPart abar
  let Caff : ℝ := Transport.roundedOuterResponseAffineConstant d
  let overlinePi : ℝ := specBound S * specBound S⁻¹
  let mult : ℝ := roundedAffineMultiplier Caff overlinePi kappa
  let C : ℝ := (Real.sqrt d / Caff) * B * Cjoint.toReal
  have hrateAffine := affineRate_absorption hSRaw hKappa hxRate hr hrm
  have hrateFull :
      (Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) * B) *
          (Cjoint.toReal *
            (((((3 : ℝ) ^ m) / xRate) ^ (-kappa)) *
              euclideanNorm (matVecMul (matSqrt S) e))) ≤
        C * Real.sqrt (vecDot e (matVecMul S e)) *
          (r / x) ^ (-kappa) := by
    have hnonneg : 0 ≤ B * Cjoint.toReal *
        euclideanNorm (matVecMul (matSqrt S) e) :=
      mul_nonneg (mul_nonneg hB.le ENNReal.toReal_nonneg)
        (euclideanNorm_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right hrateAffine hnonneg
    have hnorm := euclideanNorm_matSqrt_eq_sqrt_vecDot hSRaw.posSemidef e
    calc
      (Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) * B) *
            (Cjoint.toReal *
              (((((3 : ℝ) ^ m) / xRate) ^ (-kappa)) *
                euclideanNorm (matVecMul (matSqrt S) e))) =
          (Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) *
            ((((3 : ℝ) ^ m) / xRate) ^ (-kappa))) *
            (B * Cjoint.toReal *
              euclideanNorm (matVecMul (matSqrt S) e)) := by ring
      _ ≤ (Real.sqrt d / Caff) *
            (r / (mult * xRate)) ^ (-kappa) *
            (B * Cjoint.toReal *
              euclideanNorm (matVecMul (matSqrt S) e)) := by
        simpa only [S, Caff, overlinePi, mult] using hmul
      _ = C * Real.sqrt (vecDot e (matVecMul S e)) *
            (r / x) ^ (-kappa) := by
        rw [hxCommonEq, ← hnorm]
        dsimp only [C]
        ring
  calc
    _ = ENNReal.ofReal
        ((Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) * B) *
          (Cjoint.toReal *
            (((((3 : ℝ) ^ m) / xRate) ^ (-kappa)) *
              euclideanNorm (matVecMul (matSqrt S) e)))) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg _) hB.le),
        ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCjointTop.ne]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hrateFull

/-- **The corrector-decay terminal at an arbitrary certificate the reconciled-smallness
certificate.**  The
corrector-decay terminal closes in the exact square-root gauge.  The identity
response estimate is run at the targeted certificate scale; the single affine
multiplier already present in the exposed common scale pays for transport back
to the physical ellipsoid.

The corrector-family hypothesis and the good scale are read at a **given** certificate `GoodScale`
that projects to the printed one; the statement is the case
`GoodScale := PrintOrderRateBearingCommonAffineGoodScale d g c kappa`. -/
theorem exists_gaugeFrameCorrectorDecayConstant_atCertificate
    (d : ℕ) [NeZero d] (g : ℝ) (hg : g ∈ Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      let c := canonicalCorrectorSmallness d g hg
      ∀ (GoodScale : Mat d → CoeffSpace d → ℝ → Prop) (kappa : ℝ)
        (abar : Mat d)
        (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
        (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
        (∀ (a : CoeffSpace d) (x : ℝ), GoodScale abar a x →
          PrintOrderRateBearingCommonAffineGoodScale d g c kappa abar a x) →
        Root.CanonicalPullbackCorrectorFamily GoodScale abar Phi gradPhi →
        ∀ (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
          GoodScale abar a x →
          ∀ (e : Vec d) (r : ℝ), x ≤ r →
            ENNReal.ofReal r⁻¹ *
                  negOneNorm (ellipsoid abar r)
                    (fun y ↦ matVecMul (matSqrt (symmPart abar))
                      (gradPhi e a y)) +
                ENNReal.ofReal r⁻¹ *
                  negOneNorm (ellipsoid abar r)
                    (fun y ↦ matVecMul (matSqrt (symmPart abar))⁻¹
                      (matVecMul ((a.1 y : Mat d) - skewPart abar)
                          (e + gradPhi e a y) -
                        matVecMul (symmPart abar) e)) ≤
              ENNReal.ofReal
                (C * Real.sqrt
                    (vecDot e (matVecMul (symmPart abar) e)) *
                  (r / x) ^ (-kappa)) := by
  obtain ⟨Cjoint, hCjointTop, hCjointPos, hjoint⟩ :=
    exists_identityGaugeJointScaledNegOnePowerConstant
      d g (canonicalIdentityGeometry d g hg) hg
        (canonicalIdentityDualRegularity d g hg)
  let Caff : ℝ := Transport.roundedOuterResponseAffineConstant d
  let B : ℝ := closedBallScaledNegOneConstant d
  let C : ℝ :=
    (Real.sqrt d / Caff) * B * Cjoint.toReal
  have hCaff : 0 < Caff := by
    simpa only [Caff] using Transport.roundedOuterResponseAffineConstant_pos d
  have hB : 0 < B := by
    simpa only [B] using closedBallScaledNegOneConstant_pos d
  have hCjointReal : 0 < Cjoint.toReal :=
    ENNReal.toReal_pos hCjointPos.ne' hCjointTop.ne
  have hC : 0 < C := by
    dsimp only [C]
    have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
    positivity
  refine ⟨C, hC, ?_⟩
  dsimp only
  intro GoodScale kappa abar Phi gradPhi hproj hfamily a x hxOne hGoodAt e r hxr
  have hGood : PrintOrderRateBearingCommonAffineGoodScale d g
      (canonicalCorrectorSmallness d g hg) kappa abar a x :=
    hproj a x hGoodAt
  have hr : 0 < r := zero_lt_one.trans_le (hxOne.trans hxr)
  obtain ⟨sourceAmplitude, X, hCertificate, hxCommon⟩ := hGood
  have hCertificateData := hCertificate
  obtain ⟨_hSCert, _aCert, _hsCert, _hsCertHalf, _hAmplitude,
    hKappa, hXOne, _haCert, _hCertTail⟩ := hCertificateData
  let c : ℝ := canonicalCorrectorSmallness d g hg
  let target : ℝ := correctorTargetAmplitude c kappa
  let xRate : ℝ := targetedQuantitativeEffectiveScale
    sourceAmplitude target kappa X a
  let S : Mat d := symmPart abar
  let overlinePi : ℝ := specBound S * specBound S⁻¹
  let mult : ℝ := roundedAffineMultiplier Caff overlinePi kappa
  have hTarget : 0 < target := by
    dsimp only [target, c]
    exact correctorTargetAmplitude_pos
      (canonicalCorrectorSmallness_mem d g hg).1 hKappa
  have hTargetCertificate :
      PrintOrderQuantitativeNormalizedReferenceCertificate
        abar g target kappa xRate a := by
    simpa only [target, xRate] using
      hCertificate.targetedEffectiveScale hTarget
  have hTargetData := hTargetCertificate
  obtain ⟨_hSTarget, _aTarget, _hsTarget, _hsTargetHalf,
    _hTargetAmplitude, _hTargetKappa, hxRateOne,
    _haTarget, _hTargetTail⟩ := hTargetData
  have hxRate : 0 < xRate := zero_lt_one.trans_le hxRateOne
  have hxCommonEq : x = mult * xRate := by
    simpa only [c, target, xRate, S, overlinePi, mult, Caff,
      commonQuantitativeAffineScale, roundedAffineEffectiveScale] using
        hxCommon
  obtain ⟨hSIdentity, hI, aIdentity, hIdentity, hPower,
      PhiIdentity, hIdentityJoint⟩ :=
    exists_targetedIdentityGaugeJointLimit d g hg
      kappa abar a xRate hTargetCertificate
  obtain ⟨hSRaw, _sRaw, _toleranceRaw, aRaw, _LRaw, hCauchy,
      _hsRaw, _hsRawHalf, hRaw, _hGoodRaw, hRawJoint,
      hpullback⟩ := hfamily.normalizedJoint a x hGoodAt
  have hSProof : hSIdentity = hSRaw := Subsingleton.elim _ _
  subst hSIdentity
  let m : ℤ := outerTriadicGeneration (4 * r) (by positivity)
  let q : ℕ := m.toNat
  have hmNonneg : 0 ≤ m := by
    dsimp only [m]
    exact outerTriadicGeneration_nonneg_of_one_le (R := 4 * r)
      (by positivity) (by linarith only [hxOne, hxr])
  have hqCast : (q : ℤ) = m := by
    dsimp only [q]
    exact Int.toNat_of_nonneg hmNonneg
  have hrm : r ≤ (3 : ℝ) ^ m := by
    have houter := le_outerTriadicGeneration_scale
      (by positivity : 0 < 4 * r)
    have hfour : r ≤ 4 * r := by linarith only [hr]
    exact hfour.trans (by simpa only [m] using houter)
  have hxRateCommon : xRate ≤ x := by
    rw [hxCommonEq]
    exact le_roundedAffineEffectiveScale Caff overlinePi kappa xRate hxRate.le
  have hxRateQ : xRate ≤ (3 : ℝ) ^ q := by
    calc
      xRate ≤ x := hxRateCommon
      _ ≤ r := hxr
      _ ≤ (3 : ℝ) ^ m := hrm
      _ = (3 : ℝ) ^ q := by rw [← hqCast, zpow_natCast]
  have hpairQ := hjoint
    (exactGaugeCoeffSpace a abar hSRaw) hI aIdentity hIdentity
    kappa xRate hKappa hxRate hPower PhiIdentity hIdentityJoint
    (matVecMul (matSqrt S) e) q hxRateQ
  have hpairM :
      triadicScaledNegOneNorm m
            (correctorGradientOnOriginCube PhiIdentity
              (matVecMul (matSqrt S) e) m) +
        triadicScaledNegOneNorm m
            (scalarIdentityCorrectorFluxDefectOnOriginCube
              aIdentity PhiIdentity (matVecMul (matSqrt S) e) m) ≤
      Cjoint * ENNReal.ofReal
        (((((3 : ℝ) ^ m) / xRate) ^ (-kappa)) *
          euclideanNorm (matVecMul (matSqrt S) e)) := by
    have hthree : (3 : ℝ) ^ q = (3 : ℝ) ^ m := by
      rw [← hqCast, zpow_natCast]
    rw [hqCast, hthree] at hpairQ
    exact hpairQ
  have hphysical := physicalPair_le_identityGaugePair
    (canonicalIdentityGeometry d g hg) hSRaw aRaw hRaw hCauchy
    hRawJoint hI aIdentity hIdentity PhiIdentity hIdentityJoint
    gradPhi e (hpullback e).2 hr m rfl
  have hscaled :
      ENNReal.ofReal
            (Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) * B) *
          (triadicScaledNegOneNorm m
                (correctorGradientOnOriginCube PhiIdentity
                  (matVecMul (matSqrt S) e) m) +
            triadicScaledNegOneNorm m
                (scalarIdentityCorrectorFluxDefectOnOriginCube
                  aIdentity PhiIdentity (matVecMul (matSqrt S) e) m)) ≤
        ENNReal.ofReal
          (Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) * B) *
        (Cjoint * ENNReal.ofReal
          (((((3 : ℝ) ^ m) / xRate) ^ (-kappa)) *
            euclideanNorm (matVecMul (matSqrt S) e))) := by
    have hmul := mul_le_mul_left hpairM
      (ENNReal.ofReal
        (Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) * B))
    calc
      ENNReal.ofReal
            (Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) * B) *
          (triadicScaledNegOneNorm m
                (correctorGradientOnOriginCube PhiIdentity
                  (matVecMul (matSqrt S) e) m) +
            triadicScaledNegOneNorm m
                (scalarIdentityCorrectorFluxDefectOnOriginCube
                  aIdentity PhiIdentity (matVecMul (matSqrt S) e) m)) =
        (triadicScaledNegOneNorm m
                (correctorGradientOnOriginCube PhiIdentity
                  (matVecMul (matSqrt S) e) m) +
            triadicScaledNegOneNorm m
                (scalarIdentityCorrectorFluxDefectOnOriginCube
                  aIdentity PhiIdentity (matVecMul (matSqrt S) e) m)) *
          ENNReal.ofReal
            (Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) * B) :=
        mul_comm _ _
      _ ≤ (Cjoint * ENNReal.ofReal
            (((((3 : ℝ) ^ m) / xRate) ^ (-kappa)) *
              euclideanNorm (matVecMul (matSqrt S) e))) *
          ENNReal.ofReal
            (Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) * B) := hmul
      _ = _ := mul_comm _ _
  have hrate := affine_scaled_pair_le_physical_rate abar hSRaw
    hKappa hxRate hr hrm B hB Cjoint hCjointTop e hxCommonEq
  have hfinal := hphysical.trans (by
    simpa only [S, B] using hscaled.trans hrate)
  simpa only [C, Caff, B, S] using hfinal

end

end CorrectorComposition
end HighContrast
end HCPolySupport
