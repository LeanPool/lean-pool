/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.IntrinsicSlopeTranslatedGradientCancellation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleReverseValueGradient

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleTranslatedGradientIdentification

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Translated-gradient identification from reverse Liouville classification

The reverse theorem classifies a translated affine-corrector pair using an
initially unknown slope.  Intrinsic normalization identifies that slope with
the original one, after which the corrector gradients agree almost everywhere.
The fixed-translation boundary cost is carried by the weak corrector row of the
source carrier.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

/-- Under one small scalar good-tail threshold, reverse Liouville
classification plus intrinsic normalization identifies a translated corrector
gradient with the target joint family at the original slope. -/
theorem exists_scalarIdentityGoodTailLiouvilleTranslatedGradientIdentificationConstant
    (d : ℕ) [NeZero d] (s theta : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) (htheta : theta < 1) :
    ∃ c : ℝ, c ∈ Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ (PhiTarget : Vec d → NormalizedLocalH1Carrier d),
          IsFiniteAffineCorrectionJointLocalEquation a PhiTarget →
          ∀ {b : CoeffField d}, IsAELocallyUniformlyElliptic b →
            (∀ q : ℕ,
              Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a
                =ᵐ[volume.restrict (localGradientCube d q)] b) →
            ∀ (PhiSource : NormalizedLocalH1Carrier d) (e t : Vec d)
              (sRow N : ℝ) (q0 : ℕ),
              0 < sRow → sRow < 1 / 2 →
              HasIntrinsicNormalizedSlope e PhiSource →
              (∀ e' : Vec d,
                HasIntrinsicNormalizedSlope e' (PhiTarget e')) →
              (∀ q : ℕ, q0 ≤ q →
                cubeScaleNormalizedDualNegativeBesovVectorNormTwo
                    (originCube d (q : ℤ)) sRow
                    (fun x ↦ e + PhiSource.globalGradientRepresentative x) ≤ N) →
              ∀ {v : Vec d → ℝ},
                MemLiouvilleClass b theta v
                  (fun x ↦ e + PhiSource.globalGradientRepresentative (x + t)) →
                (fun x ↦ PhiSource.globalGradientRepresentative (x + t))
                  =ᵐ[volume] (PhiTarget e).globalGradientRepresentative := by
  obtain ⟨c, hc, hReverse⟩ :=
    exists_scalarIdentityGoodTailLiouvilleReverseValueGradientForJointEquationConstant
      d s theta hs hs_lt htheta
  refine ⟨c, hc, ?_⟩
  intro a delta n hdelta hgood PhiTarget hTargetEquation b hb
    hcoeff PhiSource e t sRow N q0 hsRow hsRow2 hSourceIntrinsic hTargetIntrinsic
    hRow v hLiouville
  obtain ⟨e', _c0, _hValue, hFullGradient⟩ :=
    hReverse a delta n hdelta hgood PhiTarget hTargetEquation
      hb hcoeff hLiouville
  have hslope : e = e' :=
    intrinsicSlope_eq_of_translated_globalFullGradient_ae_eq_of_weakRow
      hSourceIntrinsic (hTargetIntrinsic e') t e hsRow hsRow2 q0 N hRow
      hFullGradient
  have hCorrector :=
    globalGradient_translate_ae_eq_of_intrinsicSlopes_of_fullGradient_ae_eq_of_weakRow
      hSourceIntrinsic (hTargetIntrinsic e') t e hsRow hsRow2 q0 N hRow
      hFullGradient
  rw [← hslope] at hCorrector
  exact hCorrector

end

end HighContrast
end HCPolySupport
