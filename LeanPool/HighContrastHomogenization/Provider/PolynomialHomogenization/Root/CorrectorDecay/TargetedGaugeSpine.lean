/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.CanonicalGaugeSpine

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.TargetedGaugeSpine

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open Set

noncomputable section

/-- A target-amplitude certificate constructs the canonical identity-gauge
joint corrector at its own (pre-affine) effective scale.  This is the exact
variant needed to retain the affine multiplier for the later physical
negative-one transport. -/
theorem exists_targetedIdentityGaugeJointLimit
    (d : ℕ) [NeZero d] (g : ℝ) (hg : g ∈ Ico (0 : ℝ) 1) :
    let c := canonicalCorrectorSmallness d g hg
    ∀ (kappa : ℝ) (abar : Mat d) (a : CoeffSpace d) (x : ℝ),
      PrintOrderQuantitativeNormalizedReferenceCertificate abar g
          (correctorTargetAmplitude c kappa) kappa x a →
      ∃ (hS : (symmPart abar).PosDef)
          (hI : (symmPart (1 : Mat d)).PosDef)
          (aIdentity : Book.Ch03.CoeffFamily d),
        (∀ Q : TriadicCube d,
          (aIdentity.coeffOn Q).toCoeffField =
            (⇑((canonicalIdentityGeometry d g hg).centeredCoeffSpace
              (1 : Mat d) hI (exactGaugeCoeffSpace a abar hS)).1 :
                CoeffField d)) ∧
        ScalarIdentityPowerTail aIdentity (printCertificateOrder g)
          (correctorTargetAmplitude c kappa) kappa x ∧
        ∃ Phi : Vec d → NormalizedLocalH1Carrier d,
          IsFiniteAffineCorrectionJointLocalEquation aIdentity Phi := by
  dsimp only
  intro kappa abar a x hCertificate
  have hCertificateData := hCertificate
  obtain ⟨_hS, _aRef, _hs, _hsHalf, _hAmplitude,
    hKappa, hxOne, _haRef, _htail⟩ := hCertificateData
  let c := canonicalCorrectorSmallness d g hg
  obtain ⟨hS, hI, aIdentity, hIdentity, hPowerTail⟩ :=
    exists_canonicalIdentityGaugeFamily hg hCertificate
  refine ⟨hS, hI, aIdentity, hIdentity, hPowerTail, ?_⟩
  have hTargetNonneg : 0 ≤ correctorTargetAmplitude c kappa :=
    (correctorTargetAmplitude_pos
      (canonicalCorrectorSmallness_mem d g hg).1 hKappa).le
  have hgood : ScalarIdentityGoodTail aIdentity
      (printCertificateOrder g) (c / 2)
      (Quenched.triadicCeilingIndex x : ℤ) := by
    have hraw := hPowerTail.goodTail hTargetNonneg hKappa hxOne
    rw [correctorTargetAmplitude_div hKappa] at hraw
    simpa only [c] using hraw
  have hhalf : c / 2 ∈ Ioc (0 : ℝ) c := by
    have hc := canonicalCorrectorSmallness_mem d g hg
    constructor <;> linarith only [hc.1]
  have hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g (canonicalIdentityGeometry d g hg).generation :=
    canonicalIdentityDualRegularity d g hg
  obtain ⟨Phi, hPhi, _htail⟩ := exists_identityGaugeJointLimitWithTail
      d g (canonicalIdentityGeometry d g hg) hg hdual
      (exactGaugeCoeffSpace a abar hS)
      hI aIdentity hIdentity (c / 2)
      (Quenched.triadicCeilingIndex x : ℤ) hhalf hgood
  exact ⟨Phi, hPhi⟩

end

end HighContrast
end HCPolySupport
