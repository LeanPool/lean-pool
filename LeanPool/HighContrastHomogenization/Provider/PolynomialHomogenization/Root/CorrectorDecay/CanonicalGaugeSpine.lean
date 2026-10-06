/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.PrintOrderJointTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRateBearingCommonAffineGoodScaleEvent

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.CanonicalGaugeSpine

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open Set

noncomputable section

@[expose]
noncomputable def canonicalIdentityRegularityConstant
    (d : ℕ) [NeZero d] (g : ℝ) (hg : g ∈ Ico (0 : ℝ) 1) : ℝ :=
  Classical.choose (exists_printOrderIdentityCubeDualRegularityWithConstant
    d g hg)

theorem canonicalIdentityRegularity
    (d : ℕ) [NeZero d] (g : ℝ) (hg : g ∈ Ico (0 : ℝ) 1) :
    PrintOrderIdentityCubeDualRegularityWithConstant d g
      (canonicalIdentityRegularityConstant d g hg) :=
  Classical.choose_spec
    (exists_printOrderIdentityCubeDualRegularityWithConstant d g hg)

@[expose]
noncomputable def canonicalIdentitySpine
    (d : ℕ) [NeZero d] (g : ℝ) (hg : g ∈ Ico (0 : ℝ) 1) :
    PrintOrderToleranceSelectedRoundedSpine d
      (canonicalIdentityRegularityConstant d g hg) :=
  Classical.choice (nonempty_printOrderToleranceSelectedRoundedSpine d
    (canonicalIdentityRegularityConstant d g hg))

@[expose]
def canonicalIdentityGeometry
    (d : ℕ) [NeZero d] (g : ℝ) (hg : g ∈ Ico (0 : ℝ) 1) :
    RoundedGenerationAnalyticGeometry d :=
  (canonicalIdentitySpine d g hg).geometry

theorem canonicalIdentityDualRegularity
    (d : ℕ) [NeZero d] (g : ℝ) (hg : g ∈ Ico (0 : ℝ) 1) :
    PrintOrderRoundedReferenceDualRegularityAtGeneration d g
      (canonicalIdentityGeometry d g hg).generation := by
  exact printOrderRoundedReferenceDualRegularityAtGeneration_of_absorption
    d g (canonicalIdentityRegularityConstant d g hg) hg
      (canonicalIdentityRegularity d g hg)
      (canonicalIdentitySpine d g hg).absorptionProperties

@[expose]
noncomputable def canonicalCorrectorSmallness
    (d : ℕ) [NeZero d] (g : ℝ) (hg : g ∈ Ico (0 : ℝ) 1) : ℝ :=
  identitySuccessorSmallness d g (canonicalIdentityGeometry d g hg)
    hg (canonicalIdentityDualRegularity d g hg)

theorem canonicalCorrectorSmallness_mem
    (d : ℕ) [NeZero d] (g : ℝ) (hg : g ∈ Ico (0 : ℝ) 1) :
    canonicalCorrectorSmallness d g hg ∈ Ioo (0 : ℝ) 1 := by
  exact identitySuccessorSmallness_mem d g
    (canonicalIdentityGeometry d g hg) hg
      (canonicalIdentityDualRegularity d g hg)

theorem exists_canonicalIdentityGaugeFamily
    {d : ℕ} [NeZero d] {g : ℝ} {a : CoeffSpace d} {abar : Mat d}
    {amplitude kappa x : ℝ} (hg : g ∈ Ico (0 : ℝ) 1)
    (hcert : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g amplitude kappa x a) :
    ∃ (hS : (symmPart abar).PosDef)
        (hI : (symmPart (1 : Mat d)).PosDef)
        (aIdentity : Book.Ch03.CoeffFamily d),
      (∀ Q : TriadicCube d,
        (aIdentity.coeffOn Q).toCoeffField =
          (⇑((canonicalIdentityGeometry d g hg).centeredCoeffSpace
            (1 : Mat d) hI (exactGaugeCoeffSpace a abar hS)).1 :
              CoeffField d)) ∧
      ScalarIdentityPowerTail aIdentity
        (printCertificateOrder g) amplitude kappa x := by
  let spine := canonicalIdentitySpine d g hg
  obtain ⟨hS, hI, aIdentity, hIdentity, htail⟩ :=
    exists_identityGaugeFamily hcert spine.geometry
  exact ⟨hS, hI, aIdentity, hIdentity, htail⟩

end

end HighContrast
end HCPolySupport
