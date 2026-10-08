/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentitySuccessorLocal
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentityFiniteEnergy

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentitySuccessorRecurrence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open Set
open scoped BigOperators

noncomputable section

/-- The available selected-generation recurrence, specialized to an exact
identity-gauge family and to the successor restriction. -/
theorem exists_identityGaugeSuccessorRecurrenceConstant
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (aGauge : CoeffSpace d) (hI : (symmPart (1 : Mat d)).PosDef)
        (aIdentity : Book.Ch03.CoeffFamily d),
        (∀ Q : TriadicCube d,
          (aIdentity.coeffOn Q).toCoeffField =
            (⇑(geom.centeredCoeffSpace (1 : Mat d) hI aGauge).1 :
              CoeffField d)) →
        ∀ (q m : ℤ) (e : Vec d), q ≤ m - 1 - 2 →
          ScalarIdentityGoodMaxOnInterval aIdentity
            (printCertificateOrder g) 1 q (m - 1 - 2) →
          ∀ h ∈ Finset.Icc q (m - 1 - 2),
            finiteCenteredCubeSolutionEnergy aIdentity (m - 1 - 2)
                (successorInnerRestriction aIdentity m e) h ≤
              C * finiteCenteredCubeSolutionEnergy aIdentity (m - 1 - 2)
                  (successorInnerRestriction aIdentity m e) (m - 1 - 2) +
                C * ∑ j ∈ Finset.Ioc h (m - 1 - 2),
                  scalarIdentityWeakError aIdentity
                      (printCertificateOrder g) j *
                    finiteCenteredCubeSolutionEnergy aIdentity (m - 1 - 2)
                      (successorInnerRestriction aIdentity m e) j := by
  obtain ⟨C, hC, hrecurrence⟩ :=
    exists_printOrderRoundedGenerationUniformFiniteRecurrenceConstant
      d g geom hg hdual
  refine ⟨C, hC, ?_⟩
  intro aGauge hI aIdentity hIdentity q m e hqm hgood h hh
  let s := printCertificateOrder g
  let vInner := successorInnerRestriction aIdentity m e
  have hgoodRounded : RoundedGenerationSpatialGoodMaxOnInterval
      geom.generation aGauge (1 : Mat d) hI s 1 q (m - 1 - 2) := by
    intro j hj
    change geom.spatialWeakError aGauge (1 : Mat d) hI s j ≤ 1
    rw [roundedGenerationSpatialWeakError_one_eq
      geom aGauge hI aIdentity hIdentity s j]
    exact hgood j hj
  have hraw := hrecurrence aGauge (1 : Mat d) hI aIdentity hIdentity
    q (m - 1 - 2) vInner hqm hgoodRounded h hh
  have herrEq : ∀ j : ℤ,
      roundedGenerationSpatialWeakError geom.generation
          aGauge (1 : Mat d) hI s j =
        scalarIdentityWeakError aIdentity s j := by
    intro j
    simpa only [RoundedGenerationAnalyticGeometry.spatialWeakError] using
      roundedGenerationSpatialWeakError_one_eq
        geom aGauge hI aIdentity hIdentity s j
  have hsum : (∑ j ∈ Finset.Ioc h (m - 1 - 2),
        roundedGenerationSpatialWeakError geom.generation
            aGauge (1 : Mat d) hI s j *
          finiteCenteredCubeSolutionEnergy aIdentity (m - 1 - 2) vInner j) =
      ∑ j ∈ Finset.Ioc h (m - 1 - 2),
        scalarIdentityWeakError aIdentity s j *
          finiteCenteredCubeSolutionEnergy aIdentity (m - 1 - 2) vInner j := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [herrEq j]
  rw [hsum] at hraw
  exact hraw

end

end HighContrast
end HCPolySupport
