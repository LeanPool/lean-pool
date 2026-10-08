/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentitySuccessorRecurrence

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentitySuccessorConstants

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open Set
open scoped BigOperators

noncomputable section

/-- Chosen local comparison constant for the identity gauge at the supplied rounded geometry. -/
@[expose]
noncomputable def identitySuccessorLocalConstant
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1) : ℝ :=
  Classical.choose (exists_identityGaugeSuccessorLocalConstant d g geom hg)

theorem identitySuccessorLocalConstant_spec
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1) :
    0 < identitySuccessorLocalConstant d g geom hg ∧
      ∀ (aGauge : CoeffSpace d) (hI : (symmPart (1 : Mat d)).PosDef)
        (aIdentity : Book.Ch03.CoeffFamily d),
        (∀ Q : TriadicCube d,
          (aIdentity.coeffOn Q).toCoeffField =
            (⇑(geom.centeredCoeffSpace (1 : Mat d) hI aGauge).1 :
              CoeffField d)) →
        ∀ (m : ℤ) (e : Vec d),
          scalarIdentityWeakError aIdentity
              (printCertificateOrder g) (m - 1) ≤ 1 →
          scalarIdentityWeakError aIdentity
              (printCertificateOrder g) m ≤ 1 →
          scalarIdentityWeakError aIdentity
              (printCertificateOrder g) (m + 1) ≤ 1 →
          Book.Ch03.h1EnergyNormOnCube (originCube d (m - 1 - 2))
              aIdentity (successorInnerRestriction aIdentity m e).toH1 ≤
            identitySuccessorLocalConstant d g geom hg *
                (scalarIdentityWeakError aIdentity
                    (printCertificateOrder g) m +
                  scalarIdentityWeakError aIdentity
                    (printCertificateOrder g) (m + 1)) *
              euclideanNorm e :=
  Classical.choose_spec
    (exists_identityGaugeSuccessorLocalConstant d g geom hg)

/-- Chosen constant controlling the identity-gauge finite energy recurrence. -/
@[expose]
noncomputable def identitySuccessorRecurrenceConstant
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation) : ℝ :=
  Classical.choose
    (exists_identityGaugeSuccessorRecurrenceConstant d g geom hg hdual)

theorem identitySuccessorRecurrenceConstant_spec
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation) :
    1 ≤ identitySuccessorRecurrenceConstant d g geom hg hdual ∧
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
              identitySuccessorRecurrenceConstant d g geom hg hdual *
                finiteCenteredCubeSolutionEnergy aIdentity (m - 1 - 2)
                  (successorInnerRestriction aIdentity m e) (m - 1 - 2) +
              identitySuccessorRecurrenceConstant d g geom hg hdual *
                ∑ j ∈ Finset.Ioc h (m - 1 - 2),
                  scalarIdentityWeakError aIdentity
                      (printCertificateOrder g) j *
                    finiteCenteredCubeSolutionEnergy aIdentity (m - 1 - 2)
                      (successorInnerRestriction aIdentity m e) j :=
  Classical.choose_spec
    (exists_identityGaugeSuccessorRecurrenceConstant d g geom hg hdual)

/-- Energy comparison constant given by twice the recurrence constant times the local constant. -/
@[expose]
noncomputable def identitySuccessorEnergyConstant
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation) : ℝ :=
  2 * identitySuccessorRecurrenceConstant d g geom hg hdual *
    identitySuccessorLocalConstant d g geom hg

/-- Minimum of one half and the inverse of twice the recurrence constant. -/
@[expose]
noncomputable def identitySuccessorSmallness
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation) : ℝ :=
  min (1 / 2 : ℝ)
    (2 * identitySuccessorRecurrenceConstant d g geom hg hdual)⁻¹

theorem identitySuccessorEnergyConstant_pos
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation) :
    0 < identitySuccessorEnergyConstant d g geom hg hdual := by
  have hrec := (identitySuccessorRecurrenceConstant_spec
    d g geom hg hdual).1
  have hlocal := (identitySuccessorLocalConstant_spec d g geom hg).1
  exact mul_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hrec)) hlocal

theorem identitySuccessorSmallness_mem
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation) :
    identitySuccessorSmallness d g geom hg hdual ∈ Ioo (0 : ℝ) 1 := by
  have hrec := (identitySuccessorRecurrenceConstant_spec
    d g geom hg hdual).1
  have hrecPos : 0 < identitySuccessorRecurrenceConstant d g geom hg hdual :=
    zero_lt_one.trans_le hrec
  constructor
  · exact lt_min (by norm_num) (inv_pos.mpr (mul_pos (by norm_num) hrecPos))
  · exact (min_le_left (1 / 2 : ℝ) _).trans_lt (by norm_num)

end

end HighContrast
end HCPolySupport
