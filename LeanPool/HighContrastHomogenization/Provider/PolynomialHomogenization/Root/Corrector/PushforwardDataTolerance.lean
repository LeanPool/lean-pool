/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.IntrinsicCorrectorEvent
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.CorrectorWeakGradientRow
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIdentificationQuantitativeData

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardDataTolerance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The identification-data tolerance

The thresholds at which a weak-error row already carries the intrinsic slope,
the scale-linear value growth and the weak gradient row.

These declarations read a triadic family alone: no coefficient representative
and no ellipticity pair appears in any of them, so the normalized-gauge supply
consumes them unchanged.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The threshold at which a weak-error row already carries the intrinsic
slope and the scale-linear value growth. -/
@[expose]
def rootCorrectorDataTolerance (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s)
    (hs2 : s < 1 / 2) : ℝ :=
  Classical.choose
    (exists_scalarIdentityGoodTailCorrectorIdentificationDataConstant d s hs hs2)

theorem rootCorrectorData_spec (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s)
    (hs2 : s < 1 / 2) :
    rootCorrectorDataTolerance d s hs hs2 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Ioc (0 : ℝ) (rootCorrectorDataTolerance d s hs hs2) →
        ScalarIdentityGoodTail a s delta n →
        ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a) (e : Vec d),
          HasIntrinsicNormalizedSlope e
              (finiteAffineCorrectionJointLocalLimit a hCauchy e) ∧
            ∃ C : ℝ, 0 ≤ C ∧
              ∀ q : ℕ, n.toNat ≤ q →
                cubeLpNorm (originCube d (q : ℤ)) (2 : ENNReal)
                    (finiteAffineCorrectionJointLocalLimit
                      a hCauchy e).globalValueRepresentative ≤
                  C * (3 : ℝ) ^ q :=
  Classical.choose_spec
    (exists_scalarIdentityGoodTailCorrectorIdentificationDataConstant d s hs hs2)

/-- The threshold at which a weak-error row already carries the weak gradient
row of the anchored corrector. -/
@[expose]
def rootCorrectorWeakRowTolerance (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s)
    (hs2 : s < 1 / 2) : ℝ :=
  Classical.choose
    (exists_scalarIdentityGoodTailCorrectorWeakGradientRowConstant d s hs hs2)

theorem rootCorrectorWeakRow_spec (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s)
    (hs2 : s < 1 / 2) :
    rootCorrectorWeakRowTolerance d s hs hs2 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Ioc (0 : ℝ) (rootCorrectorWeakRowTolerance d s hs hs2) →
        ScalarIdentityGoodTail a s delta n →
        ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a) (e : Vec d),
          ∃ N : ℝ, 0 ≤ N ∧ ∀ q : ℕ, n.toNat ≤ q →
            cubeScaleNormalizedDualNegativeBesovVectorNormTwo
                (originCube d (q : ℤ)) s
                (fun x => e + (finiteAffineCorrectionJointLocalLimit a hCauchy
                  e).globalGradientRepresentative x) ≤ N :=
  Classical.choose_spec
    (exists_scalarIdentityGoodTailCorrectorWeakGradientRowConstant d s hs hs2)

/-- The tolerance at which the construction, its value row and its weak
gradient row are all available, at the order `s`. -/
@[expose]
def rootCorrectorSupplyTolerance (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s)
    (hs2 : s < 1 / 2) : ℝ :=
  min (min (rootCorrectorTolerance d s hs hs2) (rootCorrectorDataTolerance d s hs hs2))
    (rootCorrectorWeakRowTolerance d s hs hs2)

theorem rootCorrectorSupplyTolerance_pos (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s)
    (hs2 : s < 1 / 2) :
    0 < rootCorrectorSupplyTolerance d s hs hs2 :=
  lt_min (lt_min (rootCorrectorTolerance_pos d s hs hs2)
      (rootCorrectorData_spec d s hs hs2).1.1)
    (rootCorrectorWeakRow_spec d s hs hs2).1.1

end

end Root
end HighContrast
end HCPolySupport
