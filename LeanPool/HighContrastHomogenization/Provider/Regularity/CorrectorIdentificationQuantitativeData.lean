/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicCubeGrowth
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicSlopeGoodTail

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorIdentificationQuantitativeData

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quantitative data for corrector identification

One good-tail threshold supplies the intrinsic slope and the scale-linear value
growth of every canonical joint corrector.  Both conclusions are independent of
the physical coefficient field: the value row comes from the coarse-grained
Poincare inequality at a good scale, so no ellipticity pair enters here.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

/-- A common scalar-identity good-tail threshold produces the two
coefficient-free corrector facts consumed by translated-gradient
identification. -/
theorem exists_scalarIdentityGoodTailCorrectorIdentificationDataConstant
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hsLt : s < 1 / 2) :
    ∃ c : ℝ, c ∈ Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a) (e : Vec d),
          HasIntrinsicNormalizedSlope e
              (finiteAffineCorrectionJointLocalLimit a hCauchy e) ∧
            ∃ C : ℝ, 0 ≤ C ∧
              ∀ q : ℕ, n.toNat ≤ q →
                cubeLpNorm (originCube d (q : ℤ)) (2 : ENNReal)
                    (finiteAffineCorrectionJointLocalLimit
                      a hCauchy e).globalValueRepresentative ≤
                  C * (3 : ℝ) ^ q := by
  obtain ⟨cSlope, hcSlope, hSlope⟩ :=
    exists_scalarIdentityGoodTailIntrinsicSlopeThreshold d s hs hsLt
  obtain ⟨_KCube, cCube, _hKCube, hcCube, hCube⟩ :=
    exists_scalarIdentityGoodTailCorrectorCubeGrowthConstant d s hs hsLt
  let c : ℝ := min cSlope cCube
  have hc : c ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_min hcSlope.1 hcCube.1, (min_le_left cSlope cCube).trans_lt hcSlope.2⟩
  refine ⟨c, hc, ?_⟩
  intro a delta n hdelta hgood hCauchy e
  have hdeltaSlope : delta ∈ Ioc (0 : ℝ) cSlope :=
    ⟨hdelta.1, hdelta.2.trans (min_le_left _ _)⟩
  have hdeltaCube : delta ∈ Ioc (0 : ℝ) cCube :=
    ⟨hdelta.1, hdelta.2.trans (min_le_right _ _)⟩
  obtain ⟨hSlopeCauchy, hIntrinsic⟩ := hSlope a delta n hdeltaSlope hgood e
  have hIntrinsicAtSelected : HasIntrinsicNormalizedSlope e
      (finiteAffineCorrectionJointLocalLimit a hCauchy e) := by
    have hProof : hSlopeCauchy = hCauchy := Subsingleton.elim _ _
    simpa only [hProof] using hIntrinsic
  exact ⟨hIntrinsicAtSelected, hCube a delta n hdeltaCube hgood hCauchy e⟩

end

end HighContrast
end HCPolySupport
