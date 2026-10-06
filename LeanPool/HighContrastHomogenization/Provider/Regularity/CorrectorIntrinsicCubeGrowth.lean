/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorAnchoredFunctionGrowth
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorCoarseOscillationGrowth

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorIntrinsicCubeGrowth

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Centered-cube corrector growth from an intrinsic good tail

This module packages the complete discrete-radius function-growth estimate: the
coarse-grained Poincare inequality at a good scale, the anchored mean telescope,
and the fluctuation-plus-mean split of the normalized norm.  No representative
of the physical coefficient field enters it.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A sufficiently small scalar good tail gives scale-linear normalized
`L²` growth of the global corrector representative on all sufficiently large
centered triadic cubes. -/
theorem exists_scalarIdentityGoodTailCorrectorCubeGrowthConstant
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ K c : ℝ, 0 < K ∧ c ∈ Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a) (e : Vec d),
          ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, n.toNat ≤ q →
            cubeLpNorm (originCube d (q : ℤ)) (2 : ℝ≥0∞)
                (finiteAffineCorrectionJointLocalLimit a hCauchy e).globalValueRepresentative ≤
              C * (3 : ℝ) ^ q := by
  obtain ⟨K, c, hK, hc, hosc⟩ :=
    exists_scalarIdentityGoodTailCorrectorOscillationConstant d s hs hs_lt
  refine ⟨K, c, hK, hc, ?_⟩
  intro a delta n hdelta hgood hCauchy e
  apply
    NormalizedLocalH1Carrier.exists_globalRepresentativeLpBound_of_oscillation
    (finiteAffineCorrectionJointLocalLimit a hCauchy e)
    n.toNat (K * euclideanNorm e)
    (mul_nonneg hK.le (euclideanNorm_nonneg e))
  intro q hnq
  apply hosc a delta n hdelta hgood hCauchy e q
  omega

end

end HighContrast
end HCPolySupport
