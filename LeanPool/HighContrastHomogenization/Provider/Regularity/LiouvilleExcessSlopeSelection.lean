/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleFixedCubeExcess

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleExcessSlopeSelection

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Approximate slope selection from finite affine excess

The finite affine excess is an `ENNReal` infimum and need not be attained.
This module selects arbitrarily accurate candidates and, when a ruled slope
family is available, reparameterizes them by their exact target slope on the
fixed inner cube.
-/

namespace HCPolySupport
namespace HighContrast

open Filter
open scoped ENNReal

noncomputable section

/-- Every positive tolerance admits an affine-boundary candidate strictly
below the finite affine excess plus that tolerance. No attainment is used. -/
theorem exists_finiteAffineGradientExcess_candidate_lt_add
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0) :
    ∃ b : Vec d,
      weightedGradNorm
          (a.coeffOn (originCube d n)).toCoeffField
          (openCubeSet (originCube d n))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m b).toH1.grad x) <
        finiteAffineGradientExcess a n m u + epsilon := by
  have hcandidateTop : weightedGradNorm
      (a.coeffOn (originCube d n)).toCoeffField
      (openCubeSet (originCube d n))
      (fun x ↦ u.toH1.grad x -
        (finiteAffineSolution a m (0 : Vec d)).toH1.grad x) ≠ ∞ := by
    rw [weightedGradNorm_finiteAffineGradientResidual a hnm u 0]
    exact ENNReal.ofReal_ne_top
  have hexcessTop : finiteAffineGradientExcess a n m u ≠ ∞ :=
    ne_top_of_le_ne_top hcandidateTop
      (finiteAffineGradientExcess_le a n m u 0)
  have hlt : finiteAffineGradientExcess a n m u <
      finiteAffineGradientExcess a n m u + epsilon :=
    ENNReal.lt_add_right hexcessTop hepsilon
  unfold finiteAffineGradientExcess at hlt
  exact iInf_lt_iff.mp hlt

end

end HighContrast
end HCPolySupport
