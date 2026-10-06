/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileDefectIdentities

/-!
# High-contrast homogenization: Provider.Response.RandomAdaptedResponseDefectBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Adjoint response-defect coordinates

The sign congruence in the adjoint recentered block turns the doubled load
`(-p,r)` into the common positive-coordinate load `(p,r)` inside its
quadratic form.  This is the coordinate form used by response calibration.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

/-- The adjoint response defect is the increment of the primal recentered
quadratic form at the positive doubled load. -/
theorem profile_adjoint_response_defect_eq_recentered_quadratic
    {d : ℕ} {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) {g : Mat d} (hg : IsSkewMat g)
    {s t : ℤ} (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t) (p r : Vec d) :
    profileAdjointResponseDefect P hq g hg s t p r =
      (1 / 2 : ℝ) *
        (blockVecDot ((p, r) : BlockVec d)
            (blockMatVecMul (profileRecenteredMean P q g s)
              ((p, r) : BlockVec d)) -
          blockVecDot ((p, r) : BlockVec d)
            (blockMatVecMul (profileRecenteredMean P q g t)
              ((p, r) : BlockVec d))) := by
  rw [profileAdjointResponseDefect_identity hq hg hints hintt,
    blockMatVecMul_blockSub, blockVecDot_sub_right]
  change (1 / 2 : ℝ) *
      (blockVecDot ((-p, r) : BlockVec d)
          (blockMatVecMul
            (blockMatMul (blockDiag 1 (-1))
              (blockMatMul (profileRecenteredMean P q g s)
                (blockDiag 1 (-1)))) ((-p, r) : BlockVec d)) -
        blockVecDot ((-p, r) : BlockVec d)
          (blockMatVecMul
            (blockMatMul (blockDiag 1 (-1))
              (blockMatMul (profileRecenteredMean P q g t)
                (blockDiag 1 (-1)))) ((-p, r) : BlockVec d))) = _
  rw [blockQuadratic_adjointSign_congr,
    blockQuadratic_adjointSign_congr,
    adjointSign_mulVec]
  change (1 / 2 : ℝ) *
      (blockVecDot ((-p, -r) : BlockVec d)
          (blockMatVecMul (profileRecenteredMean P q g s)
            ((-p, -r) : BlockVec d)) -
        blockVecDot ((-p, -r) : BlockVec d)
          (blockMatVecMul (profileRecenteredMean P q g t)
            ((-p, -r) : BlockVec d))) = _
  have hquadratic (A : BlockMat d) :
      blockVecDot ((-p, -r) : BlockVec d)
          (blockMatVecMul A ((-p, -r) : BlockVec d)) =
        blockVecDot ((p, r) : BlockVec d)
          (blockMatVecMul A ((p, r) : BlockVec d)) := by
    have hneg : ((-p, -r) : BlockVec d) =
        -((p, r) : BlockVec d) := rfl
    rw [hneg, ← neg_one_smul ℝ ((p, r) : BlockVec d),
      blockMatVecMul_smul, blockVecDot_smul_left,
      blockVecDot_smul_right]
    norm_num
  rw [hquadratic, hquadratic]

end

end HCPolySupport.HighContrast.Response
