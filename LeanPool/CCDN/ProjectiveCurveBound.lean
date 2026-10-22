/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Statements
import LeanPool.CCDN.Curve.ProjectiveCurveCount

/-! CCDN Theorem 2 in every ambient dimension. Degree is the slope of
the homogeneous Hilbert function. The height and count use rational
projective points. All projection and plane-counting inputs are proved; the count with an
explicit constant is `projective_curve_count`, in `CCDN.Curve.ProjectiveCurveCount`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- CCDN (2020), Theorem 2: the bound `ProjectiveCurveBound`. -/
theorem projectiveCurveBound : ProjectiveCurveBound := by
  intro n _
  refine ⟨projectiveCurveConstant n, projectiveCurveConstant_pos n, ?_⟩
  intro I hI d hd hdegree B hB
  have : I.IsPrime := hI
  exact projective_curve_count I hd hdegree hB

end
end CCDN
