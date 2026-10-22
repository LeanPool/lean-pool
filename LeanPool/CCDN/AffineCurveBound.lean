/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Statements
import LeanPool.CCDN.Curve.AffineCurveCount

/-! The full coefficient-uniform affine curve counting theorem, with constants
depending only on ambient dimension and with the exact degree dependence in
CCDN Theorem 3. The proof is `affine_curve_count`, in `CCDN.Curve.AffineCurveCount`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The affine curve counting bound `AffineCurveBound` of CCDN Theorem 3. -/
theorem affineCurveBound : AffineCurveBound :=
  affine_curve_count

end
end CCDN
