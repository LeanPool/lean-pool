/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusNegOne
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorRealRadiusNegOneScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Running-scale normalization for centered-cube negative-one norms

This module compares inverse-side-length normalizations on a centered cube of
real side length and its canonical enclosing triadic origin cube.  The only
analytic input is the quotient-safe centered-cube restriction estimate.
-/

namespace HCPolySupport
namespace HighContrast

open scoped ENNReal

noncomputable section

/-- The inverse-side-length normalized negative-one norm on a centered cube
of real side length. -/
@[expose]
noncomputable def realRadiusScaledNegOneNorm {d : ℕ} (R : ℝ)
    (F : HilbertVectorL2 (centeredOpenCube d R)) : ℝ≥0∞ :=
  ENNReal.ofReal R⁻¹ * localNegOneNorm (centeredOpenCube d R) F

/-- The inverse-side-length normalized negative-one norm on an origin cube
of integer triadic generation. -/
@[expose]
noncomputable def triadicScaledNegOneNorm {d : ℕ} (n : ℤ)
    (F : HilbertVectorL2 (openCubeSet (originCube d n))) : ℝ≥0∞ :=
  ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
    localNegOneNorm (openCubeSet (originCube d n)) F

end

end HighContrast
end HCPolySupport
