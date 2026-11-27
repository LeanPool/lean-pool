/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroDefs

/-!
# Statement seed extracted from FreeField/TimeZeroDilation

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

/-- Spatial rescaling with explicit amplitude; the nonzero scale preserves compact support. -/
noncomputable def spatialScale (R : ℝ) (hR : R ≠ 0) (a : ℝ)
    (f : SpatialTestFunction) : SpatialTestFunction :=
  ⟨fun x => a * f.1 (R • x),
    contDiff_const.mul (f.2.1.comp (contDiff_const_smul R)),
    (f.2.2.comp_smul hR).mul_left⟩

/-- Exactly the pair transformation (2.5), without a spacetime substitution. -/
noncomputable def timeZeroDilate (R : ℝ) (hR : R ≠ 0) (u : TimeZeroSource) : TimeZeroSource :=
  (spatialScale R hR (R ^ 2) u.1, spatialScale R hR R u.2)

/-- The position-space symplectic form (2.1). -/
noncomputable def timeZeroSymplectic (u v : TimeZeroSource) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin 3), u.1.1 x * v.2.1 x - u.2.1 x * v.1.1 x


end VacuumBellSeparation
