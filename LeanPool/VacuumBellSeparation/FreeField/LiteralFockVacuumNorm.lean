/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LiteralFockVacuumDefs

/-!
# Norm of the actual literal Fock vacuum vector

This construction is separated from its later specification proofs.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory Fock
open scoped InnerProductSpace

variable {m : ℝ} (hm : 0 < m)

theorem literalFockVacuumVector_norm : ‖literalFockVacuumVector (m := m)‖ = 1 := by
  rw [literalFockVacuumVector, ← weylFockEquiv_weylVec, LinearIsometryEquiv.norm_map]
  exact norm_weylVec_zero _ (fun _ _ => rfl)


end VacuumBellSeparation
