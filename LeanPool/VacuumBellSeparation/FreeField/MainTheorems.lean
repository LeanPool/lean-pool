/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Section8EstimatesProof
public import LeanPool.VacuumBellSeparation.FreeField.Main

/-!
# The manuscript main theorem and fixed-region corollary

These theorems use the actual Section 8 estimates, the proved locality
and dilation, and the original physical vacuum Weyl model. Their statements
are `Theorem_1_1` and `Corollary_1_2` of `FreeField/Statements.lean`, retaining all
positive masses, radii, separation quantifiers and local observables.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Theorem 1.1: a mass- and radius-independent separation ratio. -/
theorem theorem_1_1 : Theorem_1_1 :=
  theorem_1_1_of_section8Estimates section8Estimates

/-- Corollary 1.2: arbitrary fixed bounded regions and spacelike direction. -/
theorem corollary_1_2 : Corollary_1_2 :=
  corollary_1_2_of_theorem_1_1 theorem_1_1

end VacuumBellSeparation
