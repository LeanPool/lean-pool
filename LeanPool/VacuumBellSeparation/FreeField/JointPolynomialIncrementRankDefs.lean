/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialIncrementNorm
public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialCombinedRange

/-!
# Literal statement construction extracted from FreeField/JointPolynomialIncrementNuclear

The moved declarations retain their original text. Later target proofs remain separate.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian Gaussian.HilbertComplexification

/-- Joint polynomial increment rank given by `2 * (9 * (n + 1) + 1) ^ 3`. -/
def jointPolynomialIncrementRank (n : ℕ) : ℕ := 2 * (9 * (n + 1) + 1) ^ 3


end VacuumBellSeparation
