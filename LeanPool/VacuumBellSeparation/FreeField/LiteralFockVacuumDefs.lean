/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Fock.WeylFockEquivalence
public import LeanPool.VacuumBellSeparation.FreeField.Existence

/-!
# Literal symmetric Fock carrier and original vacuum vector

This construction is separated from its later specification proofs.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory Fock
open scoped InnerProductSpace

variable {m : ℝ} (hm : 0 < m)

/-- Literal Fock space with underlying type `SymmetricFockSpace (Lp ℂ 2 (oneParticleMeasure m))`. -/
abbrev LiteralFockSpace := SymmetricFockSpace (Lp ℂ 2 (oneParticleMeasure m))

/-- Literal Fock vacuum vector. -/
def literalFockVacuumVector : LiteralFockSpace (m := m) :=
  coherentVector (Lp ℂ 2 (oneParticleMeasure m)) 0


end VacuumBellSeparation
