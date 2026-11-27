/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LiteralFockVacuumConstruction
public import LeanPool.VacuumBellSeparation.Fock.PhysicalTestTotality
public import LeanPool.VacuumBellSeparation.FreeField.Uniqueness

/-!
# The original free-field vacuum on the literal symmetric Fock space

The carrier is the actual Hilbert sum of symmetric Hilbert tensor powers
of the original mass-shell L2 space. Compact spacetime test cyclicity is
proved using the actual wedge source space. Every previously specified
vacuum Weyl system is genuinely unitarily equivalent, preserving all
original local algebras and vacuum expectations.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory Fock
open scoped InnerProductSpace

-- Use the exact completed carrier instance already sealed by the constructor.
attribute [local instance] literalFockConstructionComplete

variable {m : ℝ} (hm : 0 < m)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The unitary identifies the original labels, every original regional
algebra, and every bounded vacuum expectation on the full Hilbert space. -/
theorem FreeFieldVacuum.exists_literalFock_equiv (V : FreeFieldVacuum m H) :
    ∃ U : H ≃ₗᵢ[ℂ] LiteralFockSpace (m := m),
      U V.vacuum = literalFockVacuumVector ∧
      (∀ F x, U (V.weyl F x) = fockWeyl _ (oneParticleL2 hm F) (U x)) ∧
      (∀ (O : Set Spacetime) (A : H →L[ℂ] H),
        A ∈ localAlgebra V O ↔ U.conjStarAlgEquiv A ∈ localAlgebra (literalFockVacuum hm) O) ∧
      (∀ A : H →L[ℂ] H,
        vectorState (literalFockVacuum hm).vacuum (literalFockVacuum hm).vacuum_norm
          (U.conjStarAlgEquiv A) = vectorState V.vacuum V.vacuum_norm A) := by
  obtain ⟨U, hΩ, hU⟩ := FreeFieldVacuum.exists_unitary_equiv
    (H := H) (H' := LiteralFockSpace (m := m)) V (literalFockVacuum hm)
  refine ⟨U, hΩ, hU, ?_, ?_⟩
  · intro O A
    exact V.mem_localAlgebra_iff_of_conj (literalFockVacuum hm) U hU O A
  · intro A
    exact V.vectorState_conj (literalFockVacuum hm) U hΩ A

end VacuumBellSeparation
