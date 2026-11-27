/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.BipartiteNormalStateDefs
public import LeanPool.VacuumBellSeparation.Bell.StateExtension
public import LeanPool.VacuumBellSeparation.FreeField.StrongContinuity
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
Tensor observables and positivity under partial transpose for two qubits.
`Bell/DistillationScaling.lean` uses them to prove the scaling and
positive-mass facts for two-qubit output functionals.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder CStarAlgebra

/-- Qubit algebra defined as `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
abbrev QubitAlgebra := CStarMatrix (Fin 2) (Fin 2) ℂ
/-- The algebra of complex matrices on the tensor product of two qubit spaces. -/
abbrev TwoQubitAlgebra := CStarMatrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The actual tensor matrix in the ordered product of the two standard bases. -/
def qubitTensor (X Y : QubitAlgebra) : TwoQubitAlgebra :=
  CStarMatrix.ofMatrix fun i j => X i.1 j.1 * Y i.2 j.2

/-- Transpose the first matrix factor, with no complex conjugation. -/
def partialTransposeLeft (Z : TwoQubitAlgebra) : TwoQubitAlgebra :=
  CStarMatrix.ofMatrix fun i j => Z (j.1, i.2) (i.1, j.2)

/-- Positivity of the partially transposed output functional, not of its input. -/
def TwoQubitPPT (τ : TwoQubitAlgebra →ₚ[ℂ] ℂ) : Prop :=
  ∀ Z : TwoQubitAlgebra, 0 ≤ Z → 0 ≤ τ (partialTransposeLeft Z)

end VacuumBellSeparation.Bipartite
