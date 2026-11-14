/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.Configuration
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Spin-valued quantum states

The spin and L² carriers are separated from spatial geometry so that electrostatic modules
do not import Fourier theory merely to use positions and configurations.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Assignments of one of the available spin labels to each particle. -/
@[expose] def SpinLabels (N q : ℕ) : Type :=
  Fin N → Fin q

attribute [reducible] SpinLabels

/-- Complex amplitudes for every spin assignment, with the Euclidean norm. -/
@[expose] def SpinAmplitudes (N q : ℕ) : Type :=
  EuclideanSpace ℂ (SpinLabels N q)

attribute [reducible] SpinAmplitudes

/-- Square-integrable spin-valued wavefunctions on the spatial configuration space. -/
@[expose] def State (N q : ℕ) : Type :=
  Lp (SpinAmplitudes N q) 2 (volume : Measure (Configuration N))

attribute [reducible] State

/-- Relabel spin assignments by the same particle permutation. -/
@[expose] def permuteSpins {N q : ℕ} (σ : Equiv.Perm (Fin N))
    (s : SpinLabels N q) : SpinLabels N q :=
  fun i => s (σ i)

end LiebThirring

end
