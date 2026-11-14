/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Data.Fin.Basic

/-!
# Spatial particle configurations

Euclidean spatial configurations, coordinate insertion and particle permutations.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Three-dimensional Euclidean physical space. -/
@[expose] def Position : Type :=
  EuclideanSpace ℝ (Fin 3)

attribute [reducible] Position

/-- Euclidean spatial coordinates of all particles. -/
@[expose] def Configuration (N : ℕ) : Type :=
  EuclideanSpace ℝ (Fin N × Fin 3)

attribute [reducible] Configuration

/-- The spatial position of the selected particle. -/
@[expose] def particlePosition {N : ℕ} (x : Configuration N) (i : Fin N) : Position :=
  toLp 2 (fun a => x (i, a))

/-- Relabel the spatial coordinates by a permutation of the particles. -/
@[expose] def permutePositions {N : ℕ} (σ : Equiv.Perm (Fin N))
    (x : Configuration N) : Configuration N :=
  toLp 2 (fun ia => x (σ ia.1, ia.2))

/-- Spatial coordinates of the particles other than the selected particle. -/
@[expose] def OtherConfiguration {N : ℕ} (i : Fin N) : Type :=
  EuclideanSpace ℝ ({j : Fin N // j ≠ i} × Fin 3)

attribute [reducible] OtherConfiguration

/-- Fill the selected spatial coordinate while retaining all other particle coordinates. -/
@[expose] def insertParticle {N : ℕ} (i : Fin N) (x : Position)
    (y : OtherConfiguration i) : Configuration N :=
  toLp 2 (fun ja => if h : ja.1 = i then x ja.2 else y (⟨ja.1, h⟩, ja.2))

end LiebThirring

end
