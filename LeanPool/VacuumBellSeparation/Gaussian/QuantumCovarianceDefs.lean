/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WilliamsonFinite

/-!
# Literal complexification and physical quantum covariance

This construction is separated from its later specification proofs.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {ι κ : Type*}

/-- Complexify matrix obtained from `M.map`. -/
def complexifyMatrix (M : Matrix ι κ ℝ) : Matrix ι κ ℂ :=
  M.map (algebraMap ℝ ℂ)


@[simp] theorem complexifyMatrix_one [DecidableEq ι] :
    complexifyMatrix (1 : Matrix ι ι ℝ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [complexifyMatrix, Matrix.one_apply, h]

/-- Quantum covariance given by `complexifyMatrix V + (Complex.I / 2) • complexifyMatrix Ω`. -/
def quantumCovariance (V Ω : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  complexifyMatrix V + (Complex.I / 2) • complexifyMatrix Ω


end VacuumBellSeparation.Gaussian
