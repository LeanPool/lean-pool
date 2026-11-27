/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PhysicalGaussianTransport
public import LeanPool.VacuumBellSeparation.Gaussian.UnitarySandwich
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianAppendixA

/-!
# Literal statement construction extracted from Gaussian/GaussianWilliamsonSandwich

The moved declarations retain their original text. Later target proofs remain separate.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ}

/-- Williamson sandwich covariance. -/
def williamsonSandwichCovariance (q : Fin m → ℝ) (τ : ℝ)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  let T := modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ));
  -T + CFC.sqrt (T ^ 2 - (1 / 4 : ℝ) • 1) * (T - V)⁻¹ *
    CFC.sqrt (T ^ 2 - (1 / 4 : ℝ) • 1)


end VacuumBellSeparation.Gaussian
