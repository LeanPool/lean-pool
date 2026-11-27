/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianSandwichTraceRatio

/-!
# Literal statement construction extracted from Gaussian/GaussianAppendixA

The moved declarations retain their original text. Later target proofs remain separate.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
variable {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

/-- Gaussian relative perturbation defined as `normalizedPerturbation (CFC.sqrt
(thermalReferenceGap q τ)) (V - thermalReferenceCovariance q)`. -/
def gaussianRelativePerturbation (q : Fin m → ℝ) (τ : ℝ)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  normalizedPerturbation (CFC.sqrt (thermalReferenceGap q τ))
    (V - thermalReferenceCovariance q)


end VacuumBellSeparation.Gaussian
