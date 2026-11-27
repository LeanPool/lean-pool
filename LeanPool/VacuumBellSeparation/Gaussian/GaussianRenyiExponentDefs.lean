/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.IntrinsicGaussianPerturbationDefs
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianRenyiParameters

/-!
# Literal Gaussian Renyi exponential coefficient

This construction is separated from its later specification proofs.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal Matrix.Norms.L2Operator

variable {m : ℕ}
  {ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
  {Vρ Vσ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

/-- Gaussian Rényi exponent. -/
noncomputable def gaussianRenyiExponent (ρ σ : MultiModeOscillatorSpace m →L[ℂ]
  MultiModeOscillatorSpace m)
    (r : ℝ) : ℝ :=
  2 * r * max 2 (gaussianRenyiTau r)⁻¹ *
    matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ (gaussianRenyiTau r))


end VacuumBellSeparation.Gaussian
