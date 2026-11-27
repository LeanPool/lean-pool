/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianCovarianceUniqueness
public import LeanPool.VacuumBellSeparation.Gaussian.RelativeCovarianceCongruence

/-!
# Actual normalized-power covariance increment and intrinsic perturbation

This construction is separated from its later specification proofs.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped Matrix.Norms.L2Operator

variable {m : ℕ}
variable {ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
variable {Vρ Vσ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

/-- Gaussian power increment defined as `normalizedGaussianPowerCovariance σ τ -
gaussianPhysicalCovariance σ`. -/
def gaussianPowerIncrement
    (σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) (τ : ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  normalizedGaussianPowerCovariance σ τ - gaussianPhysicalCovariance σ

/-- Intrinsic Gaussian relative perturbation. -/
def intrinsicGaussianRelativePerturbation
    (ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) (τ : ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  relativeCovariancePerturbation (gaussianPowerIncrement σ τ)
    (gaussianPhysicalCovariance ρ - gaussianPhysicalCovariance σ)


end VacuumBellSeparation.Gaussian
