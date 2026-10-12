/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.State

/-!
# Kinetic energy

The nonnegative extended Fourier quadratic form with the physical kinetic normalization.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Nonnegative Fourier quadratic form with the physical minus-Laplacian normalization. -/
@[expose] noncomputable def kineticEnergy {N q : ℕ} (ψ : State N q) : ℝ≥0∞ :=
  ∫⁻ ξ : Configuration N,
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
      (‖(Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) ψ) ξ‖₊ : ℝ≥0∞) ^ 2

end LiebThirring

end
