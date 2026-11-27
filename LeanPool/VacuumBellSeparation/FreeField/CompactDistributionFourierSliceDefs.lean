/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CompactDistributionFourierDefs
public import LeanPool.VacuumBellSeparation.FreeField.CompactDistributionEntire

/-! # Entire Fourier slices of compactly supported distributions -/

@[expose] public section

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform InnerProductSpace Topology

namespace VacuumBellSeparation

theorem hasCompactSupport_cutoffFourierKernel
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ)
    (p : EuclideanSpace ℝ (Fin 3)) : HasCompactSupport (cutoffFourierKernel χ p) :=
  hχ.of_isClosed_subset isClosed_closure (tsupport_cutoffFourierKernel_subset χ p)

/-- An actual entire extension of each affine real-frequency slice. -/
noncomputable def compactDistributionFourierSlice
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ)
    (p a : EuclideanSpace ℝ (Fin 3)) (z : ℂ) : ℂ :=
  T (spatialSchwartzExponential (innerSL ℝ a) (cutoffFourierKernel χ p)
    (hasCompactSupport_cutoffFourierKernel χ hχ p) (-(2 * Real.pi : ℂ) * Complex.I * z))

end VacuumBellSeparation
