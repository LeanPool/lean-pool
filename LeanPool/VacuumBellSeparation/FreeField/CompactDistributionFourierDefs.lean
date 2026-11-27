/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CutoffFourierKernel

/-! # Fourier transform of a compactly supported distribution -/

@[expose] public section

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform InnerProductSpace Topology

namespace VacuumBellSeparation

/-- Compact distribution Fourier defined as `T (cutoffFourierKernel χ p)`. -/
noncomputable def compactDistributionFourier
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ := T (cutoffFourierKernel χ p)

end VacuumBellSeparation
