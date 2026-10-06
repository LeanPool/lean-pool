/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.Concentration
public import LeanPool.HighContrastHomogenization.Support.Geometry.ScaleColoring

/-!
# Coarse-graining support: Support.Book.Ch04.PartitionAverageConstants

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Coefficient-free constants for Chapter 4 partition averages

This module owns the numerical scales and color-count constants shared by the
partition-average and descendant-average concentration APIs.
-/

namespace HCPolySupport.Book.Ch04

noncomputable section

/-- Cardinal square-root fluctuation scale of a triadic partition. -/
@[expose]
noncomputable def partitionCardinalityScale {d : ℕ} (n m : ℤ) : ℝ :=
  Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) /
    ((descendantsAtScale (originCube d m) n).card : ℝ)

/-- Explicit color-count constant for descendant averages with `Gamma_sigma`
tails. -/
@[expose]
noncomputable def gammaSigmaDescendantsAtScaleConst (d : ℕ) (k : ℤ) (σ : ℝ) : ℝ :=
  gammaTriangleConst σ * gammaSigmaIndependentSumConst σ *
    Real.sqrt ((((scaleColorPeriod k) ^ d : ℕ) : ℝ))

/-- Explicit color-count constant for descendant averages with `Psi_sigma`
tails. -/
@[expose]
noncomputable def psiSigmaDescendantsAtScaleConst (d : ℕ) (k : ℤ) (σ : ℝ) : ℝ :=
  psiSigmaTriangleConst σ * psiSigmaIndependentSumConst σ *
    Real.sqrt ((((scaleColorPeriod k) ^ d : ℕ) : ℝ))

/-- Explicit color-count constant multiplying the real-exponent `L^p`
Rosenthal term in a descendant-average bound. -/
@[expose]
noncomputable def rosenthalDescendantsAtScaleRpowLpConst
    (d : ℕ) (k : ℤ) (p : ℝ) : ℝ :=
  2 * p * ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) ^ (1 - 1 / p)

/-- Explicit color-count constant multiplying the square-function term in a
real-exponent Rosenthal descendant-average bound. -/
@[expose]
noncomputable def rosenthalDescendantsAtScaleRpowSqrtConst
    (d : ℕ) (k : ℤ) (p : ℝ) : ℝ :=
  4 * rosenthalBennettIntegralConst *
    (Real.sqrt p * Real.sqrt ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)))

end

end HCPolySupport.Book.Ch04
