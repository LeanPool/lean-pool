/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Analysis.FundamentalSolutionMeasures
import LeanPool.LiebThirring.Analysis.FundamentalSolutionApproximation
import LeanPool.LiebThirring.Analysis.FundamentalSolutionLimits

/-!
# The three-dimensional Coulomb fundamental solution

The Coulomb fundamental-solution identity, the fundamental solution. Together with
`integrable_inv_norm_sub_mul_laplacian`, this asserts absolute integrability and the value of
the pairing. `C²` suffices, so in particular the identity holds for every smooth compactly
supported test.

A finite positive charge with bounded extended potential satisfies the test-function identity
the fundamental solution. Local integrability is supplied by
`locallyIntegrable_coulombPotential_toReal`, and absolute test-pairing integrability by
`integrable_coulombPotential_toReal_mul_laplacian`.
-/

public section

open MeasureTheory Filter InnerProductSpace Laplacian
open scoped Topology ENNReal

namespace LiebThirring

/-- The Coulomb fundamental-solution identity, the fundamental solution.
Together with `integrable_inv_norm_sub_mul_laplacian`, this asserts absolute
integrability and the value of the pairing. `C²` suffices, so in particular
the identity holds for every smooth compactly supported test. -/
theorem integral_inv_norm_sub_mul_laplacian {f : Position → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (y : Position) :
    (∫ x, ‖x - y‖⁻¹ * Δ f x) = -4 * Real.pi * f y := by
  have hleft := tendsto_integral_regularizedCoulombKernel_sub_mul_laplacian hf hfc y
  have hright := (tendsto_integral_coulombApproximationDensity_sub_mul
    hf.continuous hfc y).neg
  have ht : Tendsto (fun ε : ℝ => ∫ x, regularizedCoulombKernel ε (x - y) * Δ f x)
      (𝓝[>] 0) (𝓝 (-4 * Real.pi * f y)) := by
    have h := hright.congr' (by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact (integral_regularizedCoulombKernel_sub_mul_laplacian hε hf hfc y).symm)
    simpa only [neg_mul] using h
  exact tendsto_nhds_unique hleft ht

/-- A finite positive charge with bounded extended potential satisfies
the test-function identity the fundamental solution. Local integrability is supplied by
`locallyIntegrable_coulombPotential_toReal`, and absolute test-pairing
integrability by `integrable_coulombPotential_toReal_mul_laplacian`. -/
theorem integral_coulombPotential_toReal_mul_laplacian
    (β : Measure Position) [IsFiniteMeasure β] {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hβ : ∀ x, coulombPotential β x ≤ C)
    {f : Position → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x, (coulombPotential β x).toReal * Δ f x) = -4 * Real.pi * ∫ y, f y ∂β := by
  rw [integral_coulombPotential_toReal_mul_laplacian_eq_integral_integral β hC hβ hf hfc]
  simp_rw [integral_inv_norm_sub_mul_laplacian hf hfc]
  exact integral_const_mul _ _

end LiebThirring

end
