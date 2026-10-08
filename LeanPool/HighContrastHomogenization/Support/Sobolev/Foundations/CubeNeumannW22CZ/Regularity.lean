/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ArbitraryCubeEndpoint

/-!
# Coarse-graining support: Support.Sobolev.Foundations.CubeNeumannW22CZ.Regularity

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport

/-!
# Legacy positive-test Neumann compatibility package

This module packages the downstream positive-test endpoint for Neumann Poisson
solutions.  It does **not** state the manuscript's weak-Hessian
Calderon--Zygmund estimate; that literal statement lives in the exact
Euclidean-normalized lane.
-/

namespace Legacy

open scoped ENNReal

noncomputable section

/-- Legacy name for the downstream positive-test core estimate.  This is a
compatibility wrapper, not a weak-Hessian Calderon--Zygmund statement. -/
@[expose]
def CubeNeumannW22CalderonZygmundRegularity {d : ℕ}
    (Q : TriadicCube d) (C : ℝ) : Prop :=
  CubePoissonGradientDualTestNormL2CoreEstimate Q C

/-- Dimension-uniform legacy positive-test compatibility predicate on cubes. -/
@[expose]
def CubeNeumannW22CalderonZygmundRegularityInDimension
    (d : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ Q : TriadicCube d, CubeNeumannW22CalderonZygmundRegularity Q C

/-- Chosen dimension-only constant for the legacy positive-test compatibility
package, obtained from the reflected-parent depth and component-average
constants. -/
@[expose]
noncomputable def cubeNeumannW22CalderonZygmundConstant
    (d : ℕ) : ℝ :=
  originCubeWeakInteriorDepthConstantExact d 0 +
    (d : ℝ) * (originCubeMeanZeroH1CoerciveEstimate d 0).constantValue

theorem cubeNeumannW22CalderonZygmundConstant_nonneg
    (d : ℕ) :
    0 ≤ cubeNeumannW22CalderonZygmundConstant d := by
  exact add_nonneg
    (originCubeWeakInteriorDepthConstantExact_nonneg d 0)
    (mul_nonneg (Nat.cast_nonneg d)
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg)

/-- Selected legacy positive-test compatibility estimate on a cube. -/
theorem cubeNeumannW22CalderonZygmundRegularity
    {d : ℕ} (Q : TriadicCube d) :
    CubeNeumannW22CalderonZygmundRegularity Q
      (cubeNeumannW22CalderonZygmundConstant d) := by
  have hcore :=
    MeanZeroNeumannPoissonSolution.cubePoissonGradientDualTestNormL2CoreEstimate_cube Q
  have hdepth := cubeWeakInteriorDepthConstant_eq_dimensionConstant Q
  have havg := cubePoissonGradientAverageConstant_eq_dimensionConstant Q
  simpa [CubeNeumannW22CalderonZygmundRegularity,
    cubeNeumannW22CalderonZygmundConstant, hdepth, havg] using hcore

/-- The legacy positive-test compatibility package has the explicit constant
above in every dimension. -/
theorem exists_cubeNeumannW22CalderonZygmundRegularityInDimension
    (d : ℕ) :
    ∃ C : ℝ, CubeNeumannW22CalderonZygmundRegularityInDimension d C := by
  exact ⟨cubeNeumannW22CalderonZygmundConstant d,
    cubeNeumannW22CalderonZygmundConstant_nonneg d,
    cubeNeumannW22CalderonZygmundRegularity⟩

/-- Local existence form of the legacy positive-test compatibility input. -/
theorem exists_cubeNeumannW22CalderonZygmundRegularity
    {d : ℕ} (Q : TriadicCube d) :
    ∃ C : ℝ, CubeNeumannW22CalderonZygmundRegularity Q C :=
  ⟨cubeNeumannW22CalderonZygmundConstant d,
    cubeNeumannW22CalderonZygmundRegularity Q⟩

/-- Downstream positive-test core estimate from the legacy compatibility
package. -/
theorem exists_cubePoissonGradientDualTestNormL2CoreEstimate
    {d : ℕ} (Q : TriadicCube d) :
    ∃ C : ℝ, CubePoissonGradientDualTestNormL2CoreEstimate Q C := by
  exact
    ⟨cubeNeumannW22CalderonZygmundConstant d,
      cubeNeumannW22CalderonZygmundRegularity Q⟩

end

end Legacy

end HCPolySupport
