/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCurvatureLinear.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCurvatureDeficit
public import LeanPool.GinibrePoincare.Analysis.GinibrePointwiseCurvature
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
/-!
# Correspondence curvature linear

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceImaginaryCoordinate_gradient`,
`correspondenceImaginaryCoordinate_HessianSquare`.
-/

@[expose] public section
open Set Filter
open scoped ContDiff BigOperators ComplexConjugate Topology
namespace GinibrePoincare
noncomputable section

/-- The real-linear coordinate functional `z ↦ (z j).im` on configurations. -/
def correspondenceImaginaryCoordinate {n : ℕ} (j : Fin n) : Configuration n →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.proj j)

theorem correspondenceImaginaryCoordinate_gradient {n : ℕ} (j : Fin n) (z : Configuration n) :
    ginibreBochnerGradient (correspondenceImaginaryCoordinate j) z = imaginaryCoordinateDirection j
        := by
  ext i
  rw [correspondenceBochnerGradient_coordinate]
  unfold bochnerDirectionalDerivative
  rw [(correspondenceImaginaryCoordinate j).fderiv]
  by_cases hij : i=j
  · subst i
    simp [correspondenceImaginaryCoordinate, realCoordinateDirection, imaginaryCoordinateDirection,
        coordinateDirection]
  · simp [hij, Ne.symm hij, correspondenceImaginaryCoordinate, realCoordinateDirection,
      imaginaryCoordinateDirection,
    coordinateDirection]

theorem correspondenceImaginaryCoordinate_hessian {n : ℕ} (j : Fin n) (z : Configuration n) :
    fderiv ℝ (fderiv ℝ (correspondenceImaginaryCoordinate j)) z = 0 := by
  have he : fderiv ℝ (correspondenceImaginaryCoordinate j) =
      fun _ => correspondenceImaginaryCoordinate j := by
    funext x
    exact (correspondenceImaginaryCoordinate j).fderiv
  rw [he]
  exact congrFun (fderiv_const (𝕜 := ℝ) (E := Configuration n) (correspondenceImaginaryCoordinate
      j)) z

theorem correspondenceImaginaryCoordinate_HessianSquare {n : ℕ} (j : Fin n) (z : Configuration n) :
    ginibreBochnerHessianSquare (correspondenceImaginaryCoordinate j) z = 0 := by
  simp [ginibreBochnerHessianSquare, correspondenceImaginaryCoordinate_hessian]

end
end GinibrePoincare
