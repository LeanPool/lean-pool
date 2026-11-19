/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurAngularDensity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurInjectiveIntegration
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Matrix Schur angular density

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchurAngularDensity_zero`, `measurable_matrixSchurAngularDensity`.
-/

@[expose] public section

open Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section

theorem matrixSchurExponentialFrame_fderiv_zero (n : ℕ) :
    fderiv ℝ (matrixSchurExponentialFrame n) 0 = schurSkewCLM n := by
  let M := Matrix (Fin n) (Fin n) ℂ
  have he : HasFDerivAt (exp : M → M) (1 : M →L[ℝ] M) 0 := hasFDerivAt_exp_zero
  have hz : schurSkewCLM n 0 = 0 := map_zero _
  rw [← hz] at he
  have hc := he.comp (0 : SchurLowerIndex n → ℂ) (schurSkewCLM n).hasFDerivAt
  have hf : matrixSchurExponentialFrame n = exp ∘ ⇑(schurSkewCLM n) := by
    funext x
    rw [Function.comp_apply, schurSkewCLM_apply]
    rfl
  rw [hf]
  exact hc.fderiv

theorem matrixSchurAngularDensity_zero (n : ℕ) : matrixSchurAngularDensity n 0 = 1 := by
  have hQ : matrixSchurExponentialFrame n 0 = 1 := by
    simp [matrixSchurExponentialFrame, ← schurSkewCLM_apply, exp_zero]
  have hJ : (matrixLowerRead n).comp (matrixUnitaryConnection (matrixSchurExponentialFrame n 0)
      (fderiv ℝ (matrixSchurExponentialFrame n) 0)) =
      ContinuousLinearMap.id ℝ (SchurLowerIndex n → ℂ) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [ContinuousLinearMap.comp_apply, matrixUnitaryConnection_apply, hQ,
      Matrix.conjTranspose_one, Matrix.one_mul, matrixSchurExponentialFrame_fderiv_zero,
      schurSkewCLM_apply, matrixLowerRead_skew]
    rfl
  rw [matrixSchurAngularDensity, hJ]
  simp

theorem measurable_matrixSchurAngularDensity (n : ℕ) :
    Measurable (matrixSchurAngularDensity n) := by
  have hf : matrixSchurExponentialFrame n = exp ∘ ⇑(schurSkewCLM n) := by
    funext x
    rw [Function.comp_apply, schurSkewCLM_apply]
    rfl
  have hc : ContDiff ℝ 1 (matrixSchurExponentialFrame n) := by
    rw [hf]
    exact (AnalyticOnNhd.contDiff fun A _ => exp_analytic (𝕂 := ℝ) A).comp
      (schurSkewCLM n).contDiff
  have hDc := hc.continuous_fderiv one_ne_zero
  have hQc := hc.continuous
  apply Continuous.measurable
  unfold matrixSchurAngularDensity
  refine continuous_abs.comp (ContinuousLinearMap.continuous_det.comp ?_)
  unfold matrixUnitaryConnection
  fun_prop

end
end GinibrePoincare
