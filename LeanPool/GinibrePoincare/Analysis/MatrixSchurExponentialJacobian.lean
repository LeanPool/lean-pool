/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurExponentialJacobian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurFrameJacobian
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Matrix Schur exponential jacobian

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchurAngularDensity_nonneg`, `matrixSchurExponentialJacobian`.
-/

@[expose] public section

open Matrix NormedSpace Filter
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

/-- The actual lower skew exponential section of the unitary group. -/
def matrixSchurExponentialFrame (n : ℕ) (x : SchurLowerIndex n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := exp (schurSkewCombination x)

theorem matrixSchurExponentialFrame_unitary (n : ℕ) (x : SchurLowerIndex n → ℂ) :
    matrixSchurExponentialFrame n x ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  (schurAmbientChart_skew_unitary (0 : Matrix (Fin n) (Fin n) ℂ) 0 x).1

theorem matrixSchurExponentialFrame_differentiable (n : ℕ) :
    Differentiable ℝ (matrixSchurExponentialFrame n) := by
  intro x
  have he := (exp_analytic (𝕂 := ℝ) (schurSkewCombination x)).differentiableAt
  have hs := (schurSkewCLM n).differentiableAt (x := x)
  rw [← schurSkewCLM_apply] at he
  have hf : matrixSchurExponentialFrame n = exp ∘ ⇑(schurSkewCLM n) := by
    funext z
    rw [Function.comp_apply, schurSkewCLM_apply]
    rfl
  rw [hf]
  exact he.comp x hs

/-- The angular density is defined from the derivative of the actual unitary section,
independently of all eigenvalues and strict upper entries. -/
def matrixSchurAngularDensity (n : ℕ) (x : SchurLowerIndex n → ℂ) : ℝ :=
  |(((matrixLowerRead n).comp (matrixUnitaryConnection (matrixSchurExponentialFrame n x)
    (fderiv ℝ (matrixSchurExponentialFrame n) x))).toLinearMap).det|

theorem matrixSchurAngularDensity_nonneg (n : ℕ) (x : SchurLowerIndex n → ℂ) :
    0 ≤ matrixSchurAngularDensity n x := abs_nonneg _

/-- The Schur Jacobian factorization for the concrete exponential chart at every point. -/
theorem matrixSchurExponentialJacobian {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (x : SchurLowerIndex n → ℂ) (y : SchurUpperIndex n → ℂ) :
    |(schurEntryCoordinates.comp
        (fderiv ℝ (matrixSchurFrameChart (matrixSchurExponentialFrame n) T) (x,
            y)).toLinearMap).det| =
      vandermondeWeight (fun i => (T + schurUpperCombination y) i i) *
        matrixSchurAngularDensity n x := by
  apply matrixSchurFrame_entry_fderiv_abs_det
  · exact hT
  · exact (matrixSchurExponentialFrame_differentiable n x).hasFDerivAt
  · exact Filter.Eventually.of_forall (matrixSchurExponentialFrame_unitary n)

end
end GinibrePoincare
