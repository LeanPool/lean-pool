/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixUnitaryDerivative.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSkewCoordinates
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Matrix unitary derivative

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixUnitary_left_derivative_skew`.
-/

@[expose] public section

open Matrix Filter
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

/-- Differentiating actual unitary paths yields a skew-Hermitian left logarithmic derivative. -/
theorem matrixUnitary_left_derivative_skew {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {Q : E → Matrix (Fin n) (Fin n) ℂ} {D : E →L[ℝ] Matrix (Fin n) (Fin n) ℂ}
    {x : E} (hQ : HasFDerivAt Q D x)
    (hunit : ∀ᶠ y in 𝓝 x, Q y ∈ Matrix.unitaryGroup (Fin n) ℂ) (v : E) :
    ((Q x)ᴴ * D v)ᴴ = -((Q x)ᴴ * D v) := by
  let A := schurConjTransposeCLM n
  have hs := A.hasFDerivAt.comp x hQ
  have hp := hs.mul' hQ
  have hevent : (fun y => A (Q y) * Q y) =ᶠ[𝓝 x] (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    filter_upwards [hunit] with y hy
    exact Matrix.mem_unitaryGroup_iff'.mp hy
  have hc := (hasFDerivAt_const (𝕜 := ℝ) (1 : Matrix (Fin n) (Fin n) ℂ) x).congr_of_eventuallyEq
    hevent
  have he := hp.unique hc
  have hv := congrArg (fun L : E →L[ℝ] Matrix (Fin n) (Fin n) ℂ => L v) he
  have hz : (Q x)ᴴ * D v + (D v)ᴴ * Q x = 0 := hv
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hz)

end
end GinibrePoincare
