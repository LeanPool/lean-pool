/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebMatrix.lean.
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
public import Mathlib.LinearAlgebra.Matrix.PosDef
/-!
# Correspondence Brascamp Lieb matrix

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_inverse_cauchy_schwarz`.
-/

@[expose] public section
open scoped Matrix BigOperators
namespace GinibrePoincare
noncomputable section

/-- The pointwise Hessian-inverse Cauchy–Schwarz estimate used in the genuine
Brascamp–Lieb inequality. Positive definiteness is a concrete matrix property. -/
theorem correspondenceBrascampLieb_inverse_cauchy_schwarz
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (hH : H.PosDef) (a b : ι → ℝ) :
    (a ⬝ᵥ b)^2≤(a ⬝ᵥ H⁻¹*ᵥa)*(b ⬝ᵥ H*ᵥb) := by
  have hc := hH.star_dotProduct_mulVec_mul_le (H⁻¹*ᵥa) b
  have hinv : H*(H⁻¹)=1 := Matrix.mul_nonsing_inv H (H.isUnit_iff_isUnit_det.mp hH.isUnit)
  have he : H*ᵥ(H⁻¹*ᵥa)=a := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hs : (H⁻¹*ᵥa) ⬝ᵥ (H*ᵥb)=a ⬝ᵥ b := by
    have hsym : H.transpose=H := by exact hH.isHermitian.isSymm
    rw [Matrix.dotProduct_mulVec]
    have hv : (H⁻¹ *ᵥ a) ᵥ* H = a := by
      calc
        (H⁻¹ *ᵥ a) ᵥ* H = (H⁻¹ *ᵥ a) ᵥ* H.transpose := by rw [hsym]
        _ = H *ᵥ (H⁻¹ *ᵥ a) := Matrix.vecMul_transpose _ _
        _ = a := he
    rw [hv]
  simpa only [star_trivial, he, hs, pow_two, dotProduct_comm] using hc

end
end GinibrePoincare
