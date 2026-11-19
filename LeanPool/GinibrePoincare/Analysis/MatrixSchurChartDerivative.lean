/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurChartDerivative.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurJacobian
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Instances.Matrix

/-!
# Matrix Schur chart derivative

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `schurAmbientChart_skew_unitary`, `schurAmbientChart_fderiv_lowerBlock`.
-/

@[expose] public section

open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section

/-- The ambient chart `(K, Y) ↦ exp K (T + Y) exp (-K)` around the matrix `T`. -/
def schurAmbientChart {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := exp p.1 * (T + p.2) * exp (-p.1)

theorem schurAmbientChart_fderiv {n : ℕ} (T K H : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℝ (schurAmbientChart T) (0, 0) (K, H) = K * T - T * K + H := by
  let M := Matrix (Fin n) (Fin n) ℂ
  have hfst : HasFDerivAt (Prod.fst : M × M → M) (ContinuousLinearMap.fst ℝ M M) (0, 0) :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : M × M → M) (ContinuousLinearMap.snd ℝ M M) (0, 0) :=
    hasFDerivAt_snd
  have hexp : HasFDerivAt (exp : M → M) (1 : M →L[ℝ] M) 0 := hasFDerivAt_exp_zero
  have hL := hexp.comp ((0, 0) : M × M) hfst
  have hx : (-Prod.fst) ((0, 0) : M × M) = 0 := by simp
  rw [← hx] at hexp
  have hR := hexp.comp ((0, 0) : M × M) hfst.neg
  have hM := (hasFDerivAt_const T ((0, 0) : M × M)).add hsnd
  have hd := (hL.mul' hM).mul' hR
  unfold schurAmbientChart
  rw [show fderiv ℝ (fun p : M × M => exp p.1 * (T + p.2) * exp (-p.1)) (0, 0) = _ from
    hd.fderiv]
  simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, Pi.neg_apply, neg_zero, exp_zero,
    one_mul, add_zero]
  change (T • (1 : M →L[ℝ] M).comp (-ContinuousLinearMap.fst ℝ M M) + MulOpposite.op (1 : M) •
    ((1 : M) • (0 + ContinuousLinearMap.snd ℝ M M) +
      MulOpposite.op T • (1 : M →L[ℝ] M).comp (ContinuousLinearMap.fst ℝ M M))) (K, H) = _
  simp only [ContinuousLinearMap.comp_neg, smul_neg, MulOpposite.op_one, zero_add, one_smul,
    smul_add, _root_.add_apply, _root_.neg_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', one_apply_eq_self, smul_eq_mul,
    ContinuousLinearMap.coe_snd', MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  abel

theorem schurAmbientChart_skew_unitary {n : ℕ} (T H : Matrix (Fin n) (Fin n) ℂ)
    (x : SchurLowerIndex n → ℂ) :
    exp (schurSkewCombination x) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      schurAmbientChart T (schurSkewCombination x, H) =
        exp (schurSkewCombination x) * (T + H) * (exp (schurSkewCombination x))ᴴ := by
  have hskew : schurSkewCombination x ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
    skewAdjoint.mem_iff.mpr (schurSkewCombination_conjTranspose x)
  refine ⟨@exp_mem_unitary_of_mem_skewAdjoint (Matrix (Fin n) (Fin n) ℂ) _ _ _ _
    ⟨Continuous.matrix_conjTranspose continuous_id⟩ _ hskew, ?_⟩
  unfold schurAmbientChart
  rw [← Matrix.exp_conjTranspose, schurSkewCombination_conjTranspose]

/-- The previously computed Vandermonde block occurs in the actual real chart derivative
for skew-Hermitian lower coordinates and upper-triangular perturbations. -/
theorem schurAmbientChart_fderiv_lowerBlock {n : ℕ} (T H : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hH : ∀ i j, j < i → H i j = 0)
    (x : SchurLowerIndex n → ℂ) (p : SchurLowerIndex n) :
    fderiv ℝ (schurAmbientChart T) (0, 0) (schurSkewCombination x, H)
      (schurLowerRow p) (schurLowerCol p) = (schurLowerJacobian T *ᵥ x) p := by
  rw [schurAmbientChart_fderiv, Matrix.add_apply]
  have hz : H (schurLowerRow p) (schurLowerCol p) = 0 := hH _ _ p.property
  rw [hz, add_zero]
  exact (schurLowerJacobian_skew_commutator T hT x p).symm

end
end GinibrePoincare
