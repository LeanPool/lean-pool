/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebAdjoint.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebJets
/-!
# Correspondence Brascamp Lieb adjoint

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_adjoint_integral`.
-/

@[expose] public section
open MeasureTheory Measure
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The formal adjoint of the directional derivative along `v` in `L²(exp (-W))`, applied to `f`:
`x ↦ ∂_v W x * f x - ∂_v f x`. -/
def correspondenceBrascampLiebAdjoint (W f : E → ℝ) (v : E) (x : E) : ℝ :=
  bakryEmeryGibbsDirectional W v x * f x - bakryEmeryGibbsDirectional f v x

theorem correspondenceBrascampLieb_adjoint_contDiff (W f : E → ℝ) (v : E)
    (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (correspondenceBrascampLiebAdjoint W f v) := by
  exact ((correspondenceBrascampLieb_direction_contDiff (m := 1) hW v).mul
    (hf.of_le (by norm_num))).sub
      (correspondenceBrascampLieb_direction_contDiff (m := 1) hf v)

theorem correspondenceBrascampLieb_adjoint_commutator
    (W f : E → ℝ) (v w : E) (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 2 f)
    (x : E) :
    bakryEmeryGibbsDirectional (correspondenceBrascampLiebAdjoint W f v) w x =
      correspondenceBrascampLiebAdjoint W (bakryEmeryGibbsDirectional f w) v x +
        bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w x * f x := by
  have hWv := correspondenceBrascampLieb_direction_contDiff (m := 1) hW v
  have hfv := correspondenceBrascampLieb_direction_contDiff (m := 1) hf v
  unfold correspondenceBrascampLiebAdjoint
  rw [correspondenceBrascampLieb_direction_sub
    (hWv.mul (hf.of_le (by norm_num))) hfv,
    correspondenceBrascampLieb_direction_mul hWv (hf.of_le (by norm_num))]
  rw [congrFun (correspondenceBrascampLieb_direction_commute hf v w) x]
  ring

variable [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

omit [CompleteSpace E] in
/-- Exact variable-Hessian weighted commutator identity for compact tests. -/
theorem correspondenceBrascampLieb_adjoint_integral
    (W f g : E → ℝ) (v w : E)
    (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x, correspondenceBrascampLiebAdjoint W f v x *
      correspondenceBrascampLiebAdjoint W g w x * bakryEmeryGibbsWeight W x) =
    (∫ x, bakryEmeryGibbsDirectional f w x * bakryEmeryGibbsDirectional g v x *
      bakryEmeryGibbsWeight W x) +
    ∫ x, bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w x *
      f x * g x * bakryEmeryGibbsWeight W x := by
  have hfw := correspondenceBrascampLieb_direction_contDiff (m := 1) hf w
  have hWv := correspondenceBrascampLieb_direction_contDiff (m := 1) hW v
  have hweight : Continuous (bakryEmeryGibbsWeight W) :=
    Real.continuous_exp.comp hW.continuous.neg
  have hH : Continuous (bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w) :=
    (hWv.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
  have hA := correspondenceBrascampLieb_adjoint_contDiff W f v hW hf
  have hA' : Continuous (correspondenceBrascampLiebAdjoint W
      (bakryEmeryGibbsDirectional f w) v) := by
    exact (((hW.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuous.clm_apply continuous_const |>.mul
        hfw.continuous).sub
          ((hfw.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const)
  have hiA : Integrable (fun x => correspondenceBrascampLiebAdjoint W
      (bakryEmeryGibbsDirectional f w) v x * g x * bakryEmeryGibbsWeight W x) :=
    ((hA'.mul hg.continuous).mul hweight).integrable_of_hasCompactSupport
      (hgc.mul_left.mul_right)
  have hiH : Integrable (fun x =>
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w x *
        f x * g x * bakryEmeryGibbsWeight W x) :=
    (((hH.mul hf.continuous).mul hg.continuous).mul hweight).integrable_of_hasCompactSupport
      (hgc.mul_left.mul_right)
  have h1 := bakryEmeryGibbs_directional_adjoint W
    (correspondenceBrascampLiebAdjoint W f v) g w
    (hW.of_le (by norm_num)) hA hg hgc
  have h2 := bakryEmeryGibbs_directional_adjoint W g
    (bakryEmeryGibbsDirectional f w) v (hW.of_le (by norm_num)) hg hfw
    (hfc.fderiv_apply ℝ w)
  change (∫ x, bakryEmeryGibbsDirectional (correspondenceBrascampLiebAdjoint W f v) w x *
    g x * bakryEmeryGibbsWeight W x) = _ at h1
  change (∫ x, bakryEmeryGibbsDirectional (correspondenceBrascampLiebAdjoint W f v) w x *
    g x * bakryEmeryGibbsWeight W x) =
    ∫ x, correspondenceBrascampLiebAdjoint W f v x *
      correspondenceBrascampLiebAdjoint W g w x * bakryEmeryGibbsWeight W x at h1
  rw [← h1]
  simp_rw [correspondenceBrascampLieb_adjoint_commutator W f v w hW hf]
  have hsplit : (∫ x, (correspondenceBrascampLiebAdjoint W
      (bakryEmeryGibbsDirectional f w) v x +
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w x * f x) *
      g x * bakryEmeryGibbsWeight W x) =
      (∫ x, correspondenceBrascampLiebAdjoint W (bakryEmeryGibbsDirectional f w) v x *
        g x * bakryEmeryGibbsWeight W x) +
      ∫ x, bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w x *
        f x * g x * bakryEmeryGibbsWeight W x := by
    simp_rw [add_mul]
    exact integral_add hiA hiH
  rw [hsplit]
  congr 1
  calc
    _ = ∫ x, g x * correspondenceBrascampLiebAdjoint W
        (bakryEmeryGibbsDirectional f w) v x * bakryEmeryGibbsWeight W x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = ∫ x, bakryEmeryGibbsDirectional g v x * bakryEmeryGibbsDirectional f w x *
        bakryEmeryGibbsWeight W x := h2.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring

end
end GinibrePoincare
