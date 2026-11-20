/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticProductBergman.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticBergmanComplex
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticL2TensorOperators

/-! # Concrete commuting Bergman coordinate projections
These operators act on the actual planar product Lebesgue L² space. -/

@[expose] public section
open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section

/-- The Hilbert space `L²(ℂ × ℂ)` for the product of two Lebesgue measures. -/
abbrev PlanarProductLebesgueL2 := Lp ℂ 2 ((volume : Measure ℂ).prod (volume : Measure ℂ))

/-- The planar Bergman projection acting in the left factor of `L²(ℂ × ℂ)`. -/
def planarLeftBergmanProjection (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) :
    PlanarProductLebesgueL2 →L[ℂ] PlanarProductLebesgueL2 :=
  l2ProductLeftOperator (planarBergmanProjection n V hV)

/-- The planar Bergman projection acting in the right factor of `L²(ℂ × ℂ)`. -/
def planarRightBergmanProjection (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) :
    PlanarProductLebesgueL2 →L[ℂ] PlanarProductLebesgueL2 :=
  l2ProductRightOperator (planarBergmanProjection n V hV)

theorem planarBergmanCoordinateProjections_commute (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) :
    (planarLeftBergmanProjection n V hV).comp (planarRightBergmanProjection n V hV) =
      (planarRightBergmanProjection n V hV).comp (planarLeftBergmanProjection n V hV) :=
  l2ProductLeftRight_commute _ _

theorem planarLeftBergmanProjection_adjoint (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) :
    (planarLeftBergmanProjection n V hV).adjoint = planarLeftBergmanProjection n V hV := by
  apply l2ProductLeftOperator_selfadjoint
  exact isSelfAdjoint_starProjection (planarBergmanKernelClosed n V hV).toSubmodule

theorem planarRightBergmanProjection_adjoint (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) :
    (planarRightBergmanProjection n V hV).adjoint = planarRightBergmanProjection n V hV := by
  apply l2ProductRightOperator_selfadjoint
  exact isSelfAdjoint_starProjection (planarBergmanKernelClosed n V hV).toSubmodule

theorem planarLeftBergmanProjection_idempotent (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) :
    (planarLeftBergmanProjection n V hV).comp (planarLeftBergmanProjection n V hV) =
      planarLeftBergmanProjection n V hV := by
  apply l2ProductLeftOperator_idempotent
  exact (planarBergmanKernelClosed n V hV).toSubmodule.isIdempotentElem_starProjection

theorem planarRightBergmanProjection_idempotent (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) :
    (planarRightBergmanProjection n V hV).comp (planarRightBergmanProjection n V hV) =
      planarRightBergmanProjection n V hV := by
  apply l2ProductRightOperator_idempotent
  exact (planarBergmanKernelClosed n V hV).toSubmodule.isIdempotentElem_starProjection

theorem planarLeftBergmanProjection_norm_le (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) : ‖planarLeftBergmanProjection n V hV‖ ≤ 1 :=
  (l2ProductLeftOperator_norm_le _).trans
    (planarBergmanKernelClosed n V hV).toSubmodule.starProjection_norm_le

theorem planarRightBergmanProjection_norm_le (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) : ‖planarRightBergmanProjection n V hV‖ ≤ 1 :=
  (l2ProductRightOperator_norm_le _).trans
    (planarBergmanKernelClosed n V hV).toSubmodule.starProjection_norm_le

/-- The concrete coordinate projection cannot increase the actual L² norm. -/
theorem planarLeftBergmanProjection_contracts (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) (F : PlanarProductLebesgueL2) :
    ‖planarLeftBergmanProjection n V hV F‖ ≤ ‖F‖ := by
  exact ((planarLeftBergmanProjection n V hV).le_opNorm F).trans
    ((mul_le_mul_of_nonneg_right (planarLeftBergmanProjection_norm_le n V hV)
      (norm_nonneg F)).trans_eq (one_mul _))

/-- Projecting both coordinates produces a vector fixed by both genuine
weighted Bergman coordinate projections. -/
theorem planarBergman_product_mem_coordinate_kernels (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) (F : PlanarProductLebesgueL2) :
    let G := planarLeftBergmanProjection n V hV (planarRightBergmanProjection n V hV F)
    planarLeftBergmanProjection n V hV G = G ∧
      planarRightBergmanProjection n V hV G = G := by
  dsimp
  constructor
  · exact congrArg (fun T : PlanarProductLebesgueL2 →L[ℂ] PlanarProductLebesgueL2 =>
      T (planarRightBergmanProjection n V hV F))
      (planarLeftBergmanProjection_idempotent n V hV)
  · have hc := congrArg (fun T : PlanarProductLebesgueL2 →L[ℂ] PlanarProductLebesgueL2 =>
      T (planarRightBergmanProjection n V hV F))
      (planarBergmanCoordinateProjections_commute n V hV)
    have hi := congrArg (fun T : PlanarProductLebesgueL2 →L[ℂ] PlanarProductLebesgueL2 => T F)
      (planarRightBergmanProjection_idempotent n V hV)
    simp only [ContinuousLinearMap.comp_apply] at hc hi
    rw [hi] at hc
    exact hc.symm

/-- Sharp tensorization of the concrete Bergman projection errors on the
whole product L² space. -/
theorem planarBergman_product_projection_error (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) (F : PlanarProductLebesgueL2) :
    ‖F - planarLeftBergmanProjection n V hV (planarRightBergmanProjection n V hV F)‖ ^ 2 ≤
      ‖F - planarLeftBergmanProjection n V hV F‖ ^ 2 +
        ‖F - planarRightBergmanProjection n V hV F‖ ^ 2 := by
  let P := planarLeftBergmanProjection n V hV
  let Q := planarRightBergmanProjection n V hV
  have hi : P (P F) = P F := congrArg (fun T : PlanarProductLebesgueL2 →L[ℂ] PlanarProductLebesgueL2
      => T F)
    (planarLeftBergmanProjection_idempotent n V hV)
  have hz : P (F - P F) = 0 := by rw [map_sub, hi, sub_self]
  have ho : ⟪F - P F, P (F - Q F)⟫_ℂ = 0 := by
    have ha : P.adjoint = P := planarLeftBergmanProjection_adjoint n V hV
    rw [← ha, ContinuousLinearMap.adjoint_inner_right]
    rw [ha]
    change ⟪P (F - P F), F - Q F⟫_ℂ = 0
    rw [hz, inner_zero_left]
  have he : F - P (Q F) = (F - P F) + P (F - Q F) := by
    rw [map_sub]
    abel
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (F - P F) (P (F - Q F)) ho
  have hb := planarLeftBergmanProjection_contracts n V hV (F - Q F)
  change ‖F - P (Q F)‖ ^ 2 ≤ _
  rw [he]
  have hn' : ‖(F - P F) + P (F - Q F)‖ ^ 2 = ‖F - P F‖ ^ 2 + ‖P (F - Q F)‖ ^ 2 := by
    simpa only [sq] using hn
  rw [hn']
  exact add_le_add (le_refl _) ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hb)

end
end GinibrePoincare
