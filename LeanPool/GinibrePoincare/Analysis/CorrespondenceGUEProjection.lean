/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEProjection.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUERealMeasure
/-!
# Correspondence GUE projection

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueRealProjectionLinear_apply`, `gueRealProjection_contDiff`,
`gueRealProjection_gradient_norm_sq`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- `gueRealProjection n` as a continuous linear map. -/
def gueRealProjectionLinear (n : ℕ) :
    EuclideanSpace ℝ (Fin n×Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ((WithLp.linearEquiv 2 ℝ (Fin n→ℝ)).symm.toLinearMap.comp
    (LinearMap.pi (fun i => (PiLp.proj 2 (fun _ : Fin n×Fin 2 => ℝ) (i,
        0)).toLinearMap))).toContinuousLinearMap

theorem gueRealProjectionLinear_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    gueRealProjectionLinear n x=gueRealProjection n x := rfl

theorem gueRealProjection_contDiff (n : ℕ) : ContDiff ℝ ∞ (gueRealProjection n) :=
  (gueRealProjectionLinear n).contDiff

theorem gue_gradient_coordinate {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    (gradient f x) i=fderiv ℝ f x (EuclideanSpace.basisFun ι ℝ i) := by
  classical
  rw [← toDual_gradient]
  simp only [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_basisFun_real]

theorem gueRealProjection_basis_real (n : ℕ) (i : Fin n) :
    gueRealProjectionLinear n (EuclideanSpace.basisFun (Fin n×Fin 2) ℝ (i, 0))=
      EuclideanSpace.basisFun (Fin n) ℝ i := by
  ext j
  simp [gueRealProjectionLinear, EuclideanSpace.basisFun_apply, PiLp.single_apply]

theorem gueRealProjection_basis_aux (n : ℕ) (i : Fin n) :
    gueRealProjectionLinear n (EuclideanSpace.basisFun (Fin n×Fin 2) ℝ (i, 1))=0 := by
  ext j
  simp [gueRealProjectionLinear, EuclideanSpace.basisFun_apply]

theorem gueRealProjection_gradient_norm_sq (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    ‖gradient (f ∘ gueRealProjection n) x‖^2=‖gradient f (gueRealProjection n x)‖^2 := by
  have hd := (hf.differentiable (by norm_num) (gueRealProjection n x)).hasFDerivAt.comp x
    (gueRealProjectionLinear n).hasFDerivAt
  have he : fderiv ℝ (f ∘ gueRealProjection n) x =
      (fderiv ℝ f (gueRealProjection n x)).comp (gueRealProjectionLinear n) := hd.fderiv
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, gue_gradient_coordinate, he, ContinuousLinearMap.comp_apply,
    gueRealProjection_basis_real, gueRealProjection_basis_aux, map_zero, zero_pow (by decide : 2≠0),
        add_zero]

end
end GinibrePoincare
