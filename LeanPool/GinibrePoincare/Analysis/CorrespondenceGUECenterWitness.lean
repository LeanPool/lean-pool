/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUECenterWitness.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUECenterGaussian
/-!
# Correspondence GUE center witness

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueCenterCoordinate_contDiff`, `gueCenterCoordinate_memLp`,
`gueCenterCoordinate_gradient_memLp`, `gueCenterCoordinate_poincare_equality`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem gueCenterCoordinate_contDiff (n : ℕ) : ContDiff ℝ ∞ (gueCenterCoordinate n) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (gueCenterUnit n)).contDiff

theorem gueCenterCoordinate_memLp {n : ℕ} (hn : 0 < n) : MemLp (gueCenterCoordinate n) 2
    (gueFullMeasure n) := by
  exact (IsGaussian.memLp_id (gaussianReal 0 (gueCenterVariance n)) 2 (by
      finiteness)).comp_measurePreserving
    (gueCenterCoordinate_measurePreserving hn)

theorem gueCenterCoordinate_gradient (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (gueCenterCoordinate n) x=gueCenterUnit n := by
  unfold gradient
  change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (gueCenterUnit n))
        x)=gueCenterUnit n
  rw [ContinuousLinearMap.fderiv]
  simp

theorem gueCenterCoordinate_gradient_memLp {n : ℕ} (hn : 0 < n) :
    MemLp (gradient (gueCenterCoordinate n)) 2 (gueFullMeasure n) := by
  let := gueFullMeasure_probability hn
  have he : gradient (gueCenterCoordinate n)=fun _ => gueCenterUnit n := funext
      (gueCenterCoordinate_gradient n)
  rw [he]
  exact memLp_const (μ := gueFullMeasure n) (p := 2) (gueCenterUnit n)

theorem gueCenterCoordinate_poincare_equality {n : ℕ} (hn : 0 < n) :
    (∫x, gueCenterCoordinate n x^2 ∂gueFullMeasure n)-
      (∫x, gueCenterCoordinate n x ∂gueFullMeasure n)^2=
    (1/(n : ℝ))*(∫x, ‖gradient (gueCenterCoordinate n) x‖^2 ∂gueFullMeasure n) := by
  let := gueFullMeasure_probability hn
  rw [gueFullMeasure_center_gaussian_integral hn (fun t => t^2),
    gueFullMeasure_center_gaussian_integral hn (fun t => t)]
  simp only [integral_id_gaussianReal, zero_pow (by decide : 2≠0), sub_zero,
    gueCenterCoordinate_gradient, gueCenterUnit_norm hn, one_pow, integral_const, probReal_univ,
        smul_eq_mul, mul_one]
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := gueCenterVariance n)
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at hv
  simp only [integral_id_gaussianReal, sub_zero] at hv
  rw [show (gueCenterVariance n : ℝ)=(n : ℝ)⁻¹ from rfl] at hv
  simpa only [one_div] using hv

end
end GinibrePoincare
