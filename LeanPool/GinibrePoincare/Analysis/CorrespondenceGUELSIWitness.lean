/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUELSIWitness.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUECenterWitness
/-!
# Correspondence GUELSI witness

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueLSIWitness_lsi_equality`, `gueLSIWitness_memLp`, `gueLSIWitness_gradient_memLp`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- The test function `x ↦ exp (gueCenterCoordinate n x / 2)`. -/
def gueLSIWitness (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (gueCenterCoordinate n x/2)

theorem gueLSIWitness_square (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gueLSIWitness n x^2=Real.exp (gueCenterCoordinate n x) := by
  unfold gueLSIWitness
  rw [pow_two,← Real.exp_add]
  congr 1
  ring

theorem gueLSIWitness_square_integral {n : ℕ} (hn : 0 < n) :
    (∫x, gueLSIWitness n x^2 ∂gueFullMeasure n)=Real.exp ((gueCenterVariance n : ℝ)/2) := by
  simp_rw [gueLSIWitness_square]
  rw [gueFullMeasure_center_gaussian_integral hn Real.exp]
  have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := gueCenterVariance n)) 1
  simpa only [mgf, zero_mul, zero_add, one_pow, mul_one, one_mul] using h

theorem gueLSIWitness_entropy_integral {n : ℕ} (hn : 0 < n) :
    (∫x, gueLSIWitness n x^2*Real.log (gueLSIWitness n x^2) ∂gueFullMeasure n)=
      (gueCenterVariance n : ℝ)*Real.exp ((gueCenterVariance n : ℝ)/2) := by
  simp_rw [gueLSIWitness_square, Real.log_exp]
  rw [gueFullMeasure_center_gaussian_integral hn (fun t => Real.exp t*t)]
  have hd := deriv_mgf (X := fun x : ℝ => x) (μ := gaussianReal 0 (gueCenterVariance n))
    (t := 1) (by simp)
  rw [mgf_fun_id_gaussianReal] at hd
  have hdexp : HasDerivAt (fun t : ℝ => Real.exp ((gueCenterVariance n : ℝ)*t^2/2))
      ((gueCenterVariance n : ℝ)*Real.exp ((gueCenterVariance n : ℝ)/2)) 1 := by
    convert (((hasDerivAt_id (1 : ℝ)).pow 2).const_mul (gueCenterVariance n : ℝ) |>.div_const 2).exp
        using 1 <;> norm_num; ring
  have he : (fun t : ℝ => Real.exp ((0 : ℝ)*t+(gueCenterVariance n : ℝ)*t^2/2))=
      (fun t : ℝ => Real.exp ((gueCenterVariance n : ℝ)*t^2/2)) := by simp
  rw [he, hdexp.deriv] at hd
  simpa only [one_mul, mul_one, mul_comm] using hd.symm

theorem gueLSIWitness_contDiff (n : ℕ) : ContDiff ℝ ∞ (gueLSIWitness n) :=
  Real.contDiff_exp.comp ((gueCenterCoordinate_contDiff n).div_const 2)

theorem gueLSIWitness_gradient (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (gueLSIWitness n) x=(gueLSIWitness n x/2) • gueCenterUnit n := by
  have hd0 : HasFDerivAt (gueCenterCoordinate n)
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (gueCenterUnit n)) x :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (gueCenterUnit n)).hasFDerivAt
  have hd := (hd0.const_mul (1/2 : ℝ)).exp
  have he (y) : (1/2 : ℝ)*gueCenterCoordinate n y=gueCenterCoordinate n y/2 := by ring
  simp_rw [he] at hd
  unfold gradient gueLSIWitness
  rw [hd.fderiv]
  simp only [map_smul]
  rw [(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm_apply_apply, smul_smul]
  congr 1
  ring

theorem gueLSIWitness_gradient_energy {n : ℕ} (hn : 0 < n) :
    (∫x, ‖gradient (gueLSIWitness n) x‖^2 ∂gueFullMeasure n)=
      (1/4)*Real.exp ((gueCenterVariance n : ℝ)/2) := by
  simp_rw [gueLSIWitness_gradient, norm_smul, gueCenterUnit_norm hn, mul_one, Real.norm_eq_abs,
      sq_abs, div_pow]
  have he (x) : gueLSIWitness n x^2/(2 : ℝ)^2=(1/4)*gueLSIWitness n x^2 := by ring
  simp_rw [he]
  rw [integral_const_mul, gueLSIWitness_square_integral hn]

theorem gueLSIWitness_lsi_equality {n : ℕ} (hn : 0 < n) :
    squareEntropy (gueFullMeasure n) (gueLSIWitness n)=
      (2/(n : ℝ))*(∫x, ‖gradient (gueLSIWitness n) x‖^2 ∂gueFullMeasure n) := by
  unfold squareEntropy
  rw [gueLSIWitness_entropy_integral hn, gueLSIWitness_square_integral hn, Real.log_exp,
    gueLSIWitness_gradient_energy hn, show (gueCenterVariance n : ℝ)=(n : ℝ)⁻¹ from rfl]
  ring

theorem gueLSIWitness_memLp {n : ℕ} (hn : 0 < n) : MemLp (gueLSIWitness n) 2 (gueFullMeasure n) :=
    by
  apply (memLp_two_iff_integrable_sq (gueLSIWitness_contDiff n).continuous.aestronglyMeasurable).mpr
  apply Integrable.of_integral_ne_zero
  rw [gueLSIWitness_square_integral hn]
  exact Real.exp_ne_zero _

theorem gueLSIWitness_gradient_memLp {n : ℕ} (hn : 0 < n) :
    MemLp (gradient (gueLSIWitness n)) 2 (gueFullMeasure n) := by
  have hg : Continuous (gradient (gueLSIWitness n)) := by
    have he : gradient (gueLSIWitness n)=fun x => (gueLSIWitness n x/2) • gueCenterUnit n :=
      funext (gueLSIWitness_gradient n)
    rw [he]
    exact ((gueLSIWitness_contDiff n).continuous.div_const 2).smul continuous_const
  apply (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
  apply Integrable.of_integral_ne_zero
  rw [gueLSIWitness_gradient_energy hn]
  positivity

end
end GinibrePoincare
