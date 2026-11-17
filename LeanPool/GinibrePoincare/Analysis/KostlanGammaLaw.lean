/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/KostlanGammaLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.KostlanProductLaw
public import LeanPool.GinibrePoincare.Analysis.HomogeneousRadialMeasure
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Kostlan Gamma Law
-/


@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Pointwise
namespace GinibrePoincare
noncomputable section

/-- The scaled squared radius used in Kostlan's Gamma description. -/
def kostlanSquaredRadius (n : ℕ) (z : ℂ) : ℝ := (n : ℝ) * Complex.normSq z

private def coordinatePolynomialMeasure (k : ℕ) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (Complex.normSq z ^ k))

private theorem coordinatePolynomialMeasure_radius (n k : ℕ) (hn : 0 < n) :
    (coordinatePolynomialMeasure k).map (kostlanSquaredRadius n) =
      (((k + 1 : ℕ) : ℝ≥0∞) *
        coordinatePolynomialMeasure k ((kostlanSquaredRadius n) ⁻¹' Iic 1)) •
          radialPowerMeasure (k + 1) := by
  have hq : Continuous (kostlanSquaredRadius n) := Complex.continuous_normSq.const_mul _
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcompact : IsCompact ((kostlanSquaredRadius n) ⁻¹' Iic 1) := by
    apply (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
      (isClosed_le hq continuous_const)
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    change (n : ℝ) * Complex.normSq z ≤ 1 at hz
    rw [Complex.normSq_eq_norm_sq] at hz
    have := norm_nonneg z
    nlinarith [sq_nonneg (‖z‖ - 1)]
  have hfinite : coordinatePolynomialMeasure k ((kostlanSquaredRadius n) ⁻¹' Iic 1) < ⊤ := by
    unfold coordinatePolynomialMeasure
    rw [withDensity_apply _ (hq.measurable measurableSet_Iic)]
    exact (Complex.continuous_normSq.pow k).continuousOn.integrableOn_compact hcompact
      |>.lintegral_lt_top
  have hzero : coordinatePolynomialMeasure k ((kostlanSquaredRadius n) ⁻¹' {0}) = 0 := by
    have hset : (kostlanSquaredRadius n) ⁻¹' {0} = {0} := by
      ext z
      simp only [mem_preimage, mem_singleton_iff, kostlanSquaredRadius, mul_eq_zero,
        Complex.normSq_eq_zero, Nat.cast_eq_zero, hn.ne', false_or]
    rw [hset]
    exact withDensity_absolutelyContinuous _ _ (measure_singleton _)
  apply map_quadratic_homogeneous_measure _ _ hq.measurable
    (fun z => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)) _
    (Nat.succ_pos k) _ _ hzero hfinite
  · intro t ht z
    simp only [kostlanSquaredRadius, Complex.real_smul, map_mul, Complex.normSq_ofReal]
    ring
  · intro t ht s
    have hh : ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        ENNReal.ofReal (Complex.normSq (r • z) ^ k) =
          ENNReal.ofReal (r ^ (2 * k)) * ENNReal.ofReal (Complex.normSq z ^ k) := by
      intro r hr z
      simp only [Complex.real_smul, map_mul, Complex.normSq_ofReal, mul_pow]
      rw [← ENNReal.ofReal_mul (pow_nonneg hr.le (2 * k))]
      congr 1
      rw [show 2 * k = k + k by omega, pow_add]
    have h := homogeneous_withDensity_smul (volume : Measure ℂ)
      (fun z => ENNReal.ofReal (Complex.normSq z ^ k)) (by fun_prop) (2 * k) hh t ht s
    rw [Complex.finrank_real_complex] at h
    rw [show 2 + 2 * k = 2 * (k + 1) by omega] at h
    exact h

/-- Every normalized coordinate tilt has Gamma squared radius: shape `k+1`, rate one. -/
theorem kostlanCoordinateLaw_gamma (n k : ℕ) (hn : 0 < n) :
    (kostlanCoordinateLaw n k).map (kostlanSquaredRadius n) =
      gammaMeasure ((k + 1 : ℕ) : ℝ) 1 := by
  let b : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) / Real.pi *
    ((n : ℝ) ^ k / (k.factorial : ℝ)))
  have htilt : kostlanCoordinateLaw n k = b •
      (coordinatePolynomialMeasure k).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-kostlanSquaredRadius n z))) := by
    unfold kostlanCoordinateLaw coordinatePolynomialMeasure
    rw [complexCoordinateGaussianMeasure_eq_withDensity hn,
      ← withDensity_mul _ (by
        unfold complexCoordinateGaussianDensity
        fun_prop) (by
        unfold kostlanCoordinateWeight
        fun_prop),
      ← withDensity_mul _ (by fun_prop) (by unfold kostlanSquaredRadius; fun_prop),
      ← withDensity_smul _ (by unfold kostlanSquaredRadius; fun_prop)]
    congr 1
    funext z
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    unfold complexCoordinateGaussianDensity kostlanCoordinateWeight kostlanSquaredRadius b
    have hz : 0 ≤ Complex.normSq z ^ k := pow_nonneg (Complex.normSq_nonneg _) _
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hm : (kostlanCoordinateLaw n k).map (kostlanSquaredRadius n) =
      (b * (((k + 1 : ℕ) : ℝ≥0∞) *
        coordinatePolynomialMeasure k ((kostlanSquaredRadius n) ⁻¹' Iic 1))) •
          (radialPowerMeasure (k + 1)).withDensity (fun x => ENNReal.ofReal (Real.exp (-x))) := by
    rw [htilt, Measure.map_smul _ (by unfold kostlanSquaredRadius; fun_prop)]
    change b • ((coordinatePolynomialMeasure k).withDensity
      ((fun x => ENNReal.ofReal (Real.exp (-x))) ∘ kostlanSquaredRadius n)).map _ = _
    rw [map_withDensity_comp_measurable _ _ (by unfold kostlanSquaredRadius; fun_prop) _ (by
      fun_prop),
      coordinatePolynomialMeasure_radius n k hn, withDensity_smul_measure, smul_smul]
  have hprob : IsProbabilityMeasure ((kostlanCoordinateLaw n k).map (kostlanSquaredRadius n)) := by
    have := kostlanCoordinateLaw_isProbabilityMeasure n k hn
    exact (by infer_instance)
  rw [hm] at hprob ⊢
  exact normalized_gaussian_tilt_gamma _ (Nat.succ_pos k) _ hprob

/-- The squared individual radii under the reference law are independent Gamma variables. -/
theorem kostlanReference_gamma_product (n : ℕ) (hn : 0 < n) :
    (kostlanReference n).map (fun z i => kostlanSquaredRadius n (z i)) =
      Measure.pi (fun i : Fin n => gammaMeasure ((i.val + 1 : ℕ) : ℝ) 1) := by
  rw [kostlanReference_eq_product n hn]
  have hp : ∀ i : Fin n, IsProbabilityMeasure
      ((kostlanCoordinateLaw n i.val).map (kostlanSquaredRadius n)) := by
    intro i
    rw [kostlanCoordinateLaw_gamma n i.val hn]
    exact isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  let := hp
  rw [Measure.pi_map_pi (fun i => (show Measurable (kostlanSquaredRadius n) by
    unfold kostlanSquaredRadius; fun_prop).aemeasurable)]
  simp_rw [kostlanCoordinateLaw_gamma n _ hn]

/-- Kostlan's expectation identity for bounded continuous symmetric tests:
`n|z_i|²` can be replaced by independent Gamma variables of shapes `i+1`. -/
theorem ginibre_radial_expectation_eq_gamma_product (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F)
    (hS : IsSymmetricRadiusTest n F) (C : ℝ) (hC : ∀ r, ‖F r‖ ≤ C) :
    (∫ z, F (fun i => kostlanSquaredRadius n (z i)) ∂ginibreMeasure n) =
      ∫ r, F r ∂Measure.pi (fun i : Fin n => gammaMeasure ((i.val + 1 : ℕ) : ℝ) 1) := by
  have ht := ginibre_radial_expectation_eq_kostlanReference n hn
    (fun r => F (fun i => (n : ℝ) * r i)) (by fun_prop)
    (by intro σ r; exact hS σ (fun i => (n : ℝ) * r i)) C
    (fun r => hC _)
  change (∫ z, F (fun i => kostlanSquaredRadius n (z i)) ∂ginibreMeasure n) =
    ∫ z, F (fun i => kostlanSquaredRadius n (z i)) ∂kostlanReference n at ht
  rw [ht, ← kostlanReference_gamma_product n hn]
  have hq : Continuous (fun z : Configuration n => fun i => kostlanSquaredRadius n (z i)) := by
    unfold kostlanSquaredRadius
    fun_prop
  exact (integral_map hq.measurable.aemeasurable hF.aestronglyMeasurable).symm

end
end GinibrePoincare
