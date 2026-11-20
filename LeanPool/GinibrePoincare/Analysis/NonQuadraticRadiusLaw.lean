/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticRadiusLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticKostlan
public import LeanPool.GinibrePoincare.Analysis.HomogeneousRadialMeasure
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Explicit squared-radius laws for arbitrary radial confinement
The independent coordinates have normalized densities proportional to
s^k exp(-n V(sqrt(s))) on the positive half-line. All normalization constants
are actual masses; their validity follows from the original finite partition.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal Pointwise
namespace GinibrePoincare
noncomputable section

/-- Polynomially weighted planar volume for the radial pushforward. -/
def potentialPolynomialVolume (k : ℕ) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (Complex.normSq z ^ k))

instance (k : ℕ) : SigmaFinite (potentialPolynomialVolume k) := by
  unfold potentialPolynomialVolume
  infer_instance

/-- The squared-radius pushforward of weighted planar volume is a power law.
The scalar is determined by the actual mass of the unit disk. -/
theorem potentialPolynomialVolume_squaredRadius (k : ℕ) :
    (potentialPolynomialVolume k).map Complex.normSq =
      (((k + 1 : ℕ) : ℝ≥0∞) * potentialPolynomialVolume k (Complex.normSq ⁻¹' Iic 1)) •
        radialPowerMeasure (k + 1) := by
  have hq := Complex.continuous_normSq
  have hcompact : IsCompact (Complex.normSq ⁻¹' Iic 1) := by
    apply (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
      (isClosed_le hq continuous_const)
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    change Complex.normSq z ≤ 1 at hz
    rw [Complex.normSq_eq_norm_sq] at hz
    have := norm_nonneg z
    nlinarith [sq_nonneg (‖z‖ - 1)]
  have hfinite : potentialPolynomialVolume k (Complex.normSq ⁻¹' Iic 1) < ⊤ := by
    unfold potentialPolynomialVolume
    rw [withDensity_apply _ (hq.measurable measurableSet_Iic)]
    exact (Complex.continuous_normSq.pow k).continuousOn.integrableOn_compact hcompact
        |>.lintegral_lt_top
  have hzero : potentialPolynomialVolume k (Complex.normSq ⁻¹' {0}) = 0 := by
    have hs : Complex.normSq ⁻¹' {0} = {0} := by ext z; simp
    rw [hs]
    exact withDensity_absolutelyContinuous _ _ (measure_singleton _)
  apply map_quadratic_homogeneous_measure _ _ hq.measurable Complex.normSq_nonneg _
    (Nat.succ_pos k) _ _ hzero hfinite
  · intro t ht z
    simp only [Complex.real_smul, map_mul, Complex.normSq_ofReal]
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

/-- Actual unnormalized positive-half-line density s^k exp(-nV(sqrt(s))). -/
def rawPotentialSquaredRadiusLaw (n k : ℕ) (V : Potential) : Measure ℝ :=
  (radialPowerMeasure (k + 1)).withDensity
    (fun s => ENNReal.ofReal (Real.exp (-(n : ℝ) * potentialSquaredRadiusProfile V s)))

/-- Its normalization uses the actual radial partition integral. -/
def potentialSquaredRadiusLaw (n k : ℕ) (V : Potential) : Measure ℝ :=
  (rawPotentialSquaredRadiusLaw n k V Set.univ)⁻¹ • rawPotentialSquaredRadiusLaw n k V

/-- The coordinate Gaussian tilt has exactly the desired planar Lebesgue
confinement; its Gaussian reference scalar is explicit. -/
theorem rawPotentialKostlanCoordinateLaw_eq_volume (n k : ℕ) (hn : 0 < n)
    {V : Potential} (hVc : Continuous V) :
    rawPotentialKostlanCoordinateLaw n k V = ENNReal.ofReal ((n : ℝ) / Real.pi) •
      (potentialPolynomialVolume k).withDensity (fun z => ENNReal.ofReal (Real.exp (-(n : ℝ) * V
          z))) := by
  unfold rawPotentialKostlanCoordinateLaw potentialPolynomialVolume
  rw [complexCoordinateGaussianMeasure_eq_withDensity hn,
    ← withDensity_mul _ (measurable_complexCoordinateGaussianDensity n)
      (by unfold potentialKostlanCoordinateWeight;
          exact ((Complex.continuous_normSq.pow k).mul
            (Real.continuous_exp.comp (continuous_const.mul
              (hVc.sub Complex.continuous_normSq)))).measurable.ennreal_ofReal),
    ← withDensity_mul (volume : Measure ℂ)
      (f := fun z => ENNReal.ofReal (Complex.normSq z ^ k))
      (g := fun z => ENNReal.ofReal (Real.exp (-(n : ℝ) * V z))) (by fun_prop)
      ((show Continuous (fun z => Real.exp (-(n : ℝ) * V z)) from
        Real.continuous_exp.comp (continuous_const.mul hVc)).measurable.ennreal_ofReal),
    ← withDensity_smul _ (by
      apply Measurable.mul
      · fun_prop
      · exact (show Continuous (fun z => Real.exp (-(n : ℝ) * V z)) from
          Real.continuous_exp.comp (continuous_const.mul hVc)).measurable.ennreal_ofReal)]
  congr 1
  funext z
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, complexCoordinateGaussianDensity,
    potentialKostlanCoordinateWeight]
  rw [← ENNReal.ofReal_mul (pow_nonneg (Complex.normSq_nonneg z) k),
    ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have he : Real.exp (-(n : ℝ) * Complex.normSq z) *
      Real.exp (-(n : ℝ) * (V z - Complex.normSq z)) = Real.exp (-(n : ℝ) * V z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ((n : ℝ) / Real.pi * Real.exp (-(n : ℝ) * Complex.normSq z)) *
        (Complex.normSq z ^ k * Real.exp (-(n : ℝ) * (V z - Complex.normSq z))) =
      ((n : ℝ) / Real.pi) * (Complex.normSq z ^ k *
        (Real.exp (-(n : ℝ) * Complex.normSq z) *
          Real.exp (-(n : ℝ) * (V z - Complex.normSq z)))) := by ring
    _ = _ := by rw [he]

/-- The normalized independent coordinate has exactly the normalized
positive-half-line squared-radius density from the paper. -/
theorem potentialKostlanCoordinateLaw_squaredRadius (n : ℕ) (hn : 0 < n)
    {V : Potential} (hVc : Continuous V) (hVr : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (i : Fin n) :
    (potentialKostlanCoordinateLaw n i.val V).map Complex.normSq =
      potentialSquaredRadiusLaw n i.val V := by
  let b := ENNReal.ofReal ((n : ℝ) / Real.pi) *
    (((i.val + 1 : ℕ) : ℝ≥0∞) *
      potentialPolynomialVolume i.val (Complex.normSq ⁻¹' Iic 1))
  have ht : (rawPotentialKostlanCoordinateLaw n i.val V).map Complex.normSq =
      b • rawPotentialSquaredRadiusLaw n i.val V := by
    rw [rawPotentialKostlanCoordinateLaw_eq_volume n i.val hn hVc, Measure.map_smul _
        Complex.continuous_normSq.measurable.aemeasurable]
    have hprofile : (fun z : ℂ => ENNReal.ofReal (Real.exp (-(n : ℝ) * V z))) =
        (fun s => ENNReal.ofReal (Real.exp (-(n : ℝ) * potentialSquaredRadiusProfile V s))) ∘
          Complex.normSq := by
      funext z
      rw [Function.comp_apply, potential_eq_squaredRadiusProfile hVr]
    rw [hprofile, map_withDensity_comp_measurable _ _ Complex.continuous_normSq.measurable _
      (by unfold potentialSquaredRadiusProfile;
          exact (Real.continuous_exp.comp (continuous_const.mul
            (hVc.comp (Complex.continuous_ofReal.comp
                Real.continuous_sqrt)))).measurable.ennreal_ofReal),
      potentialPolynomialVolume_squaredRadius, withDensity_smul_measure, smul_smul]
    rfl
  have hp := potentialKostlanCoordinateLaw_isProbabilityMeasure n hn hVc hVr hfin i
  let := hp
  have hmapP : IsProbabilityMeasure
      ((potentialKostlanCoordinateLaw n i.val V).map Complex.normSq) :=
    (by infer_instance)
  unfold potentialKostlanCoordinateLaw at hmapP ⊢
  rw [Measure.map_smul _ Complex.continuous_normSq.measurable.aemeasurable, ht,
    smul_smul] at hmapP ⊢
  have hm := hmapP.measure_univ
  rw [Measure.smul_apply, smul_eq_mul] at hm
  have hcoef := ENNReal.eq_inv_of_mul_eq_one_left hm
  rw [hcoef]
  rfl

/-- The explicit normalized squared-radius law is a probability measure,
proved from the actual original partition condition. -/
theorem potentialSquaredRadiusLaw_isProbabilityMeasure (n : ℕ) (hn : 0 < n)
    {V : Potential} (hVc : Continuous V) (hVr : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (i : Fin n) :
    IsProbabilityMeasure (potentialSquaredRadiusLaw n i.val V) := by
  rw [← potentialKostlanCoordinateLaw_squaredRadius n hn hVc hVr hfin i]
  let := potentialKostlanCoordinateLaw_isProbabilityMeasure n hn hVc hVr hfin i
  exact (by infer_instance)

/-- Actual independent squared-radius law for arbitrary radial confinement. -/
def potentialSquaredRadiusProduct (n : ℕ) (V : Potential) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i : Fin n => potentialSquaredRadiusLaw n i.val V)

/-- The coordinate-product reference has exactly the explicit independent
positive-half-line squared-radius laws. -/
theorem potentialKostlanReference_squaredRadiusProduct (n : ℕ) (hn : 0 < n)
    {V : Potential} (hVc : Continuous V) (hVr : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) :
    (potentialKostlanReference n V).map (fun z i => Complex.normSq (z i)) =
      potentialSquaredRadiusProduct n V := by
  rw [potentialKostlanReference_eq_product n hn hVc hVr hfin]
  have hp : ∀ i : Fin n, IsProbabilityMeasure
      ((potentialKostlanCoordinateLaw n i.val V).map Complex.normSq) := by
    intro i
    rw [potentialKostlanCoordinateLaw_squaredRadius n hn hVc hVr hfin i]
    exact potentialSquaredRadiusLaw_isProbabilityMeasure n hn hVc hVr hfin i
  let := hp
  rw [Measure.pi_map_pi (fun i => Complex.continuous_normSq.measurable.aemeasurable)]
  simp_rw [potentialKostlanCoordinateLaw_squaredRadius n hn hVc hVr hfin]
  rfl

/-- General Kostlan expectation identity in the paper's literal squared
individual radius variables. -/
theorem potential_radial_expectation_eq_squaredRadiusProduct (n : ℕ) (hn : 0 < n)
    {V : Potential} (hVc : Continuous V) (hVr : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (F : (Fin n → ℝ) → ℝ)
    (hF : Continuous F) (hS : IsSymmetricRadiusTest n F) (C : ℝ)
    (hC : ∀ r, ‖F r‖ ≤ C) :
    (∫ z, F (fun i => Complex.normSq (z i)) ∂potentialMeasure n V) =
      ∫ r, F r ∂potentialSquaredRadiusProduct n V := by
  rw [potential_radial_integral_eq_product n hn hVc hVr hfin F hF hS C hC,
    ← potentialKostlanReference_eq_product n hn hVc hVr hfin,
    ← potentialKostlanReference_squaredRadiusProduct n hn hVc hVr hfin]
  have hm : Measurable (fun z : Configuration n => fun i => Complex.normSq (z i)) :=
    (continuous_pi (fun i => Complex.continuous_normSq.comp (continuous_apply i))).measurable
  exact (integral_map hm.aemeasurable hF.aestronglyMeasurable).symm

/-- The literal square entropy identity for the explicit independent
nonquadratic squared-radius densities. -/
theorem potential_radial_entropy_eq_squaredRadiusProduct (n : ℕ) (hn : 0 < n)
    {V : Potential} (hVc : Continuous V) (hVr : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (F : (Fin n → ℝ) → ℝ)
    (hF : Continuous F) (hc : HasCompactSupport F) (hS : IsSymmetricRadiusTest n F) :
    squareEntropy (potentialMeasure n V) (fun z => F (fun i => Complex.normSq (z i))) =
      squareEntropy (potentialSquaredRadiusProduct n V) F := by
  apply squareEntropy_eq_of_moments
  · have hs : HasCompactSupport (fun r => F r ^ 2) := by
      apply hc.mono
      intro r hr hz
      exact hr (by simp [hz])
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous (hF.pow 2)
    exact potential_radial_expectation_eq_squaredRadiusProduct n hn hVc hVr hfin (fun r => F r ^ 2)
      (hF.pow 2) (by intro σ r; exact congrArg (fun x : ℝ => x ^ 2) (hS σ r)) C hC
  · obtain ⟨C, hC⟩ := (compactSupport_square_mul_log hc).exists_bound_of_continuous
      (continuous_square_mul_log hF)
    exact potential_radial_expectation_eq_squaredRadiusProduct n hn hVc hVr hfin
      (fun r => F r ^ 2 * Real.log (F r ^ 2)) (continuous_square_mul_log hF)
      (by intro σ r; exact congrArg (fun x : ℝ => x ^ 2 * Real.log (x ^ 2)) (hS σ r)) C hC

end
end GinibrePoincare
