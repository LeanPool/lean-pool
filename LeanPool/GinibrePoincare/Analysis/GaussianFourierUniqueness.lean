/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianFourierUniqueness.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianFourierCoordinates
public import LeanPool.GinibrePoincare.Analysis.GaussianHermiteMoments
public import LeanPool.GinibrePoincare.Analysis.HermiteL2Family
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Positive-measure reduction for Gaussian Fourier uniqueness -/


@[expose] public section


open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace GinibrePoincare

noncomputable section

theorem integrable_re_Lp_two {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    Integrable (fun z ↦ (v z).re) (complexGaussianMeasure n) :=
  ((Lp.memLp v).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).re

theorem integrable_im_Lp_two {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    Integrable (fun z ↦ (v z).im) (complexGaussianMeasure n) :=
  ((Lp.memLp v).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).im

private theorem integrable_max_zero {n : ℕ} {f : Configuration n → ℝ}
    (hf : Integrable f (complexGaussianMeasure n)) :
    Integrable (fun z ↦ max (f z) 0) (complexGaussianMeasure n) := by
  convert hf.sup
    (integrable_zero (Configuration n) ℝ (complexGaussianMeasure n)) using 1

/-- Positive and negative density measures associated with the real part of
an `L²` vector. -/
def gaussianRealPartPositiveMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) : Measure (Configuration n) :=
  (complexGaussianMeasure n).withDensity
    (fun z ↦ ENNReal.ofReal (max (v z).re 0))

/-- The Gaussian measure weighted by the negative part of the real component of an L²
function. -/
def gaussianRealPartNegativeMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) : Measure (Configuration n) :=
  (complexGaussianMeasure n).withDensity
    (fun z ↦ ENNReal.ofReal (max (-(v z).re) 0))

/-- Positive and negative density measures associated with the imaginary
part of an `L²` vector. -/
def gaussianImagPartPositiveMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) : Measure (Configuration n) :=
  (complexGaussianMeasure n).withDensity
    (fun z ↦ ENNReal.ofReal (max (v z).im 0))

/-- The Gaussian measure weighted by the negative part of the imaginary component of an L²
function. -/
def gaussianImagPartNegativeMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) : Measure (Configuration n) :=
  (complexGaussianMeasure n).withDensity
    (fun z ↦ ENNReal.ofReal (max (-(v z).im) 0))

theorem isFiniteMeasure_gaussianRealPartPositiveMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    IsFiniteMeasure (gaussianRealPartPositiveMeasure v) := by
  apply isFiniteMeasure_withDensity_ofReal
  exact (integrable_max_zero (integrable_re_Lp_two v)).hasFiniteIntegral

theorem isFiniteMeasure_gaussianRealPartNegativeMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    IsFiniteMeasure (gaussianRealPartNegativeMeasure v) := by
  apply isFiniteMeasure_withDensity_ofReal
  exact (integrable_max_zero (integrable_re_Lp_two v).neg).hasFiniteIntegral

theorem isFiniteMeasure_gaussianImagPartPositiveMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    IsFiniteMeasure (gaussianImagPartPositiveMeasure v) := by
  apply isFiniteMeasure_withDensity_ofReal
  exact (integrable_max_zero (integrable_im_Lp_two v)).hasFiniteIntegral

theorem isFiniteMeasure_gaussianImagPartNegativeMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    IsFiniteMeasure (gaussianImagPartNegativeMeasure v) := by
  apply isFiniteMeasure_withDensity_ofReal
  exact (integrable_max_zero (integrable_im_Lp_two v).neg).hasFiniteIntegral

/-- Euclidean pushforwards of the positive and negative real-part measures. -/
def euclideanRealPartPositiveMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    Measure (EuclideanSpace ℝ (Fin n × Fin 2)) :=
  (gaussianRealPartPositiveMeasure v).map (configurationEuclideanEquiv n)

/-- Euclidean-coordinate pushforward of the negative real-part density measure. -/
def euclideanRealPartNegativeMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    Measure (EuclideanSpace ℝ (Fin n × Fin 2)) :=
  (gaussianRealPartNegativeMeasure v).map (configurationEuclideanEquiv n)

/-- Euclidean pushforwards of the positive and negative imaginary-part measures. -/
def euclideanImagPartPositiveMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    Measure (EuclideanSpace ℝ (Fin n × Fin 2)) :=
  (gaussianImagPartPositiveMeasure v).map (configurationEuclideanEquiv n)

/-- Euclidean-coordinate pushforward of the negative imaginary-part density measure. -/
def euclideanImagPartNegativeMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    Measure (EuclideanSpace ℝ (Fin n × Fin 2)) :=
  (gaussianImagPartNegativeMeasure v).map (configurationEuclideanEquiv n)

/-- Push a nonnegative integrable Gaussian density to Euclidean coordinates and express its
characteristic function through the configuration Fourier character. -/
theorem charFun_map_gaussian_withDensity {n : ℕ} (ρ : Configuration n → ℝ)
    (hρ : ∀ z, 0 ≤ ρ z) (hρInt : Integrable ρ (complexGaussianMeasure n))
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    charFun (((complexGaussianMeasure n).withDensity (fun z ↦ ENNReal.ofReal (ρ z))).map
      (configurationEuclideanEquiv n)) x =
      ∫ z, (ρ z : ℂ) * configurationFourierCharacter
        ((configurationEuclideanEquiv n).symm x) z ∂complexGaussianMeasure n := by
  let : IsFiniteMeasure ((complexGaussianMeasure n).withDensity
      (fun z ↦ ENNReal.ofReal (ρ z))) :=
    isFiniteMeasure_withDensity_ofReal hρInt.hasFiniteIntegral
  rw [charFun_apply]
  rw [integral_map
    (measurable_configurationEuclideanEquiv n).aemeasurable (by fun_prop)]
  rw [integral_withDensity_eq_integral_toReal_smul₀]
  · apply integral_congr_ae
    filter_upwards with z
    rw [real_inner_configurationEuclideanEquiv]
    simp [configurationFourierCharacter, ENNReal.toReal_ofReal (hρ z)]
  · exact hρInt.aemeasurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun z ↦ ENNReal.ofReal_lt_top

theorem charFun_euclideanRealPartPositiveMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    charFun (euclideanRealPartPositiveMeasure v) x =
      ∫ z, ((max (v z).re 0 : ℝ) : ℂ) *
        configurationFourierCharacter
          ((configurationEuclideanEquiv n).symm x) z
        ∂complexGaussianMeasure n := by
  exact charFun_map_gaussian_withDensity (fun z ↦ max (v z).re 0)
    (fun _ ↦ le_max_right _ _) (integrable_max_zero (integrable_re_Lp_two v)) x

theorem charFun_euclideanRealPartNegativeMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    charFun (euclideanRealPartNegativeMeasure v) x =
      ∫ z, ((max (-(v z).re) 0 : ℝ) : ℂ) *
        configurationFourierCharacter
          ((configurationEuclideanEquiv n).symm x) z
        ∂complexGaussianMeasure n := by
  exact charFun_map_gaussian_withDensity (fun z ↦ max (-(v z).re) 0)
    (fun _ ↦ le_max_right _ _) (integrable_max_zero (integrable_re_Lp_two v).neg) x

theorem charFun_euclideanImagPartPositiveMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    charFun (euclideanImagPartPositiveMeasure v) x =
      ∫ z, ((max (v z).im 0 : ℝ) : ℂ) *
        configurationFourierCharacter
          ((configurationEuclideanEquiv n).symm x) z
        ∂complexGaussianMeasure n := by
  exact charFun_map_gaussian_withDensity (fun z ↦ max (v z).im 0)
    (fun _ ↦ le_max_right _ _) (integrable_max_zero (integrable_im_Lp_two v)) x

theorem charFun_euclideanImagPartNegativeMeasure {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    charFun (euclideanImagPartNegativeMeasure v) x =
      ∫ z, ((max (-(v z).im) 0 : ℝ) : ℂ) *
        configurationFourierCharacter
          ((configurationEuclideanEquiv n).symm x) z
        ∂complexGaussianMeasure n := by
  exact charFun_map_gaussian_withDensity (fun z ↦ max (-(v z).im) 0)
    (fun _ ↦ le_max_right _ _) (integrable_max_zero (integrable_im_Lp_two v).neg) x

private theorem configurationFourierCharacter_neg {n : ℕ}
    (t z : Configuration n) :
    conj (configurationFourierCharacter (-t) z) =
      configurationFourierCharacter t z := by
  unfold configurationFourierCharacter configurationRealPairing
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.neg_apply,
    Complex.neg_re, Complex.neg_im, neg_mul]
  push_cast
  rw [show (∑ x, (-((t x).re * (z x).re) + -((t x).im * (z x).im) : ℂ)) =
      -(∑ x, ((t x).re * (z x).re + (t x).im * (z x).im : ℂ)) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  ring

/-- An integrable complex function stays integrable after multiplication by a Fourier character. -/
theorem integrable_mul_configurationFourierCharacter_of_integrable {n : ℕ}
    {f : Configuration n → ℂ} (hf : Integrable f (complexGaussianMeasure n))
    (t : Configuration n) :
    Integrable (fun z ↦ f z * configurationFourierCharacter t z)
      (complexGaussianMeasure n) := by
  exact hf.mul_bdd (c := 1)
    (continuous_configurationFourierCharacter t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z ↦ by simp)

/-- Vanishing Fourier tests also annihilate the conjugated L² representative. -/
theorem integral_conj_mul_configurationFourierCharacter_eq_zero {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (hzero : ∀ t, gaussianL2FourierTest v t = 0) (t : Configuration n) :
    (∫ z, conj (v z) * configurationFourierCharacter t z
      ∂complexGaussianMeasure n) = 0 := by
  have hn := congrArg conj (hzero (-t))
  unfold gaussianL2FourierTest at hn
  rw [← integral_conj] at hn
  simpa only [map_mul, configurationFourierCharacter_neg, map_zero] using hn

theorem integral_re_mul_configurationFourierCharacter_eq_zero {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (hzero : ∀ t, gaussianL2FourierTest v t = 0)
    (t : Configuration n) :
    (∫ z, ((v z).re : ℂ) * configurationFourierCharacter t z
      ∂complexGaussianMeasure n) = 0 := by
  have hp := hzero t
  unfold gaussianL2FourierTest at hp
  have hn' := integral_conj_mul_configurationFourierCharacter_eq_zero v hzero t
  have hvInt := integrable_mul_configurationFourierCharacter v t
  have hcvInt : Integrable (fun z ↦ conj (v z) * configurationFourierCharacter t z)
      (complexGaussianMeasure n) :=
    integrable_mul_configurationFourierCharacter_of_integrable
      (Complex.conjCLE.toContinuousLinearMap.integrable_comp
        ((Lp.memLp v).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))) t
  rw [show (fun z ↦ ((v z).re : ℂ) * configurationFourierCharacter t z) =
      fun z ↦ (v z * configurationFourierCharacter t z +
        conj (v z) * configurationFourierCharacter t z) / 2 by
    funext z
    apply Complex.ext <;> simp; ring]
  rw [integral_div, integral_add hvInt hcvInt, hp, hn']
  simp

theorem integral_im_mul_configurationFourierCharacter_eq_zero {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (hzero : ∀ t, gaussianL2FourierTest v t = 0)
    (t : Configuration n) :
    (∫ z, ((v z).im : ℂ) * configurationFourierCharacter t z
      ∂complexGaussianMeasure n) = 0 := by
  have hp := hzero t
  unfold gaussianL2FourierTest at hp
  have hn' := integral_conj_mul_configurationFourierCharacter_eq_zero v hzero t
  have hvInt := integrable_mul_configurationFourierCharacter v t
  have hcvInt : Integrable (fun z ↦ conj (v z) * configurationFourierCharacter t z)
      (complexGaussianMeasure n) :=
    integrable_mul_configurationFourierCharacter_of_integrable
      (Complex.conjCLE.toContinuousLinearMap.integrable_comp
        ((Lp.memLp v).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))) t
  rw [show (fun z ↦ ((v z).im : ℂ) * configurationFourierCharacter t z) =
      fun z ↦ (v z * configurationFourierCharacter t z -
        conj (v z) * configurationFourierCharacter t z) / (2 * Complex.I) by
    funext z
    rw [show ((v z).im : ℂ) = (v z - conj (v z)) / (2 * Complex.I) by
      apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im]; ring]
    ring]
  rw [integral_div, integral_sub hvInt hcvInt, hp, hn']
  simp

private theorem integrable_ofReal_mul_configurationFourierCharacter {n : ℕ}
    {f : Configuration n → ℝ}
    (hf : Integrable f (complexGaussianMeasure n)) (t : Configuration n) :
    Integrable (fun z ↦ (f z : ℂ) * configurationFourierCharacter t z)
      (complexGaussianMeasure n) := by
  exact integrable_mul_configurationFourierCharacter_of_integrable hf.ofReal t

/-- A real integrable density with zero Fourier integrals has equal positive/negative tests. -/
theorem charFun_gaussian_density_parts_eq_of_fourier_integrals_eq_zero {n : ℕ}
    (f : Configuration n → ℝ) (hf : Integrable f (complexGaussianMeasure n))
    (hzero : ∀ t, (∫ z, (f z : ℂ) * configurationFourierCharacter t z
      ∂complexGaussianMeasure n) = 0) :
    charFun (((complexGaussianMeasure n).withDensity
      (fun z ↦ ENNReal.ofReal (max (f z) 0))).map (configurationEuclideanEquiv n)) =
    charFun (((complexGaussianMeasure n).withDensity
      (fun z ↦ ENNReal.ofReal (max (-(f z)) 0))).map (configurationEuclideanEquiv n)) := by
  funext x
  have hneg : Integrable (fun z ↦ max (-(f z)) 0) (complexGaussianMeasure n) :=
    integrable_max_zero hf.neg
  rw [charFun_map_gaussian_withDensity _ (fun _ ↦ le_max_right _ _)
      (integrable_max_zero hf),
    charFun_map_gaussian_withDensity _ (fun _ ↦ le_max_right _ _) hneg, ← sub_eq_zero]
  rw [← integral_sub
    (integrable_ofReal_mul_configurationFourierCharacter (integrable_max_zero hf) _)
    (integrable_ofReal_mul_configurationFourierCharacter hneg _)]
  convert hzero ((configurationEuclideanEquiv n).symm x) using 1
  apply integral_congr_ae
  filter_upwards with z
  rw [← sub_mul]
  norm_cast
  rw [max_zero_sub_max_neg_zero_eq_self]

/-- Fourier uniqueness identifies the positive and negative measures of an integrable density. -/
theorem gaussian_density_parts_eq_of_fourier_integrals_eq_zero {n : ℕ}
    (f : Configuration n → ℝ) (hf : Integrable f (complexGaussianMeasure n))
    (hzero : ∀ t, (∫ z, (f z : ℂ) * configurationFourierCharacter t z
      ∂complexGaussianMeasure n) = 0) :
    (complexGaussianMeasure n).withDensity (fun z ↦ ENNReal.ofReal (max (f z) 0)) =
      (complexGaussianMeasure n).withDensity (fun z ↦ ENNReal.ofReal (max (-(f z)) 0)) := by
  let : IsFiniteMeasure ((complexGaussianMeasure n).withDensity
      (fun z ↦ ENNReal.ofReal (max (f z) 0))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_max_zero hf).hasFiniteIntegral
  let : IsFiniteMeasure ((complexGaussianMeasure n).withDensity
      (fun z ↦ ENNReal.ofReal (max (-(f z)) 0))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_max_zero hf.neg).hasFiniteIntegral
  apply (configurationEuclideanEquiv
    n).toHomeomorph.toMeasurableEquiv.measurableEmbedding.map_injective
  exact Measure.ext_of_charFun
    (charFun_gaussian_density_parts_eq_of_fourier_integrals_eq_zero f hf hzero)

/-- Vanishing Fourier integrals force an arbitrary real integrable Gaussian density to vanish. -/
theorem ae_eq_zero_of_gaussian_fourier_integrals_eq_zero {n : ℕ}
    (f : Configuration n → ℝ) (hf : Integrable f (complexGaussianMeasure n))
    (hzero : ∀ t, (∫ z, (f z : ℂ) * configurationFourierCharacter t z
      ∂complexGaussianMeasure n) = 0) :
    ∀ᵐ z ∂complexGaussianMeasure n, f z = 0 := by
  have heq := gaussian_density_parts_eq_of_fourier_integrals_eq_zero f hf hzero
  have hdens := (withDensity_eq_iff_of_sigmaFinite
    (integrable_max_zero hf).aemeasurable.ennreal_ofReal
    (integrable_max_zero hf.neg).aemeasurable.ennreal_ofReal).mp heq
  filter_upwards [hdens] with z hz
  have hm : max (f z) 0 = max (-(f z)) 0 :=
    (ENNReal.ofReal_eq_ofReal_iff (le_max_right _ _) (le_max_right _ _)).mp hz
  have hsub := max_zero_sub_max_neg_zero_eq_self (f z)
  rw [hm, sub_self] at hsub
  exact hsub.symm

theorem charFun_euclideanRealParts_eq_of_fourierTest_eq_zero {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (hzero : ∀ t, gaussianL2FourierTest v t = 0) :
    charFun (euclideanRealPartPositiveMeasure v) =
      charFun (euclideanRealPartNegativeMeasure v) := by
  exact charFun_gaussian_density_parts_eq_of_fourier_integrals_eq_zero
    (fun z ↦ (v z).re) (integrable_re_Lp_two v)
    (integral_re_mul_configurationFourierCharacter_eq_zero v hzero)

theorem charFun_euclideanImagParts_eq_of_fourierTest_eq_zero {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (hzero : ∀ t, gaussianL2FourierTest v t = 0) :
    charFun (euclideanImagPartPositiveMeasure v) =
      charFun (euclideanImagPartNegativeMeasure v) := by
  exact charFun_gaussian_density_parts_eq_of_fourier_integrals_eq_zero
    (fun z ↦ (v z).im) (integrable_im_Lp_two v)
    (integral_im_mul_configurationFourierCharacter_eq_zero v hzero)

theorem gaussianRealPartPositiveMeasure_eq_negative_of_fourierTest_eq_zero {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (hzero : ∀ t, gaussianL2FourierTest v t = 0) :
    gaussianRealPartPositiveMeasure v = gaussianRealPartNegativeMeasure v := by
  exact gaussian_density_parts_eq_of_fourier_integrals_eq_zero
    (fun z ↦ (v z).re) (integrable_re_Lp_two v)
    (integral_re_mul_configurationFourierCharacter_eq_zero v hzero)

theorem gaussianImagPartPositiveMeasure_eq_negative_of_fourierTest_eq_zero {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (hzero : ∀ t, gaussianL2FourierTest v t = 0) :
    gaussianImagPartPositiveMeasure v = gaussianImagPartNegativeMeasure v := by
  exact gaussian_density_parts_eq_of_fourier_integrals_eq_zero
    (fun z ↦ (v z).im) (integrable_im_Lp_two v)
    (integral_im_mul_configurationFourierCharacter_eq_zero v hzero)

theorem ae_re_eq_zero_of_fourierTest_eq_zero {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (hzero : ∀ t, gaussianL2FourierTest v t = 0) :
    ∀ᵐ z ∂complexGaussianMeasure n, (v z).re = 0 := by
  exact ae_eq_zero_of_gaussian_fourier_integrals_eq_zero
    (fun z ↦ (v z).re) (integrable_re_Lp_two v)
    (integral_re_mul_configurationFourierCharacter_eq_zero v hzero)

theorem ae_im_eq_zero_of_fourierTest_eq_zero {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (hzero : ∀ t, gaussianL2FourierTest v t = 0) :
    ∀ᵐ z ∂complexGaussianMeasure n, (v z).im = 0 := by
  exact ae_eq_zero_of_gaussian_fourier_integrals_eq_zero
    (fun z ↦ (v z).im) (integrable_im_Lp_two v)
    (integral_im_mul_configurationFourierCharacter_eq_zero v hzero)

theorem eq_zero_of_gaussianL2FourierTest_eq_zero {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (hzero : ∀ t, gaussianL2FourierTest v t = 0) : v = 0 := by
  apply Lp.ext
  filter_upwards [ae_re_eq_zero_of_fourierTest_eq_zero v hzero,
    ae_im_eq_zero_of_fourierTest_eq_zero v hzero] with z hre him
  apply Complex.ext
  · simpa using hre
  · simpa using him

theorem eq_zero_of_orthogonal_hermites (n : ℕ) (hn : 0 < n)
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (horth : ∀ p q : Fin n → ℕ,
      inner ℂ (multivariateNormalizedL2 n hn p q) v = 0) : v = 0 := by
  apply eq_zero_of_gaussianL2FourierTest_eq_zero v
  exact gaussianL2FourierTest_eq_zero_of_orthogonal_hermites n hn v horth

theorem gaussianHermiteSpan_orthogonal_eq_bot (n : ℕ) (hn : 0 < n) :
    (gaussianHermiteSpan n hn)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  apply eq_zero_of_orthogonal_hermites n hn v
  intro p q
  exact hv (multivariateNormalizedL2 n hn p q)
    (multivariateNormalizedL2_mem_span n hn p q)

theorem gaussianHermiteSpan_topologicalClosure_eq_top (n : ℕ) (hn : 0 < n) :
    (gaussianHermiteSpan n hn).topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.orthogonal_closure]
  exact gaussianHermiteSpan_orthogonal_eq_bot n hn

/-- The normalized multivariate complex Hermites, packaged as a complete
Hilbert basis of Gaussian `L²`. -/
def gaussianHermiteHilbertBasis (n : ℕ) (hn : 0 < n) :
    HilbertBasis (ComplexHermite.HermiteMultiIndex n) ℂ
      (Lp ℂ 2 (complexGaussianMeasure n)) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (ComplexHermite.orthonormal_hermiteL2Family_gaussian n hn)
    (by
      change (gaussianHermiteSpan n hn)ᗮ = ⊥
      exact gaussianHermiteSpan_orthogonal_eq_bot n hn)

@[simp] theorem gaussianHermiteHilbertBasis_apply (n : ℕ) (hn : 0 < n)
    (pq : ComplexHermite.HermiteMultiIndex n) :
    gaussianHermiteHilbertBasis n hn pq = multivariateNormalizedL2 n hn pq.1 pq.2 := by
  simp [gaussianHermiteHilbertBasis, ComplexHermite.hermiteL2Family,
    multivariateNormalizedL2]

end
end GinibrePoincare
