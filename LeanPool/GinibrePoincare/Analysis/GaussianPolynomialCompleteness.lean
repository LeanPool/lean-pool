/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianPolynomialCompleteness.lean.
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

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import LeanPool.GinibrePoincare.Analysis.MultivariateHermiteIntegrability

/-! # Fourier tests for Gaussian polynomial completeness -/


@[expose] public section


open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace GinibrePoincare

noncomputable section

/-- A product-form Fernique estimate for the finite complex Gaussian law. -/
theorem exists_integrable_exp_sum_normSq_complexGaussianMeasure (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ Integrable
      (fun z : Configuration n ↦ Real.exp (C * ∑ i, ‖z i‖ ^ 2))
      (complexGaussianMeasure n) := by
  let μ : Measure ℂ := complexCoordinateGaussianProbability n
  let : ProbabilityTheory.IsGaussian μ :=
    isGaussian_complexCoordinateGaussianProbability n
  obtain ⟨C, hC, hInt⟩ :=
    ProbabilityTheory.IsGaussian.exists_integrable_exp_sq μ
  refine ⟨C, hC, ?_⟩
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  have hp : Integrable
      (fun z : Configuration n ↦ ∏ i, Real.exp (C * ‖z i‖ ^ 2))
      (Measure.pi fun _ : Fin n ↦ μ) :=
    Integrable.fintype_prod fun _ ↦ hInt
  convert hp using 1
  funext z
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

/-- The standard real Euclidean pairing on complex configuration space. -/
def configurationRealPairing {n : ℕ}
    (t z : Configuration n) : ℝ :=
  ∑ i : Fin n, ((t i).re * (z i).re + (t i).im * (z i).im)

theorem continuous_configurationRealPairing_left {n : ℕ}
    (t : Configuration n) :
    Continuous (configurationRealPairing t) := by
  unfold configurationRealPairing
  fun_prop

theorem configurationRealPairing_add {n : ℕ}
    (s t z : Configuration n) :
    configurationRealPairing (s + t) z =
      configurationRealPairing s z + configurationRealPairing t z := by
  simp only [configurationRealPairing, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Complex.add_re, Complex.add_im]
  ring

/-- Unit-modulus Fourier character associated with a real frequency on
underlying real configuration space. -/
def configurationFourierCharacter {n : ℕ}
    (t z : Configuration n) : ℂ :=
  Complex.exp ((configurationRealPairing t z : ℂ) * Complex.I)

theorem continuous_configurationFourierCharacter {n : ℕ}
    (t : Configuration n) :
    Continuous (configurationFourierCharacter t) := by
  unfold configurationFourierCharacter
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp
      (continuous_configurationRealPairing_left t)).mul continuous_const)

@[simp] theorem norm_configurationFourierCharacter {n : ℕ}
    (t z : Configuration n) :
    ‖configurationFourierCharacter t z‖ = 1 := by
  unfold configurationFourierCharacter
  exact Complex.norm_exp_ofReal_mul_I _

theorem configurationFourierCharacter_add {n : ℕ}
    (s t z : Configuration n) :
    configurationFourierCharacter (s + t) z =
      configurationFourierCharacter s z *
        configurationFourierCharacter t z := by
  unfold configurationFourierCharacter
  rw [configurationRealPairing_add]
  rw [show ((configurationRealPairing s z + configurationRealPairing t z : ℝ) : ℂ) *
      Complex.I = (configurationRealPairing s z : ℂ) * Complex.I +
        (configurationRealPairing t z : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_add _ _

/-- Real scalar multiplication of a complex configuration, made explicit to
avoid changing the ambient scalar field. -/
def realScaleConfiguration {n : ℕ} (r : ℝ) (t : Configuration n) :
    Configuration n := fun i ↦ (r : ℂ) * t i

theorem configurationRealPairing_realScale {n : ℕ}
    (r : ℝ) (t z : Configuration n) :
    configurationRealPairing (realScaleConfiguration r t) z =
      r * configurationRealPairing t z := by
  unfold configurationRealPairing realScaleConfiguration
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.mul_im]
  ring

/-- A fixed real linear coordinate pairing has every finite Gaussian
moment. -/
theorem memLp_configurationRealPairing_of_ne_top {n : ℕ}
    (t : Configuration n) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (configurationRealPairing t) p (complexGaussianMeasure n) := by
  let μ : Measure ℂ := complexCoordinateGaussianProbability n
  let : ProbabilityTheory.IsGaussian μ :=
    isGaussian_complexCoordinateGaussianProbability n
  have hid : MemLp (id : ℂ → ℂ) p μ :=
    ProbabilityTheory.IsGaussian.memLp_id μ p hp
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  unfold configurationRealPairing
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hterm : MemLp (fun z : Configuration n ↦
          (t i).re * (z i).re + (t i).im * (z i).im) p
          (Measure.pi fun _ : Fin n ↦ μ) := by
        have hev : MemLp (fun z : Configuration n ↦ z i) p
            (Measure.pi fun _ : Fin n ↦ μ) := by
          change MemLp (id ∘ Function.eval i) p
            (Measure.pi fun _ : Fin n ↦ μ)
          exact hid.comp_measurePreserving
            (measurePreserving_eval (μ := fun _ : Fin n ↦ μ) i)
        exact (hev.re.const_mul (t i).re).add (hev.im.const_mul (t i).im)
      simp_rw [Finset.sum_insert hi]
      convert hterm.add ih using 1

/-- A fixed real linear coordinate pairing belongs to Gaussian `L²`. -/
theorem memLp_configurationRealPairing {n : ℕ} (t : Configuration n) :
    MemLp (configurationRealPairing t) 2 (complexGaussianMeasure n) :=
  memLp_configurationRealPairing_of_ne_top t 2 (by norm_num)

/-- Cauchy--Schwarz domination required for differentiating the Fourier test
of an arbitrary Gaussian `L²` vector. -/
theorem integrable_norm_mul_abs_configurationRealPairing {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n) :
    Integrable (fun z ↦ ‖v z‖ * |configurationRealPairing t z|)
      (complexGaussianMeasure n) := by
  have h := (Lp.memLp v).norm.integrable_mul
    (memLp_configurationRealPairing t).norm
  convert h using 1

/-- All directional moments of a Gaussian `L²` vector are integrable. -/
theorem integrable_norm_mul_abs_configurationRealPairing_pow {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n) (k : ℕ) :
    Integrable (fun z ↦ ‖v z‖ * |configurationRealPairing t z| ^ k)
      (complexGaussianMeasure n) := by
  cases k with
  | zero =>
      simpa using (Lp.memLp v).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) |>.norm
  | succ k =>
      let q : ℝ≥0∞ := (↑(k + 1) : ℝ≥0∞)
      have hq0 : q ≠ 0 := by simp [q]
      have hqtop : q ≠ ⊤ := by simp [q]
      have hp : MemLp (configurationRealPairing t) (2 * q)
          (complexGaussianMeasure n) :=
        memLp_configurationRealPairing_of_ne_top t (2 * q)
          (ENNReal.mul_ne_top (by norm_num) hqtop)
      have hpow : MemLp (fun z ↦ ‖configurationRealPairing t z‖ ^ q.toReal) 2
          (complexGaussianMeasure n) := by
        have hm := (memLp_norm_rpow_iff
          (continuous_configurationRealPairing_left t).aestronglyMeasurable
          hq0 hqtop).2 hp
        rw [show 2 * q / q = 2 by
          rw [div_eq_mul_inv, mul_assoc,
            ENNReal.mul_inv_cancel hq0 hqtop, mul_one]] at hm
        exact hm
      have hqreal : q.toReal = (k + 1 : ℕ) := by
        rw [show q = (k : ℝ≥0∞) + 1 by simp [q], ENNReal.toReal_add]
        · simp
        · simp
        · simp
      have hpowNat : MemLp (fun z ↦ |configurationRealPairing t z| ^ (k + 1)) 2
          (complexGaussianMeasure n) := by
        convert hpow using 1
        ext z
        rw [hqreal]
        rw [show (↑(k + 1) : ℝ) = (k + 1 : ℕ) by norm_num,
          Real.rpow_natCast]
        simp [Real.norm_eq_abs]
      have h := (Lp.memLp v).norm.integrable_mul hpowNat
      convert h using 1

/-- The `k`th directional Fourier moment of a Gaussian `L²` vector. -/
def gaussianL2LineMoment {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n) (k : ℕ) : ℂ :=
  ∫ z, v z * ((configurationRealPairing t z : ℂ) * Complex.I) ^ k
    ∂complexGaussianMeasure n

theorem integrable_gaussianL2LineMoment_integrand {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n) (k : ℕ) :
    Integrable (fun z ↦ v z *
      ((configurationRealPairing t z : ℂ) * Complex.I) ^ k)
      (complexGaussianMeasure n) := by
  have hmeas : AEStronglyMeasurable (fun z ↦ v z *
      ((configurationRealPairing t z : ℂ) * Complex.I) ^ k)
      (complexGaussianMeasure n) := by
    have hc : Continuous (fun z ↦
        ((configurationRealPairing t z : ℂ) * Complex.I) ^ k) :=
      (((Complex.continuous_ofReal.comp
        (continuous_configurationRealPairing_left t)).mul continuous_const).pow k)
    exact (Lp.aestronglyMeasurable v).mul hc.aestronglyMeasurable
  rw [← integrable_norm_iff hmeas]
  convert integrable_norm_mul_abs_configurationRealPairing_pow v t k using 1
  ext z
  simp [Real.norm_eq_abs]

/-- Fourier line with `k` powers of the directional generator inserted. -/
def gaussianL2FourierMomentLine {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n)
    (k : ℕ) (r : ℝ) : ℂ :=
  ∫ z, (v z * ((configurationRealPairing t z : ℂ) * Complex.I) ^ k) *
      configurationFourierCharacter (realScaleConfiguration r t) z
    ∂complexGaussianMeasure n

/-- Pointwise derivative of a Fourier character along a real frequency
line.  This is the local derivative used by the dominated integral theorem. -/
theorem hasDerivAt_configurationFourierCharacter_line {n : ℕ}
    (r : ℝ) (t z : Configuration n) :
    HasDerivAt (fun s : ℝ ↦
      configurationFourierCharacter (realScaleConfiguration s t) z)
      (((configurationRealPairing t z : ℂ) * Complex.I) *
        configurationFourierCharacter (realScaleConfiguration r t) z) r := by
  rw [show (fun s : ℝ ↦
      configurationFourierCharacter (realScaleConfiguration s t) z) =
      fun s : ℝ ↦ Complex.exp
        ((s : ℂ) * ((configurationRealPairing t z : ℂ) * Complex.I)) by
    funext s
    unfold configurationFourierCharacter
    rw [configurationRealPairing_realScale]
    push_cast
    ring]
  let A : ℂ := (configurationRealPairing t z : ℂ) * Complex.I
  have hinner : HasDerivAt (fun w : ℂ ↦ w * A) A (r : ℂ) := by
    simpa using ((hasDerivAt_id (r : ℂ)).mul_const A)
  have hd : HasDerivAt (fun w : ℂ ↦ Complex.exp (w * A))
      (Complex.exp ((r : ℂ) * A) * A) (r : ℂ) :=
    (Complex.hasDerivAt_exp ((r : ℂ) * A)).comp (r : ℂ)
      hinner
  have hdr := hd.comp_ofReal
  simpa [A, configurationFourierCharacter, configurationRealPairing_realScale,
    mul_comm, mul_left_comm] using hdr

/-- Every Fourier character is in Gaussian `L²`; in fact it lies in every
finite or infinite `Lᵖ` because its norm is one. -/
theorem memLp_configurationFourierCharacter {n : ℕ}
    (t : Configuration n) (p : ℝ≥0∞) :
    MemLp (configurationFourierCharacter t) p
      (complexGaussianMeasure n) := by
  apply MemLp.of_bound
    (continuous_configurationFourierCharacter t).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun z ↦ by simp

/-- The product of a Gaussian `L²` vector with a Fourier character is
integrable.  This is the bounded exponential test needed for the moment
uniqueness argument. -/
theorem integrable_mul_configurationFourierCharacter {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n) :
    Integrable (fun z ↦ v z * configurationFourierCharacter t z)
      (complexGaussianMeasure n) := by
  exact (Lp.memLp v).integrable_mul
    (memLp_configurationFourierCharacter t 2)

/-- Every Hermite moment of a Gaussian `L²` vector is absolutely
integrable.  This supplies the moment side of differentiation under the
Fourier integral. -/
theorem integrable_mul_multivariateNormalized {n : ℕ} (hn : 0 < n)
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (p q : Fin n → ℕ) :
    Integrable (fun z ↦ v z *
      ComplexHermite.multivariateNormalized n hn p q z)
      (complexGaussianMeasure n) := by
  exact (Lp.memLp v).integrable_mul
    (ComplexHermite.memLp_two_multivariateNormalized n hn p q)

/-- Fourier transform of the finite complex measure with density represented
by a Gaussian `L²` vector. -/
def gaussianL2FourierTest {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n) : ℂ :=
  ∫ z, v z * configurationFourierCharacter t z
    ∂complexGaussianMeasure n

/-- The inserted-moment Fourier lines form a derivative ladder. -/
theorem hasDerivAt_gaussianL2FourierMomentLine {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n)
    (k : ℕ) (r : ℝ) :
    HasDerivAt (gaussianL2FourierMomentLine v t k)
      (gaussianL2FourierMomentLine v t (k + 1) r) r := by
  let A : Configuration n → ℂ := fun z ↦
    (configurationRealPairing t z : ℂ) * Complex.I
  let F : ℝ → Configuration n → ℂ := fun s z ↦
    (v z * A z ^ k) * configurationFourierCharacter
      (realScaleConfiguration s t) z
  let F' : ℝ → Configuration n → ℂ := fun s z ↦
    (v z * A z ^ k) * (A z * configurationFourierCharacter
      (realScaleConfiguration s t) z)
  let B : Configuration n → ℝ := fun z ↦
    ‖v z‖ * |configurationRealPairing t z| ^ (k + 1)
  have hbase := integrable_gaussianL2LineMoment_integrand v t k
  have hchar (s : ℝ) : AEStronglyMeasurable
      (configurationFourierCharacter (realScaleConfiguration s t))
      (complexGaussianMeasure n) :=
    (continuous_configurationFourierCharacter
      (realScaleConfiguration s t)).aestronglyMeasurable
  have hFint : Integrable (F r) (complexGaussianMeasure n) := by
    exact hbase.mul_bdd (c := 1) (hchar r)
      (Filter.Eventually.of_forall fun z ↦ by simp)
  have hFmeas : ∀ᶠ s in nhds r,
      AEStronglyMeasurable (F s) (complexGaussianMeasure n) :=
    Filter.Eventually.of_forall fun s ↦
      (hbase.mul_bdd (c := 1) (hchar s)
        (Filter.Eventually.of_forall fun z ↦ by simp)).aestronglyMeasurable
  have hA : Continuous A := by
    unfold A
    exact (Complex.continuous_ofReal.comp
      (continuous_configurationRealPairing_left t)).mul continuous_const
  have hF'meas : AEStronglyMeasurable (F' r)
      (complexGaussianMeasure n) :=
    ((Lp.aestronglyMeasurable v).mul (hA.pow k).aestronglyMeasurable).mul
      (hA.aestronglyMeasurable.mul (hchar r))
  have hbound : ∀ᵐ z ∂complexGaussianMeasure n,
      ∀ s ∈ Set.univ, ‖F' s z‖ ≤ B z := by
    filter_upwards with z s hs
    simp only [Complex.norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, norm_configurationFourierCharacter, pow_succ, F', A, B]
    rw [mul_assoc]
  have hdiff : ∀ᵐ z ∂complexGaussianMeasure n,
      ∀ s ∈ Set.univ, HasDerivAt (F · z) (F' s z) s := by
    filter_upwards with z s hs
    exact (hasDerivAt_configurationFourierCharacter_line s t z).const_mul
      (v z * A z ^ k)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (x₀ := r) (F := F) (F' := F') (bound := B)
    Filter.univ_mem hFmeas hFint hF'meas hbound
    (integrable_norm_mul_abs_configurationRealPairing_pow v t (k + 1)) hdiff
  have hfun : gaussianL2FourierMomentLine v t k =
      fun s ↦ ∫ z, F s z ∂complexGaussianMeasure n := by
    rfl
  rw [hfun]
  have hmom : gaussianL2FourierMomentLine v t (k + 1) r =
      ∫ z, F' r z ∂complexGaussianMeasure n := by
    apply integral_congr_ae
    filter_upwards with z
    simp [F', A, pow_succ, mul_assoc]
  rw [hmom]
  exact h.2

@[simp] theorem configurationFourierCharacter_zero {n : ℕ}
    (z : Configuration n) :
    configurationFourierCharacter 0 z = 1 := by
  simp [configurationFourierCharacter, configurationRealPairing]

theorem gaussianL2FourierTest_zero {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianL2FourierTest v 0 = ∫ z, v z ∂complexGaussianMeasure n := by
  simp [gaussianL2FourierTest]

theorem gaussianL2FourierMomentLine_zero {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n) (k : ℕ) :
    gaussianL2FourierMomentLine v t k 0 = gaussianL2LineMoment v t k := by
  have hzero : realScaleConfiguration 0 t = 0 := by
    ext i
    simp [realScaleConfiguration]
  unfold gaussianL2FourierMomentLine gaussianL2LineMoment
  rw [hzero]
  simp

theorem gaussianL2FourierMomentLine_zeroIndex {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n) (r : ℝ) :
    gaussianL2FourierMomentLine v t 0 r =
      gaussianL2FourierTest v (realScaleConfiguration r t) := by
  simp [gaussianL2FourierMomentLine, gaussianL2FourierTest]

/-- Differentiation of the Gaussian Fourier test along a fixed real
frequency direction. -/
theorem hasDerivAt_gaussianL2FourierTest_line {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n) (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦
      gaussianL2FourierTest v (realScaleConfiguration s t))
      (∫ z, v z * (((configurationRealPairing t z : ℂ) * Complex.I) *
        configurationFourierCharacter (realScaleConfiguration r t) z)
        ∂complexGaussianMeasure n) r := by
  have h := hasDerivAt_gaussianL2FourierMomentLine v t 0 r
  have hfun : gaussianL2FourierMomentLine v t 0 =
      fun s : ℝ ↦ gaussianL2FourierTest v (realScaleConfiguration s t) := by
    funext s
    exact gaussianL2FourierMomentLine_zeroIndex v t s
  rw [hfun] at h
  simpa only [zero_add, gaussianL2FourierMomentLine, pow_one, mul_assoc] using h


end

end GinibrePoincare
