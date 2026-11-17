/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GroundStateDbar.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreMassFiniteness
public import LeanPool.GinibrePoincare.Concrete.AnalyticStatements

/-! # The Vandermonde ground-state transform and `dbar`

Complex differentiability makes the coordinate dbar derivative of the
Vandermonde vanish. The product rule therefore differentiates only the
observable in the normalized ground-state transform. Squaring, summing and
integrating gives the factor-four Dirichlet identity. Compact support and
Gaussian integrability also establish admissibility of the transformed
centered observable; these are the two analytic inputs used by the original
smooth-core Poincaré proof.
-/


@[expose] public section


open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace GinibrePoincare

noncomputable section

/-- The Vandermonde polynomial is holomorphic on configuration space. -/
theorem differentiable_vandermonde (n : ℕ) :
    Differentiable ℂ (fun z : Configuration n ↦ vandermonde z) := by
  rw [show (fun z : Configuration n ↦ vandermonde z) =
      fun z ↦ ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (z j - z i) by
    funext z
    rw [vandermonde_eq_product]]
  fun_prop

/-- A complex-differentiable function has vanishing coordinate `dbar`. -/
theorem dbarComponent_eq_zero_of_differentiable_complex {n : ℕ}
    {g : Configuration n → ℂ} (hg : Differentiable ℂ g)
    (k : Fin n) (z : Configuration n) :
    dbarComponent g k z = 0 := by
  rw [dbarComponent, (hg z).fderiv_restrictScalars ℝ]
  have hi : imaginaryCoordinateDirection k =
      Complex.I • realCoordinateDirection k := by
    ext j
    by_cases hj : j = k <;>
      simp [realCoordinateDirection, imaginaryCoordinateDirection,
        coordinateDirection, hj]
  change (1 / 2 : ℂ) *
    ((fderiv ℂ g z) (realCoordinateDirection k) +
      Complex.I * (fderiv ℂ g z) (imaginaryCoordinateDirection k)) = 0
  rw [hi, (fderiv ℂ g z).map_smul]
  have hI (x : ℂ) : Complex.I * (Complex.I * x) = -x := by
    rw [← mul_assoc, Complex.I_mul_I]
    simp
  change (1 / 2 : ℂ) *
    ((fderiv ℂ g z) (realCoordinateDirection k) +
      Complex.I * (Complex.I *
        (fderiv ℂ g z) (realCoordinateDirection k))) = 0
  rw [hI]
  ring

/-- Every coordinate `dbar` derivative of the Vandermonde vanishes. -/
@[simp] theorem dbarComponent_vandermonde {n : ℕ}
    (k : Fin n) (z : Configuration n) :
    dbarComponent (fun w : Configuration n ↦ vandermonde w) k z = 0 :=
  dbarComponent_eq_zero_of_differentiable_complex
    (differentiable_vandermonde n) k z

/-- Product rule for the concrete coordinate `dbar` operator. -/
theorem dbarComponent_mul {n : ℕ} {f g : Configuration n → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (k : Fin n) (z : Configuration n) :
    dbarComponent (fun w ↦ f w * g w) k z =
      dbarComponent f k z * g z + f z * dbarComponent g k z := by
  change dbarComponent (f * g) k z = _
  rw [dbarComponent, dbarComponent, dbarComponent,
    fderiv_mul (hf z) (hg z)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Multiplication by a holomorphic factor commutes with `dbar`. -/
theorem dbarComponent_holomorphic_mul {n : ℕ}
    {h g : Configuration n → ℂ} (hh : Differentiable ℂ h)
    (hg : Differentiable ℝ g) (k : Fin n) (z : Configuration n) :
    dbarComponent (fun w ↦ h w * g w) k z =
      h z * dbarComponent g k z := by
  rw [dbarComponent_mul (hh.restrictScalars ℝ) hg,
    dbarComponent_eq_zero_of_differentiable_complex hh]
  simp

/-- Exact product rule for the normalized Vandermonde transform. -/
theorem dbarComponent_normalizedVandermondeTransform {n : ℕ}
    {g : Configuration n → ℂ} (hg : Differentiable ℝ g)
    (k : Fin n) (z : Configuration n) :
    dbarComponent (normalizedVandermondeTransform n g) k z =
      ((groundStateNormalization n : ℂ)⁻¹ * vandermonde z) *
        dbarComponent g k z := by
  rw [show normalizedVandermondeTransform n g = fun w ↦
      (((groundStateNormalization n : ℂ)⁻¹ * vandermonde w) * g w) by
    funext w
    exact normalizedVandermondeTransform_apply n g w]
  apply dbarComponent_holomorphic_mul
  · exact (differentiable_const (c := (groundStateNormalization n : ℂ)⁻¹)).mul
      (differentiable_vandermonde n)
  · exact hg

/-- Pointwise squared `dbar` norm under the normalized ground-state transform. -/
theorem dbarNormSq_normalizedVandermondeTransform {n : ℕ}
    {g : Configuration n → ℂ} (hg : Differentiable ℝ g)
    (z : Configuration n) :
    dbarNormSq (normalizedVandermondeTransform n g) z =
      Complex.normSq ((groundStateNormalization n : ℂ)⁻¹) *
        vandermondeWeight z * dbarNormSq g z := by
  unfold dbarNormSq
  simp_rw [dbarComponent_normalizedVandermondeTransform hg,
    Complex.normSq_mul]
  unfold vandermondeWeight
  rw [Finset.mul_sum]

/-- The squared normalization multiplier is the reciprocal of the actual
Vandermonde mass. -/
theorem normSq_groundStateNormalization_inv (n : ℕ) :
    Complex.normSq ((groundStateNormalization n : ℂ)⁻¹) =
      (ginibreNormalizingMass n).toReal⁻¹ := by
  rw [Complex.normSq_inv, Complex.normSq_ofReal]
  rw [← pow_two]
  unfold groundStateNormalization
  rw [Real.sq_sqrt ENNReal.toReal_nonneg]

/-- Pointwise ground-state scaling, expressed using the normalizing mass. -/
theorem dbarNormSq_normalizedVandermondeTransform_mass {n : ℕ}
    {g : Configuration n → ℂ} (hg : Differentiable ℝ g)
    (z : Configuration n) :
    dbarNormSq (normalizedVandermondeTransform n g) z =
      (ginibreNormalizingMass n).toReal⁻¹ * vandermondeWeight z *
        dbarNormSq g z := by
  rw [dbarNormSq_normalizedVandermondeTransform hg,
    normSq_groundStateNormalization_inv n]

/-- Coordinate formula for `dbar` of a complexified real function. -/
theorem dbarComponent_ofReal {n : ℕ} {f : Configuration n → ℝ}
    (hf : Differentiable ℝ f) (k : Fin n) (z : Configuration n) :
    dbarComponent (fun w ↦ (f w : ℂ)) k z =
      (1 / 2 : ℂ) *
        (((fderiv ℝ f z (realCoordinateDirection k) : ℝ) : ℂ) +
          Complex.I *
            ((fderiv ℝ f z (imaginaryCoordinateDirection k) : ℝ) : ℂ)) := by
  unfold dbarComponent
  rw [show (fun w ↦ (f w : ℂ)) = Complex.ofRealCLM ∘ f by rfl,
    fderiv_comp z Complex.ofRealCLM.differentiableAt (hf z),
    Complex.ofRealCLM.fderiv]
  rfl

/-- Squared coordinate `dbar` norm of a complexified real function. -/
theorem normSq_dbarComponent_ofReal {n : ℕ} {f : Configuration n → ℝ}
    (hf : Differentiable ℝ f) (k : Fin n) (z : Configuration n) :
    Complex.normSq (dbarComponent (fun w ↦ (f w : ℂ)) k z) =
      (1 / 4 : ℝ) *
        ((fderiv ℝ f z (realCoordinateDirection k)) ^ 2 +
          (fderiv ℝ f z (imaginaryCoordinateDirection k)) ^ 2) := by
  rw [dbarComponent_ofReal hf]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num
  ring

/-- Sum-of-coordinate-squares formula for the `dbar` norm of a complexified
real function. -/
theorem dbarNormSq_ofReal {n : ℕ} {f : Configuration n → ℝ}
    (hf : Differentiable ℝ f) (z : Configuration n) :
    dbarNormSq (fun w ↦ (f w : ℂ)) z =
      (1 / 4 : ℝ) * ∑ k : Fin n,
        ((fderiv ℝ f z (realCoordinateDirection k)) ^ 2 +
          (fderiv ℝ f z (imaginaryCoordinateDirection k)) ^ 2) := by
  unfold dbarNormSq
  simp_rw [normSq_dbarComponent_ofReal hf]
  rw [Finset.mul_sum]

/-- In the concrete Euclidean-coordinate definition, complexification turns
the real gradient square into four times the `dbar` square. -/
theorem dbarNormSq_ofReal_eq_realGradientNormSq {n : ℕ}
    {f : Configuration n → ℝ} (hf : Differentiable ℝ f)
    (z : Configuration n) :
    dbarNormSq (fun w ↦ (f w : ℂ)) z =
      (1 / 4 : ℝ) * realGradientNormSq f z := by
  rw [dbarNormSq_ofReal hf]
  rfl

/-- Integration against the normalized Ginibre measure is normalized
Vandermonde-weighted Gaussian integration. -/
theorem integral_ginibreMeasure (n : ℕ) (h : Configuration n → ℝ) :
    ∫ z, h z ∂ginibreMeasure n =
      (ginibreNormalizingMass n).toReal⁻¹ *
        ∫ z, vandermondeWeight z * h z ∂complexGaussianMeasure n := by
  unfold ginibreMeasure rawGinibreMeasure
  rw [integral_smul_measure, ENNReal.toReal_inv]
  rw [integral_withDensity_eq_integral_toReal_smul
    measurable_vandermondeDensity
    (ae_of_all _ fun z ↦ ENNReal.ofReal_lt_top)]
  simp_rw [vandermondeDensity,
    ENNReal.toReal_ofReal (vandermondeWeight_nonneg _), smul_eq_mul]

/-- Centering does not change the real Fréchet derivative. -/
theorem fderiv_centeredObservable {n : ℕ} {f : Configuration n → ℝ}
    (hf : Differentiable ℝ f) (z : Configuration n) :
    fderiv ℝ (centeredObservable n f) z = fderiv ℝ f z := by
  unfold centeredObservable
  change fderiv ℝ (f - fun _ ↦ smoothGinibreMean n f) z = _
  rw [fderiv_sub (hf z) (differentiableAt_const _)]
  simp

/-- Centering does not change the pointwise gradient square. -/
theorem realGradientNormSq_centeredObservable {n : ℕ}
    {f : Configuration n → ℝ} (hf : Differentiable ℝ f)
    (z : Configuration n) :
    realGradientNormSq (centeredObservable n f) z =
      realGradientNormSq f z := by
  unfold realGradientNormSq
  rw [fderiv_centeredObservable hf]

/-- Fully expanded pointwise ground-state identity for a real observable. -/
theorem dbarNormSq_normalizedVandermondeTransform_ofReal {n : ℕ}
    {f : Configuration n → ℝ} (hf : Differentiable ℝ f)
    (z : Configuration n) :
    dbarNormSq
        (normalizedVandermondeTransform n (fun w ↦ (f w : ℂ))) z =
      (ginibreNormalizingMass n).toReal⁻¹ * vandermondeWeight z *
        ((1 / 4 : ℝ) * ∑ k : Fin n,
          ((fderiv ℝ f z (realCoordinateDirection k)) ^ 2 +
            (fderiv ℝ f z (imaginaryCoordinateDirection k)) ^ 2)) := by
  have hfc : Differentiable ℝ (fun w ↦ (f w : ℂ)) := by
    fun_prop
  rw [dbarNormSq_normalizedVandermondeTransform_mass hfc,
    dbarNormSq_ofReal hf]

/-- Pointwise ground-state identity specialized to a centered smooth real
observable. -/
theorem dbarNormSq_normalized_centeredObservable {n : ℕ}
    {f : Configuration n → ℝ} (hf : Differentiable ℝ f)
    (z : Configuration n) :
    dbarNormSq
        (normalizedVandermondeTransform n
          (fun w ↦ (centeredObservable n f w : ℂ))) z =
      (ginibreNormalizingMass n).toReal⁻¹ * vandermondeWeight z *
        ((1 / 4 : ℝ) * realGradientNormSq f z) := by
  have hc : Differentiable ℝ (centeredObservable n f) := by
    unfold centeredObservable
    fun_prop
  rw [dbarNormSq_normalizedVandermondeTransform_ofReal hc]
  rw [fderiv_centeredObservable hf]
  rfl

/-- Exact Dirichlet-form identity under the normalized Vandermonde
ground-state transform. -/
theorem groundStateEnergyIdentity : GroundStateEnergyIdentityStatement := by
  intro n hn hprob f hf
  have hdiff : Differentiable ℝ f := hf.1.differentiable (by simp)
  unfold smoothGinibreEnergy gaussianDbarEnergy
  rw [integral_ginibreMeasure]
  have hint :
      (∫ z,
          dbarNormSq
            (normalizedVandermondeTransform n
              (fun w ↦ (centeredObservable n f w : ℂ))) z
          ∂complexGaussianMeasure n) =
        (ginibreNormalizingMass n).toReal⁻¹ * (1 / 4 : ℝ) *
          ∫ z, vandermondeWeight z * realGradientNormSq f z
            ∂complexGaussianMeasure n := by
    calc
      _ = ∫ z,
          (ginibreNormalizingMass n).toReal⁻¹ *
            ((1 / 4 : ℝ) *
              (vandermondeWeight z * realGradientNormSq f z))
          ∂complexGaussianMeasure n := by
            apply integral_congr_ae
            filter_upwards with z
            rw [dbarNormSq_normalized_centeredObservable hdiff]
            ring
      _ = _ := by
        rw [integral_const_mul, integral_const_mul]
        ring
  rw [hint]
  ring

/-- A compactly supported continuous factor remains integrable after
multiplication by the Vandermonde weight. -/
theorem integrable_vandermondeWeight_mul_of_compactSupport {n : ℕ}
    {h : Configuration n → ℝ} (hh : Continuous h)
    (hcompact : HasCompactSupport h) :
    Integrable (fun z ↦ vandermondeWeight z * h z)
      (complexGaussianMeasure n) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_normSq.comp continuous_vandermonde).mul hh
  · change HasCompactSupport
      ((vandermondeWeight : Configuration n → ℝ) * h)
    exact hcompact.mul_left

/-- A centered compactly supported smooth observable has an integrable
Vandermonde-weighted square. -/
theorem integrable_vandermondeWeight_mul_centered_sq {n : ℕ}
    {f : Configuration n → ℝ} (hf : Continuous f)
    (hcompact : HasCompactSupport f) :
    Integrable
      (fun z ↦ vandermondeWeight z * (centeredObservable n f z) ^ 2)
      (complexGaussianMeasure n) := by
  have hf1 : Integrable (fun z ↦ vandermondeWeight z * f z)
      (complexGaussianMeasure n) :=
    integrable_vandermondeWeight_mul_of_compactSupport hf hcompact
  have hf2 : Integrable (fun z ↦ vandermondeWeight z * f z ^ 2)
    (complexGaussianMeasure n) :=
    integrable_vandermondeWeight_mul_of_compactSupport
      (hf.pow 2) (by
        apply hcompact.mono
        intro z hz
        simp only [Function.mem_support, ne_eq] at hz ⊢
        intro hzero
        apply hz
        simp [hzero])
  have hv := integrable_vandermondeWeight_complexGaussianMeasure n
  have hmid := hf1.const_mul (2 * smoothGinibreMean n f)
  have hlast := hv.const_mul ((smoothGinibreMean n f) ^ 2)
  have hcomb := (hf2.sub hmid).add hlast
  apply hcomb.congr
  filter_upwards with z
  unfold centeredObservable
  change vandermondeWeight z * f z ^ 2 -
      2 * smoothGinibreMean n f * (vandermondeWeight z * f z) +
        smoothGinibreMean n f ^ 2 * vandermondeWeight z =
    vandermondeWeight z * (f z - smoothGinibreMean n f) ^ 2
  ring

/-- The normalized transform has the expected pointwise squared modulus. -/
theorem normSq_normalizedVandermondeTransform {n : ℕ}
    (g : Configuration n → ℂ) (z : Configuration n) :
    Complex.normSq (normalizedVandermondeTransform n g z) =
      (ginibreNormalizingMass n).toReal⁻¹ * vandermondeWeight z *
        Complex.normSq (g z) := by
  rw [normalizedVandermondeTransform_apply, Complex.normSq_mul,
    Complex.normSq_mul, normSq_groundStateNormalization_inv]
  unfold vandermondeWeight
  ring

/-- The Vandermonde polynomial is real-smooth to every order. -/
theorem contDiff_vandermonde (n : ℕ) :
    ContDiff ℝ ∞ (fun z : Configuration n ↦ vandermonde z) := by
  rw [show (fun z : Configuration n ↦ vandermonde z) =
      fun z ↦ ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (z j - z i) by
    funext z
    rw [vandermonde_eq_product]]
  fun_prop

/-- The normalized transform of a centered smooth function remains smooth. -/
theorem contDiff_normalizedVandermonde_centered {n : ℕ}
    {f : Configuration n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞
      (normalizedVandermondeTransform n
        (fun z ↦ (centeredObservable n f z : ℂ))) := by
  rw [show normalizedVandermondeTransform n
      (fun z ↦ (centeredObservable n f z : ℂ)) = fun z ↦
        ((groundStateNormalization n : ℂ)⁻¹ * vandermonde z) *
          (centeredObservable n f z : ℂ) by
    funext z
    exact normalizedVandermondeTransform_apply n _ z]
  unfold centeredObservable
  have hc : ContDiff ℝ ∞ (fun z ↦ f z - smoothGinibreMean n f) :=
    hf.sub contDiff_const
  exact (contDiff_const.mul (contDiff_vandermonde n)).mul
    (Complex.ofRealCLM.contDiff.comp hc)

theorem contDiff_normalizedVandermonde_ofReal {n : ℕ}
    {f : Configuration n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞
      (normalizedVandermondeTransform n (fun z ↦ (f z : ℂ))) := by
  rw [show normalizedVandermondeTransform n (fun z ↦ (f z : ℂ)) = fun z ↦
      ((groundStateNormalization n : ℂ)⁻¹ * vandermonde z) * (f z : ℂ) by
    funext z
    exact normalizedVandermondeTransform_apply n _ z]
  exact (contDiff_const.mul (contDiff_vandermonde n)).mul
    (Complex.ofRealCLM.contDiff.comp hf)

theorem hasCompactSupport_normalizedVandermonde_ofReal {n : ℕ}
    {f : Configuration n → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport
      (normalizedVandermondeTransform n (fun z ↦ (f z : ℂ))) := by
  rw [show normalizedVandermondeTransform n (fun z ↦ (f z : ℂ)) = fun z ↦
      ((groundStateNormalization n : ℂ)⁻¹ * vandermonde z) * (f z : ℂ) by
    funext z
    exact normalizedVandermondeTransform_apply n _ z]
  have hfC : HasCompactSupport (fun z => (f z : ℂ)) :=
    hf.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  exact hfC.mul_left

theorem gaussianDbarEnergy_normalizedVandermonde_centered_eq_uncentered
    {n : ℕ} {f : Configuration n → ℝ} (hf : Differentiable ℝ f) :
    gaussianDbarEnergy n
        (normalizedVandermondeTransform n
          (fun z ↦ (centeredObservable n f z : ℂ))) =
      gaussianDbarEnergy n
        (normalizedVandermondeTransform n (fun z ↦ (f z : ℂ))) := by
  unfold gaussianDbarEnergy
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [dbarNormSq_normalized_centeredObservable hf,
    dbarNormSq_normalizedVandermondeTransform_ofReal hf]
  rfl

/-- Gaussian square-integrability of the normalized centered transform. -/
theorem isGaussianL2_normalizedVandermonde_centered {n : ℕ}
    {f : Configuration n → ℝ} (hf : Continuous f)
    (hcompact : HasCompactSupport f) :
    IsGaussianL2 n
      (normalizedVandermondeTransform n
        (fun z ↦ (centeredObservable n f z : ℂ))) := by
  unfold IsGaussianL2
  have hi := (integrable_vandermondeWeight_mul_centered_sq hf hcompact).const_mul
    (ginibreNormalizingMass n).toReal⁻¹
  apply hi.congr
  filter_upwards with z
  rw [normSq_normalizedVandermondeTransform]
  simp only [Complex.normSq_ofReal]
  ring

private theorem integrable_vandermondeWeight_mul_fderiv_sq {n : ℕ}
    {f : Configuration n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport f) (v : Configuration n) :
    Integrable (fun z ↦ vandermondeWeight z * (fderiv ℝ f z v) ^ 2)
      (complexGaussianMeasure n) := by
  apply integrable_vandermondeWeight_mul_of_compactSupport
  · exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2
  · apply (hcompact.fderiv_apply ℝ v).mono
    intro z hz
    simp only [Function.mem_support, ne_eq] at hz ⊢
    intro hzero
    apply hz
    simp [hzero]

/-- Each transformed coordinate `dbar` square is Gaussian-integrable. -/
theorem integrable_normSq_dbarComponent_normalized_centered {n : ℕ}
    {f : Configuration n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport f) (k : Fin n) :
    Integrable
      (fun z ↦ Complex.normSq
        (dbarComponent
          (normalizedVandermondeTransform n
            (fun w ↦ (centeredObservable n f w : ℂ))) k z))
      (complexGaussianMeasure n) := by
  have hr := integrable_vandermondeWeight_mul_fderiv_sq hf hcompact
    (realCoordinateDirection k)
  have hi := integrable_vandermondeWeight_mul_fderiv_sq hf hcompact
    (imaginaryCoordinateDirection k)
  have hbase := (hr.add hi).const_mul
    ((ginibreNormalizingMass n).toReal⁻¹ * (1 / 4 : ℝ))
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hcenter : Differentiable ℝ (centeredObservable n f) := by
    unfold centeredObservable
    fun_prop
  have hcenterC : Differentiable ℝ
      (fun w ↦ (centeredObservable n f w : ℂ)) := by fun_prop
  apply hbase.congr
  filter_upwards with z
  rw [dbarComponent_normalizedVandermondeTransform hcenterC,
    Complex.normSq_mul, Complex.normSq_mul,
    normSq_groundStateNormalization_inv]
  unfold vandermondeWeight
  rw [normSq_dbarComponent_ofReal hcenter]
  rw [fderiv_centeredObservable hdiff]
  simp only [Pi.add_apply]
  ring

/-- The normalized Vandermonde transform of every smooth compactly supported
observable satisfies the concrete Gaussian `dbar` form-domain conditions. -/
theorem groundStateAdmissibility : GroundStateAdmissibilityStatement := by
  intro n hn hprob f hf
  refine ⟨contDiff_normalizedVandermonde_centered hf.1,
    isGaussianL2_normalizedVandermonde_centered hf.1.continuous hf.2.1, ?_⟩
  intro k
  exact integrable_normSq_dbarComponent_normalized_centered hf.1 hf.2.1 k

end

end GinibrePoincare
