/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianHermiteMoments.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MultivariateHermiteMonomialSpan
public import LeanPool.GinibrePoincare.Analysis.GaussianPolynomialCompleteness
public import LeanPool.GinibrePoincare.Analysis.GaussianPolynomialDensity

/-! # Polynomial Gaussian `L²` vectors and Hermite moments -/


@[expose] public section


open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace GinibrePoincare

noncomputable section

open ComplexHermite

/-- All coordinate/conjugate-coordinate monomials, as pointwise functions. -/
def configurationMixedMonomialSpan (n : ℕ) :
    Submodule ℂ (Configuration n → ℂ) :=
  Submodule.span ℂ {f | ∃ p q : Fin n → ℕ,
    f = fun z ↦ ∏ i, z i ^ p i * (conj (z i)) ^ q i}

private theorem configurationMixedMonomialSpan_one (n : ℕ) :
    (1 : Configuration n → ℂ) ∈ configurationMixedMonomialSpan n := by
  apply Submodule.subset_span
  refine ⟨0, 0, ?_⟩
  funext z
  simp

private theorem configurationMixedMonomialSpan_mul {n : ℕ}
    {f g : Configuration n → ℂ}
    (hf : f ∈ configurationMixedMonomialSpan n)
    (hg : g ∈ configurationMixedMonomialSpan n) :
    f * g ∈ configurationMixedMonomialSpan n := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨p, q, rfl⟩
      induction hg using Submodule.span_induction with
      | mem g hg =>
          rcases hg with ⟨r, s, rfl⟩
          apply Submodule.subset_span
          refine ⟨p + r, q + s, ?_⟩
          funext z
          simp only [Pi.add_apply, Pi.mul_apply, pow_add]
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro i hi
          ring
      | zero => simp
      | add x y hx hy ihx ihy => simpa [mul_add] using
          (configurationMixedMonomialSpan n).add_mem ihx ihy
      | smul c x hx ih =>
          simpa [Pi.smul_apply, smul_eq_mul, mul_assoc] using
            (configurationMixedMonomialSpan n).smul_mem c ih
  | zero => simp
  | add x y hx hy ihx ihy => simpa [add_mul] using
      (configurationMixedMonomialSpan n).add_mem ihx ihy
  | smul c x hx ih =>
      simpa [Pi.smul_apply, smul_eq_mul, mul_assoc] using
        (configurationMixedMonomialSpan n).smul_mem c ih

private theorem configurationMixedMonomialSpan_pow {n : ℕ}
    {f : Configuration n → ℂ} (hf : f ∈ configurationMixedMonomialSpan n)
    (k : ℕ) : f ^ k ∈ configurationMixedMonomialSpan n := by
  induction k with
  | zero => simpa using configurationMixedMonomialSpan_one n
  | succ k ih => simpa [pow_succ] using configurationMixedMonomialSpan_mul ih hf

theorem configurationRealPairing_complex_mem_mixedMonomialSpan {n : ℕ}
    (t : Configuration n) :
    (fun z ↦ (configurationRealPairing t z : ℂ)) ∈
      configurationMixedMonomialSpan n := by
  rw [show (fun z ↦ (configurationRealPairing t z : ℂ)) =
      ∑ i : Fin n, (2 : ℂ)⁻¹ •
        ((conj (t i)) • (fun z : Configuration n ↦ z i) +
          (t i) • (fun z : Configuration n ↦ conj (z i))) by
    funext z
    apply Complex.ext <;>
      simp [configurationRealPairing, Finset.sum_apply] <;> ring_nf
    all_goals simp]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨Function.update 0 i 1, 0, ?_⟩
    funext z
    simp [Function.update_apply, apply_ite]
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨0, Function.update 0 i 1, ?_⟩
    funext z
    simp [Function.update_apply, apply_ite]

/-- Every pointwise polynomial in coordinates and conjugate coordinates is
`L²`, and its `L²` class lies in the algebraic Hermite span. -/
theorem mixedMonomialSpan_toLp_mem_gaussianHermiteSpan (n : ℕ) (hn : 0 < n)
    {f : Configuration n → ℂ} (hf : f ∈ configurationMixedMonomialSpan n) :
    ∃ hmem : MemLp f 2 (complexGaussianMeasure n),
      hmem.toLp f ∈ gaussianHermiteSpan n hn := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨p, q, rfl⟩
      have hpoint : (fun z : Configuration n ↦
          ∏ i, z i ^ p i * (conj (z i)) ^ q i) ∈
          multivariateNormalizedRectangleSpan n hn p q := by
        rw [multivariateNormalizedRectangleSpan_eq_mixedMonomialRectangleSpan]
        apply Submodule.subset_span
        exact ⟨p, q, fun _ ↦ le_rfl, fun _ ↦ le_rfl, rfl⟩
      have lift : ∀ {F : Configuration n → ℂ},
          F ∈ multivariateNormalizedRectangleSpan n hn p q →
          ∃ hmem : MemLp F 2 (complexGaussianMeasure n),
            hmem.toLp F ∈ gaussianHermiteSpan n hn := by
        intro F hF
        induction hF using Submodule.span_induction with
        | mem g hg =>
            rcases hg with ⟨a, b, ha, hb, rfl⟩
            exact ⟨memLp_two_multivariateNormalized n hn a b,
              multivariateNormalizedL2_mem_span n hn a b⟩
        | zero => exact ⟨MemLp.zero, by simp⟩
        | add x y hx hy ihx ihy =>
            rcases ihx with ⟨hxmem, hxspan⟩
            rcases ihy with ⟨hymem, hyspan⟩
            refine ⟨hxmem.add hymem, ?_⟩
            rw [MemLp.toLp_add hxmem hymem]
            exact (gaussianHermiteSpan n hn).add_mem hxspan hyspan
        | smul c x hx ih =>
            rcases ih with ⟨hxmem, hxspan⟩
            refine ⟨hxmem.const_smul c, ?_⟩
            rw [MemLp.toLp_const_smul c hxmem]
            exact (gaussianHermiteSpan n hn).smul_mem c hxspan
      exact lift hpoint
  | zero => exact ⟨MemLp.zero, by simp⟩
  | add x y hx hy ihx ihy =>
      rcases ihx with ⟨hxmem, hxspan⟩
      rcases ihy with ⟨hymem, hyspan⟩
      refine ⟨hxmem.add hymem, ?_⟩
      rw [MemLp.toLp_add hxmem hymem]
      exact (gaussianHermiteSpan n hn).add_mem hxspan hyspan
  | smul c x hx ih =>
      rcases ih with ⟨hxmem, hxspan⟩
      refine ⟨hxmem.const_smul c, ?_⟩
      rw [MemLp.toLp_const_smul c hxmem]
      exact (gaussianHermiteSpan n hn).smul_mem c hxspan

/-- A coordinate/conjugate-coordinate monomial belongs to Gaussian `L²`. -/
theorem memLp_two_multivariateMixedMonomial (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) :
    MemLp (fun z : Configuration n ↦
      ∏ i, z i ^ p i * (conj (z i)) ^ q i) 2
      (complexGaussianMeasure n) := by
  apply (mixedMonomialSpan_toLp_mem_gaussianHermiteSpan n hn ?_).choose
  apply Submodule.subset_span
  exact ⟨p, q, rfl⟩

/-- A coordinate/conjugate-coordinate monomial packaged in Gaussian `L²`. -/
def multivariateMixedMonomialL2 (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) : Lp ℂ 2 (complexGaussianMeasure n) :=
  (memLp_two_multivariateMixedMonomial n hn p q).toLp
    (fun z : Configuration n ↦
      ∏ i, z i ^ p i * (conj (z i)) ^ q i)

theorem multivariateMixedMonomialL2_mem_gaussianHermiteSpan
    (n : ℕ) (hn : 0 < n) (p q : Fin n → ℕ) :
    multivariateMixedMonomialL2 n hn p q ∈ gaussianHermiteSpan n hn := by
  have hgen : (fun z : Configuration n ↦
      ∏ i, z i ^ p i * (conj (z i)) ^ q i) ∈
      configurationMixedMonomialSpan n := by
    apply Submodule.subset_span
    exact ⟨p, q, rfl⟩
  obtain ⟨hmem, hspan⟩ :=
    mixedMonomialSpan_toLp_mem_gaussianHermiteSpan n hn hgen
  simpa [multivariateMixedMonomialL2] using hspan

/-- Every power of a directional real pairing, with the Fourier factor
`I^k`, represents a vector in the Hermite span. -/
theorem exists_memLp_lineMomentPolynomial_mem_gaussianHermiteSpan
    (n : ℕ) (hn : 0 < n) (t : Configuration n) (k : ℕ) :
    ∃ hmem : MemLp (fun z ↦
        ((configurationRealPairing t z : ℂ) * Complex.I) ^ k) 2
        (complexGaussianMeasure n),
      hmem.toLp (fun z ↦
        ((configurationRealPairing t z : ℂ) * Complex.I) ^ k) ∈
        gaussianHermiteSpan n hn := by
  apply mixedMonomialSpan_toLp_mem_gaussianHermiteSpan n hn
  have hp := configurationMixedMonomialSpan_pow
    (configurationRealPairing_complex_mem_mixedMonomialSpan t) k
  convert (configurationMixedMonomialSpan n).smul_mem (Complex.I ^ k) hp using 1
  ext z
  simp [mul_pow, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Orthogonality to every normalized Hermite tensor forces every
directional Fourier moment to vanish. -/
theorem gaussianL2LineMoment_eq_zero_of_orthogonal_hermites
    (n : ℕ) (hn : 0 < n)
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (horth : ∀ p q : Fin n → ℕ,
      inner ℂ (multivariateNormalizedL2 n hn p q) v = 0)
    (t : Configuration n) (k : ℕ) :
    gaussianL2LineMoment v t k = 0 := by
  have hspan : ∀ x ∈ gaussianHermiteSpan n hn, inner ℂ x v = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨⟨p, q⟩, rfl⟩
        exact horth p q
    | zero => simp
    | add x y hx hy ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
    | smul c x hx ih => rw [inner_smul_left, ih, mul_zero]
  let nt : Configuration n := -t
  obtain ⟨hmem, hmemSpan⟩ :=
    exists_memLp_lineMomentPolynomial_mem_gaussianHermiteSpan n hn nt k
  have hz := hspan _ hmemSpan
  rw [MeasureTheory.L2.inner_def] at hz
  rw [gaussianL2LineMoment]
  calc
    ∫ z, v z * ((configurationRealPairing t z : ℂ) * Complex.I) ^ k
        ∂complexGaussianMeasure n =
        ∫ z, inner ℂ (hmem.toLp (fun z ↦
          ((configurationRealPairing nt z : ℂ) * Complex.I) ^ k) z) (v z)
          ∂complexGaussianMeasure n := by
            apply integral_congr_ae
            filter_upwards [hmem.coeFn_toLp] with z hzmem
            rw [hzmem, RCLike.inner_apply]
            have hneg : configurationRealPairing nt z =
                -configurationRealPairing t z := by
              unfold nt configurationRealPairing
              simp only [Pi.neg_apply, Complex.neg_re, Complex.neg_im,
                neg_mul, ← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              ring
            rw [hneg]
            simp only [map_pow, map_mul, Complex.conj_ofReal, Complex.conj_I]
            simp [mul_pow]
    _ = 0 := hz

private def complexPairingCLM (t : ℂ) : ℂ →L[ℝ] ℝ :=
  t.re • Complex.reCLM + t.im • Complex.imCLM

@[simp] private theorem complexPairingCLM_apply (t z : ℂ) :
    complexPairingCLM t z = t.re * z.re + t.im * z.im := by
  simp [complexPairingCLM]

private theorem integrable_exp_mul_complexPairing (n : ℕ) (t : ℂ) (r : ℝ) :
    Integrable (fun z : ℂ ↦ Real.exp (r * complexPairingCLM t z))
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  let μ : Measure ℂ := complexCoordinateGaussianProbability n
  let : ProbabilityTheory.IsGaussian μ :=
    isGaussian_complexCoordinateGaussianProbability n
  let L := complexPairingCLM t
  have hg := ProbabilityTheory.integrable_exp_mul_gaussianReal
    (t := r) (μ := ∫ z, L z ∂μ) (v := (ProbabilityTheory.variance L μ).toNNReal)
  rw [← ProbabilityTheory.IsGaussian.map_eq_gaussianReal L] at hg
  exact hg.comp_aemeasurable L.continuous.aemeasurable

/-- Every real exponential of a directional pairing is Gaussian-integrable. -/
theorem integrable_exp_mul_configurationRealPairing
    (n : ℕ) (t : Configuration n) (r : ℝ) :
    Integrable (fun z ↦ Real.exp (r * configurationRealPairing t z))
      (complexGaussianMeasure n) := by
  unfold complexGaussianMeasure complexGaussianProbability configurationRealPairing
  simp only [ProbabilityMeasure.toMeasure_pi]
  rw [show (fun z : Configuration n ↦
      Real.exp (r * ∑ i, ((t i).re * (z i).re + (t i).im * (z i).im))) =
      fun z ↦ ∏ i, Real.exp (r * complexPairingCLM (t i) (z i)) by
    funext z
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 1]
  exact Integrable.fintype_prod fun i ↦
    integrable_exp_mul_complexPairing n (t i) r

/-- Absolute linear exponentials of a directional pairing are integrable. -/
theorem integrable_exp_mul_abs_configurationRealPairing
    (n : ℕ) (t : Configuration n) (r : ℝ) :
    Integrable (fun z ↦ Real.exp (r * |configurationRealPairing t z|))
      (complexGaussianMeasure n) :=
  ProbabilityTheory.integrable_exp_mul_abs
    (integrable_exp_mul_configurationRealPairing n t r)
    (integrable_exp_mul_configurationRealPairing n t (-r))

/-- Terms of the exponential expansion of the Fourier test. -/
def gaussianL2FourierSeriesTerm {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n)
    (k : ℕ) (z : Configuration n) : ℂ :=
  v z * (((configurationRealPairing t z : ℂ) * Complex.I) ^ k /
    (k.factorial : ℂ))

theorem hasSum_gaussianL2FourierSeriesTerm {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t z : Configuration n) :
    HasSum (fun k ↦ gaussianL2FourierSeriesTerm v t k z)
      (v z * configurationFourierCharacter t z) := by
  unfold gaussianL2FourierSeriesTerm configurationFourierCharacter
  simpa [Complex.exp_eq_exp_ℂ] using
    (NormedSpace.expSeries_div_hasSum_exp
      ((configurationRealPairing t z : ℂ) * Complex.I)).mul_left (v z)

private theorem memLp_two_exp_abs_configurationRealPairing {n : ℕ}
    (t : Configuration n) :
    MemLp (fun z ↦ Real.exp |configurationRealPairing t z|) 2
      (complexGaussianMeasure n) := by
  rw [memLp_two_iff_integrable_sq_norm]
  · convert integrable_exp_mul_abs_configurationRealPairing n t 2 using 1
    funext z
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  · exact (Real.continuous_exp.comp
      (continuous_configurationRealPairing_left t).abs).aestronglyMeasurable

private theorem integrable_fourierSeriesMajorant {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n) :
    Integrable (fun z ↦ ‖v z‖ * Real.exp |configurationRealPairing t z|)
      (complexGaussianMeasure n) := by
  exact (Lp.memLp v).norm.integrable_mul
    (memLp_two_exp_abs_configurationRealPairing t)

/-- The termwise Fourier-series integrals sum to the Fourier test. -/
theorem hasSum_integral_gaussianL2FourierSeriesTerm {n : ℕ}
    (v : Lp ℂ 2 (complexGaussianMeasure n)) (t : Configuration n) :
    HasSum (fun k ↦ ∫ z, gaussianL2FourierSeriesTerm v t k z
        ∂complexGaussianMeasure n)
      (gaussianL2FourierTest v t) := by
  have hdom := integrable_fourierSeriesMajorant v t
  have hsbound : ∀ z : Configuration n,
      HasSum (fun k : ℕ ↦ ‖v z‖ *
        (|configurationRealPairing t z| ^ k / k.factorial))
        (‖v z‖ * Real.exp |configurationRealPairing t z|) := by
    intro z
    simpa [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp
        |configurationRealPairing t z|).mul_left ‖v z‖
  have hs := MeasureTheory.hasSum_integral_of_dominated_convergence
    (fun k z ↦ ‖v z‖ *
      (|configurationRealPairing t z| ^ k / k.factorial))
    (F := fun k z ↦ gaussianL2FourierSeriesTerm v t k z)
    (f := fun z ↦ v z * configurationFourierCharacter t z)
    (fun k ↦
      ((Lp.aestronglyMeasurable v).mul
        (((((Complex.continuous_ofReal.comp
          (continuous_configurationRealPairing_left t)).mul continuous_const).pow k).div_const
            _).aestronglyMeasurable)))
    (fun k ↦ Filter.Eventually.of_forall fun z ↦ by
      simp [gaussianL2FourierSeriesTerm, Real.norm_eq_abs])
    (Filter.Eventually.of_forall fun z ↦ (hsbound z).summable)
    (by simpa only [(hsbound _).tsum_eq] using hdom)
    (Filter.Eventually.of_forall fun z ↦
      hasSum_gaussianL2FourierSeriesTerm v t z)
  simpa [gaussianL2FourierTest] using hs

/-- Orthogonality to every Hermite tensor makes the full Gaussian Fourier
test vanish at every frequency. -/
theorem gaussianL2FourierTest_eq_zero_of_orthogonal_hermites
    (n : ℕ) (hn : 0 < n)
    (v : Lp ℂ 2 (complexGaussianMeasure n))
    (horth : ∀ p q : Fin n → ℕ,
      inner ℂ (multivariateNormalizedL2 n hn p q) v = 0)
    (t : Configuration n) : gaussianL2FourierTest v t = 0 := by
  have hs := hasSum_integral_gaussianL2FourierSeriesTerm v t
  have hz : ∀ k : ℕ,
      (∫ z, gaussianL2FourierSeriesTerm v t k z
        ∂complexGaussianMeasure n) = 0 := by
    intro k
    unfold gaussianL2FourierSeriesTerm
    rw [show (∫ z, v z *
        (((configurationRealPairing t z : ℂ) * Complex.I) ^ k /
          (k.factorial : ℂ)) ∂complexGaussianMeasure n) =
        gaussianL2LineMoment v t k / (k.factorial : ℂ) by
      rw [gaussianL2LineMoment]
      rw [show (fun z ↦ v z *
          (((configurationRealPairing t z : ℂ) * Complex.I) ^ k /
            (k.factorial : ℂ))) = fun z ↦
          (v z * ((configurationRealPairing t z : ℂ) * Complex.I) ^ k) /
            (k.factorial : ℂ) by funext z; ring]
      rw [integral_div]]
    rw [gaussianL2LineMoment_eq_zero_of_orthogonal_hermites n hn v horth t k]
    simp
  simpa [hz] using hs.tsum_eq.symm

end
end GinibrePoincare
