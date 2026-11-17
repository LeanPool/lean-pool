/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreSymmetricWeakPoincare.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreArbitraryWeakPairClosure
public import LeanPool.GinibrePoincare.Endgame.ConcreteTheoremOneNine
public import LeanPool.GinibrePoincare.Analysis.EntropyL2Closure
public import LeanPool.GinibrePoincare.Analysis.EquilibriumProbability
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianMoments
public import LeanPool.GinibrePoincare.Analysis.KostlanProductLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreSmoothDistributionalGradient
public import LeanPool.GinibrePoincare.Analysis.CenterOfMassEigenfunctions

/-!
# Ginibre Symmetric Weak Poincare
-/


@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- The constant function `c`, represented in actual Ginibre `L²`. -/
def ginibreRealConstantL2 (n : ℕ) (hn : 0 < n) (c : ℝ) :
    Lp ℝ 2 (ginibreMeasure n) := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  exact (memLp_const c : MemLp (fun _ : Configuration n => c)
    2 (ginibreMeasure n)).toLp (fun _ => c)

theorem ginibreRealConstantL2_ae (n : ℕ) (hn : 0 < n) (c : ℝ) :
    (ginibreRealConstantL2 n hn c : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun _ => c := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact (memLp_const c : MemLp (fun _ : Configuration n => c)
    2 (ginibreMeasure n)).coeFn_toLp

/-- Mean of an actual Ginibre `L²` class. -/
def ginibreL2Mean (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n)) : ℝ :=
  ∫ z, u z ∂ginibreMeasure n

/-- Variance of an actual Ginibre `L²` class, defined by its centered Hilbert norm. -/
def ginibreL2Variance (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) : ℝ :=
  ‖u - ginibreRealConstantL2 n hn (ginibreL2Mean n u)‖ ^ 2

/-- Dirichlet energy of a distributional weak pair in the paper's normalization. -/
def ginibreWeakEnergy (n : ℕ)
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) : ℝ :=
  (1 / (n : ℝ)) * ‖g‖ ^ 2

theorem ginibreL2Mean_continuous (n : ℕ) (hn : 0 < n) :
    Continuous (ginibreL2Mean n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have h1 : MemLp (fun _ : Configuration n => (1 : ℝ)) 2 (ginibreMeasure n) :=
    memLp_const 1
  have h := continuous_L2_integral_mul (ginibreMeasure n)
    (fun _ : Configuration n => (1 : ℝ)) h1
  have heq : ginibreL2Mean n = fun u => ∫ z, u z * 1 ∂ginibreMeasure n := by
    funext u
    unfold ginibreL2Mean
    congr 1
    funext z
    ring
  rw [heq]
  exact h

theorem ginibreL2Variance_continuous (n : ℕ) (hn : 0 < n) :
    Continuous (ginibreL2Variance n hn) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  let one : Lp ℝ 2 (ginibreMeasure n) :=
    (memLp_const (1 : ℝ) : MemLp (fun _ : Configuration n => (1 : ℝ))
      2 (ginibreMeasure n)).toLp (fun _ => (1 : ℝ))
  have hc : Continuous (fun u : Lp ℝ 2 (ginibreMeasure n) =>
      ginibreL2Mean n u • one) :=
    (ginibreL2Mean_continuous n hn).smul continuous_const
  have hconst (c : ℝ) : ginibreRealConstantL2 n hn c = c • one := by
    apply Lp.ext
    filter_upwards [
      ginibreRealConstantL2_ae n hn c,
      Lp.coeFn_smul c one,
      (memLp_const (1 : ℝ) : MemLp (fun _ : Configuration n => (1 : ℝ))
        2 (ginibreMeasure n)).coeFn_toLp] with z hc hs hone
    rw [hc, hs]
    simp [one]
  have hrepr : ginibreL2Variance n hn = fun u =>
      ‖u - ginibreL2Mean n u • one‖ ^ 2 := by
    funext u
    simp only [ginibreL2Variance, hconst]
  rw [hrepr]
  exact (continuous_norm.comp (continuous_id.sub hc)).pow 2

theorem ginibreWeakEnergy_continuous (n : ℕ) :
    Continuous (ginibreWeakEnergy n) := by
  exact continuous_const.mul (continuous_norm.pow 2)

/-- The sharp Poincaré inequality on the full symmetric distributional weak-H¹ domain. -/
theorem ginibre_symmetric_weak_poincare {n : ℕ} (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ginibreL2Variance n hn u ≤ ginibreWeakEnergy n g / 2 := by
  obtain ⟨q, hq, hqconv⟩ := ginibreSymmetricWeakPair_exists_core_sequence hn u g hg hs
  have hcore (p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
      (hp : p ∈ ginibreTheoremOneNineCorePairs n) :
      ginibreL2Variance n hn p.1 ≤ ginibreWeakEnergy n p.2 / 2 := by
    obtain ⟨f, hf, hv, hgrad⟩ := hp
    let := ginibreMeasure_isProbabilityMeasure hn
    have hmean : ginibreL2Mean n p.1 = smoothGinibreMean n f := by
      unfold ginibreL2Mean smoothGinibreMean
      apply integral_congr_ae
      exact hv
    have hvar : ginibreL2Variance n hn p.1 = smoothGinibreVariance n f := by
      rw [ginibreL2Variance, hmean]
      calc
        ‖p.1 - ginibreRealConstantL2 n hn (smoothGinibreMean n f)‖ ^ 2 =
            ∫ z, (p.1 z - smoothGinibreMean n f) ^ 2 ∂ginibreMeasure n := by
              rw [← integral_square_eq_L2_norm_sq]
              apply integral_congr_ae
              filter_upwards [Lp.coeFn_sub p.1
                  (ginibreRealConstantL2 n hn (smoothGinibreMean n f)),
                hv, ginibreRealConstantL2_ae n hn (smoothGinibreMean n f)]
                with z hsub hz hc
              rw [hsub]
              change ((p.1 : Configuration n → ℝ) z -
                (ginibreRealConstantL2 n hn (smoothGinibreMean n f) :
                  Configuration n → ℝ) z) ^ 2 = _
              rw [hz, hc]
        _ = smoothGinibreVariance n f := by
          unfold smoothGinibreVariance
          apply integral_congr_ae
          filter_upwards [hv] with z hz
          rw [hz]
    have henergy : ginibreWeakEnergy n p.2 = smoothGinibreEnergy n f := by
      rw [ginibreWeakEnergy, ← integral_norm_sq_eq_L2_norm_sq]
      unfold smoothGinibreEnergy
      congr 1
      apply integral_congr_ae
      filter_upwards [hgrad] with z hz
      rw [hz, ginibreEuclideanGradient_norm_sq]
    have hdef := concrete_theoremOneNine hn f hf
    have hm : ∀ k : ℕ, 0 ≤ concretePositiveHermiteModeMass hn f hf k := by
      intro k
      exact sq_nonneg _
    rcases hdef with ⟨hdef, _⟩
    rw [hvar, henergy]
    have htail := modeTail_nonneg (concretePositiveHermiteModeMass hn f hf) hm
    nlinarith [hdef, htail, sq_nonneg (‖centeredObservableL2 hn f hf -
      (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
        (centeredObservableL2 hn f hf) - star
          ((ginibreHolomorphicAmbientClosedSpan n hn).starProjection
            (centeredObservableL2 hn f hf))‖)]
  have hclosed : IsClosed {p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) |
      ginibreL2Variance n hn p.1 ≤ ginibreWeakEnergy n p.2 / 2} := by
    have hcont : Continuous (fun p : Lp ℝ 2 (ginibreMeasure n) ×
        Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) =>
        ginibreWeakEnergy n p.2 / 2 - ginibreL2Variance n hn p.1) := by
      exact (((ginibreWeakEnergy_continuous n).comp continuous_snd).div_const 2).sub
        ((ginibreL2Variance_continuous n hn).comp continuous_fst)
    have heq : {p : Lp ℝ 2 (ginibreMeasure n) ×
        Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) |
        ginibreL2Variance n hn p.1 ≤ ginibreWeakEnergy n p.2 / 2} =
        (fun p : Lp ℝ 2 (ginibreMeasure n) ×
          Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) =>
          ginibreWeakEnergy n p.2 / 2 - ginibreL2Variance n hn p.1) ⁻¹' Set.Ici 0 := by
      ext p
      simp [Set.mem_preimage, Set.mem_Ici, sub_nonneg]
    rw [heq]
    exact isClosed_Ici.preimage hcont
  have hmem : (u, g) ∈ {p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) |
      ginibreL2Variance n hn p.1 ≤ ginibreWeakEnergy n p.2 / 2} :=
    hclosed.mem_of_tendsto hqconv (Eventually.of_forall fun m => hcore (q m) (hq m))
  exact hmem

/-- The real center-of-mass observable is square-integrable for every Ginibre law. -/
theorem memLp_centerOfMassReal (n : ℕ) (hn : 0 < n) :
    MemLp (centerOfMassReal : Configuration n → ℝ) 2 (ginibreMeasure n) := by
  have hgauss : Integrable (fun s : ℂ => ‖s‖ ^ 2) standardComplexGaussianMeasure := by
    simpa [standardComplexGaussianMeasure] using
      (integrable_norm_pow_complexCoordinateGaussianProbability 1 2)
  have hcomp : Integrable (fun z : Configuration n => ‖coordinateSum z‖ ^ 2)
      (ginibreMeasure n) := by
    have hpush : Integrable (fun s : ℂ => ‖s‖ ^ 2)
        ((ginibreMeasure n).map coordinateSum) := by
      rw [coordinateSum_ginibre_gaussian n hn]
      exact hgauss
    exact hpush.comp_aemeasurable (measurable_coordinateSum n).aemeasurable
  have hcont : Continuous (centerOfMassReal : Configuration n → ℝ) := by
    have hsum : (coordinateSum : Configuration n → ℂ) = coordinateSumCLM n := by
      funext z
      exact (coordinateSumCLM_apply n z).symm
    rw [show (centerOfMassReal : Configuration n → ℝ) =
      Complex.reCLM ∘L coordinateSumCLM n by
        funext z
        simp [centerOfMassReal]]
    exact (Complex.reCLM.comp (coordinateSumCLM n)).continuous
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
  apply hcomp.mono'
  · exact (continuous_norm.comp hcont).pow 2 |>.aestronglyMeasurable
  · filter_upwards with z
    change ‖‖centerOfMassReal z‖ ^ 2‖ ≤ ‖coordinateSum z‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb : ‖centerOfMassReal z‖ ≤ ‖coordinateSum z‖ := by
      change |(coordinateSum z).re| ≤ ‖coordinateSum z‖
      exact Complex.abs_re_le_norm _
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hb

/-- Exact first and second real moments of the standard complex Gaussian. -/
theorem standardComplexGaussian_real_moments :
    (∫ s : ℂ, s.re ∂standardComplexGaussianMeasure) = 0 ∧
      (∫ s : ℂ, s.re ^ 2 ∂standardComplexGaussianMeasure) = 1 / 2 := by
  have hfirst : complexGaussianMixedMoment 1 1 0 = 0 := by
    rw [complexGaussianMixedMoment_formula (by norm_num) 1 0]
    norm_num [complexGaussianMixedMoment]
  have hsecond : complexGaussianMixedMoment 1 2 0 = 0 := by
    rw [complexGaussianMixedMoment_formula (by norm_num) 2 0]
    norm_num [complexGaussianMixedMoment]
  have hnorm : (∫ s : ℂ, Complex.normSq s ∂standardComplexGaussianMeasure) = 1 := by
    simpa [standardComplexGaussianMeasure] using integral_normSq_pow_coordinate 1 1 (by norm_num)
  have hi1 : Integrable (fun s : ℂ => s) standardComplexGaussianMeasure := by
    simpa [standardComplexGaussianMeasure, complexGaussianMixedMoment] using
      integrable_mixedComplexMonomial 1 1 0
  have hi2 : Integrable (fun s : ℂ => s ^ 2) standardComplexGaussianMeasure := by
    simpa [standardComplexGaussianMeasure, complexGaussianMixedMoment] using
      integrable_mixedComplexMonomial 1 2 0
  have hfirst' : (∫ s : ℂ, s ∂standardComplexGaussianMeasure) = 0 := by
    unfold complexGaussianMixedMoment at hfirst
    simpa [standardComplexGaussianMeasure] using hfirst
  have hsecond' : (∫ s : ℂ, s ^ 2 ∂standardComplexGaussianMeasure) = 0 := by
    unfold complexGaussianMixedMoment at hsecond
    simpa [standardComplexGaussianMeasure] using hsecond
  constructor
  · calc
      (∫ s : ℂ, s.re ∂standardComplexGaussianMeasure) =
          (∫ s : ℂ, s ∂standardComplexGaussianMeasure).re := integral_re hi1
      _ = 0 := by rw [hfirst']; rfl
  · have hid (s : ℂ) : s.re ^ 2 = (Complex.normSq s + (s ^ 2).re) / 2 := by
      rcases s with ⟨a, b⟩
      have hs : ((⟨a, b⟩ : ℂ) ^ 2).re = a * a - b * b := by
        rw [pow_two, Complex.mul_re]
      rw [Complex.normSq_apply, hs]
      ring
    have hnI : Integrable (fun s : ℂ => Complex.normSq s) standardComplexGaussianMeasure := by
      simpa [standardComplexGaussianMeasure, pow_one] using integrable_normSq_pow_coordinate 1 1
    have hr2 : Integrable (fun s : ℂ => s.re ^ 2) standardComplexGaussianMeasure := by
      apply hnI.mono'
      · fun_prop
      · filter_upwards with s
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s.re), Complex.normSq_apply]
        nlinarith [sq_nonneg s.im]
    have hreal2 := integral_re hi2
    rw [hsecond'] at hreal2
    have hreal2' : (∫ a : ℂ, (a ^ 2).re ∂standardComplexGaussianMeasure) = 0 := by
      simpa using hreal2
    have hadd := integral_add hnI hi2.re
    calc
      (∫ s : ℂ, s.re ^ 2 ∂standardComplexGaussianMeasure) =
          (∫ s : ℂ, (Complex.normSq s + (s ^ 2).re) / 2
            ∂standardComplexGaussianMeasure) := by
              apply integral_congr_ae
              filter_upwards with s
              exact hid s
      _ = 1 / 2 := by
        rw [integral_div]
        rw [show (∫ a : ℂ, Complex.normSq a + (a ^ 2).re
            ∂standardComplexGaussianMeasure) =
          (∫ a : ℂ, Complex.normSq a ∂standardComplexGaussianMeasure) +
            ∫ a : ℂ, (a ^ 2).re ∂standardComplexGaussianMeasure by simpa using hadd]
        rw [hnorm, hreal2']
        norm_num

theorem standardComplexGaussian_imag_moments :
    (∫ s : ℂ, s.im ∂standardComplexGaussianMeasure) = 0 ∧
      (∫ s : ℂ, s.im ^ 2 ∂standardComplexGaussianMeasure) = 1 / 2 := by
  have hfirst : complexGaussianMixedMoment 1 1 0 = 0 := by
    rw [complexGaussianMixedMoment_formula (by norm_num) 1 0]
    norm_num [complexGaussianMixedMoment]
  have hsecond : complexGaussianMixedMoment 1 2 0 = 0 := by
    rw [complexGaussianMixedMoment_formula (by norm_num) 2 0]
    norm_num [complexGaussianMixedMoment]
  have hnorm : (∫ s : ℂ, Complex.normSq s ∂standardComplexGaussianMeasure) = 1 := by
    simpa [standardComplexGaussianMeasure] using integral_normSq_pow_coordinate 1 1 (by norm_num)
  have hi1 : Integrable (fun s : ℂ => s) standardComplexGaussianMeasure := by
    simpa [standardComplexGaussianMeasure, complexGaussianMixedMoment] using
      integrable_mixedComplexMonomial 1 1 0
  have hi2 : Integrable (fun s : ℂ => s ^ 2) standardComplexGaussianMeasure := by
    simpa [standardComplexGaussianMeasure, complexGaussianMixedMoment] using
      integrable_mixedComplexMonomial 1 2 0
  have hfirst' : (∫ s : ℂ, s ∂standardComplexGaussianMeasure) = 0 := by
    unfold complexGaussianMixedMoment at hfirst
    simpa [standardComplexGaussianMeasure] using hfirst
  have hsecond' : (∫ s : ℂ, s ^ 2 ∂standardComplexGaussianMeasure) = 0 := by
    unfold complexGaussianMixedMoment at hsecond
    simpa [standardComplexGaussianMeasure] using hsecond
  constructor
  · calc
      (∫ s : ℂ, s.im ∂standardComplexGaussianMeasure) =
          (∫ s : ℂ, s ∂standardComplexGaussianMeasure).im := integral_im hi1
      _ = 0 := by rw [hfirst']; rfl
  · have hid (s : ℂ) : s.im ^ 2 = (Complex.normSq s - (s ^ 2).re) / 2 := by
      rcases s with ⟨a, b⟩
      have hs : ((⟨a, b⟩ : ℂ) ^ 2).re = a * a - b * b := by
        rw [pow_two, Complex.mul_re]
      rw [Complex.normSq_apply, hs]
      ring
    have hnI : Integrable (fun s : ℂ => Complex.normSq s) standardComplexGaussianMeasure := by
      simpa [standardComplexGaussianMeasure, pow_one] using integrable_normSq_pow_coordinate 1 1
    have hr2 : Integrable (fun s : ℂ => s.im ^ 2) standardComplexGaussianMeasure := by
      apply hnI.mono'
      · fun_prop
      · filter_upwards with s
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s.im), Complex.normSq_apply]
        nlinarith [sq_nonneg s.re]
    have hreal2 := integral_re hi2
    rw [hsecond'] at hreal2
    have hreal2' : (∫ a : ℂ, (a ^ 2).re ∂standardComplexGaussianMeasure) = 0 := by
      simpa using hreal2
    have hadd := integral_sub hnI hi2.re
    calc
      (∫ s : ℂ, s.im ^ 2 ∂standardComplexGaussianMeasure) =
          (∫ s : ℂ, (Complex.normSq s - (s ^ 2).re) / 2
            ∂standardComplexGaussianMeasure) := by
              apply integral_congr_ae
              filter_upwards with s
              exact hid s
      _ = 1 / 2 := by
        rw [integral_div]
        rw [show (∫ a : ℂ, Complex.normSq a - (a ^ 2).re
            ∂standardComplexGaussianMeasure) =
          (∫ a : ℂ, Complex.normSq a ∂standardComplexGaussianMeasure) -
            ∫ a : ℂ, (a ^ 2).re ∂standardComplexGaussianMeasure by simpa using hadd]
        rw [hnorm, hreal2']
        norm_num

/-- The classical gradient of the real sum coordinate is a fixed vector. -/
theorem centerOfMassReal_gradient_const (n : ℕ) (z : Configuration n) :
    ginibreEuclideanGradient centerOfMassReal z =
      ginibreEuclideanGradient centerOfMassReal 0 := by
  apply PiLp.ext
  intro k
  rw [ginibreEuclideanGradient_coordinate, ginibreEuclideanGradient_coordinate]
  have hlin : (centerOfMassReal : Configuration n → ℝ) =
      (Complex.reCLM.comp (coordinateSumCLM n) : Configuration n → ℝ) := by
    funext w
    simp [centerOfMassReal, coordinateSumCLM_apply]
  rw [hlin, ContinuousLinearMap.fderiv]
  simp [ginibreCoordinateDirection, coordinateSumCLM_apply,
    realCoordinateDirection,
    imaginaryCoordinateDirection]

theorem centerOfMassReal_gradient_norm_sq (n : ℕ) (z : Configuration n) :
    ‖ginibreEuclideanGradient centerOfMassReal z‖ ^ 2 = (n : ℝ) := by
  rw [ginibreEuclideanGradient_norm_sq]
  unfold realGradientNormSq
  have hlin : (centerOfMassReal : Configuration n → ℝ) =
      (Complex.reCLM.comp (coordinateSumCLM n) : Configuration n → ℝ) := by
    funext w
    simp [centerOfMassReal, coordinateSumCLM_apply]
  simp only [hlin, ContinuousLinearMap.fderiv]
  simp [coordinateSumCLM_apply,
    coordinateSum_coordinateDirection, realCoordinateDirection,
    imaginaryCoordinateDirection]

/-- The noncompact real center-of-mass observable belongs to the full symmetric
weak-H¹ domain and attains equality in the sharp Poincaré inequality. -/
theorem centerOfMassReal_attains_symmetric_weak_poincare (n : ℕ) (hn : 0 < n) :
    ∃ u : Lp ℝ 2 (ginibreMeasure n),
      ∃ g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
        IsGinibreDistributionalGradient n u g ∧ IsGinibreSymmetricWeakPair (u, g) ∧
          (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] centerOfMassReal ∧
          ginibreL2Variance n hn u = ginibreWeakEnergy n g / 2 := by
  let hu := memLp_centerOfMassReal n hn
  let f : Configuration n → ℝ := centerOfMassReal
  let hcont : ContDiff ℝ ∞ f := by
    have hlin : f = (Complex.reCLM.comp (coordinateSumCLM n) : Configuration n → ℝ) := by
      funext z
      simp [f, centerOfMassReal, coordinateSumCLM_apply]
    rw [hlin]
    exact (Complex.reCLM.comp (coordinateSumCLM n)).contDiff
  let v : EuclideanSpace ℝ (Fin n × Fin 2) := ginibreEuclideanGradient f 0
  let := ginibreMeasure_isProbabilityMeasure hn
  have hgmem : MemLp (fun _ : Configuration n => v) 2 (ginibreMeasure n) := memLp_const v
  let u : Lp ℝ 2 (ginibreMeasure n) := hu.toLp f
  let g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) := hgmem.toLp (fun _ => v)
  have hgrad : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[
      ginibreMeasure n] ginibreEuclideanGradient f := by
    filter_upwards [hgmem.coeFn_toLp] with z hz
    rw [hz, centerOfMassReal_gradient_const]
  have hweak : IsGinibreDistributionalGradient n u g :=
    ginibre_smooth_distributional_gradient n hn u g f hcont hu.coeFn_toLp hgrad
  have hsym : IsGinibreSymmetricWeakPair (u, g) := by
    intro σ
    constructor
    · apply Lp.ext
      have hcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
        hu.coeFn_toLp
      filter_upwards [ginibreRealPermutationL2_ae σ u, hcomp, hu.coeFn_toLp]
        with z hperm huval huval0
      rw [hperm]
      change (hu.toLp centerOfMassReal : Configuration n → ℝ) (permute σ z) =
        (hu.toLp centerOfMassReal : Configuration n → ℝ) z
      have huval' : (hu.toLp centerOfMassReal : Configuration n → ℝ)
          (permute σ z) = centerOfMassReal (permute σ z) := by
        simpa only [Function.comp_apply] using huval
      rw [huval', huval0]
      simp [centerOfMassReal, coordinateSum_permute]
    · apply Lp.ext
      have hgcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
        hgmem.coeFn_toLp
      filter_upwards [ginibreGradientPermutationL2_ae σ g, hgcomp, hgmem.coeFn_toLp]
        with z hperm hgval hgval0
      rw [hperm]
      change WithLp.toLp 2 (fun k : Fin n × Fin 2 =>
        (hgmem.toLp (fun _ => v) : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
          (permute σ z) (σ.symm k.1, k.2)) =
        (hgmem.toLp (fun _ => v) : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) z
      have hgval' : (hgmem.toLp (fun _ => v) :
          Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) (permute σ z) = v := by
        simpa only [Function.comp_apply] using hgval
      rw [hgval', hgval0]
      apply PiLp.ext
      intro k
      change v (σ.symm k.1, k.2) = v k
      have hlin : (centerOfMassReal : Configuration n → ℝ) =
          (Complex.reCLM.comp (coordinateSumCLM n) : Configuration n → ℝ) := by
        funext w
        simp [centerOfMassReal, coordinateSumCLM_apply]
      have hv : v (σ.symm k.1, k.2) = v k := by
        dsimp [v]
        rw [ginibreEuclideanGradient_coordinate, ginibreEuclideanGradient_coordinate]
        change (fderiv ℝ centerOfMassReal 0)
          (ginibreCoordinateDirection (σ.symm k.1, k.2)) =
          (fderiv ℝ centerOfMassReal 0) (ginibreCoordinateDirection k)
        rw [hlin, ContinuousLinearMap.fderiv]
        by_cases hk : k.2 = 0
        · simp [ginibreCoordinateDirection, hk, realCoordinateDirection,
            coordinateSum_coordinateDirection]
        · simp [ginibreCoordinateDirection, hk,
            imaginaryCoordinateDirection, coordinateSum_coordinateDirection]
      exact hv
  have hmean : ginibreL2Mean n u = 0 := by
    unfold ginibreL2Mean
    rw [integral_congr_ae hu.coeFn_toLp]
    have hmap : (∫ s : ℂ, s.re ∂((ginibreMeasure n).map coordinateSum)) =
        ∫ z, (coordinateSum z).re ∂ginibreMeasure n :=
      integral_map (μ := ginibreMeasure n) (measurable_coordinateSum n).aemeasurable
        (Complex.continuous_re.aestronglyMeasurable)
    calc
      (∫ z, (coordinateSum z).re ∂ginibreMeasure n) =
          ∫ s, s.re ∂((ginibreMeasure n).map coordinateSum) := hmap.symm
      _ = 0 := by
        rw [coordinateSum_ginibre_gaussian n hn]
        exact standardComplexGaussian_real_moments.1
  have hvar : ginibreL2Variance n hn u = 1 / 2 := by
    have hc0 : ginibreRealConstantL2 n hn 0 = 0 := by
      apply Lp.ext
      filter_upwards [ginibreRealConstantL2_ae n hn 0] with z hz
      simp [hz]
    rw [ginibreL2Variance, hmean, hc0, sub_zero]
    rw [← integral_square_eq_L2_norm_sq]
    have hsecond : (∫ z, centerOfMassReal z ^ 2 ∂ginibreMeasure n) = 1 / 2 := by
      have hmap : (∫ s : ℂ, s.re ^ 2 ∂((ginibreMeasure n).map coordinateSum)) =
          ∫ z, (coordinateSum z).re ^ 2 ∂ginibreMeasure n :=
        integral_map (μ := ginibreMeasure n) (measurable_coordinateSum n).aemeasurable
          ((Complex.continuous_re.pow 2).aestronglyMeasurable)
      calc
        (∫ z, centerOfMassReal z ^ 2 ∂ginibreMeasure n) =
            ∫ z, (coordinateSum z).re ^ 2 ∂ginibreMeasure n := by rfl
        _ = ∫ s, s.re ^ 2 ∂((ginibreMeasure n).map coordinateSum) := hmap.symm
        _ = 1 / 2 := by
          rw [coordinateSum_ginibre_gaussian n hn]
          exact standardComplexGaussian_real_moments.2
    calc
      (∫ z, u z ^ 2 ∂ginibreMeasure n) =
          ∫ z, centerOfMassReal z ^ 2 ∂ginibreMeasure n := by
            apply integral_congr_ae
            filter_upwards [hu.coeFn_toLp] with z hz
            rw [hz]
      _ = 1 / 2 := hsecond
  have henergy : ginibreWeakEnergy n g = 1 := by
    rw [ginibreWeakEnergy, ← integral_norm_sq_eq_L2_norm_sq]
    have hae : (fun z => ‖g z‖ ^ 2) =ᵐ[ginibreMeasure n]
        fun z => ‖ginibreEuclideanGradient f z‖ ^ 2 := by
      filter_upwards [hgrad] with z hz
      rw [hz]
    rw [integral_congr_ae hae]
    rw [show (fun z => ‖ginibreEuclideanGradient f z‖ ^ 2) =
      fun _ => (n : ℝ) by
        funext z
        simpa [f] using centerOfMassReal_gradient_norm_sq n z]
    norm_num [probReal_univ, hn.ne']
  refine ⟨u, g, hweak, hsym, hu.coeFn_toLp, ?_⟩
  rw [hvar, henergy]

/-- The imaginary center-of-mass observable is square-integrable for every Ginibre law. -/
theorem memLp_centerOfMassImag (n : ℕ) (hn : 0 < n) :
    MemLp (centerOfMassImag : Configuration n → ℝ) 2 (ginibreMeasure n) := by
  have hgauss : Integrable (fun s : ℂ => ‖s‖ ^ 2) standardComplexGaussianMeasure := by
    simpa [standardComplexGaussianMeasure] using
      (integrable_norm_pow_complexCoordinateGaussianProbability 1 2)
  have hcomp : Integrable (fun z : Configuration n => ‖coordinateSum z‖ ^ 2)
      (ginibreMeasure n) := by
    have hpush : Integrable (fun s : ℂ => ‖s‖ ^ 2)
        ((ginibreMeasure n).map coordinateSum) := by
      rw [coordinateSum_ginibre_gaussian n hn]
      exact hgauss
    exact hpush.comp_aemeasurable (measurable_coordinateSum n).aemeasurable
  have hcont : Continuous (centerOfMassImag : Configuration n → ℝ) := by
    have hsum : (coordinateSum : Configuration n → ℂ) = coordinateSumCLM n := by
      funext z
      exact (coordinateSumCLM_apply n z).symm
    rw [show (centerOfMassImag : Configuration n → ℝ) =
      Complex.imCLM ∘L coordinateSumCLM n by
        funext z
        simp [centerOfMassImag]]
    exact (Complex.imCLM.comp (coordinateSumCLM n)).continuous
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
  apply hcomp.mono'
  · exact (continuous_norm.comp hcont).pow 2 |>.aestronglyMeasurable
  · filter_upwards with z
    change ‖‖centerOfMassImag z‖ ^ 2‖ ≤ ‖coordinateSum z‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb : ‖centerOfMassImag z‖ ≤ ‖coordinateSum z‖ := by
      change |(coordinateSum z).im| ≤ ‖coordinateSum z‖
      exact Complex.abs_im_le_norm _
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hb

theorem centerOfMassImag_gradient_const (n : ℕ) (z : Configuration n) :
    ginibreEuclideanGradient centerOfMassImag z =
      ginibreEuclideanGradient centerOfMassImag 0 := by
  apply PiLp.ext
  intro k
  rw [ginibreEuclideanGradient_coordinate, ginibreEuclideanGradient_coordinate]
  have hlin : (centerOfMassImag : Configuration n → ℝ) =
      (Complex.imCLM.comp (coordinateSumCLM n) : Configuration n → ℝ) := by
    funext w
    simp [centerOfMassImag, coordinateSumCLM_apply]
  rw [hlin, ContinuousLinearMap.fderiv]
  simp [ginibreCoordinateDirection, coordinateSumCLM_apply,
    realCoordinateDirection, imaginaryCoordinateDirection]

theorem centerOfMassImag_gradient_norm_sq (n : ℕ) (z : Configuration n) :
    ‖ginibreEuclideanGradient centerOfMassImag z‖ ^ 2 = (n : ℝ) := by
  rw [ginibreEuclideanGradient_norm_sq]
  unfold realGradientNormSq
  have hlin : (centerOfMassImag : Configuration n → ℝ) =
      (Complex.imCLM.comp (coordinateSumCLM n) : Configuration n → ℝ) := by
    funext w
    simp [centerOfMassImag, coordinateSumCLM_apply]
  simp only [hlin, ContinuousLinearMap.fderiv]
  simp [coordinateSumCLM_apply, realCoordinateDirection,
    imaginaryCoordinateDirection]

/-- The imaginary center-of-mass observable is a noncompact equality attainer
inside the full symmetric weak-H¹ domain. -/
theorem centerOfMassImag_attains_symmetric_weak_poincare (n : ℕ) (hn : 0 < n) :
    ∃ u : Lp ℝ 2 (ginibreMeasure n),
      ∃ g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
        IsGinibreDistributionalGradient n u g ∧ IsGinibreSymmetricWeakPair (u, g) ∧
          (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] centerOfMassImag ∧
          ginibreL2Variance n hn u = ginibreWeakEnergy n g / 2 := by
  let hu := memLp_centerOfMassImag n hn
  let f : Configuration n → ℝ := centerOfMassImag
  let hcont : ContDiff ℝ ∞ f := by
    have hlin : f = (Complex.imCLM.comp (coordinateSumCLM n) : Configuration n → ℝ) := by
      funext z
      simp [f, centerOfMassImag, coordinateSumCLM_apply]
    rw [hlin]
    exact (Complex.imCLM.comp (coordinateSumCLM n)).contDiff
  let v : EuclideanSpace ℝ (Fin n × Fin 2) := ginibreEuclideanGradient f 0
  let := ginibreMeasure_isProbabilityMeasure hn
  have hgmem : MemLp (fun _ : Configuration n => v) 2 (ginibreMeasure n) := memLp_const v
  let u : Lp ℝ 2 (ginibreMeasure n) := hu.toLp f
  let g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) := hgmem.toLp (fun _ => v)
  have hgrad : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[
      ginibreMeasure n] ginibreEuclideanGradient f := by
    filter_upwards [hgmem.coeFn_toLp] with z hz
    rw [hz, centerOfMassImag_gradient_const]
  have hweak : IsGinibreDistributionalGradient n u g :=
    ginibre_smooth_distributional_gradient n hn u g f hcont hu.coeFn_toLp hgrad
  have hsym : IsGinibreSymmetricWeakPair (u, g) := by
    intro σ
    constructor
    · apply Lp.ext
      have hcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
        hu.coeFn_toLp
      filter_upwards [ginibreRealPermutationL2_ae σ u, hcomp, hu.coeFn_toLp]
        with z hperm huval huval0
      rw [hperm]
      change (hu.toLp centerOfMassImag : Configuration n → ℝ) (permute σ z) =
        (hu.toLp centerOfMassImag : Configuration n → ℝ) z
      have huval' : (hu.toLp centerOfMassImag : Configuration n → ℝ)
          (permute σ z) = centerOfMassImag (permute σ z) := by
        simpa only [Function.comp_apply] using huval
      rw [huval', huval0]
      simp [centerOfMassImag, coordinateSum_permute]
    · apply Lp.ext
      have hgcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
        hgmem.coeFn_toLp
      filter_upwards [ginibreGradientPermutationL2_ae σ g, hgcomp, hgmem.coeFn_toLp]
        with z hperm hgval hgval0
      rw [hperm]
      change WithLp.toLp 2 (fun k : Fin n × Fin 2 =>
        (hgmem.toLp (fun _ => v) : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
          (permute σ z) (σ.symm k.1, k.2)) =
        (hgmem.toLp (fun _ => v) : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) z
      have hgval' : (hgmem.toLp (fun _ => v) :
          Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) (permute σ z) = v := by
        simpa only [Function.comp_apply] using hgval
      rw [hgval', hgval0]
      apply PiLp.ext
      intro k
      change v (σ.symm k.1, k.2) = v k
      have hlin : (centerOfMassImag : Configuration n → ℝ) =
          (Complex.imCLM.comp (coordinateSumCLM n) : Configuration n → ℝ) := by
        funext w
        simp [centerOfMassImag, coordinateSumCLM_apply]
      have hv : v (σ.symm k.1, k.2) = v k := by
        dsimp [v]
        rw [ginibreEuclideanGradient_coordinate, ginibreEuclideanGradient_coordinate]
        change (fderiv ℝ centerOfMassImag 0)
          (ginibreCoordinateDirection (σ.symm k.1, k.2)) =
          (fderiv ℝ centerOfMassImag 0) (ginibreCoordinateDirection k)
        rw [hlin, ContinuousLinearMap.fderiv]
        by_cases hk : k.2 = 0
        · simp [ginibreCoordinateDirection, hk, realCoordinateDirection,
            coordinateSum_coordinateDirection]
        · simp [ginibreCoordinateDirection, hk,
            imaginaryCoordinateDirection, coordinateSum_coordinateDirection]
      exact hv
  have hmean : ginibreL2Mean n u = 0 := by
    unfold ginibreL2Mean
    rw [integral_congr_ae hu.coeFn_toLp]
    have hmap : (∫ s : ℂ, s.im ∂((ginibreMeasure n).map coordinateSum)) =
        ∫ z, (coordinateSum z).im ∂ginibreMeasure n :=
      integral_map (μ := ginibreMeasure n) (measurable_coordinateSum n).aemeasurable
        (Complex.continuous_im.aestronglyMeasurable)
    calc
      (∫ z, (coordinateSum z).im ∂ginibreMeasure n) =
          ∫ s, s.im ∂((ginibreMeasure n).map coordinateSum) := hmap.symm
      _ = 0 := by
        rw [coordinateSum_ginibre_gaussian n hn]
        exact standardComplexGaussian_imag_moments.1
  have hvar : ginibreL2Variance n hn u = 1 / 2 := by
    have hc0 : ginibreRealConstantL2 n hn 0 = 0 := by
      apply Lp.ext
      filter_upwards [ginibreRealConstantL2_ae n hn 0] with z hz
      simp [hz]
    rw [ginibreL2Variance, hmean, hc0, sub_zero]
    rw [← integral_square_eq_L2_norm_sq]
    have hsecond : (∫ z, centerOfMassImag z ^ 2 ∂ginibreMeasure n) = 1 / 2 := by
      have hmap : (∫ s : ℂ, s.im ^ 2 ∂((ginibreMeasure n).map coordinateSum)) =
          ∫ z, (coordinateSum z).im ^ 2 ∂ginibreMeasure n :=
        integral_map (μ := ginibreMeasure n) (measurable_coordinateSum n).aemeasurable
          ((Complex.continuous_im.pow 2).aestronglyMeasurable)
      calc
        (∫ z, centerOfMassImag z ^ 2 ∂ginibreMeasure n) =
            ∫ z, (coordinateSum z).im ^ 2 ∂ginibreMeasure n := by rfl
        _ = ∫ s, s.im ^ 2 ∂((ginibreMeasure n).map coordinateSum) := hmap.symm
        _ = 1 / 2 := by
          rw [coordinateSum_ginibre_gaussian n hn]
          exact standardComplexGaussian_imag_moments.2
    calc
      (∫ z, u z ^ 2 ∂ginibreMeasure n) =
          ∫ z, centerOfMassImag z ^ 2 ∂ginibreMeasure n := by
            apply integral_congr_ae
            filter_upwards [hu.coeFn_toLp] with z hz
            rw [hz]
      _ = 1 / 2 := hsecond
  have henergy : ginibreWeakEnergy n g = 1 := by
    rw [ginibreWeakEnergy, ← integral_norm_sq_eq_L2_norm_sq]
    have hae : (fun z => ‖g z‖ ^ 2) =ᵐ[ginibreMeasure n]
        fun z => ‖ginibreEuclideanGradient f z‖ ^ 2 := by
      filter_upwards [hgrad] with z hz
      rw [hz]
    rw [integral_congr_ae hae]
    rw [show (fun z => ‖ginibreEuclideanGradient f z‖ ^ 2) =
      fun _ => (n : ℝ) by
        funext z
        simpa [f] using centerOfMassImag_gradient_norm_sq n z]
    norm_num [probReal_univ, hn.ne']
  refine ⟨u, g, hweak, hsym, hu.coeFn_toLp, ?_⟩
  rw [hvar, henergy]

end
end GinibrePoincare
