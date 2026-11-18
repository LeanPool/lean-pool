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
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakConstantPairs
public import LeanPool.GinibrePoincare.Endgame.ConcreteTheoremOneNine
public import LeanPool.GinibrePoincare.Analysis.EquilibriumProbability
public import LeanPool.GinibrePoincare.Analysis.CenterOfMassEigenfunctions
public import LeanPool.GinibrePoincare.Analysis.GinibreCoordinateSumL2

/-!
# Ginibre Symmetric Weak Poincare
-/


@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Variance of an actual Ginibre `L²` class, defined by its centered Hilbert norm. -/
def ginibreL2Variance (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) : ℝ :=
  ‖u - ginibreRealConstantL2 n hn (ginibreL2Mean n u)‖ ^ 2

theorem ginibreL2Variance_continuous (n : ℕ) (hn : 0 < n) :
    Continuous (ginibreL2Variance n hn) := by
  let one := ginibreRealConstantL2 n hn 1
  have hc : Continuous (fun u : Lp ℝ 2 (ginibreMeasure n) =>
      ginibreL2Mean n u • one) :=
    (ginibreL2Mean_continuous n hn).smul continuous_const
  have hrepr : ginibreL2Variance n hn = fun u =>
      ‖u - ginibreL2Mean n u • one‖ ^ 2 := by
    funext u
    unfold ginibreL2Variance
    rw [ginibreRealConstantL2_eq_smul_one n hn (ginibreL2Mean n u)]
  rw [hrepr]
  exact (continuous_norm.comp (continuous_id.sub hc)).pow 2

/-- A weak gradient representative has the corresponding smooth Dirichlet energy. -/
theorem ginibreWeakEnergy_eq_smoothGinibreEnergy {n : ℕ}
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (f : Configuration n → ℝ)
    (hg : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
      ginibreEuclideanGradient f) :
    ginibreWeakEnergy n g = smoothGinibreEnergy n f := by
  rw [ginibreWeakEnergy, ← integral_norm_sq_eq_L2_norm_sq]
  unfold smoothGinibreEnergy
  congr 1
  apply integral_congr_ae
  filter_upwards [hg] with z hz
  rw [hz, ginibreEuclideanGradient_norm_sq]

/-- An L² representative has the variance of its almost-everywhere equal observable. -/
theorem ginibreL2Variance_eq_smoothGinibreVariance {n : ℕ} (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (f : Configuration n → ℝ)
    (hu : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f) :
    ginibreL2Variance n hn u = smoothGinibreVariance n f := by
  have hmean : ginibreL2Mean n u = smoothGinibreMean n f := integral_congr_ae hu
  rw [ginibreL2Variance, hmean]
  calc
    ‖u - ginibreRealConstantL2 n hn (smoothGinibreMean n f)‖ ^ 2 =
        ∫ z, (u z - smoothGinibreMean n f) ^ 2 ∂ginibreMeasure n := by
          rw [← integral_square_eq_L2_norm_sq]
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_sub u
              (ginibreRealConstantL2 n hn (smoothGinibreMean n f)),
            hu, ginibreRealConstantL2_ae n hn (smoothGinibreMean n f)]
            with z hsub hz hc
          rw [hsub]
          change ((u : Configuration n → ℝ) z -
            (ginibreRealConstantL2 n hn (smoothGinibreMean n f) :
              Configuration n → ℝ) z) ^ 2 = _
          rw [hz, hc]
    _ = smoothGinibreVariance n f := by
      unfold smoothGinibreVariance
      apply integral_congr_ae
      filter_upwards [hu] with z hz
      rw [hz]

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
    have hvar := ginibreL2Variance_eq_smoothGinibreVariance hn p.1 f hv
    have henergy := ginibreWeakEnergy_eq_smoothGinibreEnergy p.2 f hgrad
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
    exact isClosed_le ((ginibreL2Variance_continuous n hn).comp continuous_fst)
      (((ginibreWeakEnergy_continuous n).comp continuous_snd).div_const 2)
  have hmem : (u, g) ∈ {p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) |
      ginibreL2Variance n hn p.1 ≤ ginibreWeakEnergy n p.2 / 2} :=
    hclosed.mem_of_tendsto hqconv (Eventually.of_forall fun m => hcore (q m) (hq m))
  exact hmem

/-- The real center-of-mass observable is square-integrable for every Ginibre law. -/
theorem memLp_centerOfMassReal (n : ℕ) (hn : 0 < n) :
    MemLp (centerOfMassReal : Configuration n → ℝ) 2 (ginibreMeasure n) := by
  exact Complex.reCLM.comp_memLp' (memLp_coordinateSum n hn)

private theorem standardComplexGaussian_complex_moments :
    Integrable (fun s : ℂ => s) standardComplexGaussianMeasure ∧
      Integrable (fun s : ℂ => s ^ 2) standardComplexGaussianMeasure ∧
      (∫ s : ℂ, s ∂standardComplexGaussianMeasure) = 0 ∧
      (∫ s : ℂ, s ^ 2 ∂standardComplexGaussianMeasure) = 0 ∧
      (∫ s : ℂ, Complex.normSq s ∂standardComplexGaussianMeasure) = 1 := by
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
  exact ⟨hi1, hi2, hfirst', hsecond', hnorm⟩

/-- Exact first and second real moments of the standard complex Gaussian. -/
theorem standardComplexGaussian_real_moments :
    (∫ s : ℂ, s.re ∂standardComplexGaussianMeasure) = 0 ∧
      (∫ s : ℂ, s.re ^ 2 ∂standardComplexGaussianMeasure) = 1 / 2 := by
  obtain ⟨hi1, hi2, hfirst', hsecond', hnorm⟩ := standardComplexGaussian_complex_moments
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
  let e := complexMulMeasurableEquiv (-Complex.I) (by simp)
  have hrot : MeasurePreserving e standardComplexGaussianMeasure
      standardComplexGaussianMeasure := by
    simpa [e, complexMulMeasurableEquiv, standardComplexGaussianMeasure] using
      measurePreserving_complexCoordinateGaussian_mul (n := 1) (by decide)
        (-Complex.I) (by simp)
  constructor
  · have h := hrot.integral_comp' (fun s : ℂ => s.re)
    simpa [e, complexMulMeasurableEquiv, Complex.mul_re] using
      h.trans standardComplexGaussian_real_moments.1
  · have h := hrot.integral_comp' (fun s : ℂ => s.re ^ 2)
    simpa [e, complexMulMeasurableEquiv, Complex.mul_re] using
      h.trans standardComplexGaussian_real_moments.2

private theorem coordinateSumLinear_gradient_const (n : ℕ) (L : ℂ →L[ℝ] ℝ)
    (z : Configuration n) :
    ginibreEuclideanGradient (fun w => L (coordinateSum w)) z =
      ginibreEuclideanGradient (fun w => L (coordinateSum w)) 0 := by
  have hlin : (fun w : Configuration n => L (coordinateSum w)) =
      (L.comp (coordinateSumCLM n) : Configuration n → ℝ) := by
    funext w
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, coordinateSumCLM_apply]
  apply PiLp.ext
  intro k
  simp only [ginibreEuclideanGradient_coordinate, hlin, ContinuousLinearMap.fderiv]

/-- The classical gradient of the real sum coordinate is a fixed vector. -/
theorem centerOfMassReal_gradient_const (n : ℕ) (z : Configuration n) :
    ginibreEuclideanGradient centerOfMassReal z =
      ginibreEuclideanGradient centerOfMassReal 0 := by
  exact coordinateSumLinear_gradient_const n Complex.reCLM z

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

/-- A real-linear sum coordinate with Gaussian variance one half and gradient
norm squared `n` gives a symmetric weak-H¹ equality witness. -/
private theorem coordinateSumLinear_attains_symmetric_weak_poincare
    (n : ℕ) (hn : 0 < n) (L : ℂ →L[ℝ] ℝ)
    (hmoments : (∫ s : ℂ, L s ∂standardComplexGaussianMeasure) = 0 ∧
      (∫ s : ℂ, (L s) ^ 2 ∂standardComplexGaussianMeasure) = 1 / 2)
    (hnorm : ∀ z : Configuration n,
      ‖ginibreEuclideanGradient (fun w => L (coordinateSum w)) z‖ ^ 2 = (n : ℝ)) :
    ∃ u : Lp ℝ 2 (ginibreMeasure n),
      ∃ g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
        IsGinibreDistributionalGradient n u g ∧ IsGinibreSymmetricWeakPair (u, g) ∧
          (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] (fun z => L (coordinateSum z)) ∧
          ginibreL2Variance n hn u = ginibreWeakEnergy n g / 2 := by
  let f : Configuration n → ℝ := fun z => L (coordinateSum z)
  let hu : MemLp f 2 (ginibreMeasure n) := L.comp_memLp' (memLp_coordinateSum n hn)
  let hcont : ContDiff ℝ ∞ f := by
    have hlin : f = (L.comp (coordinateSumCLM n) : Configuration n → ℝ) := by
      funext z
      simp [f, coordinateSumCLM_apply]
    rw [hlin]
    exact (L.comp (coordinateSumCLM n)).contDiff
  let v : EuclideanSpace ℝ (Fin n × Fin 2) := ginibreEuclideanGradient f 0
  let := ginibreMeasure_isProbabilityMeasure hn
  have hgmem : MemLp (fun _ : Configuration n => v) 2 (ginibreMeasure n) := memLp_const v
  let u : Lp ℝ 2 (ginibreMeasure n) := hu.toLp f
  let g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) := hgmem.toLp (fun _ => v)
  have hgrad : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[
      ginibreMeasure n] ginibreEuclideanGradient f := by
    filter_upwards [hgmem.coeFn_toLp] with z hz
    rw [hz, coordinateSumLinear_gradient_const n L]
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
      change (hu.toLp f : Configuration n → ℝ) (permute σ z) =
        (hu.toLp f : Configuration n → ℝ) z
      have huval' : (hu.toLp f : Configuration n → ℝ)
          (permute σ z) = f (permute σ z) := by
        simpa only [Function.comp_apply] using huval
      rw [huval', huval0]
      simp [f, coordinateSum_permute]
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
      have hlin : (f : Configuration n → ℝ) =
          (L.comp (coordinateSumCLM n) : Configuration n → ℝ) := by
        funext w
        simp [f, coordinateSumCLM_apply]
      have hv : v (σ.symm k.1, k.2) = v k := by
        dsimp [v]
        rw [ginibreEuclideanGradient_coordinate, ginibreEuclideanGradient_coordinate]
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
    have hmap : (∫ s : ℂ, L s ∂((ginibreMeasure n).map coordinateSum)) =
        ∫ z, L (coordinateSum z) ∂ginibreMeasure n :=
      integral_map (μ := ginibreMeasure n) (measurable_coordinateSum n).aemeasurable
        (L.continuous.aestronglyMeasurable)
    calc
      (∫ z, L (coordinateSum z) ∂ginibreMeasure n) =
          ∫ s, L s ∂((ginibreMeasure n).map coordinateSum) := hmap.symm
      _ = 0 := by
        rw [coordinateSum_ginibre_gaussian n hn]
        exact hmoments.1
  have hvar : ginibreL2Variance n hn u = 1 / 2 := by
    rw [ginibreL2Variance, hmean, ginibreRealConstantL2_zero, sub_zero]
    rw [← integral_square_eq_L2_norm_sq]
    have hsecond : (∫ z, f z ^ 2 ∂ginibreMeasure n) = 1 / 2 := by
      have hmap : (∫ s : ℂ, L s ^ 2 ∂((ginibreMeasure n).map coordinateSum)) =
          ∫ z, L (coordinateSum z) ^ 2 ∂ginibreMeasure n :=
        integral_map (μ := ginibreMeasure n) (measurable_coordinateSum n).aemeasurable
          ((L.continuous.pow 2).aestronglyMeasurable)
      calc
        (∫ z, f z ^ 2 ∂ginibreMeasure n) =
            ∫ z, L (coordinateSum z) ^ 2 ∂ginibreMeasure n := by rfl
        _ = ∫ s, L s ^ 2 ∂((ginibreMeasure n).map coordinateSum) := hmap.symm
        _ = 1 / 2 := by
          rw [coordinateSum_ginibre_gaussian n hn]
          exact hmoments.2
    calc
      (∫ z, u z ^ 2 ∂ginibreMeasure n) =
          ∫ z, f z ^ 2 ∂ginibreMeasure n := by
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
        simpa [f] using hnorm z]
    norm_num [probReal_univ, hn.ne']
  refine ⟨u, g, hweak, hsym, hu.coeFn_toLp, ?_⟩
  rw [hvar, henergy]

/-- The noncompact real center-of-mass observable belongs to the full symmetric
weak-H¹ domain and attains equality in the sharp Poincaré inequality. -/
theorem centerOfMassReal_attains_symmetric_weak_poincare (n : ℕ) (hn : 0 < n) :
    ∃ u : Lp ℝ 2 (ginibreMeasure n),
      ∃ g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
        IsGinibreDistributionalGradient n u g ∧ IsGinibreSymmetricWeakPair (u, g) ∧
          (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] centerOfMassReal ∧
          ginibreL2Variance n hn u = ginibreWeakEnergy n g / 2 := by
  exact coordinateSumLinear_attains_symmetric_weak_poincare n hn Complex.reCLM
    standardComplexGaussian_real_moments (centerOfMassReal_gradient_norm_sq n)

/-- The imaginary center-of-mass observable is square-integrable for every Ginibre law. -/
theorem memLp_centerOfMassImag (n : ℕ) (hn : 0 < n) :
    MemLp (centerOfMassImag : Configuration n → ℝ) 2 (ginibreMeasure n) := by
  exact Complex.imCLM.comp_memLp' (memLp_coordinateSum n hn)

theorem centerOfMassImag_gradient_const (n : ℕ) (z : Configuration n) :
    ginibreEuclideanGradient centerOfMassImag z =
      ginibreEuclideanGradient centerOfMassImag 0 := by
  exact coordinateSumLinear_gradient_const n Complex.imCLM z

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
  exact coordinateSumLinear_attains_symmetric_weak_poincare n hn Complex.imCLM
    standardComplexGaussian_imag_moments (centerOfMassImag_gradient_norm_sq n)

end
end GinibrePoincare
