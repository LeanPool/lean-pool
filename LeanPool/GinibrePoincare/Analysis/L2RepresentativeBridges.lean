/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/L2RepresentativeBridges.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteParsevalModes
public import LeanPool.GinibrePoincare.Concrete.Generator
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
public import LeanPool.GinibrePoincare.Concrete.HolomorphicDistance

public import LeanPool.GinibrePoincare.Analysis.GinibreL2Norm

/-! # Bridges between concrete representatives and `L²` classes -/


@[expose] public section


open MeasureTheory

namespace GinibrePoincare

noncomputable section

/-- Continuous Gaussian representatives that agree almost everywhere agree
pointwise. -/
theorem continuous_eq_of_ae_eq_complexGaussian {n : ℕ}
    (hn : 0 < n) {f g : Configuration n → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[complexGaussianMeasure n] g) : f = g := by
  let : (complexGaussianMeasure n).IsOpenPosMeasure := by
    rw [complexGaussianDensityIdentification n hn]
    let : (configurationVolume n).IsOpenPosMeasure := by
      unfold configurationVolume
      infer_instance
    have hac : configurationVolume n ≪
        (configurationVolume n).withDensity (complexGaussianDensity n) := by
      apply withDensity_absolutelyContinuous'
      · exact (measurable_complexGaussianDensity n).aemeasurable
      · filter_upwards with z
        unfold complexGaussianDensity gaussianWeight
        positivity
    exact hac.isOpenPosMeasure
  exact Measure.eq_of_ae_eq h hf hg

/-- A centered core observable is square-integrable for the Ginibre measure. -/
theorem memLp_centeredObservable_of_core {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    MemLp (fun z => (centeredObservable n f z : ℂ)) 2 (ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  let F : Configuration n → ℂ := fun z => (f z : ℂ)
  have hFc : Continuous F := by
    exact Complex.continuous_ofReal.comp hf.1.continuous
  have hFcomp : HasCompactSupport F := by
    apply hf.2.1.mono
    intro z hz hzero
    apply hz
    simp only [F, hzero, Complex.ofReal_zero]
  let Fb := ofCompactSupport F hFc hFcomp
  have hmemF : MemLp F 2 (ginibreMeasure n) := by
    apply MemLp.of_bound hFc.aestronglyMeasurable ‖Fb‖
    filter_upwards with z
    exact Fb.norm_coe_le_norm z
  convert hmemF.sub (memLp_const (smoothGinibreMean n f : ℂ)) using 1
  ext z
  simp [F, centeredObservable]

/-- The centered real observable, embedded into complex Ginibre `L²`. -/
def centeredObservableL2 {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) : Lp ℂ 2 (ginibreMeasure n) :=
  (memLp_centeredObservable_of_core hn f hf).toLp _

theorem centeredObservableL2_coeFn {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    centeredObservableL2 hn f hf =ᵐ[ginibreMeasure n]
      fun z => (centeredObservable n f z : ℂ) := by
  exact (memLp_centeredObservable_of_core hn f hf).coeFn_toLp

/-- The squared Ginibre `L²` norm of the centered observable is its concrete
variance. -/
theorem norm_sq_centeredObservableL2 {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    ‖centeredObservableL2 hn f hf‖ ^ 2 = smoothGinibreVariance n f := by
  simpa only [smoothGinibreVariance, centeredObservable] using
    L2_norm_sq_eq_integral_sq_of_ae_ofReal (ginibreMeasure n)
      (centeredObservableL2 hn f hf) (centeredObservable n f)
      (centeredObservableL2_coeFn hn f hf)

/-- The normalized Vandermonde image of the centered observable. -/
def transformedCenteredObservableL2 {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  normalizedVandermondeL2 n hn (centeredObservableL2 hn f hf)

/-- Vandermonde multiplication preserves the centered-observable norm and
hence realizes the variance in Gaussian `L²`. -/
theorem norm_sq_transformedCenteredObservableL2 {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ‖transformedCenteredObservableL2 hn f hf‖ ^ 2 =
      smoothGinibreVariance n f := by
  rw [transformedCenteredObservableL2,
    (normalizedVandermondeL2 n hn).norm_map,
    norm_sq_centeredObservableL2 hn]

/-- Concrete Parseval decomposition of the Ginibre variance into the
holomorphic (zero antiholomorphic degree) part and the positive modes. -/
theorem smoothGinibreVariance_eq_zeroMode_add_positiveModeMass {n : ℕ}
    (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    smoothGinibreVariance n f =
      ‖gaussianHermiteMode hn 0
        (transformedCenteredObservableL2 hn f hf)‖ ^ 2 +
      ∑' k, positiveHermiteModeMass hn
        (transformedCenteredObservableL2 hn f hf) k := by
  rw [← norm_sq_transformedCenteredObservableL2 hn f hf]
  exact norm_sq_eq_zeroMode_add_positiveModeMass hn _

theorem summable_transformedCentered_positiveModeMass {n : ℕ}
    (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    Summable (positiveHermiteModeMass hn
      (transformedCenteredObservableL2 hn f hf)) :=
  summable_positiveHermiteModeMass hn _

end
end GinibrePoincare
