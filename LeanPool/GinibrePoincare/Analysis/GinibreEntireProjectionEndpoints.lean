/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEntireProjectionEndpoints.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEntireProjectionDistance
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireDistance
public import LeanPool.GinibrePoincare.Analysis.GaussianGinibreProjectionIntertwining

/-!
# Ginibre entire projection endpoints

Part of the ginibre measure and holomorphic geometry development of the
Ginibre Poincaré formalization.

Main results: `groundStateDistanceIdentityStatement`, `ginibreHalfDistanceStatement`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
namespace GinibrePoincare
noncomputable section

theorem memLp_smoothCenteredObservable {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f) :
    MemLp (fun z => (centeredObservable n f z : ℂ)) 2 (ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  let F : Configuration n → ℂ := fun z => (f z : ℂ)
  have hFc : Continuous F := Complex.continuous_ofReal.comp hf.1.continuous
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

/-- The centered observable `f - 𝔼 f` of a smooth compactly supported symmetric `f`, as a
complex vector of Ginibre `L²`. -/
def smoothCenteredObservableL2 {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f) :
    Lp ℂ 2 (ginibreMeasure n) := (memLp_smoothCenteredObservable hn f hf).toLp _

theorem smoothCenteredObservableL2_rep {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f) :
    (fun z => (centeredObservable n f z : ℂ)) =ᵐ[ginibreMeasure n]
      smoothCenteredObservableL2 hn f hf := (memLp_smoothCenteredObservable hn f hf).coeFn_toLp.symm

theorem smoothCenteredObservableL2_symmetric {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f) :
    smoothCenteredObservableL2 hn f hf ∈ ginibreSymmetricL2 n := by
  apply ginibreEntireRepresentative_mem_symmetric _ _ _ (smoothCenteredObservableL2_rep hn f hf)
  intro σ z
  change ((f (permute σ z) - smoothGinibreMean n f : ℝ) : ℂ) = _
  simpa only [centeredObservable] using congrArg
    (fun r : ℝ => ((r - smoothGinibreMean n f : ℝ) : ℂ)) (hf.2.2 σ z)

/-- Literal equation (2.23), using the paper's representative infima. -/
theorem groundStateDistanceIdentityStatement : GroundStateDistanceIdentityStatement := by
  intro n hn _ f hf
  let u := smoothCenteredObservableL2 hn f hf
  have hu := smoothCenteredObservableL2_rep hn f hf
  have hT : normalizedVandermondeTransform n (fun z => (centeredObservable n f z : ℂ))
      =ᵐ[complexGaussianMeasure n] normalizedVandermondeL2 n hn u := by
    have hrep := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
      (ginibreMassEvaluation n hn)).ae_eq hu
    filter_upwards [hrep, normalizedVandermondeL2_coeFn_public n hn u] with z hz ht
    rw [ht]
    simp only [normalizedVandermondeTransform, vandermondeTransform,
        normalizedVandermondeMultiplier]
    rw [hz, mul_assoc]
  rw [gaussianHolomorphicDistanceSq_eq_projectionNorm hn _ _ hT,
    ginibreHolomorphicDistanceSq_eq_projectionNorm hn u _ hu,
    ginibreDivisibleEntireClosedSpace_eq_holomorphic]
  exact normalizedVandermonde_projection_distance hn
    ⟨u, smoothCenteredObservableL2_symmetric hn f hf⟩

/-- Literal equation (2.24) on the full smooth compact symmetric core. -/
theorem ginibreHalfDistanceStatement : GinibreHalfDistanceStatement := by
  intro n hn _ f hf
  let := ginibreMeasure_isProbabilityMeasure hn
  let u := smoothCenteredObservableL2 hn f hf
  have hu := smoothCenteredObservableL2_rep hn f hf
  have hr : star u = u := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star u, hu] with z hs hz
    rw [hs]
    change star (u z) = u z
    rw [← hz]
    simp
  have hi : ∫ z, centeredObservable n f z ∂ginibreMeasure n = 0 := by
    have hfi := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1 (μ := ginibreMeasure n)
    simp only [centeredObservable]
    rw [integral_sub hfi (integrable_const (smoothGinibreMean n f))]
    simp [smoothGinibreMean]
  have hc : (ginibreConstantClosedSubspace n hn).starProjection u = 0 := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
    rintro c ⟨a, rfl⟩
    simp only [sub_zero]
    rw [← inner_conj_symm]
    change star (inner ℂ (ginibreConstantL2 n hn a) u) = 0
    suffices inner ℂ (ginibreConstantL2 n hn a) u = 0 by simp only [this, star_zero]
    rw [MeasureTheory.L2.inner_def]
    have he : (fun z => inner ℂ ((ginibreConstantL2 n hn a) z) (u z))
        =ᵐ[ginibreMeasure n] (fun z => (centeredObservable n f z : ℂ) * star a) := by
      filter_upwards [Lp.coeFn_const (α := Configuration n) (μ := ginibreMeasure n)
        (p := (2 : ℝ≥0∞)) a, hu] with z ha hz
      change inner ℂ ((Lp.const 2 (ginibreMeasure n) a) z) (u z) = _
      rw [ha, ← hz]
      simp [RCLike.inner_apply]
    rw [integral_congr_ae he, integral_mul_const, integral_complex_ofReal, hi]
    simp
  have hv : ‖u‖ ^ 2 = smoothGinibreVariance n f := by
    rw [← integral_norm_sq_eq_L2_norm_sq]
    unfold smoothGinibreVariance
    apply integral_congr_ae
    filter_upwards [hu] with z hz
    rw [← hz]
    simp [centeredObservable, Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [ginibreHolomorphicDistanceSq_eq_projectionNorm hn u _ hu, ← hv]
  have hgeom := ginibre_real_centered_projection_geometry n hn u hr hc
  rw [ginibreDivisibleEntireClosedSpace_eq_holomorphic]
  exact hgeom.2.2.2.2.2

end
end GinibrePoincare
