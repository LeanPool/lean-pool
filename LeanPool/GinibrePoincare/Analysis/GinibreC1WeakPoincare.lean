/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreC1WeakPoincare.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! # Ordinary weak gradients of actual smooth Ginibre L² pairs

The first theorem uses Lebesgue integration by parts with compact tests away
from collisions, after transferring almost-everywhere representatives from
Ginibre measure to volume. It therefore verifies the ordinary distributional
gradient identity rather than defining it by closure. The finite-energy
Poincaré theorem then inserts these classical value-gradient representatives
into the proved symmetric weak-domain inequality.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Every smooth value with its actual square-integrable classical gradient
satisfies the independently defined distributional identities. -/
theorem ginibre_C1_distributional_gradient (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (f : Configuration n → ℝ) (hs : ContDiff ℝ 1 f)
    (hu : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hg : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
      ginibreEuclideanGradient f) : IsGinibreDistributionalGradient n u g := by
  have hu' := (ginibre_ae_eq_iff_volume n hn _ _).mp hu
  have hg' := (ginibre_ae_eq_iff_volume n hn _ _).mp hg
  refine ⟨ginibre_memLp_locallyIntegrable_collisionFree hn u (Lp.memLp u), ?_, ?_⟩
  · intro k
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) k
    exact ginibre_memLp_locallyIntegrable_collisionFree hn _ (P.comp_memLp g)
  · intro k θ hθ hc hsub
    have hdf : Continuous (fun z => fderiv ℝ f z (ginibreCoordinateDirection k)) :=
      (hs.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have ht := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      ((hdf.mul hθ.continuous).integrable_of_hasCompactSupport hc.mul_left)
      ((hs.continuous.mul ((hθ.continuous_fderiv (by simp)).clm_apply
          continuous_const)).integrable_of_hasCompactSupport
        (hc.fderiv_apply ℝ _).mul_left)
      ((hs.continuous.mul hθ.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun z _ => (hs.differentiable (by norm_num)).differentiableAt)
      (fun z _ => (hθ.differentiable (by simp)).differentiableAt)
    have hl : (∫ z, g z k * θ z) = ∫ z, fderiv ℝ f z (ginibreCoordinateDirection k) * θ z := by
      apply integral_congr_ae
      filter_upwards [hg'] with z hz
      rw [hz, ginibreEuclideanGradient_coordinate]
    have hr : (∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)) =
        ∫ z, f z * fderiv ℝ θ z (ginibreCoordinateDirection k) := by
      apply integral_congr_ae
      filter_upwards [hu'] with z hz
      rw [hz]
    rw [hl, hr, ht]
    simp

/-- The sharp original Poincaré inequality for every finite-energy symmetric
C¹ function, without an assumed Sobolev graph or distributional identity. -/
theorem ginibre_C1_finite_energy_poincare {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ 1 f)
    (hsym : ∀ σ : Fin n ≃ Fin n, ∀ z, f (z ∘ σ) = f z)
    (hfl : MemLp f 2 (ginibreMeasure n))
    (hgl : MemLp (ginibreEuclideanGradient f) 2 (ginibreMeasure n)) :
    smoothGinibreVariance n f ≤
      (1 / (2 * (n : ℝ))) * ∫ z, realGradientNormSq f z ∂ginibreMeasure n := by
  let u : Lp ℝ 2 (ginibreMeasure n) := hfl.toLp f
  let g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) :=
    hgl.toLp (ginibreEuclideanGradient f)
  have hu : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f := hfl.coeFn_toLp
  have hg : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
      =ᵐ[ginibreMeasure n] ginibreEuclideanGradient f := hgl.coeFn_toLp
  have hweak := ginibre_C1_distributional_gradient n hn u g f hf hu hg
  have hsymu (σ : ParticlePermutation n) : ginibreRealPermutationL2 σ u = u := by
    apply Lp.ext
    filter_upwards [ginibreRealPermutationL2_ae σ u,
      (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp hu, hu]
      with z hp hc hz
    dsimp only [Function.comp_def] at hc
    rw [hp, hc, hz]
    exact hsym σ z
  have hsympair : IsGinibreSymmetricWeakPair (u, g) := by
    intro σ
    refine ⟨hsymu σ, ?_⟩
    have hw := ginibreDistributionalGradient_permute hn σ u g hweak
    rw [hsymu σ] at hw
    exact ginibre_distributional_gradient_unique n hn u _ g hw hweak
  have hmean : ginibreL2Mean n u = smoothGinibreMean n f :=
    integral_congr_ae hu
  have hvar : ginibreL2Variance n hn u = smoothGinibreVariance n f := by
    rw [ginibreL2Variance, hmean, ← integral_square_eq_L2_norm_sq]
    unfold smoothGinibreVariance
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u (ginibreRealConstantL2 n hn (smoothGinibreMean n f)),
      hu, ginibreRealConstantL2_ae n hn (smoothGinibreMean n f)] with z hs hz hc
    rw [hs]
    change ((u : Configuration n → ℝ) z -
      (ginibreRealConstantL2 n hn (smoothGinibreMean n f) : Configuration n → ℝ) z) ^ 2 = _
    rw [hz, hc]
  have he : ginibreWeakEnergy n g =
      (1 / (n : ℝ)) * ∫ z, realGradientNormSq f z ∂ginibreMeasure n := by
    rw [ginibreWeakEnergy, ← integral_norm_sq_eq_L2_norm_sq]
    congr 1
    apply integral_congr_ae
    filter_upwards [hg] with z hz
    rw [hz, ginibreEuclideanGradient_norm_sq]
  have h := ginibre_symmetric_weak_poincare hn u g hweak hsympair
  rw [hvar, he] at h
  convert h using 1
  ring
end
end GinibrePoincare
