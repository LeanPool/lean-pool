/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreSmoothDistributionalGradient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakSobolevMultipliers
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Ordinary weak gradients of actual smooth Ginibre L² pairs -/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Every smooth value with its actual square-integrable classical gradient
satisfies the independently defined distributional identities. -/
theorem ginibre_smooth_distributional_gradient (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (f : Configuration n → ℝ) (hs : ContDiff ℝ ∞ f)
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
      (hs.continuous_fderiv (by simp)).clm_apply continuous_const
    have ht := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      ((hdf.mul hθ.continuous).integrable_of_hasCompactSupport hc.mul_left)
      ((hs.continuous.mul ((hθ.continuous_fderiv (by simp)).clm_apply
        continuous_const)).integrable_of_hasCompactSupport
        (hc.fderiv_apply ℝ _).mul_left)
      ((hs.continuous.mul hθ.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun z _ => (hs.differentiable (by simp)).differentiableAt)
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
end
end GinibrePoincare
