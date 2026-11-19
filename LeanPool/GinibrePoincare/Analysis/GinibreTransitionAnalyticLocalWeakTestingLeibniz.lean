/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalWeakTestingLeibniz.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreArbitraryWeakPairApproximation
public import LeanPool.GinibrePoincare.Analysis.GinibreValueTruncationWeakChain
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakPermutation
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Ginibre transition analytic local weak testing leibniz

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalWeak_distributional_gradient_mul`.
-/

@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalWeak_distributional_gradient_mul (n : ℕ) (hn : 0 < n)
    (u : Configuration n → ℝ)
    (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : LocallyIntegrableOn u {z : Configuration n | CollisionFree z} volume)
    (hgl : ∀ k, LocallyIntegrableOn (fun z => g z k) {z : Configuration n | CollisionFree z} volume)
    (hw : ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)))
    (χ : Configuration n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (v : Lp ℝ 2 (ginibreMeasure n))
    (h : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hv : (v : Configuration n → ℝ) =ᵐ[ginibreMeasure n] fun z => χ z * u z)
    (hh : (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
      =ᵐ[ginibreMeasure n] fun z => χ z • g z + u z • ginibreEuclideanGradient χ z) :
    IsGinibreDistributionalGradient n v h := by
  have hv' := (ginibre_ae_eq_iff_volume n hn _ _).mp hv
  have hh' := (ginibre_ae_eq_iff_volume n hn _ _).mp hh
  refine ⟨ginibre_memLp_locallyIntegrable_collisionFree hn v (Lp.memLp v), ?_, ?_⟩
  · intro k
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ :=
      PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) k
    have hm : MemLp (fun z => h z k) 2 (ginibreMeasure n) := P.comp_memLp h
    exact ginibre_memLp_locallyIntegrable_collisionFree hn _ hm
  · intro k θ hθ hθc hs
    have hm : ContDiff ℝ ∞ (χ * θ) := hχ.mul hθ
    have hmc : HasCompactSupport (χ * θ) := hθc.mul_left
    have hms : tsupport (χ * θ) ⊆ {z | CollisionFree z} :=
      (tsupport_mul_subset_right).trans hs
    have he := hw k (χ * θ) hm hmc hms
    have hd (z : Configuration n) :
        fderiv ℝ (χ * θ) z (ginibreCoordinateDirection k) =
          χ z * fderiv ℝ θ z (ginibreCoordinateDirection k) +
            θ z * fderiv ℝ χ z (ginibreCoordinateDirection k) := by
      rw [fderiv_mul (hχ.differentiable (by simp)).differentiableAt
        (hθ.differentiable (by simp)).differentiableAt]
      simp only [add_apply, smul_apply, smul_eq_mul]
    have hi₁ : Integrable (fun z => g z k * (χ z * θ z)) := by
      exact integrable_mul_collisionFree_test _ _ (hgl k) hm.continuous hmc hms
    have hi₂ : Integrable (fun z => u z *
        (fderiv ℝ χ z (ginibreCoordinateDirection k) * θ z)) := by
      have ht : Continuous (fun z => fderiv ℝ χ z (ginibreCoordinateDirection k) * θ z) :=
        ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).mul hθ.continuous
      have htc : HasCompactSupport (fun z =>
          fderiv ℝ χ z (ginibreCoordinateDirection k) * θ z) := hθc.mul_left
      have hts : tsupport (fun z =>
          fderiv ℝ χ z (ginibreCoordinateDirection k) * θ z) ⊆ {z | CollisionFree z} :=
        tsupport_mul_subset_right.trans hs
      exact integrable_mul_collisionFree_test _ _ hu ht htc hts
    have hi₃ : Integrable (fun z => u z *
        (χ z * fderiv ℝ θ z (ginibreCoordinateDirection k))) := by
      have ht : Continuous (fun z => χ z * fderiv ℝ θ z (ginibreCoordinateDirection k)) :=
        hχ.continuous.mul ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)
      have htc : HasCompactSupport (fun z => χ z *
          fderiv ℝ θ z (ginibreCoordinateDirection k)) := (hθc.fderiv_apply ℝ _).mul_left
      have hts : tsupport (fun z => χ z *
          fderiv ℝ θ z (ginibreCoordinateDirection k)) ⊆ {z | CollisionFree z} :=
        tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ _).trans hs)
      exact integrable_mul_collisionFree_test _ _ hu ht htc hts
    have hl : (∫ z, h z k * θ z) =
        (∫ z, g z k * (χ z * θ z)) +
          ∫ z, u z * (fderiv ℝ χ z (ginibreCoordinateDirection k) * θ z) := by
      rw [← integral_add hi₁ hi₂]
      apply integral_congr_ae
      filter_upwards [hh'] with z hz
      rw [hz]
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        ginibreEuclideanGradient_coordinate]
      ring
    have hr : (∫ z, v z * fderiv ℝ θ z (ginibreCoordinateDirection k)) =
        ∫ z, u z * (χ z * fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
      apply integral_congr_ae
      filter_upwards [hv'] with z hz
      rw [hz]
      ring
    have hdint : (∫ z, u z * fderiv ℝ (χ * θ) z (ginibreCoordinateDirection k)) =
        (∫ z, u z * (χ z * fderiv ℝ θ z (ginibreCoordinateDirection k))) +
          ∫ z, u z * (fderiv ℝ χ z (ginibreCoordinateDirection k) * θ z) := by
      rw [← integral_add hi₃ hi₂]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by dsimp only; rw [hd]; ring)
    rw [hdint] at he
    change (∫ z, g z k * (χ z * θ z)) = -_ at he
    rw [hl, hr]
    linarith

end
end GinibrePoincare
