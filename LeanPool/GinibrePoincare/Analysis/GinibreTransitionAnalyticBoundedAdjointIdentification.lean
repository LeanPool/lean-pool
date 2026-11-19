/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticBoundedAdjointIdentification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityAdjointDensity
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingDistributional
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingLocalIntegrability
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticUnrestrictedWeakComparison

/-!
# Ginibre transition analytic bounded adjoint identification

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreTransitionAnalytic_bounded_adjoint_identification`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Every genuine bounded adjoint resolvent solution with symmetric forcing
is the actual analytic resolvent. Solution symmetry and its entire gradient
are derived, rather than required. -/
theorem ginibreTransitionAnalytic_bounded_adjoint_identification
    (n : ℕ) (hn : 0 < n) (f : ginibreFullSymmetricValues n)
    (u : Configuration n → ℝ) (hu : MemLp u 2 (ginibreMeasure n))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ z, ‖u z‖ ≤ A)
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, u z*θ z ∂ginibreMeasure n)-(∫ z, u z*ginibrePregenerator n θ z ∂ginibreMeasure n) =
        (∫ z, f.val z*θ z ∂ginibreMeasure n)) :
    hu.toLp u = (ginibreFullSymmetricResolvent n hn f).val := by
  have hf : MemLp (f.val : Configuration n → ℝ) 2 (ginibreMeasure n) := Lp.memLp _
  obtain ⟨g, hgm, hlocal, hraw⟩ := ginibreTransitionAnalytic_compact_adjoint_exists_local_gradient n
      hn u f.val hu hf heq
  have hw : ∀ k (θ : Configuration n → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, g z k*θ z) = -(∫ z, u z*fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
    intro k θ hθ hc hs
    calc
      _ = ∫ z, θ z*g z k := by
        apply integral_congr_ae
        exact ae_of_all volume fun z => by dsimp only; exact mul_comm _ _
      _ = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*u z) := hraw k θ hθ hc hs
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact ae_of_all volume fun z => by dsimp only; exact mul_comm _ _
  have hP : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      1*(∫ z, u z*ginibrePregenerator n θ z ∂ginibreMeasure n) =
        1*(∫ z, u z*θ z ∂ginibreMeasure n)-(∫ z, f.val z*θ z ∂ginibreMeasure n) := by
    intro θ hθ hc hs
    have he := heq θ hθ hc hs
    linear_combination -he
  have hgrad := ginibreLocalWeak_adjoint_to_gradient_equation hn u f.val g hu hw hlocal 1 1 hP
  have hg : MemLp g 2 (ginibreMeasure n) :=
    ginibreLocalWeak_resolvent_global_gradient_memLp hn u f.val g
      (ginibre_memLp_locallyIntegrable_collisionFree hn u hu)
      (ginibreLocalWeak_compact_L2_coordinates_locallyIntegrable g hlocal) hw hu hf
      hgm.aestronglyMeasurable hlocal A hA hb 1 (1/(n : ℝ)) (by norm_num) (by positivity) hgrad
  have hdist := ginibreLocalWeak_global_distributional_pair hn u g hu hg hw
  have hcompact : ∀ p ∈ ginibreInteriorSmoothPair n,
      inner ℝ (hu.toLp u) p.1+(1/(n : ℝ))*inner ℝ (hg.toLp g) p.2=inner ℝ f.val p.1 := by
    intro p hp
    obtain ⟨θ, hθ, hθc, hθs, hpval, hpgrad⟩ := hp
    have huv : inner ℝ (hu.toLp u) p.1 = ∫ z, u z*θ z ∂ginibreMeasure n := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp, hpval] with z hz hv
      change p.1 z*(hu.toLp u) z = u z*θ z
      rw [hz, hv, mul_comm]
    have hgv : inner ℝ (hg.toLp g) p.2 =
        ∫ z, inner ℝ (g z) (ginibreEuclideanGradient θ z) ∂ginibreMeasure n := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp, hpgrad] with z hz hv
      change inner ℝ ((hg.toLp g) z) (p.2 z) = _
      rw [hz, hv]
    have hfv : inner ℝ f.val p.1 = ∫ z, f.val z*θ z ∂ginibreMeasure n := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hpval] with z hv
      change p.1 z*f.val z = f.val z*θ z
      rw [hv, mul_comm]
    rw [huv, hgv, hfv]
    simpa only [one_mul] using hgrad θ hθ hθc hθs
  apply ginibreFullSymmetricResolvent_unique_unrestricted_weak hn f (hu.toLp u) (hg.toLp g) hdist
  intro w h hw
  exact ginibreDistributionalWeakPair_compact_equation_complete hn (hu.toLp u) f.val (hg.toLp g)
    hcompact w h hw

end
end GinibrePoincare
