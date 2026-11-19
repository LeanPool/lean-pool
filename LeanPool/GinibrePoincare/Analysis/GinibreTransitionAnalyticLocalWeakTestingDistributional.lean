/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalWeakTestingDistributional.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingGlobalEnergy
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingGreen

/-!
# Ginibre transition analytic local weak testing distributional

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalWeak_global_distributional_pair`.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalWeak_global_distributional_pair {n : ℕ} (hn : 0 < n)
    (u : Configuration n → ℝ) (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : MemLp u 2 (ginibreMeasure n)) (hg : MemLp g 2 (ginibreMeasure n))
    (hw : ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k))) :
    IsGinibreDistributionalGradient n (hu.toLp u) (hg.toLp g) := by
  refine ⟨ginibre_memLp_locallyIntegrable_collisionFree hn _ (Lp.memLp _),?_,?_⟩
  · intro k
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) k
    exact ginibre_memLp_locallyIntegrable_collisionFree hn _ (P.comp_memLp (hg.toLp g))
  · intro k θ hθ hc hs
    have hu' := (ginibre_ae_eq_iff_volume n hn _ _).mp hu.coeFn_toLp
    have hg' := (ginibre_ae_eq_iff_volume n hn _ _).mp hg.coeFn_toLp
    have hl : (∫ z, hg.toLp g z k*θ z) = (∫ z, g z k*θ z) := by
      apply integral_congr_ae
      filter_upwards [hg'] with z hz
      rw [hz]
    have hr : (∫ z, hu.toLp u z*fderiv ℝ θ z (ginibreCoordinateDirection k)) =
        (∫ z, u z*fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
      apply integral_congr_ae
      filter_upwards [hu'] with z hz
      rw [hz]
    rw [hl, hr]
    exact hw k θ hθ hc hs

end
end GinibrePoincare
