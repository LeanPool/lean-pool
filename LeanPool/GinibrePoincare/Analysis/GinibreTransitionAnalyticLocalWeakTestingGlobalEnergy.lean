/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalWeakTestingGlobalEnergy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticGlobalEnergy

/-!
# Ginibre transition analytic local weak testing global energy

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalWeak_resolvent_global_gradient_memLp`.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalWeak_resolvent_global_gradient_memLp {n : ℕ} (hn : 0 < n)
    (u f : Configuration n → ℝ) (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (huL : LocallyIntegrableOn u {z : Configuration n | CollisionFree z} volume)
    (hgL : ∀ k : Fin n × Fin 2,
      LocallyIntegrableOn (fun z => g z k) {z : Configuration n | CollisionFree z} volume)
    (hw : ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, g z k*θ z)=-(∫ z, u z*fderiv ℝ θ z (ginibreCoordinateDirection k)))
    (hu : MemLp u 2 (ginibreMeasure n)) (hf : MemLp f 2 (ginibreMeasure n))
    (hg : AEStronglyMeasurable g (ginibreMeasure n))
    (hlocal : ∀ K : Set (Configuration n), IsCompact K → K ⊆ {z | CollisionFree z} →
      MemLp g 2 (volume.restrict K))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ z, ‖u z‖ ≤ A)
    (ℓ c : ℝ) (hℓ : 0 < ℓ) (hc : 0 < c)
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      ℓ*(∫ z, u z*θ z ∂ginibreMeasure n)+
      c*(∫ z, inner ℝ (g z) (ginibreEuclideanGradient θ z) ∂ginibreMeasure n)=
      ∫ z, f z*θ z ∂ginibreMeasure n) : MemLp g 2 (ginibreMeasure n) := by
  have hSupport (η : Configuration n → ℝ) (hη : IsTheoremOneNineCore η) :
      tsupport η ⊆ {z | CollisionFree z} := by
    intro z hz
    exact (collisionFree_iff_not_mem_collisionSet z).mpr (hη.2.2.1 hz)
  apply ginibreTransitionAnalytic_local_resolvent_global_gradient_memLp hn u f g hu hf hg
    A hA hb ℓ c hℓ hc
  · intro η hη
    exact ginibreLocalWeak_cutoff_gradient_memLp hn g η hη.1 hη.2.1
      (hlocal (tsupport η) hη.2.1 (hSupport η hη))
  · intro η hη
    exact ginibreLocalWeak_resolvent_cutoff_identity hn u f g huL hgL hw hu hf η hη.1 hη.2.1
      (hSupport η hη) (hlocal (tsupport η) hη.2.1 (hSupport η hη)) ℓ c heq

end
end GinibrePoincare
