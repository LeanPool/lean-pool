/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalWeakTestingApproximation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingLeibniz

/-!
# Ginibre transition analytic local weak testing approximation

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalWeak_cutoff_smooth_sequence`.
-/

@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalWeak_gradient_tsupport {n : ℕ} (η : Configuration n → ℝ) :
    tsupport (ginibreEuclideanGradient η) ⊆ tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro z hz
  by_contra hn
  have hd : fderiv ℝ η z = 0 := fderiv_of_notMem_tsupport ℝ hn
  apply hz
  ext k
  simp only [ginibreEuclideanGradient_coordinate, hd, zero_apply, PiLp.zero_apply]

theorem ginibreLocalWeak_cutoff_smooth_sequence {n : ℕ} (hn : 0 < n)
    (u : Configuration n → ℝ) (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : LocallyIntegrableOn u {z : Configuration n | CollisionFree z} volume)
    (hgl : ∀ k : Fin n × Fin 2, LocallyIntegrableOn (fun z => g z k) {z : Configuration n |
        CollisionFree z} volume)
    (hw : ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)))
    (η : Configuration n → ℝ) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ {z | CollisionFree z})
    (hv : MemLp (fun z => η z*u z) 2 (ginibreMeasure n))
    (hG : MemLp (fun z => η z • g z + u z • ginibreEuclideanGradient η z) 2 (ginibreMeasure n)) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
        Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ ginibreInteriorSmoothPair n) ∧
      Tendsto q atTop (𝓝 (hv.toLp (fun z => η z*u z),
        hG.toLp (fun z => η z • g z + u z • ginibreEuclideanGradient η z))) := by
  let v := hv.toLp (fun z => η z*u z)
  let G := hG.toLp (fun z => η z • g z + u z • ginibreEuclideanGradient η z)
  have hv' : (v : Configuration n → ℝ) =ᵐ[ginibreMeasure n] (fun z => η z*u z) := hv.coeFn_toLp
  have hG' : (G : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
      (fun z => η z • g z + u z • ginibreEuclideanGradient η z) := hG.coeFn_toLp
  have hd := ginibreLocalWeak_distributional_gradient_mul n hn u g hu hgl hw η hη v G hv' hG'
  have hvC : HasCompactSupport (fun z => η z*u z) := hc.mul_right
  have hGC : HasCompactSupport (fun z => η z • g z + u z • ginibreEuclideanGradient η z) :=
    (hc.smul_right (f' := g)).add
      ((compactSupport_ginibreEuclideanGradient η hc).smul_left (f := u))
  have hvS : tsupport (fun z => η z*u z) ⊆ {z | CollisionFree z} :=
    tsupport_mul_subset_left.trans hs
  have hGS : tsupport (fun z => η z • g z + u z • ginibreEuclideanGradient η z) ⊆ {z | CollisionFree
      z} :=
    (tsupport_add (fun z => η z • g z) (fun z => u z • ginibreEuclideanGradient η z)).trans
      (Set.union_subset
        ((tsupport_smul_subset_left η g).trans hs)
        ((tsupport_smul_subset_right u (ginibreEuclideanGradient η)).trans
          ((ginibreLocalWeak_gradient_tsupport η).trans hs)))
  exact ginibreInteriorWeakPair_exists_smoothSequence hn v G hd _ _ hv' hG' hvC hGC hvS hGS

end
end GinibrePoincare
