/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalWeakTestingIdentity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingContinuity
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingLocalization
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation

/-!
# Ginibre transition analytic local weak testing identity

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalWeak_resolvent_cutoff_identity`.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalWeak_smooth_pair_equation {n : ℕ}
    (u f : Configuration n → ℝ) (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (η : Configuration n → ℝ) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ {z | CollisionFree z})
    (ℓ c : ℝ)
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      ℓ*(∫ z, u z*θ z ∂ginibreMeasure n)+
      c*(∫ z, inner ℝ (g z) (ginibreEuclideanGradient θ z) ∂ginibreMeasure n)=
      ∫ z, f z*θ z ∂ginibreMeasure n)
    (hA : MemLp (fun z => η z*u z) 2 (ginibreMeasure n))
    (hB : MemLp (fun z => η z • g z) 2 (ginibreMeasure n))
    (hH : MemLp (fun z => inner ℝ (g z) (ginibreEuclideanGradient η z)) 2 (ginibreMeasure n))
    (hC : MemLp (fun z => η z*f z) 2 (ginibreMeasure n))
    (q : Lp ℝ 2 (ginibreMeasure n) × Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hq : q ∈ ginibreInteriorSmoothPair n) :
    ℓ*inner ℝ (hA.toLp _) q.1+c*inner ℝ (hB.toLp _) q.2+
      c*inner ℝ (hH.toLp _) q.1=inner ℝ (hC.toLp _) q.1 := by
  obtain ⟨φ, hφ, hφc, hφs, hv, hG⟩ := hq
  have h := heq (η*φ) (hη.mul hφ) hc.mul_right
    (tsupport_mul_subset_left.trans hs)
  have hcoA := hA.coeFn_toLp
  have hcoB := hB.coeFn_toLp
  have hcoH := hH.coeFn_toLp
  have hcoC := hC.coeFn_toLp
  have ha : inner ℝ (hA.toLp _) q.1 = ∫ z, u z*(η*φ) z ∂ginibreMeasure n := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hcoA, hv] with z hz hz'
    simp only [hz, hz', Real.inner_apply, Pi.mul_apply]
    ring
  have hb : inner ℝ (hB.toLp _) q.2+inner ℝ (hH.toLp _) q.1 =
      ∫ z, inner ℝ (g z) (ginibreEuclideanGradient (η*φ) z) ∂ginibreMeasure n := by
    rw [L2.inner_def, L2.inner_def,← integral_add (L2.integrable_inner (𝕜 := ℝ) (hB.toLp _) q.2)
      (L2.integrable_inner (𝕜 := ℝ) (hH.toLp _) q.1)]
    apply integral_congr_ae
    filter_upwards [hcoB, hcoH, hv, hG] with z hz hz' hv' hG'
    rw [hz, hz', hv', hG', ginibreEuclideanGradient_mul φ η hφ hη]
    simp only [inner_add_right, inner_smul_right, real_inner_smul_left, Real.inner_apply]
    ring
  have hc' : inner ℝ (hC.toLp _) q.1 = ∫ z, f z*(η*φ) z ∂ginibreMeasure n := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hcoC, hv] with z hz hz'
    simp only [hz, hz', Real.inner_apply, Pi.mul_apply]
    ring
  rw [← ha,← hb,← hc'] at h
  linarith

theorem ginibreLocalWeak_resolvent_cutoff_identity {n : ℕ} (hn : 0 < n)
    (u f : Configuration n → ℝ) (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (huL : LocallyIntegrableOn u {z : Configuration n | CollisionFree z} volume)
    (hgL : ∀ k : Fin n × Fin 2,
      LocallyIntegrableOn (fun z => g z k) {z : Configuration n | CollisionFree z} volume)
    (hw : ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, g z k*θ z)=-(∫ z, u z*fderiv ℝ θ z (ginibreCoordinateDirection k)))
    (hu : MemLp u 2 (ginibreMeasure n)) (hf : MemLp f 2 (ginibreMeasure n))
    (η : Configuration n → ℝ) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ {z | CollisionFree z})
    (hg : MemLp g 2 (volume.restrict (tsupport η)))
    (ℓ c : ℝ)
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      ℓ*(∫ z, u z*θ z ∂ginibreMeasure n)+
      c*(∫ z, inner ℝ (g z) (ginibreEuclideanGradient θ z) ∂ginibreMeasure n)=
      ∫ z, f z*θ z ∂ginibreMeasure n) :
    ℓ*(∫ z, (η z*u z)^2 ∂ginibreMeasure n)+
      c*(∫ z, ‖η z • g z‖^2 ∂ginibreMeasure n)=
      (∫ z, (η z*f z)*(η z*u z) ∂ginibreMeasure n)-
        2*c*(∫ z, inner ℝ (η z • g z) (u z • ginibreEuclideanGradient η z) ∂ginibreMeasure n) := by
  obtain ⟨hA, hG⟩ := ginibreLocalWeak_cutoff_pair_memLp hn u g hu η hη hc hg
  have hB := ginibreLocalWeak_cutoff_gradient_memLp hn g η hη hc hg
  have hH := ginibreLocalWeak_cutoff_inner_memLp hn g η hη hc hg
  have hC : MemLp (fun z => η z*f z) 2 (ginibreMeasure n) := by
    simpa only [smul_eq_mul] using ginibreLocalWeak_compact_smul_memLp
      (ginibreMeasure n) η hη.continuous hc f hf
  have hE : MemLp (fun z => u z • ginibreEuclideanGradient η z) 2 (ginibreMeasure n) := by
    apply (hG.sub hB).ae_eq
    exact ae_of_all _ (fun z => by simp)
  obtain ⟨q, hq, hqt⟩ := ginibreLocalWeak_cutoff_smooth_sequence hn u g huL hgL hw η hη hc hs hA hG
  have hh := ginibreLocalWeak_pairing_limit (hA.toLp _) (hC.toLp _) (hH.toLp _) (hB.toLp _)
    ℓ c q (hA.toLp _) (hG.toLp _) hqt
    (fun m => ginibreLocalWeak_smooth_pair_equation u f g η hη hc hs ℓ c heq hA hB hH hC (q m) (hq
        m))
  have hsum : hG.toLp _ = hB.toLp _ + hE.toLp _ := by
    apply Lp.ext
    filter_upwards [hG.coeFn_toLp, hB.coeFn_toLp, hE.coeFn_toLp,
      Lp.coeFn_add (hB.toLp _) (hE.toLp _)] with z h1 h2 h3 h4
    rw [h1, h4]
    simp only [Pi.add_apply, h2, h3]
  rw [hsum, inner_add_right] at hh
  have ha : inner ℝ (hA.toLp _) (hA.toLp _) = ∫ z, (η z*u z)^2 ∂ginibreMeasure n := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hA.coeFn_toLp] with z hz
    simp only [hz, Real.inner_apply]
    ring
  have hb : inner ℝ (hB.toLp _) (hB.toLp _) = ∫ z, ‖η z • g z‖^2 ∂ginibreMeasure n := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hB.coeFn_toLp] with z hz
    rw [hz, real_inner_self_eq_norm_sq]
  have hx : inner ℝ (hB.toLp _) (hE.toLp _) =
      ∫ z, inner ℝ (η z • g z) (u z • ginibreEuclideanGradient η z) ∂ginibreMeasure n := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hB.coeFn_toLp, hE.coeFn_toLp] with z hz hz'
    rw [hz, hz']
  have hcross : inner ℝ (hH.toLp _) (hA.toLp _) = inner ℝ (hB.toLp _) (hE.toLp _) := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hH.coeFn_toLp, hA.coeFn_toLp, hB.coeFn_toLp, hE.coeFn_toLp] with z h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    simp only [Real.inner_apply, real_inner_smul_left, inner_smul_right]; ring
  have hf' : inner ℝ (hC.toLp _) (hA.toLp _) =
      ∫ z, (η z*f z)*(η z*u z) ∂ginibreMeasure n := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hC.coeFn_toLp, hA.coeFn_toLp] with z hz hz'
    simp only [hz, hz', Real.inner_apply]
  rw [ha, hb, hcross, hx, hf'] at hh
  linarith

end
end GinibrePoincare
