/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoungSmoothGeometry.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungMollifier
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultConfiguration

/-!
# Correspondence Dolbeault Young smooth geometry

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultCoordinateConvolutionPointwise_smooth`,
`dolbeaultCoordinateConvolutionPointwise_compact`.
-/

@[expose] public section
open MeasureTheory Set
open scoped ContDiff Convolution
namespace GinibrePoincare
noncomputable section

/-- Pointwise convolution in the `j`-th coordinate: `x ↦ ∫ y, k y * f (x - Pi.single j y)`. -/
def dolbeaultCoordinateConvolutionPointwise {n : ℕ} (j : Fin n) (k : ℂ → ℂ)
    (f : Configuration n → ℂ) (x : Configuration n) : ℂ :=
  ∫ y : ℂ, k y*f (x-Pi.single j y)

theorem dolbeaultCoordinateConvolutionPointwise_smooth {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : LocallyIntegrable k volume)
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (dolbeaultCoordinateConvolutionPointwise j k f) := by
  obtain ⟨M, hM⟩ := hc.isBounded.exists_norm_le
  let a : Configuration n → ℂ → ℂ := fun p z => f (dolbeaultReplaceCoordinate j (p, z))
  have ha : ContDiff ℝ ∞ (Function.uncurry a) := hf.comp (dolbeaultReplaceCoordinate j).contDiff
  have hs (p : Configuration n) (z : ℂ) (hz : z∉Metric.closedBall (0 : ℂ) M) : a p z=0 := by
    by_contra hn
    have hb := hM _ (subset_tsupport f hn)
    have he : (dolbeaultReplaceCoordinate j (p, z)) j=z := by simp
                                                                [dolbeaultReplaceCoordinate_apply]
    have hl := norm_le_pi_norm (dolbeaultReplaceCoordinate j (p, z)) j
    rw [he] at hl
    apply hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using hl.trans hb
  have h := contDiffOn_convolution_right_with_param (ContinuousLinearMap.mul ℝ ℂ)
    (s := (univ : Set (Configuration n))) isOpen_univ
    (isCompact_closedBall (0 : ℂ) M) (fun p z _ hz => hs p z hz) hk
    (show ContDiffOn ℝ ∞ (Function.uncurry a) (univ ×ˢ univ) from ha.contDiffOn)
  have hg : ContDiff ℝ ∞ (fun q : Configuration n × ℂ =>
      (k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] a q.1) q.2) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using h
  have ht : ContDiff ℝ ∞ (fun x : Configuration n =>
      (k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] a x) (x j)) :=
    hg.comp (contDiff_id.prodMk (contDiff_apply ℝ (fun _ => ℂ) j))
  have he : (fun x : Configuration n =>
      (k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] a x) (x j)) =
      dolbeaultCoordinateConvolutionPointwise j k f := by
    funext x
    unfold convolution dolbeaultCoordinateConvolutionPointwise
    congr 1
    funext y
    change k y*f (dolbeaultReplaceCoordinate j (x, x j-y)) = k y*f (x-Pi.single j y)
    congr 2
    ext l
    by_cases hl : l=j
    · subst l
      simp [dolbeaultReplaceCoordinate_apply]
    · simp [dolbeaultReplaceCoordinate_apply, hl]
  rw [he] at ht
  exact ht

theorem dolbeaultCoordinateConvolutionPointwise_compact {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : HasCompactSupport k)
    (f : Configuration n → ℂ) (hc : HasCompactSupport f) :
    HasCompactSupport (dolbeaultCoordinateConvolutionPointwise j k f) := by
  obtain ⟨M, hM⟩ := hc.isBounded.exists_norm_le
  obtain ⟨S, hS⟩ := hk.isBounded.exists_norm_le
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Configuration n) (M+S))
  intro x hx
  unfold dolbeaultCoordinateConvolutionPointwise
  have he : (fun y : ℂ => k y*f (x-Pi.single j y)) = 0 := by
    funext y
    by_cases hy : k y=0
    · simp [hy]
    by_cases hf : f (x-Pi.single j y)=0
    · simp [hf]
    have hb := hM _ (subset_tsupport f hf)
    have hb' := hS _ (subset_tsupport k hy)
    have hn := norm_add_le (x-Pi.single j y) (Pi.single j y : Configuration n)
    rw [sub_add_cancel, Pi.norm_single] at hn
    have hxin : x∈Metric.closedBall (0 : Configuration n) (M+S) := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      linarith
    exact False.elim (hx hxin)
  rw [he]
  exact integral_zero ℂ ℂ

end
end GinibrePoincare
