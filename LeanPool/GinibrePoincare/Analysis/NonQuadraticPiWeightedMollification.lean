/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiWeightedMollification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiTensorConvolution
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiConvolutionSupport
public import Mathlib.Basic.Complex.BigOperators

/-!
# Non quadratic pi weighted mollification

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `weightedPiBumpAverage_tendsto`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology Pointwise ENNReal
namespace GinibrePoincare
noncomputable section

/-- The normalised bump `φ.normed volume`, as a complex compactly supported planar test. -/
def planarPiNormalizedBumpTest (φ : ContDiffBump (0 : ℂ)) : PlanarComplexCompactTest :=
  ⟨fun x => (φ.normed volume x : ℂ), Complex.ofRealCLM.contDiff.comp φ.contDiff_normed,
    φ.hasCompactSupport_normed.comp_left (g := Complex.ofReal) Complex.ofReal_zero⟩

/-- The value component of `∫ a, f a • G a`, where `G a` is the weighted `∂̄`-graph of the pure
tensor of normalised bumps translated to the points `a i`. -/
def weightedPiBumpAverage {d : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ : ContDiffBump (0 : ℂ)) (f : Configuration (d + 1) → ℂ) : PlanarPiLebesgueL2 (d+1) :=
  (∫ a, f a • planarPiPureDbarGraph n V hV
    (fun i => planarComplexTestTranslate (planarPiNormalizedBumpTest φ) (a i))
    ∂Measure.pi (fun _ => (volume : Measure ℂ))).1

theorem weightedPiBumpAverage_coeFn {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ : ContDiffBump (0 : ℂ))
    (f : Configuration (d + 1) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    (weightedPiBumpAverage n V hV φ f : Configuration (d+1) → ℂ)
      =ᵐ[volume] (fun x => (∫ a, f a * (piPlanarBump (d+1) φ (x-a) : ℂ)) * piPotentialHalfWeight
          (d+1) n V x) := by
  have he := planarPiTranslatedGraph_integral_value_ae n V hV
    (fun _ => planarPiNormalizedBumpTest φ) f hf hc
  simpa only [weightedPiBumpAverage, planarPiNormalizedBumpTest, piPlanarBump,
    Complex.ofReal_prod, Pi.sub_apply, MeasureTheory.volume_pi] using he
theorem weightedPiBumpAverage_tendsto {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (f : Configuration (d + 1) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun m => weightedPiBumpAverage n V hV (φ m) f) atTop
      (𝓝 (piCompactFunctionL2 (d+1) (fun x => f x * piPotentialHalfWeight (d+1) n V x)
        (hf.mul (piPotentialHalfWeight_continuous (d+1) n V hV)) hc.mul_right)) := by
  let S := tsupport f + Metric.closedBall (0 : Configuration (d+1)) 1
  have hS : IsCompact S := IsCompact.add hc (isCompact_closedBall _ _)
  let w := piPotentialHalfWeight (d+1) n V
  have hw : Continuous w := piPotentialHalfWeight_continuous (d+1) n V hV
  obtain ⟨T, hT⟩ := exists_compactPiL2WeightMultiplier (d+1) w hw S hS
  let u := piCompactFunctionL2 (d+1) f hf hc
  let uw := piCompactFunctionL2 (d+1) (fun x => f x * w x) (hf.mul hw) hc.mul_right
  have hu : (u : Configuration (d+1) → ℂ) =ᵐ[(volume : Measure (Configuration (d+1)))] f :=
    (hf.memLp_of_hasCompactSupport hc).coeFn_toLp
  have huw : (uw : Configuration (d+1) → ℂ) =ᵐ[(volume : Measure (Configuration (d+1)))] (fun x => f
      x * w x) :=
    ((hf.mul hw).memLp_of_hasCompactSupport hc.mul_right).coeFn_toLp
  have hfS (x : Configuration (d+1)) (hx : x ∉ S) : f x = 0 := by
    by_contra h
    apply hx
    exact ⟨x, subset_closure h, 0, by simp, by simp⟩
  have hTu : T u = uw := by
    apply Lp.ext
    filter_upwards [hT u, hu, huw] with x ht hf' hw'
    rw [ht, hf', hw']
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
      exact mul_comm _ _
    · simp only [Set.indicator_of_notMem hx, hfS x hx, zero_mul, mul_zero]
  have hsmall : ∀ᶠ m in atTop, (φ m).rOut ≤ 1 :=
    ((tendsto_order.mp hφ).2 1 (by norm_num)).mono (fun m hm => hm.le)
  have he : ∀ᶠ m in atTop, T (piL2BumpAverage (d+1) (φ m) u) =
      weightedPiBumpAverage n V hV (φ m) f := by
    filter_upwards [hsmall] with m hm
    apply Lp.ext
    filter_upwards [hT (piL2BumpAverage (d+1) (φ m) u),
      piL2BumpAverage_convolution_ae (d+1) (φ m) f hf hc,
      weightedPiBumpAverage_coeFn n V hV (φ m) f hf hc] with x ht ha hw'
    rw [ht, ha, hw']
    rw [piPlane_convolution_swap (d+1)]
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
      exact mul_comm _ _
    · have hz := piCompactConvolution_eq_zero_of_not_mem (d+1) f (φ m) 1 hm x hx
      simp only [Set.indicator_of_notMem hx, hz, zero_mul, mul_zero]
  have ht := T.continuous.tendsto u |>.comp (piL2BumpAverage_tendsto (d+1) φ hφ u)
  rw [hTu] at ht
  exact ht.congr' he
end
end GinibrePoincare
