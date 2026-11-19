/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiConvolutionSupport.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiBumpConvolution
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticLpMultiplier

/-!
# Non quadratic pi convolution support

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `piPlane_convolution_swap`, `piCompactConvolution_eq_zero_of_not_mem`,
`exists_compactPiL2WeightMultiplier`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology Pointwise ENNReal
namespace GinibrePoincare
noncomputable section

theorem piPlane_convolution_swap (d : ℕ) (k f : Configuration d → ℂ) (x : Configuration d) :
    (∫ a, k a * f (x-a)) = ∫ a, f a * k (x-a) := by
  rw [← integral_sub_left_eq_self (fun a => k a * f (x-a))
    (volume : Measure (Configuration d)) x]
  apply integral_congr_ae
  exact Eventually.of_forall (fun a => by simp only [sub_sub_cancel]; exact mul_comm _ _)
theorem piCompactConvolution_eq_zero_of_not_mem (d : ℕ)
    (f : Configuration d → ℂ) (φ : ContDiffBump (0 : ℂ)) (R : ℝ)
    (hR : φ.rOut ≤ R) (x : Configuration d)
    (hx : x ∉ tsupport f + Metric.closedBall (0 : Configuration d) R) :
    (∫ a, f a * (piPlanarBump d φ (x-a) : ℂ)
      ∂(volume : Measure (Configuration d))) = 0 := by
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro a
  by_cases ha : f a = 0
  · simp only [ha, zero_mul, Pi.zero_apply]
  by_cases hk : piPlanarBump d φ (x-a) = 0
  · simp only [hk, Complex.ofReal_zero, mul_zero, Pi.zero_apply]
  exfalso
  apply hx
  exact ⟨a, subset_closure ha, x-a,
    ((piPlanarBump_support_ball d φ (x-a) hk).le.trans hR), by abel_nf⟩

/-- Every continuous weight has a genuine bounded multiplication operator
on a fixed compact region of the whole product-plane L² space. -/
theorem exists_compactPiL2WeightMultiplier (d : ℕ)
    (w : Configuration d → ℂ) (hw : Continuous w) (S : Set (Configuration d)) (hS : IsCompact S) :
    ∃ T : Lp ℂ 2 (volume : Measure (Configuration d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Configuration d)),
      ∀ u, (T u : Configuration d → ℂ) =ᵐ[(volume : Measure (Configuration d))]
        (fun x => (S.indicator w) x * u x) := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hw.continuousOn
  let b := S.indicator w
  have hb : AEStronglyMeasurable b (volume : Measure (Configuration d)) :=
    hw.aestronglyMeasurable.indicator hS.measurableSet
  have hbn (x : Configuration d) : ‖b x‖ ≤ max C 0 := by
    by_cases hx : x ∈ S
    · simpa only [b, Set.indicator_of_mem hx] using (hC x hx).trans (le_max_left _ _)
    · simpa only [b, Set.indicator_of_notMem hx, norm_zero] using (le_max_right C 0)
  exact ⟨boundedComplexL2Multiplier b hb (max C 0) hbn,
    boundedComplexL2Multiplier_coeFn b hb (max C 0) hbn⟩
end
end GinibrePoincare
