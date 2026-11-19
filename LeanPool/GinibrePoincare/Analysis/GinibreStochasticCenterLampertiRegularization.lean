/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterLampertiRegularization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLampertiGenerator
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Globally smooth center square-root tests, exactly equal to the original
square root above an explicit positive threshold. -/

@[expose] public section
open Set Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- The smooth regularization `√(c + δ * smoothTransition (2 - 2c / δ))` of the center modulus,
where `c = ginibreCenterSquared n z`; the correction vanishes once `c ≥ δ`. -/
def ginibreCenterSquareRootRegularized (n : ℕ) (δ : ℝ) (z : Configuration n) : ℝ :=
  Real.sqrt (ginibreCenterSquared n z +
    δ * Real.smoothTransition (2 - 2 * ginibreCenterSquared n z / δ))

theorem contDiff_ginibreCenterSquareRootRegularized (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (ginibreCenterSquareRootRegularized n δ) := by
  apply ContDiff.sqrt
  · exact (contDiff_ginibreCenterSquared n).add
      (contDiff_const.mul (Real.smoothTransition.contDiff.comp
        (contDiff_const.sub ((contDiff_const.mul (contDiff_ginibreCenterSquared n)).div_const δ))))
  · intro z
    have hr : 0 ≤ ginibreCenterSquared n z := Complex.normSq_nonneg _
    have hs := Real.smoothTransition.nonneg (2 - 2 * ginibreCenterSquared n z / δ)
    have hp : 0 < ginibreCenterSquared n z +
        δ * Real.smoothTransition (2 - 2 * ginibreCenterSquared n z / δ) := by
      by_cases hz : ginibreCenterSquared n z = 0
      · simp only [hz, mul_zero, zero_div, sub_zero, zero_add]
        rw [Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2)]
        simpa using hδ
      · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hr (Ne.symm hz)) (mul_nonneg hδ.le hs)
    exact hp.ne'

theorem ginibreCenterSquareRootRegularized_eq {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Configuration n) (hz : δ ≤ ginibreCenterSquared n z) :
    ginibreCenterSquareRootRegularized n δ z = ginibreSquareRootCenter n z := by
  have hh : 2 - 2 * ginibreCenterSquared n z / δ ≤ 0 := by
    have h := (le_div_iff₀ hδ).mpr (show 2 * δ ≤ 2 * ginibreCenterSquared n z by linarith)
    linarith
  simp [ginibreCenterSquareRootRegularized, ginibreSquareRootCenter,
    Real.smoothTransition.zero_of_nonpos hh]

theorem ginibreCenterSquareRootRegularized_eventuallyEq {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Configuration n) (hz : δ < ginibreCenterSquared n z) :
    ginibreCenterSquareRootRegularized n δ =ᶠ[𝓝 z] ginibreSquareRootCenter n := by
  filter_upwards [(contDiff_ginibreCenterSquared n).continuous.continuousAt.eventually
    (eventually_gt_nhds hz)] with w hw
  exact ginibreCenterSquareRootRegularized_eq hδ w hw.le

theorem ginibrePregenerator_congr_of_eventuallyEq {n : ℕ}
    (f g : Configuration n → ℝ) (z : Configuration n)
    (h : f =ᶠ[𝓝 z] g) : ginibrePregenerator n f z = ginibrePregenerator n g z := by
  have hd := h.fderiv_eq (𝕜 := ℝ)
  have hdd (v : Configuration n) : secondDirectionalDerivative f v z =
      secondDirectionalDerivative g v z := by
    unfold secondDirectionalDerivative
    have he : (fun x => fderiv ℝ f x v) =ᶠ[𝓝 z] (fun x => fderiv ℝ g x v) := by
      filter_upwards [h.fderiv (𝕜 := ℝ)] with x hx
      rw [hx]
    rw [he.fderiv_eq]
  simp only [ginibrePregenerator, configurationLaplacian, hd, hdd]

theorem ginibreCenterSquareRootRegularized_generator {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) {δ : ℝ} (hδ : 0 < δ) (z : Configuration n)
    (hz : CollisionFree z) (hr : δ < ginibreCenterSquared n z) :
    ginibreRealPaperSpeedGenerator n α (ginibreCenterSquareRootRegularized n δ) z =
      ginibreLampertiCenterDrift n α (ginibreCenterSquared n z) := by
  unfold ginibreRealPaperSpeedGenerator
  rw [ginibrePregenerator_congr_of_eventuallyEq _ _ z
    (ginibreCenterSquareRootRegularized_eventuallyEq hδ z hr)]
  exact ginibreRealPaperSpeedGenerator_squareRootCenter hn α z hz (hδ.trans hr)

end
end GinibrePoincare
