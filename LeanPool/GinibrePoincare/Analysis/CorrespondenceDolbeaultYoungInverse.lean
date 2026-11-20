/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoungInverse.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungInverseFubini

/-!
# Correspondence Dolbeault Young inverse

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultCauchyGreenL2_weak_inverse`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem dolbeaultSlice_truncated_fundamental {n : ℕ} (j : Fin n)
    (M T R : ℝ) (hR : M + T ≤ R) (w : Configuration n) (hw : ‖w‖ ≤ M)
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ)
    (hT : ∀ z ∈ tsupport θ, ‖z‖ ≤ T) :
    (∫ y : ℂ, dolbeaultTruncatedCauchyGreen R y*dbarComponent θ j (w+Pi.single j y)) = -θ w := by
  rw [← dolbeaultSlice_fundamental j w θ hθ hc]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    by_cases hy : y∈Metric.closedBall (0 : ℂ) R
    · simp only [dolbeaultTruncatedCauchyGreen, Set.indicator_of_mem hy]
    · have hout : w+Pi.single j y ∉ tsupport θ := by
        intro hz
        have he : y = (w+Pi.single j y : Configuration n) j-w j := by simp
        have hl : ‖y‖ ≤ ‖w+Pi.single j y‖+‖w‖ := by
          calc
            _ = ‖(w+Pi.single j y : Configuration n) j-w j‖ := congrArg norm he
            _ ≤ ‖(w+Pi.single j y : Configuration n) j‖+‖w j‖ := norm_sub_le _ _
            _ ≤ _ := add_le_add (norm_le_pi_norm _ j) (norm_le_pi_norm _ j)
        apply hy
        simp only [Metric.mem_closedBall, dist_zero_right]
        have ht := hT _ hz
        linarith
      have hd : dbarComponent θ j (w+Pi.single j y)=0 := by
        unfold dbarComponent
        rw [fderiv_of_notMem_tsupport ℝ hout]
        simp
      simp only [dolbeaultTruncatedCauchyGreen, Set.indicator_of_notMem hy, hd, mul_zero])

/-- Actual ordinary distributional coordinate right-inverse for arbitrary compact
L² input, obtained from the locally L¹ singular kernel, not from a Gaussian input. -/
theorem dolbeaultCauchyGreenL2_weak_inverse {n : ℕ} (j : Fin n)
    (M T R : ℝ) (hR : M + T ≤ R) (u : dolbeaultOrdinaryL2 n)
    (hu : ∀ᵐ z : Configuration n ∂volume, z ∉ Metric.closedBall 0 M → u z = 0)
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hT : ∀ z ∈ tsupport θ, ‖z‖ ≤ T) :
    (∫ z : Configuration n, dbarComponent θ j z*(dolbeaultCauchyGreenL2 j R u) z) =
      -(∫ z : Configuration n, θ z*u z) := by
  have hd : Continuous (dbarComponent θ j) :=
    continuous_const.mul
      (((hθ.continuous_fderiv (by simp)).clm_apply continuous_const).add
        (continuous_const.mul ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)))
  have hdc : HasCompactSupport (dbarComponent θ j) := by
    exact ((hc.fderiv_apply ℝ (realCoordinateDirection j)).add
      ((hc.fderiv_apply ℝ (imaginaryCoordinateDirection j)).mul_left (f := fun _ =>
          Complex.I))).mul_left
        (f := fun _ => (1/2 : ℂ))
  change (∫ z : Configuration n, dbarComponent θ j z*
    (dolbeaultCoordinateConvolution j (dolbeaultTruncatedCauchyGreen R) u) z) = _
  rw [dolbeaultCoordinateConvolution_test_fubini j _ (dolbeaultTruncatedCauchyGreen_integrable R)
    u (dolbeaultOrdinaryL2_integrable_compact u M hu) _ hd hdc,← integral_neg]
  apply integral_congr_ae
  filter_upwards [hu] with w hw
  by_cases hm : w∈Metric.closedBall (0 : Configuration n) M
  · have hb : ‖w‖≤M := by simpa only [Metric.mem_closedBall, dist_zero_right] using hm
    rw [dolbeaultSlice_truncated_fundamental j M T R hR w hb θ (hθ.of_le (by simp)) hc hT]
    ring
  · rw [hw hm]
    simp

end
end GinibrePoincare
