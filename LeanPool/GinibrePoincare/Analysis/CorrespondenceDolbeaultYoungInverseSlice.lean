/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoungInverseSlice.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungKernel
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenFundamental
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Correspondence Dolbeault Young inverse slice

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultSlice_fundamental`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem dolbeaultSlice_contDiff {n : ℕ} (j : Fin n) (w : Configuration n)
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ 1 θ) :
    ContDiff ℝ 1 (fun y : ℂ => θ (w+Pi.single j y)) := by
  exact hθ.comp (contDiff_const.add (contDiff_single (fun _ : Fin n => ℂ) 1 j))

theorem dolbeaultSlice_dbar {n : ℕ} (j : Fin n) (w : Configuration n)
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ 1 θ) (y : ℂ) :
    planarDbar (fun a : ℂ => θ (w+Pi.single j a)) y =
      dbarComponent θ j (w+Pi.single j y) := by
  have hs := (hasFDerivAt_single (𝕜 := ℝ) (i := j) y).const_add w
  have hd := ((hθ.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp y hs
  unfold planarDbar dbarComponent
  have he : (fun a : ℂ => θ (w+Pi.single j a)) = θ ∘ (fun a : ℂ => w+Pi.single j a) := rfl
  rw [he, hd.fderiv]
  have hl (v : ℂ) : (ContinuousLinearMap.pi (Pi.single j (ContinuousLinearMap.id ℝ ℂ))) v =
      coordinateDirection j v := by
    ext k
    by_cases hk : k=j
    · subst k
      simp [coordinateDirection]
    · simp [coordinateDirection, hk]
  simp only [ContinuousLinearMap.comp_apply, hl]
  rfl

theorem dolbeaultSlice_compact {n : ℕ} (j : Fin n) (w : Configuration n)
    (θ : Configuration n → ℂ) (hc : HasCompactSupport θ) :
    HasCompactSupport (fun y : ℂ => θ (w+Pi.single j y)) := by
  obtain ⟨M, hM⟩ := hc.isBounded.exists_norm_le
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (M+‖w‖))
  intro y hy
  by_contra hn
  have hb := hM (w+Pi.single j y) (subset_tsupport θ hn)
  have he : y = (w+Pi.single j y : Configuration n) j-w j := by simp
  have hl : ‖y‖ ≤ ‖w+Pi.single j y‖+‖w‖ := by
    calc
      _ = ‖(w+Pi.single j y : Configuration n) j-w j‖ := congrArg norm he
      _ ≤ ‖(w+Pi.single j y : Configuration n) j‖+‖w j‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (norm_le_pi_norm _ j) (norm_le_pi_norm _ j)
  apply hy
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact hl.trans (add_le_add hb le_rfl)

/-- Actual coordinate fundamental solution, with the other coordinates fixed. -/
theorem dolbeaultSlice_fundamental {n : ℕ} (j : Fin n) (w : Configuration n)
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ y : ℂ, cauchyGreenKernel y*dbarComponent θ j (w+Pi.single j y)) = -θ w := by
  let φ : ℂ → ℂ := fun y => θ (w+Pi.single j y)
  have hφ : ContDiff ℝ 1 φ := dolbeaultSlice_contDiff (n := n) j w θ hθ
  have hφc : HasCompactSupport φ := dolbeaultSlice_compact (n := n) j w θ hc
  have h := cauchyGreenKernel_fundamental_identity φ hφ hφc
  change (∫ y : ℂ, cauchyGreenKernel y * planarDbar φ y) = -φ 0 at h
  dsimp only [φ] at h
  simpa only [dolbeaultSlice_dbar j w θ hθ, Pi.single_zero, add_zero] using h

end
end GinibrePoincare
