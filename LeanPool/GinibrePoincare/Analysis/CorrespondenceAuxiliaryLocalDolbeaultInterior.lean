/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultInterior.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultMollification
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiBump

/-!
# Correspondence auxiliary local Dolbeault interior

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultBump_translated_tsupport_interior`, `localDolbeault_indicator_closed`.
-/

@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

theorem dbarComponent_zero_of_notMem_tsupport {n : ℕ}
    (θ : Configuration n → ℂ) (j : Fin n) (y : Configuration n)
    (hy : y ∉ tsupport θ) : dbarComponent θ j y = 0 := by
  simp [dbarComponent, fderiv_of_notMem_tsupport ℝ hy]

theorem dolbeaultBump_translated_tsupport {n : ℕ}
    (φ : ContDiffBump (0 : ℂ)) (p : Configuration n) :
    tsupport (fun y : Configuration n => Complex.ofReal (piPlanarBump n φ (p-y))) ⊆
      closedBall p φ.rOut := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  have hnon : piPlanarBump n φ (p-y) ≠ 0 := by
    intro hzero
    apply hy
    simp only [hzero, Complex.ofReal_zero]
  have h := piPlanarBump_support_ball n φ (p-y) hnon
  apply ball_subset_closedBall
  simpa only [mem_ball, dist_eq_norm, sub_zero, norm_sub_rev] using h

theorem dolbeaultBump_translated_tsupport_interior {n : ℕ}
    (φ : ContDiffBump (0 : ℂ)) (x p : Configuration n) (R : ℝ)
    (hR : φ.rOut + dist p x < R) :
    tsupport (fun y : Configuration n => Complex.ofReal (piPlanarBump n φ (p-y))) ⊆ ball x R :=
  (dolbeaultBump_translated_tsupport φ p).trans (closedBall_subset_ball' hR)

/-- Compact localization preserves the original ordinary distributional
closedness on the interior of the localization ball. -/
theorem localDolbeault_indicator_closed {n : ℕ}
    (Ω : Set (Configuration n)) (α : Fin n → Configuration n → ℂ)
    (hclosed : ∀ θ : Configuration n → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ Ω → ∀ j k,
        (∫ y, dbarComponent θ k y * α j y) = ∫ y, dbarComponent θ j y * α k y)
    (x : Configuration n) (R : ℝ) (hball : closedBall x R ⊆ Ω)
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ ∞ θ) (hcθ : HasCompactSupport θ)
    (hsθ : tsupport θ ⊆ ball x R) (j k : Fin n) :
    (∫ y, dbarComponent θ k y * (closedBall x R).indicator (α j) y) =
      ∫ y, dbarComponent θ j y * (closedBall x R).indicator (α k) y := by
  have he (s t : Fin n) (y : Configuration n) :
      dbarComponent θ s y * (closedBall x R).indicator (α t) y =
        dbarComponent θ s y * α t y := by
    by_cases hy : y ∈ closedBall x R
    · rw [indicator_of_mem hy]
    · have hys : y ∉ tsupport θ := fun h => hy (ball_subset_closedBall (hsθ h))
      rw [dbarComponent_zero_of_notMem_tsupport θ s y hys, zero_mul, zero_mul]
  simp_rw [he]
  exact hclosed θ hθ hcθ (hsθ.trans (ball_subset_closedBall.trans hball)) j k

end
end GinibrePoincare
