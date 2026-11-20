/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupOrderTest.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupChainRule
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # A concrete smooth test of negativity for the full Dirichlet resolvent -/

@[expose] public section
open Filter
open scoped NNReal ContDiff
namespace GinibrePoincare
noncomputable section

/-- Smooth nonnegative detection of the negative half-line. -/
def ginibreNegativeTest (x : ℝ) : ℝ := Real.smoothTransition (-x)

theorem ginibreNegativeTest_smooth : ContDiff ℝ ∞ ginibreNegativeTest :=
  Real.smoothTransition.contDiff.comp contDiff_id.neg

@[simp] theorem ginibreNegativeTest_zero : ginibreNegativeTest 0 = 0 := by
  simp [ginibreNegativeTest]

theorem ginibreNegativeTest_nonneg (x : ℝ) : 0 ≤ ginibreNegativeTest x :=
  Real.smoothTransition.nonneg (-x)

theorem ginibreNegativeTest_pos {x : ℝ} (hx : x < 0) : 0 < ginibreNegativeTest x :=
  Real.smoothTransition.pos_of_pos (neg_pos.mpr hx)

theorem ginibreNegativeTest_mul_nonpos (x : ℝ) : x * ginibreNegativeTest x ≤ 0 := by
  by_cases hx : x ≤ 0
  · exact mul_nonpos_of_nonpos_of_nonneg hx (ginibreNegativeTest_nonneg x)
  · have he : ginibreNegativeTest x = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [he, mul_zero]

theorem ginibreNegativeTest_antitone : Antitone ginibreNegativeTest :=
  Real.smoothTransition.monotone.comp_antitone (fun _ _ h => neg_le_neg h)

theorem ginibreNegativeTest_deriv_nonpos (x : ℝ) : deriv ginibreNegativeTest x ≤ 0 :=
  ginibreNegativeTest_antitone.deriv_nonpos

/-- The transition derivative vanishes outside its actual compact transition interval. -/
theorem smoothTransition_deriv_zero_outside {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition x = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have he : Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he |>.deriv
  · have he : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    exact (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq he |>.deriv

/-- A finite, explicitly justified Lipschitz constant for the negativity test. -/
theorem ginibreNegativeTest_lipschitz : ∃ K : ℝ≥0, LipschitzWith K ginibreNegativeTest := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hc.continuousOn
  have hb : ∀ x : ℝ, ‖deriv Real.smoothTransition x‖ ≤ max B 0 := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · exact (hB x hx).trans (le_max_left _ _)
    · rw [smoothTransition_deriv_zero_outside hx, norm_zero]
      exact le_max_right _ _
  have hl : LipschitzWith ⟨max B 0, le_max_right _ _⟩ Real.smoothTransition :=
    lipschitzWith_of_nnNorm_deriv_le
      ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable (by
          simp))
      (fun x => by exact_mod_cast hb x)
  refine ⟨⟨max B 0, le_max_right _ _⟩, ?_⟩
  have hcomp : LipschitzWith (⟨max B 0, le_max_right _ _⟩ * (1 : ℝ≥0)) ginibreNegativeTest :=
    hl.comp (LipschitzWith.id.neg : LipschitzWith 1 (fun x : ℝ => -x))
  have he : (⟨max B 0, le_max_right _ _⟩ * (1 : ℝ≥0)) =
      (⟨max B 0, le_max_right _ _⟩ : ℝ≥0) := by
    apply Subtype.ext
    change max B 0 * 1 = max B 0
    ring
  rw [he] at hcomp
  exact hcomp

end
end GinibrePoincare
