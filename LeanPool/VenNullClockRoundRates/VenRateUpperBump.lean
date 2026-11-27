/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.Linarith

/-!
# Normalized smooth bump functions with prescribed support
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace VenRateUpper

/-- Every nonempty open interval admits a nonnegative smooth bump of integral
one, with compact support inside the interval and a finite uniform bound. -/
theorem exists_normalized_interval_bump {l r : ℝ} (hlr : l < r) :
    ∃ (ψ : ℝ → ℝ) (B : ℝ), 0 < B ∧ ContDiff ℝ ∞ ψ ∧ (∫ t, ψ t) = 1 ∧
      HasCompactSupport ψ ∧ tsupport ψ ⊆ Set.Ioo l r ∧
      (∀ t, 0 ≤ ψ t) ∧ (∀ t, |ψ t| ≤ B) := by
  let center := (l + r) / 2
  let bump : ContDiffBump center :=
    { rIn := (r - l) / 8
      rOut := (r - l) / 4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hInt : 0 < ∫ t : ℝ, bump t := bump.integral_pos (μ := volume)
  refine ⟨bump.normed volume, 1 / (∫ t : ℝ, bump t), div_pos zero_lt_one hInt,
    bump.contDiff_normed (n := ⊤), bump.integral_normed, bump.hasCompactSupport_normed,
    ?_, bump.nonneg_normed, ?_⟩
  · rw [bump.tsupport_normed_eq]
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq] at ht
    change |t - center| ≤ (r - l) / 4 at ht
    have hdist := abs_le.mp ht
    dsimp [center] at hdist
    exact ⟨by linarith [hdist.1], by linarith [hdist.2]⟩
  · intro t
    rw [abs_of_nonneg (bump.nonneg_normed t), bump.normed_def]
    exact div_le_div_of_nonneg_right bump.le_one hInt.le

end VenRateUpper
