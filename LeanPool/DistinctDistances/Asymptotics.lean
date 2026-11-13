/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Order.Filter.AtTopBot.Basic
public import LeanPool.DistinctDistances.Foundation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Asymptotics helpers for the Tier A bridge.

Filter-monotonicity lemmas used to lift "eventually beats every linear bound"
to `Tendsto (· / n) atTop atTop`.
-/

@[expose] public section

namespace Esgk

open Filter
open Topology

/-- Eventually `(n : ℝ) > 0` along `atTop`; trivial cast helper for division-by-`n` filter
manipulations. -/
theorem eventually_pos_nat_cast : ∀ᶠ n : ℕ in Filter.atTop, (0 : ℝ) < (n : ℝ) := by
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact_mod_cast hn


/-- If `f` eventually beats every linear function in `n`, then `f n / n → ∞`. -/
theorem tendsto_atTop_of_eventually_linear_lower_bound {f : ℕ → ℝ}
    (h : ∀ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop, A * (n : ℝ) ≤ f n) :
    Tendsto (fun n : ℕ ↦ f n / (n : ℝ)) Filter.atTop Filter.atTop := by
  rw [tendsto_atTop]
  intro M
  have hpos : ∀ᶠ n : ℕ in Filter.atTop, (0 : ℝ) < (n : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact_mod_cast hn
  filter_upwards [h M, hpos] with n hn hnpos
  rw [le_div_iff₀ hnpos]
  linarith


end Esgk
