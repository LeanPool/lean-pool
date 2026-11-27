/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# A horizon from bounded integer advice

The stage construction has two rational finite-horizon quantities: the mass
of partial remaining ranks, and the mass of first drops already seen. Their
limits need not be computable. Only one bounded integer locating the second
limit is supplied as advice; the horizon itself is found by a finite rational
test. The companion file `StageHorizonComputable` implements that search.

The subtraction in the test is rational subtraction. In particular, advice
zero gives the negative threshold `-error`, which is necessary when the total
mass of first drops is zero.
-/

@[expose] public section

namespace Klr.StageHorizon

open Filter
open scoped Topology

/-- The two strict rational inequalities checked at a proposed horizon. -/
def Accepted (error : ℚ) (u v : ℕ → ℚ) (advice horizon : ℕ) : Prop :=
  u horizon < 3 * error ∧ ((advice : ℚ) - 1) * error < v horizon

/-- The stage-dependent bound for the integer advice. It is independent of
the trial rank, candidate support, and horizon. -/
def adviceBound (error : ℚ) (protectedCount : ℕ) : ℕ :=
  ⌊(protectedCount : ℚ) / error⌋₊

/-- The integer advice places the limiting first-drop mass in an interval
of width `error`. This assertion makes no computability claim about the limit. -/
def Quantized (error : ℚ) (limit : ℝ) (advice : ℕ) : Prop :=
  (advice : ℝ) * (error : ℝ) ≤ limit ∧
    limit < ((advice : ℝ) + 1) * (error : ℝ)

theorem zero_advice_threshold (error : ℚ) :
    (((0 : ℕ) : ℚ) - 1) * error = -error := by
  simp

/-- The usual floor choice gives advice bounded entirely by the stage data. -/
theorem exists_bounded_quantized {error : ℚ} (herror : 0 < error)
    {limit : ℝ} (hlimit : 0 ≤ limit) {protectedCount : ℕ}
    (hbound : limit ≤ protectedCount) :
    ∃ advice, advice ≤ adviceBound error protectedCount ∧
      Quantized error limit advice := by
  have he : (0 : ℝ) < error := by exact_mod_cast herror
  let advice : ℕ := ⌊limit / (error : ℝ)⌋₊
  have hlo : (advice : ℝ) * (error : ℝ) ≤ limit :=
    (le_div_iff₀ he).mp (Nat.floor_le (div_nonneg hlimit he.le))
  have hhi : limit < ((advice : ℝ) + 1) * (error : ℝ) :=
    (div_lt_iff₀ he).mp (Nat.lt_floor_add_one (limit / (error : ℝ)))
  refine ⟨advice, ?_, hlo, hhi⟩
  apply Nat.le_floor
  apply (le_div_iff₀ herror).mpr
  exact_mod_cast hlo.trans hbound

/-- The lower endpoint of the advice interval is strictly above the rational
search threshold, including when the advice is zero. -/
theorem threshold_lt_limit {error : ℚ} (herror : 0 < error)
    {limit : ℝ} {advice : ℕ} (hquantized : Quantized error limit advice) :
    ((((advice : ℚ) - 1) * error : ℚ) : ℝ) < limit := by
  have he : (0 : ℝ) < error := by exact_mod_cast herror
  push_cast
  have hlo := hquantized.1
  nlinarith

/-- Every accepted horizon has first-drop tail mass below twice the error.
This uses only the upper endpoint of the advice interval, not a modulus of
convergence for the first-drop probabilities. -/
theorem tail_lt_of_accepted {error : ℚ} {limit : ℝ} {advice horizon : ℕ}
    {u v : ℕ → ℚ} (hquantized : Quantized error limit advice)
    (haccepted : Accepted error u v advice horizon) :
    limit - (v horizon : ℝ) < 2 * (error : ℝ) := by
  have hv : ((advice : ℝ) - 1) * (error : ℝ) < (v horizon : ℝ) := by
    exact_mod_cast haccepted.2
  have hhi := hquantized.2
  nlinarith

/-- Convergence supplies accepted horizons eventually once both limiting
values lie strictly inside the acceptance inequalities. -/
theorem eventually_accepted_of_tendsto {error : ℚ} {u v : ℕ → ℚ}
    {uLimit vLimit : ℝ} {advice : ℕ}
    (hu : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 uLimit))
    (hv : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 vLimit))
    (huLimit : uLimit < 3 * (error : ℝ))
    (hvLimit : ((((advice : ℚ) - 1) * error : ℚ) : ℝ) < vLimit) :
    ∀ᶠ horizon in atTop, Accepted error u v advice horizon := by
  have hu' := (tendsto_order.mp hu).2 _ huLimit
  have hv' := (tendsto_order.mp hv).1 _ hvLimit
  filter_upwards [hu', hv'] with horizon huH hvH
  exact ⟨by exact_mod_cast huH, by exact_mod_cast hvH⟩

/-- Quantized advice and the partial-rank limit bound imply eventual
acceptance. A non-strict `2 * error` bound is sufficient. -/
theorem eventually_accepted_of_quantized {error : ℚ} (herror : 0 < error)
    {u v : ℕ → ℚ} {uLimit vLimit : ℝ} {advice : ℕ}
    (hu : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 uLimit))
    (hv : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 vLimit))
    (huLimit : uLimit ≤ 2 * (error : ℝ))
    (hquantized : Quantized error vLimit advice) :
    ∀ᶠ horizon in atTop, Accepted error u v advice horizon := by
  have he : (0 : ℝ) < error := by exact_mod_cast herror
  exact eventually_accepted_of_tendsto hu hv (by linarith)
    (threshold_lt_limit herror hquantized)

/-- A bounded choice of advice admits a finite rational search and certifies
the tail bound at every horizon accepted by that search. -/
theorem exists_bounded_advice {error : ℚ} (herror : 0 < error)
    {u v : ℕ → ℚ} {uLimit vLimit : ℝ} {protectedCount : ℕ}
    (hu : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 uLimit))
    (hv : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 vLimit))
    (huLimit : uLimit ≤ 2 * (error : ℝ)) (hvLimit : 0 ≤ vLimit)
    (hbound : vLimit ≤ protectedCount) :
    ∃ advice, advice ≤ adviceBound error protectedCount ∧
      Quantized error vLimit advice ∧
      (∀ᶠ horizon in atTop, Accepted error u v advice horizon) ∧
      ∀ horizon, Accepted error u v advice horizon →
        vLimit - (v horizon : ℝ) < 2 * (error : ℝ) := by
  obtain ⟨advice, hadvice, hquantized⟩ :=
    exists_bounded_quantized herror hvLimit hbound
  exact ⟨advice, hadvice, hquantized,
    eventually_accepted_of_quantized herror hu hv huLimit hquantized,
    fun _ hh => tail_lt_of_accepted hquantized hh⟩

end Klr.StageHorizon
