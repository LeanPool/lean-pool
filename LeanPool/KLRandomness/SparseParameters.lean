/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Eventual numerical bounds for sparse candidate lists

The polynomial choices `M = r^8`, `m = r^2`, and `J = M^3` satisfy the
support, rank, and finite-list concentration estimates for every fixed
positive support density and error tolerance once `r` is sufficiently
large. The assertions here contain no probabilistic hypotheses.
-/

@[expose] public section

namespace Klr.SparseParameters

open Filter
open scoped Topology

/-- The block length. -/
def blockSize (r : ℕ) : ℕ := r ^ 8

/-- The number of columns in a support. -/
def supportSize (r : ℕ) : ℕ := r ^ 2

/-- The number of independent candidates in a list. -/
def listSize (r : ℕ) : ℕ := (blockSize r) ^ 3

theorem tendsto_nat_power (n : ℕ) (hn : n ≠ 0) :
    Tendsto (fun r : ℕ => ((r ^ n : ℕ) : ℝ)) atTop atTop := by
  simpa only [Function.comp_def, Nat.cast_pow] using
    (tendsto_pow_atTop (α := ℝ) hn).comp tendsto_natCast_atTop_atTop

theorem tendsto_blockSize : Tendsto (fun r => (blockSize r : ℝ)) atTop atTop :=
  tendsto_nat_power 8 (by decide)

theorem tendsto_supportSize : Tendsto (fun r => (supportSize r : ℝ)) atTop atTop :=
  tendsto_nat_power 2 (by decide)

/-- All elementary size hypotheses hold already from `r = 2` onward. -/
theorem basic_bounds {r : ℕ} (hr : 2 ≤ r) :
    2 ≤ supportSize r ∧ supportSize r ≤ blockSize r ∧ r + 1 ≤ supportSize r := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [supportSize]
    nlinarith
  · exact pow_le_pow_right' (by omega : 1 ≤ r) (by norm_num : 2 ≤ 8)
  · dsimp [supportSize]
    nlinarith

theorem eventually_basic_bounds :
    ∀ᶠ r : ℕ in atTop,
      2 ≤ supportSize r ∧ supportSize r ≤ blockSize r ∧ r + 1 ≤ supportSize r :=
  (eventually_ge_atTop 2).mono fun _ hr => basic_bounds hr

/-- The expected unread support size eventually dominates four times the
number of rows, for every fixed positive density. -/
theorem eventually_support_margin (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ r : ℕ in atTop, 4 * (r : ℝ) ≤ τ * (supportSize r : ℝ) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (4 / τ))
  filter_upwards [h] with r hr
  have hm := mul_le_mul_of_nonneg_right ((div_le_iff₀ hτ).mp hr) (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  simpa [supportSize, pow_two, mul_assoc, mul_comm, mul_left_comm] using hm

/-- The genuine one-candidate failure bound tends to zero. -/
theorem tendsto_single_failure (τ : ℝ) (hτ : 0 < τ) :
    Tendsto (fun r : ℕ =>
      4 / (τ * (supportSize r : ℝ)) + 2 * (1 / 2 : ℝ) ^ r) atTop (𝓝 0) := by
  have hden : Tendsto (fun r => τ * (supportSize r : ℝ)) atTop atTop :=
    tendsto_supportSize.const_mul_atTop hτ
  have hi := hden.inv_tendsto_atTop.const_mul (4 : ℝ)
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 : ℝ)
  simpa [div_eq_mul_inv] using hi.add hp

theorem eventually_single_failure_le (τ θ : ℝ) (hτ : 0 < τ) (hθ : 0 < θ) :
    ∀ᶠ r : ℕ in atTop,
      4 / (τ * (supportSize r : ℝ)) + 2 * (1 / 2 : ℝ) ^ r ≤ θ / 4 :=
  (tendsto_single_failure τ hτ).eventually_le_const (by positivity)

/-- Once both negative exponents dominate `-M`, the two union-bound terms
are bounded by the familiar exponential tail. -/
theorem union_bound_le_simple {M m θ : ℝ} (hM : 0 ≤ M)
    (hθ : 8 ≤ θ * M ^ 2) (hm : 6 ≤ m * M) :
    Real.exp (M - θ * M ^ 3 / 4) + M * Real.exp (-m * M ^ 2 / 6) ≤
      Real.exp (-M) + M * Real.exp (-M) := by
  have hθM := mul_le_mul_of_nonneg_right hθ hM
  have hmM := mul_le_mul_of_nonneg_right hm hM
  apply add_le_add
  · apply Real.exp_le_exp.mpr
    nlinarith
  · apply mul_le_mul_of_nonneg_left _ hM
    apply Real.exp_le_exp.mpr
    nlinarith

/-- The total finite-list failure bound tends to zero for the polynomial
parameter choices. This is the numerical final step of the probabilistic
existence argument. -/
theorem tendsto_list_failure (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun r : ℕ =>
      Real.exp ((blockSize r : ℝ) - θ * (listSize r : ℝ) / 4) +
        (blockSize r : ℝ) *
          Real.exp (-(supportSize r : ℝ) * (blockSize r : ℝ) ^ 2 / 6))
      atTop (𝓝 0) := by
  have hsimple : Tendsto (fun r : ℕ =>
      Real.exp (-(blockSize r : ℝ)) +
        (blockSize r : ℝ) * Real.exp (-(blockSize r : ℝ))) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_blockSize
    have hp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp tendsto_blockSize
    simpa using he.add hp
  have hθlim : Tendsto (fun r : ℕ => θ * (blockSize r : ℝ) ^ 2) atTop atTop :=
    ((tendsto_pow_atTop (α := ℝ) (by decide : 2 ≠ 0)).comp tendsto_blockSize).const_mul_atTop hθ
  have hmlim : Tendsto (fun r : ℕ => (supportSize r : ℝ) * (blockSize r : ℝ)) atTop atTop := by
    convert tendsto_nat_power 10 (by decide) using 1
    ext r
    simp only [supportSize, blockSize, Nat.cast_pow]
    ring
  apply squeeze_zero' (Eventually.of_forall fun r => by positivity) _ hsimple
  filter_upwards [hθlim.eventually (eventually_ge_atTop 8),
    hmlim.eventually (eventually_ge_atTop 6)] with r hθr hmr
  simpa [listSize] using union_bound_le_simple
    (Nat.cast_nonneg (blockSize r)) hθr hmr

theorem eventually_list_failure_lt_one (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ r : ℕ in atTop,
      Real.exp ((blockSize r : ℝ) - θ * (listSize r : ℝ) / 4) +
        (blockSize r : ℝ) *
          Real.exp (-(supportSize r : ℝ) * (blockSize r : ℝ) ^ 2 / 6) < 1 :=
  (tendsto_list_failure θ hθ).eventually_lt_const (by norm_num)

/-- Every numerical premise of the sparse finite-list construction holds
simultaneously for all sufficiently large row counts. -/
theorem eventually_candidate_parameters (τ θ : ℝ) (hτ : 0 < τ) (hθ : 0 < θ) :
    ∀ᶠ r : ℕ in atTop,
      2 ≤ supportSize r ∧
      supportSize r ≤ blockSize r ∧
      r + 1 ≤ supportSize r ∧
      4 * (r : ℝ) ≤ τ * (supportSize r : ℝ) ∧
      4 / (τ * (supportSize r : ℝ)) + 2 * (1 / 2 : ℝ) ^ r ≤ θ / 4 ∧
      Real.exp ((blockSize r : ℝ) - θ * (listSize r : ℝ) / 4) +
        (blockSize r : ℝ) *
          Real.exp (-(supportSize r : ℝ) * (blockSize r : ℝ) ^ 2 / 6) < 1 := by
  filter_upwards [eventually_basic_bounds, eventually_support_margin τ hτ,
    eventually_single_failure_le τ θ hτ hθ, eventually_list_failure_lt_one θ hθ]
    with r hr hmargin hsingle hlist
  exact ⟨hr.1, hr.2.1, hr.2.2, hmargin, hsingle, hlist⟩

end Klr.SparseParameters
