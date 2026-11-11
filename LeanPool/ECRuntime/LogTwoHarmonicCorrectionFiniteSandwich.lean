/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RLSUniformInitialCorrectionCauchy
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Finite enclosures for the logarithmic half-series. Mathlib's logarithmic
Taylor-remainder estimate bounds `log 2` minus the first `n` terms of
`sum 1 / (j * 2^j)` and controls the coupon-collector correction.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open Filter
namespace ECRuntime

/-! The current Mathlib logarithmic Taylor remainder bound gives a much
shorter proof of Stage 154 than constructing interval integrals from scratch.
The following is only an index conversion between a range and an Icc sum;
it introduces no analytic hypothesis. -/
private theorem stage154_range_to_Icc (n : Nat) :
    (Finset.range n).sum (fun k =>
        (1 / 2 : Real) ^ (k + 1) / ((k : Real) + 1)) =
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hout : n + 1 ∉ Finset.Icc 1 n := by simp
      have hIcc : Finset.Icc 1 (n + 1) =
          insert (n + 1) (Finset.Icc 1 n) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [Finset.sum_range_succ, hIcc, Finset.sum_insert hout, ih]
      have hterm :
          (1 / 2 : Real) ^ (n + 1) / ((n : Real) + 1) =
            (1 : Real) / (((n + 1 : Nat) : Real) * (2 : Real) ^ (n + 1)) := by
        -- Force both presentations of the half-base into the same field
        -- expression before normalizing the remaining products.
        have hhalf : (1 / 2 : Real) = (2 : Real)⁻¹ := by norm_num
        rw [hhalf]
        push_cast
        simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, one_mul]
      rw [hterm]
      ring

private theorem stage154_log_half :
    Real.log (1 - (1 / 2 : Real)) = -Real.log 2 := by
  have h : (1 : Real) - 1 / 2 = (2 : Real)⁻¹ := by norm_num
  rw [h, Real.log_inv]

/-- Mathlib's proved finite Taylor-remainder estimate controls the
harmonic half-series uniformly by the geometric tail. -/
private theorem stage154_abs_log_error (n : Nat) :
    |(Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) - Real.log 2| ≤
          (1 : Real) / (2 : Real) ^ n := by
  have h := Real.abs_log_sub_add_sum_range_le
    (by norm_num : |(1 / 2 : Real)| < 1) n
  rw [stage154_range_to_Icc n, stage154_log_half] at h
  have hs : |(1 / 2 : Real)| = 1 / 2 := by norm_num
  rw [hs] at h
  have hnorm :
      |(Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) +
        -Real.log 2| =
      |(Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) - Real.log 2| := by
    simp only [sub_eq_add_neg]
  rw [hnorm] at h
  calc
    _ ≤ (1 / 2 : Real) ^ (n + 1) / (1 - (1 / 2 : Real)) := h
    _ = (1 / 2 : Real) ^ n := by rw [pow_succ]; ring
    _ = (1 : Real) / (2 : Real) ^ n := by
      simp only [one_div, inv_pow]

/-- The half-harmonic partial sums converge to log 2 by the proved
Mathlib logarithmic power series, not by a new axiom or an assumed limit. -/
private theorem stage154_log_series_tendsto :
    Tendsto (fun n : Nat => (Finset.Icc 1 n).sum (fun j =>
      (1 : Real) / ((j : Real) * (2 : Real) ^ j)))
      atTop (nhds (Real.log 2)) := by
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one
    (by norm_num : |(1 / 2 : Real)| < 1)).tendsto_sum_nat
  rw [stage154_log_half] at h
  simpa only [stage154_range_to_Icc, neg_neg] using h

/-- A finite enclosure for `log 2` by harmonic half-series partial sums.
It avoids assuming a power-series expansion as an axiom. -/
theorem proposed_logTwo_harmonicHalfSeries_finiteSandwich (n : Nat) :
    (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤ Real.log 2 ∧
      Real.log 2 ≤
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j)) +
          (1 : Real) / (2 : Real) ^ n := by
  have hlim := stage154_log_series_tendsto
  have hle :
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤ Real.log 2 := by
    have hev : ∀ᶠ m : Nat in atTop,
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤
        (Finset.Icc 1 m).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j)) := by
      filter_upwards [Filter.eventually_ge_atTop n] with m hnm
      exact sub_nonneg.mp
        (proposed_rlsUniformInitial_harmonicCorrection_cauchyModulus n m hnm).1
    exact ge_of_tendsto hlim hev
  have htail := stage154_abs_log_error n
  constructor
  · exact hle
  · have hlower := (abs_le.mp htail).1
    linarith

end ECRuntime
