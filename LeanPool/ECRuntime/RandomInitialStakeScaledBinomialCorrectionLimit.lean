/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.LogTwoHarmonicCorrectionFiniteSandwich

/-!
Geometric decay of the scaled logarithmic half-series remainder.
The finite enclosure reduces the bound to `n / 2^n`, which tends to zero.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open Filter
open scoped BigOperators

namespace ECRuntime

/-- Polynomial factors are dominated by geometric growth. -/
private theorem stage208_nat_div_pow_two_tendsto_zero :
    Tendsto (fun n : Nat => (n : Real) / (2 : Real) ^ n)
      atTop (nhds (0 : Real)) := by
  simpa only [pow_one] using
    tendsto_pow_const_div_const_pow_of_one_lt 1 (show (1 : Real) < 2 by norm_num)

/-- The scaled finite correction vanishes. No stronger assumption is used
than the already certified finite log-two series enclosure. -/
theorem proposed_randomInitialStake_scaledBinomialCorrection_tendsto_zero :
    Tendsto
      (fun n : Nat => (n : Real) *
        (Real.log 2 -
          (Finset.Icc 1 n).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j))))
      atTop (nhds (0 : Real)) := by
  have hbound (n : Nat) :
      0 <= (n : Real) *
        (Real.log 2 - (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) /\
      (n : Real) *
        (Real.log 2 - (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) <=
        (n : Real) / (2 : Real) ^ n := by
    have hfinite := proposed_logTwo_harmonicHalfSeries_finiteSandwich n
    have hnnonneg : (0 : Real) <= (n : Real) := Nat.cast_nonneg _
    constructor
    · exact mul_nonneg hnnonneg (sub_nonneg.mpr hfinite.1)
    · have hle : Real.log 2 -
          (Finset.Icc 1 n).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j)) <=
          (1 : Real) / (2 : Real) ^ n := by
        linarith [hfinite.2]
      calc
        _ <= (n : Real) * ((1 : Real) / (2 : Real) ^ n) :=
          mul_le_mul_of_nonneg_left hle hnnonneg
        _ = (n : Real) / (2 : Real) ^ n := by ring
  exact squeeze_zero (fun n => (hbound n).1) (fun n => (hbound n).2)
    stage208_nat_div_pow_two_tendsto_zero

end ECRuntime
