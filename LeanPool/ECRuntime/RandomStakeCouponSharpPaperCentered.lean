/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RLSAllDimensionPaperSharpCentered
public import LeanPool.ECRuntime.RLSCouponExactUniformMean

/-!
The sharp full-sequence mean for coupon collection from a uniform initial set.
The coupon process uses the OneMax one-bit kernel: sampling an absent coupon
adds it, while sampling a present coupon leaves the collected set unchanged.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open Filter
open scoped BigOperators
namespace ECRuntime

/-- The uniform-start coupon process has the paper's half-harmonic
second-order correction `-1/2` along all positive dimensions. -/
theorem proposed_randomStakeCoupon_allDimensionPaperSharpCentered :
    Tendsto
      (fun n : Nat =>
        if hn : 0 < n then
          ((Finset.univ.sum (fun x : BitString n =>
            (runtimeSup (randomStakeCouponTransition hn)
              ({allOnes n} : Set (BitString n)) x).toReal)) /
            (2 : Real) ^ n) -
            (n : Real) *
              ((harmonicReal (n / 2) + harmonicReal ((n + 1) / 2)) / 2)
        else 0)
      atTop (nhds (-(1 / 2 : Real))) := by
  have hf := oneMaxReal_coordinateStrictMonotonicity
  apply (proposed_strictMonotoneRLS_allDimensionPaperSharpCentered
    (fun n => oneMaxReal (n := n)) hf).congr'
  filter_upwards [] with n
  by_cases hn : 0 < n
  · simp only [dite_eq_left hn]
    rw [proposed_couponUniformRuntime_eq_strictMonotoneRLSUniformInitialMean hn]
  · simp only [dite_eq_right hn]

end ECRuntime
