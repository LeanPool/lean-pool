/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.DoerrDoerrMonotoneUniformMean
public import LeanPool.ECRuntime.RLSCouponProcessKernelCorrespondence

/-!
P02 / 2013 preprint: an exact finite-dimensional coupon-process
counterpart, without any asymptotic or uniform integrability arguments.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal
namespace ECRuntime

/-- The direct coupon process, from independently uniform initial coupons,
has the same exact mean as uniformly initialized one-bit RLS on OneMax. -/
theorem proposed_couponUniformRuntime_eq_strictMonotoneRLSUniformInitialMean
    {n : Nat} (hn : 0 < n) :
    (Finset.univ.sum (fun x : BitString n =>
      (runtimeSup (randomStakeCouponTransition hn)
        ({allOnes n} : Set (BitString n)) x).toReal)) / (2 : Real) ^ n =
      strictMonotoneRLSUniformInitialMean hn (oneMaxReal (n := n)) := by
  rfl

end ECRuntime
