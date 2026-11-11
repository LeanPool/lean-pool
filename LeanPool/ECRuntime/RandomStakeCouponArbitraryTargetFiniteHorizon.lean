/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RLSCouponProcessKernelCorrespondence

/-!
P02: extend the coupon/RLS kernel equivalence to arbitrary finite
horizons and arbitrary targets, not just the optimum singleton.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/-- Every finite-time survival mass is invariant under replacing the
direct coupon process by RLS for a coordinatewise strictly monotone fitness. -/
theorem proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n))
    [DecidablePred (fun x : BitString n => x ∈ target)]
    (t : Nat) (x : BitString n) :
    finiteLevelSurvival
      (randomStakeCouponTransition hn) targetᶜ t x =
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        targetᶜ t x := by
  rw [proposed_couponProcess_transition_eq_strictMonotoneRLS hn fitness hf]

end ECRuntime
