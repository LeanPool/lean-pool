/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RLSCouponProcessKernelCorrespondence

/-!
P02: the direct coupon/RLS identity holds for arbitrary stopping
targets, including non-monotone subsets; this is kernel equality, not a
fitness-level ordering argument.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-- All extended expected hitting times agree pointwise for any target. -/
theorem proposed_couponProcess_arbitraryTarget_runtimeSup_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (x : BitString n) :
    runtimeSup (randomStakeCouponTransition hn) target x =
      runtimeSup
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        target x := by
  rw [proposed_couponProcess_transition_eq_strictMonotoneRLS hn fitness hf]

end ECRuntime
