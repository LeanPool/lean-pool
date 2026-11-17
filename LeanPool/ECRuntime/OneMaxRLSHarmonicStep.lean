/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RLSOneBitExpectationSupport

/-!
The exact one-step harmonic identity for one-bit OneMax RLS.
It supplies the Bellman certificate for the coupon-collector expectation.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/-- The scaled harmonic potential decreases by one in conditional
expectation at every nonoptimal OneMax state under one-bit RLS. At the
optimum it is zero. This is the missing local certificate for Stage 109. -/
theorem proposed_oneMaxRLS_harmonic_one_step
    {n : Nat} (hn : 0 < n) (x : BitString n) :
    expectedValueAfter
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      (fun y : BitString n =>
        (n : Real) * harmonicReal (zeroCount y)) x =
      if zeroCount x = 0 then 0
      else (n : Real) * harmonicReal (zeroCount x) - 1 := by
  exact candidate_rlsOneMax_harmonic_one_step hn x

end ECRuntime
