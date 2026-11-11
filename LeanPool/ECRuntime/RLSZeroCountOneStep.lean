/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RLSOneBitExpectationSupport

/-!
The exact one-step drift of the zero count under one-bit RLS.
It is the eigenfunction identity used in the finite survival estimate.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/-- RLS on OneMax decreases the expected zero count by a fraction `1/n`
in every state, including the optimum. -/
theorem proposed_rlsOneMax_expectedZeroCount_oneStep
    {n : Nat} (hn : 0 < n) (x : BitString n) :
    expectedValueAfter
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      (fun y : BitString n => (zeroCount y : Real)) x =
        (1 - 1 / (n : Real)) * (zeroCount x : Real) := by
  exact candidate_rlsOneMax_expectedZeroCount_exact hn x

end ECRuntime
