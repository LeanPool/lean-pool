/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RLSUniformInitialRuntimeFiniteCorrection

/-!
Odd-dimensional RLS mean decomposed around the lower-half harmonic
number. The parity bridge identifies the extra reciprocal term; the
series remainder is kept explicit.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Exact odd-dimensional runtime decomposition relative to `H_m`.
Unlike the even version, its sharp harmonic correction tends to +1/2. -/
theorem proposed_rlsLinear_uniformInitial_oddCentered_exact
    (m : Nat) (hn : 0 < 2 * m + 1) (w : Fin (2 * m + 1) → Real)
    (hw : PositiveLinearWeights w) :
    ((Finset.univ.sum (fun x : BitString (2 * m + 1) =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes (2 * m + 1)} : Set (BitString (2 * m + 1))) x).toReal)) /
      (2 : Real) ^ (2 * m + 1)) -
        (((2 * m + 1 : Nat) : Real) * harmonicReal m) =
      (((2 * m + 1 : Nat) : Real) *
        (harmonicReal (2 * m + 1) - harmonicReal m - Real.log 2)) +
      (((2 * m + 1 : Nat) : Real) *
        (Real.log 2 -
          (Finset.Icc 1 (2 * m + 1)).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j)))) := by
  have hmean := proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection hn w hw
  rw [hmean]
  ring

end ECRuntime
