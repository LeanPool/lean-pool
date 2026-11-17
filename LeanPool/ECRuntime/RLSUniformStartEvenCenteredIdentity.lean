/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RLSUniformInitialRuntimeFiniteCorrection

/-!
Even-dimensional RLS mean as the half-dimension harmonic term plus
the dyadic harmonic correction and an exponentially small series remainder.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Exact even-dimensional runtime decomposition around the half-index harmonic
number. It isolates the sole remaining correction term needed for the
Doerr--Doerr sharp expected-runtime asymptotic. -/
theorem proposed_rlsLinear_uniformInitial_evenCentered_exact
    (m : Nat) (hn : 0 < 2 * m) (w : Fin (2 * m) → Real)
    (hw : PositiveLinearWeights w) :
    ((Finset.univ.sum (fun x : BitString (2 * m) =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes (2 * m)} : Set (BitString (2 * m))) x).toReal)) /
      (2 : Real) ^ (2 * m)) -
        (((2 * m : Nat) : Real) * harmonicReal m) =
      (((2 * m : Nat) : Real) *
        (harmonicReal (2 * m) - harmonicReal m - Real.log 2)) +
      (((2 * m : Nat) : Real) *
        (Real.log 2 -
          (Finset.Icc 1 (2 * m)).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j)))) := by
  have hmean := proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection hn w hw
  rw [hmean]
  ring

end ECRuntime
