/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.BinomialHarmonicAverageClosedForm
public import LeanPool.ECRuntime.RLSUniformInitialExact

/-!
An exact finite-dimensional runtime correction for uniformly initialized
one-bit RLS, obtained from the binomial-harmonic transform. Initial fitness
evaluation is excluded from the iteration count.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Exact expected mutation iterations under uniform initialization,
for any positive linear objective, with the finite binomial correction. -/
theorem proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n)) x).toReal)) /
      (2 : Real) ^ n =
    (n : Real) *
      (harmonicReal n -
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) := by
  -- Stage 138 passed the official Round 28 promotion gate.
  have hclosed := proposed_binomialHarmonicAverage_closedForm n
  have hstage134 := proposed_rlsLinear_uniformInitial_runtimeAverage hn w hw
  rw [hstage134]
  rw [← hclosed]
  ring

end ECRuntime
