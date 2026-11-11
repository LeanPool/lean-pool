/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RLSUniformStartOddCenteredIdentity
public import LeanPool.ECRuntime.RandomInitialStakeOddSharpCorrection
public import LeanPool.ECRuntime.RandomInitialStakeScaledBinomialCorrectionLimit

/-!
Sharp odd-dimensional expected RLS runtime centered at the lower-half
harmonic number. This convention gives the additive `+1/2` limit, before
conversion to the paper's adjacent-harmonic average.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open Filter
open scoped BigOperators

namespace ECRuntime

/-- The expected runtime centered at `(2m+1) * H_m` has limiting additive
constant `+1/2` for odd dimensions. -/
theorem proposed_rlsLinear_uniformInitial_oddSharpCentered :
    Tendsto
      (fun m : Nat =>
        ((Finset.univ.sum (fun x : BitString (2 * m + 1) =>
          (runtimeSup
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw
              (show 0 < 2 * m + 1 by omega)).transition
              (linearFitness (fun _ : Fin (2 * m + 1) => (1 : Real))))
            ({allOnes (2 * m + 1)} : Set (BitString (2 * m + 1))) x).toReal)) /
              (2 : Real) ^ (2 * m + 1)) -
          (((2 * m + 1 : Nat) : Real) * harmonicReal m))
      atTop (nhds (1 / 2 : Real)) := by
  have hDoublePlus : Tendsto (fun m : Nat => 2 * m + 1) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall
        (fun m : Nat => (show m <= 2 * m + 1 by omega)))
      tendsto_id
  have hsum : Tendsto
      (fun m : Nat =>
        (((2 * m + 1 : Nat) : Real) *
          (harmonicReal (2 * m + 1) - harmonicReal m - Real.log 2)) +
        (((2 * m + 1 : Nat) : Real) *
          (Real.log 2 - (Finset.Icc 1 (2 * m + 1)).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j)))))
      atTop (nhds (1 / 2 : Real)) := by
    simpa only [Function.comp_def, add_zero] using
      (proposed_randomInitialStake_oddSharpHalfHarmonicCorrection.add
        (proposed_randomInitialStake_scaledBinomialCorrection_tendsto_zero.comp
          hDoublePlus))
  apply hsum.congr'
  filter_upwards [] with m
  have hn : 0 < 2 * m + 1 := by omega
  have hw : PositiveLinearWeights (fun _ : Fin (2 * m + 1) => (1 : Real)) := by
    intro i
    norm_num
  simpa only using
    (proposed_rlsLinear_uniformInitial_oddCentered_exact m hn
      (fun _ : Fin (2 * m + 1) => (1 : Real)) hw).symm

end ECRuntime
