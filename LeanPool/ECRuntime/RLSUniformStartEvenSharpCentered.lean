/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RLSUniformStartEvenCenteredIdentity
public import LeanPool.ECRuntime.RandomInitialStakeEvenSharpCorrection
public import LeanPool.ECRuntime.RandomInitialStakeScaledBinomialCorrectionLimit

/-!
Sharp even-dimensional expected RLS runtime on the canonical positive
linear objective, combining the exact centered identity, the sharp dyadic
harmonic limit, and geometric decay of the series remainder.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open Filter
open scoped BigOperators

namespace ECRuntime

/-- The expected runtime for uniformly initialized one-bit RLS, centered
at `2m * H_m`, has the sharp additive constant `-1/2` for even dimensions. -/
theorem proposed_rlsLinear_uniformInitial_evenSharpCentered :
    Tendsto
      (fun m : Nat =>
        if hn : 0 < 2 * m then
          ((Finset.univ.sum (fun x : BitString (2 * m) =>
            (runtimeSup
              ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
                (linearFitness (fun _ : Fin (2 * m) => (1 : Real))))
              ({allOnes (2 * m)} : Set (BitString (2 * m))) x).toReal)) /
                (2 : Real) ^ (2 * m)) -
          (((2 * m : Nat) : Real) * harmonicReal m)
        else 0)
      atTop (nhds (-(1 / 2 : Real))) := by
  have hDouble : Tendsto (fun m : Nat => 2 * m) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall (fun m : Nat => (show m <= 2 * m by omega)))
      tendsto_id
  have hsum : Tendsto
      (fun m : Nat =>
        (((2 * m : Nat) : Real) *
          (harmonicReal (2 * m) - harmonicReal m - Real.log 2)) +
        (((2 * m : Nat) : Real) *
          (Real.log 2 - (Finset.Icc 1 (2 * m)).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j)))))
      atTop (nhds (-(1 / 2 : Real))) := by
    simpa only [Function.comp_def, add_zero] using
      (proposed_randomInitialStake_evenSharpHalfHarmonicCorrection.add
        (proposed_randomInitialStake_scaledBinomialCorrection_tendsto_zero.comp
          hDouble))
  apply hsum.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with m hm
  have hn : 0 < 2 * m := by omega
  have hw : PositiveLinearWeights (fun _ : Fin (2 * m) => (1 : Real)) := by
    intro i
    norm_num
  simpa only [dite_eq_left hn] using
    (proposed_rlsLinear_uniformInitial_evenCentered_exact m hn
      (fun _ : Fin (2 * m) => (1 : Real)) hw).symm

end ECRuntime
