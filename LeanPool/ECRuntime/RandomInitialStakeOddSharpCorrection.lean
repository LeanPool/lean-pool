/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.RandomInitialStakeEvenSharpCorrection
public import LeanPool.ECRuntime.RandomInitialStakeOddScaledTailBridge

/-!
The odd-dimensional harmonic correction centered at the lower-half
harmonic number. The finite parity bridge transfers the even `-1/2` limit
to this convention's `+1/2` limit.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open Filter

namespace ECRuntime

/-- Exact decomposition of the scaled odd discrepancy into the even scaled
    discrepancy, the unscaled even discrepancy, and one. This bridge is a
    finite algebraic identity; it is not itself the missing limit theorem. -/
theorem stage186_oddScaledTail_evenScaledDecomposition (m : Nat) :
    (((2 * m + 1 : Nat) : Real) *
       (harmonicReal (2 * m + 1) - harmonicReal m - Real.log 2)) =
    (((2 * m : Nat) : Real) *
       (harmonicReal (2 * m) - harmonicReal m - Real.log 2)) +
       (harmonicReal (2 * m) - harmonicReal m - Real.log 2) + 1 := by
  rw [proposed_randomInitialStake_oddScaledTail_evenBridge]
  push_cast
  ring

/-- Proposed sharp odd-parity counterpart to the open Stage 176 limit. -/
theorem proposed_randomInitialStake_oddSharpHalfHarmonicCorrection :
    Tendsto
      (fun m : Nat =>
        (((2 * m + 1 : Nat) : Real) *
          (harmonicReal (2 * m + 1) - harmonicReal m - Real.log 2)))
      atTop (nhds (1 / 2 : Real)) := by
  let D : Nat → Real := fun m =>
    harmonicReal (2 * m) - harmonicReal m - Real.log 2
  have hEven : Tendsto
      (fun m : Nat => ((2 * m : Nat) : Real) * D m)
      atTop (nhds (-(1 / 2 : Real))) := by
    simpa only [D] using
      proposed_randomInitialStake_evenSharpHalfHarmonicCorrection
  have hden : Tendsto (fun m : Nat => ((2 * m : Nat) : Real))
      atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall (fun m : Nat => by
        exact_mod_cast (by omega : m ≤ 2 * m)))
      tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun m : Nat => ((2 * m : Nat) : Real)⁻¹)
      atTop (nhds (0 : Real)) :=
    tendsto_inv_atTop_zero.comp hden
  have hprod : Tendsto
      (fun m : Nat =>
        (((2 * m : Nat) : Real) * D m) * ((2 * m : Nat) : Real)⁻¹)
      atTop (nhds (0 : Real)) := by
    simpa only [mul_zero] using hEven.mul hinv
  have hD : Tendsto D atTop (nhds (0 : Real)) := by
    apply hprod.congr'
    filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with m hm
    have hmne : ((2 * m : Nat) : Real) ≠ 0 := by
      have h : (2 * m : Nat) ≠ 0 := by omega
      exact_mod_cast h
    calc
      (((2 * m : Nat) : Real) * D m) * ((2 * m : Nat) : Real)⁻¹ =
          D m * (((2 * m : Nat) : Real) * ((2 * m : Nat) : Real)⁻¹) := by ring
      _ = D m := by rw [mul_inv_cancel₀ hmne, mul_one]
  have hsum : Tendsto
      (fun m : Nat =>
        (((2 * m : Nat) : Real) * D m) + D m + 1)
      atTop (nhds (1 / 2 : Real)) := by
    convert (hEven.add hD).add tendsto_const_nhds using 1; norm_num
  apply hsum.congr'
  filter_upwards [] with m
  simpa only [D] using
    (stage186_oddScaledTail_evenScaledDecomposition m).symm

end ECRuntime
