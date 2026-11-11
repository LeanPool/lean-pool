/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FitnessLevel
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
The upper-half harmonic sum tends to `log 2`. The Mathlib limit for
`harmonic n - log n` is applied along `2m` and `m`, cancelling the
Euler–Mascheroni constant.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open Filter

namespace ECRuntime

/-- The upper-half harmonic series tends to `log 2`. -/
theorem proposed_randomInitialStake_dyadicHarmonic_tendsto_logTwo :
    Tendsto (fun m : Nat => harmonicReal (2 * m) - harmonicReal m)
      atTop (nhds (Real.log 2)) := by
  have hbase : Tendsto
      (fun n : Nat => harmonicReal n - Real.log (n : Real))
      atTop (nhds Real.eulerMascheroniConstant) := by
    simpa only [harmonicReal] using Real.tendsto_harmonic_sub_log
  have hdoubling : Tendsto (fun m : Nat => 2 * m) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall (fun m : Nat => (show m ≤ 2 * m by omega)))
      tendsto_id
  have hdouble : Tendsto
      (fun m : Nat => harmonicReal (2 * m) - Real.log ((2 * m : Nat) : Real))
      atTop (nhds Real.eulerMascheroniConstant) := by
    simpa only [Function.comp_def] using hbase.comp hdoubling
  have hcancel : Tendsto
      (fun m : Nat =>
        (harmonicReal (2 * m) - Real.log ((2 * m : Nat) : Real)) -
        (harmonicReal m - Real.log (m : Real)))
      atTop (nhds (0 : Real)) := by
    convert hdouble.sub hbase using 1; norm_num
  have hsum : Tendsto
      (fun m : Nat =>
        ((harmonicReal (2 * m) - Real.log ((2 * m : Nat) : Real)) -
         (harmonicReal m - Real.log (m : Real))) + Real.log 2)
      atTop (nhds (Real.log 2)) := by
    simpa only [zero_add] using hcancel.add_const (Real.log 2)
  apply hsum.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with m hm
  have hm0 : (m : Real) ≠ 0 := by
    exact_mod_cast (by omega : m ≠ 0)
  have hlog : Real.log ((2 * m : Nat) : Real) =
      Real.log 2 + Real.log (m : Real) := by
    have hcast : ((2 * m : Nat) : Real) = 2 * (m : Real) := by
      push_cast
      ring
    rw [hcast, Real.log_mul (by norm_num : (2 : Real) ≠ 0) hm0]
  rw [hlog]
  ring

end ECRuntime
