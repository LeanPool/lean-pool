/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.DoerrDoerrMonotoneUniformMean
public import LeanPool.ECRuntime.RLSUniformStartOddSharpCentered

/-!
The sharp odd-dimensional uniform-start RLS mean for arbitrary
families of strictly coordinate-monotone fitness functions, before
conversion from the lower-half harmonic center to the paper's center.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open Filter
open scoped BigOperators

namespace ECRuntime

/-- The odd-dimensional sharp `+1/2` additive correction holds for any
strictly coordinate-monotone family of objective functions. -/
theorem proposed_strictMonotoneRLS_uniformInitial_oddSharpCentered
    (fitness : (n : Nat) → BitString n → Real)
    (hf : ∀ n : Nat, CandidateCoordinateStrictMonotonicity (fitness n)) :
    Tendsto
      (fun m : Nat =>
        strictMonotoneRLSUniformInitialMean
            (show 0 < 2 * m + 1 by omega) (fitness (2 * m + 1)) -
          (((2 * m + 1 : Nat) : Real) * harmonicReal m))
      atTop (nhds (1 / 2 : Real)) := by
  apply proposed_rlsLinear_uniformInitial_oddSharpCentered.congr'
  filter_upwards [] with m
  have hn : 0 < 2 * m + 1 := by omega
  have hw : PositiveLinearWeights
      (fun _ : Fin (2 * m + 1) => (1 : Real)) := by
    intro i
    norm_num
  have hmon :=
    proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection
      hn (fitness (2 * m + 1)) (hf (2 * m + 1))
  have hlinear :=
    proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection
      hn (fun _ : Fin (2 * m + 1) => (1 : Real)) hw
  have heq := hmon.trans hlinear.symm
  simpa only using
    congrArg (fun z : Real =>
      z - (((2 * m + 1 : Nat) : Real) * harmonicReal m)) heq.symm

end ECRuntime
