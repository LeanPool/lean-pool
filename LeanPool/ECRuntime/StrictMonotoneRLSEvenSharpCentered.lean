/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.DoerrDoerrMonotoneUniformMean
public import LeanPool.ECRuntime.RLSUniformStartEvenSharpCentered

/-!
The sharp even-dimensional uniform-start RLS mean for arbitrary
families of strictly coordinate-monotone fitness functions, transferred
from the common one-bit transition kernel.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open Filter
open scoped BigOperators

namespace ECRuntime

/-- The sharp additive correction for uniform-start one-bit RLS is independent
of the particular strictly coordinate-monotone objective at every dimension. -/
theorem proposed_strictMonotoneRLS_uniformInitial_evenSharpCentered
    (fitness : (n : Nat) → BitString n → Real)
    (hf : ∀ n : Nat, CandidateCoordinateStrictMonotonicity (fitness n)) :
    Tendsto
      (fun m : Nat =>
        if hn : 0 < 2 * m then
          strictMonotoneRLSUniformInitialMean hn (fitness (2 * m)) -
            (((2 * m : Nat) : Real) * harmonicReal m)
        else 0)
      atTop (nhds (-(1 / 2 : Real))) := by
  apply proposed_rlsLinear_uniformInitial_evenSharpCentered.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with m hm
  have hn : 0 < 2 * m := by omega
  have hw : PositiveLinearWeights
      (fun _ : Fin (2 * m) => (1 : Real)) := by
    intro i
    norm_num
  have hmon :=
    proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection
      hn (fitness (2 * m)) (hf (2 * m))
  have hlinear :=
    proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection
      hn (fun _ : Fin (2 * m) => (1 : Real)) hw
  have heq := hmon.trans hlinear.symm
  simpa only [dite_eq_left hn] using
    congrArg (fun z : Real =>
      z - (((2 * m : Nat) : Real) * harmonicReal m)) heq.symm

end ECRuntime
