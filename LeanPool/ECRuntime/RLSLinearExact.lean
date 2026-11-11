/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.OneMaxRLSExact
public import LeanPool.ECRuntime.RLSOneBitSupport

/-!
Exact coupon-collector expectations for one-bit RLS on positive linear
objectives. Singleton acceptance depends only on the sign of its coordinate
weight, so no sorting or reordering assumption on the weights is required.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ECRuntime

/-- Bellman equality of the proposed coupon-collector runtime certificate.
This has equality (not only super-solution inequality). -/
theorem rlsLinear_harmonic_bellman
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w)
    (x : BitString n) :
    (if x = allOnes n then (0 : Real)
      else 1 + expectedValueAfter
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
          (linearFitness w))
        (fun y : BitString n =>
          (n : Real) * harmonicReal (zeroCount y)) x) =
      (n : Real) * harmonicReal (zeroCount x) := by
  rw [candidate_rls_linear_transition_eq_oneMax hn w hw,
    candidate_rlsOneMax_harmonic_one_step hn x]
  by_cases hx : x = allOnes n
  · simp [hx]
  · have hz : zeroCount x ≠ 0 := by
      intro hzero
      exact hx ((zeroCount_eq_zero_iff_allOnes x).mp hzero)
    simp [hx, hz]

/-- Exact unrestricted expected number of RLS iterations to the optimum. -/
theorem rlsLinear_runtimeSup_eq_harmonic
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w)
    (x : BitString n) :
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w))
      ({allOnes n} : Set (BitString n)) x =
      ENNReal.ofReal ((n : Real) * harmonicReal (zeroCount x)) := by
  rw [candidate_rls_linear_transition_eq_oneMax hn w hw]
  exact oneMaxRLS_runtimeSup_eq_harmonic hn x

end ECRuntime
