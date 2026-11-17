/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.OneMaxRLSExact
public import LeanPool.ECRuntime.StrictMonotoneRLSKernelSupport

/-!
Exact one-bit RLS runtime for strictly coordinate-monotone Boolean
landscapes. The singleton kernel bridge reduces the Bellman certificate
and survival estimate to OneMax.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal
namespace ECRuntime

/-- Strict coordinatewise monotonicity identifies RLS with OneMax RLS. -/
theorem candidateStrictMonotoneRLS_transition_eq_oneMax
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness) :
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness =
      (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal := by
  exact support_strictMonotoneRLS_transition_eq_oneMax hn fitness hf

/-- Exact coupon-collector expectation for the broader monotone class. -/
theorem candidateStrictMonotoneRLS_runtimeSup_eq_harmonic
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (x : BitString n) :
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
      ({allOnes n} : Set (BitString n)) x =
      ENNReal.ofReal ((n : Real) * harmonicReal (zeroCount x)) := by
  rw [candidateStrictMonotoneRLS_transition_eq_oneMax hn fitness hf]
  exact oneMaxRLS_runtimeSup_eq_harmonic hn x

end ECRuntime
