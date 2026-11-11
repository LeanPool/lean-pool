/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.LinearPotential
public import LeanPool.ECRuntime.StrictMonotoneRLSKernelSupport

/-!
Positive linear weights give each singleton flip the same accept/reject
decision as OneMax. Consequently the one-bit transition matrices agree
without a coordinate-ordering hypothesis.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Positive linear fitness strictly improves under every singleton zero-to-one flip. -/
theorem linearFitness_coordinateStrictMonotonicity
    {n : Nat} (w : Fin n → Real) (hw : PositiveLinearWeights w) :
    CandidateCoordinateStrictMonotonicity (linearFitness w) := by
  intro x i hi
  exact linearFitness_single_zero_flip_improves w hw x i hi

/-- Positive linear and OneMax selection agree for a specified singleton. -/
theorem candidate_rls_selected_singleton_eq_oneMax
    {n : Nat} (w : Fin n → Real) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) :
    selectedAfterMask (linearFitness w) x ({i} : MutationMask n) =
      selectedAfterMask oneMaxReal x ({i} : MutationMask n) := by
  exact candidateStrictMonotoneRLS_selected_singleton_eq_oneMax
    (linearFitness w) (linearFitness_coordinateStrictMonotonicity w hw) x i

/-- Exact equality of the RLS transition matrices, for all states. -/
theorem candidate_rls_linear_transition_eq_oneMax
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
      (linearFitness w) =
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
      oneMaxReal := by
  exact support_strictMonotoneRLS_transition_eq_oneMax
    hn (linearFitness w) (linearFitness_coordinateStrictMonotonicity w hw)

end ECRuntime
