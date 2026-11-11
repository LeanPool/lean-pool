/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.OneMax
public import LeanPool.ECRuntime.RLSOneBitExpectationSupport
public import LeanPool.ECRuntime.UniformOneBitMutation

/-!
The exact one-step drift of the zero count under one-bit RLS.
It is the eigenfunction identity used in the finite survival estimate.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/-- The outcome of flipping one prescribed coordinate under elitist OneMax
    is exactly the initial zero count or one less.  This is the local
    combinatorial identity needed for the exact Stage-124 one-step mean. -/
private theorem stage124_selected_zeroCount_singleton
    {n : Nat} (x : BitString n) (i : Fin n) :
    zeroCount (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) =
      if x i = false then zeroCount x - 1 else zeroCount x := by
  by_cases hxi : x i = false
  · have hacc : Accepts oneMaxReal x
        (mutateWithMask x ({i} : MutationMask n)) := by
      unfold Accepts oneMaxReal
      exact_mod_cast Nat.le_of_lt (oneMax_single_zero_flip_improves x i hxi)
    rw [selectedAfterMask, elitistSelect_of_accepts _ _ _ hacc, ite_eq_left hxi]
    have hcount := zeroCount_mutate_single_of_false x i hxi
    omega
  · have hxi' : x i = true := by
      cases hi : x i <;> simp_all
    have hrej : ¬ Accepts oneMaxReal x
        (mutateWithMask x ({i} : MutationMask n)) := by
      unfold Accepts oneMaxReal
      have hcount := oneCount_mutate_single_of_true x i hxi'
      have hdrop : oneCount (mutateWithMask x ({i} : MutationMask n)) <
          oneCount x := by omega
      exact not_le_of_gt (by exact_mod_cast hdrop :
        (oneCount (mutateWithMask x ({i} : MutationMask n)) : Real) <
          (oneCount x : Real))
    rw [selectedAfterMask, elitistSelect_of_rejects _ _ _ hrej, ite_eq_right hxi]

/-- RLS on OneMax decreases the expected zero count by a fraction `1/n`
in every state, including the optimum. -/
theorem proposed_rlsOneMax_expectedZeroCount_oneStep
    {n : Nat} (hn : 0 < n) (x : BitString n) :
    expectedValueAfter
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      (fun y : BitString n => (zeroCount y : Real)) x =
        (1 - 1 / (n : Real)) * (zeroCount x : Real) := by
  exact candidate_rlsOneMax_expectedZeroCount_exact hn x

end ECRuntime
