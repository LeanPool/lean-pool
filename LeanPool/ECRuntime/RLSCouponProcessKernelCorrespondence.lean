/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.StrictMonotoneRLS

/-!
The coupon process has a Boolean vector of collected types as its state.
A uniformly chosen coordinate is set to true; a previously collected type is
retained. The observable identity below makes that update rule explicit and
identifies its kernel with strictly coordinate-monotone one-bit RLS.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Explicit one-coupon sampling kernel. -/
noncomputable def randomStakeCouponTransition
    {n : Nat} (hn : 0 < n) : TransitionMatrix (BitString n) :=
  (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal

/-- The coupon kernel is stochastic. -/
theorem randomStakeCouponTransition_stochastic {n : Nat} (hn : 0 < n) :
    IsStochastic (randomStakeCouponTransition hn) :=
  (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition_stochastic oneMaxReal

/-- OneMax selection sets the sampled coordinate to true and retains every other bit. -/
theorem oneMax_selectedAfterMask_singleton_eq_update
    {n : Nat} (x : BitString n) (i : Fin n) :
    selectedAfterMask oneMaxReal x ({i} : MutationMask n) = Function.update x i true := by
  classical
  by_cases hi : x i = false
  · have haccept : Accepts oneMaxReal x (mutateWithMask x {i}) := by
      unfold Accepts oneMaxReal
      exact_mod_cast (Nat.le_of_lt (oneMax_single_zero_flip_improves x i hi))
    rw [selectedAfterMask, elitistSelect_of_accepts _ _ _ haccept]
    funext j
    by_cases hji : j = i
    · subst j
      simp [mutateWithMask, hi]
    · simp [mutateWithMask, hji]
  · have hitrue : x i = true := by cases h : x i <;> simp_all
    have hreject : ¬ Accepts oneMaxReal x (mutateWithMask x {i}) := by
      unfold Accepts oneMaxReal
      have hcount := oneCount_mutate_single_of_true x i hitrue
      have hdrop : oneCount (mutateWithMask x {i}) < oneCount x := by omega
      exact not_le_of_gt (by exact_mod_cast hdrop :
        (oneCount (mutateWithMask x {i}) : Real) < (oneCount x : Real))
    rw [selectedAfterMask, elitistSelect_of_rejects _ _ _ hreject]
    funext j
    by_cases hji : j = i
    · subst j
      simp [hitrue]
    · simp [hji]

/-- Every coupon-step observable is averaged over all uniformly sampled coordinates.
The initial state is arbitrary; the update retains coupons already present. -/
theorem randomStakeCoupon_expectedValueAfter_eq_uniform_updates
    {n : Nat} (hn : 0 < n) (F : BitString n → Real) (x : BitString n) :
    expectedValueAfter (randomStakeCouponTransition hn) F x =
      (n : Real)⁻¹ * ∑ i : Fin n, F (Function.update x i true) := by
  change expectedValueAfter
    ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal) F x = _
  rw [candidate_rls_expectedValueAfter_eq_singleton_average hn oneMaxReal F x]
  simp_rw [oneMax_selectedAfterMask_singleton_eq_update]

/-- Uniform coupon sampling and strictly coordinate-monotone one-bit
RLS agree as Markov kernels. -/
theorem proposed_couponProcess_transition_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness) :
    randomStakeCouponTransition hn =
      (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness := by
  exact (candidateStrictMonotoneRLS_transition_eq_oneMax hn fitness hf).symm

end ECRuntime
