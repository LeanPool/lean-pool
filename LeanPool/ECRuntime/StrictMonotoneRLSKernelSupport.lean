/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.OneMax
public import LeanPool.ECRuntime.UniformOneBitMutation

/-!
Strict coordinate monotonicity gives the same singleton accept/reject
choices as OneMax, including reverse one-to-zero moves. This identifies
the entire one-bit RLS transition kernel.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators ENNReal
namespace ECRuntime

/-- Every singleton zero-to-one flip strictly improves the objective. -/
def CandidateCoordinateStrictMonotonicity {n : Nat}
    (fitness : BitString n → Real) : Prop :=
  ∀ (x : BitString n) (i : Fin n), x i = false →
    fitness x < fitness (mutateWithMask x ({i} : MutationMask n))

/-- A strictly monotone objective makes exactly the OneMax accept/reject
choices for a singleton mutation, including the reverse one-to-zero move. -/
private theorem candidateStrictMonotoneRLS_selected_singleton_eq_oneMax
    {n : Nat} (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (x : BitString n) (i : Fin n) :
    selectedAfterMask fitness x ({i} : MutationMask n) =
      selectedAfterMask oneMaxReal x ({i} : MutationMask n) := by
  classical
  let z : BitString n := mutateWithMask x ({i} : MutationMask n)
  by_cases hxi : x i = false
  · have ha : Accepts fitness x z := le_of_lt (hf x i hxi)
    have hb : Accepts oneMaxReal x z := by
      unfold Accepts oneMaxReal
      exact_mod_cast (Nat.le_of_lt (oneMax_single_zero_flip_improves x i hxi))
    simp [selectedAfterMask, z, elitistSelect_of_accepts _ _ _ ha,
      elitistSelect_of_accepts _ _ _ hb]
  · have hxi' : x i = true := by cases h : x i <;> simp_all
    have hzi : z i = false := by simp [z, hxi']
    have hback : mutateWithMask z ({i} : MutationMask n) = x := by simp [z]
    have hdecrease : fitness z < fitness x := by
      simpa [hback] using (hf z i hzi)
    have ha : ¬ Accepts fitness x z := not_le_of_gt hdecrease
    have hb : ¬ Accepts oneMaxReal x z := by
      unfold Accepts oneMaxReal
      have hcount := oneCount_mutate_single_of_true x i hxi'
      have hnat : oneCount z < oneCount x := by
        dsimp [z]
        omega
      exact not_le_of_gt
        (by exact_mod_cast hnat : (oneCount z : Real) < oneCount x)
    simp [selectedAfterMask, z, elitistSelect_of_rejects _ _ _ ha,
      elitistSelect_of_rejects _ _ _ hb]

/-- Strict coordinatewise monotonicity identifies RLS with OneMax RLS. -/
theorem support_strictMonotoneRLS_transition_eq_oneMax
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness) :
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness =
      (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal := by
  classical
  funext x y
  let law := StaticUnaryUnbiasedMutation.uniformOneBitLaw hn
  change (∑ mask : MutationMask n,
    if selectedAfterMask fitness x mask = y
    then law.weight mask else 0) =
    ∑ mask : MutationMask n,
      if selectedAfterMask oneMaxReal x mask = y
      then law.weight mask else 0
  apply Finset.sum_congr rfl
  intro mask _
  by_cases hc : mask.card = 1
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    subst mask
    rw [candidateStrictMonotoneRLS_selected_singleton_eq_oneMax fitness hf x i]
  · have hzero : law.weight mask = 0 := by
      dsimp [law, StaticUnaryUnbiasedMutation.uniformOneBitLaw]
      simp [hc]
    simp [hzero]

end ECRuntime
