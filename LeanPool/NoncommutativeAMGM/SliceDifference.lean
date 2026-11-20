/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.MixedMoments
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # The alternating coefficient in the harmonic slice norm -/

@[expose] public section
namespace NoncommutativeAMGM
open scoped BigOperators

theorem powerset_mixedMoment {n : ℕ} (r : ℕ) (s : ℝ) (U : Finset (Fin n))
    (hsize : r + U.card ≤ n) :
    (∑ V ∈ U.powerset, (-1 : ℝ) ^ V.card * sliceMoment n s (r + V.card)) =
      falling s r * falling ((n : ℝ) - s) U.card / falling n (r + U.card) := by
  classical
  induction U using Finset.induction_on generalizing r with
  | empty => simp [sliceMoment]
  | @insert i U hi ih =>
    have hcard : (insert i U).card = U.card + 1 := Finset.card_insert_of_notMem hi
    have he : (∑ V ∈ U.powerset,
        (-1 : ℝ) ^ (insert i V).card * sliceMoment n s (r + (insert i V).card)) =
        -(∑ V ∈ U.powerset, (-1 : ℝ) ^ V.card * sliceMoment n s (r + 1 + V.card)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro V hV
      have hiV : i ∉ V := fun h ↦ hi ((Finset.mem_powerset.mp hV) h)
      rw [Finset.card_insert_of_notMem hiV, pow_succ]
      rw [show r + (V.card + 1) = r + 1 + V.card by omega]
      ring
    rw [Finset.sum_powerset_insert hi, he, ← sub_eq_add_neg, hcard]
    rw [ih r (by omega), ih (r + 1) (by omega)]
    exact mixed_moment_step n r U.card s (by omega)

theorem powerset_harmonic_weight {n : ℕ} (s : ℝ) (S : Finset (Fin n))
    (hsize : 2 * S.card ≤ n) :
    (∑ R ∈ S.powerset, (-1 : ℝ) ^ (S.card - R.card) *
      sliceMoment n s (2 * S.card - R.card)) =
      falling s S.card * falling ((n : ℝ) - s) S.card / falling n (2 * S.card) := by
  classical
  have he : (∑ R ∈ S.powerset, (-1 : ℝ) ^ (S.card - R.card) *
      sliceMoment n s (2 * S.card - R.card)) =
      ∑ V ∈ S.powerset, (-1 : ℝ) ^ V.card * sliceMoment n s (S.card + V.card) := by
    apply Finset.sum_bij (fun R _ ↦ S \ R)
    · intro R _
      exact Finset.mem_powerset.mpr Finset.sdiff_subset
    · intro R hR V hV heq
      have hRS := Finset.mem_powerset.mp hR
      have hVS := Finset.mem_powerset.mp hV
      have heq' := congrArg (fun T ↦ S \ T) heq
      simpa [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr hRS,
        Finset.inter_eq_right.mpr hVS] using heq'
    · intro V hV
      refine ⟨S \ V, Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
      exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hV)
    · intro R hR
      have hRS := Finset.mem_powerset.mp hR
      rw [Finset.card_sdiff_of_subset hRS]
      congr 2
      have := Finset.card_le_card hRS
      omega
  rw [he]
  simpa [two_mul] using powerset_mixedMoment S.card s S (by omega)

end NoncommutativeAMGM
