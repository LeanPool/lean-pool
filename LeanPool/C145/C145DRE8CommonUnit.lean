/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

/-! Finite-coordinate common-unit tensor bound for C145 DRE8 Lemma B.
All energies are explicit coordinate sums. No matrix/Pi default norm occurs. -/

@[expose] public section

namespace C145DRE8
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sum of squares of all entries of a cubic tensor. -/
noncomputable def tensorSq (E : ι → ι → ι → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, E i j k ^ 2
/-- Sum of squares of tensor entries whose second and third indices differ. -/
noncomputable def offSq (E : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if j = k then 0 else E i j k ^ 2
/-- Sum of squares of entries with equal last two indices and a distinct first index. -/
noncomputable def repeatSq (E : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else E i j j ^ 2
/-- Sum of squares of entries with all three indices equal. -/
noncomputable def diagSq (E : ι → ι → ι → ℝ) : ℝ := ∑ j, E j j j ^ 2

theorem repeatSq_nonneg (E : ι → ι → ι → ℝ) : 0 ≤ repeatSq E := by
  unfold repeatSq
  positivity

theorem tensorSq_decompose (E : ι → ι → ι → ℝ) :
    tensorSq E = offSq E + repeatSq E + diagSq E := by
  have hpoint (i j k : ι) : E i j k ^ 2 =
      (if j = k then 0 else E i j k ^ 2) + (if j = k then E i j k ^ 2 else 0) := by
    split_ifs <;> ring
  have hsum : tensorSq E = offSq E + ∑ i, ∑ j, E i j j ^ 2 := by
    unfold tensorSq offSq
    calc
      _ = ∑ i, ∑ j, ∑ k, ((if j = k then 0 else E i j k ^ 2) +
            (if j = k then E i j k ^ 2 else 0)) := by
        apply Finset.sum_congr rfl; intro i hi
        apply Finset.sum_congr rfl; intro j hj
        apply Finset.sum_congr rfl; intro k hk
        exact hpoint i j k
      _ = _ := by simp [Finset.sum_add_distrib]
  rw [hsum, add_assoc]
  congr 1
  unfold repeatSq diagSq
  calc
    _ = ∑ i, ∑ j, ((if i = j then 0 else E i j j ^ 2) +
          (if i = j then E i j j ^ 2 else 0)) := by
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      split_ifs <;> ring
    _ = _ := by simp [Finset.sum_add_distrib]

theorem repeat_le_half_off (E : ι → ι → ι → ℝ)
    (h13 : ∀ i j k, E i j k = E k j i)
    (h12 : ∀ i j k, E i j k = E j i k) :
    2 * repeatSq E ≤ offSq E := by
  let A : ι → ι → ι → ℝ := fun i j k => if i = j then
    (if j = k then 0 else E i j k ^ 2) else 0
  let B : ι → ι → ι → ℝ := fun i j k => if i = k then
    (if j = k then 0 else E i j k ^ 2) else 0
  have hp (i j k : ι) : A i j k + B i j k ≤
      if j = k then 0 else E i j k ^ 2 := by
    dsimp [A, B]
    split_ifs with hij hjk hik <;> subst_vars <;> simp_all [sq_nonneg]
  have hA : (∑ i, ∑ j, ∑ k, A i j k) = repeatSq E := by
    rw [Finset.sum_comm]
    unfold repeatSq
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k hk
    simp only [A, Fintype.sum_ite_eq']
    by_cases hjk : j = k
    · simp [hjk]
    · simp only [hjk, Ne.symm hjk, ↓reduceIte]
      rw [h13]
  have hB : (∑ i, ∑ j, ∑ k, B i j k) = repeatSq E := by
    unfold repeatSq
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    simp only [B, Fintype.sum_ite_eq]
    by_cases hij : i = j
    · simp [hij]
    · simp only [Ne.symm hij, ↓reduceIte]
      rw [h12]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
      Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hp i j k)))
  simp only [Finset.sum_add_distrib] at hh
  rw [hA, hB] at hh
  unfold offSq
  linarith

theorem common_unit_diag_bound (E : ι → ι → ι → ℝ)
    (hunit : ∀ j, ∑ i, E i j j = 0) :
    diagSq E ≤ ((Fintype.card ι : ℝ) - 1) * repeatSq E := by
  have hj (j : ι) : E j j j ^ 2 ≤ ((Fintype.card ι : ℝ) - 1) *
      ∑ i, if i = j then 0 else E i j j ^ 2 := by
    let s := Finset.univ.erase j
    have hsum : ∑ i ∈ s, E i j j = - E j j j := by
      have hh := Finset.sum_erase_add Finset.univ (fun i => E i j j) (Finset.mem_univ j)
      rw [hunit j] at hh
      dsimp [s]
      linarith
    have hc : (s.card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
      dsimp [s]
      rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
      simp only [Finset.card_univ]
      rw [Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨j⟩)]
      simp
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => E i j j)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    rw [hsum, neg_sq, hc] at hcs
    have he : (∑ i ∈ s, E i j j ^ 2) = ∑ i, if i = j then 0 else E i j j ^ 2 := by
      dsimp [s]
      symm
      rw [← Finset.sum_erase_add Finset.univ
        (fun i => if i = j then 0 else E i j j ^ 2) (Finset.mem_univ j)]
      simp only [↓reduceIte, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      simp [(Finset.mem_erase.mp hi).1]
    rwa [he] at hcs
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
  rw [← Finset.mul_sum] at hh
  rw [Finset.sum_comm] at hh
  exact hh

/-- DRE8's common-unit/symmetry contribution, valid also for empty and singleton index sets. -/
theorem common_unit_tensor_bound (E : ι → ι → ι → ℝ)
    (h13 : ∀ i j k, E i j k = E k j i)
    (h12 : ∀ i j k, E i j k = E j i k)
    (hunit : ∀ j, ∑ i, E i j j = 0) :
    2 * tensorSq E ≤ ((Fintype.card ι : ℝ) + 2) * offSq E := by
  have hd := common_unit_diag_bound E hunit
  have hu := repeat_le_half_off E h13 h12
  have hc : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_left hu hc
  rw [tensorSq_decompose]
  nlinarith

end C145DRE8

end
