/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.BernoulliMixture
public import Mathlib.Data.Finset.Card

/-! The correspondence between bits on omitted positions and subsets avoiding that position. -/

@[expose] public section

namespace Shellsort
open scoped BigOperators

def omittedPositionEmbedding {α : Type*} (i : α) : {j : α // j ≠ i} ↪ α :=
  ⟨Subtype.val, Subtype.val_injective⟩

def subsetOfBits {α : Type*} [Fintype α] [DecidableEq α]
    (i : α) (x : {j : α // j ≠ i} → Bool) : Finset α :=
  (Finset.univ.filter (fun j => x j = true)).map (omittedPositionEmbedding i)

theorem self_not_mem_subsetOfBits {α : Type*} [Fintype α] [DecidableEq α]
    (i : α) (x : {j : α // j ≠ i} → Bool) : i ∉ subsetOfBits i x := by
  intro hi
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi
  exact j.property hj

theorem mem_subsetOfBits {α : Type*} [Fintype α] [DecidableEq α]
    (i : α) (x : {j : α // j ≠ i} → Bool) (j : {a : α // a ≠ i}) :
    j.val ∈ subsetOfBits i x ↔ x j = true := by
  constructor
  · intro hj
    obtain ⟨k, hk, he⟩ := Finset.mem_map.mp hj
    have hkj : k = j := Subtype.ext he
    simpa only [hkj, Finset.mem_filter, Finset.mem_univ, true_and] using hk
  · intro hx
    exact Finset.mem_map.mpr ⟨j, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx],
      rfl⟩

theorem subsetOfBits_card {α : Type*} [Fintype α] [DecidableEq α]
    (i : α) (x : {j : α // j ≠ i} → Bool) :
    (subsetOfBits i x).card = finiteBitCount x := by
  simp [subsetOfBits, finiteBitCount]

/-- Concrete bits on all positions except i are equivalent to subsets excluding i. -/
def omittedBitsSubsetEquiv {α : Type*} [Fintype α] [DecidableEq α] (i : α) :
    ({j : α // j ≠ i} → Bool) ≃ {B : Finset α // i ∉ B} where
  toFun x := ⟨subsetOfBits i x, self_not_mem_subsetOfBits i x⟩
  invFun B := fun j => decide (j.val ∈ B.val)
  left_inv x := by
    funext j
    simp only [mem_subsetOfBits, Bool.decide_coe]
  right_inv B := by
    apply Subtype.ext
    apply Finset.ext
    intro j
    by_cases hj : j = i
    · subst j
      simp only [self_not_mem_subsetOfBits, B.property]
    · simp only [mem_subsetOfBits i _ ⟨j, hj⟩, decide_eq_true_eq]

theorem omittedBitsSubsetEquiv_card {α : Type*} [Fintype α] [DecidableEq α]
    (i : α) (x : {j : α // j ≠ i} → Bool) :
    ((omittedBitsSubsetEquiv i) x).val.card = finiteBitCount x :=
  subsetOfBits_card i x

theorem omittedPosition_card {α : Type*} [Fintype α] [DecidableEq α] (i : α) :
    Fintype.card {j : α // j ≠ i} + 1 = Fintype.card α := by
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨i⟩
  simp only [Fintype.card_subtype_compl, Fintype.card_unique]
  omega

end Shellsort
