/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Fermion operators

The operators `HubbardMoments.annihilate` and `HubbardMoments.create` act on the Fock space
of a finite set of orbitals `O`, in the occupation-number basis ordered by `ord : O ↪ ℕ`.

* `annihilate_conjTranspose`: `(c_o)† = c†_o`;
* `annihilate_anticomm`, `create_anticomm`, `annihilate_create_anticomm`: the canonical
  anticommutation relations `{c_o, c_o'} = 0`, `{c†_o, c†_o'} = 0`, `{c_o, c†_o'} = δ_{oo'}`;
* `create_mul_annihilate_apply`: one hop, `c†_{o'} c_o |S⟩ = (-1)^{m + p} |S \ {o} ∪ {o'}⟩`
  with `m` the number of orbitals of `S` before `o` and `p` the number of orbitals of
  `S \ {o}` before `o'`. This is the sorted-tuple sign rule of the paper's App. E.

Every fermionic matrix element in this project is computed from these operators.
-/

@[expose] public section

namespace HubbardMoments

open Finset
open scoped Matrix

variable {O : Type*} [DecidableEq O] (ord : O ↪ ℕ)

/-! ### Counting the orbitals before `o` -/

theorem countBelow_insert_self (S : Finset O) (o : O) :
    countBelow ord (insert o S) o = countBelow ord S o := by
  simp [countBelow, filter_insert]

theorem countBelow_erase_self (S : Finset O) (o : O) :
    countBelow ord (S.erase o) o = countBelow ord S o := by
  rw [countBelow, countBelow, filter_erase, erase_eq_of_notMem (by simp)]

theorem countBelow_insert {S : Finset O} {o' : O} (h : o' ∉ S) (o : O) :
    countBelow ord (insert o' S) o =
      countBelow ord S o + if ord o' < ord o then 1 else 0 := by
  rw [countBelow, countBelow, filter_insert]
  split_ifs with hlt
  · rw [card_insert_of_notMem (fun hm => h (mem_filter.1 hm).1)]
  · rfl

theorem countBelow_erase {S : Finset O} {o' : O} (h : o' ∈ S) (o : O) :
    countBelow ord S o =
      countBelow ord (S.erase o') o + if ord o' < ord o then 1 else 0 := by
  conv_lhs => rw [← insert_erase h]
  exact countBelow_insert ord (notMem_erase o' S) o

omit [DecidableEq O] in
/-- Of two distinct orbitals, exactly one comes first. -/
theorem lt_add_lt_eq_one {o o' : O} (h : o ≠ o') :
    ((if ord o' < ord o then 1 else 0) + if ord o < ord o' then 1 else 0 : ℕ) = 1 := by
  have hne : ord o ≠ ord o' := fun he => h (ord.injective he)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · simp [hlt, not_lt.2 hlt.le]
  · simp [hlt, not_lt.2 hlt.le]

theorem neg_one_pow_mul_self (n : ℕ) : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by
  rw [← mul_pow]
  simp

theorem neg_one_pow_add_add {a b δ₁ δ₂ : ℕ} (hδ : δ₁ + δ₂ = 1) :
    (-1 : ℂ) ^ (a + δ₁) * (-1) ^ (b + δ₂) + (-1) ^ b * (-1) ^ a = 0 := by
  rcases (by omega : δ₁ = 0 ∧ δ₂ = 1 ∨ δ₁ = 1 ∧ δ₂ = 0) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [pow_succ, add_zero] <;> ring

theorem neg_one_pow_cancel {a b δ₁ δ₂ : ℕ} (hδ : δ₁ + δ₂ = 1) :
    (-1 : ℂ) ^ a * (-1) ^ (b + δ₁) + (-1) ^ b * (-1) ^ (a + δ₂) = 0 := by
  rcases (by omega : δ₁ = 0 ∧ δ₂ = 1 ∨ δ₁ = 1 ∧ δ₂ = 0) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [pow_succ, add_zero] <;> ring

variable [Fintype O]

/-! ### Products with `c_o` and `c†_o` -/

theorem mul_annihilate_apply (M : Matrix (Finset O) (Finset O) ℂ) (o : O) (S' S : Finset O) :
    (M * annihilate ord o) S' S =
      if o ∈ S then M S' (S.erase o) * (-1) ^ countBelow ord S o else 0 := by
  by_cases h : o ∈ S <;> simp [Matrix.mul_apply, annihilate, h, mul_ite, sum_ite_eq']

theorem mul_create_apply (M : Matrix (Finset O) (Finset O) ℂ) (o : O) (S' S : Finset O) :
    (M * create ord o) S' S =
      if o ∉ S then M S' (insert o S) * (-1) ^ countBelow ord S o else 0 := by
  by_cases h : o ∈ S <;> simp [Matrix.mul_apply, create, h, mul_ite, sum_ite_eq']

/-! ### Adjoint and anticommutation relations -/

omit [Fintype O] in
/-- **`c†_o` is the adjoint of `c_o`.** -/
theorem annihilate_conjTranspose (o : O) : (annihilate ord o)ᴴ = create ord o := by
  ext S' S
  simp only [Matrix.conjTranspose_apply, annihilate, create]
  have e : (o ∈ S' ∧ S = S'.erase o) ↔ (o ∉ S ∧ S' = insert o S) := by
    constructor
    · rintro ⟨ho, rfl⟩
      exact ⟨notMem_erase o S', (insert_erase ho).symm⟩
    · rintro ⟨ho, rfl⟩
      exact ⟨mem_insert_self o S, (erase_insert ho).symm⟩
  by_cases h : o ∉ S ∧ S' = insert o S
  · obtain ⟨ho, rfl⟩ := h
    have hc : o ∈ insert o S ∧ S = (insert o S).erase o :=
      ⟨mem_insert_self o S, (erase_insert ho).symm⟩
    simp only [iff_true_intro hc, ho, not_false_eq_true, and_true, ↓reduceIte,
      countBelow_insert_self, star_pow, star_neg, star_one]
  · have hn : ¬ (o ∈ S' ∧ S = S'.erase o) := fun h' => h (e.1 h')
    simp only [hn, h, ↓reduceIte, star_zero]

/-- **`{c_o, c_o'} = 0`.** -/
theorem annihilate_anticomm (o o' : O) :
    annihilate ord o * annihilate ord o' + annihilate ord o' * annihilate ord o = 0 := by
  ext S' S
  simp only [Matrix.add_apply, mul_annihilate_apply, annihilate, Matrix.zero_apply]
  by_cases hoo : o = o'
  · subst hoo
    simp
  by_cases ho : o ∈ S
  swap
  · simp [ho]
  by_cases ho' : o' ∈ S
  swap
  · simp [ho']
  have h1 : o ∈ S.erase o' := mem_erase.2 ⟨hoo, ho⟩
  have h2 : o' ∈ S.erase o := mem_erase.2 ⟨Ne.symm hoo, ho'⟩
  have h3 : (S.erase o).erase o' = (S.erase o').erase o := erase_right_comm
  by_cases hS' : S' = (S.erase o').erase o
  swap
  · simp [ho, ho', h1, h2, h3, hS']
  simp only [ho, ho', h1, h2, h3, hS', and_self, ↓reduceIte]
  rw [countBelow_erase ord ho' o, countBelow_erase ord ho o']
  exact neg_one_pow_cancel (by rw [add_comm]; exact lt_add_lt_eq_one ord hoo)

/-- **`{c_o, c†_o'} = δ_{oo'}`.** -/
theorem annihilate_create_anticomm (o o' : O) :
    annihilate ord o * create ord o' + create ord o' * annihilate ord o =
      if o = o' then 1 else 0 := by
  ext S' S
  simp only [Matrix.add_apply, mul_annihilate_apply, mul_create_apply, annihilate, create]
  by_cases hoo : o = o'
  · subst hoo
    simp only [↓reduceIte, Matrix.one_apply]
    by_cases ho : o ∈ S
    · simp only [ho, not_true_eq_false, ↓reduceIte, notMem_erase, not_false_eq_true, true_and,
        insert_erase ho, countBelow_erase_self, zero_add]
      split_ifs <;> simp [neg_one_pow_mul_self]
    · simp only [ho, not_false_eq_true, ↓reduceIte, mem_insert_self, true_and, erase_insert ho,
        countBelow_insert_self, add_zero]
      split_ifs <;> simp [neg_one_pow_mul_self]
  simp only [hoo, ↓reduceIte, Matrix.zero_apply]
  by_cases ho : o ∈ S
  swap
  · simp [ho, hoo]
  by_cases ho' : o' ∈ S
  · simp [ho', Ne.symm hoo]
  have h1 : o ∈ insert o' S := mem_insert_of_mem ho
  have h2 : o' ∉ S.erase o := fun h => ho' (mem_of_mem_erase h)
  have h3 : (insert o' S).erase o = insert o' (S.erase o) := erase_insert_of_ne (Ne.symm hoo)
  by_cases hS' : S' = insert o' (S.erase o)
  swap
  · simp [ho, ho', h1, h2, h3, hS']
  simp only [ho, ho', h1, h2, h3, hS', not_false_eq_true, and_self, ↓reduceIte]
  rw [countBelow_insert ord ho' o, countBelow_erase ord ho o']
  exact neg_one_pow_add_add (lt_add_lt_eq_one ord hoo)

/-- **`{c†_o, c†_o'} = 0`.** -/
theorem create_anticomm (o o' : O) :
    create ord o * create ord o' + create ord o' * create ord o = 0 := by
  have h := congrArg Matrix.conjTranspose (annihilate_anticomm ord o' o)
  simpa [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, annihilate_conjTranspose] using h

/-- **One hop: the sorted-tuple sign rule.** `c†_{o'} c_o |S⟩ = (-1)^{m + p} |S \ {o} ∪ {o'}⟩`
when `o ∈ S` and `o' ∉ S \ {o}`, with `m` the number of orbitals of `S` before `o` and `p`
the number of orbitals of `S \ {o}` before `o'`; otherwise `0`. -/
theorem create_mul_annihilate_apply (o o' : O) (S' S : Finset O) :
    (create ord o' * annihilate ord o) S' S =
      if o ∈ S ∧ o' ∉ S.erase o ∧ S' = insert o' (S.erase o) then
        (-1) ^ (countBelow ord S o + countBelow ord (S.erase o) o') else 0 := by
  rw [mul_annihilate_apply]
  simp only [create]
  by_cases ho : o ∈ S <;> by_cases h : o' ∉ S.erase o ∧ S' = insert o' (S.erase o) <;>
    simp [ho, h, pow_add, mul_comm]

end HubbardMoments
