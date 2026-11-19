/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.FermionOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Fermion operators

The operators `HubbardMoments.annihilate` and `HubbardMoments.create` act on the Fock space
of a finite set of orbitals `O`, in the occupation-number basis ordered by `ord : O ↪ ℕ`.

* `annihilate_conjTranspose`: `(c_o)† = c†_o`;
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

variable [Fintype O]

/-! ### Products with `c_o` and `c†_o` -/

theorem mul_annihilate_apply (M : Matrix (Finset O) (Finset O) ℂ) (o : O) (S' S : Finset O) :
    (M * annihilate ord o) S' S =
      if o ∈ S then M S' (S.erase o) * (-1) ^ countBelow ord S o else 0 := by
  by_cases h : o ∈ S <;> simp [Matrix.mul_apply, annihilate, h, mul_ite, sum_ite_eq']

/-! ### Adjoint -/

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
