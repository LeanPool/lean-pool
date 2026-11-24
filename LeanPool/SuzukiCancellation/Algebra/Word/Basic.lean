/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin

/-!
# Ordered word products and substitution

Words are evaluated by `List.prod`, preserving the order of their letters.
The product is Mathlib's `MultilinearMap.mkPiAlgebraFin`, so homogeneity and
expansion at any finite set of positions follow from the multilinear API.

## Main definitions

* `wordEval`: evaluation of a word over an arbitrary alphabet.
* `wordPositions`: the positions at which a word carries a specified letter.

## Main results

* `smul_prod`, `sum_prod_map_smul`: homogeneity of products and word sums.
* `prod_piecewise_add`: expansion at an arbitrary set of positions.
* `prod_piecewise_add_eq_sum`: expansion of two inputs with the other positions fixed.
* `prod_word_update_add`: expansion after adding to a specified letter.
-/

@[expose] public section

namespace FQFP

/-- Evaluate a word by multiplying its letters in their given order. -/
abbrev wordEval {n : ℕ} {κ A : Type*} [Monoid A] (letters : κ → A)
    (w : Fin n → κ) : A :=
  ((List.ofFn w).map letters).prod

/-- Scaling every factor scales an ordered product by the corresponding power. -/
lemma smul_prod {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {n : ℕ} (c : R) (w : Fin n → A) :
    (List.ofFn fun i ↦ c • w i).prod = c ^ n • (List.ofFn w).prod := by
  simpa using (MultilinearMap.mkPiAlgebraFin R n A).map_smul_univ (fun _ ↦ c) w

/-- Scaling the alphabet scales a word by the power given by its length. -/
theorem prod_map_smul {R κ A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (letters : κ → A) (w : List κ) (c : R) :
    (w.map fun k ↦ c • letters k).prod = c ^ w.length • (w.map letters).prod := by
  rw [← List.ofFn_getElem_eq_map w (fun k ↦ c • letters k),
    ← List.ofFn_getElem_eq_map w letters]
  exact smul_prod c _

/-- A sum of words of length `n` is homogeneous of degree `n` in its alphabet. -/
theorem sum_prod_map_smul {R κ A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype ι] {n : ℕ} (letters : κ → A) (w : ι → Fin n → κ) (c : R) :
    (∑ i, wordEval (fun k ↦ c • letters k) (w i)) =
      c ^ n • ∑ i, wordEval letters (w i) := by
  simp only [wordEval, List.map_ofFn, Function.comp_def, smul_prod, Finset.smul_sum]

/-- Positions of a specified letter in a finite word. -/
def wordPositions {κ : Type*} [DecidableEq κ] {n : ℕ} (w : Fin n → κ)
    (a : κ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ w i = a

@[simp]
lemma mem_wordPositions {κ : Type*} [DecidableEq κ] {n : ℕ}
    (w : Fin n → κ) (a : κ) (i : Fin n) : i ∈ wordPositions w a ↔ w i = a := by
  simp [wordPositions]

/-- The positions of a letter in a list are counted by `List.count`. -/
@[simp]
lemma card_wordPositions_get {κ : Type*} [DecidableEq κ] (w : List κ) (a : κ) :
    (wordPositions w.get a).card = w.count a := by
  simpa only [List.ofFn_get, wordPositions] using (List.count_ofFn w.get a).symm

/-- Expand the sum of two inputs on a selected set, keeping the other positions fixed. -/
theorem prod_piecewise_add_eq_sum {A : Type*} [Semiring A] {n : ℕ}
    (u v w : Fin n → A) (s : Finset (Fin n)) :
    (List.ofFn (s.piecewise (u + v) w)).prod =
      ∑ t ∈ s.powerset, (List.ofFn (t.piecewise u (s.piecewise v w))).prod := by
  have h : s.piecewise (u + v) w = s.piecewise (u + s.piecewise v w) (s.piecewise v w) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [h]
  exact (MultilinearMap.mkPiAlgebraFin ℕ n A).map_piecewise_add u (s.piecewise v w) s

/-- Expand a product at selected positions without changing the order of its factors. -/
theorem prod_piecewise_add {A : Type*} [Semiring A] {n : ℕ}
    (u v : Fin n → A) (s : Finset (Fin n)) :
    (List.ofFn (s.piecewise (u + v) v)).prod =
      ∑ t ∈ s.powerset, (List.ofFn (t.piecewise u v)).prod := by
  simpa only [Finset.piecewise_same] using prod_piecewise_add_eq_sum u v v s

/-- Add to one letter of an arbitrary alphabet and expand over its positions in a word. -/
theorem prod_word_update_add {κ A : Type*} [DecidableEq κ] [Semiring A] {n : ℕ}
    (w : Fin n → κ) (letters : κ → A) (a : κ) (c : A) :
    (List.ofFn fun i ↦ Function.update letters a (letters a + c) (w i)).prod =
      ∑ s ∈ (wordPositions w a).powerset,
        (List.ofFn (s.piecewise (fun _ ↦ c) (fun i ↦ letters (w i)))).prod := by
  rw [← prod_piecewise_add]
  congr 2
  funext i
  by_cases h : w i = a <;> simp [h, Finset.piecewise, add_comm]

end FQFP
