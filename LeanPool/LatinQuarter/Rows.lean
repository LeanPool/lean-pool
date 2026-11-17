/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.CharP.Two
public import LeanPool.LatinQuarter.Basic

/-!
# Independent permutations of free row entries
-/

@[expose] public section

namespace LatinQuarter
open scoped BigOperators Matrix

/-- Columns whose entries in row `r` have not been specified as clues. -/
abbrev FreeColumn {n : ℕ} (P : Finset (Cell n)) (r : Fin n) :=
  {c : Fin n // (r, c) ∉ P}

/-- Independent permutations of the unfilled positions in each row. -/
abbrev RowChoices {n : ℕ} (P : Finset (Cell n)) :=
  (r : Fin n) → Equiv.Perm (FreeColumn P r)

/-- Permute the symbols of each row only within its unfilled cells. -/
noncomputable def chosenSquare {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (σ : RowChoices P) : Square n := by
  classical
  exact fun r c => L r ((σ r).subtypeCongr (Equiv.refl _) c)

@[simp] theorem chosenSquare_free {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (σ : RowChoices P) (r : Fin n) (c : FreeColumn P r) :
    chosenSquare P L σ r c = L r (σ r c) := by
  classical
  simp [chosenSquare]

@[simp] theorem chosenSquare_clue {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (σ : RowChoices P) (r c : Fin n) (hc : (r, c) ∈ P) :
    chosenSquare P L σ r c = L r c := by
  classical
  simp [chosenSquare, hc]

@[simp] theorem chosenSquare_one {n : ℕ} (P : Finset (Cell n)) (L : Square n) :
    chosenSquare P L 1 = L := by
  classical
  ext r c
  simp [chosenSquare, Equiv.Perm.subtypeCongr.apply]

theorem chosenSquare_rows {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (hL : IsLatin L) (σ : RowChoices P) :
    ∀ r, Function.Bijective (chosenSquare P L σ r) := by
  classical
  intro r
  exact (hL.1 r).comp ((σ r).subtypeCongr (Equiv.refl _)).bijective

theorem chosenSquare_agrees {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (σ : RowChoices P) : Agrees P L (chosenSquare P L σ) := by
  intro p hp
  exact chosenSquare_clue P L σ p.1 p.2 hp

theorem chosenSquare_injective {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (hL : IsLatin L) : Function.Injective (chosenSquare P L) := by
  intro σ τ h
  funext r
  apply Equiv.ext
  intro c
  apply Subtype.ext
  apply (hL.1 r).injective
  have he := congrArg (fun M => M r c) h
  simpa only [chosenSquare_free] using he

theorem unique_chosenSquare {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (h : IsDefining P L) (σ : RowChoices P)
    (hσ : IsLatin (chosenSquare P L σ)) : σ = 1 := by
  apply chosenSquare_injective P L h.1
  rw [chosenSquare_one]
  exact h.2 _ hσ (chosenSquare_agrees P L σ)

/-- In characteristic two the determinant is exactly the unsigned
matching sum, written with a choice in each selected row. -/
theorem det_eq_matching_sum {R ι : Type*} [CommRing R] [CharP R 2]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    M.det = ∑ σ : Equiv.Perm ι, ∏ i, M i (σ i) := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  have hs : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
      simp [h, CharTwo.neg_eq]
  rw [hs, one_mul]
  rfl

end LatinQuarter
