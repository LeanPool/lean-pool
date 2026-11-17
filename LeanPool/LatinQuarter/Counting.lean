/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import LeanPool.LatinQuarter.Rows
public import LeanPool.LatinQuarter.Tags
public import LeanPool.LatinQuarter.SquareZero

/-!
# Polynomial coefficients count Latin completions
-/

@[expose] public section

namespace LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial

/-- The factors contributed by the filled cells to the completion polynomial. -/
noncomputable def clueProduct {n : ℕ} {R : Type*} [CommRing R]
    (P : Finset (Cell n)) (L : Square n) (Y : Matrix (Fin n) (Fin n) R) : R := by
  classical
  exact ∏ r, ∏ c : {c : Fin n // (r, c) ∈ P}, Y c (L r c)

/-- The product of row matching determinants over the unfilled cells. -/
noncomputable def rowMinorProduct {n : ℕ} {R : Type*} [CommRing R]
    (P : Finset (Cell n)) (L : Square n) (Y : Matrix (Fin n) (Fin n) R) : R := by
  classical
  exact ∏ r, (Y.submatrix (fun c : FreeColumn P r => c.val)
    (fun c : FreeColumn P r => L r c)).det

/-- Expanding the row matching sums enumerates all independent ways to
finish the rows. The clue factors restore the full set of cells. -/
theorem expand_row_matchings {n : ℕ} {R : Type*} [CommRing R] [CharP R 2]
    (P : Finset (Cell n)) (L : Square n) (Y : Matrix (Fin n) (Fin n) R) :
    clueProduct P L Y * rowMinorProduct P L Y =
      ∑ σ : RowChoices P, ∏ p : Cell n, Y p.2 (chosenSquare P L σ p.1 p.2) := by
  classical
  unfold rowMinorProduct
  simp_rw [det_eq_matching_sum]
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Fintype.prod_prod_type]
  unfold clueProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r _
  have hp := Fintype.prod_subtype_mul_prod_subtype (fun c : Fin n => (r, c) ∈ P)
    (fun c => Y c (chosenSquare P L σ r c))
  convert hp using 1
  · apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro c _
      rw [chosenSquare_clue P L σ r c c.property]
    · apply Finset.prod_congr rfl
      intro c _
      simp only [Matrix.submatrix_apply, chosenSquare_free]

/-- The column-symbol position recording a cell's contribution to its monomial. -/
abbrev columnSymbol {n : ℕ} (M : Square n) (p : Cell n) : Cell n :=
  (p.2, M p.1 p.2)

theorem columnSymbol_bijective {n : ℕ} {M : Square n} (hM : IsLatin M) :
    Function.Bijective (columnSymbol M) := by
  apply Function.Injective.bijective_of_finite
  intro p q hpq
  have hc : p.2 = q.2 := congrArg Prod.fst hpq
  have hs : M p.1 p.2 = M q.1 q.2 := congrArg Prod.snd hpq
  apply Prod.ext
  · apply (hM.2 p.2).injective
    simpa only [columnSymbol, ← hc] using hs
  · exact hc

theorem isLatin_of_columnSymbol_injective {n : ℕ} {M : Square n}
    (hr : ∀ r, Function.Bijective (M r)) (hi : Function.Injective (columnSymbol M)) :
    IsLatin M := by
  refine ⟨hr, fun c => Function.Injective.bijective_of_finite ?_⟩
  intro r s h
  have he : columnSymbol M (r, c) = columnSymbol M (s, c) := Prod.ext rfl h
  exact congrArg Prod.fst (hi he)

open Classical in
/-- The full square-free coefficient is one for a Latin square and zero
for a row permutation that repeats a symbol in a column. -/
theorem full_coefficient {n : ℕ} (M : Square n)
    (hr : ∀ r, Function.Bijective (M r)) :
    (∏ p : Cell n, X (columnSymbol M p) : MvPolynomial (Cell n) (ZMod 2)).coeff
      (allTagsExponent (Cell n)) =
      if IsLatin M then 1 else 0 := by
  classical
  by_cases hM : IsLatin M
  · rw [ite_eq_left hM]
    have hp := (Equiv.ofBijective (columnSymbol M) (columnSymbol_bijective hM)).prod_comp
      (fun p => (X p : MvPolynomial (Cell n) (ZMod 2)))
    change (∏ p, X (columnSymbol M p) : MvPolynomial (Cell n) (ZMod 2)) = ∏ p, X p at hp
    rw [hp]
    exact coeff_allTags_product
  · rw [ite_eq_right hM]
    have hn : ¬ Function.Injective (columnSymbol M) :=
      fun hi => hM (isLatin_of_columnSymbol_injective hr hi)
    simp only [Function.Injective, not_forall] at hn
    obtain ⟨p, q, hpq⟩ := hn
    have he : columnSymbol M p = columnSymbol M q := by tauto
    have hne : p ≠ q := by tauto
    apply squarefree_coeff_zero_of_quotient_zero _ (by simp)
    simp only [map_prod]
    change (∏ p : Cell n, tag (columnSymbol M p)) = 0
    exact product_eq_zero_of_repeated_square_zero _ hne (congrArg tag he) (tag_sq _)

open Classical in
/-- The highest square-free coefficient counts the Latin row choices modulo two. -/
theorem coefficient_eq_sum_latin_choices {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (hL : IsLatin L) (a : Cell n → ZMod 2) :
    (clueProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s))) *
      rowMinorProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s)))).coeff
      (allTagsExponent (Cell n)) =
      ∑ σ : RowChoices P, if IsLatin (chosenSquare P L σ) then (1 : ZMod 2) else 0 := by
  classical
  rw [expand_row_matchings, coeff_sum]
  apply Finset.sum_congr rfl
  intro σ _
  change (∏ p : Cell n, (X (columnSymbol (chosenSquare P L σ) p) +
    C (a (columnSymbol (chosenSquare P L σ) p)))).coeff (allTagsExponent (Cell n)) = _
  rw [coeff_prod_add_constants _ _ _ (by simp)]
  exact full_coefficient _ (chosenSquare_rows P L hL σ)

/-- Adding constants preserves the completion coefficient, and unique
completion makes that coefficient exactly one. -/
theorem defining_coefficient_one {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (h : IsDefining P L) (a : Cell n → ZMod 2) :
    (clueProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s))) *
      rowMinorProduct P L (Matrix.of fun c s => X (c, s) + C (a (c, s)))).coeff
      (allTagsExponent (Cell n)) = 1 := by
  classical
  rw [coefficient_eq_sum_latin_choices P L h.1 a]
  rw [Finset.sum_eq_single (1 : RowChoices P)]
  · simp [h.1]
  · intro σ _ hσ
    rw [ite_eq_right]
    exact fun hl => hσ (unique_chosenSquare P L h σ hl)
  · simp

end LatinQuarter
