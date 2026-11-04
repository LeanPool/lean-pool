/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import LeanPool.LatinQuarter.Counting
public import LeanPool.LatinQuarter.Shifted
public import LeanPool.LatinQuarter.Budget

/-!
# The lower bound for defining sets
-/

@[expose] public section

namespace LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial

/-- Below the quarter bound, any balanced choice of marked positions makes the
completion polynomial's highest square-free coefficient vanish. No Latin condition
on the reference square is required. -/
theorem small_clue_coefficient_zero {n : ℕ} (P : Finset (Cell n)) (L : Square n)
    (e : Fin (n / 2) ⊕ Fin (n - n / 2) ≃ Fin n) (hP : P.card < n * n / 4) :
    (clueProduct P L (Matrix.of fun c s => X (c, s) + C (markedConstant e c s)) *
      rowMinorProduct P L (Matrix.of fun c s => X (c, s) + C (markedConstant e c s))).coeff
      (allTagsExponent (Cell n)) = 0 := by
  classical
  let Y : Matrix (Fin n) (Fin n) (MvPolynomial (Cell n) (ZMod 2)) :=
    fun c s => X (c, s) + C (markedConstant e c s)
  let q := Ideal.Quotient.mk (repeatedTagIdeal (Cell n))
  have hrow : q (rowMinorProduct P L Y) = rowMinorProduct P L (shiftedTags e) := by
    unfold rowMinorProduct
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro r _
    rw [q.map_det]
    congr 1
  have hz : rowMinorProduct P L (shiftedTags e) = 0 :=
    shifted_tags_product_vanishes e (fun r => FreeColumn P r)
      (fun _ c => c.val) (fun r c => L r c) (clue_budget P hP)
  have hzq : q (clueProduct P L Y * rowMinorProduct P L Y) = 0 := by
    rw [map_mul, hrow, hz, mul_zero]
  exact squarefree_coeff_zero_of_quotient_zero hzq (by simp)

/-- Every defining set in every labelled Latin square has at least the
quarter-square number of clues. No restriction on the completed square
or on the distribution of its clues is assumed. -/
theorem defining_set_lower_bound {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (h : IsDefining P L) : n * n / 4 ≤ P.card := by
  classical
  by_contra! hP
  let e : Fin (n / 2) ⊕ Fin (n - n / 2) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (by omega))
  have hc0 := small_clue_coefficient_zero P L e hP
  have hc1 := defining_coefficient_one P L h (fun p => markedConstant e p.1 p.2)
  exact zero_ne_one (hc0.symm.trans hc1)

end LatinQuarter
