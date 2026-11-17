/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.DetLow.Unit
public import LeanPool.AaronsonAmbainis.DetLow.NonZero
public import LeanPool.AaronsonAmbainis.DetLow.RowOps
public import LeanPool.AaronsonAmbainis.DetLow.Degree
public import LeanPool.AaronsonAmbainis.DetLow.Count

/-!
# DetLow: the theorems `lowestUnit : LowestUnit` and `lowestBound : LowestBound`

`lowestUnit` is Lemma 3.3 of the paper; `lowestBound` is Lemma 3.4 and Lemma 3.6.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

/-- Lemma 3.3 of the paper: multiplying by a polynomial with constant coefficient `1` does not
change the monomials of least total degree. -/
theorem lowestUnit : AaronsonAmbainis.LowestUnit := by
  intro ι _ u q hu m
  exact ⟨isLowest_of_unit_mul u q hu m, isLowest_unit_mul u q hu m⟩

/-- The cofactor `R` of `(1 - s_j^2)^(e_j)` has degree at most `b_j(g)` in `s_j` (proof of
Lemma 3.6 of the paper). -/
theorem degreeOf_cofactor_le {ι : Type} [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (j : ι)
    (R : MvPolynomial ι ℤ) (hR : (agMatrix g).det = (1 - X j ^ 2) ^ (Up g j).card * R) :
    degreeOf j R ≤ bdry g j := by
  have hp : (agMatrix g).det ≠ 0 := agMatrix_det_ne_zero g
  have hu0 : ((1 : MvPolynomial ι ℤ) - X j ^ 2) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp at h'
  have hR0 : R ≠ 0 := by
    rintro rfl
    exact hp (by rw [hR, mul_zero])
  have hdeg1 : degreeOf j ((1 : MvPolynomial ι ℤ) - X j ^ 2) = 2 := by
    have h : (1 : MvPolynomial ι ℤ) - X j ^ 2 = -(X j ^ 2) + 1 := by ring
    have hlt : degreeOf j (1 : MvPolynomial ι ℤ) < degreeOf j (-(X j ^ 2 : MvPolynomial ι ℤ)) := by
      rw [degreeOf_neg, degreeOf_X_self_pow, degreeOf_one]
      norm_num
    rw [h, degreeOf_add_eq_of_degreeOf_lt hlt, degreeOf_neg, degreeOf_X_self_pow]
  have h1 := degreeOf_det_le g j
  rw [hR, degreeOf_mul_eq (pow_ne_zero _ hu0) hR0, degreeOf_pow_eq j _ _ hu0, hdeg1,
    card_ones_eq g j] at h1
  omega

/-- Lemma 3.4 and Lemma 3.6 of the paper: the determinant of the agreement matrix is nonzero, and
each of its monomials of least total degree has exponent at most `b_j(g)` in every variable
`s_j`. -/
theorem lowestBound : AaronsonAmbainis.LowestBound := by
  intro ι _ _ g
  refine ⟨agMatrix_det_ne_zero g, ?_⟩
  intro m hm j
  obtain ⟨R, hR⟩ := det_factor g j
  have hu : constantCoeff ((1 - X j ^ 2 : MvPolynomial ι ℤ) ^ (Up g j).card) = 1 := by
    simp
  rw [hR] at hm
  have hlow : IsLowest R m := isLowest_of_unit_mul _ R hu m hm
  exact (monomial_le_degreeOf j hlow.1).trans (degreeOf_cofactor_le g j R hR)

end DetLow
end AaronsonAmbainis
