/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import LeanPool.AaronsonAmbainis.DetLow.Basic

/-!
# DetLow: the degree of the determinant of the agreement matrix in each variable

In each variable the determinant of the agreement matrix has degree at most the number of ones
of `g`. This is a step of the proof of Lemma 3.6 of the paper.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Each entry of the agreement matrix has degree at most one in each variable. -/
theorem degreeOf_agMon_le (x z : Cube ι) (j : ι) : degreeOf j (agMon x z) ≤ 1 := by
  classical
  unfold agMon
  refine (degreeOf_prod_le j univ _).trans ?_
  calc ∑ i, degreeOf j (if x i = z i then (X i : MvPolynomial ι ℤ) else 1)
      ≤ ∑ i, (if j = i then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : x i = z i
        · rw [ite_eq_left h, degreeOf_X]
        · rw [ite_eq_right h, degreeOf_one]
          exact Nat.zero_le _
    _ = 1 := by simp

/-- In the variable `s_j` the determinant of the agreement matrix has degree at most the number
of ones of `g` (proof of Lemma 3.6 of the paper). -/
theorem degreeOf_det_le (g : Cube ι → Bool) (j : ι) :
    degreeOf j (agMatrix g).det ≤ Fintype.card (Ones g) := by
  have hc : ∀ n : ℤ, degreeOf j ((n : MvPolynomial ι ℤ)) = 0 := by
    intro n
    rw [← eq_intCast (C : ℤ →+* MvPolynomial ι ℤ) n, degreeOf_C]
  rw [Matrix.det_apply']
  refine (degreeOf_sum_le j univ _).trans ?_
  apply Finset.sup_le
  intro σ _
  refine (degreeOf_mul_le j _ _).trans ?_
  rw [hc, zero_add]
  refine (degreeOf_prod_le j univ _).trans ?_
  calc ∑ i : Ones g, degreeOf j (agMatrix g (σ i) i) ≤ ∑ _i : Ones g, 1 :=
        Finset.sum_le_sum (fun i _ => degreeOf_agMon_le _ _ j)
    _ = Fintype.card (Ones g) := by simp

end DetLow
end AaronsonAmbainis
