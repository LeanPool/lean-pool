/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.LinearAlgebra.AffineSpace.Independent

-- [TABLET NODE: P4802T1TriangleIndependent]

/-!
# P4802T1TriangleIndependent

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4802T1TriangleIndependent (p : Fin 3 → Real × Real)
    (hd : (p 1).1 * (p 2).2 - (p 1).1 * (p 0).2 -
      (p 0).1 * (p 2).2 - (p 1).2 * (p 2).1 +
      (p 1).2 * (p 0).1 + (p 0).2 * (p 2).1 ≠ 0) :
    AffineIndependent Real p := by
-- BODY
  rw [affineIndependent_iff_of_fintype]
  intro w hw hp
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hp
  have hx := congrArg Prod.fst hp
  have hy := congrArg Prod.snd hp
  simp only [ Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_one_eq_two, Prod.fst_add, Prod.smul_fst,
    smul_eq_mul, Prod.fst_zero, Prod.snd_add, Prod.smul_snd, Prod.snd_zero ] at hw hx hy
  have h1 : w 1 = 0 := by
    apply (mul_eq_zero.mp (show w 1 *
      ((p 1).1 * (p 2).2 - (p 1).1 * (p 0).2 -
      (p 0).1 * (p 2).2 - (p 1).2 * (p 2).1 +
      (p 1).2 * (p 0).1 + (p 0).2 * (p 2).1) = 0 from ?_)).resolve_right hd
    linear_combination ((p 2).2 - (p 0).2) * hx -
      ((p 2).1 - (p 0).1) * hy +
      ((p 0).2 * (p 2).1 - (p 0).1 * (p 2).2) * hw
  have h2 : w 2 = 0 := by
    apply (mul_eq_zero.mp (show w 2 *
      ((p 1).1 * (p 2).2 - (p 1).1 * (p 0).2 -
      (p 0).1 * (p 2).2 - (p 1).2 * (p 2).1 +
      (p 1).2 * (p 0).1 + (p 0).2 * (p 2).1) = 0 from ?_)).resolve_right hd
    linear_combination -((p 1).2 - (p 0).2) * hx +
      ((p 1).1 - (p 0).1) * hy +
      ((p 0).1 * (p 1).2 - (p 0).2 * (p 1).1) * hw
  intro i
  fin_cases i <;> simp_all

end ApollonianSuperharmonic

end
