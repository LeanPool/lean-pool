/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateNormLaw
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinatePolarizationLaw

-- [TABLET NODE: TangencyCoordinateSuccessorNorm]

/-!
# TangencyCoordinateSuccessorNorm

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TangencyCoordinateSuccessorNorm (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q)
    (hp : TangencyCoordinatePolarizationLaw q) :
    TangencyCoordinateNormLaw
      ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
          2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
        q 0, q 2, q 3] := by
-- BODY
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all only [TangencyCoordinateNormLaw, ne_eq, Int.reduceNeg, zsmul_eq_mul,
        Zsqrtd.norm_def, Zsqrtd.re_sub, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast,
        mul_zero, zero_mul, add_zero, Zsqrtd.im_sub, Zsqrtd.im_mul, neg_mul, one_mul, neg_sub,
        TangencyCoordinatePolarizationLaw, Fin.mk_one, Fin.isValue, Fin.reduceFinMk,
        Fin.reduceEq, not_false_eq_true, Matrix.cons_val, Matrix.cons_val_one,
        Matrix.cons_val_zero, Fin.zero_eta, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_ofNat, Zsqrtd.re_add, Zsqrtd.re_ofNat, Nat.cast_ofNat,
        Zsqrtd.im_ofNat, Zsqrtd.im_add, sub_self, not_true_eq_false]
  case «0».«1» | «1».«0» =>
    have a := hn 0 2 (by decide)
    have b := hn 0 3 (by decide)
    have c := hn 1 0 (by decide)
    have d := hp 2 3 0 (by decide) (by decide) (by decide)
    have e := hp 2 1 0 (by decide) (by decide) (by decide)
    have f := hp 3 1 0 (by decide) (by decide) (by decide)
    linear_combination 4 * a + 4 * b + c + 8 * d - 4 * e - 4 * f
  case «0».«2» | «2».«0» =>
    have a := hn 0 2 (by decide)
    have b := hn 2 3 (by decide)
    have c := hn 1 2 (by decide)
    have d := hp 0 3 2 (by decide) (by decide) (by decide)
    have e := hp 0 1 2 (by decide) (by decide) (by decide)
    have f := hp 3 1 2 (by decide) (by decide) (by decide)
    linear_combination 4 * a + 4 * b + c + 8 * d - 4 * e - 4 * f
  case «0».«3» | «3».«0» =>
    have a := hn 0 3 (by decide)
    have b := hn 2 3 (by decide)
    have c := hn 1 3 (by decide)
    have d := hp 0 2 3 (by decide) (by decide) (by decide)
    have e := hp 0 1 3 (by decide) (by decide) (by decide)
    have f := hp 2 1 3 (by decide) (by decide) (by decide)
    linear_combination 4 * a + 4 * b + c + 8 * d - 4 * e - 4 * f

end ApollonianSuperharmonic

end
