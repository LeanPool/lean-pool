/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

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
    simp_all? [TangencyCoordinateNormLaw, TangencyCoordinatePolarizationLaw,
      Zsqrtd.norm_def]
  case «0».«1» | «1».«0» =>
    have a := hn 0 2 (by decide)
    have b := hn 0 3 (by decide)
    have c := hn 1 0 (by decide)
    have d := hp 2 3 0 (by decide) (by decide) (by decide)
    have e := hp 2 1 0 (by decide) (by decide) (by decide)
    have f := hp 3 1 0 (by decide) (by decide) (by decide)
    ring_nf at a b c d e f ⊢
    linarith
  case «0».«2» | «2».«0» =>
    have a := hn 0 2 (by decide)
    have b := hn 2 3 (by decide)
    have c := hn 1 2 (by decide)
    have d := hp 0 3 2 (by decide) (by decide) (by decide)
    have e := hp 0 1 2 (by decide) (by decide) (by decide)
    have f := hp 3 1 2 (by decide) (by decide) (by decide)
    ring_nf at a b c d e f ⊢
    linarith
  case «0».«3» | «3».«0» =>
    have a := hn 0 3 (by decide)
    have b := hn 2 3 (by decide)
    have c := hn 1 3 (by decide)
    have d := hp 0 2 3 (by decide) (by decide) (by decide)
    have e := hp 0 1 3 (by decide) (by decide) (by decide)
    have f := hp 2 1 3 (by decide) (by decide) (by decide)
    ring_nf at a b c d e f ⊢
    linarith

end ApollonianSuperharmonic

end
