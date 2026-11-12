/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import Mathlib.Tactic.Linarith

-- [TABLET NODE: P4536T1HalfOffsetBridge]

/-!
# P4536T1HalfOffsetBridge

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4536T1HalfOffsetBridge (A B C : GaussianInt) (h : B - C = 2 * A) :
    (1 / 2 : ℝ) • GaussianRealPoint B -
        (1 / 2 : ℝ) • GaussianRealPoint C = GaussianRealPoint A := by
-- BODY
  have hre := congrArg (fun z : GaussianInt => z.re) h
  have him := congrArg (fun z : GaussianInt => z.im) h
  have hreZ : B.re - C.re = 2 * A.re := by simpa using hre
  have himZ : B.im - C.im = 2 * A.im := by simpa using him
  have hreR : (B.re : ℝ) - (C.re : ℝ) = 2 * (A.re : ℝ) := by
    exact_mod_cast hreZ
  have himR : (B.im : ℝ) - (C.im : ℝ) = 2 * (A.im : ℝ) := by
    exact_mod_cast himZ
  apply Prod.ext
  · change (1 / 2 : ℝ) * (B.re : ℝ) -
        (1 / 2 : ℝ) * (C.re : ℝ) = (A.re : ℝ)
    linarith
  · change (1 / 2 : ℝ) * (B.im : ℝ) -
        (1 / 2 : ℝ) * (C.im : ℝ) = (A.im : ℝ)
    linarith

end ApollonianSuperharmonic

end
