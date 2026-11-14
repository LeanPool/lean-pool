/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.GridCellCenter
public import LeanPool.ApollonianSuperharmonic.GridSegmentLogLiftDelta

/-!
# GridHorizontalLogLiftDelta

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Set

noncomputable section

-- [TABLET NODE: GridHorizontalLogLiftDelta]
theorem GridHorizontalLogLiftDelta (q a b : GaussianInt)
    (him : a.im = b.im)
    (L : Set.Icc (0 : Real) 1 → ℂ) (hL : Continuous L)
    (hexp : ∀ t, Complex.exp (L t) =
      (1 - (t : Real)) * ((a : ℂ) - GridCellCenter q) +
        (t : Real) * ((b : ℂ) - GridCellCenter q)) :
    L ⟨1, by norm_num⟩ - L ⟨0, by norm_num⟩ =
      Complex.log ((b : ℂ) - GridCellCenter q) -
        Complex.log ((a : ℂ) - GridCellCenter q) := by
-- BODY
  apply GridSegmentLogLiftDelta _ _ _ L hL hexp
  intro t
  rw [Complex.mem_slitPlane_iff]
  right
  norm_num [GridCellCenter, Complex.mul_im]
  intro hz
  have hcast : ((a.im : Int) : Real) = (b.im : Int) := by exact_mod_cast him
  have hcastC : (a : ℂ).im = (b : ℂ).im := by simpa using hcast
  rw [← hcastC] at hz
  have haC : (a : ℂ).im = ((a.im : Int) : Real) := by simp
  have hqC : (q : ℂ).im = ((q.im : Int) : Real) := by simp
  rw [haC, hqC] at hz
  have heq2 : (((2 * (a.im - q.im) : Int) : Real)) = 1 := by
    push_cast
    linarith
  have : (2 * (a.im - q.im) : Int) = 1 := by exact_mod_cast heq2
  omega

end

end ApollonianSuperharmonic

end
