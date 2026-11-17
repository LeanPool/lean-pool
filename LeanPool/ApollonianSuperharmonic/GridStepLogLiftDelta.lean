/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.GridHorizontalLogLiftDelta
public import LeanPool.ApollonianSuperharmonic.GridVerticalDownLogLiftDelta
public import LeanPool.ApollonianSuperharmonic.GridVerticalUpLogLiftDelta

/-!
# GridStepLogLiftDelta

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Set

noncomputable section

-- [TABLET NODE: GridStepLogLiftDelta]
theorem GridStepLogLiftDelta (q a b : GaussianInt)
    (hab : FourNeighborAdjacent a b)
    (L : Set.Icc (0 : Real) 1 → ℂ) (hL : Continuous L)
    (hexp : ∀ t, Complex.exp (L t) =
      (1 - (t : Real)) * ((a : ℂ) - GridCellCenter q) +
        (t : Real) * ((b : ℂ) - GridCellCenter q)) :
    L ⟨1, by norm_num⟩ - L ⟨0, by norm_num⟩ =
      Complex.log ((b : ℂ) - GridCellCenter q) -
        Complex.log ((a : ℂ) - GridCellCenter q) -
        (2 * Real.pi * Complex.I) *
          (if b = a + ⟨0, 1⟩ ∧ a.im = q.im ∧ a.re ≤ q.re then (1 : Int)
           else if b = a - ⟨0, 1⟩ ∧ b.im = q.im ∧ a.re ≤ q.re then (-1 : Int)
           else 0) := by
-- BODY
  rcases hab with rfl | rfl | rfl | rfl
  · have h := GridHorizontalLogLiftDelta q a (a + 1) (by simp) L hL hexp
    have hneU : a + 1 ≠ a + ⟨0, 1⟩ := by
      intro he
      have hh := congrArg Zsqrtd.im he
      norm_num at hh
    have hneD : a + 1 ≠ a - ⟨0, 1⟩ := by
      intro he
      have hh := congrArg Zsqrtd.im he
      simp at hh
      omega
    simpa [hneU, hneD] using h
  · have h := GridHorizontalLogLiftDelta q a (a - 1) (by simp) L hL hexp
    have hneU : a - 1 ≠ a + ⟨0, 1⟩ := by
      intro he
      have hh := congrArg Zsqrtd.im he
      norm_num at hh
    have hneD : a - 1 ≠ a - ⟨0, 1⟩ := by
      intro he
      have hh := congrArg Zsqrtd.im he
      simp at hh
      omega
    simpa [hneU, hneD] using h
  · have h := GridVerticalUpLogLiftDelta q a L hL hexp
    have hneD : a + ⟨0, 1⟩ ≠ a - ⟨0, 1⟩ := by
      intro he
      have hh := congrArg Zsqrtd.im he
      simp at hh
      omega
    by_cases hc : a.im = q.im ∧ a.re ≤ q.re
    · simpa [hc, hneD] using h
    · simpa [hc, hneD] using h
  · have h := GridVerticalDownLogLiftDelta q a L hL hexp
    have hneU : a - ⟨0, 1⟩ ≠ a + ⟨0, 1⟩ := by
      intro he
      have hh := congrArg Zsqrtd.im he
      simp at hh
      omega
    rw [ite_eq_right (by intro hc; exact hneU hc.1)]
    simp only [true_and]
    by_cases hc : a.im - 1 = q.im ∧ a.re ≤ q.re
    · simp only [Icc.mk_one, Icc.mk_zero, Int.reduceNeg, map_sub, Zsqrtd.im_sub, hc, and_self,
        ↓reduceIte, Int.cast_neg, Int.cast_one, mul_neg, mul_one, sub_neg_eq_add] at h ⊢
      convert h using 1
    · simpa [hc] using h

end

end ApollonianSuperharmonic

end
