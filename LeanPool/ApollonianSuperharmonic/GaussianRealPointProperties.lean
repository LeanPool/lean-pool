/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import Mathlib.Init


/-!
# GaussianRealPointProperties

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace GaussianRealPointProperties

/-- Shared add identity for GaussianRealPointProperties. -/
theorem add :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt), GaussianRealPoint (x + y) = GaussianRealPoint x
            + GaussianRealPoint y ) := by
  classical
  intro x y
  ext <;> simp [GaussianRealPoint]

/-- Shared negation identity for GaussianRealPointProperties. -/
theorem negation :
    (by
      classical
      exact
        ∀ (z : GaussianInt), GaussianRealPoint (-z) = -GaussianRealPoint z ) := by
  classical
  intro z
  ext <;> simp [GaussianRealPoint]

/-- Shared injective identity for GaussianRealPointProperties. -/
theorem injective :
    (by
      classical
      exact
        Function.Injective GaussianRealPoint ) := by
  classical
  intro x y hxy
  apply Zsqrtd.ext
  · have h := congrArg Prod.fst hxy
    dsimp [GaussianRealPoint] at h
    exact_mod_cast h
  · have h := congrArg Prod.snd hxy
    dsimp [GaussianRealPoint] at h
    exact_mod_cast h

/-- The Gaussian embedding preserves subtraction. -/
theorem sub (x y : GaussianInt) :
    GaussianRealPoint (x - y) = GaussianRealPoint x - GaussianRealPoint y := by
  rw [sub_eq_add_neg, add, negation, sub_eq_add_neg]

/-- Scalar multiples of the Gaussian embedding preserve differences. -/
theorem scaledSub (c : ℝ) (x y : GaussianInt) :
    c • GaussianRealPoint x - c • GaussianRealPoint y =
      c • GaussianRealPoint (x - y) := by
  rw [sub, smul_sub]

/-- Differences of coordinates relative to a common origin cancel that origin. -/
theorem relativeDifference {A B C : ℝ × ℝ} {X Y Z : GaussianInt} (c : ℝ)
    (ha : A - C = c • GaussianRealPoint X)
    (hb : B - C = c • GaussianRealPoint Y)
    (hxy : X - Y = Z) : A - B = c • GaussianRealPoint Z := by
  calc
    _ = (A - C) - (B - C) := (sub_sub_sub_cancel_right A B C).symm
    _ = c • GaussianRealPoint (X - Y) := by rw [ha, hb, scaledSub]
    _ = _ := by rw [hxy]

end GaussianRealPointProperties
end ApollonianSuperharmonic

end
