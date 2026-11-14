/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Analysis.Complex.Basic
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity

/-!
# Distance between positive circles in a proper band quadruple

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
The shared proof converts the integral tangency identity to a Euclidean distance.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- The centers of two positive tangent band circles are separated by the sum of their radii. -/
theorem ProperBandCircleCenterDistance (v : Fin 4 → CircleCoordinates)
    (hv : ProperBandQuadruple v) (i k : Fin 4) (hik : i ≠ k)
    (hi : 0 < (v i).1) (hk : 0 < (v k).1) :
    dist (((v i).2 : Complex) / (v i).1) (((v k).2 : Complex) / (v k).1) =
      1 / ((v i).1 : Real) + 1 / ((v k).1 : Real) := by
  classical
  let w : GaussianInt := (v k).1 • (v i).2 - (v i).1 • (v k).2
  have ht := TangencyCoordinateIdentity v hv.1 i k hik
  have normCast (w : GaussianInt) :
      Complex.normSq (w : Complex) = (Zsqrtd.norm w : Real) := by
    simp [Complex.normSq, Zsqrtd.norm_def]
  have hn : Complex.normSq (w : Complex) =
      (((v i).1 + (v k).1 : ℤ)^2 : Real) := by
    change Complex.normSq
        (((v k).1 • (v i).2 - (v i).1 • (v k).2 : GaussianInt) : Complex) = _
    rw [normCast]
    exact_mod_cast ht
  have hnsq : ‖(w : Complex)‖ ^ 2 =
      (((v i).1 + (v k).1 : ℤ) : Real) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hn]
  have hnorm : ‖(w : Complex)‖ =
      (((v i).1 + (v k).1 : ℤ) : Real) := by
    have hnonneg := norm_nonneg (w : Complex)
    have hsum : 0 ≤ (((v i).1 + (v k).1 : ℤ) : Real) := by positivity
    nlinarith
  have hdiff :
      ((v i).2 : Complex) / (v i).1 - ((v k).2 : Complex) / (v k).1 =
        (w : Complex) / (((v i).1 * (v k).1 : ℤ) : Complex) := by
    dsimp [w]
    push_cast
    simp only [map_sub, map_zsmul]
    have hia : (v i).1 ≠ 0 := ne_of_gt hi
    have hkb : (v k).1 ≠ 0 := ne_of_gt hk
    field_simp [hia, hkb]
    ring
  rw [Complex.dist_eq, hdiff, Complex.norm_div, Complex.norm_intCast, hnorm]
  have ha : 0 < ((v i).1 : Real) := by exact_mod_cast hi
  have hb : 0 < ((v k).1 : Real) := by exact_mod_cast hk
  have hab : 0 < (((v i).1 * (v k).1 : ℤ) : Real) := by
    exact_mod_cast mul_pos hi hk
  rw [abs_of_pos hab]
  push_cast
  field_simp [ne_of_gt ha, ne_of_gt hb]
  ring

end ApollonianSuperharmonic

end
