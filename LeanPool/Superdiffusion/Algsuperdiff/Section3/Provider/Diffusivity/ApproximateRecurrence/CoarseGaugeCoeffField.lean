/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Setup

/-!
# CoarseGaugeCoeffField

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: constant skew shifts of a coefficient field

Step 3 of `l.approximate.recurrence.formula` (ABK26) shifts the coefficient
field by the constant matrix `hbar`, the average of the fresh shell `k_m -
k_{m-h}` over the localization cube, and compensates by the doubled shear
`bfG_{-hbar}` of `e.Gh.def`.  The matrix `hbar` is skew because it is an
average of skew matrices.

This module supplies the *pointwise* half of that shift, at the carrier of
`Homogenization.Ambient.CoefficientField`:

* the two elementary consequences of skewness, `x . h x = 0` and
  `x . h y = - (h x) . y`;
* invariance of the symmetric part, `symmPart (A - h) = symmPart A`, together
  with its additive form.

Only linear algebra occurs here: neither the ellipticity transfer for the
shifted matrix nor the packaging of `a - hbar` as an object of
`Homogenization.Book.Ch02.CoeffOn` is carried out in this module.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport

variable {d : ℕ}

/-! ## Elementary consequences of skewness -/

/-- Pairing across a skew matrix is antisymmetric. -/
theorem vecDot_matVecMul_swap_of_transpose_eq_neg {H : Mat d}
    (hH : matTranspose H = -H) (x y : Vec d) :
    vecDot x (matVecMul H y) = -vecDot (matVecMul H x) y := by
  have h := vecDot_matVecMul_transpose x y H
  rw [hH, neg_matVecMul, vecDot_neg_right] at h
  linarith

/-- The quadratic form of a skew matrix vanishes. -/
theorem vecDot_matVecMul_self_eq_zero_of_transpose_eq_neg {H : Mat d}
    (hH : matTranspose H = -H) (x : Vec d) :
    vecDot x (matVecMul H x) = 0 := by
  have h := vecDot_matVecMul_swap_of_transpose_eq_neg hH x x
  rw [vecDot_comm (matVecMul H x) x] at h
  linarith

theorem vecDot_sub_left (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, sub_eq_add_neg]

theorem vecDot_sub_right (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, sub_eq_add_neg]

theorem matTranspose_neg (H : Mat d) : matTranspose (-H) = -matTranspose H := by
  ext i j
  simp [matTranspose]

/-- A constant skew summand does not change the symmetric part. -/
theorem symmPart_add_of_transpose_eq_neg {H : Mat d}
    (hH : matTranspose H = -H) (A : Mat d) :
    symmPart (A + H) = symmPart A := by
  ext i j
  have hij : H j i = -H i j := by
    have h := congrFun (congrFun hH i) j
    simpa [matTranspose, Matrix.transpose_apply] using h
  show ((A + H) i j + (A + H) j i) / 2 = (A i j + A j i) / 2
  simp only [Matrix.add_apply, hij]
  ring

/-- A constant skew subtrahend does not change the symmetric part. -/
theorem symmPart_sub_of_transpose_eq_neg {H : Mat d}
    (hH : matTranspose H = -H) (A : Mat d) :
    symmPart (A - H) = symmPart A := by
  have hneg : matTranspose (-H) = -(-H) := by
    rw [matTranspose_neg, hH]
  rw [sub_eq_add_neg]
  exact symmPart_add_of_transpose_eq_neg hneg A

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
