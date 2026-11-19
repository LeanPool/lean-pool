/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Coprime.Basic

/-!
# Coprimality along a remainder sequence

A candidate for `Mathlib.RingTheory.Coprime.Basic`, next to `isCoprime_mul_unit_left_right` and
`IsCoprime.add_mul_right_right_iff`: one step `a x = q y - b z` of a remainder sequence with units
`a` and `b` keeps coprimality (`isCoprime_iff_of_mul_eq_mul_sub_mul`), so that the last two elements
of such a sequence are coprime exactly when the first two are.
-/

@[expose] public section

/-- One step `a x = q y - b z` of a remainder sequence with units `a` and `b`, such as a step
`x = q y + z` of the Euclidean algorithm, with `a = 1` and `b = -1`, keeps coprimality. -/
theorem isCoprime_iff_of_mul_eq_mul_sub_mul {R : Type*} [CommRing R] {a b q x y z : R}
    (ha : IsUnit a) (hb : IsUnit b) (h : a * x = q * y - b * z) :
    IsCoprime y z ↔ IsCoprime x y := by
  have hz : b * z = -(a * x) + q * y := by rw [h, neg_sub, sub_add_cancel]
  rw [← isCoprime_mul_unit_left_right hb, hz, IsCoprime.add_mul_right_right_iff,
    IsCoprime.neg_right_iff, isCoprime_mul_unit_left_right ha, isCoprime_comm]

end
