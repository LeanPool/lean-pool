/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
Upstream FloatLib code retains its MIT license below. The Lean Pool integration changes are
covered by the standard header above.

MIT License

Copyright (c) 2026 FloatLib

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Analysis.DyadicOrder
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.ERealSemantics

/-!
# Correctness of binary comparisons

The format-parameterized executable comparison agrees with exact dyadic, real, and extended-real
order. The selection theorems also specify IEEE `minimum` and `maximum`, including infinities
and signed-zero tie breaking.

All results are uniform in the binary format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

section

/-! ## Classification helpers -/

/-- NaN selection returns `none` when both inputs are known not to be NaNs. -/
theorem chooseNaN2_none_of_not_isNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    chooseNaN2 x y = none :=
  (chooseNaN2_eq_none_iff x y).2 ⟨hx, hy⟩

/-- Exactly pairs containing a NaN produce the unordered comparison relation. -/
theorem compare_eq_none_iff {fmt : FloatFormat} (x y : Model fmt) :
    compare x y = none ↔ isNaN x = true ∨ isNaN y = true := by
  cases hx : isNaN x <;> cases hy : isNaN y <;> simp [compare, hx, hy]

/-- Without NaNs, `minNum` is exactly the ordinary IEEE `minimum` operation. -/
theorem minNum_eq_minimum_of_not_isNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    minNum x y = minimum x y := by
  have hxSNaN := isSNaN_eq_false_of_isNaN_eq_false x hx
  have hySNaN := isSNaN_eq_false_of_isNaN_eq_false y hy
  simp [minNum, hxSNaN, hySNaN, hx, hy]

/-- Without NaNs, `maxNum` is exactly the ordinary IEEE `maximum` operation. -/
theorem maxNum_eq_maximum_of_not_isNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    maxNum x y = maximum x y := by
  have hxSNaN := isSNaN_eq_false_of_isNaN_eq_false x hx
  have hySNaN := isSNaN_eq_false_of_isNaN_eq_false y hy
  simp [maxNum, hxSNaN, hySNaN, hx, hy]

/--
A signaling left operand has first priority in `minNum` and is returned after quieting.
-/
theorem minNum_of_isSNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSNaN x = true) :
    minNum x y = quietNaN x := by
  simp [minNum, hx]

/--
When the left operand is not signaling, a signaling right operand has priority in `minNum`.
-/
theorem minNum_of_isSNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSNaN x = false) (hy : isSNaN y = true) :
    minNum x y = quietNaN y := by
  simp [minNum, hx, hy]

/--
After signaling NaNs are excluded, `minNum` skips one quiet NaN on the left.
-/
theorem minNum_of_isNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hxSNaN : isSNaN x = false) (hySNaN : isSNaN y = false)
    (hxNaN : isNaN x = true) (hyNaN : isNaN y = false) :
    minNum x y = y := by
  simp [minNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
After signaling NaNs are excluded, `minNum` skips one quiet NaN on the right.
-/
theorem minNum_of_isNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hxSNaN : isSNaN x = false) (hySNaN : isSNaN y = false)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = true) :
    minNum x y = x := by
  simp [minNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
When both operands are quiet NaNs, `minNum` quiets and returns the left operand.
-/
theorem minNum_of_isNaN_both {fmt : FloatFormat} (x y : Model fmt)
    (hxSNaN : isSNaN x = false) (hySNaN : isSNaN y = false)
    (hxNaN : isNaN x = true) (hyNaN : isNaN y = true) :
    minNum x y = quietNaN x := by
  simp [minNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
A signaling left operand has first priority in `maxNum` and is returned after quieting.
-/
theorem maxNum_of_isSNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSNaN x = true) :
    maxNum x y = quietNaN x := by
  simp [maxNum, hx]

/--
When the left operand is not signaling, a signaling right operand has priority in `maxNum`.
-/
theorem maxNum_of_isSNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSNaN x = false) (hy : isSNaN y = true) :
    maxNum x y = quietNaN y := by
  simp [maxNum, hx, hy]

/--
After signaling NaNs are excluded, `maxNum` skips one quiet NaN on the left.
-/
theorem maxNum_of_isNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hxSNaN : isSNaN x = false) (hySNaN : isSNaN y = false)
    (hxNaN : isNaN x = true) (hyNaN : isNaN y = false) :
    maxNum x y = y := by
  simp [maxNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
After signaling NaNs are excluded, `maxNum` skips one quiet NaN on the right.
-/
theorem maxNum_of_isNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hxSNaN : isSNaN x = false) (hySNaN : isSNaN y = false)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = true) :
    maxNum x y = x := by
  simp [maxNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
When both operands are quiet NaNs, `maxNum` quiets and returns the left operand.
-/
theorem maxNum_of_isNaN_both {fmt : FloatFormat} (x y : Model fmt)
    (hxSNaN : isSNaN x = false) (hySNaN : isSNaN y = false)
    (hxNaN : isNaN x = true) (hyNaN : isNaN y = true) :
    maxNum x y = quietNaN x := by
  simp [maxNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/-! ### IEEE 754-2019 `minimumNumber` and `maximumNumber` -/

/-- Without NaNs, `minimumNumber` is exactly the IEEE `minimum` operation. -/
theorem minimumNumber_eq_minimum_of_not_isNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    minimumNumber x y = minimum x y := by
  simp [minimumNumber, hx, hy]

/-- Without NaNs, `maximumNumber` is exactly the IEEE `maximum` operation. -/
theorem maximumNumber_eq_maximum_of_not_isNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    maximumNumber x y = maximum x y := by
  simp [maximumNumber, hx, hy]

/--
`minimumNumber` returns the right operand whenever only the left operand is a NaN, even a
signaling one. This is the point where IEEE 754-2019 departs from `minNum`.
-/
theorem minimumNumber_of_isNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = true) (hy : isNaN y = false) :
    minimumNumber x y = y := by
  simp [minimumNumber, hx, hy]

/-- `minimumNumber` returns the left operand whenever only the right operand is a NaN. -/
theorem minimumNumber_of_isNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = true) :
    minimumNumber x y = x := by
  simp [minimumNumber, hx, hy]

/-- When both operands are NaNs, `minimumNumber` delivers the quiet NaN chosen by
  `bothNaNNumber`. -/
theorem minimumNumber_of_isNaN_both {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = true) (hy : isNaN y = true) :
    minimumNumber x y = bothNaNNumber x y := by
  simp [minimumNumber, hx, hy]

/-- `maximumNumber` returns the right operand whenever only the left operand is a NaN. -/
theorem maximumNumber_of_isNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = true) (hy : isNaN y = false) :
    maximumNumber x y = y := by
  simp [maximumNumber, hx, hy]

/-- `maximumNumber` returns the left operand whenever only the right operand is a NaN. -/
theorem maximumNumber_of_isNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = true) :
    maximumNumber x y = x := by
  simp [maximumNumber, hx, hy]

/-- When both operands are NaNs, `maximumNumber` delivers the quiet NaN chosen by
  `bothNaNNumber`. -/
theorem maximumNumber_of_isNaN_both {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = true) (hy : isNaN y = true) :
    maximumNumber x y = bothNaNNumber x y := by
  simp [maximumNumber, hx, hy]

/-- The NaN chosen for two NaN operands is always one of them, quieted. -/
theorem bothNaNNumber_eq_or {fmt : FloatFormat} (x y : Model fmt) :
    bothNaNNumber x y = quietNaN x ∨ bothNaNNumber x y = quietNaN y := by
  unfold bothNaNNumber
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/--
When neither operand is a signaling NaN, `minimumNumber` agrees with `minNum`, including when
one or both operands are quiet NaNs.
-/
theorem minimumNumber_eq_minNum_of_not_isSNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSNaN x = false) (hy : isSNaN y = false) :
    minimumNumber x y = minNum x y := by
  cases hxNaN : isNaN x <;> cases hyNaN : isNaN y <;>
    simp [minimumNumber, minNum, bothNaNNumber, hx, hy, hxNaN, hyNaN]

/-- The `maximumNumber` counterpart of `minimumNumber_eq_minNum_of_not_isSNaN`. -/
theorem maximumNumber_eq_maxNum_of_not_isSNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSNaN x = false) (hy : isSNaN y = false) :
    maximumNumber x y = maxNum x y := by
  cases hxNaN : isNaN x <;> cases hyNaN : isNaN y <;>
    simp [maximumNumber, maxNum, bothNaNNumber, hx, hy, hxNaN, hyNaN]

/-- The real interpretation erases the sign of an executable zero. -/
theorem toReal_eq_zero_of_isZero {fmt : FloatFormat} (x : Model fmt)
    (hx : isZero x = true) :
    toReal x = 0 := by
  rw [toReal_eq, toDyadicOption_eq_zero_of_isZero_eq_true x hx]
  simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]

/-! ## Non-NaN minimum and maximum -/

/-- IEEE `minimum` is non-NaN when both operands are non-NaN. -/
theorem isNaN_minimum_eq_false_of_isNaN_eq_false
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    isNaN (minimum x y) = false := by
  have hchoose := chooseNaN2_none_of_not_isNaN x y hxNaN hyNaN
  simp only [minimum, withNaNSelection_of_none _ _ hchoose]
  cases compareNonNaN x y hxNaN hyNaN <;>
    simp [apply_ite, hxNaN, hyNaN]

/-- IEEE `maximum` is non-NaN when both operands are non-NaN. -/
theorem isNaN_maximum_eq_false_of_isNaN_eq_false
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    isNaN (maximum x y) = false := by
  have hchoose := chooseNaN2_none_of_not_isNaN x y hxNaN hyNaN
  simp only [maximum, withNaNSelection_of_none _ _ hchoose]
  cases compareNonNaN x y hxNaN hyNaN <;>
    simp [apply_ite, hxNaN, hyNaN]

/-- `minimumNumber` never returns a NaN unless both operands are NaNs. -/
theorem isNaN_minimumNumber_eq_false_of_not_both
    {fmt : FloatFormat} (x y : Model fmt)
    (h : isNaN x = false ∨ isNaN y = false) :
    isNaN (minimumNumber x y) = false := by
  cases hx : isNaN x <;> cases hy : isNaN y <;>
    simp_all [minimumNumber, isNaN_minimum_eq_false_of_isNaN_eq_false]

/-- `maximumNumber` never returns a NaN unless both operands are NaNs. -/
theorem isNaN_maximumNumber_eq_false_of_not_both
    {fmt : FloatFormat} (x y : Model fmt)
    (h : isNaN x = false ∨ isNaN y = false) :
    isNaN (maximumNumber x y) = false := by
  cases hx : isNaN x <;> cases hy : isNaN y <;>
    simp_all [maximumNumber, isNaN_maximum_eq_false_of_isNaN_eq_false]

/-! ## Finite comparison -/

/--
Once both operands are known not to be NaNs, the public comparison is exactly the total
non-NaN comparison.
-/
theorem compare_eq_some_compareNonNaN
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    compare x y = some (compareNonNaN x y hx hy) := by
  simp [compare, hx, hy]

/--
Any successful public comparison determines the result of the total non-NaN comparison.

This is the proof bridge used by the min/max semantics below: runtime code does not need an
unreachable unordered branch once NaNs have already been excluded.
-/
@[simp] theorem compareNonNaN_eq_of_compare_eq_some
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) {order : Ordering}
    (hcompare : compare x y = some order) :
    compareNonNaN x y hx hy = order := by
  simpa [compare, hx, hy] using hcompare

/--
When both operands decode to dyadics, executable comparison returns their exact dyadic ordering.
-/
theorem compare_eq_some_cmpDyadic_of_toDyadicOption
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadicOption x = some dx) (hy : toDyadicOption y = some dy) :
    compare x y = some (cmpDyadic dx dy) := by
  have hxNaN := isNaN_eq_false_of_toDyadicOption_some hx
  have hyNaN := isNaN_eq_false_of_toDyadicOption_some hy
  have hxInf := isInf_eq_false_of_toDyadicOption_some hx
  have hyInf := isInf_eq_false_of_toDyadicOption_some hy
  simp [compare, compareNonNaN, hxNaN, hyNaN, hxInf, hyInf, hx, hy]

/-- Finite executable comparison returns `.lt` exactly when the decoded reals are ordered. -/
theorem compare_eq_some_lt_iff_toReal_lt
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadicOption x = some dx) (hy : toDyadicOption y = some dy) :
    compare x y = some .lt ↔ toReal x < toReal y := by
  have hcompare :=
    compare_eq_some_cmpDyadic_of_toDyadicOption x y hx hy
  have hxReal : toReal x = dx.toReal := by
    simp [toReal_eq, hx]
  have hyReal : toReal y = dy.toReal := by
    simp [toReal_eq, hy]
  simpa [hcompare, hxReal, hyReal] using cmpDyadic_lt_iff dx dy

/-- Finite executable comparison returns `.eq` exactly when the decoded reals are equal. -/
theorem compare_eq_some_eq_iff_toReal_eq
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadicOption x = some dx) (hy : toDyadicOption y = some dy) :
    compare x y = some .eq ↔ toReal x = toReal y := by
  have hcompare :=
    compare_eq_some_cmpDyadic_of_toDyadicOption x y hx hy
  have hxReal : toReal x = dx.toReal := by
    simp [toReal_eq, hx]
  have hyReal : toReal y = dy.toReal := by
    simp [toReal_eq, hy]
  simpa [hcompare, hxReal, hyReal] using cmpDyadic_eq_iff dx dy

/-- Finite executable comparison returns `.gt` exactly when the decoded reals are reversed. -/
theorem compare_eq_some_gt_iff_toReal_gt
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadicOption x = some dx) (hy : toDyadicOption y = some dy) :
    compare x y = some .gt ↔ toReal y < toReal x := by
  have hcompare :=
    compare_eq_some_cmpDyadic_of_toDyadicOption x y hx hy
  have hxReal : toReal x = dx.toReal := by
    simp [toReal_eq, hx]
  have hyReal : toReal y = dy.toReal := by
    simp [toReal_eq, hy]
  simpa [hcompare, hxReal, hyReal] using cmpDyadic_gt_iff dx dy

/-- On finite inputs, executable comparison agrees with strict real order. -/
theorem compare_eq_some_lt_iff_toReal_lt_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    compare x y = some .lt ↔ toReal x < toReal y := by
  obtain ⟨dx, hdx⟩ := exists_toDyadicOption_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadicOption_of_isFinite hy
  exact compare_eq_some_lt_iff_toReal_lt x y hdx hdy

/-- On finite inputs, executable comparison agrees with real equality. -/
theorem compare_eq_some_eq_iff_toReal_eq_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    compare x y = some .eq ↔ toReal x = toReal y := by
  obtain ⟨dx, hdx⟩ := exists_toDyadicOption_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadicOption_of_isFinite hy
  exact compare_eq_some_eq_iff_toReal_eq x y hdx hdy

/-- On finite inputs, executable comparison agrees with reversed strict real order. -/
theorem compare_eq_some_gt_iff_toReal_gt_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    compare x y = some .gt ↔ toReal y < toReal x := by
  obtain ⟨dx, hdx⟩ := exists_toDyadicOption_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadicOption_of_isFinite hy
  exact compare_eq_some_gt_iff_toReal_gt x y hdx hdy

/-! ## Signed-zero tie breaking -/

/-- Positive and policy-selected negative zero compare equal numerically. -/
@[simp] theorem compare_zero_false_true (fmt : FloatFormat) :
    compare (zero fmt false) (zero fmt true) = some .eq := by
  rw [compare_eq_some_cmpDyadic_of_toDyadicOption
    (zero fmt false) (zero fmt true)
    (toDyadicOption_zero fmt false) (toDyadicOption_zero fmt true)]
  simp [cmpDyadic]

/--
`minimum` selects policy-negative zero from a positive-zero/negative-zero tie.

In a format without signed zero, both inputs and the result are the single positive zero.
-/
@[simp] theorem minimum_zero_false_true (fmt : FloatFormat) :
    minimum (zero fmt false) (zero fmt true) = zero fmt true := by
  have hchoose :=
    chooseNaN2_none_of_not_isNaN
      (zero fmt false) (zero fmt true)
      (isNaN_zero fmt false) (isNaN_zero fmt true)
  simp [minimum, hchoose, compare_zero_false_true, signBit_zero]
  cases hfmt : fmt.supportsSignedZero <;> simp [zero, hfmt]

/--
`maximum` selects positive zero from a positive-zero/negative-zero tie.

In a format without signed zero, both inputs already denote the single positive zero.
-/
@[simp] theorem maximum_zero_false_true (fmt : FloatFormat) :
    maximum (zero fmt false) (zero fmt true) = zero fmt false := by
  have hchoose :=
    chooseNaN2_none_of_not_isNaN
      (zero fmt false) (zero fmt true)
      (isNaN_zero fmt false) (isNaN_zero fmt true)
  simp [maximum, hchoose, compare_zero_false_true, signBit_zero]

/--
For every encoding with signed zero, `minimum (+0, -0)` returns the negative zero encoding.
-/
@[simp] theorem minimum_posZero_negZero_of_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    minimum (posZero fmt) (negZero fmt) = negZero fmt := by
  rw [← show zero fmt false = posZero fmt by simp [zero],
    ← show zero fmt true = negZero fmt by simp [zero, hfmt],
    minimum_zero_false_true]

/--
For every encoding with signed zero, `maximum (+0, -0)` returns the positive zero encoding.
-/
@[simp] theorem maximum_posZero_negZero_of_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    maximum (posZero fmt) (negZero fmt) = posZero fmt := by
  rw [← show zero fmt false = posZero fmt by simp [zero],
    ← show zero fmt true = negZero fmt by simp [zero, hfmt],
    maximum_zero_false_true]

/--
For every encoding with signed zero, `minNum (+0, -0)` returns the negative zero encoding.
-/
@[simp] theorem minNum_posZero_negZero_of_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    minNum (posZero fmt) (negZero fmt) = negZero fmt := by
  rw [minNum_eq_minimum_of_not_isNaN _ _ (isNaN_posZero fmt) (isNaN_negZero fmt hfmt),
    minimum_posZero_negZero_of_supportsSignedZero fmt hfmt]

/--
For every encoding with signed zero, `maxNum (+0, -0)` returns the positive zero encoding.
-/
@[simp] theorem maxNum_posZero_negZero_of_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    maxNum (posZero fmt) (negZero fmt) = posZero fmt := by
  rw [maxNum_eq_maximum_of_not_isNaN _ _ (isNaN_posZero fmt) (isNaN_negZero fmt hfmt),
    maximum_posZero_negZero_of_supportsSignedZero fmt hfmt]

/--
For every encoding with signed zero, `minimumNumber (+0, -0)` returns the negative zero encoding.
-/
@[simp] theorem minimumNumber_posZero_negZero_of_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    minimumNumber (posZero fmt) (negZero fmt) = negZero fmt := by
  rw [minimumNumber_eq_minimum_of_not_isNaN _ _ (isNaN_posZero fmt) (isNaN_negZero fmt hfmt),
    minimum_posZero_negZero_of_supportsSignedZero fmt hfmt]

/--
For every encoding with signed zero, `maximumNumber (+0, -0)` returns the positive zero encoding.
-/
@[simp] theorem maximumNumber_posZero_negZero_of_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    maximumNumber (posZero fmt) (negZero fmt) = posZero fmt := by
  rw [maximumNumber_eq_maximum_of_not_isNaN _ _ (isNaN_posZero fmt) (isNaN_negZero fmt hfmt),
    maximum_posZero_negZero_of_supportsSignedZero fmt hfmt]

/-! ## Finite minimum and maximum -/

/-- On finite inputs, IEEE `minimum` agrees with real `min`. -/
theorem toReal_minimum_eq_min
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadicOption x = some dx) (hy : toDyadicOption y = some dy) :
    toReal (minimum x y) = min (toReal x) (toReal y) := by
  have hxNaN := isNaN_eq_false_of_toDyadicOption_some hx
  have hyNaN := isNaN_eq_false_of_toDyadicOption_some hy
  have hchoose := chooseNaN2_none_of_not_isNaN x y hxNaN hyNaN
  have hcompare :=
    compare_eq_some_cmpDyadic_of_toDyadicOption x y hx hy
  cases horder : cmpDyadic dx dy with
  | lt =>
      have hcompare' : compare x y = some .lt := by
        simpa [horder] using hcompare
      have hlt : toReal x < toReal y :=
        (compare_eq_some_lt_iff_toReal_lt x y hx hy).mp hcompare'
      calc
        toReal (minimum x y) = toReal x := by
          simp [minimum, hchoose, hcompare']
        _ = min (toReal x) (toReal y) := (min_eq_left hlt.le).symm
  | eq =>
      have hcompare' : compare x y = some .eq := by
        simpa [horder] using hcompare
      have heq : toReal x = toReal y :=
        (compare_eq_some_eq_iff_toReal_eq x y hx hy).mp hcompare'
      cases hzeros : isZero x && isZero y with
      | false =>
          calc
            toReal (minimum x y) = toReal x := by
              simp [minimum, hchoose, hcompare', hzeros]
            _ = min (toReal x) (toReal y) := (min_eq_left heq.le).symm
      | true =>
          have hzeroParts : isZero x = true ∧ isZero y = true := by
            simpa [Bool.and_eq_true] using hzeros
          have hxZero := toReal_eq_zero_of_isZero x hzeroParts.1
          have hyZero := toReal_eq_zero_of_isZero y hzeroParts.2
          calc
            toReal (minimum x y) = 0 := by
              cases hsign : signBit x || signBit y <;>
                simp [minimum, hchoose, hcompare', hzeros, hsign]
            _ = min (toReal x) (toReal y) := by
              simp [hxZero, hyZero]
  | gt =>
      have hcompare' : compare x y = some .gt := by
        simpa [horder] using hcompare
      have hlt : toReal y < toReal x :=
        (compare_eq_some_gt_iff_toReal_gt x y hx hy).mp hcompare'
      calc
        toReal (minimum x y) = toReal y := by
          simp [minimum, hchoose, hcompare']
        _ = min (toReal x) (toReal y) := (min_eq_right hlt.le).symm

/-- On finite inputs, IEEE `maximum` agrees with real `max`. -/
theorem toReal_maximum_eq_max
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadicOption x = some dx) (hy : toDyadicOption y = some dy) :
    toReal (maximum x y) = max (toReal x) (toReal y) := by
  have hxNaN := isNaN_eq_false_of_toDyadicOption_some hx
  have hyNaN := isNaN_eq_false_of_toDyadicOption_some hy
  have hchoose := chooseNaN2_none_of_not_isNaN x y hxNaN hyNaN
  have hcompare :=
    compare_eq_some_cmpDyadic_of_toDyadicOption x y hx hy
  cases horder : cmpDyadic dx dy with
  | lt =>
      have hcompare' : compare x y = some .lt := by
        simpa [horder] using hcompare
      have hlt : toReal x < toReal y :=
        (compare_eq_some_lt_iff_toReal_lt x y hx hy).mp hcompare'
      calc
        toReal (maximum x y) = toReal y := by
          simp [maximum, hchoose, hcompare']
        _ = max (toReal x) (toReal y) := (max_eq_right hlt.le).symm
  | eq =>
      have hcompare' : compare x y = some .eq := by
        simpa [horder] using hcompare
      have heq : toReal x = toReal y :=
        (compare_eq_some_eq_iff_toReal_eq x y hx hy).mp hcompare'
      cases hzeros : isZero x && isZero y with
      | false =>
          calc
            toReal (maximum x y) = toReal x := by
              simp [maximum, hchoose, hcompare', hzeros]
            _ = max (toReal x) (toReal y) := (max_eq_left heq.ge).symm
      | true =>
          have hzeroParts : isZero x = true ∧ isZero y = true := by
            simpa [Bool.and_eq_true] using hzeros
          have hxZero := toReal_eq_zero_of_isZero x hzeroParts.1
          have hyZero := toReal_eq_zero_of_isZero y hzeroParts.2
          calc
            toReal (maximum x y) = 0 := by
              cases hsign : (!signBit x) || (!signBit y) <;>
                simp [maximum, hchoose, hcompare', hzeros]
            _ = max (toReal x) (toReal y) := by
              simp [hxZero, hyZero]
  | gt =>
      have hcompare' : compare x y = some .gt := by
        simpa [horder] using hcompare
      have hlt : toReal y < toReal x :=
        (compare_eq_some_gt_iff_toReal_gt x y hx hy).mp hcompare'
      calc
        toReal (maximum x y) = toReal x := by
          simp [maximum, hchoose, hcompare']
        _ = max (toReal x) (toReal y) := (max_eq_left hlt.le).symm

/-- On finite inputs, IEEE `minimum` agrees with real `min`. -/
theorem toReal_minimum_eq_min_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    toReal (minimum x y) = min (toReal x) (toReal y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadicOption_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadicOption_of_isFinite hy
  exact toReal_minimum_eq_min x y hdx hdy

/-- On finite inputs, IEEE `maximum` agrees with real `max`. -/
theorem toReal_maximum_eq_max_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    toReal (maximum x y) = max (toReal x) (toReal y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadicOption_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadicOption_of_isFinite hy
  exact toReal_maximum_eq_max x y hdx hdy

/-! ## Extended-real comparison -/

/-- Every non-NaN executable value has a partial extended-real interpretation. -/
theorem exists_toERealOption_of_isNaN_eq_false
    {fmt : FloatFormat} (x : Model fmt) (hx : isNaN x = false) :
    ∃ value, toERealOption x = some value := by
  cases hinf : isInf x <;> simp [toERealOption, hx, hinf]

/--
Every successful extended-real interpretation is either a signed infinity or a finite real value.
-/
theorem toERealOption_cases
    {fmt : FloatFormat} (x : Model fmt) {value : EReal}
    (hx : toERealOption x = some value) :
    (isInf x = true ∧
        value = if signBit x then (⊥ : EReal) else (⊤ : EReal)) ∨
      (isFinite x = true ∧ value = (toReal x : EReal)) := by
  by_cases hinf : isInf x = true
  · left
    refine ⟨hinf, ?_⟩
    have hnan := isNaN_eq_false_of_isInf_eq_true x hinf
    unfold toERealOption at hx
    rw [hnan, hinf] at hx
    simpa using hx.symm
  · right
    have hinfFalse : isInf x = false := by
      simpa using hinf
    have hnan : isNaN x = false := by
      by_contra h
      simp only [Bool.not_eq_false] at h
      unfold toERealOption at hx
      rw [h] at hx
      simp at hx
    have hfinite :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnan hinfFalse
    refine ⟨hfinite, ?_⟩
    unfold toERealOption at hx
    rw [hnan, hinfFalse] at hx
    simpa using hx.symm

/-- A non-NaN comparison returns the ordering of its exact extended-real values. -/
theorem compare_eq_of_toERealOption {fmt : FloatFormat} {x y : Model fmt} {a b : EReal}
    (hx : toERealOption x = some a) (hy : toERealOption y = some b) :
    compare x y = some (Ord.compare a b) := by
  classical
  symm
  rcases toERealOption_cases x hx with ⟨hxInf, rfl⟩ | ⟨hxFin, rfl⟩ <;>
    rcases toERealOption_cases y hy with ⟨hyInf, rfl⟩ | ⟨hyFin, rfl⟩
  · have hxNaN := isNaN_eq_false_of_isInf_eq_true x hxInf
    have hyNaN := isNaN_eq_false_of_isInf_eq_true y hyInf
    cases hxSign : signBit x <;> cases hySign : signBit y <;>
      simp [compare, compareNonNaN, hxNaN, hyNaN, hxInf, hyInf, hxSign, hySign,
        compare_lt_iff_lt, compare_gt_iff_gt]
  · have hxNaN := isNaN_eq_false_of_isInf_eq_true x hxInf
    have hyNaN := isNaN_eq_false_of_isFinite_eq_true y hyFin
    have hyInf := isInf_eq_false_of_isFinite_eq_true y hyFin
    cases hxSign : signBit x <;>
      simp [compare, compareNonNaN, hxNaN, hyNaN, hxInf, hyInf, hxSign,
        compare_lt_iff_lt, compare_gt_iff_gt]
  · have hxNaN := isNaN_eq_false_of_isFinite_eq_true x hxFin
    have hyNaN := isNaN_eq_false_of_isInf_eq_true y hyInf
    have hxInf := isInf_eq_false_of_isFinite_eq_true x hxFin
    cases hySign : signBit y <;>
      simp [compare, compareNonNaN, hxNaN, hyNaN, hxInf, hyInf, hySign,
        compare_lt_iff_lt, compare_gt_iff_gt]
  · rcases lt_trichotomy (toReal x) (toReal y) with h | h | h
    · rw [(compare_eq_some_lt_iff_toReal_lt_of_isFinite x y hxFin hyFin).2 h]
      simp [compare_lt_iff_lt, h]
    · rw [(compare_eq_some_eq_iff_toReal_eq_of_isFinite x y hxFin hyFin).2 h, h]
      simp
    · rw [(compare_eq_some_gt_iff_toReal_gt_of_isFinite x y hxFin hyFin).2 h]
      simp [compare_gt_iff_gt, h]

/-- Non-NaN executable comparison agrees with strict extended-real order. -/
theorem compare_eq_some_lt_iff_toEReal_lt
    {fmt : FloatFormat} {x y : Model fmt} {ex ey : EReal}
    (hx : toERealOption x = some ex) (hy : toERealOption y = some ey) :
    compare x y = some .lt ↔ ex < ey := by
  rw [compare_eq_of_toERealOption hx hy, Option.some.injEq, compare_lt_iff_lt]

/-- Non-NaN executable comparison agrees with extended-real equality. -/
theorem compare_eq_some_eq_iff_toEReal_eq
    {fmt : FloatFormat} {x y : Model fmt} {ex ey : EReal}
    (hx : toERealOption x = some ex) (hy : toERealOption y = some ey) :
    compare x y = some .eq ↔ ex = ey := by
  rw [compare_eq_of_toERealOption hx hy, Option.some.injEq, compare_eq_iff_eq]

/-- Every non-NaN value compares equal to itself. -/
theorem compare_self_of_isNaN_eq_false {fmt : FloatFormat}
    (x : Model fmt) (h : isNaN x = false) :
    compare x x = some .eq := by
  obtain ⟨value, hx⟩ := exists_toERealOption_of_isNaN_eq_false x h
  exact (compare_eq_some_eq_iff_toEReal_eq hx hx).2 rfl

/-- Non-NaN executable comparison agrees with reversed strict extended-real order. -/
theorem compare_eq_some_gt_iff_toEReal_gt
    {fmt : FloatFormat} {x y : Model fmt} {ex ey : EReal}
    (hx : toERealOption x = some ex) (hy : toERealOption y = some ey) :
    compare x y = some .gt ↔ ey < ex := by
  rw [compare_eq_of_toERealOption hx hy, Option.some.injEq, compare_gt_iff_gt]

/-! ## Extended-real minimum and maximum -/

/-- The total extended-real interpretation erases the sign of an executable zero. -/
theorem toEReal_eq_zero_of_isZero
    {fmt : FloatFormat} (x : Model fmt) (hx : isZero x = true) :
    toEReal x = 0 := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true x hx
  rw [toEReal_eq_coe_toReal_of_isFinite x hfinite,
    toReal_eq_zero_of_isZero x hx]
  simp

/-- IEEE `minimum` agrees with `min` on every pair of non-NaN extended-real values. -/
theorem toEReal_minimum_eq_min
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (minimum x y) = min (toEReal x) (toEReal y) := by
  obtain ⟨ex, hx⟩ := exists_toERealOption_of_isNaN_eq_false x hxNaN
  obtain ⟨ey, hy⟩ := exists_toERealOption_of_isNaN_eq_false y hyNaN
  have hxTotal : toEReal x = ex := toEReal_of_toERealOption hx
  have hyTotal : toEReal y = ey := toEReal_of_toERealOption hy
  have hchoose := chooseNaN2_none_of_not_isNaN x y hxNaN hyNaN
  rcases lt_trichotomy ex ey with hlt | heq | hgt
  · have hcompare :=
      (compare_eq_some_lt_iff_toEReal_lt hx hy).mpr hlt
    simp [minimum, hchoose, hcompare, hxTotal, hyTotal, min_eq_left hlt.le]
  · have hcompare :=
      (compare_eq_some_eq_iff_toEReal_eq hx hy).mpr heq
    cases hzeros : isZero x && isZero y with
    | false =>
        simp [minimum, hchoose, hcompare, hzeros, hxTotal, hyTotal,
          min_eq_left heq.le]
    | true =>
        have hzeroParts : isZero x = true ∧ isZero y = true := by
          simpa [Bool.and_eq_true] using hzeros
        have hxZero := toEReal_eq_zero_of_isZero x hzeroParts.1
        have hyZero := toEReal_eq_zero_of_isZero y hzeroParts.2
        calc
          toEReal (minimum x y) = 0 := by
            by_cases hsign : signBit x = true ∨ signBit y = true
            · simp [minimum, hchoose, hcompare, hzeros]
            · simp [minimum, hchoose, hcompare, hzeros]
          _ = min (toEReal x) (toEReal y) := by
            simp [hxZero, hyZero]
  · have hcompare :=
      (compare_eq_some_gt_iff_toEReal_gt hx hy).mpr hgt
    simp [minimum, hchoose, hcompare, hxTotal, hyTotal, min_eq_right hgt.le]

/-- IEEE `maximum` agrees with `max` on every pair of non-NaN extended-real values. -/
theorem toEReal_maximum_eq_max
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (maximum x y) = max (toEReal x) (toEReal y) := by
  obtain ⟨ex, hx⟩ := exists_toERealOption_of_isNaN_eq_false x hxNaN
  obtain ⟨ey, hy⟩ := exists_toERealOption_of_isNaN_eq_false y hyNaN
  have hxTotal : toEReal x = ex := toEReal_of_toERealOption hx
  have hyTotal : toEReal y = ey := toEReal_of_toERealOption hy
  have hchoose := chooseNaN2_none_of_not_isNaN x y hxNaN hyNaN
  rcases lt_trichotomy ex ey with hlt | heq | hgt
  · have hcompare :=
      (compare_eq_some_lt_iff_toEReal_lt hx hy).mpr hlt
    simp [maximum, hchoose, hcompare, hxTotal, hyTotal, max_eq_right hlt.le]
  · have hcompare :=
      (compare_eq_some_eq_iff_toEReal_eq hx hy).mpr heq
    cases hzeros : isZero x && isZero y with
    | false =>
        simp [maximum, hchoose, hcompare, hzeros, hxTotal, hyTotal,
          max_eq_left heq.ge]
    | true =>
        have hzeroParts : isZero x = true ∧ isZero y = true := by
          simpa [Bool.and_eq_true] using hzeros
        have hxZero := toEReal_eq_zero_of_isZero x hzeroParts.1
        have hyZero := toEReal_eq_zero_of_isZero y hzeroParts.2
        calc
          toEReal (maximum x y) = 0 := by
            by_cases hsign : signBit x = false ∨ signBit y = false
            · simp [maximum, hchoose, hcompare, hzeros]
            · simp [maximum, hchoose, hcompare, hzeros]
          _ = max (toEReal x) (toEReal y) := by
            simp [hxZero, hyZero]
  · have hcompare :=
      (compare_eq_some_gt_iff_toEReal_gt hx hy).mpr hgt
    simp [maximum, hchoose, hcompare, hxTotal, hyTotal, max_eq_left hgt.le]

/--
On non-NaN values, `minNum` has the exact extended-real semantics of mathematical minimum.
Signed-zero tie breaking remains visible in the encoded result even though `toEReal` identifies
the two zeros.
-/
theorem toEReal_minNum_eq_min
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (minNum x y) = min (toEReal x) (toEReal y) := by
  rw [minNum_eq_minimum_of_not_isNaN x y hxNaN hyNaN]
  exact toEReal_minimum_eq_min x y hxNaN hyNaN

/--
On non-NaN values, `maxNum` has the exact extended-real semantics of mathematical maximum.
Signed-zero tie breaking remains visible in the encoded result even though `toEReal` identifies
the two zeros.
-/
theorem toEReal_maxNum_eq_max
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (maxNum x y) = max (toEReal x) (toEReal y) := by
  rw [maxNum_eq_maximum_of_not_isNaN x y hxNaN hyNaN]
  exact toEReal_maximum_eq_max x y hxNaN hyNaN

/-- On non-NaN values, `minimumNumber` has the extended-real semantics of mathematical minimum. -/
theorem toEReal_minimumNumber_eq_min
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (minimumNumber x y) = min (toEReal x) (toEReal y) := by
  rw [minimumNumber_eq_minimum_of_not_isNaN x y hxNaN hyNaN]
  exact toEReal_minimum_eq_min x y hxNaN hyNaN

/-- On non-NaN values, `maximumNumber` has the extended-real semantics of mathematical maximum. -/
theorem toEReal_maximumNumber_eq_max
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (maximumNumber x y) = max (toEReal x) (toEReal y) := by
  rw [maximumNumber_eq_maximum_of_not_isNaN x y hxNaN hyNaN]
  exact toEReal_maximum_eq_max x y hxNaN hyNaN

/--
`minimumNumber` is commutative up to extended-real value on non-NaN operands. This interpretation
identifies the two signed zeros.
-/
theorem toEReal_minimumNumber_comm
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (minimumNumber x y) = toEReal (minimumNumber y x) := by
  rw [toEReal_minimumNumber_eq_min x y hxNaN hyNaN,
    toEReal_minimumNumber_eq_min y x hyNaN hxNaN, min_comm]

/-- The `maximumNumber` counterpart of `toEReal_minimumNumber_comm`. -/
theorem toEReal_maximumNumber_comm
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (maximumNumber x y) = toEReal (maximumNumber y x) := by
  rw [toEReal_maximumNumber_eq_max x y hxNaN hyNaN,
    toEReal_maximumNumber_eq_max y x hyNaN hxNaN, max_comm]

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
