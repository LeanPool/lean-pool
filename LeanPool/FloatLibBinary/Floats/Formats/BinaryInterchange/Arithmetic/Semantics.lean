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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.Finiteness
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Proof

/-!
# Correctness of IEEE binary arithmetic

The executable operations in `Model` first decode finite operands to exact dyadics, perform
integer arithmetic, and round once in the destination format. This module proves the corresponding
real-number statements uniformly in the exponent and fraction widths for descriptors satisfying
`fmt.isIEEE = true`.

The result-finiteness hypotheses exclude IEEE overflow to infinity. NaNs and infinities are covered
by the executable special-value rules, but they do not have values in this real-number semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats

/--
Finite operands whose exact real sum is within the destination's largest finite magnitude cannot
overflow under nearest-even addition.
-/
theorem isFinite_add_of_abs_toReal_add_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x + toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (add x y) = true := by
  obtain ⟨dx, hdx⟩ := exists_toDyadicOption_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadicOption_of_isFinite hy
  have hadd : add x y = roundDyadic fmt (addDyadic dx dy) := by
    simp [Proof.add_eq_spec, Spec.add, hdx, hdy]
  rw [hadd]
  apply isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite fmt hfmt
  rw [Dyadic.toReal_addDyadic]
  simpa [toReal_eq, hdx, hdy] using hbound

/--
The triangle bound `|x| + |y| ≤ maxFinite` is a symbolic sufficient condition for finite
nearest-even addition.
-/
theorem isFinite_add_of_abs_add_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x| + |toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (add x y) = true :=
  isFinite_add_of_abs_toReal_add_le_posMaxFinite x y hfmt hx hy
    ((abs_add_le (toReal x) (toReal y)).trans hbound)

/--
Finite addition is exact real addition followed by one nearest-even format rounding.

The hypothesis `hfin` excludes overflow: it asks that the executable sum itself be finite, which
is decidable on the result. `toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite` replaces that
observation by a symbolic bound on the operands.
-/
theorem toReal_add_eq_roundAt {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hfin : isFinite (add x y) = true) :
    toReal (add x y) = roundAt fmt (toReal x + toReal y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadicOption_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadicOption_of_isFinite hy
  have hadd : add x y = roundDyadic fmt (addDyadic dx dy) := by
    simp [Proof.add_eq_spec, Spec.add, hdx, hdy]
  have hroundFinite : isFinite (roundDyadic fmt (addDyadic dx dy)) = true := by
    simpa [hadd] using hfin
  calc
    toReal (add x y) = toReal (roundDyadic fmt (addDyadic dx dy)) := by rw [hadd]
    _ = roundAt fmt (addDyadic dx dy).toReal :=
      toReal_roundDyadic_eq_roundAt fmt hfmt (addDyadic dx dy) hroundFinite
    _ = roundAt fmt (dx.toReal + dy.toReal) := by rw [Dyadic.toReal_addDyadic]
    _ = roundAt fmt (toReal x + toReal y) := by simp [toReal_eq, hdx, hdy]

/--
Finite addition under a symbolic triangle bound is exact real addition followed by one
nearest-even format rounding.
-/
theorem toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x| + |toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal (add x y) = roundAt fmt (toReal x + toReal y) :=
  toReal_add_eq_roundAt x y hfmt hx hy
    (isFinite_add_of_abs_add_le_posMaxFinite x y hfmt hx hy hbound)

/--
Finite operands whose exact real product is within the destination's largest finite magnitude
cannot overflow under nearest-even multiplication.
-/
theorem isFinite_mul_of_abs_mul_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x| * |toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (mul x y) = true := by
  obtain ⟨dx, hdx⟩ := exists_toDyadicOption_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadicOption_of_isFinite hy
  let product : Numerics.Dyadic :=
    { negative := Bool.xor dx.negative dy.negative
      significand := dx.significand * dy.significand
      exponent := dx.exponent + dy.exponent }
  by_cases hxzero : dx.significand = 0
  · have hmul : mul x y = zero fmt (Bool.xor dx.negative dy.negative) := by
      simp [Proof.mul_eq_spec, Spec.mul, hdx, hdy, hxzero]
    rw [hmul]
    exact isFinite_eq_true_of_isZero_eq_true _
      (isZero_zero fmt (Bool.xor dx.negative dy.negative))
  · by_cases hyzero : dy.significand = 0
    · have hmul : mul x y = zero fmt (Bool.xor dx.negative dy.negative) := by
        simp [Proof.mul_eq_spec, Spec.mul, hdx, hdy, hyzero]
      rw [hmul]
      exact isFinite_eq_true_of_isZero_eq_true _
        (isZero_zero fmt (Bool.xor dx.negative dy.negative))
    · have hmul : mul x y = roundDyadic fmt product := by
        simp [Proof.mul_eq_spec, Spec.mul, hdx, hdy, hxzero, hyzero, product]
      rw [hmul]
      apply isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite fmt hfmt
      rw [show product.toReal = dx.toReal * dy.toReal by
        simpa [product] using Dyadic.toReal_mul dx dy]
      simpa [toReal_eq, hdx, hdy, abs_mul] using hbound

/--
Finite multiplication is exact real multiplication followed by one nearest-even rounding.

The hypothesis `hfin` excludes overflow by asking that the executable product be finite;
`toReal_mul_eq_roundAt_of_abs_mul_le_posMaxFinite` supplies it from a bound on the operands.
-/
theorem toReal_mul_eq_roundAt {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hfin : isFinite (mul x y) = true) :
    toReal (mul x y) = roundAt fmt (toReal x * toReal y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadicOption_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadicOption_of_isFinite hy
  let product : Numerics.Dyadic :=
    { negative := Bool.xor dx.negative dy.negative
      significand := dx.significand * dy.significand
      exponent := dx.exponent + dy.exponent }
  by_cases hxzero : dx.significand = 0
  · have hxReal : toReal x = 0 := by simp [toReal_eq, hdx, Numerics.Dyadic.toReal, hxzero]
    have hmul : mul x y = zero fmt (Bool.xor dx.negative dy.negative) := by
      simp [Proof.mul_eq_spec, Spec.mul, hdx, hdy, hxzero]
    rw [hmul, toReal_zero, hxReal, zero_mul, roundAt_zero]
  · by_cases hyzero : dy.significand = 0
    · have hyReal : toReal y = 0 := by simp [toReal_eq, hdy, Numerics.Dyadic.toReal, hyzero]
      have hmul : mul x y = zero fmt (Bool.xor dx.negative dy.negative) := by
        simp [Proof.mul_eq_spec, Spec.mul, hdx, hdy, hyzero]
      rw [hmul, toReal_zero, hyReal, mul_zero, roundAt_zero]
    · have hmul : mul x y = roundDyadic fmt product := by
        simp [Proof.mul_eq_spec, Spec.mul, hdx, hdy, hxzero, hyzero, product]
      have hroundFinite : isFinite (roundDyadic fmt product) = true := by
        simpa [hmul] using hfin
      calc
        toReal (mul x y) = toReal (roundDyadic fmt product) := by rw [hmul]
        _ = roundAt fmt product.toReal :=
          toReal_roundDyadic_eq_roundAt fmt hfmt product hroundFinite
        _ = roundAt fmt (dx.toReal * dy.toReal) := by
          rw [show product.toReal = dx.toReal * dy.toReal by
            simpa [product] using Dyadic.toReal_mul dx dy]
        _ = roundAt fmt (toReal x * toReal y) := by simp [toReal_eq, hdx, hdy]

/--
Finite multiplication under a symbolic magnitude-product bound is exact real multiplication
followed by one nearest-even format rounding.
-/
theorem toReal_mul_eq_roundAt_of_abs_mul_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x| * |toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal (mul x y) = roundAt fmt (toReal x * toReal y) :=
  toReal_mul_eq_roundAt x y hfmt hx hy
    (isFinite_mul_of_abs_mul_le_posMaxFinite x y hfmt hx hy hbound)

/--
Finite operands whose exact fused result is within the destination's largest finite magnitude
cannot overflow under nearest-even fused multiply-add.
-/
theorem isFinite_fma_of_abs_toReal_fma_le_posMaxFinite
    {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hbound : |toReal x * toReal y + toReal z| ≤ toReal (posMaxFinite fmt)) :
    isFinite (fma x y z) = true := by
  obtain ⟨dx, hdx⟩ := exists_toDyadicOption_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadicOption_of_isFinite hy
  obtain ⟨dz, hdz⟩ := exists_toDyadicOption_of_isFinite hz
  let product : Numerics.Dyadic :=
    { negative := Bool.xor dx.negative dy.negative
      significand := dx.significand * dy.significand
      exponent := dx.exponent + dy.exponent }
  have hencoding : fmt.encoding = .ieee :=
    ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  have hxSNaN : IEEE.isSNaN x = false := by
    simpa [isSNaN, hencoding] using isSNaN_eq_false_of_toDyadicOption_some hdx
  have hySNaN : IEEE.isSNaN y = false := by
    simpa [isSNaN, hencoding] using isSNaN_eq_false_of_toDyadicOption_some hdy
  have hzSNaN : IEEE.isSNaN z = false := by
    simpa [isSNaN, hencoding] using isSNaN_eq_false_of_toDyadicOption_some hdz
  have hfma : fma x y z = roundDyadic fmt (addDyadic product dz) := by
    simp [Proof.fma_eq_spec, Spec.fma, chooseNaN3, isSNaN, hencoding, hdx, hdy, hdz,
      hxSNaN, hySNaN, hzSNaN,
      isNaN_eq_false_of_toDyadicOption_some,
      isInf_eq_false_of_toDyadicOption_some, product]
  rw [hfma]
  apply isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite fmt hfmt
  rw [Dyadic.toReal_addDyadic]
  rw [show product.toReal = dx.toReal * dy.toReal by
    simpa [product] using Dyadic.toReal_mul dx dy]
  simpa [toReal_eq, hdx, hdy, hdz] using hbound

/--
The triangle bound `|x| * |y| + |z| ≤ maxFinite` is a symbolic sufficient condition for finite
nearest-even fused multiply-add.
-/
theorem isFinite_fma_of_abs_mul_add_le_posMaxFinite
    {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hbound :
      |toReal x| * |toReal y| + |toReal z| ≤ toReal (posMaxFinite fmt)) :
    isFinite (fma x y z) = true := by
  apply isFinite_fma_of_abs_toReal_fma_le_posMaxFinite x y z hfmt hx hy hz
  calc
    |toReal x * toReal y + toReal z| ≤
        |toReal x * toReal y| + |toReal z| :=
      abs_add_le _ _
    _ = |toReal x| * |toReal y| + |toReal z| := by rw [abs_mul]
    _ ≤ toReal (posMaxFinite fmt) := hbound

/--
Finite fused multiply-add is exact real multiplication and addition followed by one rounding.

The hypothesis `hfin` excludes overflow by asking that the executable result be finite;
`toReal_fma_eq_roundAt_of_abs_mul_add_le_posMaxFinite` supplies it from a bound on the operands.
-/
theorem toReal_fma_eq_roundAt {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hfin : isFinite (fma x y z) = true) :
    toReal (fma x y z) = roundAt fmt (toReal x * toReal y + toReal z) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadicOption_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadicOption_of_isFinite hy
  obtain ⟨dz, hdz⟩ := exists_toDyadicOption_of_isFinite hz
  let product : Numerics.Dyadic :=
    { negative := Bool.xor dx.negative dy.negative
      significand := dx.significand * dy.significand
      exponent := dx.exponent + dy.exponent }
  have hencoding : fmt.encoding = .ieee :=
    ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  have hxSNaN : IEEE.isSNaN x = false := by
    simpa [isSNaN, hencoding] using isSNaN_eq_false_of_toDyadicOption_some hdx
  have hySNaN : IEEE.isSNaN y = false := by
    simpa [isSNaN, hencoding] using isSNaN_eq_false_of_toDyadicOption_some hdy
  have hzSNaN : IEEE.isSNaN z = false := by
    simpa [isSNaN, hencoding] using isSNaN_eq_false_of_toDyadicOption_some hdz
  have hfma : fma x y z = roundDyadic fmt (addDyadic product dz) := by
    simp [Proof.fma_eq_spec, Spec.fma, chooseNaN3, isSNaN, hencoding, hdx, hdy, hdz,
      hxSNaN, hySNaN, hzSNaN,
      isNaN_eq_false_of_toDyadicOption_some,
      isInf_eq_false_of_toDyadicOption_some, product]
  have hroundFinite : isFinite (roundDyadic fmt (addDyadic product dz)) = true := by
    simpa [hfma] using hfin
  calc
    toReal (fma x y z) = toReal (roundDyadic fmt (addDyadic product dz)) := by rw [hfma]
    _ = roundAt fmt (addDyadic product dz).toReal :=
      toReal_roundDyadic_eq_roundAt fmt hfmt (addDyadic product dz) hroundFinite
    _ = roundAt fmt (product.toReal + dz.toReal) := by rw [Dyadic.toReal_addDyadic]
    _ = roundAt fmt (dx.toReal * dy.toReal + dz.toReal) := by
      rw [show product.toReal = dx.toReal * dy.toReal by
        simpa [product] using Dyadic.toReal_mul dx dy]
    _ = roundAt fmt (toReal x * toReal y + toReal z) := by
      simp [toReal_eq, hdx, hdy, hdz]

/--
Finite fused multiply-add under a symbolic triangle bound is exact real FMA followed by one
nearest-even format rounding.
-/
theorem toReal_fma_eq_roundAt_of_abs_mul_add_le_posMaxFinite
    {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hbound :
      |toReal x| * |toReal y| + |toReal z| ≤ toReal (posMaxFinite fmt)) :
    toReal (fma x y z) = roundAt fmt (toReal x * toReal y + toReal z) :=
  toReal_fma_eq_roundAt x y z hfmt hx hy hz
    (isFinite_fma_of_abs_mul_add_le_posMaxFinite x y z hfmt hx hy hz hbound)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
