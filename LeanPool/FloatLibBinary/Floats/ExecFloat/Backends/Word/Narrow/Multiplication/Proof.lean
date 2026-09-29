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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Finite.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Multiplication.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Rounding.Proof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set

/-!
# Correctness of native-word finite multiplication for generic binary32

The direct `UInt64` multiplication kernel is proved equivalent to its exact-dyadic finite
specification. Runtime clients can import `Multiplication.Runtime` without the component and
rounding developments.

The significands have at most 24 bits, so their product is exact in `UInt64`. The proof bounds
the unsigned product scale and applies the native rounder theorem for `FloatFormat.binary32`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- The direct `UInt64` finite multiply kernel equals the exact-dyadic reference operation. -/
theorem mulFiniteImpl_eq (x y : Value) :
    mulFiniteImplOption x y = mulFiniteOption x y := by
  unfold mulFiniteImplOption mulFiniteOption
  rw [toDyadic_eq_finiteComponents x, toDyadic_eq_finiteComponents y]
  dsimp only
  simp only [Bool.or_eq_true, beq_iff_eq]
  set xExponent := expField (toUInt32 x) with hxExponent
  set yExponent := expField (toUInt32 y) with hyExponent
  set xFraction := fracField (toUInt32 x) with hxFraction
  set yFraction := fracField (toUInt32 y) with hyFraction
  set xMantissa : UInt64 := finiteMantissa xExponent xFraction with hxMantissa
  set yMantissa : UInt64 := finiteMantissa yExponent yFraction with hyMantissa
  set xScale : UInt64 := finiteScale xExponent with hxScale
  set yScale : UInt64 := finiteScale yExponent with hyScale
  by_cases hxExceptional : xExponent = 0xff
  · simp [hxExceptional]
  by_cases hyExceptional : yExponent = 0xff
  · simp [hxExceptional, hyExceptional]
  by_cases hxZero : xMantissa = 0
  · by_cases hyZero : yMantissa = 0 <;>
      simp [hxExceptional, hyExceptional, hxZero, hyZero, roundProduct]
  by_cases hyZero : yMantissa = 0
  · simp [hxExceptional, hyExceptional, hxZero, hyZero, roundProduct]
  have hxNatNonzero : xMantissa.toNat ≠ 0 :=
    (FloatLib.Numerics.FixedWord.uint64_toNat_eq_zero xMantissa).not.mpr hxZero
  have hyNatNonzero : yMantissa.toNat ≠ 0 :=
    (FloatLib.Numerics.FixedWord.uint64_toNat_eq_zero yMantissa).not.mpr hyZero
  simp only [hxExceptional, hyExceptional, hxZero, hyZero, hxNatNonzero,
    hyNatNonzero, or_self, ite_false]
  have hxMantissaLt :=
    finiteMantissa_lt_of_components x hxExponent hxFraction hxMantissa
  have hyMantissaLt :=
    finiteMantissa_lt_of_components y hyExponent hyFraction hyMantissa
  have hproductBound :
      xMantissa.toNat * yMantissa.toNat < 2 ^ 48 := by
    norm_num at hxMantissaLt hyMantissaLt ⊢
    nlinarith
  have hproduct :
      (xMantissa * yMantissa).toNat =
        xMantissa.toNat * yMantissa.toNat := by
    rw [UInt64.toNat_mul]
    apply Nat.mod_eq_of_lt
    exact lt_trans hproductBound (by norm_num)
  have hxScaleLe :=
    finiteScale_le_of_components x hxExponent hxScale hxExceptional
  have hyScaleLe :=
    finiteScale_le_of_components y hyExponent hyScale hyExceptional
  have hscale :
      (xScale + yScale).toNat = xScale.toNat + yScale.toNat := by
    rw [UInt64.toNat_add]
    apply Nat.mod_eq_of_lt
    omega
  have hscaleLe : (xScale + yScale).toNat ≤ 506 := by
    rw [hscale]
    omega
  have hexponent :
      Int.ofNat (xScale.toNat + yScale.toNat) - 298 =
        (Int.ofNat xScale.toNat - 149) +
          (Int.ofNat yScale.toNat - 149) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    omega
  have hround := roundProduct_eq_roundDyadic
    (signBit (toUInt32 x) ^^ signBit (toUInt32 y))
    (xMantissa * yMantissa) (xScale + yScale)
    hscaleLe
  rw [hproduct, hscale, hexponent] at hround
  exact congrArg (fun bits => some (ofUInt32 bits)) hround

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
