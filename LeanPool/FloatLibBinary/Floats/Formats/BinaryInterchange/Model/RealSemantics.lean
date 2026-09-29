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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Core
import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Arithmetic.Proof
public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Real
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# Real interpretation of binary models

Finite format-parameterized bit patterns denote exact real values. Arithmetic refinement belongs
in later modules, after the executable operation has been related to one exact dyadic
intermediate and one rounding step.
-/

@[expose] public section

section

open FloatLib.Floats.Formats.Flocq

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Dyadic

/-- A dyadic with zero mantissa denotes zero, independently of its sign and exponent. -/
@[simp] theorem toReal_of_mantissa_zero (sign : Bool) (exponent : Int) :
    (Numerics.Dyadic.mk sign 0 exponent).toReal = 0 := by
  cases sign <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]

/-- Numerics.Dyadic real semantics expressed using a signed integer significand. -/
theorem toReal_eq_signedSignificand (d : Numerics.Dyadic) :
    d.toReal = (d.signedSignificand : ℝ) *
      FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix d.exponent := by
  rfl

/-- Left-shifting a signed significand multiplies its real value by the matching power of two. -/
theorem signedSignificand_shiftLeft (d : Numerics.Dyadic) (shift : Nat) :
    ((Numerics.Dyadic.mk d.negative
      (Nat.shiftLeft d.significand shift) 0).signedSignificand : ℝ) =
      (d.signedSignificand : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix (Int.ofNat shift) := by
  cases hs : d.negative <;>
    simp [Numerics.Dyadic.signedSignificand, hs, Nat.shiftLeft_eq,
      FloatLib.Floats.Formats.Flocq.bpow,
      FloatLib.Numerics.binaryRadix, Numerics.Radix.toReal]

/-- Exact dyadic addition agrees with addition in the real semantics. -/
theorem toReal_addDyadic (a b : Numerics.Dyadic) :
    (addDyadic a b).toReal = a.toReal + b.toReal := by
  have h :=
    congrArg (fun value : Rat => (value : ℝ))
      (Numerics.Dyadic.add_toRat a b)
  simpa only [addDyadic, Numerics.Dyadic.cast_toRat, Rat.cast_add] using h

/-- The exact dyadic product used by `Model.mul` agrees with real multiplication. -/
theorem toReal_mul (a b : Numerics.Dyadic) :
    (Numerics.Dyadic.mk (Bool.xor a.negative b.negative)
      (a.significand * b.significand) (a.exponent + b.exponent)).toReal =
      a.toReal * b.toReal := by
  cases ha : a.negative <;> cases hb : b.negative <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      ha, hb, Bool.xor, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] <;> ring

end Dyadic

/-- Real interpretation for finite values; returns `none` for NaN and infinity. -/
noncomputable def toRealOption {fmt : FloatFormat} (x : Model fmt) : Option ℝ :=
  match toDyadicOption x with
  | some d => some d.toReal
  | none => none

/-- Total real interpretation, mapping NaN and infinity to `0`. Numerical theorems must
therefore establish finiteness or handle exceptional inputs separately. -/
noncomputable def toReal {fmt : FloatFormat} (x : Model fmt) : ℝ :=
  match toRealOption x with
  | some r => r
  | none => 0

/-- Real interpretation of Lean's unpacked logical float; NaN and infinity map to zero. -/
noncomputable def unpackedToReal (x : Float.Model.UnpackedFloat) : ℝ :=
  match unpackedToDyadicOption x with
  | some d => d.toReal
  | none => 0

/-- Both signed zeros of Lean's unpacked float model denote the real zero. -/
@[simp] theorem unpackedToReal_zero (sign : Float.Model.UnpackedFloat.Sign) :
    unpackedToReal (.zero sign) = 0 := by
  cases sign <;>
    simp [unpackedToReal, unpackedToDyadicOption, Numerics.Dyadic.toReal,
      Numerics.Dyadic.signedSignificand]

/-- A finite unpacked model value denotes its signed integer mantissa times its dyadic scale. -/
@[simp] theorem unpackedToReal_finite
    (sign : Float.Model.UnpackedFloat.Sign) (mantissa : Nat) (exponent : Int)
    (hm : 0 < mantissa) :
    unpackedToReal (.finite sign mantissa exponent hm) =
      (if modelSignBit sign then (-1 : ℝ) else 1) * (mantissa : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix exponent := by
  cases sign <;>
    simp [unpackedToReal, unpackedToDyadicOption, Numerics.Dyadic.toReal,
      Numerics.Dyadic.signedSignificand, modelSignBit, bpow, Numerics.binaryRadix,
      Numerics.Radix.toReal]

/-- `toReal` is the dyadic denotation on finite values and zero on NaN and infinities. -/
lemma toReal_eq {fmt : FloatFormat} (x : Model fmt) :
    toReal x = match toDyadicOption x with
      | some d => d.toReal
      | none => 0 := by
  cases h : toDyadicOption x <;> simp [toReal, toRealOption, h]

/-- The policy-aware zero constructor denotes zero for every encoding. -/
@[simp] theorem toReal_zero (fmt : FloatFormat) (sign : Bool) :
    toReal (zero fmt sign) = 0 := by
  rw [toReal_eq, toDyadicOption_zero]
  simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]

/-- Executable and logical decoding agree for formats represented by Lean's IEEE model. -/
theorem toReal_eq_unpackedToReal_toModel {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x : Model fmt) :
    toReal x = unpackedToReal (toModel x) := by
  rw [toReal_eq, toDyadicOption_ieee_eq_model fmt hfmt x]
  rfl

end Model
end FloatLib.Floats.Formats.BinaryInterchange

end -- noncomputable section
