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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.ModelSqrt.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Runtime


/-!
# Executable compact finite square root

The compiled path consumes the sign, significand, and exponent from `FiniteKernel.Components`,
avoiding a second storage decode. Conventional IEEE descriptors use the unpacked-model kernel;
other descriptors use an arbitrary-precision integer square root. Correctness proofs live in
`Sqrt.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteSqrt

/-- Destination dyadic exponent for the rounded square root of a positive exact dyadic. -/
@[inline] def targetExponent
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) : Int :=
  let sourceTotal := Int.ofNat mantissa.log2 + 1 + exponent
  let resultTotal := (sourceTotal + 1).ediv 2
  max (resultTotal - Int.ofNat (fmt.fracWidth + 1))
    fmt.minSubnormalExponent

/--
Round an integer square-root approximation after discarding `shift` low root bits.

`remainder` records the positive irrational tail: zero means the scaled radicand was a perfect
square. At an exact half-way discarded-bit pattern, any nonzero square-root remainder moves the
exact result above the tie.
-/
@[inline] def roundRoot
    (root remainder shift : Nat) : Nat :=
  if shift == 0 then
    if remainder == 0 || remainder ≤ root then root else root + 1
  else
    let quotient := root >>> shift
    let discarded := root - (quotient <<< shift)
    let half := pow2 (shift - 1)
    if discarded < half then
      quotient
    else if discarded > half then
      quotient + 1
    else if remainder == 0 then
      if quotient % 2 == 0 then quotient else quotient + 1
    else
      quotient + 1

/--
Descriptor-aware positive square root for formats not represented by Lean's conventional IEEE
model.

The radicand and root use natural-number arithmetic; exponents use `Int`.
`IntegerSquareRoot.sqrtNat` uses the proved `UInt64` kernel when the scaled radicand fits and
`Nat.sqrt` for larger inputs.
-/
@[inline] def sqrtGeneral
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) : Model fmt :=
  if mantissa == 0 then
    posZero fmt
  else
    let finalExponent := targetExponent fmt mantissa exponent
    let rootExponent := min (exponent.ediv 2) finalExponent
    let radicandShift := (exponent - 2 * rootExponent).toNat
    let scaledMantissa := mantissa <<< radicandShift
    let root := FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrtNat scaledMantissa
    let remainder := scaledMantissa - root * root
    let roundingShift := (finalExponent - rootExponent).toNat
    let roundedRoot := roundRoot root remainder roundingShift
    roundDyadicImpl fmt
      { negative := false
        significand := roundedRoot
        exponent := finalExponent }

/--
Positive finite square root from an exact dyadic.

The IEEE branch deliberately retains the established logical model and native replacement theorem.
The non-IEEE branch follows the complete descriptor and never converts through `Float.Model`.
-/
@[inline] def sqrtPositiveDyadic
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) : Model fmt :=
  if hzero : mantissa = 0 then
    posZero fmt
  else if fmt.isIEEE then
    ofModel fmt <|
      NativeModelSqrt.sqrt (FloatFormat.toModel fmt)
        (.finite .positive mantissa exponent (Nat.pos_of_ne_zero hzero))
  else
    sqrtGeneral fmt mantissa exponent

/-- Square root of already-decoded positive finite components. -/
@[inline] def sqrtComponentsOption
    (fmt : FloatFormat) (value : FiniteKernel.Components) :
    Option (Model fmt) :=
  if value.sign then
    none
  else if value.mantissa == 0 then
    none
  else
    some <| sqrtPositiveDyadic fmt value.mantissa
      (FiniteKernel.dyadicExponent fmt value.exponent)

/--
Square root of a positive finite nonzero value from compact decoded fields.

`none` means that the input is exceptional, negative, or zero.
-/
@[inline] def sqrtPositiveOption {fmt : FloatFormat}
    (x : Model fmt) : Option (Model fmt) :=
  match FiniteKernel.decodeOption x with
  | none => none
  | some value => sqrtComponentsOption fmt value

/-- Square root directly from scalar finite fields. -/
@[inline] def sqrtFieldsOption
    (fmt : FloatFormat) (sign : Bool) (exponent mantissa : Nat) :
    Option (Model fmt) :=
  if sign then
    none
  else if mantissa == 0 then
    none
  else
    some <| sqrtPositiveDyadic fmt mantissa
      (FiniteKernel.dyadicExponent fmt exponent)

/-- Compiled positive square root with scalar field decoding. -/
@[inline] def sqrtPositiveRuntimeOption {fmt : FloatFormat}
    (x : Model fmt) : Option (Model fmt) :=
  FiniteKernel.withFiniteOption x fun sign exponent mantissa =>
    sqrtFieldsOption fmt sign exponent mantissa

/--
Square root of a value already classified as positive, finite, and nonzero.

The evidence is erased. IEEE descriptors decode the storage word once; other descriptors use their
policy-aware fields. Both paths call `sqrtPositiveDyadic`, which selects the conventional IEEE
model or the descriptor-aware integer square-root kernel.
-/
@[inline] def sqrtPositiveRuntime {fmt : FloatFormat}
    (x : Model fmt)
    (_hfinite : isFinite x = true)
    (_hnonzero : isZero x = false)
    (_hpositive : signBit x = false) : Model fmt :=
  if fmt.isIEEE then
    let bits := x.toNatBits
    let exponent :=
      (bits >>> fmt.fracWidth) &&& FloatFormat.expAllOnesNat fmt
    let fraction := bits &&& FloatFormat.fracMaskNat fmt
    let mantissa := FiniteKernel.decodeMantissa fmt exponent fraction
    sqrtPositiveDyadic fmt mantissa
      (FiniteKernel.dyadicExponent fmt exponent)
  else
    let exponent := expField x
    let fraction := fracField x
    let mantissa := FiniteKernel.decodeMantissa fmt exponent fraction
    sqrtPositiveDyadic fmt mantissa
      (FiniteKernel.dyadicExponent fmt exponent)

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteSqrt
