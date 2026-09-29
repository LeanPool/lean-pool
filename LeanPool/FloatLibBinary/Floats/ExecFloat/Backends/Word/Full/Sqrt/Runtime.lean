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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Core.Runtime

/-!
# Native binary64 square-root runtime

Positive finite inputs are scaled to a 105- or 106-bit radicand held in two `UInt64` limbs. A
53-step restoring square-root loop computes the floor root and remainder using native words. The
remainder classifies the nearest-even result directly, after which the binary64 exponent and
fraction are packed without constructing a generic unpacked-float model.

Correctness proofs and the `Nat.sqrt` model are isolated in `Sqrt.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord

/-- Shift a binary64 significand into two limbs; callers supply a positive shift below 128
and a result that fits in 128 bits. -/
@[inline] def shiftedRadicand
    (mantissa : UInt64) (shift : Nat) : FloatLib.Numerics.FixedWord.UInt128 :=
  if shift < 64 then
    { hi := mantissa >>> UInt64.ofNat (64 - shift)
      lo := mantissa <<< UInt64.ofNat shift }
  else
    { hi := mantissa <<< UInt64.ofNat (shift - 64)
      lo := 0 }

/-- Read a base-four digit of a two-limb radicand, for an index below 64. -/
@[inline] def digitAt (radicand : FloatLib.Numerics.FixedWord.UInt128) (index : Nat) : UInt64 :=
  if index < 32 then
    (radicand.lo >>> UInt64.ofNat (2 * index)) &&& 3
  else
    (radicand.hi >>> UInt64.ofNat (2 * (index - 32))) &&& 3

/--
Consume one base-four digit in the restoring square-root recurrence.

For the binary64 radicands constructed above, `53` iterations produce a 53-bit floor root. The
remainder and trial divisor remain below one native word.
-/
@[inline] def rootStep (digit : UInt64)
    (state : RestoringRootState UInt64) : RestoringRootState UInt64 :=
  let expanded := state.remainder * 4 + digit
  let trial := state.root * 4 + 1
  if trial ≤ expanded then
    { root := state.root * 2 + 1
      remainder := expanded - trial }
  else
    { root := state.root * 2
      remainder := expanded }

/-- Consume a requested number of radicand digits from most significant to least significant. -/
@[inline] def rootLoop
    (radicand : FloatLib.Numerics.FixedWord.UInt128) :
    Nat → RestoringRootState UInt64 → RestoringRootState UInt64
  | 0, state => state
  | steps + 1, state =>
      let digit := digitAt radicand steps
      rootLoop radicand steps (rootStep digit state)

/-- Compute the floor root and exact remainder of a binary64-sized scaled radicand. -/
@[inline] def rootAndRemainder
    (mantissa : UInt64) (shift : Nat) : RestoringRootState UInt64 :=
  rootLoop (shiftedRadicand mantissa shift) 53 { root := 0, remainder := 0 }

/--
Direct positive-finite binary64 square root.

For a nonzero significand below `2^53` and a scale at most 2045, the input value is
`mantissa * 2^(scale - 1074)`, with subtraction in the exponent interpreted in `Int`. Parity
chooses a 105- or 106-bit integer radicand. Its square root cannot be a half-integer, so
`remainder ≤ root` is precisely the round-down condition.
-/
@[inline] def sqrtPositiveFiniteCore
    (mantissa scale : UInt64) : UInt64 :=
  let leading := mantissa.log2
  let position := leading + scale
  let shift :=
    if position % 2 == 0 then
      104 - leading.toNat
    else
      105 - leading.toNat
  let state := rootAndRemainder mantissa shift
  let roundedRoot :=
    if state.remainder ≤ state.root then state.root else state.root + 1
  let carry := roundedRoot == 0x0020000000000000
  let encodedExponent :=
    (position + 972) / 2 + if carry then 1 else 0
  let roundedMantissa :=
    if carry then 0x0010000000000000 else roundedRoot
  let fraction := roundedMantissa - 0x0010000000000000
  packFieldsWord false encodedExponent fraction

/-- Decode binary64 fields and run the bounded positive-finite square-root kernel. -/
@[inline] def sqrtPositiveFinite (exponent fraction : UInt64) : UInt64 :=
  sqrtPositiveFiniteCore
    (finiteMantissa exponent fraction)
    (finiteScale exponent)

/-- Native binary64 square root, including IEEE exceptional-value behavior. -/
@[inline] def sqrt (x : Value) : Value :=
  match Model.chooseNaN1 x with
  | some nan => nan
  | none =>
      if Model.isInf x then
        if Model.signBit x then
          Model.canonicalNaN FloatFormat.binary64
        else
          Model.posInf FloatFormat.binary64
      else if Model.isZero x then
        x
      else if Model.signBit x then
        Model.canonicalNaN FloatFormat.binary64
      else
        let bits := toUInt64 x
        ofUInt64 (sqrtPositiveFinite (expField bits) (fracField bits))

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
