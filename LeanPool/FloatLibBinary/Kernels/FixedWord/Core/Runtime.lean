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

public import LeanPool.FloatLibBinary.Numerics.Quantization.Deterministic
public import Init.Data.UInt.Log2

/-!
# Shared fixed-word runtime primitives

Fixed-format and fixed-limb backends share a native-integer toolbox for bounded arithmetic. It
implements nearest-even shifts and quotients, two-word arithmetic, and restoring square-root
state without committing to a floating-point format.

The common case stays in `UInt64` or `UInt128` so a specialized backend does not pay for arbitrary
precision arithmetic merely to manipulate a few limbs. Every boundary where truncation or
overflow could matter is kept explicit, and `Core.Proof` relates these routines to their
unbounded-natural specifications. Wider inputs use the general numerical kernel rather than an
approximate host operation.
-/

@[expose] public section

universe u

namespace FloatLib.Numerics.FixedWord

/-- Encode a finite exponent as the nonnegative scale used by compact arithmetic kernels. -/
@[inline] def finiteScale (exponent : UInt64) : UInt64 :=
  if exponent == 0 then 0 else exponent - 1

/-- Round a `UInt64` divided by `2^shift` to nearest, with ties to even. -/
@[inline] def roundShiftRightEven (value : UInt64) (shift : Nat) : UInt64 :=
  if shift == 0 then
    value
  else if shift < 64 then
    let amount := UInt64.ofNat shift
    let quotient := value >>> amount
    let remainder := value &&& ((1 <<< amount) - 1)
    let half := (1 : UInt64) <<< UInt64.ofNat (shift - 1)
    if remainder < half then
      quotient
    else if remainder > half then
      quotient + 1
    else if (quotient &&& 1) == 0 then
      quotient
    else
      quotient + 1
  else if shift == 64 then
    if value > 0x8000000000000000 then 1 else 0
  else
    0

/--
Use native nearest-even shifting whenever the input fits in one machine word.

`Core.Proof.Rounding` registers this dispatcher as the `@[csimp]` replacement for
`Numerics.roundShiftRightEven`. The arbitrary-precision branch therefore repeats the logical
definition instead of calling it, so compiler simplification cannot recurse through the
replacement theorem.
-/
@[inline] def roundShiftRightEvenNat (value shift : Nat) : Nat :=
  if _hvalue : value < 2 ^ 64 then
    (roundShiftRightEven (UInt64.ofNat value) shift).toNat
  else if shift == 0 then
    value
  else if value.log2 + 1 < shift then
    0
  else
    let quotient := Nat.shiftRight value shift
    let remainder := shiftRightRemainder value shift
    let half := Nat.shiftLeft 1 (shift - 1)
    if remainder < half then
      quotient
    else if half < remainder then
      quotient + 1
    else if quotient % 2 == 0 then
      quotient
    else
      quotient + 1

/--
Round the native quotient `num / den` to nearest, with ties to even.

Since `num % den < den`, comparing the remainder with `den - remainder` decides `2 * remainder`
against `den` without leaving the word: the subtraction is exact and no doubling can wrap. For
`den = 0` the kernel returns `0`. This differs from `Numerics.roundQuotientEven num 0`, which
inherits Lean's `n / 0 = 0` and `n % 0 = n` and so returns `1` for nonzero `num`;
`roundQuotientEven_toNat` accordingly assumes `den ≠ 0`.
-/
@[inline] def roundQuotientEven (num den : UInt64) : UInt64 :=
  if den == 0 then
    0
  else
    let quotient := num / den
    let remainder := num % den
    let complement := den - remainder
    if remainder < complement then
      quotient
    else if complement < remainder then
      quotient + 1
    else if quotient % 2 == 0 then
      quotient
    else
      quotient + 1

/--
Use native quotient rounding when the numerator fits in the signed-word range and the denominator
is a nonzero machine word.

The numerator bound keeps the incremented quotient below `2^64`. `Core.Proof.Rounding` registers
this dispatcher as the `@[csimp]` replacement for `Numerics.roundQuotientEven`, so the
arbitrary-precision branch repeats the logical definition instead of calling it; compiler
simplification must not recurse through the replacement theorem.
-/
@[inline] def roundQuotientEvenNat (num den : Nat) : Nat :=
  if _hfit : num < 2 ^ 63 ∧ 0 < den ∧ den < 2 ^ 64 then
    (roundQuotientEven (UInt64.ofNat num) (UInt64.ofNat den)).toNat
  else
    let quotient := num / den
    let remainder := num % den
    let twice := 2 * remainder
    if twice < den then
      quotient
    else if den < twice then
      quotient + 1
    else if quotient % 2 == 0 then
      quotient
    else
      quotient + 1

end FloatLib.Numerics.FixedWord

namespace FloatLib.Numerics.FixedWord

/--
Root and remainder produced by a restoring square-root loop.

The carrier is selected by exact capacity. Restoring kernels over one or more native words share
this state and the same square/remainder invariant.
-/
structure RestoringRootState (α : Type u) where
  /-- Current floor-root prefix. -/
  root : α
  /-- Exact remainder after the consumed base-four digits. -/
  remainder : α
  deriving DecidableEq, Repr

/-! ## Representation-independent nearest-even selection -/

/--
Select one of two adjacent natural-number codes from an exact midpoint comparison.

The comparison is `target` versus `midpoint`. Equality uses the low bit of the lower code for
ties-to-even. Numerical formats may share this decision primitive while retaining their own
decoders, candidate construction, and exceptional-value semantics.
-/
@[inline] def selectNearestEvenNat
    (comparison : Ordering) (lower upper : Nat) : Nat :=
  match comparison with
  | .lt => lower
  | .eq => if lower % 2 = 0 then lower else upper
  | .gt => upper

/--
Machine-word sibling of `selectNearestEvenNat`.

Keeping the parity test in `UInt64` prevents an otherwise unnecessary arbitrary-precision
conversion in fixed-carrier rounding kernels.
-/
@[inline] def selectNearestEvenWord
    (comparison : Ordering) (lower upper : UInt64) : UInt64 :=
  match comparison with
  | .lt => lower
  | .eq => if (lower &&& 1) == 0 then lower else upper
  | .gt => upper

/-! ## Machine-width bit-field primitives -/

/--
Read one bit from a machine word using a machine-word index.

Lean's `UInt64` shifts reduce their count modulo 64. The explicit range check is therefore part of
the semantics: an index outside the stored word returns `false` instead of wrapping to a different
bit. Format backends should keep statically bounded field widths in this representation throughout
their hot decoder and cross to `Nat` only at an exact arbitrary-precision boundary.
-/
@[inline] def bitAtWord (value index : UInt64) : Bool :=
  if index < 64 then
    (((value >>> index) &&& 1) == 1)
  else
    false

/--
Mask the low `width` bits of a machine word.

The complete-width branch avoids the modulo-64 interpretation of `1 <<< 64`.
-/
@[inline] def lowMaskWord (width : UInt64) : UInt64 :=
  if width < 64 then
    ((1 : UInt64) <<< width) - 1
  else
    0xffffffffffffffff

/-- Retain the low `width` bits of a machine word. -/
@[inline] def lowBitsWord (value width : UInt64) : UInt64 :=
  value &&& lowMaskWord width

/--
Count leading zeroes in the retained low-width field without crossing through `Nat`.

Callers establish `width ≤ 64`. For a nonzero field, `UInt64.log2` gives its highest set-bit index,
so the result is `width - bitLength`; the subtraction is exact under that capacity contract.
-/
@[inline] def countLeadingZerosWord (value width : UInt64) : UInt64 :=
  let truncated := lowBitsWord value width
  if truncated == 0 then
    width
  else
    width - (truncated.log2 + 1)

/--
Count a leading equal-bit run in a low-width machine field.

Leading ones are leading zeroes after whole-word complementation. Bits above `width` are discarded
by `lowBitsWord`, so the complement has exactly the intended fixed-field meaning.
-/
@[inline] def countLeadingRunWord
    (value width : UInt64) (bit : Bool) : UInt64 :=
  countLeadingZerosWord (if bit then ~~~value else value) width

/--
Shift right by a machine-word amount, returning zero at and beyond the carrier width.
-/
@[inline] def shiftRightWord (value shift : UInt64) : UInt64 :=
  if shift < 64 then value >>> shift else 0

/-- A 128-bit unsigned value represented by two native 64-bit limbs. -/
structure UInt128 where
  /-- Bits 64 through 127. -/
  hi : UInt64
  /-- Bits 0 through 63. -/
  lo : UInt64
  deriving DecidableEq, Repr

namespace UInt128

/-- Mathematical value of a two-limb unsigned integer. -/
def toNat (value : UInt128) : Nat :=
  value.lo.toNat + value.hi.toNat * 2 ^ 64

/-- Split the residue of a natural number modulo `2^128` into two native 64-bit limbs. -/
@[inline] def ofNat (value : Nat) : UInt128 :=
  ⟨UInt64.ofNat (value >>> 64), UInt64.ofNat value⟩

end UInt128

/-- Low 32-bit half of a native word. -/
@[inline] def low32 (value : UInt64) : UInt64 :=
  value &&& 0xffffffff

/-- High 32-bit half of a native word. -/
@[inline] def high32 (value : UInt64) : UInt64 :=
  value >>> 32

/--
Exact native multiplication of two 64-bit words.

The implementation follows the four-half-word decomposition from Hacker's Delight.
-/
@[inline] def mul64 (x y : UInt64) : UInt128 :=
  let x0 := low32 x
  let x1 := high32 x
  let y0 := low32 y
  let y1 := high32 y
  let w0 := x0 * y0
  let t := x1 * y0 + high32 w0
  let w1 := low32 t
  let w2 := high32 t
  let w1 := x0 * y1 + w1
  let hi := x1 * y1 + w2 + high32 w1
  let lo := (low32 w1 <<< 32) + low32 w0
  ⟨hi, lo⟩

end FloatLib.Numerics.FixedWord
