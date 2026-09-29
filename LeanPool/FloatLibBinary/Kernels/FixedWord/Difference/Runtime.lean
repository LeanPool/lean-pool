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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Runtime

/-!
# Fixed-limb difference runtime

Unsigned two-limb comparison, subtraction, leading-bit discovery, and normalization share the
same borrow and shift conventions. Keeping those conventions here prevents the dyadic comparison
and rounding kernels from growing subtly different copies.

The hot path uses explicit `UInt64` limbs without converting through `Nat`. Their
natural-number meanings, and the preconditions under which wrapping subtraction denotes ordinary
subtraction, are proved separately in `Difference.Proof`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.UInt128

/-- Compare two two-word unsigned values. -/
@[inline] def less (x y : UInt128) : Bool :=
  x.hi < y.hi || (x.hi == y.hi && x.lo < y.lo)

/--
Three-way comparison of two two-word unsigned values.

Exact dyadic certificates use this comparison on widened products without rebuilding them as
arbitrary-precision naturals.
-/
@[inline] def compare (x y : UInt128) : Ordering :=
  if less x y then
    .lt
  else if less y x then
    .gt
  else
    .eq

/-- Subtract two two-word values with borrow. The result wraps modulo `2^128`. -/
@[inline] def sub (x y : UInt128) : UInt128 :=
  let borrow : UInt64 := if x.lo < y.lo then 1 else 0
  {
    hi := x.hi - y.hi - borrow
    lo := x.lo - y.lo
  }

/-- Position of the most significant set bit, with zero mapped to zero. -/
@[inline] def log2 (value : UInt128) : Nat :=
  if value.hi == 0 then value.lo.log2.toNat
  else 64 + value.hi.log2.toNat

/--
Shift a two-word value right, returning zero at and beyond the 128-bit carrier width.

The explicit ranges avoid the modulo reduction performed by native machine-word shifts.
-/
@[inline] def shiftRight (value : UInt128) (shift : Nat) : UInt128 :=
  if shift == 0 then
    value
  else if shift < 64 then
    {
      hi := value.hi >>> UInt64.ofNat shift
      lo :=
        (value.lo >>> UInt64.ofNat shift) |||
          (lowBitsWord value.hi (UInt64.ofNat shift) <<<
            UInt64.ofNat (64 - shift))
    }
  else if shift < 128 then
    {
      hi := 0
      lo := value.hi >>> UInt64.ofNat (shift - 64)
    }
  else
    ⟨0, 0⟩

/--
A two-word value with exactly one bit set, returning zero beyond the 128-bit carrier.

Constructing the bit directly in its containing limb avoids routing fixed-width significands
through an arbitrary-precision power before their final mathematical conversion.
-/
@[inline] def singleBit (index : Nat) : UInt128 :=
  if index < 64 then
    ⟨0, (1 : UInt64) <<< UInt64.ofNat index⟩
  else if index < 128 then
    ⟨(1 : UInt64) <<< UInt64.ofNat (index - 64), 0⟩
  else
    ⟨0, 0⟩

/--
Shift a two-word value left, returning zero at and beyond the 128-bit carrier width.

Bits carried above position 127 are discarded, so the result is `value * 2^shift` reduced modulo
`2^128`. `shiftLeft_toNat` gives the exact product when `shift < 128` and no bit is lost, and
`shiftLeft_of_ge` covers the total branch. The explicit ranges avoid the modulo reduction
performed by native machine-word shifts.
-/
@[inline] def shiftLeft (value : UInt128) (shift : Nat) : UInt128 :=
  if shift == 0 then
    value
  else if shift < 64 then
    {
      hi :=
        (value.hi <<< UInt64.ofNat shift) |||
          (value.lo >>> UInt64.ofNat (64 - shift))
      lo := value.lo <<< UInt64.ofNat shift
    }
  else if shift < 128 then
    {
      hi := value.lo <<< UInt64.ofNat (shift - 64)
      lo := 0
    }
  else
    ⟨0, 0⟩

end FloatLib.Numerics.FixedWord.UInt128
