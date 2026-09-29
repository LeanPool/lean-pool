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
public import Mathlib.Data.Rat.Cast.Order

/-!
# Finite binary32 runtime coordinates

Finite binary32 fields are converted into the mantissa-and-scale coordinates shared by native
arithmetic kernels. For every nonzero finite value, the coordinates denote its magnitude
`mantissa * 2^(scale - 149)`, with exponent subtraction in `Int`. Bounds and decoder agreement
live in `Finite.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- Decode a finite binary32 significand into one native word. -/
@[inline] def finiteMantissa (exponent fraction : UInt32) : UInt64 :=
  if exponent == 0 then
    fraction.toUInt64
  else
    fraction.toUInt64 ||| 0x800000

/--
Encode the finite exponent as a nonnegative scale, giving magnitude
`mantissa * 2^(scale - 149)` with exponent subtraction in `Int`.

The binary32 entry point only widens its native field; the scale rule itself is shared with every
word kernel.
-/
@[always_inline, inline] def finiteScale (exponent : UInt32) : UInt64 :=
  FloatLib.Numerics.FixedWord.finiteScale exponent.toUInt64

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
