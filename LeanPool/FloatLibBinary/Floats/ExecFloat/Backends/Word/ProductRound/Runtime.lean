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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Core.Runtime

/-!
# Shared native-word product finishing

The one-word and two-word multiplication kernels use different representations for the exact
product. After rounding that product to a `UInt64` significand, both kernels perform the same
carry adjustment, overflow test, and field packing. Keeping that final stage here gives the two
backends one executable definition as well as one proof.

`finishWord` returns a word rather than an `Option`; its caller chooses a decline marker outside
the valid packed range. Both definitions request inlining. The overflow threshold and exponent
offset are formed from `NativeSmallWord.biasWord` using machine-word arithmetic.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeWordProduct

open NativeSmallWord

/-- Finish a rounded native-word product already in the normal range, declining on overflow. -/
@[always_inline, inline] def finishOption (fmt : FloatFormat) (sign : Bool)
    (position rounded : UInt64) : Option (Model fmt) :=
  let carry := rounded == carryBit fmt
  let normalizedPosition := if carry then position + 1 else position
  let overflowThreshold :=
    3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2
  if overflowThreshold < normalizedPosition then
    none
  else
    let normalizedMantissa :=
      if carry then hiddenBit fmt else rounded
    let exponentOffset :=
      biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2
    let exponent := normalizedPosition - exponentOffset
    let fraction := normalizedMantissa - hiddenBit fmt
    some <| NativeSmallWord.ofWord <|
      NativeSmallWord.packFields fmt sign exponent fraction

/--
Finish a rounded native-word product without constructing an `Option`.

On overflow the function returns `decline`; otherwise it returns the packed storage word.
-/
@[always_inline, inline] def finishWord (fmt : FloatFormat) (decline : UInt64)
    (sign : Bool) (position rounded : UInt64) : UInt64 :=
  let carry := rounded == carryBit fmt
  let normalizedPosition := if carry then position + 1 else position
  let overflowThreshold :=
    3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2
  if overflowThreshold < normalizedPosition then
    decline
  else
    let normalizedMantissa :=
      if carry then hiddenBit fmt else rounded
    let exponentOffset :=
      biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2
    let exponent := normalizedPosition - exponentOffset
    let fraction := normalizedMantissa - hiddenBit fmt
    NativeSmallWord.packFields fmt sign exponent fraction

end Model.NativeWordProduct
end FloatLib.Floats.Formats.BinaryInterchange
