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

/-!
# Low-level rational rounding primitives

Format-independent executable quotient operations support nearest-even and directed rational
rounding. The quotient layer stays below `Model.Arithmetic`, allowing native arithmetic kernels
to reuse their proofs without creating an import cycle through the public dispatcher.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Ceiling of a natural quotient, totalized to zero at a zero denominator. -/
@[inline] def quotCeil (numerator denominator : Nat) : Nat :=
  if denominator == 0 then
    0
  else
    let quotient := numerator / denominator
    let remainder := numerator % denominator
    if remainder == 0 then quotient else quotient + 1

/-- Round a nonnegative quotient to an integer, selecting floor or ceiling. -/
@[inline] def roundQuotDirected (roundUp : Bool) (numerator denominator : Nat) : Nat :=
  if roundUp then quotCeil numerator denominator else numerator / denominator

end Model
end FloatLib.Floats.Formats.BinaryInterchange
