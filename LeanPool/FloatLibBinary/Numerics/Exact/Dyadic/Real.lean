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

public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Real values of exact dyadics

A dyadic denotes its signed integer significand times an integral power of two. Its rational
and real interpretations agree, so exact arithmetic identities can be transported by casting.
These definitions do not depend on any floating-point format.
-/

@[expose] public section

namespace FloatLib.Numerics.Dyadic

/-- Interpret an exact dyadic `(-1)^sign * significand * 2^exponent` as a real. -/
noncomputable def toReal (d : Dyadic) : ℝ :=
  (d.signedSignificand : ℝ) * (2 : ℝ) ^ d.exponent

/-- The exact rational and real interpretations of a dyadic agree. -/
@[simp, norm_cast] theorem cast_toRat (d : Dyadic) :
    (d.toRat : ℝ) = d.toReal := by
  simp [toRat, toReal, Rat.cast_zpow]

/-- Casting the signed significand separates its sign from its natural magnitude. -/
@[simp] theorem cast_signedSignificand (d : Dyadic) :
    (d.signedSignificand : ℝ) =
      (if d.negative then (-1 : ℝ) else 1) * (d.significand : ℝ) := by
  cases hnegative : d.negative <;>
    simp [signedSignificand, hnegative]

/-- A nonnegative dyadic constructor has the expected unsigned real denotation. -/
@[simp] theorem toReal_mk_false (significand : Nat) (exponent : Int) :
    (Dyadic.mk false significand exponent).toReal =
      (significand : ℝ) * (2 : ℝ) ^ exponent := by
  simp [toReal]

end FloatLib.Numerics.Dyadic
