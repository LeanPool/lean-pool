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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# Executable binary comparisons

Comparison first handles NaNs and signed infinities, then compares finite values through their
exact dyadic denotations. This gives every `FloatFormat` one numerical order without assuming a
particular storage width or relying on host floating-point comparison.

NaNs remain unordered. The minimum and maximum operations apply their NaN-selection and
signed-zero rules around the same comparator. Both the deprecated IEEE 754-2008 `minNum`/`maxNum`
and the IEEE 754-2019 `minimumNumber`/`maximumNumber` operations are provided; they differ only
in how a signaling NaN operand is treated.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Numerical ordering once both operands are known not to be NaNs.

Infinity is ordered by sign. Every remaining bit pattern is finite, so comparison uses the exact
dyadics extracted from those classification proofs.
-/
def compareNonNaN {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) : Ordering :=
  if hxInf : isInf x then
    if isInf y then
      if signBit x == signBit y then .eq
      else if signBit x then .lt else .gt
    else
      if signBit x then .lt else .gt
  else if hyInf : isInf y then
    if signBit y then .gt else .lt
  else
    let hxFinite :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hxNaN
        (Bool.eq_false_of_not_eq_true hxInf)
    let hyFinite :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hyNaN
        (Bool.eq_false_of_not_eq_true hyInf)
    cmpDyadic (finiteDyadic x hxFinite) (finiteDyadic y hyFinite)

/--
IEEE numerical comparison: `none` if either is NaN (unordered); otherwise `some Ordering`.

Infinities are handled first by sign; finite values are compared through `cmpDyadic`.
-/
def compare {fmt : FloatFormat} (x y : Model fmt) : Option Ordering :=
  if hnan : isNaN x || isNaN y then
    none
  else
    let hnotNaN :=
      Bool.or_eq_false_iff.mp (Bool.eq_false_of_not_eq_true hnan)
    some (compareNonNaN x y hnotNaN.1 hnotNaN.2)

/-- True iff `compare x y = some .lt` (false when unordered / NaN). -/
def lt {fmt : FloatFormat} (x y : Model fmt) : Prop :=
  compare x y = some .lt

/-- True on `some .lt` or `some .eq`; false for NaN unordered. -/
def le {fmt : FloatFormat} (x y : Model fmt) : Prop :=
  match compare x y with
  | some .lt => True
  | some .eq => True
  | _ => False

/-- IEEE `minimum`: NaNs via `chooseNaN2`; `minimum(-0,+0) = -0`. -/
def minimum {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  withNaNSelection (chooseNaN2 x y) fun hnan =>
    let hnotNaN := (chooseNaN2_eq_none_iff x y).1 hnan
    match compareNonNaN x y hnotNaN.1 hnotNaN.2 with
    | .lt => x
    | .gt => y
    | .eq =>
        if isZero x && isZero y then
          zero fmt (signBit x || signBit y)
        else
          x

/-- IEEE `maximum`: NaNs via `chooseNaN2`; `maximum(-0,+0) = +0`. -/
def maximum {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  withNaNSelection (chooseNaN2 x y) fun hnan =>
    let hnotNaN := (chooseNaN2_eq_none_iff x y).1 hnan
    match compareNonNaN x y hnotNaN.1 hnotNaN.2 with
    | .lt => y
    | .gt => x
    | .eq =>
        if isZero x && isZero y then
          zero fmt (signBit x && signBit y)
        else
          x

/--
IEEE 754-2008 `minNum`, deprecated by IEEE 754-2019 in favor of `minimumNumber`.

A signaling NaN takes priority and propagates as a quiet NaN. Otherwise, a lone quiet NaN is
ignored, two quiet NaNs select the left operand after quieting, and two numbers use `minimum`,
including its `minNum(-0, +0) = -0` rule.
-/
def minNum {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if isSNaN x then quietNaN x
  else if isSNaN y then quietNaN y
  else if isNaN x then
    if isNaN y then quietNaN x else y
  else if isNaN y then
    x
  else
    minimum x y

/--
IEEE 754-2008 `maxNum`, deprecated by IEEE 754-2019 in favor of `maximumNumber`.

A signaling NaN takes priority and propagates as a quiet NaN. Otherwise, a lone quiet NaN is
ignored, two quiet NaNs select the left operand after quieting, and two numbers use `maximum`,
including its `maxNum(-0, +0) = +0` rule.
-/
def maxNum {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if isSNaN x then quietNaN x
  else if isSNaN y then quietNaN y
  else if isNaN x then
    if isNaN y then quietNaN x else y
  else if isNaN y then
    x
  else
    maximum x y

/--
Quiet NaN delivered when both operands of `minimumNumber` or `maximumNumber` are NaNs.

The signaling operand is preferred, then the left operand, matching `chooseNaN2`.
-/
@[inline] def bothNaNNumber {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if !isSNaN x && isSNaN y then quietNaN y else quietNaN x

/--
IEEE 754-2019 §9.6 `minimumNumber`.

If exactly one operand is a NaN, quiet or signaling, the other operand is returned; a signaling
NaN is not propagated. When both operands are NaNs the result is a quiet NaN chosen by
`bothNaNNumber`. On two numbers this is `minimum`, so `minimumNumber(-0, +0) = -0`. The invalid
signal owed to a signaling operand is reported by `minimumNumberWithStatus` in
`Operations.Runtime`, since the value alone carries no status.
-/
def minimumNumber {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if isNaN x then
    if isNaN y then bothNaNNumber x y else y
  else if isNaN y then
    x
  else
    minimum x y

/--
IEEE 754-2019 §9.6 `maximumNumber`.

If exactly one operand is a NaN, quiet or signaling, the other operand is returned; a signaling
NaN is not propagated. When both operands are NaNs the result is a quiet NaN chosen by
`bothNaNNumber`. On two numbers this is `maximum`, so `maximumNumber(-0, +0) = +0`. The invalid
signal owed to a signaling operand is reported by `maximumNumberWithStatus` in
`Operations.Runtime`.
-/
def maximumNumber {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  if isNaN x then
    if isNaN y then bothNaNNumber x y else y
  else if isNaN y then
    x
  else
    maximum x y

end Model

end FloatLib.Floats.Formats.BinaryInterchange
