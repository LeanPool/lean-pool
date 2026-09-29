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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.AddDyadic.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Decode
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Proof

/-!
# Reference arithmetic with exact dyadic intermediates

Addition, subtraction, multiplication, and fused multiply-add share one specification method:
decode finite operands exactly, compute the dyadic intermediate, and round once to nearest with
ties to even. Exceptional operands follow the descriptor's NaN, infinity, overflow, and zero
policy. In particular, FMA does not round its product before adding the third operand.

These definitions are the stable proof targets for the dispatched arithmetic kernels. Quotients
use the rational specification in `Spec.Division`; roots use `Spec.SquareRoot`. Explicit rounding
directions and exception-status results belong to their separate operation APIs.

These specifications also execute when a backend declines an operand. The rounding refinement
must be imported before they are defined: it replaces the logical rounder's repeated one-bit
shifts with bulk integer rounding in their compiled code.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Spec

/-! ## Addition and subtraction -/

/-- Exact dyadic addition followed by nearest-even rounding in the destination descriptor. -/
@[inline] def add {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  match toDyadicOption x, toDyadicOption y with
  | some dx, some dy => roundDyadic fmt (addDyadic dx dy)
  | _, _ =>
      match chooseNaN2 x y with
      | some nan => nan
      | none =>
          if isInf x then
            if isInf y then
              if signBit x == signBit y then x else invalidResult fmt
            else
              x
          else if isInf y then
            y
          else
            invalidResult fmt

/--
Subtraction as addition of the negated right operand.

`neg` toggles the stored sign bit of every word in a signed-zero format, so a NaN propagated from
`y` is returned with its sign bit flipped relative to `y`. IEEE 754-2019 Section 6.3 leaves the
sign of a NaN result unspecified, so this sign choice is allowed. Callers comparing NaN words
bit for bit should not expect `sub x y` to return `y`'s NaN unchanged. In the finite-unsigned-zero
encoding `neg` leaves the NaN word unchanged, so no flip occurs there. The dispatched `Model.sub`
and its backends are proved equal to this definition, so the convention is shared by every format.
-/
@[inline] def sub {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  add x (neg y)

/-! ## Multiplication -/

/-- Exact dyadic multiplication followed by nearest-even rounding in the destination descriptor. -/
@[inline] def mul {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  match toDyadicOption x, toDyadicOption y with
  | some dx, some dy =>
      let sign := Bool.xor dx.negative dy.negative
      if dx.significand == 0 || dy.significand == 0 then
        zero fmt sign
      else
        roundDyadic fmt
          { negative := sign
            significand := dx.significand * dy.significand
            exponent := dx.exponent + dy.exponent }
  | _, _ =>
      match chooseNaN2 x y with
      | some nan => nan
      | none =>
          if isInf x then
            if isZero y then invalidResult fmt
            else nativeOverflow fmt (signBit x != signBit y)
          else if isInf y then
            if isZero x then invalidResult fmt
            else nativeOverflow fmt (signBit x != signBit y)
          else
            invalidResult fmt

/-! ## Fused multiply-add -/

/-- Exact `(x * y) + z` followed by one nearest-even destination rounding. -/
@[inline] def fma {fmt : FloatFormat} (x y z : Model fmt) : Model fmt :=
  match chooseNaN3 x y z with
  | some nan => nan
  | none =>
      if isInf x || isInf y then
        if isZero x || isZero y then
          invalidResult fmt
        else
          let prodSign := Bool.xor (signBit x) (signBit y)
          let prodInf := nativeOverflow fmt prodSign
          if isInf z then
            if signBit z != prodSign then invalidResult fmt else prodInf
          else
            prodInf
      else if isInf z then
        z
      else
        match toDyadicOption x, toDyadicOption y, toDyadicOption z with
        | some dx, some dy, some dz =>
            let product : Numerics.Dyadic :=
              { negative := Bool.xor dx.negative dy.negative
                significand := dx.significand * dy.significand
                exponent := dx.exponent + dy.exponent }
            roundDyadic fmt (addDyadic product dz)
        | _, _, _ => invalidResult fmt

end FloatLib.Floats.Formats.BinaryInterchange.Model.Spec
