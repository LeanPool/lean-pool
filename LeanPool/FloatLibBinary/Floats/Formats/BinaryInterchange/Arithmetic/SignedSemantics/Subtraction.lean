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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.Semantics

/-!
# Correctness of binary subtraction

Subtraction is implemented as addition of the negated right operand. These theorems connect that
implementation to exact real subtraction followed by one nearest-even rounding step.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Finite operands whose exact real difference is within the destination's largest finite magnitude
cannot overflow under nearest-even subtraction.
-/
theorem isFinite_sub_of_abs_toReal_sub_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x - toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (sub x y) = true := by
  have hyneg : isFinite (neg y) = true := by simpa using hy
  have hsub : sub x y = add x (neg y) := by
    calc
      sub x y = Spec.sub x y := Proof.sub_eq_spec x y
      _ = Spec.add x (neg y) := rfl
      _ = add x (neg y) := by
        exact (Proof.add_eq_spec x (neg y)).symm
  rw [hsub]
  apply isFinite_add_of_abs_toReal_add_le_posMaxFinite x (neg y) hfmt hx hyneg
  rw [toReal_neg y hy]
  simpa [sub_eq_add_neg] using hbound

/--
The triangle bound `|x| + |y| ≤ maxFinite` is a symbolic sufficient condition for finite
nearest-even subtraction.
-/
theorem isFinite_sub_of_abs_add_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x| + |toReal y| ≤ toReal (posMaxFinite fmt)) :
    isFinite (sub x y) = true := by
  apply isFinite_sub_of_abs_toReal_sub_le_posMaxFinite x y hfmt hx hy
  calc
    |toReal x - toReal y| = |toReal x + -toReal y| := by ring_nf
    _ ≤ |toReal x| + |-toReal y| := abs_add_le _ _
    _ = |toReal x| + |toReal y| := by rw [abs_neg]
    _ ≤ toReal (posMaxFinite fmt) := hbound

/--
Finite subtraction is exact real subtraction followed by one nearest-even format rounding.

The hypothesis `hfin` excludes overflow by asking that the executable difference be finite;
`toReal_sub_eq_roundAt_of_abs_add_le_posMaxFinite` supplies it from a bound on the operands.
-/
theorem toReal_sub_eq_roundAt {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hfin : isFinite (sub x y) = true) :
    toReal (sub x y) = roundAt fmt (toReal x - toReal y) := by
  have hyneg : isFinite (neg y) = true := by simpa using hy
  have hsub : sub x y = add x (neg y) := by
    calc
      sub x y = Spec.sub x y := Proof.sub_eq_spec x y
      _ = Spec.add x (neg y) := rfl
      _ = add x (neg y) := by
        exact (Proof.add_eq_spec x (neg y)).symm
  rw [hsub] at hfin ⊢
  rw [toReal_add_eq_roundAt x (neg y) hfmt hx hyneg hfin, toReal_neg y hy]
  ring_nf

/--
Finite subtraction under a symbolic triangle bound is exact real subtraction followed by one
nearest-even format rounding.
-/
theorem toReal_sub_eq_roundAt_of_abs_add_le_posMaxFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbound : |toReal x| + |toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal (sub x y) = roundAt fmt (toReal x - toReal y) :=
  toReal_sub_eq_roundAt x y hfmt hx hy
    (isFinite_sub_of_abs_add_le_posMaxFinite x y hfmt hx hy hbound)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
