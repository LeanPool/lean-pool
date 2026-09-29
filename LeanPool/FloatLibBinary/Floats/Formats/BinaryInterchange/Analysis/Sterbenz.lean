/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette, FloatLib Team
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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Analysis.SterbenzFLT
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Subtraction
public import Mathlib.Algebra.Order.Algebra

/-!
# Sterbenz exact subtraction

Sterbenz's lemma applies to the rounded-real grid of every `fmt`: two positive representable
values within a factor of two have an exactly representable difference. For an IEEE descriptor,
subtraction of the corresponding finite model values remains finite and decodes to that exact
real difference.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

/--
Sterbenz exactness for the rounded-real grid selected by `fmt`: two positive representable reals
within a factor of two have a representable difference, so nearest-even rounding changes nothing.

Strict positivity excludes signed-zero bookkeeping; the executable theorem below handles the
corresponding finite model values.
-/
theorem roundAt_sub_eq_of_sterbenz (fmt : FloatFormat) {u v : ℝ}
    (hu : genericFormat Numerics.binaryRadix (fexpOf fmt) u)
    (hv : genericFormat Numerics.binaryRadix (fexpOf fmt) v)
    (hupos : 0 < u) (hvpos : 0 < v)
    (huv : u ≤ 2 * v) (hvu : v ≤ 2 * u) :
    roundAt fmt (u - v) = u - v := by
  have hprec : (0 : Int) < Int.ofNat (fmt.fracWidth + 1) :=
    Int.natCast_pos.mpr (Nat.succ_pos fmt.fracWidth)
  have hfmt : genericFormat Numerics.binaryRadix (fexpOf fmt) (u - v) := by
    simpa [fexpOf] using
      (generic_format_FLT_sterbenz
        (β := Numerics.binaryRadix)
        (FloatFormat.minSubnormalExponent fmt)
        (Int.ofNat (fmt.fracWidth + 1))
        hprec hupos hvpos huv hvu hu hv)
  exact round_preserves_generic nearestEven (u - v) hfmt

/--
Subtraction of positive finite executable values within a factor of two has no rounding error.

The Sterbenz hypotheses also bound the exact difference by one of the finite operands, so
finiteness of the executable result follows rather than appearing as a separate premise.
-/
theorem toReal_sub_eq_of_sterbenz {fmt : FloatFormat} {x y : Model fmt}
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hxpos : 0 < toReal x) (hypos : 0 < toReal y)
    (hxy : toReal x ≤ 2 * toReal y) (hyx : toReal y ≤ 2 * toReal x) :
    toReal (sub x y) = toReal x - toReal y := by
  have hoperandBound :
      max (toReal x) (toReal y) ≤ toReal (posMaxFinite fmt) := by
    apply max_le
    · have hxBound :=
        abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite x hfmt hx
      simpa [abs_of_pos hxpos] using hxBound
    · have hyBound :=
        abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite y hfmt hy
      simpa [abs_of_pos hypos] using hyBound
  have hdifferenceBound :
      |toReal x - toReal y| ≤ toReal (posMaxFinite fmt) := by
    apply le_trans (b := max (toReal x) (toReal y))
    · by_cases horder : toReal x ≤ toReal y
      · rw [abs_of_nonpos (sub_nonpos.mpr horder)]
        simpa only [neg_sub] using
          (sub_le_self (toReal y) hxpos.le).trans
            (le_max_right (toReal x) (toReal y))
      · have hreverse : toReal y ≤ toReal x :=
          (lt_of_not_ge horder).le
        rw [abs_of_nonneg (sub_nonneg.mpr hreverse)]
        exact (sub_le_self _ hypos.le).trans (le_max_left _ _)
    · exact hoperandBound
  have hout : isFinite (sub x y) = true :=
    isFinite_sub_of_abs_toReal_sub_le_posMaxFinite
      x y hfmt hx hy hdifferenceBound
  rw [toReal_sub_eq_roundAt x y hfmt hx hy hout]
  exact roundAt_sub_eq_of_sterbenz fmt
    (toReal_genericFormat_of_isFinite x hx)
    (toReal_genericFormat_of_isFinite y hy)
    hxpos hypos hxy hyx

end Model
end FloatLib.Floats.Formats.BinaryInterchange
