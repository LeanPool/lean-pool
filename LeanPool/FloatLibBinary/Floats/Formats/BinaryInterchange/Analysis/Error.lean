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

public import Mathlib.Algebra.Order.Algebra
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.DivisionSemantics
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.SqrtSemantics
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Subtraction
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Conversion.Cast.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Error.Addition
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Error.Relative

/-!
# Error bounds for executable binary floats

These bounds relate operations on `Model fmt` to exact real arithmetic. The function `toReal`
interprets finite values in `ℝ`, and the format parameter selects the corresponding Flocq-style
grid. This real-valued grid has no upper exponent bound; the executable operation theorems apply
when the result is finite.

The operation theorems require finite inputs and outputs because infinities and NaNs have no
real value. Signed zeros both have real value zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

/-- One unit in the last place at `x` for the precision and gradual-underflow grid of `fmt`. -/
noncomputable abbrev ulpAt (fmt : FloatFormat) (x : ℝ) : ℝ :=
  ulp Numerics.binaryRadix (fexpOf fmt) x

/-- Half an ULP at `x` for the precision and gradual-underflow grid of `fmt`. -/
noncomputable abbrev epsilonAt (fmt : FloatFormat) (x : ℝ) : ℝ :=
  ulpAt fmt x / 2

/-- The least positive normal magnitude of `fmt`. -/
noncomputable abbrev minNormalAt (fmt : FloatFormat) : ℝ :=
  FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
    (FloatFormat.minNormalExponent fmt)

/-- The exponent-selection function of every executable format is monotone. -/
instance (fmt : FloatFormat) : MonotoneExp (fexpOf fmt) := by
  simpa [fexpOf] using
    (fltMonotoneExp (FloatFormat.minSubnormalExponent fmt)
      (Int.ofNat (fmt.fracWidth + 1)))

/--
Nearest-even rounding to `fmt` has at most half an ULP of absolute error.

The format-specific `epsilonAt` follows the subnormal grid near zero, so this statement remains
useful where a uniform relative-error bound is impossible.
-/
theorem abs_roundAt_sub_le (fmt : FloatFormat) (x : ℝ) :
    |roundAt fmt x - x| ≤ epsilonAt fmt x := by
  simpa [roundAt, epsilonAt, ulpAt] using
    (error_bound_ulp
      (β := Numerics.binaryRadix) (fexp := fexpOf fmt) nearestEven x)

/-- The exact real input lies in the half-ULP enclosure around its rounded value. -/
theorem roundAt_mem_Icc (fmt : FloatFormat) (x : ℝ) :
    x ∈ Set.Icc
      (roundAt fmt x - epsilonAt fmt x)
      (roundAt fmt x + epsilonAt fmt x) := by
  have h := (abs_le.mp (abs_roundAt_sub_le fmt x))
  constructor <;> linarith

/--
Normal-range nearest-even rounding has the standard relative error bound
`2^(1-precision) / 2`.
-/
theorem relativeError_roundAt_le_of_normal (fmt : FloatFormat) (x : ℝ)
    (hx : x ≠ 0) (hnormal : minNormalAt fmt ≤ |x|) :
    ErrorBounds.relativeError x (roundAt fmt x) hx ≤
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (1 - Int.ofNat (fmt.fracWidth + 1)) / 2 := by
  have hprec : (0 : Int) < Int.ofNat (fmt.fracWidth + 1) :=
    Int.natCast_pos.mpr (Nat.succ_pos fmt.fracWidth)
  have hexponent :
      FloatFormat.minSubnormalExponent fmt + Int.ofNat (fmt.fracWidth + 1) - 1 =
        FloatFormat.minNormalExponent fmt := by
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
    ring
  have hnormal' :
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (FloatFormat.minSubnormalExponent fmt + Int.ofNat (fmt.fracWidth + 1) - 1) ≤
        |x| := by
    rw [hexponent]
    exact hnormal
  simpa [roundAt, fexpOf] using
    (relative_error_round_FLT_normal
      (β := Numerics.binaryRadix)
      (FloatFormat.minSubnormalExponent fmt)
      (Int.ofNat (fmt.fracWidth + 1))
      hprec nearestEven x hx hnormal')

/-- Absolute error of one finite executable addition. -/
theorem abs_toReal_add_sub_le {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (add x y) = true) :
    |toReal (add x y) - (toReal x + toReal y)| ≤
      epsilonAt fmt (toReal x + toReal y) := by
  rw [toReal_add_eq_roundAt x y hfmt hx hy hout]
  exact abs_roundAt_sub_le fmt (toReal x + toReal y)

/-- Absolute error of one finite executable subtraction. -/
theorem abs_toReal_sub_sub_le {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (sub x y) = true) :
    |toReal (sub x y) - (toReal x - toReal y)| ≤
      epsilonAt fmt (toReal x - toReal y) := by
  rw [toReal_sub_eq_roundAt x y hfmt hx hy hout]
  exact abs_roundAt_sub_le fmt (toReal x - toReal y)

/-- Absolute error of one finite executable multiplication. -/
theorem abs_toReal_mul_sub_le {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (mul x y) = true) :
    |toReal (mul x y) - toReal x * toReal y| ≤
      epsilonAt fmt (toReal x * toReal y) := by
  rw [toReal_mul_eq_roundAt x y hfmt hx hy hout]
  exact abs_roundAt_sub_le fmt (toReal x * toReal y)

/-- Absolute error of one finite executable division by a nonzero divisor. -/
theorem abs_toReal_div_sub_le {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false) (hout : isFinite (div x y) = true) :
    |toReal (div x y) - toReal x / toReal y| ≤
      epsilonAt fmt (toReal x / toReal y) := by
  rw [toReal_div_eq_roundAt x y hfmt hx hy hy0 hout]
  exact abs_roundAt_sub_le fmt (toReal x / toReal y)

/--
Absolute error of one finite executable square root on a nonnegative input, including either
signed zero.
-/
theorem abs_toReal_sqrt_sub_le {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true)
    (hdomain : isZero x = true ∨ signBit x = false) :
    |toReal (sqrt x) - Real.sqrt (toReal x)| ≤
      epsilonAt fmt (Real.sqrt (toReal x)) := by
  rw [toReal_sqrt_eq_roundAt x hfmt hx hdomain]
  exact abs_roundAt_sub_le fmt (Real.sqrt (toReal x))

/-- Absolute error of one finite executable fused multiply-add. -/
theorem abs_toReal_fma_sub_le {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hout : isFinite (fma x y z) = true) :
    |toReal (fma x y z) - (toReal x * toReal y + toReal z)| ≤
      epsilonAt fmt (toReal x * toReal y + toReal z) := by
  rw [toReal_fma_eq_roundAt x y z hfmt hx hy hz hout]
  exact abs_roundAt_sub_le fmt (toReal x * toReal y + toReal z)

/-- Absolute error of one finite cross-format cast. -/
theorem abs_toReal_cast_sub_le {src dst : FloatFormat} (x : Model src)
    (hsrc : src.isIEEE = true) (hdst : dst.isIEEE = true)
    (hx : isFinite x = true) (hout : isFinite (cast src dst x) = true) :
    |toReal (cast src dst x) - toReal x| ≤ epsilonAt dst (toReal x) := by
  rw [cast_eq_roundAt hsrc hdst x hx hout]
  exact abs_roundAt_sub_le dst (toReal x)

/-- The exact sum lies in the half-ULP enclosure around executable addition. -/
theorem add_exact_mem_Icc {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (add x y) = true) :
    toReal x + toReal y ∈ Set.Icc
      (toReal (add x y) - epsilonAt fmt (toReal x + toReal y))
      (toReal (add x y) + epsilonAt fmt (toReal x + toReal y)) := by
  rw [toReal_add_eq_roundAt x y hfmt hx hy hout]
  exact roundAt_mem_Icc fmt (toReal x + toReal y)

/-- The exact difference lies in the half-ULP enclosure around executable subtraction. -/
theorem sub_exact_mem_Icc {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (sub x y) = true) :
    toReal x - toReal y ∈ Set.Icc
      (toReal (sub x y) - epsilonAt fmt (toReal x - toReal y))
      (toReal (sub x y) + epsilonAt fmt (toReal x - toReal y)) := by
  rw [toReal_sub_eq_roundAt x y hfmt hx hy hout]
  exact roundAt_mem_Icc fmt (toReal x - toReal y)

/-- The exact product lies in the half-ULP enclosure around executable multiplication. -/
theorem mul_exact_mem_Icc {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (mul x y) = true) :
    toReal x * toReal y ∈ Set.Icc
      (toReal (mul x y) - epsilonAt fmt (toReal x * toReal y))
      (toReal (mul x y) + epsilonAt fmt (toReal x * toReal y)) := by
  rw [toReal_mul_eq_roundAt x y hfmt hx hy hout]
  exact roundAt_mem_Icc fmt (toReal x * toReal y)

/-- The exact quotient lies in the half-ULP enclosure around executable division. -/
theorem div_exact_mem_Icc {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false) (hout : isFinite (div x y) = true) :
    toReal x / toReal y ∈ Set.Icc
      (toReal (div x y) - epsilonAt fmt (toReal x / toReal y))
      (toReal (div x y) + epsilonAt fmt (toReal x / toReal y)) := by
  rw [toReal_div_eq_roundAt x y hfmt hx hy hy0 hout]
  exact roundAt_mem_Icc fmt (toReal x / toReal y)

/-- The exact square root lies in the half-ULP enclosure around executable square root. -/
theorem sqrt_exact_mem_Icc {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true)
    (hdomain : isZero x = true ∨ signBit x = false) :
    Real.sqrt (toReal x) ∈ Set.Icc
      (toReal (sqrt x) - epsilonAt fmt (Real.sqrt (toReal x)))
      (toReal (sqrt x) + epsilonAt fmt (Real.sqrt (toReal x))) := by
  rw [toReal_sqrt_eq_roundAt x hfmt hx hdomain]
  exact roundAt_mem_Icc fmt (Real.sqrt (toReal x))

/-- The exact multiply-add lies in the half-ULP enclosure around executable FMA. -/
theorem fma_exact_mem_Icc {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hout : isFinite (fma x y z) = true) :
    toReal x * toReal y + toReal z ∈ Set.Icc
      (toReal (fma x y z) - epsilonAt fmt (toReal x * toReal y + toReal z))
      (toReal (fma x y z) + epsilonAt fmt (toReal x * toReal y + toReal z)) := by
  rw [toReal_fma_eq_roundAt x y z hfmt hx hy hz hout]
  exact roundAt_mem_Icc fmt (toReal x * toReal y + toReal z)

/-- The source real value lies in the half-ULP enclosure around a finite cast. -/
theorem cast_exact_mem_Icc {src dst : FloatFormat} (x : Model src)
    (hsrc : src.isIEEE = true) (hdst : dst.isIEEE = true)
    (hx : isFinite x = true) (hout : isFinite (cast src dst x) = true) :
    toReal x ∈ Set.Icc
      (toReal (cast src dst x) - epsilonAt dst (toReal x))
      (toReal (cast src dst x) + epsilonAt dst (toReal x)) := by
  rw [cast_eq_roundAt hsrc hdst x hx hout]
  exact roundAt_mem_Icc dst (toReal x)

/-- The residual of finite nearest-even addition is representable in the same format. -/
theorem genericFormat_toReal_add_sub {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (add x y) = true) :
    genericFormat Numerics.binaryRadix (fexpOf fmt)
      (toReal (add x y) - (toReal x + toReal y)) := by
  rw [toReal_add_eq_roundAt x y hfmt hx hy hout]
  exact add_round_error_generic
    (toReal_genericFormat_of_isFinite x hx)
    (toReal_genericFormat_of_isFinite y hy)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
