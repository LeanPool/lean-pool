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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ProductRound.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Core.Proof

/-!
# Shared proofs for native normal operand pairs

Several one-word kernels begin with the same operation: reject zero, subnormal, and exceptional
operands, then expose two normalized significands and their biased exponents. The executable
decoder remains in `Small.Core.Runtime`; this module proves its common contract once.

`View` records the exact generic decoder results together with the bounds needed by fixed-word
rounders. Multiplication and division can therefore focus on their different arithmetic without
repeating storage-field and exceptional-value arguments. No executable definition depends on this
proof layer.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeNormalPair

open NativeSmallWord

/-- Proof-facing view of two successfully decoded normal operands. -/
structure View {fmt : FloatFormat} (x y : Model fmt) where
  /-- XOR of the operand signs, as supplied to multiplicative kernels. -/
  sign : Bool
  /-- Biased exponent of the left operand. -/
  xExponent : UInt64
  /-- Biased exponent of the right operand. -/
  yExponent : UInt64
  /-- Normalized significand of the left operand. -/
  xMantissa : UInt64
  /-- Normalized significand of the right operand. -/
  yMantissa : UInt64
  /-- The native sign calculation agrees with the model fields. -/
  sign_eq :
    sign = Bool.xor (Model.signBit x) (Model.signBit y)
  /-- The generic finite decoder sees the same left operand fields. -/
  xDecode :
    FiniteKernel.decodeOption x =
      some {
        sign := Model.signBit x
        exponent := xExponent.toNat
        mantissa := xMantissa.toNat }
  /-- The generic finite decoder sees the same right operand fields. -/
  yDecode :
    FiniteKernel.decodeOption y =
      some {
        sign := Model.signBit y
        exponent := yExponent.toNat
        mantissa := yMantissa.toNat }
  /-- The left biased exponent is a nonzero stored exponent. -/
  xExponentBounds :
    0 < xExponent.toNat ∧ xExponent.toNat < 2 ^ fmt.expWidth
  /-- The right biased exponent is a nonzero stored exponent. -/
  yExponentBounds :
    0 < yExponent.toNat ∧ yExponent.toNat < 2 ^ fmt.expWidth
  /-- The left significand has its implicit leading bit. -/
  xMantissaBounds :
    2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧
      xMantissa.toNat < 2 ^ (fmt.fracWidth + 1)
  /-- The right significand has its implicit leading bit. -/
  yMantissaBounds :
    2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧
      yMantissa.toNat < 2 ^ (fmt.fracWidth + 1)

/-- A native normal field decode agrees with the generic finite decoder. -/
theorem decode_normal {fmt : FloatFormat}
    (hieee : fmt.isIEEE = true)
    (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt)
    (hnonzero :
      NativeSmallWord.exponentField fmt (NativeSmallWord.toWord x) ≠ 0)
    (hnonexceptional :
      NativeSmallWord.exponentField fmt (NativeSmallWord.toWord x) ≠
        NativeSmallWord.exponentMask fmt) :
    FiniteKernel.decodeOption x =
      some {
        sign := Model.signBit x
        exponent :=
          (NativeSmallWord.exponentField fmt
            (NativeSmallWord.toWord x)).toNat
        mantissa :=
          (NativeSmallWord.fractionField fmt
              (NativeSmallWord.toWord x) |||
            NativeSmallWord.hiddenBit fmt).toNat } := by
  have hexponent :
      (NativeSmallWord.exponentField fmt
          (NativeSmallWord.toWord x)).toNat =
        Model.expField x :=
    NativeSmallWord.exponentField_toNat hwidth x
  have hallOnes :
      (NativeSmallWord.exponentMask fmt).toNat =
        fmt.expAllOnesNat :=
    NativeSmallWord.exponentMask_toNat hwidth
  have hgenericNonzero : Model.expField x ≠ 0 := by
    intro h
    apply hnonzero
    apply UInt64.toNat_inj.mp
    rw [hexponent, h]
    rfl
  have hgenericFinite :
      Model.expField x ≠ fmt.expAllOnesNat := by
    intro h
    apply hnonexceptional
    apply UInt64.toNat_inj.mp
    rw [hexponent, hallOnes]
    exact h
  have hencoding : fmt.encoding = .ieee :=
    ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
  have hnonfinite :
      (!Model.isFinite x) =
        (Model.expField x == fmt.expAllOnesNat) := by
    simp [Model.isFinite, hencoding, Model.IEEE.isFinite, bne]
  unfold FiniteKernel.decodeOption
  rw [hnonfinite]
  simp only [beq_iff_eq, hgenericFinite, ite_false,
    FiniteKernel.decodeMantissa, hgenericNonzero]
  rw [← hexponent]
  simp only [Model.pow2_eq_two_pow]
  rw [← NativeSmallWord.normalMantissa_toNat_of_width hwidth x]

/--
Extract the shared proof view from a successful native normal-pair callback.

The callback itself remains fully generic. Its caller receives the exact fields passed at runtime,
their normalized bounds, and decoder equalities suitable for any binary operation.
-/
theorem view_of_success
    {fmt : FloatFormat} {α : Type}
    (hieee : fmt.isIEEE = true)
    (hwidth : fmt.bitWidth ≤ 64)
    (x y : Model fmt)
    (kernel :
      Bool → UInt64 → UInt64 → UInt64 → UInt64 → Option α)
    (result : α)
    (hresult :
      NativeSmallWord.withNormalPairOption x y kernel = some result) :
    ∃ view : View x y,
      kernel view.sign view.xExponent view.yExponent
          view.xMantissa view.yMantissa =
        some result := by
  let xBits := NativeSmallWord.toWord x
  let yBits := NativeSmallWord.toWord y
  let xExponent := NativeSmallWord.exponentField fmt xBits
  let yExponent := NativeSmallWord.exponentField fmt yBits
  let allOnes := NativeSmallWord.exponentMask fmt
  let xMantissa :=
    NativeSmallWord.fractionField fmt xBits ||| hiddenBit fmt
  let yMantissa :=
    NativeSmallWord.fractionField fmt yBits ||| hiddenBit fmt
  let sign :=
    Bool.xor
      (NativeSmallWord.signField fmt xBits)
      (NativeSmallWord.signField fmt yBits)
  by_cases hxZero : xExponent = 0
  · simp [NativeSmallWord.withNormalPairOption,
      xBits, xExponent, hxZero] at hresult
  by_cases hxExceptional : xExponent = allOnes
  · simp [NativeSmallWord.withNormalPairOption,
      xBits, xExponent, allOnes, hxExceptional] at hresult
  by_cases hyZero : yExponent = 0
  · simp [NativeSmallWord.withNormalPairOption,
      yBits, yExponent, hyZero] at hresult
  by_cases hyExceptional : yExponent = allOnes
  · simp [NativeSmallWord.withNormalPairOption,
      yBits, yExponent, allOnes, hyExceptional] at hresult
  have hkernel :
      kernel sign xExponent yExponent xMantissa yMantissa =
        some result := by
    simpa [NativeSmallWord.withNormalPairOption,
      xBits, yBits, xExponent, yExponent, allOnes, xMantissa,
      yMantissa, sign, hxZero, hxExceptional, hyZero, hyExceptional] using
      hresult
  have hsign :
      sign = Bool.xor (Model.signBit x) (Model.signBit y) := by
    dsimp only [sign, xBits, yBits]
    rw [NativeSmallWord.signField_eq hwidth x,
      NativeSmallWord.signField_eq hwidth y]
  have hxDecode :
      FiniteKernel.decodeOption x =
        some {
          sign := Model.signBit x
          exponent := xExponent.toNat
          mantissa := xMantissa.toNat } := by
    simpa [xExponent, xMantissa, xBits, allOnes] using
      decode_normal hieee hwidth x
        (by simpa [xExponent, xBits] using hxZero)
        (by simpa [xExponent, xBits, allOnes] using hxExceptional)
  have hyDecode :
      FiniteKernel.decodeOption y =
        some {
          sign := Model.signBit y
          exponent := yExponent.toNat
          mantissa := yMantissa.toNat } := by
    simpa [yExponent, yMantissa, yBits, allOnes] using
      decode_normal hieee hwidth y
        (by simpa [yExponent, yBits] using hyZero)
        (by simpa [yExponent, yBits, allOnes] using hyExceptional)
  have hxExponentBounds :
      0 < xExponent.toNat ∧ xExponent.toNat < 2 ^ fmt.expWidth := by
    simpa [xExponent, xBits] using
      NativeSmallWord.exponentField_bounds_of_ne_zero hwidth x (by
        simpa [xExponent, xBits] using hxZero)
  have hyExponentBounds :
      0 < yExponent.toNat ∧ yExponent.toNat < 2 ^ fmt.expWidth := by
    simpa [yExponent, yBits] using
      NativeSmallWord.exponentField_bounds_of_ne_zero hwidth y (by
        simpa [yExponent, yBits] using hyZero)
  have hxMantissaBounds :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧
        xMantissa.toNat < 2 ^ (fmt.fracWidth + 1) := by
    simpa [xMantissa, xBits] using
      NativeSmallWord.normalMantissa_bounds_of_width hwidth x
  have hyMantissaBounds :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧
        yMantissa.toNat < 2 ^ (fmt.fracWidth + 1) := by
    simpa [yMantissa, yBits] using
      NativeSmallWord.normalMantissa_bounds_of_width hwidth y
  exact ⟨{
    sign
    xExponent
    yExponent
    xMantissa
    yMantissa
    sign_eq := hsign
    xDecode := hxDecode
    yDecode := hyDecode
    xExponentBounds := hxExponentBounds
    yExponentBounds := hyExponentBounds
    xMantissaBounds := hxMantissaBounds
    yMantissaBounds := hyMantissaBounds }, hkernel⟩

/--
Lift a certified normal-product callback to the generic finite multiplication kernel.

The shared view handles native decoding. The callback hypothesis is responsible only for the
product representation and its final rounding.
-/
theorem mul_refines
    {fmt : FloatFormat}
    (hieee : fmt.isIEEE = true)
    (hwidth : fmt.bitWidth ≤ 64)
    (kernel :
      Bool → UInt64 → UInt64 → UInt64 → UInt64 →
        Option (Model fmt))
    (kernel_refines :
      ∀ (sign : Bool)
        (xExponent yExponent xMantissa yMantissa : UInt64)
        (result : Model fmt),
        (0 < xExponent.toNat ∧
          xExponent.toNat < 2 ^ fmt.expWidth) →
        (0 < yExponent.toNat ∧
          yExponent.toNat < 2 ^ fmt.expWidth) →
        (2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧
          xMantissa.toNat < 2 ^ (fmt.fracWidth + 1)) →
        (2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧
          yMantissa.toNat < 2 ^ (fmt.fracWidth + 1)) →
        kernel sign xExponent yExponent xMantissa yMantissa =
          some result →
        result =
          FiniteProductRound.round fmt sign
            (xMantissa.toNat * yMantissa.toNat)
            ((xExponent.toNat - 1) + (yExponent.toNat - 1)))
    (x y result : Model fmt)
    (hresult : NativeSmallWord.withNormalPairOption x y kernel = some result) :
    FiniteKernel.mulOption x y = some result := by
  rcases view_of_success hieee hwidth x y kernel result hresult with
    ⟨view, hkernel⟩
  have hrefines :=
    kernel_refines view.sign view.xExponent view.yExponent
      view.xMantissa view.yMantissa result
      view.xExponentBounds view.yExponentBounds
      view.xMantissaBounds view.yMantissaBounds hkernel
  have hxMantissaNe : view.xMantissa.toNat ≠ 0 := by
    exact Nat.ne_of_gt <|
      (Nat.two_pow_pos fmt.fracWidth).trans_le
        view.xMantissaBounds.1
  have hyMantissaNe : view.yMantissa.toNat ≠ 0 := by
    exact Nat.ne_of_gt <|
      (Nat.two_pow_pos fmt.fracWidth).trans_le
        view.yMantissaBounds.1
  unfold FiniteKernel.mulOption
  rw [view.xDecode, view.yDecode]
  simp only
  rw [ite_eq_right (by simp [hxMantissaNe, hyMantissaNe])]
  rw [ite_eq_left hieee]
  apply congrArg some
  simp only [FiniteKernel.scale, beq_iff_eq,
    view.xExponentBounds.1.ne', view.yExponentBounds.1.ne', ite_false]
  rw [← view.sign_eq]
  exact hrefines.symm

end Model.NativeNormalPair
end FloatLib.Floats.Formats.BinaryInterchange
