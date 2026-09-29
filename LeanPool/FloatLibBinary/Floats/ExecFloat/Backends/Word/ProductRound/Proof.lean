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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.ProductRound.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Core.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Shared proof for finishing a native-word product

The one-word and two-word multiplication kernels differ in how they form and round an exact
product. Once they have a rounded `UInt64` significand, however, carry handling, overflow testing,
and field packing are identical. This module proves that common final stage once.

The theorem is deliberately about the finishing stage only. Product construction remains in each
backend, where the machine representation and its capacity bounds are materially different.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeWordProduct

open NativeSmallWord

/--
The word-valued finishing function decodes to the optional finishing function.

The only condition on the caller's decline marker is that it lies above every valid packed word.
-/
theorem finishWord_decode
    (fmt : FloatFormat) (hwidth : fmt.bitWidth ≤ 64)
    (decline : UInt64)
    (hdecline : 2 ^ fmt.bitWidth ≤ decline.toNat)
    (sign : Bool) (position rounded : UInt64) :
    (if finishWord fmt decline sign position rounded == decline then
        none
      else
        some <| NativeSmallWord.ofWord <|
          finishWord fmt decline sign position rounded) =
      finishOption fmt sign position rounded := by
  let carry := rounded == carryBit fmt
  let normalizedPosition := if carry then position + 1 else position
  let overflowThreshold :=
    (3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2)
  let normalizedMantissa :=
    if carry then hiddenBit fmt else rounded
  let exponentOffset :=
    (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2)
  let exponent := normalizedPosition - exponentOffset
  let fraction := normalizedMantissa - hiddenBit fmt
  let packed :=
    NativeSmallWord.packFields fmt sign exponent fraction
  change
    (if
        (if overflowThreshold < normalizedPosition then decline else packed) ==
            decline then
      none
    else
      some <| NativeSmallWord.ofWord <|
        if overflowThreshold < normalizedPosition then decline else packed) =
      if overflowThreshold < normalizedPosition then
        none
      else
        some <| NativeSmallWord.ofWord packed
  by_cases hoverflow : overflowThreshold < normalizedPosition
  · simp [hoverflow]
  have hpacked :
      packed ≠ decline := by
    intro heq
    have hbound :=
      NativeSmallWord.packFields_toNat_lt
        hwidth sign exponent fraction
    have heqNat := congrArg UInt64.toNat heq
    unfold packed at heqNat
    omega
  simp [hoverflow, hpacked]

/--
Native carry, overflow, and packing agree with the natural-number normal-result specification.

Callers supply the representation facts for their product implementation: the natural values of
the position and rounded significand, the no-wrap fact for incrementing the position, and the
implicit and carry bits as machine words. The overflow threshold and exponent offset are computed
from `biasWord`, whose value follows from the width bound alone.
-/
theorem finish_eq
    (fmt : FloatFormat) (hwidth : fmt.bitWidth ≤ 64)
    (sign : Bool) (position rounded : UInt64)
    (positionNat roundedNat : Nat)
    (hposition : position.toNat = positionNat)
    (hpositionAdd : (position + 1).toNat = positionNat + 1)
    (hrounded : rounded.toNat = roundedNat)
    (hnormal :
      fmt.bias + 2 * fmt.fracWidth - 1 ≤ positionNat)
    (hhidden :
      (hiddenBit fmt).toNat = 2 ^ fmt.fracWidth)
    (hcarryBit :
      (carryBit fmt).toNat = 2 ^ (fmt.fracWidth + 1))
    (hroundedLower :
      2 ^ fmt.fracWidth ≤ roundedNat) :
    finishOption fmt sign position rounded =
      (let carry := roundedNat = pow2 (fmt.fracWidth + 1)
       let normalizedPosition :=
         if carry then positionNat + 1 else positionNat
       let overflowThreshold :=
         3 * fmt.bias + 2 * fmt.fracWidth - 2
       if overflowThreshold < normalizedPosition then
         none
       else
         let normalizedMantissa :=
           if carry then pow2 fmt.fracWidth else roundedNat
         let exponentOffset :=
           fmt.bias + 2 * fmt.fracWidth - 2
         some <| ofFields fmt sign
           (normalizedPosition - exponentOffset)
           (normalizedMantissa - pow2 fmt.fracWidth)) := by
  unfold finishOption
  dsimp only
  have hcarry :
      (rounded == carryBit fmt) =
        (roundedNat == 2 ^ (fmt.fracWidth + 1)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    rw [← UInt64.toNat_inj, hrounded, hcarryBit]
  rw [hcarry]
  let carry := roundedNat = 2 ^ (fmt.fracWidth + 1)
  let normalizedPositionWord :=
    if rounded == carryBit fmt then position + 1 else position
  let normalizedPositionNat :=
    if carry then positionNat + 1 else positionNat
  have hnormalizedPosition :
      normalizedPositionWord.toNat = normalizedPositionNat := by
    unfold normalizedPositionWord normalizedPositionNat carry
    by_cases hc : roundedNat = 2 ^ (fmt.fracWidth + 1)
    · have hcarryTrue : (rounded == carryBit fmt) = true := by
        rw [hcarry]
        simp [hc]
      rw [ite_eq_left hcarryTrue, ite_eq_left hc, hpositionAdd]
    · have hcarryFalse : ¬(rounded == carryBit fmt) = true := by
        rw [hcarry]
        simp [hc]
      rw [ite_eq_right hcarryFalse, ite_eq_right hc, hposition]
  have hoverflowThreshold :
      (3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2).toNat =
        3 * fmt.bias + 2 * fmt.fracWidth - 2 :=
    overflowThreshold_toNat hwidth
  have hnormalizedPositionWordDef :
      (if (roundedNat == 2 ^ (fmt.fracWidth + 1)) = true then
          position + 1
        else position) = normalizedPositionWord := by
    unfold normalizedPositionWord
    rw [hcarry]
  have hnormalizedPositionNatDef :
      (if roundedNat = pow2 (fmt.fracWidth + 1) then
          positionNat + 1
        else positionNat) = normalizedPositionNat := by
    unfold normalizedPositionNat carry
    rw [pow2_eq_two_pow]
  rw [hnormalizedPositionWordDef, hnormalizedPositionNatDef]
  have hoverflowWordIff :
      (3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2) <
          normalizedPositionWord ↔
        3 * fmt.bias + 2 * fmt.fracWidth - 2 <
          normalizedPositionNat := by
    rw [UInt64.lt_iff_toNat_lt, hoverflowThreshold,
      hnormalizedPosition]
  by_cases hoverflow :
      3 * fmt.bias + 2 * fmt.fracWidth - 2 <
        normalizedPositionNat
  · rw [ite_eq_left (hoverflowWordIff.mpr hoverflow),
      ite_eq_left hoverflow]
  rw [ite_eq_right (fun h => hoverflow (hoverflowWordIff.mp h)),
    ite_eq_right hoverflow]
  let normalizedMantissaWord :=
    if rounded == carryBit fmt then hiddenBit fmt else rounded
  let normalizedMantissaNat :=
    if carry then 2 ^ fmt.fracWidth else roundedNat
  have hnormalizedMantissa :
      normalizedMantissaWord.toNat = normalizedMantissaNat := by
    unfold normalizedMantissaWord normalizedMantissaNat carry
    by_cases hc : roundedNat = 2 ^ (fmt.fracWidth + 1)
    · have hword : rounded = carryBit fmt := by
        apply UInt64.toNat_inj.mp
        rw [hrounded, hcarryBit, hc]
      have hcarryTrue : (rounded == carryBit fmt) = true := by
        simp [hword]
      rw [ite_eq_left hcarryTrue, ite_eq_left hc, hhidden]
    · have hword : rounded ≠ carryBit fmt := by
        intro heq
        apply hc
        have hnat := congrArg UInt64.toNat heq
        simpa [hrounded, hcarryBit] using hnat
      have hcarryFalse : ¬(rounded == carryBit fmt) = true := by
        simp [hword]
      rw [ite_eq_right hcarryFalse, ite_eq_right hc, hrounded]
  have hexponentOffset :
      (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2).toNat =
        fmt.bias + 2 * fmt.fracWidth - 2 :=
    exponentOffset_toNat hwidth
  have hexponentLe :
      (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2) ≤
        normalizedPositionWord := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hexponentOffset, hnormalizedPosition]
    unfold normalizedPositionNat carry
    split <;> omega
  have hexponent :
      (normalizedPositionWord -
          (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2)).toNat =
        normalizedPositionNat -
          (fmt.bias + 2 * fmt.fracWidth - 2) := by
    rw [UInt64.toNat_sub_of_le _ _ hexponentLe,
      hnormalizedPosition, hexponentOffset]
  have hfractionLe :
      hiddenBit fmt ≤ normalizedMantissaWord := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hhidden, hnormalizedMantissa]
    unfold normalizedMantissaNat carry
    split <;> omega
  have hfraction :
      (normalizedMantissaWord - hiddenBit fmt).toNat =
        normalizedMantissaNat - 2 ^ fmt.fracWidth := by
    rw [UInt64.toNat_sub_of_le _ _ hfractionLe,
      hnormalizedMantissa, hhidden]
  have hnormalizedMantissaWordDef :
      (if (roundedNat == 2 ^ (fmt.fracWidth + 1)) = true then
          hiddenBit fmt
        else rounded) = normalizedMantissaWord := by
    unfold normalizedMantissaWord
    rw [hcarry]
  have hnormalizedMantissaNatDef :
      (if roundedNat = pow2 (fmt.fracWidth + 1) then
          pow2 fmt.fracWidth
        else roundedNat) = normalizedMantissaNat := by
    unfold normalizedMantissaNat carry
    simp only [pow2_eq_two_pow]
  rw [hnormalizedMantissaWordDef, hnormalizedMantissaNatDef]
  rw [NativeSmallWord.ofWord_packFields hwidth]
  rw [hexponent, hfraction]
  simp only [pow2_eq_two_pow]

end Model.NativeWordProduct
end FloatLib.Floats.Formats.BinaryInterchange
