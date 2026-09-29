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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Finite.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Base.Runtime

/-!
# Correctness of finite binary32 components

The representation lemmas here establish field bounds and connect runtime mantissa-and-scale
coordinates to the generic exact-dyadic decoder. Binary32 word proofs for addition,
multiplication, division, square root, and fused operations all reuse this boundary.

Runtime clients can import `Finite.Runtime` without these proofs. The operation proofs reuse the
same field bounds and mantissa-scale decoding theorem.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- A decoded binary32 fraction fits in its 23-bit field. -/
theorem fracField_lt (x : Value) :
    (fracField (toUInt32 x)).toNat < 2 ^ 23 := by
  change Model.fracField x < 2 ^ 23
  simpa only [show FloatFormat.binary32.fracWidth = 23 by decide] using
    Model.fracField_lt_pow2 x

/-- A decoded binary32 exponent fits in its eight-bit field. -/
theorem expField_lt (x : Value) :
    (expField (toUInt32 x)).toNat < 2 ^ 8 := by
  change Model.expField x < 2 ^ 8
  simpa only [show FloatFormat.binary32.expWidth = 8 by decide] using
    Model.expField_lt_pow2 x

/-- Interpret the native finite mantissa as an ordinary natural number. -/
theorem finiteMantissa_toNat
    (exponent fraction : UInt32) (hfraction : fraction.toNat < 2 ^ 23) :
    (finiteMantissa exponent fraction).toNat =
      if exponent = 0 then fraction.toNat else Model.pow2 23 + fraction.toNat := by
  by_cases hexponent : exponent = 0
  · simp [finiteMantissa, hexponent]
  · simp only [finiteMantissa, beq_iff_eq, hexponent, ite_false, UInt64.toNat_or,
      UInt32.toNat_toUInt64]
    rw [show (0x800000 : UInt64).toNat = 2 ^ 23 by decide]
    rw [Nat.or_two_pow_eq_add_of_lt hfraction]
    rw [Model.pow2_eq_two_pow, Nat.add_comm]

/-- Every finite binary32 mantissa fits in 24 bits. -/
theorem finiteMantissa_lt
    (exponent fraction : UInt32) (hfraction : fraction.toNat < 2 ^ 23) :
    (finiteMantissa exponent fraction).toNat < 2 ^ 24 := by
  rw [finiteMantissa_toNat exponent fraction hfraction]
  split
  · omega
  · rw [Model.pow2_eq_two_pow]
    omega

/-- Interpret the native finite scale as an ordinary natural number. -/
theorem finiteScale_toNat (exponent : UInt32) :
    (finiteScale exponent).toNat =
      if exponent = 0 then 0 else exponent.toNat - 1 := by
  by_cases hexponent : exponent = 0
  · subst exponent
    simp [finiteScale, FloatLib.Numerics.FixedWord.finiteScale]
  · have hwidened : exponent.toUInt64 ≠ 0 := by
      intro hzero
      apply hexponent
      apply UInt32.toNat_inj.mp
      have := congrArg UInt64.toNat hzero
      simpa using this
    rw [finiteScale, FloatLib.Numerics.FixedWord.finiteScale_toNat]
    simp [hexponent, hwidened]

/-- Every finite binary32 scale is at most 253. -/
theorem finiteScale_le
    (exponent : UInt32) (hexponent : exponent.toNat < 2 ^ 8)
    (hfinite : exponent ≠ 0xff) :
    (finiteScale exponent).toNat ≤ 253 := by
  rw [finiteScale_toNat]
  split
  · omega
  · have hnot255 : exponent.toNat ≠ 255 := by
      intro h
      apply hfinite
      apply UInt32.toNat_inj.mp
      simpa using h
    omega

/--
The mantissa decoded directly from a binary32 value fits in the 24 bits used by the native
finite-operation kernels.

Operation proofs should normally use this value-level lemma. The component-level
`finiteMantissa_lt` theorem remains available when a proof constructs fields independently.
-/
theorem finiteMantissa_lt_of_value (x : Value) :
    (finiteMantissa
      (expField (toUInt32 x))
      (fracField (toUInt32 x))).toNat < 2 ^ 24 :=
  finiteMantissa_lt
    (expField (toUInt32 x))
    (fracField (toUInt32 x))
    (fracField_lt x)

/--
The scale decoded from a finite binary32 value is at most 253.

This is the value-level counterpart of `finiteScale_le`; it keeps field-width bookkeeping out of
the individual arithmetic proofs.
-/
theorem finiteScale_le_of_value (x : Value)
    (hfinite : expField (toUInt32 x) ≠ 0xff) :
    (finiteScale (expField (toUInt32 x))).toNat ≤ 253 :=
  finiteScale_le
    (expField (toUInt32 x))
    (expField_lt x)
    hfinite

/--
The 24-bit mantissa bound also holds for components identified with a value's decoded fields.
-/
theorem finiteMantissa_lt_of_components
    (x : Value) {exponent fraction : UInt32} {mantissa : UInt64}
    (hexponent : exponent = expField (toUInt32 x))
    (hfraction : fraction = fracField (toUInt32 x))
    (hmantissa : mantissa = finiteMantissa exponent fraction) :
    mantissa.toNat < 2 ^ 24 := by
  simpa only [hmantissa, hexponent, hfraction] using
    finiteMantissa_lt_of_value x

/--
Transport the value-level finite-scale bound to the local component names used by a word kernel.
-/
theorem finiteScale_le_of_components
    (x : Value) {exponent : UInt32} {scale : UInt64}
    (hexponent : exponent = expField (toUInt32 x))
    (hscale : scale = finiteScale exponent)
    (hfinite : exponent ≠ 0xff) :
    scale.toNat ≤ 253 := by
  apply le_of_eq_of_le (congrArg UInt64.toNat hscale)
  apply finiteScale_le
  · simpa only [hexponent] using expField_lt x
  · simpa only [hexponent] using hfinite

/-- Native finite components decode to the same exact dyadic as the generic binary32 decoder. -/
theorem toDyadic_eq_finiteComponents (x : Value) :
    toDyadicOption (toUInt32 x) =
      let bits := toUInt32 x
      let exponent := expField bits
      let fraction := fracField bits
      if exponent = 0xff then
        none
      else
        let sign := signBit bits
        let mantissa := finiteMantissa exponent fraction
        let scale := finiteScale exponent
        if mantissa = 0 then
          some ({ negative := sign, significand := 0, exponent := 0 } : Numerics.Dyadic)
        else
          some ({
            negative := sign
            significand := mantissa.toNat
            exponent := Int.ofNat scale.toNat - 149 } : Numerics.Dyadic) := by
  unfold toDyadicOption
  dsimp only
  generalize hexponentDef : expField (toUInt32 x) = exponent
  generalize hfractionDef : fracField (toUInt32 x) = fraction
  have hfraction : fraction.toNat < 2 ^ 23 := by
    rw [← hfractionDef]
    exact fracField_lt x
  by_cases hexceptional : exponent = 0xff
  · simp [hexceptional]
  · simp only [hexceptional, beq_iff_eq, ite_false]
    by_cases hexponentZero : exponent = 0
    · simp only [hexponentZero, beq_iff_eq, ite_eq_left, finiteMantissa, finiteScale,
        FloatLib.Numerics.FixedWord.finiteScale]
      have htoUInt64Zero : fraction.toUInt64 = 0 ↔ fraction = 0 := by
        constructor
        · intro h
          apply UInt32.toNat_inj.mp
          have := congrArg UInt64.toNat h
          simpa using this
        · intro h
          apply UInt64.toNat_inj.mp
          simp [h]
      by_cases hfractionZero : fraction = 0
      · simp [hfractionZero]
      · have htoUInt64Nonzero : fraction.toUInt64 ≠ 0 :=
          (not_congr htoUInt64Zero).mpr hfractionZero
        simp only [hfractionZero, ite_false, htoUInt64Nonzero,
          UInt32.toNat_toUInt64]
        rfl
    · simp only [hexponentZero, beq_iff_eq, ite_false, finiteMantissa]
      have hmantissa :
          (fraction.toUInt64 ||| 0x800000).toNat =
            Model.pow2 23 + fraction.toNat := by
        simpa [finiteMantissa, hexponentZero] using
          finiteMantissa_toNat exponent fraction hfraction
      have hmantissaNonzero : fraction.toUInt64 ||| 0x800000 ≠ 0 := by
        intro h
        have := congrArg UInt64.toNat h
        rw [hmantissa] at this
        simp [Model.pow2_eq_two_pow] at this
      rw [ite_eq_right hmantissaNonzero]
      rw [hmantissa]
      have hexponentNat : exponent.toNat ≠ 0 := by
        intro h
        apply hexponentZero
        apply UInt32.toNat_inj.mp
        simpa using h
      rw [finiteScale_toNat exponent, ite_eq_right hexponentZero]
      congr 2
      have hexponentNatOne : 1 ≤ exponent.toNat :=
        Nat.one_le_iff_ne_zero.mpr hexponentNat
      have hpred := Nat.sub_add_cancel hexponentNatOne
      conv_lhs => rw [← hpred]
      simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
      omega

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
