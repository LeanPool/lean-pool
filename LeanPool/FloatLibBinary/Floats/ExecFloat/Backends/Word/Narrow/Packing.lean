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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Base.Runtime

/-!
# Native binary32 field-packing identities

The executable field operations live in `Narrow.Base.Runtime`. This module proves that extracting
and
repacking a native binary32 word is lossless, and records the native form of quieting a NaN.

These bit-level identities are shared by addition and fused multiply-add proofs, but do not depend
on either arithmetic operation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

private theorem fractionMask_getLsbD (i : Nat) :
    (8388607#32 : BitVec 32).getLsbD i = decide (i < 23) := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    change (2 ^ 23 - 1).testBit i = decide (i < 23)
    exact Nat.testBit_two_pow_sub_one 23 i
  · have : ¬i < 23 := by omega
    simp [hi, this]

private theorem exponentMask_getLsbD (i : Nat) :
    (255#32 : BitVec 32).getLsbD i = decide (i < 8) := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    change (2 ^ 8 - 1).testBit i = decide (i < 8)
    exact Nat.testBit_two_pow_sub_one 8 i
  · have : ¬i < 8 := by omega
    simp [hi, this]

private theorem signMask_getLsbD (i : Nat) :
    (2147483648#32 : BitVec 32).getLsbD i = decide (i = 31) := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    change (2 ^ 31).testBit i = decide (i = 31)
    simpa [eq_comm] using (Nat.testBit_two_pow (n := 31) (m := i))
  · have : i ≠ 31 := by omega
    simp [hi, this]

/-- Repacking the fields extracted from a native binary32 word returns the original word. -/
theorem mkBits_fields (bits : UInt32) :
    mkBits (signBit bits) (expField bits).toNat (fracField bits).toNat = bits := by
  by_cases hsign : bits &&& 0x80000000 = 0
  · simp only [mkBits, signBit, hsign, UInt32.ofNat_toNat]
    unfold expField fracField
    have hsignBit : bits.toBitVec.getLsbD 31 = false := by
      have h := congrArg (fun x : UInt32 => x.toBitVec.getLsbD 31) hsign
      simpa [UInt32.toBitVec_and, BitVec.getLsbD_ofNat] using h
    apply UInt32.toBitVec_inj.1
    simp only [UInt32.toBitVec_or, UInt32.toBitVec_and,
      UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight]
    norm_num
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases hlow : i < 23
    · have hfraction :
          (8388607#32 : BitVec 32)[i] = true := by
        rw [← BitVec.getLsbD_eq_getElem hi, fractionMask_getLsbD]
        simp [hlow]
      simp [hlow, hi, hfraction]
    · by_cases hmid : i < 31
      · have hindex : 23 + (i - 23) = i := by omega
        have hexponent : i - 23 < 8 := by omega
        have hexponentMask :
            (255#32 : BitVec 32)[i - 23] = true := by
          rw [← BitVec.getLsbD_eq_getElem (by omega), exponentMask_getLsbD]
          simp [hexponent]
        have hfraction :
            (8388607#32 : BitVec 32)[i] = false := by
          rw [← BitVec.getLsbD_eq_getElem hi, fractionMask_getLsbD]
          simp [hlow]
        simp [hlow, hi, hindex, hexponentMask, hfraction]
      · have heq : i = 31 := by omega
        subst i
        simp only [Nat.lt_add_one, BitVec.getLsbD_eq_getElem, BitVec.getElem_or,
          BitVec.getElem_shiftLeft,
          Nat.reduceLT, decide_false, Bool.not_false, Nat.reduceSub, BitVec.getElem_and,
            BitVec.getElem_ushiftRight,
          Nat.reduceAdd, BitVec.reduceGetElem, Bool.and_false, Bool.and_self, Bool.or_self,
            Bool.false_eq]
        rw [← BitVec.getLsbD_eq_getElem (x := bits.toBitVec) (i := 31) (by omega)]
        exact hsignBit
  · have hsignBool : (bits &&& 0x80000000 != 0) = true :=
      bne_iff_ne.mpr hsign
    simp only [mkBits, signBit, hsignBool, ite_true, UInt32.ofNat_toNat]
    unfold expField fracField
    have hsignBit : bits.toBitVec.getLsbD 31 = true := by
      by_contra hbit
      have hbitFalse : bits.toBitVec.getLsbD 31 = false := by
        exact Bool.eq_false_of_not_eq_true hbit
      apply hsign
      apply UInt32.toBitVec_inj.1
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      by_cases heq : i = 31
      · subst i
        simpa [UInt32.toBitVec_and, signMask_getLsbD, hbitFalse]
      · simp [UInt32.toBitVec_and, signMask_getLsbD, heq]
    apply UInt32.toBitVec_inj.1
    simp only [UInt32.toBitVec_or, UInt32.toBitVec_and,
      UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight]
    norm_num
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases hlow : i < 23
    · have hsignMask :
          (2147483648#32 : BitVec 32)[i] = false := by
        rw [← BitVec.getLsbD_eq_getElem hi, signMask_getLsbD]
        simp
        omega
      have hfraction :
          (8388607#32 : BitVec 32)[i] = true := by
        rw [← BitVec.getLsbD_eq_getElem hi, fractionMask_getLsbD]
        simp [hlow]
      simp [hlow, hi, hsignMask, hfraction]
    · by_cases hmid : i < 31
      · have hindex : 23 + (i - 23) = i := by omega
        have hexponent : i - 23 < 8 := by omega
        have hsignMask :
            (2147483648#32 : BitVec 32)[i] = false := by
          rw [← BitVec.getLsbD_eq_getElem hi, signMask_getLsbD]
          simp
          omega
        have hexponentMask :
            (255#32 : BitVec 32)[i - 23] = true := by
          rw [← BitVec.getLsbD_eq_getElem (by omega), exponentMask_getLsbD]
          simp [hexponent]
        have hfraction :
            (8388607#32 : BitVec 32)[i] = false := by
          rw [← BitVec.getLsbD_eq_getElem hi, fractionMask_getLsbD]
          simp [hlow]
        simp [hlow, hi, hindex, hsignMask, hexponentMask, hfraction]
      · have heq : i = 31 := by omega
        subst i
        simp [hsignBit]

/-- Setting the native quiet-NaN bit agrees with setting the generic binary32 quiet bit. -/
theorem ofUInt32_or_quietBit (x : Value) :
    ofUInt32 (toUInt32 x ||| 0x00400000) =
      Model.ofBits (x.bits ||| FloatFormat.quietBit FloatFormat.binary32) := by
  cases x
  rfl

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
