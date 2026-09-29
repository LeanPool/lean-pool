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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Proof.Word
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# Verified native-word rounding

The one-word nearest-even shift and quotient kernels agree with the shared arbitrary-precision
definitions. The compiler substitutions therefore change only the representation used for
bounded inputs, not the numerical result.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/-- Natural-number view of the shared nonnegative finite-scale encoding. -/
@[simp, grind =] theorem finiteScale_toNat (exponent : UInt64) :
    (finiteScale exponent).toNat =
      if exponent = 0 then 0 else exponent.toNat - 1 := by
  by_cases hexponent : exponent = 0
  · simp [finiteScale, hexponent]
  · simp only [finiteScale, beq_iff_eq, hexponent, ite_false]
    rw [UInt64.toNat_sub_of_le]
    · simp
    · apply UInt64.le_iff_toNat_le.mpr
      have hexponentNat : exponent.toNat ≠ 0 := by
        intro h
        apply hexponent
        apply UInt64.toNat_inj.mp
        simpa using h
      simp
      omega

private theorem uint64_rounding_increment_toNat (value : UInt64) (shift : Nat)
    (hpositive : 0 < shift) (hshift : shift < 64) :
    ((value >>> UInt64.ofNat shift) + 1).toNat =
      (value.toNat >>> shift) + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
  have hquotientLe :
      value.toNat >>> (k + 1) ≤ value.toNat >>> 1 := by
    rw [show k + 1 = 1 + k by omega, Nat.shiftRight_add]
    exact Nat.shiftRight_le _ _
  have hhalf : value.toNat >>> 1 < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by decide)]
    simpa [pow_succ] using value.toNat_lt
  have hsum : value.toNat >>> (k + 1) + 1 < 2 ^ 64 := by
    omega
  rw [UInt64.toNat_add, shiftRight_toNat value (k + 1) hshift]
  simp only [UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt hsum]

private theorem uint64_quotient_even_iff (value : UInt64) (shift : Nat)
    (hshift : shift < 64) :
    ((value >>> UInt64.ofNat shift) &&& 1) == 0 ↔
      (value.toNat >>> shift) % 2 == 0 := by
  simp [← UInt64.toNat_inj, shiftRight_toNat value shift hshift]

/-- Native word rounding agrees exactly with the generic natural-number rounder. -/
@[simp, grind =] theorem roundShiftRightEven_toNat (value : UInt64) (shift : Nat) :
    (roundShiftRightEven value shift).toNat =
      Numerics.roundShiftRightEven value.toNat shift := by
  by_cases hzero : shift = 0
  · subst shift
    simp [roundShiftRightEven, Numerics.roundShiftRightEven]
  by_cases hsmall : shift < 64
  · have hpositive : 0 < shift := Nat.pos_of_ne_zero hzero
    have hquotient :=
      shiftRight_toNat value shift hsmall
    have hremainder :=
      FloatLib.Numerics.FixedWord.uint64_lowBits_toNat
        value shift hsmall
    have hhalf :=
      FloatLib.Numerics.FixedWord.uint64_powTwo_toNat
        (shift - 1) (by omega)
    have hincrement :=
      uint64_rounding_increment_toNat value shift hpositive hsmall
    have hincrementBound : value.toNat >>> shift + 1 < 2 ^ 64 := by
      rw [← hincrement]
      exact UInt64.toNat_lt _
    have heven :=
      uint64_quotient_even_iff value shift hsmall
    have hremainderNat :
        value.toNat - (value.toNat >>> shift <<< shift) =
          value.toNat % 2 ^ shift := by
      simpa [Numerics.shiftRightRemainder] using
        Numerics.shiftRightRemainder_eq_mod value.toNat shift
    unfold roundShiftRightEven
    rw [Numerics.roundShiftRightEven_def]
    simp only [beq_iff_eq, hzero, hsmall, ite_false, ite_true]
    simp only [UInt64.lt_iff_toNat_lt, hremainder, hhalf]
    split_ifs <;> simp_all <;> omega
  · have hlarge : 64 ≤ shift := Nat.le_of_not_gt hsmall
    by_cases heq : shift = 64
    · subst shift
      have hquotient : value.toNat >>> 64 = 0 :=
        Nat.shiftRight_eq_zero _ _ value.toNat_lt
      have hhalf : (0x8000000000000000 : UInt64).toNat = 2 ^ 63 := by
        decide
      have hgeneric :
          Numerics.roundShiftRightEven value.toNat 64 =
            if 2 ^ 63 < value.toNat then 1 else 0 := by
        rw [Numerics.roundShiftRightEven_def]
        simp only [beq_iff_eq]
        rw [ite_eq_right (by decide : (64 : Nat) ≠ 0)]
        rw [show value.toNat.shiftRight 64 = 0 from hquotient]
        rw [show Nat.shiftLeft 0 64 = 0 by simp [Nat.shiftLeft_eq]]
        simp only [Nat.sub_zero, Nat.reduceSub, Nat.zero_mod]
        split_ifs <;> omega
      rw [hgeneric]
      unfold roundShiftRightEven
      simp [UInt64.lt_iff_toNat_lt, hhalf]
      split_ifs <;> rfl
    · have hgt : 64 < shift := lt_of_le_of_ne hlarge (Ne.symm heq)
      have hvaluePow : value.toNat < 2 ^ shift := by
        exact lt_of_lt_of_le value.toNat_lt
          (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hgt))
      have hquotient : value.toNat >>> shift = 0 :=
        Nat.shiftRight_eq_zero _ _ hvaluePow
      have hhalfBound : value.toNat < 2 ^ (shift - 1) := by
        exact lt_of_lt_of_le value.toNat_lt
          (Nat.pow_le_pow_right (by decide) (by omega))
      have hgeneric :
          Numerics.roundShiftRightEven value.toNat shift = 0 := by
        rw [Numerics.roundShiftRightEven_def]
        simp only [beq_iff_eq]
        rw [ite_eq_right hzero]
        rw [show value.toNat.shiftRight shift = 0 from hquotient]
        rw [show Nat.shiftLeft 0 shift = 0 by simp [Nat.shiftLeft_eq]]
        simp only [Nat.sub_zero]
        rw [ite_eq_left hhalfBound]
      rw [hgeneric]
      unfold roundShiftRightEven
      simp [beq_iff_eq, hzero, hsmall, heq]

/-- Capacity-selected nearest-even shifting agrees with arbitrary-precision rounding. -/
theorem roundShiftRightEvenNat_eq_roundShiftRightEven (value shift : Nat) :
    roundShiftRightEvenNat value shift =
      Numerics.roundShiftRightEven value shift := by
  unfold roundShiftRightEvenNat
  split
  next hvalue =>
    have hvalue64 : (UInt64.ofNat value).toNat = value :=
      UInt64.toNat_ofNat_of_lt' hvalue
    rw [roundShiftRightEven_toNat, hvalue64]
  next hvalue =>
    rw [Numerics.roundShiftRightEven]

/--
The compiler uses native nearest-even shifting for one-word inputs and the arbitrary-precision
definition otherwise.
-/
-- grind: no rule; this compiler substitution expands a capacity-dispatch implementation.
@[csimp] theorem roundShiftRightEven_eq_roundShiftRightEvenNat :
    Numerics.roundShiftRightEven = roundShiftRightEvenNat := by
  funext value shift
  exact (roundShiftRightEvenNat_eq_roundShiftRightEven value shift).symm

/--
Native quotient rounding agrees with natural-number quotient rounding whenever the denominator is
nonzero and the incremented quotient fits in one word.

No bound on `den` is needed: the kernel compares the remainder with `den - remainder` instead of
doubling it, so its intermediates never wrap.
-/
theorem roundQuotientEven_toNat (num den : UInt64)
    (hden : den ≠ 0)
    (hquotientFit : num.toNat / den.toNat + 1 < 2 ^ 64) :
    (roundQuotientEven num den).toNat =
      Numerics.roundQuotientEven num.toNat den.toNat := by
  have hdenNat : den.toNat ≠ 0 := by
    intro h
    apply hden
    apply UInt64.toNat_inj.mp
    simpa using h
  have hremainderLt :
      num.toNat % den.toNat < den.toNat :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero hdenNat)
  have hremainder :
      (num % den).toNat = num.toNat % den.toNat :=
    UInt64.toNat_mod num den
  have hremainderLe : num % den ≤ den := by
    rw [UInt64.le_iff_toNat_le, hremainder]
    exact hremainderLt.le
  have hcomplement :
      (den - num % den).toNat =
        den.toNat - num.toNat % den.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hremainderLe, hremainder]
  have hquotient :
      (num / den).toNat = num.toNat / den.toNat :=
    UInt64.toNat_div num den
  have hincrement :
      (num / den + 1).toNat =
        num.toNat / den.toNat + 1 := by
    rw [UInt64.toNat_add, hquotient]
    exact Nat.mod_eq_of_lt hquotientFit
  unfold roundQuotientEven Numerics.roundQuotientEven
  simp only [beq_iff_eq, hden, ite_false]
  have heven :
      (num / den % 2 == 0) ↔
        (num.toNat / den.toNat) % 2 == 0 := by
    simp [← UInt64.toNat_inj, hquotient]
  simp only [UInt64.lt_iff_toNat_lt, hremainder, hcomplement]
  split_ifs <;> simp_all <;> omega

/--
The native and arbitrary-precision branches compute the same nearest-even natural-number
quotient.
-/
theorem roundQuotientEvenNat_eq_roundQuotientEven (num den : Nat) :
    roundQuotientEvenNat num den = Numerics.roundQuotientEven num den := by
  unfold roundQuotientEvenNat
  split
  next hfit =>
    obtain ⟨hnum, hdenPositive, hden⟩ := hfit
    have hnum64 : (UInt64.ofNat num).toNat = num :=
      UInt64.toNat_ofNat_of_lt' (hnum.trans (by decide))
    have hden64 : (UInt64.ofNat den).toNat = den :=
      UInt64.toNat_ofNat_of_lt' hden
    have hdenNonzero : UInt64.ofNat den ≠ 0 := by
      intro h
      have := congrArg UInt64.toNat h
      simp [hden64, Nat.ne_of_gt hdenPositive] at this
    have hquotientFit : num / den + 1 < 2 ^ 64 := by
      have hquotientLe : num / den ≤ num := Nat.div_le_self _ _
      omega
    rw [roundQuotientEven_toNat _ _ hdenNonzero]
    · rw [hnum64, hden64]
    · rw [hnum64, hden64]
      exact hquotientFit
  next hfit =>
    rw [Numerics.roundQuotientEven]

/--
The compiler uses native quotient rounding for bounded inputs and the arbitrary-precision
definition otherwise.
-/
-- grind: no rule; this compiler substitution expands a capacity-dispatch implementation.
@[csimp] theorem roundQuotientEven_eq_roundQuotientEvenNat :
    Numerics.roundQuotientEven = roundQuotientEvenNat := by
  funext num den
  exact (roundQuotientEvenNat_eq_roundQuotientEven num den).symm

end FloatLib.Numerics.FixedWord
