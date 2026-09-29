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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Difference.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Proof
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Verified fixed-limb differences

These helpers compare, subtract, normalize, and shift two-word unsigned values without converting
the executable path to `Nat`. Their theorems expose the corresponding mathematical values for
format-specific subtraction proofs.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.UInt128

/-- Native two-word comparison agrees with comparison of mathematical values. -/
@[simp, grind =] theorem less_eq_true_iff (x y : UInt128) :
    less x y = true ↔ x.toNat < y.toNat := by
  unfold less UInt128.toNat
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, UInt64.lt_iff_toNat_lt]
  have hxLow := x.lo.toNat_lt
  have hyLow := y.lo.toNat_lt
  simp only [← UInt64.toNat_inj]
  omega

/-- Native three-way comparison agrees with comparison of mathematical values. -/
@[simp, grind =] theorem compare_eq_toNat_compare_toNat (x y : UInt128) :
    compare x y = Ord.compare x.toNat y.toNat := by
  unfold compare
  split
  · rename_i hless
    have hxy : x.toNat < y.toNat :=
      (less_eq_true_iff x y).mp hless
    exact (Nat.compare_eq_lt.mpr hxy).symm
  · rename_i hnotLess
    split
    · rename_i hgreater
      have hyx : y.toNat < x.toNat :=
        (less_eq_true_iff y x).mp hgreater
      exact (Nat.compare_eq_gt.mpr hyx).symm
    · rename_i hnotGreater
      have hxy : ¬x.toNat < y.toNat := by
        intro hxy
        exact hnotLess ((less_eq_true_iff x y).mpr hxy)
      have hyx : ¬y.toNat < x.toNat := by
        intro hyx
        exact hnotGreater ((less_eq_true_iff y x).mpr hyx)
      have hequal : x.toNat = y.toNat :=
        Nat.le_antisymm (Nat.le_of_not_gt hyx) (Nat.le_of_not_gt hxy)
      exact (Nat.compare_eq_eq.mpr hequal).symm

/-- Ordered two-word subtraction agrees with natural-number subtraction. -/
theorem sub_toNat (x y : UInt128) (hordered : y.toNat ≤ x.toNat) :
    (sub x y).toNat = x.toNat - y.toNat := by
  unfold sub UInt128.toNat
  change
    y.lo.toNat + y.hi.toNat * 2 ^ 64 ≤
      x.lo.toNat + x.hi.toNat * 2 ^ 64 at hordered
  have hxLow := x.lo.toNat_lt
  have hyLow := y.lo.toNat_lt
  have hxHigh := x.hi.toNat_lt
  have hyHigh := y.hi.toNat_lt
  by_cases hborrow : x.lo < y.lo
  · have hlowLt : x.lo.toNat < y.lo.toNat :=
      UInt64.lt_iff_toNat_lt.mp hborrow
    have hhighLt : y.hi.toNat < x.hi.toNat := by
      omega
    have hhighBaseLe : y.hi ≤ x.hi :=
      UInt64.le_iff_toNat_le.mpr hhighLt.le
    have hhighAfterLe : (1 : UInt64) ≤ x.hi - y.hi := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [UInt64.toNat_sub_of_le _ _ hhighBaseLe]
      simp
      omega
    simp only [hborrow, ite_true]
    rw [UInt64.toNat_sub,
      UInt64.toNat_sub_of_le _ _ hhighAfterLe,
      UInt64.toNat_sub_of_le _ _ hhighBaseLe]
    simp only [UInt64.reduceToNat]
    have hlowWrap :
        (2 ^ 64 - y.lo.toNat + x.lo.toNat) % 2 ^ 64 =
          2 ^ 64 - y.lo.toNat + x.lo.toNat := by
      rw [Nat.mod_eq_of_lt]
      omega
    rw [hlowWrap]
    omega
  · have hlowLeNat : y.lo.toNat ≤ x.lo.toNat := by
      apply Nat.le_of_not_gt
      intro hlowLt
      exact hborrow (UInt64.lt_iff_toNat_lt.mpr hlowLt)
    have hlowLe : y.lo ≤ x.lo :=
      UInt64.le_iff_toNat_le.mpr hlowLeNat
    have hhighLe : y.hi ≤ x.hi := by
      apply UInt64.le_iff_toNat_le.mpr
      omega
    simp only [hborrow, ite_false]
    rw [UInt64.sub_zero, UInt64.toNat_sub_of_le _ _ hlowLe,
      UInt64.toNat_sub_of_le _ _ hhighLe]
    omega

/-- Native two-word leading-bit selection agrees with `Nat.log2`. -/
@[simp, grind =] theorem log2_toNat (value : UInt128) :
    log2 value = value.toNat.log2 := by
  unfold log2
  by_cases hhigh : value.hi = 0
  · simp [hhigh, UInt128.toNat, FloatLib.Numerics.FixedWord.log2_toNat]
  · have hhighBool : ¬value.hi == 0 := by
      simpa only [beq_iff_eq] using hhigh
    rw [ite_eq_right hhighBool, FloatLib.Numerics.FixedWord.log2_toNat]
    have hhighNat : value.hi.toNat ≠ 0 := by
      intro hzero
      exact hhigh (UInt64.toNat_inj.mp (by simpa using hzero))
    exact (log2_low_add_high_mul_pow
      value.lo.toNat value.hi.toNat 64 value.lo.toNat_lt hhighNat).symm

/-- The total native two-word right shift is exact division by a power of two. -/
@[simp, grind =] theorem shiftRight_toNat (value : UInt128) (shift : Nat) :
    (shiftRight value shift).toNat = value.toNat / 2 ^ shift := by
  by_cases hzero : shift = 0
  · subst shift
    simp [shiftRight]
  by_cases hsmall : shift < 64
  · have hpositive : 0 < shift := Nat.pos_of_ne_zero hzero
    have hcomplement : 64 - shift < 64 := by omega
    have hshiftWord : UInt64.ofNat shift < 64 := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [UInt64.toNat_ofNat_of_lt' (hsmall.trans (by decide))]
      exact hsmall
    have hshiftWordLe : UInt64.ofNat shift ≤ (64 : UInt64) := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [UInt64.toNat_ofNat_of_lt' (hsmall.trans (by decide))]
      exact hsmall.le
    have hlow :
        (value.lo >>> UInt64.ofNat shift).toNat =
          value.lo.toNat / 2 ^ shift := by
      rw [FloatLib.Numerics.FixedWord.shiftRight_toNat _ _ hsmall,
        Nat.shiftRight_eq_div_pow]
    have hhigh :
        (value.hi >>> UInt64.ofNat shift).toNat =
          value.hi.toNat / 2 ^ shift := by
      rw [FloatLib.Numerics.FixedWord.shiftRight_toNat _ _ hsmall,
        Nat.shiftRight_eq_div_pow]
    have hhighLow :
        (lowBitsWord value.hi (UInt64.ofNat shift)).toNat =
          value.hi.toNat % 2 ^ shift := by
      rw [lowBitsWord_toNat _ _ hshiftWordLe,
        UInt64.toNat_ofNat_of_lt' (hsmall.trans (by decide))]
    have hremainderBound :
        value.hi.toNat % 2 ^ shift < 2 ^ shift :=
      Nat.mod_lt _ (Nat.two_pow_pos shift)
    have hcarryFit :
        value.hi.toNat % 2 ^ shift * 2 ^ (64 - shift) <
          2 ^ 64 := by
      have hpow :
          2 ^ shift * 2 ^ (64 - shift) = 2 ^ 64 := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hsmall)]
      rw [← hpow]
      exact Nat.mul_lt_mul_of_pos_right hremainderBound (Nat.two_pow_pos _)
    have hcarry :
        (lowBitsWord value.hi (UInt64.ofNat shift) <<<
            UInt64.ofNat (64 - shift)).toNat =
          value.hi.toNat % 2 ^ shift * 2 ^ (64 - shift) := by
      rw [FloatLib.Numerics.FixedWord.shiftLeft_toNat_mod
          _ _ hcomplement,
        hhighLow,
        Nat.mod_eq_of_lt hcarryFit]
    have hlowBound :
        value.lo.toNat / 2 ^ shift < 2 ^ (64 - shift) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)]
      have hpow :
          2 ^ (64 - shift) * 2 ^ shift = 2 ^ 64 := by
        rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hsmall)]
      simpa [hpow] using value.lo.toNat_lt
    have hor :
        (value.lo.toNat / 2 ^ shift) |||
            (value.hi.toNat % 2 ^ shift * 2 ^ (64 - shift)) =
          value.lo.toNat / 2 ^ shift +
            value.hi.toNat % 2 ^ shift * 2 ^ (64 - shift) := by
      rw [Nat.or_comm]
      simpa [Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm] using
        (Nat.shiftLeft_add_eq_or_of_lt hlowBound
          (value.hi.toNat % 2 ^ shift)).symm
    have hpow :
        2 ^ 64 = 2 ^ shift * 2 ^ (64 - shift) := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hsmall)]
    have hhighDecompose :=
      Nat.mod_add_div value.hi.toNat (2 ^ shift)
    have hdivisible :
        2 ^ shift ∣ value.hi.toNat * 2 ^ 64 := by
      rw [hpow]
      refine ⟨value.hi.toNat * 2 ^ (64 - shift), ?_⟩
      ring
    simp only [shiftRight, hzero, beq_iff_eq, ite_false,
      hsmall, ite_true]
    unfold UInt128.toNat
    rw [UInt64.toNat_or, hlow, hcarry, hor, hhigh]
    rw [Nat.add_div_of_dvd_left hdivisible]
    have hproductDiv :
        value.hi.toNat * 2 ^ 64 / 2 ^ shift =
          value.hi.toNat * 2 ^ (64 - shift) := by
      rw [hpow]
      calc
        value.hi.toNat * (2 ^ shift * 2 ^ (64 - shift)) /
              2 ^ shift =
            (value.hi.toNat * 2 ^ (64 - shift)) * 2 ^ shift /
              2 ^ shift := by
          congr 1
          ac_rfl
        _ = value.hi.toNat * 2 ^ (64 - shift) :=
          Nat.mul_div_left _ (Nat.two_pow_pos shift)
    rw [hproductDiv]
    nlinarith
  · by_cases hwidth : shift < 128
    · have hlarge : 64 ≤ shift := Nat.le_of_not_gt hsmall
      let inner := shift - 64
      have hinner : inner < 64 := by
        dsimp [inner]
        omega
      have hshiftEq : shift = 64 + inner := by
        dsimp [inner]
        omega
      have hword :
          (value.hi >>> UInt64.ofNat inner).toNat =
            value.hi.toNat / 2 ^ inner := by
        rw [FloatLib.Numerics.FixedWord.shiftRight_toNat _ _ hinner,
          Nat.shiftRight_eq_div_pow]
      have hbaseQuotient :
          (value.lo.toNat + value.hi.toNat * 2 ^ 64) / 2 ^ 64 =
            value.hi.toNat := by
        rw [Nat.mul_comm value.hi.toNat, Nat.add_mul_div_left _ _
          (Nat.two_pow_pos 64), Nat.div_eq_of_lt value.lo.toNat_lt,
          Nat.zero_add]
      simp only [shiftRight, hzero, beq_iff_eq, ite_false,
        hsmall, hwidth, ite_true]
      unfold UInt128.toNat
      simp only [UInt64.reduceToNat, zero_mul, add_zero]
      rw [hword, hshiftEq, pow_add, ← Nat.div_div_eq_div_mul,
        hbaseQuotient]
    · have hlarge : 128 ≤ shift := Nat.le_of_not_gt hwidth
      have hvalue := value.toNat_lt
      have hpower : 2 ^ 128 ≤ 2 ^ shift :=
        Nat.pow_le_pow_right (by decide) hlarge
      simp only [shiftRight, hzero, beq_iff_eq, ite_false,
        hsmall, hwidth]
      unfold UInt128.toNat
      simp only [UInt64.reduceToNat, zero_mul, add_zero]
      exact (Nat.div_eq_of_lt (hvalue.trans_le hpower)).symm

/-- A bounded native one-hot value represents the corresponding power of two. -/
theorem singleBit_toNat_of_lt (index : Nat) (hindex : index < 128) :
    (singleBit index).toNat = 2 ^ index := by
  by_cases hsmall : index < 64
  · have hfit : (1 : UInt64).toNat <<< index < 2 ^ 64 := by
      simp only [UInt64.toNat_one, Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by decide) hsmall
    simp only [singleBit, hsmall, ite_true]
    unfold UInt128.toNat
    rw [FloatLib.Numerics.FixedWord.shiftLeft_toNat
      (1 : UInt64) index hsmall hfit]
    simp [Nat.shiftLeft_eq]
  · have hlarge : 64 ≤ index := Nat.le_of_not_gt hsmall
    have hinner : index - 64 < 64 := by omega
    have hfit : (1 : UInt64).toNat <<< (index - 64) < 2 ^ 64 := by
      simp only [UInt64.toNat_one, Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by decide) hinner
    simp only [singleBit, hsmall, ite_false, hindex, ite_true]
    unfold UInt128.toNat
    rw [FloatLib.Numerics.FixedWord.shiftLeft_toNat
      (1 : UInt64) (index - 64) hinner hfit]
    simp only [UInt64.reduceToNat, zero_add, UInt64.toNat_one,
      Nat.shiftLeft_eq, one_mul]
    calc
      2 ^ (index - 64) * 2 ^ 64 =
          2 ^ ((index - 64) + 64) := by rw [pow_add]
      _ = 2 ^ index := by congr; omega

/-- A bounded native two-word left shift has its exact mathematical value. -/
theorem shiftLeft_toNat (value : UInt128) (shift : Nat)
    (hshift : shift < 128)
    (hfit : value.toNat <<< shift < 2 ^ 128) :
    (shiftLeft value shift).toNat = value.toNat <<< shift := by
  by_cases hzero : shift = 0
  · subst shift
    simp [shiftLeft]
  by_cases hsmall : shift < 64
  · have hpositive : 0 < shift := Nat.pos_of_ne_zero hzero
    have hcomplement : 64 - shift < 64 := by omega
    have htotalFit :
        (value.lo.toNat + value.hi.toNat * 2 ^ 64) * 2 ^ shift <
          2 ^ 128 := by
      simpa [UInt128.toNat, Nat.shiftLeft_eq] using hfit
    have hhighFit : value.hi.toNat * 2 ^ shift < 2 ^ 64 := by
      by_contra h
      have hlarge : 2 ^ 64 ≤ value.hi.toNat * 2 ^ shift :=
        Nat.le_of_not_gt h
      have hpow128 : 2 ^ 128 = 2 ^ 64 * 2 ^ 64 := by
        rw [show 128 = 64 + 64 by omega, pow_add]
      have hbelow :
          value.hi.toNat * 2 ^ 64 * 2 ^ shift ≤
            (value.lo.toNat + value.hi.toNat * 2 ^ 64) * 2 ^ shift := by
        apply Nat.mul_le_mul_right
        omega
      have habove :
          2 ^ 128 ≤ value.hi.toNat * 2 ^ 64 * 2 ^ shift := by
        rw [hpow128]
        calc
          2 ^ 64 * 2 ^ 64 ≤
              (value.hi.toNat * 2 ^ shift) * 2 ^ 64 :=
            Nat.mul_le_mul_right _ hlarge
          _ = value.hi.toNat * 2 ^ 64 * 2 ^ shift := by ring
      exact (Nat.not_lt_of_ge (habove.trans hbelow)) htotalFit
    have hhigh :
        (value.hi <<< UInt64.ofNat shift).toNat =
          value.hi.toNat * 2 ^ shift := by
      simpa [Nat.shiftLeft_eq] using
        FloatLib.Numerics.FixedWord.shiftLeft_toNat
          value.hi shift hsmall
          (by simpa [Nat.shiftLeft_eq] using hhighFit)
    have hcarry :
        (value.lo >>> UInt64.ofNat (64 - shift)).toNat =
          value.lo.toNat / 2 ^ (64 - shift) :=
      by
        rw [FloatLib.Numerics.FixedWord.shiftRight_toNat
            _ _ hcomplement,
          Nat.shiftRight_eq_div_pow]
    have hcarryBound :
        value.lo.toNat / 2 ^ (64 - shift) < 2 ^ shift := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      have hpow : 2 ^ shift * 2 ^ (64 - shift) = 2 ^ 64 := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hsmall)]
      simpa [hpow] using value.lo.toNat_lt
    have hor :
        (value.hi.toNat * 2 ^ shift) |||
            (value.lo.toNat / 2 ^ (64 - shift)) =
          value.hi.toNat * 2 ^ shift +
            value.lo.toNat / 2 ^ (64 - shift) := by
      simpa [Nat.shiftLeft_eq] using
        (Nat.shiftLeft_add_eq_or_of_lt hcarryBound value.hi.toNat).symm
    have hlow :=
      FloatLib.Numerics.FixedWord.shiftLeft_toNat_mod
        value.lo shift hsmall
    have hpow : 2 ^ 64 = 2 ^ (64 - shift) * 2 ^ shift := by
      rw [← pow_add]
      exact congrArg (fun exponent : Nat => 2 ^ exponent)
        (Nat.sub_add_cancel (Nat.le_of_lt hsmall)).symm
    have hdiv :
        value.lo.toNat * 2 ^ shift / 2 ^ 64 =
          value.lo.toNat / 2 ^ (64 - shift) := by
      rw [hpow]
      exact Nat.mul_div_mul_right _ _ (by positivity)
    have hdecompose :
        (value.lo.toNat * 2 ^ shift) % 2 ^ 64 +
            value.lo.toNat / 2 ^ (64 - shift) * 2 ^ 64 =
          value.lo.toNat * 2 ^ shift := by
      rw [← hdiv]
      calc
        (value.lo.toNat * 2 ^ shift) % 2 ^ 64 +
            (value.lo.toNat * 2 ^ shift) / 2 ^ 64 * 2 ^ 64 =
          (value.lo.toNat * 2 ^ shift) % 2 ^ 64 +
            2 ^ 64 * ((value.lo.toNat * 2 ^ shift) / 2 ^ 64) := by ring
        _ = value.lo.toNat * 2 ^ shift :=
          Nat.mod_add_div _ _
    simp only [shiftLeft, hzero, beq_iff_eq, ite_false, hsmall, ite_true]
    unfold UInt128.toNat
    rw [UInt64.toNat_or, hhigh, hcarry, hor, hlow]
    simp only [Nat.shiftLeft_eq]
    calc
      (value.lo.toNat * 2 ^ shift) % 2 ^ 64 +
          (value.hi.toNat * 2 ^ shift +
            value.lo.toNat / 2 ^ (64 - shift)) * 2 ^ 64 =
          ((value.lo.toNat * 2 ^ shift) % 2 ^ 64 +
            value.lo.toNat / 2 ^ (64 - shift) * 2 ^ 64) +
            value.hi.toNat * 2 ^ 64 * 2 ^ shift := by ring
      _ = value.lo.toNat * 2 ^ shift +
            value.hi.toNat * 2 ^ 64 * 2 ^ shift := by rw [hdecompose]
      _ = (value.lo.toNat + value.hi.toNat * 2 ^ 64) * 2 ^ shift := by ring
  · have hlarge : 64 ≤ shift := Nat.le_of_not_gt hsmall
    let inner := shift - 64
    have hinner : inner < 64 := by
      unfold inner
      omega
    have hshiftEq : shift = 64 + inner := by
      unfold inner
      omega
    have htotalFit :
        (value.lo.toNat + value.hi.toNat * 2 ^ 64) * 2 ^ shift <
          2 ^ 128 := by
      simpa [UInt128.toNat, Nat.shiftLeft_eq] using hfit
    have hhighZero : value.hi = 0 := by
      apply UInt64.toNat_inj.mp
      apply Nat.eq_zero_of_not_pos
      intro hpositive
      have hpow128 : 2 ^ 128 = 2 ^ 64 * 2 ^ 64 := by
        rw [show 128 = 64 + 64 by omega, pow_add]
      have hshiftPow : 2 ^ 64 ≤ 2 ^ shift :=
        Nat.pow_le_pow_right (by decide) hlarge
      have hterm :
          2 ^ 128 ≤
            (value.lo.toNat + value.hi.toNat * 2 ^ 64) * 2 ^ shift := by
        rw [hpow128]
        calc
          2 ^ 64 * 2 ^ 64 ≤
              (value.hi.toNat * 2 ^ 64) * 2 ^ 64 := by
            apply Nat.mul_le_mul_right
            nlinarith
          _ ≤ (value.hi.toNat * 2 ^ 64) * 2 ^ shift :=
            Nat.mul_le_mul_left _ hshiftPow
          _ ≤ (value.lo.toNat + value.hi.toNat * 2 ^ 64) * 2 ^ shift := by
            apply Nat.mul_le_mul_right
            omega
      exact (Nat.not_lt_of_ge hterm) htotalFit
    have hlowFit : value.lo.toNat * 2 ^ inner < 2 ^ 64 := by
      rw [hhighZero] at htotalFit
      simp only [UInt64.reduceToNat, zero_mul, add_zero] at htotalFit
      rw [hshiftEq, pow_add] at htotalFit
      nlinarith
    have hlow :
        (value.lo <<< UInt64.ofNat inner).toNat =
          value.lo.toNat * 2 ^ inner := by
      simpa [Nat.shiftLeft_eq] using
        FloatLib.Numerics.FixedWord.shiftLeft_toNat
          value.lo inner hinner
          (by simpa [Nat.shiftLeft_eq] using hlowFit)
    simp only [shiftLeft, hzero, beq_iff_eq, ite_false, hsmall, hshift, ite_true]
    unfold UInt128.toNat
    rw [hlow, hhighZero]
    simp only [UInt64.reduceToNat, zero_mul, zero_add, Nat.shiftLeft_eq]
    rw [hshiftEq, pow_add]
    ring

/-- Shifting a two-word value left by at least the carrier width returns zero. -/
theorem shiftLeft_of_ge (value : UInt128) (shift : Nat) (hshift : 128 ≤ shift) :
    shiftLeft value shift = ⟨0, 0⟩ := by
  have hzero : shift ≠ 0 := by omega
  have hsmall : ¬ shift < 64 := by omega
  have hmid : ¬ shift < 128 := by omega
  simp [shiftLeft, hzero, hsmall, hmid]

end FloatLib.Numerics.FixedWord.UInt128
