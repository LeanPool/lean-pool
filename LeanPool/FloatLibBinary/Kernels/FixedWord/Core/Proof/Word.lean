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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Runtime
import Mathlib.Tactic.Bound
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import all Init.Data.Fin.Log2
import all Init.Data.UInt.Log2

/-!
# Verified single-word primitives for executable numerical arithmetic

Native-word shifts, bit operations, and restoring square-root state have exact natural-number
interpretations. Nearest-even rounding is proved in `Core.Proof.Rounding`; wider two-limb values
and exact `64 × 64 → 128` multiplication are proved in `Core.Proof.UInt128`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/--
A native-word sum has its ordinary natural-number value when that sum does not overflow the word.
-/
theorem uint64_add_toNat_of_lt (x y : UInt64)
    (hfit : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt hfit]

/-- A native-word product has its natural-number value when it does not overflow the word. -/
theorem uint64_mul_toNat_of_lt (x y : UInt64)
    (hfit : x.toNat * y.toNat < 2 ^ 64) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hfit]

/--
Mathematical meaning of a restoring square-root state, independent of the native carrier used by
the executable loop.
-/
def RestoringRootState.Represents
    {α : Type} (toNat : α → Nat)
    (state : RestoringRootState α) (value : Nat) : Prop :=
  toNat state.root * toNat state.root + toNat state.remainder = value ∧
    toNat state.remainder ≤ 2 * toNat state.root

/--
The root component of a valid restoring state fits in the requested precision whenever the
processed radicand fits in twice that precision.
-/
theorem RestoringRootState.root_lt_two_pow
    {α : Type} (toNat : α → Nat) (precision : Nat)
    {state : RestoringRootState α} {value : Nat}
    (hrep : state.Represents toNat value)
    (hvalue : value < 2 ^ (2 * precision)) :
    toNat state.root < 2 ^ precision := by
  apply Nat.mul_self_lt_mul_self_iff.mp
  rw [← pow_add, ← two_mul]
  exact (Nat.le_add_right _ _).trans_lt (hrep.1.symm ▸ hvalue)

/--
The root component of a valid restoring state is the exact floor square root, independently of
the machine-word carrier used by the executable loop.
-/
theorem RestoringRootState.root_eq_sqrt
    {α : Type} (toNat : α → Nat)
    {state : RestoringRootState α} {value : Nat}
    (hrep : state.Represents toNat value) :
    toNat state.root = Nat.sqrt value := by
  rw [← hrep.1]
  exact (Nat.sqrt_add_eq _ (by simpa only [two_mul] using hrep.2)).symm

/--
A valid restoring state contains the exact floor square root and its square remainder.
-/
theorem RestoringRootState.sqrt_spec
    {α : Type} (toNat : α → Nat)
    {state : RestoringRootState α} {value : Nat}
    (hrep : state.Represents toNat value) :
    toNat state.root = Nat.sqrt value ∧
      toNat state.remainder = value - Nat.sqrt value * Nat.sqrt value := by
  have hroot := RestoringRootState.root_eq_sqrt toNat hrep
  constructor
  · exact hroot
  · rw [← hroot]
    exact Nat.eq_sub_of_add_eq' hrep.1

/-- Masking a native word to one base-four digit always produces a value below four. -/
theorem maskedBaseFourDigit_lt (value : UInt64) :
    (value &&& 3).toNat < 4 := by
  rw [UInt64.toNat_and]
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

/-- Native low-bit inspection is exactly natural-number parity. -/
theorem lowBitIsZero_eq_even (code : UInt64) :
    ((code &&& 1) == 0) = decide (code.toNat % 2 = 0) := by
  have hbit : (code &&& 1).toNat = code.toNat % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_one]
    norm_num [Nat.and_two_pow_sub_one_eq_mod]
  by_cases heven : code.toNat % 2 = 0
  · have hword : code &&& 1 = 0 := by
      apply UInt64.toNat_inj.mp
      simpa [hbit] using heven
    simp [hword, heven]
  · have hword : code &&& 1 ≠ 0 := by
      intro equality
      apply heven
      have equalityNat := congrArg UInt64.toNat equality
      simpa [hbit] using equalityNat
    simp [hword, heven]

/-- Native low-bit nonzero inspection is exactly odd natural-number parity. -/
theorem lowBitIsNonzero_eq_odd (code : UInt64) :
    ((code &&& 1) != 0) = (code.toNat % 2 != 0) := by
  rw [bne_eq, bne_eq, lowBitIsZero_eq_even]
  congr 1

/-- Inspecting the low bit of a two-limb word is natural-number parity. -/
theorem UInt128.lowBitIsZero_eq_even (code : UInt128) :
    ((code.lo &&& 1) == 0) = decide (code.toNat % 2 = 0) := by
  have hbit : (code.lo &&& 1).toNat = code.toNat % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_one]
    norm_num [Nat.and_two_pow_sub_one_eq_mod]
    unfold UInt128.toNat
    norm_num [Nat.add_mod, Nat.mul_mod]
  by_cases heven : code.toNat % 2 = 0
  · have hword : code.lo &&& 1 = 0 := by
      apply UInt64.toNat_inj.mp
      simpa [hbit] using heven
    simp [hword, heven]
  · have hword : code.lo &&& 1 ≠ 0 := by
      intro equality
      apply heven
      have equalityNat := congrArg UInt64.toNat equality
      simpa [hbit] using equalityNat
    simp [hword, heven]

/-- Two-limb low-bit nonzero inspection is exactly odd natural-number parity. -/
theorem UInt128.lowBitIsNonzero_eq_odd (code : UInt128) :
    ((code.lo &&& 1) != 0) = (code.toNat % 2 != 0) := by
  rw [bne_eq, bne_eq, UInt128.lowBitIsZero_eq_even]
  congr 1

/--
Machine-word nearest-even selection has the same natural-number code as the shared scalar
selector.
-/
@[simp, grind =] theorem selectNearestEvenWord_toNat
    (comparison : Ordering) (lower upper : UInt64) :
    (selectNearestEvenWord comparison lower upper).toNat =
      selectNearestEvenNat comparison lower.toNat upper.toNat := by
  cases comparison
  · rfl
  · unfold selectNearestEvenWord selectNearestEvenNat
    rw [lowBitIsZero_eq_even]
    by_cases heven : lower.toNat % 2 = 0 <;> simp [heven]
  · rfl

/-- Native `UInt64.log2` has the same natural-number value as `Nat.log2`. -/
@[simp, grind =] theorem log2_toNat (value : UInt64) :
    value.log2.toNat = value.toNat.log2 := by
  unfold UInt64.log2 Fin.log2
  rfl

/-- When the high part is nonzero, the low bits do not change its leading-bit position. -/
theorem log2_low_add_high_mul_pow (low high offset : Nat)
    (hlow : low < 2 ^ offset) (hhigh : high ≠ 0) :
    (low + high * 2 ^ offset).log2 = offset + high.log2 := by
  have hvalue : low + high * 2 ^ offset ≠ 0 := by
    positivity
  apply (Nat.log2_eq_iff hvalue).2
  constructor
  · rw [pow_add]
    calc
      2 ^ offset * 2 ^ high.log2 ≤ 2 ^ offset * high :=
        Nat.mul_le_mul_left _ (Nat.log2_self_le hhigh)
      _ = high * 2 ^ offset := Nat.mul_comm _ _
      _ ≤ low + high * 2 ^ offset := Nat.le_add_left _ _
  · rw [Nat.add_assoc, pow_add]
    calc
      low + high * 2 ^ offset < 2 ^ offset + high * 2 ^ offset :=
        Nat.add_lt_add_right hlow _
      _ = 2 ^ offset * (high + 1) := by ring
      _ ≤ 2 ^ offset * 2 ^ (high.log2 + 1) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr Nat.lt_log2_self)

/--
If a nonzero native word fits below `2 ^ width`, then its leading-bit position is smaller than
`width`.
-/
theorem log2_toNat_lt_of_toNat_lt_two_pow
    (value : UInt64) (width : Nat)
    (hvalue : value ≠ 0) (hfit : value.toNat < 2 ^ width) :
    value.log2.toNat < width := by
  rw [log2_toNat, Nat.log2_lt]
  · exact hfit
  · simpa [← UInt64.toNat_inj] using hvalue

/-- Moving a nonzero value's leading bit to `precision` puts it at or above `2 ^ precision`. -/
theorem two_pow_le_shiftLeft_sub_log2 (precision value : Nat)
    (hvalue : value ≠ 0) (hleading : value.log2 ≤ precision) :
    2 ^ precision ≤ value <<< (precision - value.log2) := by
  have hpow : 2 ^ value.log2 ≤ value :=
    (Nat.le_log2 hvalue).mp (le_refl _)
  calc
    2 ^ precision = 2 ^ value.log2 * 2 ^ (precision - value.log2) := by
      rw [← pow_add, Nat.add_sub_of_le hleading]
    _ ≤ value * 2 ^ (precision - value.log2) := Nat.mul_le_mul_right _ hpow
    _ = value <<< (precision - value.log2) := (Nat.shiftLeft_eq _ _).symm

/-- Moving the leading bit to `precision` keeps the value below the next power of two. -/
theorem shiftLeft_sub_log2_lt_two_pow (precision value : Nat)
    (hleading : value.log2 ≤ precision) :
    value <<< (precision - value.log2) < 2 ^ (precision + 1) := by
  rw [Nat.shiftLeft_eq]
  calc
    value * 2 ^ (precision - value.log2) <
        2 ^ (value.log2 + 1) * 2 ^ (precision - value.log2) :=
      Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos _)
    _ = 2 ^ (precision + 1) := by
      rw [← pow_add]
      congr 1
      omega

/--
A native left shift has its mathematical natural-number value when the shift amount and result fit.
-/
theorem shiftLeft_toNat (value : UInt64) (shift : Nat)
    (hshift : shift < 64)
    (hfit : value.toNat <<< shift < 2 ^ 64) :
    (value <<< UInt64.ofNat shift).toNat = value.toNat <<< shift := by
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat_of_lt' (hshift.trans (by decide)),
    Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hfit]

/-- An in-range native left shift is multiplication modulo the word size. -/
theorem shiftLeft_toNat_mod (value : UInt64) (shift : Nat)
    (hshift : shift < 64) :
    (value <<< UInt64.ofNat shift).toNat =
      (value.toNat * 2 ^ shift) % 2 ^ 64 := by
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat_of_lt' (hshift.trans (by decide)),
    Nat.mod_eq_of_lt hshift, Nat.shiftLeft_eq]

/-- Shifting the native word `1` within range represents the corresponding power of two. -/
theorem uint64_powTwo_toNat (exponent : Nat) (hexponent : exponent < 64) :
    (((1 : UInt64) <<< UInt64.ofNat exponent).toNat) = 2 ^ exponent := by
  rw [shiftLeft_toNat (1 : UInt64) exponent hexponent]
  · exact Nat.one_shiftLeft exponent
  · simpa only [UInt64.toNat_one, Nat.one_shiftLeft] using
      (Nat.pow_lt_pow_right (by decide) hexponent : 2 ^ exponent < 2 ^ 64)

/--
Moving the low `inner` bits of a word to the high end has the expected natural-number value.

This is the wrapped half of a cross-limb right shift. Keeping it in the fixed-word core lets every
multi-limb backend share the same machine-word argument.
-/
theorem shiftLeftLowBits_toNat (value : UInt64) (inner : Nat)
    (hpositive : 0 < inner) (hinner : inner < 64) :
    (value <<< UInt64.ofNat (64 - inner)).toNat =
      (value.toNat % 2 ^ inner) * 2 ^ (64 - inner) := by
  have hcomplement : 64 - inner < 64 := by omega
  have hsum : inner + (64 - inner) = 64 :=
    Nat.add_sub_of_le (Nat.le_of_lt hinner)
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat_of_lt' (hcomplement.trans (by decide)),
    Nat.mod_eq_of_lt hcomplement]
  simp only [Nat.shiftLeft_eq]
  have hdecompose :
      value.toNat =
        value.toNat % 2 ^ inner +
          2 ^ inner * (value.toNat / 2 ^ inner) := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div value.toNat (2 ^ inner)).symm
  conv_lhs =>
    enter [1, 1]
    rw [hdecompose]
  rw [Nat.add_mul, Nat.add_mod]
  have hremainder := Nat.mod_lt value.toNat (by positivity : 0 < 2 ^ inner)
  have hpow : 2 ^ inner * 2 ^ (64 - inner) = 2 ^ 64 := by
    rw [← pow_add, hsum]
  have hmultiple :
      (2 ^ inner * (value.toNat / 2 ^ inner) *
          2 ^ (64 - inner)) % 2 ^ 64 = 0 := by
    have heq :
      2 ^ inner * (value.toNat / 2 ^ inner) * 2 ^ (64 - inner) =
        (value.toNat / 2 ^ inner) * 2 ^ 64 := by
      calc
        2 ^ inner * (value.toNat / 2 ^ inner) * 2 ^ (64 - inner) =
            (value.toNat / 2 ^ inner) *
              (2 ^ inner * 2 ^ (64 - inner)) := by ring
        _ = (value.toNat / 2 ^ inner) * 2 ^ 64 := by
          rw [← pow_add, hsum]
    rw [heq, Nat.mul_mod_left]
  rw [hmultiple, Nat.add_zero]
  have hsmall :
      value.toNat % 2 ^ inner * 2 ^ (64 - inner) < 2 ^ 64 :=
    calc
      value.toNat % 2 ^ inner * 2 ^ (64 - inner) <
          2 ^ inner * 2 ^ (64 - inner) :=
        Nat.mul_lt_mul_of_pos_right hremainder (by positivity)
      _ = 2 ^ 64 := hpow
  rw [Nat.mod_mod]
  exact Nat.mod_eq_of_lt hsmall

/-- A native right shift by an in-range natural has the expected mathematical value. -/
theorem shiftRight_toNat (value : UInt64) (shift : Nat)
    (hshift : shift < 64) :
    (value >>> UInt64.ofNat shift).toNat = value.toNat >>> shift := by
  simp [Nat.mod_eq_of_lt hshift]

/--
Joining the two halves of a cross-limb right shift has the expected natural-number value.
-/
theorem shiftedPair_toNat (low high : UInt64) (inner : Nat)
    (hpositive : 0 < inner) (hinner : inner < 64) :
    ((low >>> UInt64.ofNat inner) |||
        (high <<< UInt64.ofNat (64 - inner))).toNat =
      low.toNat / 2 ^ inner +
        (high.toNat % 2 ^ inner) * 2 ^ (64 - inner) := by
  have hlow :
      (low >>> UInt64.ofNat inner).toNat =
        low.toNat / 2 ^ inner := by
    rw [shiftRight_toNat low inner hinner, Nat.shiftRight_eq_div_pow]
  have hhigh := shiftLeftLowBits_toNat high inner hpositive hinner
  have hbound : low.toNat / 2 ^ inner < 2 ^ (64 - inner) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have hpow : 2 ^ (64 - inner) * 2 ^ inner = 2 ^ 64 := by
      rw [← pow_add]
      congr
      omega
    simpa [hpow] using low.toNat_lt
  rw [UInt64.toNat_or, hlow, hhigh, Nat.or_comm]
  calc
    (high.toNat % 2 ^ inner * 2 ^ (64 - inner)) |||
        low.toNat / 2 ^ inner =
      ((high.toNat % 2 ^ inner) <<< (64 - inner)) |||
        low.toNat / 2 ^ inner := by simp [Nat.shiftLeft_eq]
    _ = ((high.toNat % 2 ^ inner) <<< (64 - inner)) +
        low.toNat / 2 ^ inner :=
      (Nat.shiftLeft_add_eq_or_of_lt hbound
        (high.toNat % 2 ^ inner)).symm
    _ = low.toNat / 2 ^ inner +
        high.toNat % 2 ^ inner * 2 ^ (64 - inner) := by
      simp [Nat.shiftLeft_eq, Nat.add_comm]

namespace BaseFour

/-- Positional weight of one base-four digit. -/
def place (index : Nat) : Nat :=
  2 ^ (2 * index)

/--
Value reconstructed from the first `steps` digits of any machine-word base-four source.

Concrete radicand layouts provide only their digit reader; the positional recurrence and loop
proof are shared across one-word and multi-word square-root kernels.
-/
def digitsValue {α : Type} (digitAt : α → Nat → UInt64) (source : α) : Nat → Nat
  | 0 => 0
  | steps + 1 =>
      (digitAt source steps).toNat * place steps +
        digitsValue digitAt source steps

/-- Base-four digit selected from a machine word; indices below 32 avoid shift-count wraparound. -/
def wordDigit (value : UInt64) (index : Nat) : Nat :=
  ((value >>> UInt64.ofNat (2 * index)) &&& 3).toNat

/-- Value reconstructed from the first `steps` base-four digits of a machine word. -/
def wordDigits (value : UInt64) : Nat → Nat
  | 0 => 0
  | steps + 1 =>
      wordDigit value steps * place steps + wordDigits value steps

/-- Machine extraction agrees with natural-number base-four digit selection. -/
theorem wordDigit_eq
    (value : UInt64) (index : Nat) (hindex : index < 32) :
    wordDigit value index =
      (value.toNat / place index) % 4 := by
  unfold wordDigit place
  have hshift : 2 * index < 64 := by omega
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat_of_lt' (hshift.trans (by decide)),
    Nat.mod_eq_of_lt hshift]
  change (value.toNat >>> (2 * index)) &&& 3 =
    value.toNat / 2 ^ (2 * index) % 4
  rw [show (3 : Nat) = 2 ^ 2 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

/-- Advancing one base-four position multiplies its weight by four. -/
theorem place_succ (index : Nat) :
    place (index + 1) = place index * 4 := by
  simpa only [place, Nat.pow_mul] using Nat.pow_succ 4 index

/--
Generic refinement of a restoring loop from a proved digit step.

Only the carrier-specific step theorem and recursive equations are supplied by a backend. The
base-four accumulation and induction are independent of word width.
-/
theorem loop_represents
    {α β : Type}
    (toNat : α → Nat)
    (digitAt : β → Nat → UInt64)
    (step : UInt64 → RestoringRootState α → RestoringRootState α)
    (loop : β → Nat → RestoringRootState α → RestoringRootState α)
    (bound : Nat)
    (hloopZero : ∀ source state, loop source 0 state = state)
    (hloopSucc : ∀ source steps state,
      loop source (steps + 1) state =
        loop source steps (step (digitAt source steps) state))
    (hdigit : ∀ source index, (digitAt source index).toNat < 4)
    (hstep : ∀ state digit value,
      RestoringRootState.Represents toNat state value →
      value < bound →
      digit.toNat < 4 →
      RestoringRootState.Represents toNat
        (step digit state) (value * 4 + digit.toNat))
    (source : β) (steps : Nat)
    (state : RestoringRootState α) (value : Nat)
    (hrep : RestoringRootState.Represents toNat state value)
    (hfit : value * place steps + digitsValue digitAt source steps < bound) :
    RestoringRootState.Represents toNat (loop source steps state)
      (value * place steps + digitsValue digitAt source steps) := by
  induction steps generalizing state value with
  | zero =>
      rw [hloopZero]
      simpa [place, digitsValue, RestoringRootState.Represents] using hrep
  | succ steps ih =>
      rw [hloopSucc]
      let digit := digitAt source steps
      let next := step digit state
      let nextValue := value * 4 + digit.toNat
      have hplacePositive : 0 < place (steps + 1) := by
        simp [place]
      have hvalueLe :
          value ≤ value * place (steps + 1) +
            digitsValue digitAt source (steps + 1) := by
        exact le_trans
          (Nat.le_mul_of_pos_right value hplacePositive)
          (Nat.le_add_right _ _)
      have hvalue : value < bound :=
        lt_of_le_of_lt hvalueLe hfit
      have hnext :
          RestoringRootState.Represents toNat next nextValue := by
        exact hstep state digit value hrep hvalue (hdigit source steps)
      have hsame :
          nextValue * place steps + digitsValue digitAt source steps =
            value * place (steps + 1) +
              digitsValue digitAt source (steps + 1) := by
        dsimp only [nextValue, digit]
        rw [place_succ, digitsValue]
        ring
      have hnextFit :
          nextValue * place steps + digitsValue digitAt source steps <
            bound := by
        rw [hsame]
        exact hfit
      rw [← hsame]
      exact ih next nextValue hnext hnextFit

/-- Base-four positional weights multiply when their indices add. -/
theorem place_add (left right : Nat) :
    place (left + right) = place left * place right := by
  simp only [place, Nat.pow_mul, pow_add]

/-- Reconstructing the low base-four digits is reduction modulo their total width. -/
theorem wordDigits_eq_mod
    (value : UInt64) (steps : Nat) (hsteps : steps ≤ 32) :
    wordDigits value steps = value.toNat % place steps := by
  induction steps with
  | zero => simp [wordDigits, place, Nat.mod_one]
  | succ steps ih =>
      rw [wordDigits, wordDigit_eq value steps (by omega), ih (by omega)]
      simp only [place, Nat.pow_mul]
      rw [Nat.mod_pow_succ (b := 2 ^ 2) (k := steps)]
      ac_rfl

end BaseFour

/-- Machine-indexed bit inspection agrees with natural-number bit inspection. -/
@[simp, grind =] theorem bitAtWord_eq_testBit (value index : UInt64) :
    bitAtWord value index = value.toNat.testBit index.toNat := by
  unfold bitAtWord
  split
  next hindex =>
    have hindexNat : index.toNat < 64 := by
      simpa only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] using hindex
    rw [Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj,
      UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_one,
      Nat.mod_eq_of_lt hindexNat, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  next hindex =>
    have hindexNat : 64 ≤ index.toNat := by
      simpa [UInt64.lt_iff_toNat_lt] using hindex
    symm
    exact Nat.testBit_lt_two_pow
      (value.toNat_lt.trans_le (Nat.pow_le_pow_right (by decide) hindexNat))

/-- Natural value of a machine-indexed low-bit mask below the carrier width. -/
theorem lowMaskWord_toNat (width : UInt64) (hwidth : width < 64) :
    (lowMaskWord width).toNat = 2 ^ width.toNat - 1 := by
  have hwidthNat : width.toNat < 64 := by
    simpa [UInt64.lt_iff_toNat_lt] using hwidth
  have hpow : 2 ^ width.toNat < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by decide) hwidthNat
  unfold lowMaskWord
  rw [ite_eq_left hwidth, UInt64.toNat_sub_of_le]
  · simp only [UInt64.toNat_shiftLeft, UInt64.toNat_one]
    rw [Nat.mod_eq_of_lt hwidthNat, Nat.shiftLeft_eq, one_mul]
    change 2 ^ width.toNat % 2 ^ 64 - 1 = 2 ^ width.toNat - 1
    rw [Nat.mod_eq_of_lt hpow]
  · rw [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_one, UInt64.toNat_shiftLeft]
    rw [Nat.mod_eq_of_lt hwidthNat, Nat.shiftLeft_eq, one_mul]
    rw [Nat.mod_eq_of_lt hpow]
    exact Nat.one_le_two_pow

/-- Machine-indexed low-bit extraction is exact through the complete carrier width. -/
theorem lowBitsWord_toNat (value width : UInt64) (hwidth : width ≤ 64) :
    (lowBitsWord value width).toNat =
      value.toNat % 2 ^ width.toNat := by
  by_cases hwidthLt : width < 64
  · rw [lowBitsWord, UInt64.toNat_and,
      lowMaskWord_toNat width hwidthLt]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  · have hwidthEq : width = 64 := by
      apply UInt64.toNat_inj.mp
      have hle : width.toNat ≤ 64 := by
        simpa [UInt64.le_iff_toNat_le] using hwidth
      have hnotLt : ¬width.toNat < 64 := by
        intro h
        apply hwidthLt
        exact UInt64.lt_iff_toNat_lt.mpr (by simpa using h)
      simp only [UInt64.reduceToNat]
      omega
    subst width
    simp only [lowBitsWord, lowMaskWord, UInt64.toNat_and]
    change value.toNat &&& 2 ^ 64 - 1 = value.toNat % 2 ^ 64
    exact Nat.and_two_pow_sub_one_eq_mod _ _

/--
Masking a native word to a `Nat`-indexed low-bit field agrees with reduction modulo the
corresponding power of two.

This theorem bridges kernels whose control flow uses `Nat` to the shared machine-indexed
`lowBitsWord` primitive; the executable data path remains on unboxed `UInt64` values.
-/
theorem uint64_lowBits_toNat (value : UInt64) (shift : Nat)
    (hshift : shift < 64) :
    (value &&& (((1 : UInt64) <<< UInt64.ofNat shift) - 1)).toNat =
      value.toNat % 2 ^ shift := by
  have hshiftNat : (UInt64.ofNat shift).toNat = shift :=
    UInt64.toNat_ofNat_of_lt' (hshift.trans (by decide))
  have hshiftWord : UInt64.ofNat shift < 64 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [hshiftNat]
    exact hshift
  have hshiftWordLe : UInt64.ofNat shift ≤ (64 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hshiftNat]
    exact hshift.le
  have hbits :=
    lowBitsWord_toNat value (UInt64.ofNat shift) hshiftWordLe
  unfold lowBitsWord lowMaskWord at hbits
  rw [ite_eq_left hshiftWord] at hbits
  rw [hshiftNat] at hbits
  exact hbits

/-- Machine-indexed right shift agrees with natural-number right shift in range. -/
theorem shiftRightWord_toNat (value shift : UInt64) (hshift : shift < 64) :
    (shiftRightWord value shift).toNat =
      value.toNat >>> shift.toNat := by
  have hshiftNat : shift.toNat < 64 := by
    simpa [UInt64.lt_iff_toNat_lt] using hshift
  unfold shiftRightWord
  rw [ite_eq_left hshift, UInt64.toNat_shiftRight]
  rw [Nat.mod_eq_of_lt hshiftNat]

/--
Machine-width leading-zero counting has the corresponding natural-number value.

The nonzero branch proves that `log2 + 1` is at most the retained field width before interpreting
the machine subtraction. This is the capacity invariant that rules out unsigned wraparound.
-/
theorem countLeadingZerosWord_toNat
    (value width : UInt64) (hwidth : width ≤ 64) :
    (countLeadingZerosWord value width).toNat =
      let truncated := lowBitsWord value width
      if truncated == 0 then
        width.toNat
      else
        width.toNat - (truncated.log2.toNat + 1) := by
  let truncated := lowBitsWord value width
  have htruncated :
      truncated.toNat = value.toNat % 2 ^ width.toNat := by
    exact lowBitsWord_toNat value width hwidth
  have htruncatedLt : truncated.toNat < 2 ^ width.toNat := by
    rw [htruncated]
    exact Nat.mod_lt _ (Nat.two_pow_pos width.toNat)
  unfold countLeadingZerosWord
  change
    (if truncated == 0 then
      width
    else
      width - (truncated.log2 + 1)).toNat =
        if truncated == 0 then
          width.toNat
        else
          width.toNat - (truncated.log2.toNat + 1)
  split
  · rfl
  next hnonzero =>
    have hnonzeroNat : truncated.toNat ≠ 0 := by
      intro equality
      apply hnonzero
      apply beq_iff_eq.mpr
      apply UInt64.toNat_inj.mp
      simpa using equality
    have hlogLt :
        truncated.log2.toNat < width.toNat := by
      rw [log2_toNat]
      exact (Nat.log2_lt hnonzeroNat).mpr htruncatedLt
    have hlogAdd :
        (truncated.log2 + 1).toNat =
          truncated.log2.toNat + 1 := by
      rw [UInt64.toNat_add]
      simp only [UInt64.toNat_one]
      rw [Nat.mod_eq_of_lt]
      have hlogBound : truncated.log2.toNat < 64 := by
        rw [log2_toNat]
        exact (Nat.log2_lt hnonzeroNat).mpr (UInt64.toNat_lt truncated)
      omega
    rw [UInt64.toNat_sub_of_le]
    · rw [hlogAdd]
    · rw [UInt64.le_iff_toNat_le, hlogAdd]
      omega

/-- Machine-width equal-bit run counting reduces to the shared leading-zero primitive. -/
theorem countLeadingRunWord_toNat
    (value width : UInt64) (bit : Bool) (hwidth : width ≤ 64) :
    (countLeadingRunWord value width bit).toNat =
      let source := if bit then ~~~value else value
      let truncated := lowBitsWord source width
      if truncated == 0 then
        width.toNat
      else
        width.toNat - (truncated.log2.toNat + 1) := by
  unfold countLeadingRunWord
  exact countLeadingZerosWord_toNat
    (if bit then ~~~value else value) width hwidth

end FloatLib.Numerics.FixedWord
