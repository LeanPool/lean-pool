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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.RestoringSqrt.Compiler
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Difference.Proof
public import LeanPool.FloatLibBinary.Kernels.FixedWord.LimbRound.Proof
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Restoring square-root refinement

The restoring loop returns the floor square root and square remainder of its input.
The invariant relates the consumed radicand prefix to the partial root at each shift-and-subtract
step. This direct refinement proof lets callers use the kernel without a runtime certificate
check, provided the scaled radicand fits the fixed-word bound.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.RestoringSquareRoot

open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord.BaseFour

/-! ## Restoring-loop invariant -/

local notation "RootRep128" =>
  RestoringRootState.Represents UInt128.toNat

private theorem digit_lt_four (radicand : UInt256) (index : Nat) :
    (digitAt radicand index).toNat < 4 := by
  unfold digitAt
  split
  · exact maskedBaseFourDigit_lt _
  · split
    · exact maskedBaseFourDigit_lt _
    · split <;> exact maskedBaseFourDigit_lt _

private theorem shiftLeftOne_eq (value : UInt128) :
    shiftLeftOne value = UInt128.shiftLeft value 1 := by
  simp [shiftLeftOne, UInt128.shiftLeft]

private theorem shiftLeftTwo_eq (value : UInt128) :
    shiftLeftTwo value = UInt128.shiftLeft value 2 := by
  simp [shiftLeftTwo, UInt128.shiftLeft]

private theorem shiftedLow_append_digit
    (value digit : UInt64)
    (hdigit : digit.toNat < 4) :
    ((value <<< 2) ||| digit).toNat =
      (value <<< 2).toNat + digit.toNat := by
  have hshift :
      (value <<< 2).toNat = (value.toNat % 2 ^ 62) <<< 2 := by
    rw [UInt64.toNat_shiftLeft]
    norm_num [Nat.shiftLeft_eq]
    change
      value.toNat * 4 % (2 ^ 62 * 4) =
        value.toNat % 2 ^ 62 * 4
    exact Nat.mul_mod_mul_right 4 value.toNat (2 ^ 62)
  rw [UInt64.toNat_or, hshift]
  exact (Nat.shiftLeft_add_eq_or_of_lt hdigit
    (value.toNat % 2 ^ 62)).symm

private theorem rootStep_spec
    (state : RestoringRootState UInt128) (digit : UInt64) (value : Nat)
    (hrep : RootRep128 state value)
    (hvalue : value < 2 ^ 250)
    (hdigit : digit.toNat < 4) :
    RootRep128 (rootStep digit state) (value * 4 + digit.toNat) := by
  let expandedBase := shiftLeftTwo state.remainder
  let expanded : UInt128 :=
    { expandedBase with lo := expandedBase.lo ||| digit }
  let trialBase := shiftLeftTwo state.root
  let trial := trialBase.setLowBit
  let doubledRoot := shiftLeftOne state.root
  have hroot :=
    RestoringRootState.root_lt_two_pow UInt128.toNat 125 hrep hvalue
  have hremainderLe :
      state.remainder.toNat ≤ 2 * state.root.toNat :=
    hrep.2
  have hremainder : state.remainder.toNat < 2 ^ 126 := by
    norm_num at hroot ⊢
    omega
  have hrootShiftTwoFit : state.root.toNat <<< 2 < 2 ^ 128 := by
    rw [Nat.shiftLeft_eq]
    norm_num at hroot ⊢
    omega
  have hrootShiftOneFit : state.root.toNat <<< 1 < 2 ^ 128 := by
    rw [Nat.shiftLeft_eq]
    norm_num at hroot ⊢
    omega
  have hremainderShiftTwoFit :
      state.remainder.toNat <<< 2 < 2 ^ 128 := by
    rw [Nat.shiftLeft_eq]
    norm_num at hremainder ⊢
    omega
  have htrialBase :
      trialBase.toNat = state.root.toNat * 4 := by
    dsimp only [trialBase]
    rw [shiftLeftTwo_eq, UInt128.shiftLeft_toNat
      _ 2 (by omega) hrootShiftTwoFit]
    simp [Nat.shiftLeft_eq]
  have hdoubledRoot :
      doubledRoot.toNat = state.root.toNat * 2 := by
    dsimp only [doubledRoot]
    rw [shiftLeftOne_eq, UInt128.shiftLeft_toNat
      _ 1 (by omega) hrootShiftOneFit]
    simp [Nat.shiftLeft_eq]
  have hexpandedBase :
      expandedBase.toNat = state.remainder.toNat * 4 := by
    dsimp only [expandedBase]
    rw [shiftLeftTwo_eq, UInt128.shiftLeft_toNat
      _ 2 (by omega) hremainderShiftTwoFit]
    simp [Nat.shiftLeft_eq]
  have hexpanded :
      expanded.toNat =
        state.remainder.toNat * 4 + digit.toNat := by
    have hexpandedLow :
        (expandedBase.lo ||| digit).toNat =
          expandedBase.lo.toNat + digit.toNat := by
      dsimp only [expandedBase, shiftLeftTwo]
      exact shiftedLow_append_digit state.remainder.lo digit hdigit
    dsimp only [expanded]
    unfold UInt128.toNat
    change
      (expandedBase.lo ||| digit).toNat +
          expandedBase.hi.toNat * 2 ^ 64 =
        state.remainder.toNat * 4 + digit.toNat
    rw [hexpandedLow]
    have hbase :
        expandedBase.lo.toNat + expandedBase.hi.toNat * 2 ^ 64 =
          state.remainder.toNat * 4 := by
      simpa only [UInt128.toNat] using hexpandedBase
    omega
  have htrial :
      trial.toNat = state.root.toNat * 4 + 1 := by
    dsimp only [trial]
    rw [UInt128.setLowBit_toNat, htrialBase]
    have happend :=
      Nat.shiftLeft_add_eq_or_of_lt
        (a := state.root.toNat) (i := 2) (b := 1) (by norm_num)
    simpa [Nat.shiftLeft_eq] using happend.symm
  by_cases hbelow :
      state.remainder.toNat * 4 + digit.toNat <
        state.root.toNat * 4 + 1
  · have hnativeBelow : UInt128.less expanded trial = true := by
      apply (UInt128.less_eq_true_iff expanded trial).2
      simpa [hexpanded, htrial] using hbelow
    have hstep :
        rootStep digit state =
          { root := doubledRoot, remainder := expanded } := by
      change
        (if UInt128.less expanded trial = true then
            (⟨doubledRoot, expanded⟩ : RestoringRootState UInt128)
          else
            ⟨doubledRoot.setLowBit, UInt128.sub expanded trial⟩) =
          (⟨doubledRoot, expanded⟩ : RestoringRootState UInt128)
      rw [ite_eq_left hnativeBelow]
    rw [hstep]
    have hsquare :
        state.root.toNat * 2 * (state.root.toNat * 2) =
          4 * (state.root.toNat * state.root.toNat) := by
      ring
    have hvalueEq := hrep.1
    constructor
    · rw [hdoubledRoot, hexpanded]
      omega
    · rw [hdoubledRoot, hexpanded]
      omega
  · have hnativeBelow : UInt128.less expanded trial = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      have hlt := (UInt128.less_eq_true_iff expanded trial).1 htrue
      rw [hexpanded, htrial] at hlt
      exact hbelow hlt
    have hordered : trial.toNat ≤ expanded.toNat := by
      rw [hexpanded, htrial]
      omega
    have hrootOdd :
        doubledRoot.setLowBit.toNat =
          state.root.toNat * 2 + 1 := by
      rw [UInt128.setLowBit_toNat, hdoubledRoot]
      have happend :=
        Nat.shiftLeft_add_eq_or_of_lt
          (a := state.root.toNat) (i := 1) (b := 1) (by norm_num)
      simpa [Nat.shiftLeft_eq] using happend.symm
    have hremainderSub :
        (UInt128.sub expanded trial).toNat =
          state.remainder.toNat * 4 + digit.toNat -
            (state.root.toNat * 4 + 1) := by
      rw [UInt128.sub_toNat expanded trial hordered, hexpanded, htrial]
    have hsubAdd :
        (state.remainder.toNat * 4 + digit.toNat -
            (state.root.toNat * 4 + 1)) +
            (state.root.toNat * 4 + 1) =
          state.remainder.toNat * 4 + digit.toNat :=
      Nat.sub_add_cancel (by omega)
    have hstep :
        rootStep digit state =
          { root := doubledRoot.setLowBit
            remainder := UInt128.sub expanded trial } := by
      change
        (if UInt128.less expanded trial = true then
            (⟨doubledRoot, expanded⟩ : RestoringRootState UInt128)
          else
            ⟨doubledRoot.setLowBit, UInt128.sub expanded trial⟩) =
          (⟨doubledRoot.setLowBit,
              UInt128.sub expanded trial⟩ :
            RestoringRootState UInt128)
      rw [ite_eq_right (by simpa only [hnativeBelow] using Bool.false_ne_true)]
    rw [hstep]
    have hsquare :
        (state.root.toNat * 2 + 1) * (state.root.toNat * 2 + 1) =
          4 * (state.root.toNat * state.root.toNat) + 4 * state.root.toNat + 1 := by
      ring
    have hvalueEq := hrep.1
    constructor
    · rw [hrootOdd, hremainderSub]
      omega
    · rw [hrootOdd, hremainderSub]
      apply Nat.sub_le_iff_le_add.mpr
      omega

/-! ## Four-word radicand reconstruction -/

private theorem digitAt_limb0
    (radicand : UInt256) (index : Nat) (hindex : index < 32) :
    (digitAt radicand index).toNat =
      wordDigit radicand.limb0 index := by
  simp [digitAt, wordDigit, hindex]

private theorem digitAt_limb1
    (radicand : UInt256) (index : Nat)
    (hlower : 32 ≤ index) (hupper : index < 64) :
    (digitAt radicand index).toNat =
      wordDigit radicand.limb1 (index - 32) := by
  simp [digitAt, wordDigit, Nat.not_lt.mpr hlower, hupper]

private theorem digitAt_limb2
    (radicand : UInt256) (index : Nat)
    (hlower : 64 ≤ index) (hupper : index < 96) :
    (digitAt radicand index).toNat =
      wordDigit radicand.limb2 (index - 64) := by
  simp [digitAt, wordDigit, Nat.not_lt.mpr (by omega : 32 ≤ index),
    Nat.not_lt.mpr hlower, hupper]

private theorem digitAt_limb3
    (radicand : UInt256) (index : Nat) (hlower : 96 ≤ index) :
    (digitAt radicand index).toNat =
      wordDigit radicand.limb3 (index - 96) := by
  simp [digitAt, wordDigit, Nat.not_lt.mpr (by omega : 32 ≤ index),
    Nat.not_lt.mpr (by omega : 64 ≤ index),
    Nat.not_lt.mpr hlower]

private theorem digitsValue_limb0
    (radicand : UInt256) (steps : Nat) (hsteps : steps ≤ 32) :
    digitsValue digitAt radicand steps =
      wordDigits radicand.limb0 steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [digitsValue, wordDigits,
        digitAt_limb0 radicand steps (by omega), ih (by omega)]

private theorem digitsValue_limb1
    (radicand : UInt256) (steps : Nat) (hsteps : steps ≤ 32) :
    digitsValue digitAt radicand (32 + steps) =
      wordDigits radicand.limb1 steps * place 32 +
        wordDigits radicand.limb0 32 := by
  induction steps with
  | zero =>
      change
        digitsValue digitAt radicand 32 =
          0 * place 32 + wordDigits radicand.limb0 32
      rw [zero_mul, zero_add]
      exact digitsValue_limb0 radicand 32 (by omega)
  | succ steps ih =>
      change
        (digitAt radicand (32 + steps)).toNat *
              place (32 + steps) +
            digitsValue digitAt radicand (32 + steps) =
          (wordDigit radicand.limb1 steps * place steps +
              wordDigits radicand.limb1 steps) * place 32 +
            wordDigits radicand.limb0 32
      rw [digitAt_limb1 radicand (32 + steps) (by omega) (by omega),
        show 32 + steps - 32 = steps by omega, ih (by omega),
        place_add]
      ring

private theorem digitsValue_limb2
    (radicand : UInt256) (steps : Nat) (hsteps : steps ≤ 32) :
    digitsValue digitAt radicand (64 + steps) =
      wordDigits radicand.limb2 steps * place 64 +
        wordDigits radicand.limb1 32 * place 32 +
        wordDigits radicand.limb0 32 := by
  induction steps with
  | zero =>
      change
        digitsValue digitAt radicand 64 =
          0 * place 64 +
            wordDigits radicand.limb1 32 * place 32 +
            wordDigits radicand.limb0 32
      rw [zero_mul, zero_add]
      simpa only [show 64 = 32 + 32 by omega] using
        digitsValue_limb1 radicand 32 (by omega)
  | succ steps ih =>
      change
        (digitAt radicand (64 + steps)).toNat *
              place (64 + steps) +
            digitsValue digitAt radicand (64 + steps) =
          (wordDigit radicand.limb2 steps * place steps +
              wordDigits radicand.limb2 steps) * place 64 +
            wordDigits radicand.limb1 32 * place 32 +
            wordDigits radicand.limb0 32
      rw [digitAt_limb2 radicand (64 + steps) (by omega) (by omega),
        show 64 + steps - 64 = steps by omega, ih (by omega),
        place_add]
      ring

private theorem digitsValue_limb3
    (radicand : UInt256) (steps : Nat) (hsteps : steps ≤ 32) :
    digitsValue digitAt radicand (96 + steps) =
      wordDigits radicand.limb3 steps * place 96 +
        wordDigits radicand.limb2 32 * place 64 +
        wordDigits radicand.limb1 32 * place 32 +
        wordDigits radicand.limb0 32 := by
  induction steps with
  | zero =>
      change
        digitsValue digitAt radicand 96 =
          0 * place 96 +
            wordDigits radicand.limb2 32 * place 64 +
            wordDigits radicand.limb1 32 * place 32 +
            wordDigits radicand.limb0 32
      rw [zero_mul, zero_add]
      simpa only [show 96 = 64 + 32 by omega] using
        digitsValue_limb2 radicand 32 (by omega)
  | succ steps ih =>
      change
        (digitAt radicand (96 + steps)).toNat *
              place (96 + steps) +
            digitsValue digitAt radicand (96 + steps) =
          (wordDigit radicand.limb3 steps * place steps +
              wordDigits radicand.limb3 steps) * place 96 +
            wordDigits radicand.limb2 32 * place 64 +
            wordDigits radicand.limb1 32 * place 32 +
            wordDigits radicand.limb0 32
      rw [digitAt_limb3 radicand (96 + steps) (by omega),
        show 96 + steps - 96 = steps by omega, ih (by omega),
        place_add]
      ring

/-! ## Restoring-loop refinement -/

private theorem rootLoop_spec
    (radicand : UInt256) (steps : Nat)
    (state : RestoringRootState UInt128) (value : Nat)
    (hrep : RootRep128 state value)
    (hfit :
      value * place steps + digitsValue digitAt radicand steps < 2 ^ 250) :
    RootRep128 (rootLoop radicand steps state)
      (value * place steps + digitsValue digitAt radicand steps) :=
  loop_represents UInt128.toNat digitAt rootStep rootLoop (2 ^ 250)
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    digit_lt_four rootStep_spec radicand steps state value hrep hfit

private theorem rootAndRemainder_rep
    (radicand : UInt256) (steps : Nat)
    (hdigits : digitsValue digitAt radicand steps = radicand.toNat)
    (hfit : radicand.toNat < 2 ^ 250) :
    RootRep128 (rootAndRemainder radicand steps) radicand.toNat := by
  have hinitial :
      RootRep128
        ({ root := ⟨0, 0⟩, remainder := ⟨0, 0⟩ } :
          RestoringRootState UInt128) 0 := by
    simp [RestoringRootState.Represents, UInt128.toNat]
  have hloop :=
    rootLoop_spec radicand steps
      { root := ⟨0, 0⟩, remainder := ⟨0, 0⟩ } 0 hinitial
  rw [zero_mul, zero_add, hdigits] at hloop
  exact hloop hfit

/--
The first `steps` base-four digits reconstruct every radicand below `2^(2 * steps)`, for any digit
count between 64 and 128.

This covers both the 96- and 113-digit kernels; the two-word square-root kernels use
`fracWidth + 1` digits.
-/
private theorem digitsValue_eq_toNat
    (radicand : UInt256) (steps : Nat)
    (hlower : 64 ≤ steps) (hupper : steps ≤ 128)
    (hfit : radicand.toNat < 2 ^ (2 * steps)) :
    digitsValue digitAt radicand steps = radicand.toNat := by
  have h0 := radicand.limb0.toNat_lt
  have h1 := radicand.limb1.toNat_lt
  have h2 := radicand.limb2.toNat_lt
  have hlimb0 : radicand.limb0.toNat % place 32 = radicand.limb0.toNat := by
    apply Nat.mod_eq_of_lt
    simpa [place] using h0
  have hlimb1 : radicand.limb1.toNat % place 32 = radicand.limb1.toNat := by
    apply Nat.mod_eq_of_lt
    simpa [place] using h1
  have hvalue :
      radicand.toNat =
        radicand.limb0.toNat + radicand.limb1.toNat * 2 ^ 64 +
          radicand.limb2.toNat * 2 ^ 128 + radicand.limb3.toNat * 2 ^ 192 := rfl
  by_cases hmiddle : steps ≤ 96
  · -- The top limb is zero and the third limb has at most `2 * steps - 128` significant bits.
    have hsplit : steps = 64 + (steps - 64) := by omega
    have hpow : 2 ^ (2 * steps) = 2 ^ (2 * (steps - 64)) * 2 ^ 128 := by
      rw [← pow_add]
      congr 1
      omega
    have hlimb3 : radicand.limb3.toNat = 0 := by
      have hbound : radicand.limb3.toNat * 2 ^ 192 < 2 ^ 192 := by
        calc
          radicand.limb3.toNat * 2 ^ 192 ≤ radicand.toNat := by
            rw [hvalue]
            exact Nat.le_add_left _ _
          _ < 2 ^ (2 * steps) := hfit
          _ ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) (by omega)
      have hone : radicand.limb3.toNat * 2 ^ 192 < 1 * 2 ^ 192 := by
        rw [one_mul]
        exact hbound
      have hlt : radicand.limb3.toNat < 1 := Nat.lt_of_mul_lt_mul_right hone
      omega
    have hlimb2 : radicand.limb2.toNat % place (steps - 64) = radicand.limb2.toNat := by
      apply Nat.mod_eq_of_lt
      have hbound :
          radicand.limb2.toNat * 2 ^ 128 < 2 ^ (2 * (steps - 64)) * 2 ^ 128 := by
        calc
          radicand.limb2.toNat * 2 ^ 128 ≤ radicand.toNat := by
            rw [hvalue, hlimb3]
            omega
          _ < 2 ^ (2 * steps) := hfit
          _ = 2 ^ (2 * (steps - 64)) * 2 ^ 128 := hpow
      unfold place
      exact Nat.lt_of_mul_lt_mul_right hbound
    rw [hsplit, digitsValue_limb2 radicand (steps - 64) (by omega),
      wordDigits_eq_mod radicand.limb2 (steps - 64) (by omega),
      wordDigits_eq_mod radicand.limb1 32 (by omega),
      wordDigits_eq_mod radicand.limb0 32 (by omega), hlimb0, hlimb1, hlimb2, hvalue, hlimb3]
    simp [place]
    ring
  · -- The top limb has at most `2 * steps - 192` significant bits.
    have hsplit : steps = 96 + (steps - 96) := by omega
    have hpow : 2 ^ (2 * steps) = 2 ^ (2 * (steps - 96)) * 2 ^ 192 := by
      rw [← pow_add]
      congr 1
      omega
    have hlimb2 : radicand.limb2.toNat % place 32 = radicand.limb2.toNat := by
      apply Nat.mod_eq_of_lt
      simpa [place] using h2
    have hlimb3 : radicand.limb3.toNat % place (steps - 96) = radicand.limb3.toNat := by
      apply Nat.mod_eq_of_lt
      have hbound :
          radicand.limb3.toNat * 2 ^ 192 < 2 ^ (2 * (steps - 96)) * 2 ^ 192 := by
        calc
          radicand.limb3.toNat * 2 ^ 192 ≤ radicand.toNat := by
            rw [hvalue]
            exact Nat.le_add_left _ _
          _ < 2 ^ (2 * steps) := hfit
          _ = 2 ^ (2 * (steps - 96)) * 2 ^ 192 := hpow
      unfold place
      exact Nat.lt_of_mul_lt_mul_right hbound
    rw [hsplit, digitsValue_limb3 radicand (steps - 96) (by omega),
      wordDigits_eq_mod radicand.limb3 (steps - 96) (by omega),
      wordDigits_eq_mod radicand.limb2 32 (by omega),
      wordDigits_eq_mod radicand.limb1 32 (by omega),
      wordDigits_eq_mod radicand.limb0 32 (by omega), hlimb0, hlimb1, hlimb2, hlimb3, hvalue]
    simp [place]
    ring

/--
The restoring kernel with `steps` digits returns the exact floor root and square remainder for
every radicand below `2^(2 * steps)`, for any digit count between 64 and 125.

The upper bound keeps the remainder doubled twice inside the two-word state; the two-word
square-root kernels use `fracWidth + 1` digits.
-/
theorem rootAndRemainder_spec
    (radicand : UInt256) (steps : Nat)
    (hlower : 64 ≤ steps) (hupper : steps ≤ 125)
    (hfit : radicand.toNat < 2 ^ (2 * steps)) :
    let state := rootAndRemainder radicand steps
    state.root.toNat = Nat.sqrt radicand.toNat ∧
      state.remainder.toNat =
        radicand.toNat -
          Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat := by
  let state := rootAndRemainder radicand steps
  have hfit250 : radicand.toNat < 2 ^ 250 :=
    lt_of_lt_of_le hfit (Nat.pow_le_pow_right (by decide) (by omega))
  have hrep : RootRep128 state radicand.toNat :=
    rootAndRemainder_rep radicand steps
      (digitsValue_eq_toNat radicand steps hlower (by omega) hfit) hfit250
  exact RestoringRootState.sqrt_spec UInt128.toNat hrep

/-- Native nearest-root rounding agrees with the mathematical remainder boundary. -/
theorem roundRoot_toNat
    (radicand : UInt256) (steps : Nat)
    (hlower : 64 ≤ steps) (hupper : steps ≤ 125)
    (hfit : radicand.toNat < 2 ^ (2 * steps)) :
    (roundRoot (rootAndRemainder radicand steps)).toNat =
      let root := Nat.sqrt radicand.toNat
      let remainder := radicand.toNat - root * root
      if remainder ≤ root then root else root + 1 := by
  let state := rootAndRemainder radicand steps
  change
    (roundRoot state).toNat =
      if radicand.toNat -
            Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat ≤
          Nat.sqrt radicand.toNat then
        Nat.sqrt radicand.toNat
      else
        Nat.sqrt radicand.toNat + 1
  have hspec := rootAndRemainder_spec radicand steps hlower hupper hfit
  have hroot : state.root.toNat = Nat.sqrt radicand.toNat := hspec.1
  have hremainder :
      state.remainder.toNat =
        radicand.toNat -
          Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat :=
    hspec.2
  have hrootUpper : state.root.toNat < 2 ^ steps := by
    rw [hroot, Nat.sqrt_lt, ← pow_add, ← two_mul]
    exact hfit
  have hincrementFit : state.root.toNat + 1 < 2 ^ 128 := by
    have hcapacity : 2 ^ steps + 1 < 2 ^ 128 := by
      have := Nat.pow_le_pow_right (by decide : 0 < 2) hupper
      norm_num at this ⊢
      omega
    omega
  have hincrement :
      state.root.increment.toNat = state.root.toNat + 1 :=
    FloatLib.Numerics.FixedWord.UInt128.increment_toNat state.root hincrementFit
  by_cases hle : state.remainder.toNat ≤ state.root.toNat
  · have hnative :
        FloatLib.Numerics.FixedWord.UInt128.less state.root state.remainder = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact (Nat.not_lt_of_ge hle)
        ((FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff _ _).1 htrue)
    have hsemantic :
        radicand.toNat - Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat ≤
          Nat.sqrt radicand.toNat := by
      simpa only [hremainder, hroot] using hle
    simp only [roundRoot, hnative, Bool.false_eq_true, ite_false]
    rw [hroot]
    simp only [hsemantic, ite_true]
  · have hnative :
        FloatLib.Numerics.FixedWord.UInt128.less state.root state.remainder = true := by
      apply (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff _ _).2
      omega
    have hsemantic :
        ¬radicand.toNat - Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat ≤
          Nat.sqrt radicand.toNat := by
      intro h
      apply hle
      simpa only [hremainder, hroot] using h
    simp only [roundRoot, hnative, ite_true]
    rw [hincrement, hroot]
    simp only [hsemantic, ite_false]

end FloatLib.Numerics.FixedWord.RestoringSquareRoot
