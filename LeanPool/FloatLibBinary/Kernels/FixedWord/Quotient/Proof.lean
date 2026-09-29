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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Difference.Proof
public import LeanPool.FloatLibBinary.Numerics.Exact.RationalBinary
public import LeanPool.FloatLibBinary.Kernels.FixedWord.LimbRound.Proof
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Quotient.Runtime
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Correctness of restoring quotient generation

The one-word restoring loop computes exact nearest-even rational rounding under its capacity
bounds. This module also proves the two-limb step and the one-word rational logarithm.
`Quotient.Restoring128Proof` extends the step theorem to the two-limb loop. Floating-point kernels
supply their own decoding, exponent handling, and packing.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.RestoringQuotient

open FloatLib.Numerics.FixedWord

/-- One restoring-division step in the natural-number proof model. -/
def natQuotientStep (den : Nat) (state : QuotientState Nat) :
    QuotientState Nat :=
  let doubledRemainder := 2 * state.remainder
  if doubledRemainder < den then
    { quotient := 2 * state.quotient
      remainder := doubledRemainder }
  else
    { quotient := 2 * state.quotient + 1
      remainder := doubledRemainder - den }

/-- Iterate the natural-number restoring-division step `n` times. -/
def natQuotientSteps (den : Nat) :
    Nat -> QuotientState Nat -> QuotientState Nat
  | 0, state => state
  | n + 1, state => natQuotientSteps den n (natQuotientStep den state)

/--
One restoring step doubles the represented numerator, preserves a reduced remainder, and never
decreases the quotient.
-/
theorem natQuotientStep_spec (den : Nat) (state : QuotientState Nat)
    (hremainder : state.remainder < den) :
    let next := natQuotientStep den state
    next.quotient * den + next.remainder =
        2 * (state.quotient * den + state.remainder) ∧
      next.remainder < den ∧
      state.quotient ≤ next.quotient := by
  by_cases hbelow : 2 * state.remainder < den
  · simp only [natQuotientStep, hbelow, ite_true]
    refine ⟨?_, ?_, ?_⟩
    · ring
    · trivial
    · omega
  · simp only [natQuotientStep, hbelow, ite_false]
    have hge : den ≤ 2 * state.remainder := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [show (2 * state.quotient + 1) * den =
          2 * state.quotient * den + den by ring]
      rw [Nat.add_assoc, Nat.add_sub_of_le hge]
      ring
    · omega
    · omega

/--
After `n` restoring steps, the state represents the original numerator scaled by `2^n`, with a
remainder below the denominator.
-/
theorem natQuotientSteps_spec (den n : Nat)
    (state : QuotientState Nat)
    (hremainder : state.remainder < den) :
    let result := natQuotientSteps den n state
    result.quotient * den + result.remainder =
        (state.quotient * den + state.remainder) * 2 ^ n ∧
      result.remainder < den ∧
      state.quotient ≤ result.quotient := by
  induction n generalizing state with
  | zero =>
      simp [natQuotientSteps, hremainder]
  | succ n ih =>
      let next := natQuotientStep den state
      have hstep := natQuotientStep_spec den state hremainder
      have hnextRemainder : next.remainder < den := by
        simpa only [next] using hstep.2.1
      have hrest := ih next hnextRemainder
      dsimp only [natQuotientSteps]
      refine ⟨?_, hrest.2.1, le_trans hstep.2.2 hrest.2.2⟩
      rw [hrest.1, hstep.1, pow_succ]
      ring

/--
The restoring loop returns the ordinary quotient and remainder of the scaled natural-number
numerator.
-/
theorem natQuotientSteps_div_mod (den n : Nat)
    (state : QuotientState Nat)
    (hremainder : state.remainder < den) :
    let numerator := (state.quotient * den + state.remainder) * 2 ^ n
    let result := natQuotientSteps den n state
    result.quotient = numerator / den ∧
      result.remainder = numerator % den := by
  let numerator := (state.quotient * den + state.remainder) * 2 ^ n
  let result := natQuotientSteps den n state
  change result.quotient = numerator / den ∧
    result.remainder = numerator % den
  have hspec := natQuotientSteps_spec den n state hremainder
  have hdenPositive : 0 < den := by omega
  have hunique :
      numerator / den = result.quotient ∧
        numerator % den = result.remainder :=
    (Nat.div_mod_unique hdenPositive).2 <| by
      refine ⟨?_, hspec.2.1⟩
      simpa only [result, numerator, Nat.add_comm, Nat.mul_comm] using
        hspec.1
  exact ⟨hunique.1.symm, hunique.2.symm⟩

/-- Convert a native quotient state to its natural-number proof model. -/
def QuotientState.toNat (state : QuotientState UInt64) :
    QuotientState Nat :=
  { quotient := state.quotient.toNat
    remainder := state.remainder.toNat }

/-- Convert a two-limb quotient state to its natural-number proof model. -/
def QuotientState.toNat128
    (state : QuotientState FloatLib.Numerics.FixedWord.UInt128) :
    QuotientState Nat :=
  { quotient := state.quotient.toNat
    remainder := state.remainder.toNat }

/-- A bounded native-word restoring step agrees with the natural-number step. -/
private theorem quotientStep_toNat (den : UInt64) (state : QuotientState UInt64)
    (hdenFit : den.toNat < 2 ^ 63)
    (hremainder : state.remainder.toNat < den.toNat)
    (hnextFit :
      (natQuotientStep den.toNat state.toNat).quotient < 2 ^ 63) :
    (quotientStep den state).toNat =
      natQuotientStep den.toNat state.toNat := by
  have hremainderDoubleFit :
      state.remainder.toNat + state.remainder.toNat < 2 ^ 64 := by
    nlinarith
  have hremainderDouble :
      (state.remainder + state.remainder).toNat =
        2 * state.remainder.toNat := by
    rw [uint64_add_toNat_of_lt _ _ hremainderDoubleFit]
    ring
  by_cases hbelow :
      2 * state.remainder.toNat < den.toNat
  · have hnativeBelow :
        state.remainder + state.remainder < den := by
      rw [UInt64.lt_iff_toNat_lt, hremainderDouble]
      exact hbelow
    have hquotientDoubleFit :
        state.quotient.toNat + state.quotient.toNat < 2 ^ 64 := by
      have hbound :
          2 * state.quotient.toNat < 2 ^ 63 := by
        simpa only [natQuotientStep, hbelow, ite_true,
          QuotientState.toNat] using hnextFit
      nlinarith
    have hquotientDouble :
        (state.quotient + state.quotient).toNat =
          2 * state.quotient.toNat := by
      rw [uint64_add_toNat_of_lt _ _ hquotientDoubleFit]
      ring
    simp [quotientStep, natQuotientStep, QuotientState.toNat,
      hnativeBelow, hbelow, hquotientDouble, hremainderDouble]
  · have hnativeBelow :
        ¬state.remainder + state.remainder < den := by
      rw [UInt64.lt_iff_toNat_lt, hremainderDouble]
      exact hbelow
    have hge :
        den.toNat ≤
          (state.remainder + state.remainder).toNat := by
      rw [hremainderDouble]
      omega
    have hwordGe :
        den ≤ state.remainder + state.remainder := by
      exact UInt64.le_iff_toNat_le.mpr hge
    have hquotientIncrementFit :
        2 * state.quotient.toNat + 1 < 2 ^ 64 := by
      have hbound :
          2 * state.quotient.toNat + 1 < 2 ^ 63 := by
        simpa only [natQuotientStep, hbelow, ite_false,
          QuotientState.toNat] using hnextFit
      omega
    have hquotientDoubleFit :
        state.quotient.toNat + state.quotient.toNat < 2 ^ 64 := by
      omega
    have hquotientDouble :
        (state.quotient + state.quotient).toNat =
          2 * state.quotient.toNat := by
      rw [uint64_add_toNat_of_lt _ _ hquotientDoubleFit]
      ring
    have hquotientIncrement :
        (state.quotient + state.quotient + 1).toNat =
          2 * state.quotient.toNat + 1 := by
      have hone : (1 : UInt64).toNat = 1 := by decide
      rw [uint64_add_toNat_of_lt _ _]
      · rw [hquotientDouble, hone]
      · rw [hquotientDouble]
        exact hquotientIncrementFit
    have hremainderSubtract :
        (state.remainder + state.remainder - den).toNat =
          2 * state.remainder.toNat - den.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ hwordGe, hremainderDouble]
    simp [quotientStep, natQuotientStep, QuotientState.toNat,
      hnativeBelow, hbelow, hquotientIncrement, hremainderSubtract]

/-- A bounded native-word restoring loop agrees with its natural-number iteration. -/
private theorem quotientSteps_toNat (den : UInt64) (n : Nat)
    (state : QuotientState UInt64)
    (hden : den ≠ 0)
    (hdenFit : den.toNat < 2 ^ 63)
    (hremainder : state.remainder.toNat < den.toNat)
    (hresultFit :
      (natQuotientSteps den.toNat n state.toNat).quotient < 2 ^ 63) :
    (quotientSteps den n state).toNat =
      natQuotientSteps den.toNat n state.toNat := by
  have hdenPositive : 0 < den.toNat := by
    simpa [Nat.pos_iff_ne_zero, ← UInt64.toNat_inj] using hden
  induction n generalizing state with
  | zero =>
      rfl
  | succ n ih =>
      let nextNat := natQuotientStep den.toNat state.toNat
      have hstepSpec :=
        natQuotientStep_spec den.toNat state.toNat hremainder
      have hnextRemainder : nextNat.remainder < den.toNat := by
        simpa only [nextNat] using hstepSpec.2.1
      have hrestSpec :=
        natQuotientSteps_spec den.toNat n nextNat hnextRemainder
      have hnextFit : nextNat.quotient < 2 ^ 63 := by
        apply lt_of_le_of_lt hrestSpec.2.2
        simpa only [quotientSteps, natQuotientSteps, nextNat] using
          hresultFit
      have hstep :=
        quotientStep_toNat den state hdenFit hremainder
          (by simpa only [nextNat] using hnextFit)
      have hnativeRemainder :
          (quotientStep den state).remainder.toNat < den.toNat := by
        rw [show (quotientStep den state).remainder.toNat =
          (quotientStep den state).toNat.remainder by rfl, hstep]
        exact hnextRemainder
      change
        (quotientSteps den n (quotientStep den state)).toNat =
          natQuotientSteps den.toNat n nextNat
      have hnextEq :
          (quotientStep den state).toNat = nextNat := by
        simpa only [nextNat] using hstep
      rw [← hnextEq]
      apply ih (quotientStep den state) hnativeRemainder
      rw [hstep]
      simpa only [quotientSteps, natQuotientSteps, nextNat] using
        hresultFit

/-- One native two-limb restoring step refines the natural-number recurrence. -/
theorem quotientStep128_toNat
    (den : FloatLib.Numerics.FixedWord.UInt128)
    (state : QuotientState FloatLib.Numerics.FixedWord.UInt128)
    (hdenFit : den.toNat < 2 ^ 127)
    (hremainder : state.remainder.toNat < den.toNat)
    (hnextFit :
      (natQuotientStep den.toNat state.toNat128).quotient < 2 ^ 128) :
    (quotientStep128 den state).toNat128 =
      natQuotientStep den.toNat state.toNat128 := by
  let doubledQuotient :=
    FloatLib.Numerics.FixedWord.UInt128.shiftLeft state.quotient 1
  let doubledRemainder :=
    FloatLib.Numerics.FixedWord.UInt128.shiftLeft state.remainder 1
  have hremainderDoubleFit :
      state.remainder.toNat + state.remainder.toNat < 2 ^ 128 := by
    nlinarith
  have hremainderShiftFit :
      state.remainder.toNat <<< 1 < 2 ^ 128 := by
    simp only [Nat.shiftLeft_eq, pow_one]
    omega
  have hremainderDouble :
      doubledRemainder.toNat = 2 * state.remainder.toNat := by
    dsimp only [doubledRemainder]
    rw [FloatLib.Numerics.FixedWord.UInt128.shiftLeft_toNat
      _ 1 (by omega) hremainderShiftFit]
    simp [Nat.shiftLeft_eq, Nat.mul_comm]
  by_cases hbelow :
      2 * state.remainder.toNat < den.toNat
  · have hnativeBelow :
        FloatLib.Numerics.FixedWord.UInt128.less
            doubledRemainder den = true := by
      apply
        (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff
          doubledRemainder den).2
      rwa [hremainderDouble]
    have hquotientDoubleFit :
        state.quotient.toNat + state.quotient.toNat < 2 ^ 128 := by
      have hbound :
          2 * state.quotient.toNat < 2 ^ 128 := by
        simpa only [natQuotientStep, hbelow, ite_true,
          QuotientState.toNat128] using hnextFit
      nlinarith
    have hquotientShiftFit :
        state.quotient.toNat <<< 1 < 2 ^ 128 := by
      simp only [Nat.shiftLeft_eq, pow_one]
      omega
    have hquotientDouble :
        doubledQuotient.toNat = 2 * state.quotient.toNat := by
      dsimp only [doubledQuotient]
      rw [FloatLib.Numerics.FixedWord.UInt128.shiftLeft_toNat
        _ 1 (by omega) hquotientShiftFit]
      simp [Nat.shiftLeft_eq, Nat.mul_comm]
    have hstep :
        quotientStep128 den state =
          { quotient := doubledQuotient
            remainder := doubledRemainder } := by
      change
        (if FloatLib.Numerics.FixedWord.UInt128.less
              doubledRemainder den = true then
            (⟨doubledQuotient, doubledRemainder⟩ :
              QuotientState FloatLib.Numerics.FixedWord.UInt128)
          else
            ⟨doubledQuotient.setLowBit,
              FloatLib.Numerics.FixedWord.UInt128.sub
                doubledRemainder den⟩) =
          (⟨doubledQuotient, doubledRemainder⟩ :
            QuotientState FloatLib.Numerics.FixedWord.UInt128)
      rw [ite_eq_left hnativeBelow]
    rw [hstep]
    simp only [QuotientState.toNat128, natQuotientStep,
      hbelow, ite_true]
    rw [hquotientDouble, hremainderDouble]
  · have hnativeBelow :
        FloatLib.Numerics.FixedWord.UInt128.less
            doubledRemainder den = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      have hlt :=
        (FloatLib.Numerics.FixedWord.UInt128.less_eq_true_iff
          doubledRemainder den).1 htrue
      rw [hremainderDouble] at hlt
      exact hbelow hlt
    have hge : den.toNat ≤ doubledRemainder.toNat := by
      rw [hremainderDouble]
      omega
    have hnextQuotientFit :
        2 * state.quotient.toNat + 1 < 2 ^ 128 := by
      simpa only [natQuotientStep, hbelow, ite_false,
        QuotientState.toNat128] using hnextFit
    have hquotientDoubleFit :
        state.quotient.toNat + state.quotient.toNat < 2 ^ 128 := by
      omega
    have hquotientShiftFit :
        state.quotient.toNat <<< 1 < 2 ^ 128 := by
      simp only [Nat.shiftLeft_eq, pow_one]
      omega
    have hquotientDouble :
        doubledQuotient.toNat = 2 * state.quotient.toNat := by
      dsimp only [doubledQuotient]
      rw [FloatLib.Numerics.FixedWord.UInt128.shiftLeft_toNat
        _ 1 (by omega) hquotientShiftFit]
      simp [Nat.shiftLeft_eq, Nat.mul_comm]
    have hquotientSetLowBit :
        doubledQuotient.setLowBit.toNat =
          2 * state.quotient.toNat + 1 := by
      rw [FloatLib.Numerics.FixedWord.UInt128.setLowBit_toNat,
        hquotientDouble]
      have happend :=
        Nat.shiftLeft_add_eq_or_of_lt
          (a := state.quotient.toNat) (i := 1) (b := 1)
          (by norm_num)
      simpa [Nat.shiftLeft_eq, Nat.mul_comm] using happend.symm
    have hremainderSubtract :
        (FloatLib.Numerics.FixedWord.UInt128.sub
            doubledRemainder den).toNat =
          2 * state.remainder.toNat - den.toNat := by
      rw [FloatLib.Numerics.FixedWord.UInt128.sub_toNat
        doubledRemainder den hge, hremainderDouble]
    have hstep :
        quotientStep128 den state =
          { quotient := doubledQuotient.setLowBit
            remainder :=
              FloatLib.Numerics.FixedWord.UInt128.sub
                doubledRemainder den } := by
      change
        (if FloatLib.Numerics.FixedWord.UInt128.less
              doubledRemainder den = true then
            (⟨doubledQuotient, doubledRemainder⟩ :
              QuotientState FloatLib.Numerics.FixedWord.UInt128)
          else
            ⟨doubledQuotient.setLowBit,
              FloatLib.Numerics.FixedWord.UInt128.sub
                doubledRemainder den⟩) =
          (⟨doubledQuotient.setLowBit,
              FloatLib.Numerics.FixedWord.UInt128.sub
                doubledRemainder den⟩ :
            QuotientState FloatLib.Numerics.FixedWord.UInt128)
      rw [ite_eq_right (by simpa only [hnativeBelow] using Bool.false_ne_true)]
    rw [hstep]
    simp only [QuotientState.toNat128, natQuotientStep,
      hbelow, ite_false]
    rw [hquotientSetLowBit, hremainderSubtract]

/--
Native restoring division computes the exact nearest-even rounding of the scaled rational quotient.
-/
theorem roundScaledQuotient_toNat
    (num den : UInt64) (shift : Nat)
    (hden : den ≠ 0)
    (hdenFit : den.toNat < 2 ^ 63)
    (hquotientFit :
      (num.toNat <<< shift) / den.toNat + 1 < 2 ^ 63) :
    (roundScaledQuotient num den shift).toNat =
      Numerics.roundQuotientEven
        (num.toNat <<< shift) den.toNat := by
  let initial : QuotientState UInt64 :=
    { quotient := num / den
      remainder := num % den }
  let initialNat : QuotientState Nat :=
    { quotient := num.toNat / den.toNat
      remainder := num.toNat % den.toNat }
  let final := quotientSteps den shift initial
  let finalNat := natQuotientSteps den.toNat shift initialNat
  have hdenNat : den.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hden
  have hremainder :
      initial.remainder.toNat < den.toNat := by
    dsimp only [initial]
    rw [UInt64.toNat_mod]
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero hdenNat)
  have hinitial :
      initial.toNat = initialNat := by
    simp [initial, initialNat, QuotientState.toNat, UInt64.toNat_div,
      UInt64.toNat_mod]
  have hscaled :
      (initialNat.quotient * den.toNat + initialNat.remainder) *
          2 ^ shift =
        num.toNat <<< shift := by
    rw [Nat.shiftLeft_eq]
    congr 1
    simpa [initialNat, Nat.mul_comm] using
      (Nat.div_add_mod num.toNat den.toNat)
  have hfinalNat :
      finalNat.quotient = (num.toNat <<< shift) / den.toNat ∧
        finalNat.remainder = (num.toNat <<< shift) % den.toNat := by
    have hspec :=
      natQuotientSteps_div_mod den.toNat shift initialNat
        (by
          dsimp only [initialNat]
          exact Nat.mod_lt _ (Nat.pos_of_ne_zero hdenNat))
    simpa only [finalNat, hscaled] using hspec
  have hsteps :
      final.toNat = finalNat := by
    have hfit :
        (natQuotientSteps den.toNat shift initial.toNat).quotient <
          2 ^ 63 := by
      rw [hinitial]
      change finalNat.quotient < 2 ^ 63
      rw [hfinalNat.1]
      omega
    have hnative :=
      quotientSteps_toNat den shift initial hden hdenFit
        hremainder hfit
    simpa only [final, finalNat, hinitial] using hnative
  have hfinalQuotient :
      final.quotient.toNat =
        (num.toNat <<< shift) / den.toNat := by
    rw [show final.quotient.toNat = final.toNat.quotient by rfl,
      hsteps, hfinalNat.1]
  have hfinalRemainder :
      final.remainder.toNat =
        (num.toNat <<< shift) % den.toNat := by
    rw [show final.remainder.toNat = final.toNat.remainder by rfl,
      hsteps, hfinalNat.2]
  have hremainderLt :
      final.remainder.toNat < den.toNat := by
    rw [hfinalRemainder]
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero hdenNat)
  have hdoubleFit :
      final.remainder.toNat + final.remainder.toNat < 2 ^ 64 := by
    nlinarith
  have hdouble :
      (final.remainder + final.remainder).toNat =
        2 * ((num.toNat <<< shift) % den.toNat) := by
    rw [uint64_add_toNat_of_lt _ _ hdoubleFit, hfinalRemainder]
    ring
  have hincrementFit :
      final.quotient.toNat + 1 < 2 ^ 64 := by
    rw [hfinalQuotient]
    exact lt_trans hquotientFit (by norm_num)
  have hincrement :
      (final.quotient + 1).toNat =
        (num.toNat <<< shift) / den.toNat + 1 := by
    have hone : (1 : UInt64).toNat = 1 := by decide
    rw [uint64_add_toNat_of_lt _ _]
    · rw [hfinalQuotient, hone]
    · simpa only [hone] using hincrementFit
  have heven :
      (final.quotient % 2 == 0) ↔
        ((num.toNat <<< shift) / den.toNat) % 2 == 0 := by
    simp only [beq_iff_eq]
    constructor
    · intro h
      have hnat := congrArg UInt64.toNat h
      simpa [UInt64.toNat_mod, hfinalQuotient] using hnat
    · intro h
      apply UInt64.toNat_inj.mp
      simpa [UInt64.toNat_mod, hfinalQuotient] using h
  unfold roundScaledQuotient
  change (roundQuotientState den final).toNat =
    Numerics.roundQuotientEven
      (num.toNat <<< shift) den.toNat
  unfold roundQuotientState Numerics.roundQuotientEven
  simp only [UInt64.lt_iff_toNat_lt, hdouble, heven]
  split_ifs <;> simp_all


/--
The native-word rational logarithm selector agrees with the exact representation-independent
`floorLog2` specification for nonzero operands.
-/
theorem floorLog2RatWord_eq (num den : UInt64)
    (hnum : num ≠ 0) (hden : den ≠ 0) :
    floorLog2RatWord num den =
      FloatLib.Numerics.RationalBinary.floorLog2
        num.toNat den.toNat := by
  have hnumNat : num.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hnum
  have hdenNat : den.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hden
  have hnumLog := FloatLib.Numerics.FixedWord.log2_toNat num
  have hdenLog := FloatLib.Numerics.FixedWord.log2_toNat den
  have hnumLogLt : num.toNat.log2 < 64 := by
    rw [Nat.log2_lt hnumNat]
    exact num.toNat_lt
  have hdenLogLt : den.toNat.log2 < 64 := by
    rw [Nat.log2_lt hdenNat]
    exact den.toNat_lt
  have hnumWordLogLt : num.log2.toNat < 64 := by
    rw [hnumLog]
    exact hnumLogLt
  have hdenWordLogLt : den.log2.toNat < 64 := by
    rw [hdenLog]
    exact hdenLogLt
  unfold floorLog2RatWord
    FloatLib.Numerics.RationalBinary.floorLog2
  rw [← hnumLog, ← hdenLog]
  by_cases hlogs : den.log2.toNat ≤ num.log2.toNat
  · simp only [hlogs, ite_true]
    let shift := num.log2.toNat - den.log2.toNat
    have hshiftLt : shift < 64 := by
      dsimp only [shift]
      omega
    have hdenShiftFit :
        den.toNat <<< shift < 2 ^ 64 := by
      have hbound :
          den.toNat <<< shift <
            2 ^ (den.toNat.log2 + 1 + shift) :=
        Nat.shiftLeft_lt Nat.lt_log2_self
      rw [← hdenLog] at hbound
      have hexponent :
          den.log2.toNat + 1 + shift =
            num.log2.toNat + 1 := by
        dsimp only [shift]
        omega
      rw [hexponent] at hbound
      exact lt_of_lt_of_le hbound <|
        Nat.pow_le_pow_right (by decide) (by omega)
    have hshifted :
        (den <<< UInt64.ofNat shift).toNat =
          den.toNat <<< shift :=
      FloatLib.Numerics.FixedWord.shiftLeft_toNat den shift hshiftLt hdenShiftFit
    have hinitial :
        Int.ofNat num.log2.toNat - Int.ofNat den.log2.toNat =
          Int.ofNat shift := by
      change (num.log2.toNat : Int) - den.log2.toNat = (shift : Int)
      simpa only [shift] using (Int.ofNat_sub hlogs).symm
    simp only [show num.log2.toNat - den.log2.toNat = shift by rfl]
    rw [hinitial]
    simp only [Numerics.RationalBinary.lessThanPowerOfTwo_ofNat]
    have hcompare :
        (num < den <<< UInt64.ofNat shift) ↔
          num.toNat < den.toNat <<< shift := by
      rw [UInt64.lt_iff_toNat_lt, hshifted]
    simp only [hcompare]
    by_cases hbelow : num.toNat < den.toNat <<< shift
    · simp [hbelow]
    · simp only [hbelow, ↓reduceIte, Int.ofNat_eq_natCast, Nat.shiftLeft_eq', decide_false,
      Bool.false_eq_true,
        right_eq_ite_iff, left_eq_add, one_ne_zero, imp_false, Bool.not_eq_true]
      have hnumUpper : num.toNat < 2 ^ (num.toNat.log2 + 1) :=
        Nat.lt_log2_self
      have hdenLower : 2 ^ den.toNat.log2 ≤ den.toNat :=
        Nat.log2_self_le hdenNat
      have hupper :
          num.toNat < den.toNat <<< (shift + 1) := by
        rw [Nat.shiftLeft_eq]
        calc
          num.toNat < 2 ^ (num.toNat.log2 + 1) := hnumUpper
          _ = 2 ^ den.toNat.log2 * 2 ^ (shift + 1) := by
            rw [← pow_add]
            congr 1
            rw [← hnumLog, ← hdenLog]
            dsimp only [shift]
            omega
          _ ≤ den.toNat * 2 ^ (shift + 1) :=
            Nat.mul_le_mul_right _ hdenLower
      have hnotGe :
          Numerics.RationalBinary.atLeastPowerOfTwo num.toNat den.toNat
              (Int.ofNat shift + 1) = false := by
        have hexponent :
            Int.ofNat shift + 1 = Int.ofNat (shift + 1) := by
          exact Int.ofNat_add_one_out shift
        rw [hexponent]
        simp [Numerics.RationalBinary.atLeastPowerOfTwo, hupper]
      simpa [hnotGe]
  · have hlogsLt : num.log2.toNat < den.log2.toNat := by
      omega
    simp only [hlogs, ite_false]
    let shift := den.log2.toNat - num.log2.toNat
    have hshiftPos : 0 < shift := by
      dsimp only [shift]
      omega
    have hshiftLt : shift < 64 := by
      dsimp only [shift]
      omega
    have hnumShiftFit :
        num.toNat <<< shift < 2 ^ 64 := by
      have hbound :
          num.toNat <<< shift <
            2 ^ (num.toNat.log2 + 1 + shift) :=
        Nat.shiftLeft_lt Nat.lt_log2_self
      rw [← hnumLog] at hbound
      have hexponent :
          num.log2.toNat + 1 + shift =
            den.log2.toNat + 1 := by
        dsimp only [shift]
        omega
      rw [hexponent] at hbound
      exact lt_of_lt_of_le hbound <|
        Nat.pow_le_pow_right (by decide) (by omega)
    have hshifted :
        (num <<< UInt64.ofNat shift).toNat =
          num.toNat <<< shift :=
      FloatLib.Numerics.FixedWord.shiftLeft_toNat num shift hshiftLt hnumShiftFit
    have hinitial :
        Int.ofNat num.log2.toNat - Int.ofNat den.log2.toNat =
          -Int.ofNat shift := by
      change (num.log2.toNat : Int) - den.log2.toNat = -(shift : Int)
      dsimp only [shift]
      rw [Int.ofNat_sub (Nat.le_of_lt hlogsLt)]
      ring
    simp only [show den.log2.toNat - num.log2.toNat = shift by rfl]
    rw [hinitial]
    have hnegative :
        -Int.ofNat shift = Int.negSucc (shift - 1) := by
      change -(shift : Int) = Int.negSucc (shift - 1)
      apply Int.neg_ofNat_eq_negSucc_iff.mpr
      omega
    rw [hnegative]
    simp only [Numerics.RationalBinary.lessThanPowerOfTwo_negSucc]
    have hshiftSucc : shift - 1 + 1 = shift := by omega
    have hcompare :
        (num <<< UInt64.ofNat shift < den) ↔
          num.toNat <<< shift < den.toNat := by
      rw [UInt64.lt_iff_toNat_lt, hshifted]
    simp only [hshiftSucc, hcompare]
    by_cases hbelow : num.toNat <<< shift < den.toNat
    · simp [hbelow]
      have hnotGe :
          Numerics.RationalBinary.atLeastPowerOfTwo num.toNat den.toNat
              (Int.negSucc (shift - 1)) = false := by
        simp [Numerics.RationalBinary.atLeastPowerOfTwo,
          hshiftSucc, hbelow]
      simpa [hnotGe]
    · simp only [hbelow, ↓reduceIte, Nat.shiftLeft_eq', decide_false, Bool.false_eq_true,
      right_eq_ite_iff,
        left_eq_add, one_ne_zero, imp_false, Bool.not_eq_true]
      have hnumUpper : num.toNat < 2 ^ (num.toNat.log2 + 1) :=
        Nat.lt_log2_self
      have hdenLower : 2 ^ den.toNat.log2 ≤ den.toNat :=
        Nat.log2_self_le hdenNat
      by_cases hshiftOne : shift = 1
      · have hnumDen : num.toNat < den.toNat := by
          calc
            num.toNat < 2 ^ (num.toNat.log2 + 1) := hnumUpper
            _ = 2 ^ den.toNat.log2 := by
              rw [← hnumLog, ← hdenLog]
              congr 1
              dsimp only [shift] at hshiftOne
              omega
            _ ≤ den.toNat := hdenLower
        have hnotGe :
            Numerics.RationalBinary.atLeastPowerOfTwo num.toNat den.toNat 0 = false := by
          simp [Numerics.RationalBinary.atLeastPowerOfTwo, hnumDen]
        have hexponent :
            Int.negSucc (shift - 1) + 1 = 0 := by
          simp [Int.negSucc_eq, hshiftOne]
        simp [hexponent, hnotGe]
      · have hshiftTwo : 2 ≤ shift := by omega
        have hupper :
            num.toNat <<< (shift - 1) < den.toNat := by
          rw [Nat.shiftLeft_eq]
          calc
            num.toNat * 2 ^ (shift - 1) <
                2 ^ (num.toNat.log2 + 1) * 2 ^ (shift - 1) :=
              Nat.mul_lt_mul_of_pos_right hnumUpper (pow_pos (by decide) _)
            _ = 2 ^ den.toNat.log2 := by
              rw [← pow_add]
              congr 1
              rw [← hnumLog, ← hdenLog]
              dsimp only [shift]
              omega
            _ ≤ den.toNat := hdenLower
        have hexponent :
            Int.negSucc (shift - 1) + 1 =
              Int.negSucc (shift - 2) := by
          omega
        have hnotGe :
            Numerics.RationalBinary.atLeastPowerOfTwo num.toNat den.toNat
                (Int.negSucc (shift - 2)) = false := by
          have hamount : shift - 2 + 1 = shift - 1 := by omega
          simp [Numerics.RationalBinary.atLeastPowerOfTwo,
            hamount, hupper]
        simp [hexponent, hnotGe]

/--
The native quotient logarithm differs from the difference of the operand logarithms by at most
one.
-/
theorem floorLog2RatWord_log_bounds (num den : UInt64) :
    Int.ofNat num.log2.toNat - Int.ofNat den.log2.toNat - 1 ≤
        floorLog2RatWord num den ∧
      floorLog2RatWord num den ≤
        Int.ofNat num.log2.toNat - Int.ofNat den.log2.toNat := by
  unfold floorLog2RatWord
  by_cases hlogs : den.log2.toNat ≤ num.log2.toNat
  · simp only [hlogs, ite_true]
    have hdifference :
        Int.ofNat num.log2.toNat - Int.ofNat den.log2.toNat =
          Int.ofNat (num.log2.toNat - den.log2.toNat) := by
      simpa using (Int.ofNat_sub hlogs).symm
    rw [hdifference]
    split <;> omega
  · have hlogsLt : num.log2.toNat < den.log2.toNat := by
      omega
    simp only [hlogs, ite_false]
    have hdifference :
        Int.ofNat num.log2.toNat - Int.ofNat den.log2.toNat =
          -Int.ofNat (den.log2.toNat - num.log2.toNat) := by
      change (num.log2.toNat : Int) - den.log2.toNat =
        -(den.log2.toNat - num.log2.toNat : Nat)
      rw [Int.ofNat_sub (Nat.le_of_lt hlogsLt)]
      ring
    rw [hdifference]
    split <;> omega

end FloatLib.Numerics.FixedWord.RestoringQuotient
