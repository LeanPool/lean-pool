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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Quotient.Runtime

/-!
# Compiler certificates for restoring quotient loops

The logical restoring loop is convenient for proofs, while the primitive-word accumulator avoids
allocating a state at every generated quotient bit. This module proves the one- and two-limb loops
extensionally equal and registers the optimized direction with `@[csimp]`.

Keeping this certificate separate from `Quotient.Proof` matters for executable clients: they can
enable the verified compiler rewrite without importing the much larger rational-arithmetic proof
development.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.RestoringQuotient

/-- The unboxed one-word accumulators preserve every step of the restoring recurrence. -/
theorem quotientStepsWords_eq (den : UInt64) (n : Nat) (quotient remainder : UInt64) :
    quotientStepsWords den n quotient remainder =
      quotientSteps den n { quotient, remainder } := by
  induction n generalizing quotient remainder with
  | zero => rfl
  | succ n ih =>
      simp only [quotientStepsWords, quotientSteps, quotientStep]
      split <;> exact ih _ _

/-- The one-word implementation agrees for every state and iteration count. -/
theorem quotientStepsImpl_eq_quotientSteps
    (den : UInt64) (n : Nat) (state : QuotientState UInt64) :
    quotientStepsImpl den n state = quotientSteps den n state := by
  exact quotientStepsWords_eq den n state.quotient state.remainder

/-- Compile one-word restoring division through primitive accumulators. -/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem quotientSteps_eq_quotientStepsImpl :
    quotientSteps = quotientStepsImpl := by
  funext den n state
  exact (quotientStepsImpl_eq_quotientSteps den n state).symm

/--
Compile scaled quotient rounding through the same accumulator.

This equation also replaces calls whose original body was compiled before the loop certificate
was imported.
-/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem roundScaledQuotient_eq_roundScaledQuotientImpl :
    roundScaledQuotient = roundScaledQuotientImpl := by
  funext num den shift
  simp only [roundScaledQuotient, roundScaledQuotientImpl, quotientStepsWords_eq]

/-- Reassemble one primitive-word accumulator step as a two-limb quotient state. -/
private def quotientStep128WordsState
    (den quotient remainder : FloatLib.Numerics.FixedWord.UInt128) :
    QuotientState FloatLib.Numerics.FixedWord.UInt128 :=
  let doubledQuotientHi :=
    (quotient.hi <<< 1) ||| (quotient.lo >>> 63)
  let doubledQuotientLo := quotient.lo <<< 1
  let doubledRemainderHi :=
    (remainder.hi <<< 1) ||| (remainder.lo >>> 63)
  let doubledRemainderLo := remainder.lo <<< 1
  let below :=
    doubledRemainderHi < den.hi ||
      (doubledRemainderHi == den.hi && doubledRemainderLo < den.lo)
  if below then
    { quotient := ⟨doubledQuotientHi, doubledQuotientLo⟩
      remainder := ⟨doubledRemainderHi, doubledRemainderLo⟩ }
  else
    let borrow : UInt64 := if doubledRemainderLo < den.lo then 1 else 0
    { quotient := ⟨doubledQuotientHi, doubledQuotientLo ||| 1⟩
      remainder :=
        ⟨doubledRemainderHi - den.hi - borrow,
          doubledRemainderLo - den.lo⟩ }

/-- The reassembled primitive-word step is the logical two-limb restoring step. -/
private theorem quotientStep128WordsState_eq
    (den quotient remainder : FloatLib.Numerics.FixedWord.UInt128) :
    quotientStep128WordsState den quotient remainder =
      quotientStep128 den
        { quotient := quotient, remainder := remainder } := by
  unfold quotientStep128WordsState quotientStep128
  rfl

/-- The primitive-word accumulator unfolds by one reassembled restoring step. -/
private theorem quotientSteps128Words_succ
    (den : FloatLib.Numerics.FixedWord.UInt128) (n : Nat)
    (quotient remainder : FloatLib.Numerics.FixedWord.UInt128) :
    quotientSteps128Words den.hi den.lo (n + 1)
        quotient.hi quotient.lo remainder.hi remainder.lo =
      let next := quotientStep128WordsState den quotient remainder
      quotientSteps128Words den.hi den.lo n
        next.quotient.hi next.quotient.lo
        next.remainder.hi next.remainder.lo := by
  unfold quotientStep128WordsState
  simp only [quotientSteps128Words]
  split <;> rfl

/-- Every primitive-word accumulator iteration agrees with the logical two-limb loop. -/
private theorem quotientSteps128Words_eq
    (den : FloatLib.Numerics.FixedWord.UInt128) (n : Nat)
    (quotient remainder : FloatLib.Numerics.FixedWord.UInt128) :
    quotientSteps128Words den.hi den.lo n
        quotient.hi quotient.lo remainder.hi remainder.lo =
      quotientSteps128 den n
        { quotient := quotient, remainder := remainder } := by
  induction n generalizing quotient remainder with
  | zero =>
      rfl
  | succ n ih =>
      rw [quotientSteps128Words_succ, quotientSteps128]
      rw [quotientStep128WordsState_eq]
      simpa using
        ih (quotientStep128 den
              { quotient := quotient, remainder := remainder }).quotient
          (quotientStep128 den
              { quotient := quotient, remainder := remainder }).remainder

/-- The primitive-word accumulator implements the logical two-limb restoring recurrence. -/
theorem quotientSteps128Impl_eq_quotientSteps128
    (den : FloatLib.Numerics.FixedWord.UInt128) (n : Nat)
    (state : QuotientState FloatLib.Numerics.FixedWord.UInt128) :
    quotientSteps128Impl den n state =
      quotientSteps128 den n state := by
  unfold quotientSteps128Impl
  simpa using
    quotientSteps128Words_eq den n state.quotient state.remainder

/-- Compile the logical two-limb quotient loop through its verified word accumulator. -/
-- grind: no rule; this compiler substitution exposes an implementation accumulator.
@[csimp] theorem quotientSteps128_eq_quotientSteps128Impl :
    quotientSteps128 = quotientSteps128Impl := by
  funext den n state
  exact (quotientSteps128Impl_eq_quotientSteps128 den n state).symm

end FloatLib.Numerics.FixedWord.RestoringQuotient
