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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.RestoringSqrt.Runtime

/-!
# Compiler certificates for restoring square root

Four word accumulators implement the two-limb recurrence for every radicand, initial state, and
digit count. The compiler substitutions preserve wrapping arithmetic outside the numeric bounds
of `RestoringSqrt.Proof`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.RestoringSquareRoot

/-- One accumulator step reassembled as a two-limb state. -/
private def rootStepWordsState (digit : UInt64) (root remainder : UInt128) :
    RestoringRootState UInt128 :=
  let expandedHi := (remainder.hi <<< 2) ||| (remainder.lo >>> 62)
  let expandedLo := (remainder.lo <<< 2) ||| digit
  let trialHi := (root.hi <<< 2) ||| (root.lo >>> 62)
  let trialLo := (root.lo <<< 2) ||| 1
  let doubledRootHi := (root.hi <<< 1) ||| (root.lo >>> 63)
  let doubledRootLo := root.lo <<< 1
  if expandedHi < trialHi || (expandedHi == trialHi && expandedLo < trialLo) then
    { root := ⟨doubledRootHi, doubledRootLo⟩, remainder := ⟨expandedHi, expandedLo⟩ }
  else
    let borrow : UInt64 := if expandedLo < trialLo then 1 else 0
    { root := ⟨doubledRootHi, doubledRootLo ||| 1⟩
      remainder := ⟨expandedHi - trialHi - borrow, expandedLo - trialLo⟩ }

private theorem rootStepWordsState_eq (digit : UInt64) (root remainder : UInt128) :
    rootStepWordsState digit root remainder = rootStep digit { root, remainder } := by
  rfl

private theorem rootLoopWords_succ (radicand : UInt256) (steps : Nat)
    (root remainder : UInt128) :
    rootLoopWords radicand (steps + 1) root.hi root.lo remainder.hi remainder.lo =
      let next := rootStepWordsState (digitAt radicand steps) root remainder
      rootLoopWords radicand steps next.root.hi next.root.lo
        next.remainder.hi next.remainder.lo := by
  unfold rootStepWordsState
  simp only [rootLoopWords]
  split <;> rfl

/-- The accumulator and state recurrences agree without capacity or digit-count hypotheses. -/
theorem rootLoopWords_eq (radicand : UInt256) (steps : Nat) (root remainder : UInt128) :
    rootLoopWords radicand steps root.hi root.lo remainder.hi remainder.lo =
      rootLoop radicand steps { root, remainder } := by
  induction steps generalizing root remainder with
  | zero => rfl
  | succ steps ih =>
      rw [rootLoopWords_succ, rootLoop, rootStepWordsState_eq]
      exact ih _ _

/-- The word implementation preserves every initial state and iteration count. -/
theorem rootLoopImpl_eq_rootLoop (radicand : UInt256) (steps : Nat)
    (state : RestoringRootState UInt128) :
    rootLoopImpl radicand steps state = rootLoop radicand steps state :=
  rootLoopWords_eq radicand steps state.root state.remainder

/-- Compile the state recurrence through its equal word-accumulator recurrence. -/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem rootLoop_eq_rootLoopImpl : rootLoop = rootLoopImpl := by
  funext radicand steps state
  exact (rootLoopImpl_eq_rootLoop radicand steps state).symm

/-- Compile the zero-initialized loop through the same word accumulators. -/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem rootAndRemainder_eq_rootAndRemainderImpl :
    rootAndRemainder = rootAndRemainderImpl := by
  funext radicand steps
  exact (rootLoopWords_eq radicand steps ⟨0, 0⟩ ⟨0, 0⟩).symm

end FloatLib.Numerics.FixedWord.RestoringSquareRoot
