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
public import LeanPool.FloatLibBinary.Kernels.FixedWord.LimbRound.Runtime

/-!
# Fixed-word restoring square-root runtime

The restoring loop consumes a four-word radicand two bits at a time and retains the root and
remainder in two words. `RestoringSqrt.Proof` proves exactness under the digit-count and capacity
bounds stated below.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.RestoringSquareRoot

/-- Shift a two-word value left by one bit, discarding overflow. -/
@[inline] def shiftLeftOne
    (value : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  {
    hi := (value.hi <<< 1) ||| (value.lo >>> 63)
    lo := value.lo <<< 1
  }

/-- Shift a two-word value left by two bits, discarding overflow. -/
@[inline] def shiftLeftTwo
    (value : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  {
    hi := (value.hi <<< 2) ||| (value.lo >>> 62)
    lo := value.lo <<< 2
  }

/-- Read base-four digit `index` from a four-word radicand, for `index < 128`. -/
@[inline] def digitAt
    (radicand : FloatLib.Numerics.FixedWord.UInt256) (index : Nat) : UInt64 :=
  if index < 32 then
    (radicand.limb0 >>> UInt64.ofNat (2 * index)) &&& 3
  else if index < 64 then
    (radicand.limb1 >>> UInt64.ofNat (2 * (index - 32))) &&& 3
  else if index < 96 then
    (radicand.limb2 >>> UInt64.ofNat (2 * (index - 64))) &&& 3
  else
    (radicand.limb3 >>> UInt64.ofNat (2 * (index - 96))) &&& 3

/-- One base-four restoring square-root step. -/
@[inline] def rootStep (digit : UInt64)
    (state : RestoringRootState FloatLib.Numerics.FixedWord.UInt128) :
    RestoringRootState FloatLib.Numerics.FixedWord.UInt128 :=
  let expandedBase := shiftLeftTwo state.remainder
  let expanded : FloatLib.Numerics.FixedWord.UInt128 :=
    { expandedBase with lo := expandedBase.lo ||| digit }
  let trialBase := shiftLeftTwo state.root
  let trial : FloatLib.Numerics.FixedWord.UInt128 :=
    trialBase.setLowBit
  let doubledRoot := shiftLeftOne state.root
  if FloatLib.Numerics.FixedWord.UInt128.less expanded trial then
    {
      root := doubledRoot
      remainder := expanded
    }
  else
    {
      root := doubledRoot.setLowBit
      remainder := FloatLib.Numerics.FixedWord.UInt128.sub expanded trial
    }

/-- Consume base-four digits from most significant to least significant. -/
@[inline] def rootLoop
    (radicand : FloatLib.Numerics.FixedWord.UInt256) :
    Nat → RestoringRootState FloatLib.Numerics.FixedWord.UInt128 →
      RestoringRootState FloatLib.Numerics.FixedWord.UInt128
  | 0, state => state
  | steps + 1, state =>
      rootLoop radicand steps (rootStep (digitAt radicand steps) state)

/-- Consume base-four digits with four word accumulators, constructing only the final state. -/
def rootLoopWords
    (radicand : FloatLib.Numerics.FixedWord.UInt256) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 →
      RestoringRootState FloatLib.Numerics.FixedWord.UInt128
  | 0, rootHi, rootLo, remainderHi, remainderLo =>
      { root := ⟨rootHi, rootLo⟩, remainder := ⟨remainderHi, remainderLo⟩ }
  | steps + 1, rootHi, rootLo, remainderHi, remainderLo =>
      let expandedHi := (remainderHi <<< 2) ||| (remainderLo >>> 62)
      let expandedLo := (remainderLo <<< 2) ||| digitAt radicand steps
      let trialHi := (rootHi <<< 2) ||| (rootLo >>> 62)
      let trialLo := (rootLo <<< 2) ||| 1
      let doubledRootHi := (rootHi <<< 1) ||| (rootLo >>> 63)
      let doubledRootLo := rootLo <<< 1
      if expandedHi < trialHi || (expandedHi == trialHi && expandedLo < trialLo) then
        rootLoopWords radicand steps
          doubledRootHi doubledRootLo expandedHi expandedLo
      else
        let borrow : UInt64 := if expandedLo < trialLo then 1 else 0
        rootLoopWords radicand steps
          doubledRootHi (doubledRootLo ||| 1)
          (expandedHi - trialHi - borrow) (expandedLo - trialLo)

/-- The word-accumulator implementation of `rootLoop`, including its wrapping arithmetic. -/
@[inline] def rootLoopImpl
    (radicand : FloatLib.Numerics.FixedWord.UInt256) (steps : Nat)
    (state : RestoringRootState FloatLib.Numerics.FixedWord.UInt128) :
    RestoringRootState FloatLib.Numerics.FixedWord.UInt128 :=
  rootLoopWords radicand steps state.root.hi state.root.lo state.remainder.hi state.remainder.lo

/--
Compute the floor root and exact square remainder from the requested base-four digits.

The digit count fixes the verified capacity: `rootAndRemainder_spec` covers radicands below
`2^(2 * steps)` for any digit count from 64 to 125. Larger radicands lose their leading digits,
so the result need not be the root of the original radicand.
-/
@[inline] def rootAndRemainder
    (radicand : FloatLib.Numerics.FixedWord.UInt256) (steps : Nat) :
    RestoringRootState FloatLib.Numerics.FixedWord.UInt128 :=
  rootLoop radicand steps
    { root := ⟨0, 0⟩, remainder := ⟨0, 0⟩ }

/-- Run the word-accumulator loop from zero root and remainder. -/
@[inline] def rootAndRemainderImpl
    (radicand : FloatLib.Numerics.FixedWord.UInt256) (steps : Nat) :
    RestoringRootState FloatLib.Numerics.FixedWord.UInt128 :=
  rootLoopWords radicand steps 0 0 0 0

/--
Round a floor root to the nearest integer root.

The root increments exactly when the remainder exceeds the root, which is the midpoint test for
the square. `roundRoot_toNat` verifies this for every digit count from 64 to 125.
-/
@[inline] def roundRoot
    (state : RestoringRootState FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  if FloatLib.Numerics.FixedWord.UInt128.less state.root state.remainder then
    state.root.increment
  else
    state.root

end FloatLib.Numerics.FixedWord.RestoringSquareRoot
