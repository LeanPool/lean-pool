/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext120000130000
import Mathlib.Tactic.FinCases

/-!
# Sext 120000 130000 6

Kernel-checked forced assignments and closed-interval exclusions.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

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

@[expose] public section

-- Generated checkpoints are proposals; all acceptance proofs are checked by the kernel.

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext120000130000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner2Part0 : FanWitness := (.next ([2085000000000], [585000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([495000000000], [195000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([5250000000000], [2670000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2700000000000,
    9000000000000], [2745000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([2010000000000, 9000000000000], [3240000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([1650000000000], [2670000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1155000000000], [2475000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([1620000000000],
    [3825000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([930000000000], [4320000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([1080000000000, 9000000000000], [5835000000000, 0])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([0], [5835000000000]) (some (0, 2, 3)) (some (0, 2,
    3)) (.next ([-390000000000], [4215000000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next
    ([-585000000000], [4905000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1590000000000,
    9000000000000], [7920000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-585000000000],
    [2670000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-195000000000], [690000000000])
    (some (0, 2, 4)) (some (5, 2, 4)) (.next ([-2670000000000], [7920000000000]) (some (5, 2, 4))
    (some (5, 2, 4)) (.next ([-2745000000000, 9000000000000], [5445000000000, 0]) (some (5, 2, 4))
    (some (5, 2, 4)) (.next ([-3240000000000, 9000000000000], [5250000000000, 0]) (some (5, 2, 4))
    (some (5, 2, 4)) (.next ([-2670000000000], [4320000000000]) (some (5, 2, 4)) (some (5, 3, 4))
    (.next ([-2475000000000], [3630000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
    ([-3825000000000], [5445000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4320000000000],
    [5250000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-5835000000000, 0], [6915000000000,
    9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.terminal (some (5, 3, 4)) (some (5, 3, 0))
    (some (5, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner3Part0 : FanWitness := (.next ([5205000000000, 9000000000000], [2715000000000,
    -9000000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next ([1620000000000], [960000000000])
    (some (4, 0, 1)) (some (4, 0, 1)) (.next ([2085000000000], [1710000000000]) (some (4, 0, 1))
    (some (4, 0, 2)) (.next ([3750000000000], [3165000000000]) (some (4, 0, 2)) (some (4, 5, 2))
    (.next ([4125000000000], [3795000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([1620000000000, 9000000000000], [3630000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5,
    2)) (.next ([915000000000], [2670000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([1080000000000, 9000000000000], [5835000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([540000000000], [4710000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0, 9000000000000],
    [2670000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0], [5835000000000])
    (some (4, 5, 2)) (some (4, 5, 3)) (.next ([-45000000000], [5250000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-585000000000], [5295000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-1080000000000], [3750000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2715000000000, 9000000000000], [7920000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-960000000000], [2580000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1710000000000],
    [3795000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3165000000000], [6915000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3795000000000], [7920000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-3630000000000, 9000000000000], [5250000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-2670000000000], [3585000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-5835000000000, 0], [6915000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-4710000000000], [5250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-2670000000000, 9000000000000], [2670000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal
    (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan50Owner3Part0 : FanWitness := (.next ([3750000000000], [3165000000000]) (some (4, 0, 5))
    (some (4, 0, 5)) (.next ([3165000000000], [5010000000000]) (some (4, 0, 5)) (some (4, 0, 5))
    (.next ([1620000000000, 9000000000000], [3630000000000, -9000000000000]) (some (4, 0, 5)) (some
    (4, 5, 5)) (.next ([1905000000000], [4425000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next
    ([1905000000000, 9000000000000], [7095000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5,
    2)) (.next ([1080000000000, 9000000000000], [5835000000000]) (some (4, 5, 2)) (some (4, 5, 2))
    (.next ([540000000000], [4710000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([825000000000], [8175000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([285000000000],
    [3465000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0, 9000000000000], [2670000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0], [5835000000000]) (some (4, 5,
    2)) (some (4, 5, 3)) (.next ([-585000000000], [5295000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-1080000000000], [3750000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-960000000000], [2580000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3165000000000],
    [6915000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5010000000000], [8175000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3630000000000, 9000000000000], [5250000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4425000000000], [6330000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-7095000000000, 9000000000000], [9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-5835000000000, 0], [6915000000000, 9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-4710000000000], [5250000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-8175000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-3465000000000], [3750000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2670000000000,
    9000000000000], [2670000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3))
    (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan50Owner4Part0 : FanWitness := (.next ([4680000000000], [960000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([3795000000000], [1080000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([4875000000000], [2040000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2340000000000],
    [5835000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1275000000000, 9000000000000],
    [3600000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1080000000000],
    [3300000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1080000000000, 9000000000000],
    [5835000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([195000000000], [1080000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1080000000000, 9000000000000], [7095000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([195000000000], [4680000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 9000000000000], [3795000000000, -9000000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [5835000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([-195000000000], [3495000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-960000000000], [5640000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1080000000000],
    [4875000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2040000000000], [6915000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5835000000000], [8175000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-3600000000000, 9000000000000], [4875000000000]) (some (0, 1, 5))
    (some (0, 5, 5)) (.next ([-3300000000000], [4380000000000]) (some (0, 5, 5)) (some (0, 5, 5))
    (.next ([-5835000000000], [6915000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-1080000000000], [1275000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-7095000000000, 9000000000000], [8175000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-4680000000000], [4875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3795000000000,
    9000000000000], [3795000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3))
    (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan51Owner2Part0 : FanWitness := (.next ([4320000000000], [585000000000]) (some (0, 0, 5)) (some
    (0, 1, 5)) (.next ([495000000000], [195000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([2700000000000, 9000000000000], [2745000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 2,
    5)) (.next ([4320000000000], [4710000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([2010000000000, 9000000000000], [3240000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2,
    5)) (.next ([1125000000000, 0], [2115000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2,
    5)) (.next ([1620000000000], [3825000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([1125000000000], [3195000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([930000000000],
    [4320000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([1080000000000, 9000000000000],
    [5835000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([495000000000], [4320000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([0], [5835000000000]) (some (0, 2, 3)) (some (0, 2,
    3)) (.next ([-390000000000], [4215000000000]) (some (0, 2, 3)) (some (0, 5, 4)) (.next
    ([-585000000000], [4905000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-195000000000],
    [690000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2745000000000, 9000000000000],
    [5445000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4710000000000], [9030000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3240000000000, 9000000000000], [5250000000000, 0])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2115000000000, 9000000000000], [3240000000000,
    -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3825000000000], [5445000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3195000000000], [4320000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-4320000000000], [5250000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-5835000000000, 0], [6915000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-4320000000000], [4815000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some
    (0, 5, 4)) (some (0, 5, 0)) (some (0, 5, 4)))))))))))))))))))))))))))

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000], [390000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([4320000000000], [585000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([6330000000000, 9000000000000], [1590000000000, -9000000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) fan48Owner2Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_9 : ExcludedOn (model48.B 9 ++ [step48.q]) 9000000000000 (model48.caps 9)
    (model48.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked48 : StepValid model48 9000000000000 step48 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded48_0
    · exact excluded48_1
    · exact excluded48_2
    · exact (hj rfl).elim
    · exact excluded48_4
    · exact excluded48_5
    · exact excluded48_6
    · exact excluded48_7
    · exact excluded48_8
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded49_0 : ExcludedOn (model49.B 0 ++ [step49.q]) 9000000000000 (model49.caps 0)
    (model49.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_1 : ExcludedOn (model49.B 1 ++ [step49.q]) 9000000000000 (model49.caps 1)
    (model49.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_2 : ExcludedOn (model49.B 2 ++ [step49.q]) 9000000000000 (model49.caps 2)
    (model49.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_3 : ExcludedOn (model49.B 3 ++ [step49.q]) 9000000000000 (model49.caps 3)
    (model49.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5205000000000], [45000000000]) (some (3, 0, 1))
      (some (4, 0, 1)) (.next ([4710000000000], [585000000000]) (some (4, 0, 1)) (some (4, 0, 1))
      (.next ([2670000000000], [1080000000000]) (some (4, 0, 1)) (some (4, 0, 1))
      fan49Owner3Part0)))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_6 : ExcludedOn (model49.B 6 ++ [step49.q]) 9000000000000 (model49.caps 6)
    (model49.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_7 : ExcludedOn (model49.B 7 ++ [step49.q]) 9000000000000 (model49.caps 7)
    (model49.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_8 : ExcludedOn (model49.B 8 ++ [step49.q]) 9000000000000 (model49.caps 8)
    (model49.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_9 : ExcludedOn (model49.B 9 ++ [step49.q]) 9000000000000 (model49.caps 9)
    (model49.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked49 : StepValid model49 9000000000000 step49 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded49_0
    · exact excluded49_1
    · exact excluded49_2
    · exact excluded49_3
    · exact (hj rfl).elim
    · exact excluded49_5
    · exact excluded49_6
    · exact excluded49_7
    · exact excluded49_8
    · exact excluded49_9
theorem next49 : model49.insert step49 = model50 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded50_1 : ExcludedOn (model50.B 1 ++ [step50.q]) 9000000000000 (model50.caps 1)
    (model50.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_2 : ExcludedOn (model50.B 2 ++ [step50.q]) 9000000000000 (model50.caps 2)
    (model50.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_3 : ExcludedOn (model50.B 3 ++ [step50.q]) 9000000000000 (model50.caps 3)
    (model50.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4710000000000], [585000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) (.next ([2670000000000], [1080000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      (.next ([1620000000000], [960000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      fan50Owner3Part0)))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_4 : ExcludedOn (model50.B 4 ++ [step50.q]) 9000000000000 (model50.caps 4)
    (model50.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3300000000000], [195000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan50Owner4Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_5 : ExcludedOn (model50.B 5 ++ [step50.q]) 9000000000000 (model50.caps 5)
    (model50.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8175000000000], [825000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([420000000000], [1080000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([1500000000000], [6570000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1080000000000, 9000000000000], [6990000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1185000000000], [7815000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([255000000000,
      9000000000000], [7920000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next ([0,
      0], [1080000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-825000000000],
      [9000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1080000000000], [1500000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6570000000000], [8070000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-6990000000000, 0], [8070000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-7815000000000], [9000000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-7920000000000, 9000000000000], [8175000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_6 : ExcludedOn (model50.B 6 ++ [step50.q]) 9000000000000 (model50.caps 6)
    (model50.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_7 : ExcludedOn (model50.B 7 ++ [step50.q]) 9000000000000 (model50.caps 7)
    (model50.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_8 : ExcludedOn (model50.B 8 ++ [step50.q]) 9000000000000 (model50.caps 8)
    (model50.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_9 : ExcludedOn (model50.B 9 ++ [step50.q]) 9000000000000 (model50.caps 9)
    (model50.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked50 : StepValid model50 9000000000000 step50 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded50_1
    · exact excluded50_2
    · exact excluded50_3
    · exact excluded50_4
    · exact excluded50_5
    · exact excluded50_6
    · exact excluded50_7
    · exact excluded50_8
    · exact excluded50_9
theorem next50 : model50.insert step50 = model51 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded51_0 : ExcludedOn (model51.B 0 ++ [step51.q]) 9000000000000 (model51.caps 0)
    (model51.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_2 : ExcludedOn (model51.B 2 ++ [step51.q]) 9000000000000 (model51.caps 2)
    (model51.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000], [390000000000]) (some (0, 0, 5))
      (some (0, 0, 5)) fan51Owner2Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded51_3 : ExcludedOn (model51.B 3 ++ [step51.q]) 9000000000000 (model51.caps 3)
    (model51.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_4 : ExcludedOn (model51.B 4 ++ [step51.q]) 9000000000000 (model51.caps 4)
    (model51.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_5 : ExcludedOn (model51.B 5 ++ [step51.q]) 9000000000000 (model51.caps 5)
    (model51.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_6 : ExcludedOn (model51.B 6 ++ [step51.q]) 9000000000000 (model51.caps 6)
    (model51.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_7 : ExcludedOn (model51.B 7 ++ [step51.q]) 9000000000000 (model51.caps 7)
    (model51.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5805000000000], [3240000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([5805000000000], [4320000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([1080000000000, 9000000000000], [3240000000000, -9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0], [4320000000000]) (some (0, 3, 2)) (some (3, 3,
      2)) (.next ([-3240000000000, 9000000000000], [9045000000000, -9000000000000]) (some (3, 3, 2))
      (some (3, 3, 2)) (.next ([-4320000000000], [10125000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-3240000000000, 9000000000000], [4320000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded51_8 : ExcludedOn (model51.B 8 ++ [step51.q]) 9000000000000 (model51.caps 8)
    (model51.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_9 : ExcludedOn (model51.B 9 ++ [step51.q]) 9000000000000 (model51.caps 9)
    (model51.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked51 : StepValid model51 9000000000000 step51 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded51_0
    · exact (hj rfl).elim
    · exact excluded51_2
    · exact excluded51_3
    · exact excluded51_4
    · exact excluded51_5
    · exact excluded51_6
    · exact excluded51_7
    · exact excluded51_8
    · exact excluded51_9
theorem next51 : model51.insert step51 = model52 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded52_1 : ExcludedOn (model52.B 1 ++ [step52.q]) 9000000000000 (model52.caps 1)
    (model52.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4680000000000], [1125000000000]) (some (0, 5,
      2)) (some (0, 5, 3)) (.next ([3600000000000, -9000000000000], [1125000000000, 0]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([5715000000000], [2325000000000]) (some (0, 5, 3)) (some (0, 5,
      3)) (.next ([2700000000000], [1125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([1620000000000, -9000000000000], [1125000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([5715000000000], [4305000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1080000000000,
      9000000000000], [1080000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([1500000000000], [4260000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([1500000000000], [5340000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([420000000000,
      -9000000000000], [6420000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([0], [1980000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1125000000000],
      [5805000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-1125000000000, 0],
      [4725000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2325000000000],
      [8040000000000]) (some (0, 5, 0)) (some (0, 5, 0)) (.next ([-1125000000000], [3825000000000])
      (some (0, 5, 0)) (some (0, 5, 0)) (.next ([-1125000000000, 0], [2745000000000,
      -9000000000000]) (some (0, 5, 0)) none (.next ([-4305000000000], [10020000000000]) none none
      (.next ([-1080000000000, -9000000000000], [2160000000000, 18000000000000]) none none (.next
      ([-4260000000000, 9000000000000], [5760000000000, -9000000000000]) (some (5, 5, 0)) (some (5,
      5, 0)) (.next ([-5340000000000], [6840000000000]) (some (5, 2, 0)) (some (5, 2, 0)) (.next
      ([-6420000000000, -9000000000000], [6840000000000, 0]) (some (5, 2, 0)) (some (5, 2, 0))
      (.terminal (some (5, 2, 0)) (some (5, 2, 0)) (some (5, 2, 0))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_2 : ExcludedOn (model52.B 2 ++ [step52.q]) 9000000000000 (model52.caps 2)
    (model52.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_3 : ExcludedOn (model52.B 3 ++ [step52.q]) 9000000000000 (model52.caps 3)
    (model52.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_4 : ExcludedOn (model52.B 4 ++ [step52.q]) 9000000000000 (model52.caps 4)
    (model52.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_5 : ExcludedOn (model52.B 5 ++ [step52.q]) 9000000000000 (model52.caps 5)
    (model52.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_6 : ExcludedOn (model52.B 6 ++ [step52.q]) 9000000000000 (model52.caps 6)
    (model52.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3240000000000, 9000000000000], [420000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2160000000000], [1500000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1500000000000], [4260000000000, -9000000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1080000000000, 9000000000000], [7920000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-420000000000, 9000000000000],
      [3660000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1500000000000], [3660000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4260000000000, 9000000000000], [5760000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7920000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_7 : ExcludedOn (model52.B 7 ++ [step52.q]) 9000000000000 (model52.caps 7)
    (model52.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_8 : ExcludedOn (model52.B 8 ++ [step52.q]) 9000000000000 (model52.caps 8)
    (model52.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_9 : ExcludedOn (model52.B 9 ++ [step52.q]) 9000000000000 (model52.caps 9)
    (model52.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked52 : StepValid model52 9000000000000 step52 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded52_1
    · exact excluded52_2
    · exact excluded52_3
    · exact excluded52_4
    · exact excluded52_5
    · exact excluded52_6
    · exact excluded52_7
    · exact excluded52_8
    · exact excluded52_9
theorem next52 : model52.insert step52 = model53 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext120000130000
end ConwaySoifer.Simplified.Certificates
