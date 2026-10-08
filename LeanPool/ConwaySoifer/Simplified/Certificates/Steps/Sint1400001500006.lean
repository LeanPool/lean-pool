/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint140000150000
import Mathlib.Tactic.FinCases

/-!
# Sint 140000 150000 6

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
namespace Sint140000150000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan50Owner6Part0 : FanWitness := (.next ([840000000000], [4500000000000]) (some (0, 6, 4)) (some
    (0, 6, 4)) (.next ([750000000000], [4290000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([330000000000], [3210000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([585000000000],
    [7665000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([255000000000], [4455000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (0, 6,
    4)) (some (0, 6, 4)) (.next ([-45000000000], [4545000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-420000000000, -9000000000000], [5760000000000, 9000000000000]) (some (0, 6, 4)) (some
    (6, 6, 4)) (.next ([-510000000000, -9000000000000], [5550000000000, 9000000000000]) (some (6, 6,
    4)) (some (6, 6, 4)) (.next ([-750000000000], [4710000000000]) (some (6, 6, 4)) (some (6, 6, 4))
    (.next ([-3705000000000], [9000000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
    ([-2010000000000, -9000000000000], [4710000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-3705000000000, 0], [7740000000000, -9000000000000]) (some (6, 3, 4)) (some (6, 3, 5)) (.next
    ([-4965000000000, -9000000000000], [10260000000000, 9000000000000]) (some (6, 3, 5)) (some (6,
    3, 5)) (.next ([-1260000000000, -9000000000000], [2520000000000, 18000000000000]) (some (6, 3,
    5)) (some (6, 3, 5)) (.next ([-210000000000], [300000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-3240000000000, 9000000000000], [4080000000000, -9000000000000]) (some (6, 3, 5)) (some
    (6, 3, 5)) (.next ([-3030000000000, 9000000000000], [3780000000000, -9000000000000]) (some (6,
    3, 5)) (some (6, 3, 5)) (.next ([-3120000000000], [3750000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-4500000000000], [5340000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-4290000000000], [5040000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-3210000000000],
    [3540000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-7665000000000], [8250000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-4455000000000], [4710000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.terminal (some (6, 3, 5)) (some (6, 3, 5)) (some (6, 3,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan51Owner6Part0 : FanWitness := (.next ([750000000000, 0], [3030000000000, -9000000000000])
    (some (5, 6, 4)) (some (5, 6, 4)) (.next ([630000000000], [3120000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([840000000000], [4500000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([915000000000], [5040000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([750000000000], [4290000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([705000000000],
    [5340000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([330000000000], [3210000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (0, 6,
    4)) (some (0, 6, 4)) (.next ([-420000000000, -9000000000000], [5760000000000, 9000000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-510000000000, -9000000000000], [5550000000000,
    9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-750000000000], [4710000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1260000000000, -9000000000000], [5205000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2010000000000, -9000000000000], [4710000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1260000000000, -9000000000000], [2520000000000,
    18000000000000]) (some (0, 6, 4)) (some (0, 6, 5)) (.next ([-4710000000000], [9165000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-210000000000], [300000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-3240000000000, 9000000000000], [4080000000000, -9000000000000]) (some
    (0, 6, 5)) (some (0, 6, 5)) (.next ([-3030000000000, 9000000000000], [3780000000000,
    -9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3120000000000], [3750000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4500000000000], [5340000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-5040000000000], [5955000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-4290000000000], [5040000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-5340000000000], [6045000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3210000000000],
    [3540000000000]) (some (0, 6, 5)) (some (6, 6, 5)) (.terminal (some (6, 6, 5)) (some (6, 3, 5))
    (some (6, 6, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan55Owner4Part0 : FanWitness := (.next ([5850000000000], [375000000000]) (some (4, 1, 3)) (some
    (4, 1, 3)) (.next ([5160000000000], [690000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([5535000000000, 0], [1260000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([4590000000000, -9000000000000], [1635000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1,
    3)) (.next ([2790000000000], [2250000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([1965000000000], [1635000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([2910000000000],
    [3885000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1530000000000, -9000000000000],
    [2250000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1260000000000], [2625000000000])
    (some (4, 1, 3)) (some (4, 5, 3)) (.next ([375000000000], [1155000000000]) (some (4, 5, 3))
    (some (4, 5, 3)) (.next ([810000000000], [3165000000000]) (some (4, 5, 3)) (some (4, 5, 3))
    (.next ([0, 0], [1260000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0,
    -9000000000000], [2625000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-375000000000],
    [6225000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-690000000000], [5850000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1260000000000, -9000000000000], [6795000000000,
    9000000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-1635000000000, -9000000000000],
    [6225000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2250000000000], [5040000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1635000000000], [3600000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-3885000000000], [6795000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-2250000000000, 0], [3780000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-2625000000000], [3885000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-1155000000000], [1530000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3165000000000],
    [3975000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 3, 4)) (some (0, 3, 4))
    (some (0, 3, 4)))))))))))))))))))))))))))

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_3 : ExcludedOn (model48.B 3 ++ [step48.q]) 9000000000000 (model48.caps 3)
    (model48.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [510000000000, 9000000000000])
      (some (5, 0, 2)) (some (5, 0, 3)) (.next ([3960000000000], [750000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([5250000000000, 0], [2700000000000, -9000000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([5250000000000], [3960000000000]) (some (5, 0, 3)) (some (5, 0, 3))
      (.next ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) (some (5, 0, 3)) (some
      (5, 0, 3)) (.next ([3990000000000, -9000000000000], [5220000000000, 9000000000000]) (some (5,
      0, 3)) (some (5, 0, 3)) (.next ([1290000000000], [3210000000000]) (some (5, 0, 3)) (some (5,
      0, 3)) (.next ([750000000000, 0], [3030000000000, -9000000000000]) (some (5, 0, 3)) (some (5,
      0, 3)) (.next ([750000000000], [4290000000000]) (some (5, 0, 3)) (some (5, 1, 3)) (.next
      ([330000000000], [3210000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([330000000000],
      [4170000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-510000000000, -9000000000000],
      [5550000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 2, 3)) (.next ([-750000000000],
      [4710000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2700000000000, 9000000000000],
      [7950000000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-3960000000000],
      [9210000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1260000000000, -9000000000000],
      [2520000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 4)) (.next ([-5220000000000,
      -9000000000000], [9210000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-3210000000000],
      [4500000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-3030000000000, 9000000000000],
      [3780000000000, -9000000000000]) (some (5, 2, 4)) (some (5, 2, 5)) (.next ([-4290000000000],
      [5040000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-3210000000000], [3540000000000])
      (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-4170000000000], [4500000000000]) (some (5, 2, 5))
      (some (5, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
      5))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_9 : ExcludedOn (model48.B 9 ++ [step48.q]) 9000000000000 (model48.caps 9)
    (model48.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded48_3
    · exact excluded48_4
    · exact (hj rfl).elim
    · exact excluded48_6
    · exact excluded48_7
    · exact excluded48_8
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded49_0 : ExcludedOn (model49.B 0 ++ [step49.q]) 9000000000000 (model49.caps 0)
    (model49.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_1 : ExcludedOn (model49.B 1 ++ [step49.q]) 9000000000000 (model49.caps 1)
    (model49.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_2 : ExcludedOn (model49.B 2 ++ [step49.q]) 9000000000000 (model49.caps 2)
    (model49.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_3 : ExcludedOn (model49.B 3 ++ [step49.q]) 9000000000000 (model49.caps 3)
    (model49.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_4 : ExcludedOn (model49.B 4 ++ [step49.q]) 9000000000000 (model49.caps 4)
    (model49.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5040000000000], [210000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([3660000000000], [840000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([2400000000000, -9000000000000], [840000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([3780000000000, -9000000000000], [1470000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([4665000000000], [4500000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([540000000000], [3870000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([255000000000], [5040000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5505000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-210000000000], [5250000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-840000000000], [4500000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([-840000000000, 0], [3240000000000, -9000000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([-1470000000000, -9000000000000], [5250000000000]) (some (0, 2, 3))
      (some (0, 4, 3)) (.next ([-4500000000000], [9165000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-3870000000000], [4410000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-5040000000000], [5295000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      0)) (some (0, 4, 0)) (some (0, 4, 0))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_7 : ExcludedOn (model49.B 7 ++ [step49.q]) 9000000000000 (model49.caps 7)
    (model49.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_8 : ExcludedOn (model49.B 8 ++ [step49.q]) 9000000000000 (model49.caps 8)
    (model49.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_9 : ExcludedOn (model49.B 9 ++ [step49.q]) 9000000000000 (model49.caps 9)
    (model49.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [255000000000]) (some (3, 0, 1))
      (some (3, 1, 2)) (.next ([3195000000000], [1890000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([4500000000000], [5340000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([2610000000000], [5340000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [5085000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-255000000000], [4755000000000])
      (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-1890000000000], [5085000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-5340000000000], [9840000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-5340000000000], [7950000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some
      (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded49_4
    · exact excluded49_5
    · exact (hj rfl).elim
    · exact excluded49_7
    · exact excluded49_8
    · exact excluded49_9
theorem next49 : model49.insert step49 = model50 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded50_0 : ExcludedOn (model50.B 0 ++ [step50.q]) 9000000000000 (model50.caps 0)
    (model50.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_1 : ExcludedOn (model50.B 1 ++ [step50.q]) 9000000000000 (model50.caps 1)
    (model50.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_2 : ExcludedOn (model50.B 2 ++ [step50.q]) 9000000000000 (model50.caps 2)
    (model50.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_3 : ExcludedOn (model50.B 3 ++ [step50.q]) 9000000000000 (model50.caps 3)
    (model50.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_4 : ExcludedOn (model50.B 4 ++ [step50.q]) 9000000000000 (model50.caps 4)
    (model50.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_5 : ExcludedOn (model50.B 5 ++ [step50.q]) 9000000000000 (model50.caps 5)
    (model50.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_6 : ExcludedOn (model50.B 6 ++ [step50.q]) 9000000000000 (model50.caps 6)
    (model50.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [45000000000]) (some (5, 6, 3))
      (some (5, 6, 4)) (.next ([5340000000000], [420000000000, 9000000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([5040000000000], [510000000000, 9000000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([3960000000000], [750000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      (.next ([5295000000000], [3705000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([2700000000000, -9000000000000], [2010000000000, 9000000000000]) (some (5, 6, 4)) (some (5,
      6, 4)) (.next ([4035000000000, -9000000000000], [3705000000000]) (some (5, 6, 4)) (some (5, 6,
      4)) (.next ([5295000000000], [4965000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      (.next ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) (some (5, 6, 4)) (some
      (5, 6, 4)) (.next ([90000000000], [210000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([840000000000, 0], [3240000000000, -9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([750000000000, 0], [3030000000000, -9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([630000000000], [3120000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      fan50Owner6Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_7 : ExcludedOn (model50.B 7 ++ [step50.q]) 9000000000000 (model50.caps 7)
    (model50.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_8 : ExcludedOn (model50.B 8 ++ [step50.q]) 9000000000000 (model50.caps 8)
    (model50.ord 8) 0 1 100 := by
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
    · exact excluded50_0
    · exact excluded50_1
    · exact excluded50_2
    · exact excluded50_3
    · exact excluded50_4
    · exact excluded50_5
    · exact excluded50_6
    · exact excluded50_7
    · exact excluded50_8
    · exact (hj rfl).elim
theorem next50 : model50.insert step50 = model51 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded51_0 : ExcludedOn (model51.B 0 ++ [step51.q]) 9000000000000 (model51.caps 0)
    (model51.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_1 : ExcludedOn (model51.B 1 ++ [step51.q]) 9000000000000 (model51.caps 1)
    (model51.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_2 : ExcludedOn (model51.B 2 ++ [step51.q]) 9000000000000 (model51.caps 2)
    (model51.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5340000000000], [420000000000, 9000000000000])
      (some (5, 6, 3)) (some (5, 6, 4)) (.next ([5040000000000], [510000000000, 9000000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) (.next ([3960000000000], [750000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([3945000000000, -9000000000000], [1260000000000, 9000000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) (.next ([2700000000000, -9000000000000], [2010000000000,
      9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1260000000000, 9000000000000],
      [1260000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([4455000000000],
      [4710000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([90000000000], [210000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) (.next ([840000000000, 0], [3240000000000, -9000000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) fan51Owner6Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded51_7 : ExcludedOn (model51.B 7 ++ [step51.q]) 9000000000000 (model51.caps 7)
    (model51.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_8 : ExcludedOn (model51.B 8 ++ [step51.q]) 9000000000000 (model51.caps 8)
    (model51.ord 8) 0 1 100 := by
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
    · exact excluded51_1
    · exact excluded51_2
    · exact excluded51_3
    · exact excluded51_4
    · exact excluded51_5
    · exact excluded51_6
    · exact excluded51_7
    · exact excluded51_8
    · exact (hj rfl).elim
theorem next51 : model51.insert step51 = model52 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded52_0 : ExcludedOn (model52.B 0 ++ [step52.q]) 9000000000000 (model52.caps 0)
    (model52.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_1 : ExcludedOn (model52.B 1 ++ [step52.q]) 9000000000000 (model52.caps 1)
    (model52.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_2 : ExcludedOn (model52.B 2 ++ [step52.q]) 9000000000000 (model52.caps 2)
    (model52.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_3 : ExcludedOn (model52.B 3 ++ [step52.q]) 9000000000000 (model52.caps 3)
    (model52.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_4 : ExcludedOn (model52.B 4 ++ [step52.q]) 9000000000000 (model52.caps 4)
    (model52.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 3)) (some (4, 1, 3)) (.next ([5850000000000], [375000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([5130000000000], [720000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([5505000000000, 0], [1260000000000, 9000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([4590000000000, -9000000000000], [1635000000000, 9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1965000000000], [1635000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([2880000000000], [2625000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([2880000000000], [3885000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1260000000000], [2625000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1620000000000],
      [3885000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1245000000000], [6225000000000])
      (some (4, 1, 3)) (some (5, 1, 3)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([0, -9000000000000], [2625000000000, 0]) (some (5, 1, 3)) (some
      (5, 1, 3)) (.next ([-375000000000], [6225000000000]) (some (5, 1, 3)) (some (5, 2, 3)) (.next
      ([-720000000000], [5850000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1260000000000,
      -9000000000000], [6765000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2, 4)) (.next
      ([-1635000000000, -9000000000000], [6225000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4))
      (.next ([-1635000000000], [3600000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-2625000000000], [5505000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next
      ([-3885000000000], [6765000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-2625000000000], [3885000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-3885000000000], [5505000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-6225000000000], [7470000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.terminal (some (5, 3,
      4)) (some (0, 3, 4)) (some (5, 3, 4))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_5 : ExcludedOn (model52.B 5 ++ [step52.q]) 9000000000000 (model52.caps 5)
    (model52.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_6 : ExcludedOn (model52.B 6 ++ [step52.q]) 9000000000000 (model52.caps 6)
    (model52.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_7 : ExcludedOn (model52.B 7 ++ [step52.q]) 9000000000000 (model52.caps 7)
    (model52.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded52_0
    · exact excluded52_1
    · exact excluded52_2
    · exact excluded52_3
    · exact excluded52_4
    · exact excluded52_5
    · exact excluded52_6
    · exact excluded52_7
    · exact (hj rfl).elim
    · exact excluded52_9
theorem next52 : model52.insert step52 = model53 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded53_0 : ExcludedOn (model53.B 0 ++ [step53.q]) 9000000000000 (model53.caps 0)
    (model53.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_1 : ExcludedOn (model53.B 1 ++ [step53.q]) 9000000000000 (model53.caps 1)
    (model53.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_2 : ExcludedOn (model53.B 2 ++ [step53.q]) 9000000000000 (model53.caps 2)
    (model53.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_3 : ExcludedOn (model53.B 3 ++ [step53.q]) 9000000000000 (model53.caps 3)
    (model53.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [630000000000, 9000000000000])
      (some (3, 5, 3)) (some (4, 5, 3)) (.next ([5250000000000], [1005000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([6357000000000], [1635000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([1260000000000], [375000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([5625000000000], [2835000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([6732000000000],
      [3465000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1107000000000], [630000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([375000000000], [1830000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([630000000000], [4995000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([0], [1260000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([-630000000000, -9000000000000], [6255000000000, 9000000000000]) (some (0, 5, 3)) (some (5,
      5, 3)) (.next ([-1005000000000], [6255000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-1635000000000], [7992000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-375000000000],
      [1635000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-2835000000000], [8460000000000])
      (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-3465000000000], [10197000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([-630000000000], [1737000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([-1830000000000], [2205000000000]) (some (5, 2, 3)) (some (5, 3, 3)) (.next
      ([-4995000000000], [5625000000000]) (some (5, 3, 3)) (some (5, 3, 3)) (.terminal (some (5, 3,
      3)) (some (5, 3, 3)) (some (5, 3, 3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded53_5 : ExcludedOn (model53.B 5 ++ [step53.q]) 9000000000000 (model53.caps 5)
    (model53.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_6 : ExcludedOn (model53.B 6 ++ [step53.q]) 9000000000000 (model53.caps 6)
    (model53.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_7 : ExcludedOn (model53.B 7 ++ [step53.q]) 9000000000000 (model53.caps 7)
    (model53.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_8 : ExcludedOn (model53.B 8 ++ [step53.q]) 9000000000000 (model53.caps 8)
    (model53.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6732000000000], [648000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([3465000000000], [5535000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([1197000000000], [2268000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1620000000000], [3915000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [7380000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-648000000000], [7380000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5535000000000], [9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-2268000000000], [3465000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-3915000000000], [5535000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some
      (0, 1, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded53_9 : ExcludedOn (model53.B 9 ++ [step53.q]) 9000000000000 (model53.caps 9)
    (model53.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked53 : StepValid model53 9000000000000 step53 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded53_0
    · exact excluded53_1
    · exact excluded53_2
    · exact excluded53_3
    · exact (hj rfl).elim
    · exact excluded53_5
    · exact excluded53_6
    · exact excluded53_7
    · exact excluded53_8
    · exact excluded53_9
theorem next53 : model53.insert step53 = model54 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded54_0 : ExcludedOn (model54.B 0 ++ [step54.q]) 9000000000000 (model54.caps 0)
    (model54.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_1 : ExcludedOn (model54.B 1 ++ [step54.q]) 9000000000000 (model54.caps 1)
    (model54.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_2 : ExcludedOn (model54.B 2 ++ [step54.q]) 9000000000000 (model54.caps 2)
    (model54.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_3 : ExcludedOn (model54.B 3 ++ [step54.q]) 9000000000000 (model54.caps 3)
    (model54.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_4 : ExcludedOn (model54.B 4 ++ [step54.q]) 9000000000000 (model54.caps 4)
    (model54.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 3)) (some (4, 5, 3)) (.next ([5850000000000], [375000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5160000000000], [690000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([5535000000000, 0], [1260000000000, 9000000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([4590000000000, -9000000000000], [1635000000000, 9000000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([5535000000000], [3000000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([1965000000000], [1635000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([2850000000000], [3375000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([2910000000000], [3885000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([885000000000],
      [1740000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1260000000000], [2625000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (4, 5,
      3)) (some (4, 5, 3)) (.next ([0, -9000000000000], [2625000000000, 0]) (some (0, 5, 3)) (some
      (0, 5, 3)) (.next ([-375000000000], [6225000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-690000000000], [5850000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1260000000000,
      -9000000000000], [6795000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next
      ([-1635000000000, -9000000000000], [6225000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-3000000000000], [8535000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-1635000000000], [3600000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3375000000000], [6225000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3885000000000], [6795000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
      ([-1740000000000], [2625000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
      ([-2625000000000], [3885000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.terminal (some (0, 3,
      4)) (some (0, 3, 4)) (some (0, 3, 4))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded54_6 : ExcludedOn (model54.B 6 ++ [step54.q]) 9000000000000 (model54.caps 6)
    (model54.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_7 : ExcludedOn (model54.B 7 ++ [step54.q]) 9000000000000 (model54.caps 7)
    (model54.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_8 : ExcludedOn (model54.B 8 ++ [step54.q]) 9000000000000 (model54.caps 8)
    (model54.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_9 : ExcludedOn (model54.B 9 ++ [step54.q]) 9000000000000 (model54.caps 9)
    (model54.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked54 : StepValid model54 9000000000000 step54 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded54_0
    · exact excluded54_1
    · exact excluded54_2
    · exact excluded54_3
    · exact excluded54_4
    · exact (hj rfl).elim
    · exact excluded54_6
    · exact excluded54_7
    · exact excluded54_8
    · exact excluded54_9
theorem next54 : model54.insert step54 = model55 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded55_0 : ExcludedOn (model55.B 0 ++ [step55.q]) 9000000000000 (model55.caps 0)
    (model55.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_1 : ExcludedOn (model55.B 1 ++ [step55.q]) 9000000000000 (model55.caps 1)
    (model55.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_2 : ExcludedOn (model55.B 2 ++ [step55.q]) 9000000000000 (model55.caps 2)
    (model55.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_3 : ExcludedOn (model55.B 3 ++ [step55.q]) 9000000000000 (model55.caps 3)
    (model55.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_4 : ExcludedOn (model55.B 4 ++ [step55.q]) 9000000000000 (model55.caps 4)
    (model55.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 3)) (some (4, 1, 3)) fan55Owner4Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded55_6 : ExcludedOn (model55.B 6 ++ [step55.q]) 9000000000000 (model55.caps 6)
    (model55.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_7 : ExcludedOn (model55.B 7 ++ [step55.q]) 9000000000000 (model55.caps 7)
    (model55.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_8 : ExcludedOn (model55.B 8 ++ [step55.q]) 9000000000000 (model55.caps 8)
    (model55.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_9 : ExcludedOn (model55.B 9 ++ [step55.q]) 9000000000000 (model55.caps 9)
    (model55.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked55 : StepValid model55 9000000000000 step55 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded55_0
    · exact excluded55_1
    · exact excluded55_2
    · exact excluded55_3
    · exact excluded55_4
    · exact (hj rfl).elim
    · exact excluded55_6
    · exact excluded55_7
    · exact excluded55_8
    · exact excluded55_9
theorem next55 : model55.insert step55 = model56 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint140000150000
end ConwaySoifer.Simplified.Certificates
