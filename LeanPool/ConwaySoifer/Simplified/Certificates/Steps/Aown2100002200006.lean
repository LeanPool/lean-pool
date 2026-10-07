/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown210000220000
import Mathlib.Tactic.FinCases

/-!
# Aown 210000 220000 6

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
namespace Aown210000220000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part0 : FanWitness := (.next ([-375000000000], [690000000000]) (some (11, 5, 9))
    (some (11, 5, 9)) (.next ([-4500000000000], [8070000000000]) (some (11, 5, 9)) (some (11, 5, 9))
    (.next ([-4125000000000], [7380000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-4410000000000], [7755000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next ([-630000000000],
    [1005000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next ([-4875000000000], [7755000000000])
    (some (11, 5, 9)) (some (11, 5, 9)) (.next ([-4785000000000], [7380000000000]) (some (11, 5, 9))
    (some (11, 5, 9)) (.next ([-5130000000000], [7755000000000]) (some (11, 5, 9)) (some (11, 5, 9))
    (.next ([-630000000000], [945000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-4785000000000], [7125000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-5505000000000], [7380000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-5505000000000], [7125000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-5670000000000], [7320000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-2700000000000], [3450000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-5040000000000], [6375000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-5295000000000], [6630000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-3420000000000], [4170000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-1380000000000], [1635000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-6045000000000], [7005000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-6300000000000], [7005000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-2700000000000], [2880000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-3420000000000], [3600000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-6375000000000], [6675000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-6630000000000], [6675000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.terminal (some (11, 5,
    9)) (some (11, 5, 9)) (some (11, 5, 9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part1 : FanWitness := (.next ([-705000000000], [7005000000000]) (some (11, 4, 8))
    (some (11, 4, 8)) (.next ([-570000000000], [5340000000000]) (some (11, 4, 8)) (some (11, 4, 8))
    (.next ([-900000000000], [7890000000000]) (some (11, 4, 8)) (some (11, 4, 8)) (.next
    ([-960000000000], [7005000000000]) (some (11, 4, 8)) (some (11, 4, 8)) (.next ([-255000000000],
    [1635000000000]) (some (11, 4, 8)) (some (11, 4, 8)) (.next ([-1275000000000], [7575000000000])
    (some (11, 4, 8)) (some (11, 4, 8)) (.next ([-1335000000000], [6630000000000]) (some (11, 4, 8))
    (some (11, 4, 8)) (.next ([-1530000000000], [7575000000000]) (some (11, 4, 8)) (some (11, 4, 8))
    (.next ([-1335000000000], [6375000000000]) (some (11, 4, 8)) (some (11, 4, 8)) (.next
    ([-1905000000000], [7200000000000]) (some (11, 4, 8)) (some (11, 5, 8)) (.next
    ([-1905000000000], [6945000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next ([-750000000000],
    [2640000000000]) (some (11, 5, 8)) (some (11, 5, 8)) (.next ([-315000000000], [945000000000])
    (some (11, 5, 8)) (some (11, 5, 8)) (.next ([-375000000000], [1005000000000]) (some (11, 5, 8))
    (some (11, 5, 8)) (.next ([-750000000000], [1920000000000]) (some (11, 5, 8)) (some (11, 5, 8))
    (.next ([-690000000000], [1695000000000]) (some (11, 5, 8)) (some (11, 5, 9)) (.next
    ([-3150000000000], [7125000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next ([-315000000000],
    [690000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next ([-3405000000000], [7380000000000])
    (some (11, 5, 9)) (some (11, 5, 9)) (.next ([-3780000000000], [8070000000000]) (some (11, 5, 9))
    (some (11, 5, 9)) (.next ([-945000000000], [1950000000000]) (some (11, 5, 9)) (some (11, 5, 9))
    (.next ([-375000000000], [750000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-4155000000000], [7755000000000]) (some (11, 5, 9)) (some (11, 5, 9)) (.next
    ([-3870000000000], [7125000000000]) (some (11, 5, 9)) (some (11, 5, 9))
    fan48Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part2 : FanWitness := (.next ([2595000000000], [4785000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([2625000000000], [5130000000000]) (some (9, 3, 6)) (some (9, 3, 6))
    (.next ([315000000000], [630000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([2340000000000], [4785000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([1875000000000],
    [5505000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([1620000000000], [5505000000000])
    (some (9, 3, 6)) (some (9, 3, 6)) (.next ([1650000000000], [5670000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([750000000000], [2700000000000]) (some (9, 3, 6)) (some (11, 3, 6))
    (.next ([1335000000000], [5040000000000]) (some (11, 3, 6)) (some (11, 3, 6)) (.next
    ([1335000000000], [5295000000000]) (some (11, 3, 6)) (some (11, 3, 6)) (.next ([750000000000],
    [3420000000000]) (some (11, 3, 6)) (some (11, 3, 6)) (.next ([255000000000], [1380000000000])
    (some (11, 3, 6)) (some (11, 3, 6)) (.next ([960000000000], [6045000000000]) (some (11, 3, 6))
    (some (11, 3, 6)) (.next ([705000000000], [6300000000000]) (some (11, 3, 6)) (some (11, 3, 6))
    (.next ([180000000000], [2700000000000]) (some (11, 3, 6)) (some (11, 3, 6)) (.next
    ([180000000000], [3420000000000]) (some (11, 3, 6)) (some (11, 3, 7)) (.next ([300000000000],
    [6375000000000]) (some (11, 3, 7)) (some (11, 3, 7)) (.next ([45000000000], [6630000000000])
    (some (11, 3, 7)) (some (11, 3, 7)) (.next ([0], [1380000000000]) (some (11, 3, 7)) (some (11,
    3, 7)) (.next ([-45000000000], [6675000000000]) (some (11, 3, 7)) (some (11, 4, 8)) (.next
    ([-270000000000], [6945000000000]) (some (11, 4, 8)) (some (11, 4, 8)) (.next ([-300000000000],
    [6675000000000]) (some (11, 4, 8)) (some (11, 4, 8)) (.next ([-330000000000], [7320000000000])
    (some (11, 4, 8)) (some (11, 4, 8)) (.next ([-525000000000], [7200000000000]) (some (11, 4, 8))
    (some (11, 4, 8)) fan48Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part3 : FanWitness := (.next ([5295000000000], [1335000000000]) (some (9, 11, 6))
    (some (9, 11, 6)) (.next ([6045000000000], [1530000000000]) (some (9, 11, 6)) (some (9, 11, 6))
    (.next ([5040000000000], [1335000000000]) (some (9, 11, 6)) (some (9, 11, 6)) (.next
    ([5295000000000], [1905000000000]) (some (9, 11, 6)) (some (9, 11, 6)) (.next ([5040000000000],
    [1905000000000]) (some (9, 11, 6)) (some (9, 11, 6)) (.next ([1890000000000], [750000000000])
    (some (9, 11, 6)) (some (9, 11, 6)) (.next ([630000000000], [315000000000]) (some (9, 11, 6))
    (some (9, 11, 6)) (.next ([630000000000], [375000000000]) (some (9, 2, 6)) (some (9, 2, 6))
    (.next ([1170000000000], [750000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next
    ([1005000000000], [690000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next ([3975000000000],
    [3150000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next ([375000000000], [315000000000]) (some
    (9, 2, 6)) (some (9, 2, 6)) (.next ([3975000000000], [3405000000000]) (some (9, 2, 6)) (some (9,
    2, 6)) (.next ([4290000000000], [3780000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next
    ([1005000000000], [945000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next ([375000000000],
    [375000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next ([3600000000000], [4155000000000])
    (some (9, 2, 6)) (some (9, 3, 6)) (.next ([3255000000000], [3870000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([315000000000], [375000000000]) (some (9, 3, 6)) (some (9, 3, 6))
    (.next ([3570000000000], [4500000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([3255000000000], [4125000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([3345000000000],
    [4410000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([375000000000], [630000000000]) (some
    (9, 3, 6)) (some (9, 3, 6)) (.next ([2880000000000], [4875000000000]) (some (9, 3, 6)) (some (9,
    3, 6)) fan48Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner5Part0 : FanWitness := (.next ([3780000000000], [750000000000]) (some (5, 1, 3)) (some
    (5, 1, 3)) (.next ([1890000000000, -9000000000000], [750000000000]) (some (5, 1, 3)) (some (5,
    1, 3)) (.next ([3198000000000], [1527000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([5790000000000, -9000000000000], [3210000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([2955000000000], [1920000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([2598000000000, 0], [1890000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([3150000000000], [5100000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1848000000000],
    [4530000000000]) (some (5, 1, 3)) (some (5, 1, 5)) (.next ([1278000000000], [6402000000000])
    (some (5, 1, 5)) (some (5, 1, 5)) (.next ([600000000000], [4125000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([195000000000], [3180000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([0], [2598000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1320000000000],
    [9000000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-750000000000], [4530000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-750000000000, 0], [2640000000000, -9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1527000000000], [4725000000000]) (some (0, 2, 5))
    (some (0, 3, 5)) (.next ([-3210000000000, -9000000000000], [9000000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-1920000000000], [4875000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-1890000000000, -9000000000000], [4488000000000, 9000000000000]) (some (0, 3, 5)) (some
    (0, 3, 5)) (.next ([-5100000000000], [8250000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-4530000000000], [6378000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-6402000000000],
    [7680000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-4125000000000], [4725000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3180000000000], [3375000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.terminal (some (0, 3, 5)) (some (0, 3, 5)) (some (0, 3,
    5)))))))))))))))))))))))))))

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6630000000000], [45000000000]) (some (9, 11, 5))
      (some (9, 11, 6)) (.next ([6675000000000], [270000000000]) (some (9, 11, 6)) (some (9, 11, 6))
      (.next ([6375000000000], [300000000000]) (some (9, 11, 6)) (some (9, 11, 6)) (.next
      ([6990000000000], [330000000000]) (some (9, 11, 6)) (some (9, 11, 6)) (.next ([6675000000000],
      [525000000000]) (some (9, 11, 6)) (some (9, 11, 6)) (.next ([6300000000000], [705000000000])
      (some (9, 11, 6)) (some (9, 11, 6)) (.next ([4770000000000], [570000000000]) (some (9, 11, 6))
      (some (9, 11, 6)) (.next ([6990000000000], [900000000000]) (some (9, 11, 6)) (some (9, 11, 6))
      (.next ([6045000000000], [960000000000]) (some (9, 11, 6)) (some (9, 11, 6)) (.next
      ([1380000000000], [255000000000]) (some (9, 11, 6)) (some (9, 11, 6)) (.next ([6300000000000],
      [1275000000000]) (some (9, 11, 6)) (some (9, 11, 6)) fan48Owner0Part3))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_3 : ExcludedOn (model48.B 3 ++ [step48.q]) 9000000000000 (model48.caps 3)
    (model48.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7110000000000, -9000000000000], [570000000000,
      9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([3000000000000], [330000000000])
      (some (3, 0, 4)) (some (3, 4, 4)) (.next ([7185000000000], [1815000000000]) (some (3, 4, 4))
      (some (3, 4, 4)) (.next ([5865000000000], [1890000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([2535000000000], [3000000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([1110000000000, -9000000000000], [2220000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([1650000000000], [4350000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([1320000000000], [7680000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [1890000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-570000000000,
      -9000000000000], [7680000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-330000000000],
      [3330000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1815000000000], [9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1890000000000, -9000000000000], [7755000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3000000000000], [5535000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2220000000000, -9000000000000], [3330000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4350000000000], [6000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-7680000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7680000000000], [1320000000000]) (some (5, 0,
      3)) (some (5, 1, 3)) fan48Owner5Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_9 : ExcludedOn (model48.B 9 ++ [step48.q]) 9000000000000 (model48.caps 9)
    (model48.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded48_5
    · exact excluded48_6
    · exact excluded48_7
    · exact excluded48_8
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown210000220000
end ConwaySoifer.Simplified.Certificates
