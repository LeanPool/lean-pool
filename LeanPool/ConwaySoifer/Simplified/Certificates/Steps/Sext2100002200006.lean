/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext210000220000
import Mathlib.Tactic.FinCases

/-!
# Sext 210000 220000 6

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
namespace Sext210000220000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part0 : FanWitness := (.next ([-2673000000000], [8253000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([-3945000000000], [9780000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([-1005000000000], [2403000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next
    ([-4260000000000], [9360000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-3150000000000],
    [6900000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-1005000000000], [2148000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-3780000000000], [7773000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([-2775000000000], [5625000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([-375000000000], [750000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next
    ([-2775000000000], [5370000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-2955000000000],
    [5505000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-420000000000], [735000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-1710000000000], [2835000000000]) (some (0, 2, 8))
    (some (0, 3, 8)) (.next ([-630000000000], [1005000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    (.next ([-3705000000000], [5880000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([-3150000000000], [4995000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-3960000000000],
    [5880000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-630000000000], [873000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-2445000000000], [3150000000000]) (some (0, 3, 8))
    (some (0, 3, 8)) (.next ([-5790000000000], [6630000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    (.next ([-4860000000000], [5505000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([-6540000000000], [7005000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-6795000000000],
    [7005000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-6105000000000], [6210000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.terminal (some (0, 3, 8)) (some (0, 3, 8)) (some (0, 3,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner0Part1 : FanWitness := (.next ([315000000000], [420000000000]) (some (7, 1, 8)) (some
    (7, 1, 8)) (.next ([1125000000000], [1710000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next
    ([375000000000], [630000000000]) (some (7, 1, 8)) (some (7, 2, 8)) (.next ([2175000000000],
    [3705000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([1845000000000], [3150000000000])
    (some (7, 2, 8)) (some (7, 2, 8)) (.next ([1920000000000], [3960000000000]) (some (7, 2, 8))
    (some (7, 2, 8)) (.next ([243000000000], [630000000000]) (some (7, 2, 8)) (some (7, 2, 8))
    (.next ([705000000000], [2445000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next
    ([840000000000], [5790000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([645000000000],
    [4860000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([465000000000], [6540000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([210000000000], [6795000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([105000000000], [6105000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([0], [1905000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-270000000000],
    [6855000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-228000000000], [5103000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-525000000000], [7110000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([-1110000000000], [8655000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([-1065000000000], [7695000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next
    ([-1800000000000], [8010000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-630000000000],
    [2778000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-1938000000000], [7938000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-375000000000], [1530000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([-375000000000], [1275000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    fan48Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner2Part0 : FanWitness := (.next ([5220000000000], [3030000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([3000000000000], [2220000000000]) (some (0, 2, 3)) (some (0, 2, 3))
    (.next ([3780000000000, 9000000000000], [2985000000000, -9000000000000]) (some (0, 2, 3)) (some
    (0, 2, 3)) (.next ([3001500000000], [3780000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([1890000000000], [4875000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([1440000000000],
    [3781500000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([1890000000000, 9000000000000],
    [6030000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([751500000000], [3028500000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([735000000000], [4140000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([345000000000], [3765000000000]) (some (0, 2, 3)) (some (0, 2, 3))
    (.next ([0], [6030000000000]) (some (0, 2, 3)) (some (0, 5, 3)) (.next ([-16500000000],
    [1111500000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-330000000000, 9000000000000],
    [3330000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1890000000000,
    9000000000000], [6781500000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3030000000000],
    [8250000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2220000000000], [5220000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2985000000000, 9000000000000], [6765000000000, 0])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3780000000000], [6781500000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-4875000000000], [6765000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-3781500000000], [5221500000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-6030000000000, 0], [7920000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-3028500000000], [3780000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4140000000000],
    [4875000000000]) (some (0, 5, 4)) (some (1, 5, 4)) (.next ([-3765000000000], [4110000000000])
    (some (1, 5, 4)) (some (1, 5, 4)) (.terminal (some (1, 5, 4)) (some (1, 5, 0)) (some (1, 5,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan50Owner2Part0 : FanWitness := (.next ([4230000000000], [2250000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([3780000000000, 9000000000000], [2985000000000, -9000000000000]) (some
    (0, 2, 5)) (some (0, 2, 5)) (.next ([3001500000000], [3780000000000]) (some (0, 2, 5)) (some (0,
    2, 5)) (.next ([285000000000, 0], [450000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2,
    5)) (.next ([2625000000000], [5745000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([1890000000000], [4875000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([1890000000000,
    9000000000000], [6030000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([751500000000],
    [3028500000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([735000000000], [4140000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([285000000000], [2340000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([0], [6030000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-16500000000], [1111500000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-1155000000000],
    [6496500000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1890000000000, 9000000000000],
    [6781500000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2250000000000], [6480000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2985000000000, 9000000000000], [6765000000000, 0])
    (some (0, 2, 4)) (some (0, 5, 4)) (.next ([-3780000000000], [6781500000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-450000000000, 9000000000000], [735000000000, -9000000000000]) (some
    (0, 5, 4)) (some (0, 5, 4)) (.next ([-5745000000000], [8370000000000]) (some (0, 5, 4)) (some
    (0, 5, 4)) (.next ([-4875000000000], [6765000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-6030000000000, 0], [7920000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-3028500000000], [3780000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4140000000000],
    [4875000000000]) (some (0, 5, 4)) (some (1, 5, 4)) (.next ([-2340000000000], [2625000000000])
    (some (1, 5, 4)) (some (1, 5, 4)) (.terminal (some (1, 5, 4)) (some (1, 5, 0)) (some (1, 5,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan51Owner1Part0 : FanWitness := (.next ([5670000000000, 9000000000000], [1110000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([6615000000000], [2385000000000])
    (some (4, 5, 2)) (some (4, 5, 2)) (.next ([4275000000000], [2625000000000]) (some (4, 5, 2))
    (some (4, 5, 2)) (.next ([3900000000000], [2505000000000]) (some (4, 5, 2)) (some (4, 5, 2))
    (.next ([3780000000000], [3000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([1890000000000, 9000000000000], [1890000000000, 9000000000000]) (some (4, 5, 2)) (some (4, 5,
    2)) (.next ([1890000000000, -9000000000000], [3000000000000, 0]) (some (4, 5, 2)) (some (4, 5,
    2)) (.next ([2385000000000, -9000000000000], [4515000000000, 9000000000000]) (some (4, 5, 2))
    (some (4, 5, 2)) (.next ([1605000000000, 9000000000000], [6660000000000]) (some (4, 5, 2)) (some
    (4, 5, 2)) (.next ([120000000000], [2595000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([0], [1890000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([-285000000000],
    [6660000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next ([-285000000000, 0], [4770000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-735000000000, 9000000000000],
    [5010000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-1110000000000,
    9000000000000], [6780000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2385000000000],
    [9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2625000000000], [6900000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2505000000000], [6405000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([-3000000000000], [6780000000000]) (some (0, 1, 4)) (some (5, 1, 4))
    (.next ([-1890000000000, -9000000000000], [3780000000000, 18000000000000]) (some (5, 1, 4))
    (some (5, 1, 4)) (.next ([-3000000000000, 0], [4890000000000, -9000000000000]) (some (5, 1, 4))
    (some (5, 1, 4)) (.next ([-4515000000000, -9000000000000], [6900000000000, 0]) (some (5, 1, 4))
    (some (5, 1, 4)) (.next ([-6660000000000], [8265000000000, 9000000000000]) (some (5, 1, 4))
    (some (5, 1, 4)) (.next ([-2595000000000], [2715000000000]) (some (5, 1, 4)) (some (5, 1, 4))
    (.terminal (some (5, 1, 4)) (some (5, 1, 4)) (some (5, 1, 4)))))))))))))))))))))))))))

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6585000000000], [270000000000]) (some (8, 0, 3))
      (some (8, 0, 3)) (.next ([4875000000000], [228000000000]) (some (8, 0, 3)) (some (8, 0, 3))
      (.next ([6585000000000], [525000000000]) (some (8, 0, 3)) (some (8, 1, 3)) (.next
      ([7545000000000], [1110000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([6630000000000],
      [1065000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([6210000000000], [1800000000000])
      (some (8, 1, 3)) (some (8, 1, 3)) (.next ([2148000000000], [630000000000]) (some (8, 1, 3))
      (some (8, 1, 3)) (.next ([6000000000000], [1938000000000]) (some (8, 1, 3)) (some (8, 1, 3))
      (.next ([1155000000000], [375000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next
      ([900000000000], [375000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([5580000000000],
      [2673000000000]) (some (8, 1, 3)) (some (8, 1, 3)) (.next ([5835000000000], [3945000000000])
      (some (8, 1, 3)) (some (8, 1, 3)) (.next ([1398000000000], [1005000000000]) (some (8, 1, 3))
      (some (8, 1, 3)) (.next ([5100000000000], [4260000000000]) (some (8, 1, 3)) (some (8, 1, 3))
      (.next ([3750000000000], [3150000000000]) (some (8, 1, 3)) (some (8, 1, 8)) (.next
      ([1143000000000], [1005000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([3993000000000],
      [3780000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([2850000000000], [2775000000000])
      (some (7, 1, 8)) (some (7, 1, 8)) (.next ([375000000000], [375000000000]) (some (7, 1, 8))
      (some (7, 1, 8)) (.next ([2595000000000], [2775000000000]) (some (7, 1, 8)) (some (7, 1, 8))
      (.next ([2550000000000], [2955000000000]) (some (7, 1, 8)) (some (7, 1, 8))
      fan48Owner0Part1)))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1095000000000], [16500000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([3000000000000, 0], [330000000000, -9000000000000]) (some (0, 1, 5))
      (some (0, 2, 5)) (.next ([4891500000000, 9000000000000], [1890000000000, -9000000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) fan48Owner2Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_3 : ExcludedOn (model48.B 3 ++ [step48.q]) 9000000000000 (model48.caps 3)
    (model48.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded48_2
    · exact excluded48_3
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
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_1 : ExcludedOn (model49.B 1 ++ [step49.q]) 9000000000000 (model49.caps 1)
    (model49.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_2 : ExcludedOn (model49.B 2 ++ [step49.q]) 9000000000000 (model49.caps 2)
    (model49.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1095000000000], [16500000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([4891500000000, 9000000000000], [1890000000000, -9000000000000])
      (some (0, 1, 5)) (some (0, 2, 5)) (.next ([5251500000000], [3780000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([3780000000000, 9000000000000], [2985000000000, -9000000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([4140000000000], [4875000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([3001500000000], [3780000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([1890000000000], [4875000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([1890000000000, 9000000000000], [6030000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([751500000000], [3028500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([735000000000],
      [4140000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([0], [6030000000000]) (some (0, 2,
      5)) (some (0, 2, 5)) (.next ([-16500000000], [1111500000000]) (some (0, 2, 5)) (some (0, 2,
      5)) (.next ([-1890000000000, 9000000000000], [6781500000000, 0]) (some (0, 2, 5)) (some (0, 2,
      5)) (.next ([-3780000000000], [9031500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-2985000000000, 9000000000000], [6765000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-4875000000000], [9015000000000]) (some (0, 2, 5)) (some (0, 3, 5)) (.next
      ([-3780000000000], [6781500000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
      ([-4875000000000], [6765000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-6030000000000,
      0], [7920000000000, 9000000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
      ([-3028500000000], [3780000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
      ([-4140000000000], [4875000000000]) (some (0, 3, 5)) (some (1, 3, 5)) (.terminal (some (1, 3,
      5)) (some (1, 5, 0)) (some (1, 5, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_3 : ExcludedOn (model49.B 3 ++ [step49.q]) 9000000000000 (model49.caps 3)
    (model49.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_4 : ExcludedOn (model49.B 4 ++ [step49.q]) 9000000000000 (model49.caps 4)
    (model49.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_6 : ExcludedOn (model49.B 6 ++ [step49.q]) 9000000000000 (model49.caps 6)
    (model49.ord 6) 0 1 100 := by
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded49_4
    · exact excluded49_5
    · exact excluded49_6
    · exact (hj rfl).elim
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

theorem excluded50_2 : ExcludedOn (model50.B 2 ++ [step50.q]) 9000000000000 (model50.caps 2)
    (model50.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1095000000000], [16500000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([5341500000000], [1155000000000]) (some (0, 1, 5)) (some (0, 2, 5))
      (.next ([4891500000000, 9000000000000], [1890000000000, -9000000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) fan50Owner2Part0)))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_3 : ExcludedOn (model50.B 3 ++ [step50.q]) 9000000000000 (model50.caps 3)
    (model50.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_4 : ExcludedOn (model50.B 4 ++ [step50.q]) 9000000000000 (model50.caps 4)
    (model50.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_5 : ExcludedOn (model50.B 5 ++ [step50.q]) 9000000000000 (model50.caps 5)
    (model50.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_6 : ExcludedOn (model50.B 6 ++ [step50.q]) 9000000000000 (model50.caps 6)
    (model50.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_7 : ExcludedOn (model50.B 7 ++ [step50.q]) 9000000000000 (model50.caps 7)
    (model50.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2535000000000], [90000000000]) (some (0, 3, 1))
      (some (0, 3, 2)) (.next ([6660000000000], [375000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([6660000000000], [2625000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([2250000000000], [4500000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0],
      [6750000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-90000000000], [2625000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-375000000000], [7035000000000]) (some (0, 3, 2))
      (some (3, 3, 2)) (.next ([-2625000000000], [9285000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-4500000000000], [6750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some
      (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_8 : ExcludedOn (model50.B 8 ++ [step50.q]) 9000000000000 (model50.caps 8)
    (model50.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_9 : ExcludedOn (model50.B 9 ++ [step50.q]) 9000000000000 (model50.caps 9)
    (model50.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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

theorem excluded51_1 : ExcludedOn (model51.B 1 ++ [step51.q]) 9000000000000 (model51.caps 1)
    (model51.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6375000000000], [285000000000]) (some (4, 5, 1))
      (some (4, 5, 2)) (.next ([4485000000000, -9000000000000], [285000000000, 0]) (some (4, 5, 2))
      (some (4, 5, 2)) (.next ([4275000000000], [735000000000, -9000000000000]) (some (4, 5, 2))
      (some (4, 5, 2)) fan51Owner1Part0))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded51_2 : ExcludedOn (model51.B 2 ++ [step51.q]) 9000000000000 (model51.caps 2)
    (model51.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_3 : ExcludedOn (model51.B 3 ++ [step51.q]) 9000000000000 (model51.caps 3)
    (model51.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_4 : ExcludedOn (model51.B 4 ++ [step51.q]) 9000000000000 (model51.caps 4)
    (model51.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_5 : ExcludedOn (model51.B 5 ++ [step51.q]) 9000000000000 (model51.caps 5)
    (model51.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_6 : ExcludedOn (model51.B 6 ++ [step51.q]) 9000000000000 (model51.caps 6)
    (model51.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4275000000000], [735000000000, -9000000000000])
      (some (2, 0, 1)) (some (2, 0, 2)) (.next ([3990000000000, 9000000000000], [2385000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([2100000000000], [4275000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1890000000000, 9000000000000], [7110000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1890000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-735000000000, 9000000000000],
      [5010000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2385000000000,
      9000000000000], [6375000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4275000000000],
      [6375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7110000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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

theorem excluded51_9 : ExcludedOn (model51.B 9 ++ [step51.q]) 9000000000000 (model51.caps 9)
    (model51.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked51 : StepValid model51 9000000000000 step51 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded51_1
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

end Sext210000220000
end ConwaySoifer.Simplified.Certificates
