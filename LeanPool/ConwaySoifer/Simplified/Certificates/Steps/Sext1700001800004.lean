/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext170000180000
import Mathlib.Tactic.FinCases

/-!
# Sext 170000 180000 4

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
namespace Sext170000180000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part0 : FanWitness := (.next ([-900000000000], [1785000000000]) (some (0, 3, 6))
    (some (1, 3, 7)) (.next ([-525000000000], [1020000000000]) (some (1, 3, 7)) (some (1, 3, 7))
    (.next ([-4140000000000], [7875000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next
    ([-510000000000], [885000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-3375000000000],
    [5790000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-1710000000000], [2805000000000])
    (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-1815000000000], [2805000000000]) (some (1, 3, 7))
    (some (1, 3, 7)) (.next ([-120000000000], [180000000000]) (some (1, 3, 7)) (some (1, 3, 7))
    (.next ([-4140000000000], [6180000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next
    ([-4260000000000], [6165000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-1905000000000],
    [2745000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-1995000000000], [2865000000000])
    (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-2250000000000], [3060000000000]) (some (1, 3, 7))
    (some (1, 3, 7)) (.next ([-1965000000000], [2625000000000]) (some (1, 3, 7)) (some (1, 9, 7))
    (.next ([-4635000000000], [5655000000000]) (some (1, 9, 7)) (some (1, 9, 7)) (.next
    ([-4260000000000], [4890000000000]) (some (1, 9, 7)) (some (1, 9, 7)) (.next ([-6180000000000],
    [6885000000000]) (some (1, 9, 7)) (some (2, 9, 7)) (.next ([-1290000000000], [1410000000000])
    (some (2, 9, 7)) (some (2, 9, 7)) (.next ([-6120000000000], [6630000000000]) (some (2, 9, 7))
    (some (2, 9, 7)) (.next ([-6000000000000], [6450000000000]) (some (2, 9, 7)) (some (2, 9, 7))
    (.next ([-6945000000000], [7275000000000]) (some (2, 9, 7)) (some (2, 9, 7)) (.next
    ([-7065000000000], [7260000000000]) (some (2, 9, 7)) (some (2, 9, 7)) (.next ([-6885000000000],
    [7020000000000]) (some (2, 9, 7)) (some (2, 9, 7)) (.next ([-6765000000000], [6840000000000])
    (some (2, 9, 7)) (some (2, 9, 7)) (.terminal (some (2, 9, 7)) (some (2, 9, 7)) (some (2, 9,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part1 : FanWitness := (.next ([510000000000], [6120000000000]) (some (0, 3, 9)) (some
    (0, 3, 9)) (.next ([450000000000], [6000000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next
    ([330000000000], [6945000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([195000000000],
    [7065000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([135000000000], [6885000000000])
    (some (0, 3, 9)) (some (0, 3, 9)) (.next ([75000000000], [6765000000000]) (some (0, 3, 9)) (some
    (0, 3, 9)) (.next ([0], [1275000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next
    ([-60000000000], [6885000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-690000000000],
    [7440000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-135000000000], [1395000000000])
    (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-15000000000], [135000000000]) (some (0, 3, 9)) (some
    (0, 3, 9)) (.next ([-885000000000], [7380000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next
    ([-945000000000], [7260000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-1080000000000],
    [7065000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-1275000000000], [7005000000000])
    (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-1335000000000], [6885000000000]) (some (0, 3, 9))
    (some (0, 3, 9)) (.next ([-60000000000], [255000000000]) (some (0, 3, 9)) (some (0, 3, 9))
    (.next ([-1155000000000], [4770000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next
    ([-2355000000000], [6990000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([-2730000000000],
    [7755000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2865000000000], [7875000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-180000000000], [435000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-3750000000000], [8250000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-375000000000], [765000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    fan33Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part2 : FanWitness := (.next ([4635000000000], [2355000000000]) (some (8, 2, 9))
    (some (8, 2, 9)) (.next ([5025000000000], [2730000000000]) (some (8, 2, 9)) (some (8, 2, 9))
    (.next ([5010000000000], [2865000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next
    ([255000000000], [180000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([4500000000000],
    [3750000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([390000000000], [375000000000]) (some
    (8, 2, 9)) (some (8, 2, 9)) (.next ([885000000000], [900000000000]) (some (8, 2, 9)) (some (8,
    2, 9)) (.next ([495000000000], [525000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next
    ([3735000000000], [4140000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([375000000000],
    [510000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([2415000000000], [3375000000000])
    (some (0, 2, 9)) (some (0, 2, 9)) (.next ([1095000000000], [1710000000000]) (some (0, 2, 9))
    (some (0, 2, 9)) (.next ([990000000000], [1815000000000]) (some (0, 2, 9)) (some (0, 3, 9))
    (.next ([60000000000], [120000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next
    ([2040000000000], [4140000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([1905000000000],
    [4260000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([840000000000], [1905000000000])
    (some (0, 3, 9)) (some (0, 3, 9)) (.next ([870000000000], [1995000000000]) (some (0, 3, 9))
    (some (0, 3, 9)) (.next ([810000000000], [2250000000000]) (some (0, 3, 9)) (some (0, 3, 9))
    (.next ([660000000000], [1965000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next
    ([1020000000000], [4635000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([630000000000],
    [4260000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([705000000000], [6180000000000])
    (some (0, 3, 9)) (some (0, 3, 9)) (.next ([120000000000], [1290000000000]) (some (0, 3, 9))
    (some (0, 3, 9)) fan33Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner3Part0 : FanWitness := (.next ([750000000000], [1290000000000]) (some (6, 0, 2)) (some
    (6, 0, 3)) (.next ([2040000000000], [4371000000000]) (some (6, 0, 4)) (some (6, 0, 4)) (.next
    ([1530000000000, 9000000000000], [5121000000000]) (some (6, 0, 4)) (some (6, 0, 4)) (.next
    ([441000000000], [4590000000000]) (some (6, 0, 4)) (some (6, 0, 4)) (.next ([375000000000],
    [4044000000000]) (some (6, 0, 4)) (some (6, 0, 4)) (.next ([126000000000], [4629000000000])
    (some (6, 0, 4)) (some (6, 0, 4)) (.next ([9000000000], [2241000000000]) (some (6, 0, 4)) (some
    (6, 0, 4)) (.next ([0], [5121000000000]) (some (6, 0, 4)) (some (6, 1, 4)) (.next
    ([-90000000000], [4680000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-99000000000],
    [2439000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-210000000000], [4380000000000])
    (some (6, 1, 4)) (some (6, 2, 4)) (.next ([-375000000000, 0], [4284000000000, 9000000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-720000000000, 9000000000000], [5130000000000]) (some
    (6, 2, 4)) (some (6, 2, 4)) (.next ([-2313000000000], [6969000000000]) (some (6, 2, 4)) (some
    (6, 2, 4)) (.next ([-2250000000000], [5130000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-2379000000000], [4746000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-2550000000000],
    [4281000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1290000000000], [2040000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4371000000000], [6411000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-5121000000000, 0], [6651000000000, 9000000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-4590000000000], [5031000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-4044000000000], [4419000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-4629000000000], [4755000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2241000000000],
    [2250000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4))
    (some (0, 2, 4)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked32 : StepValid model32 9000000000000 step32 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded32_0
    · exact excluded32_1
    · exact excluded32_2
    · exact excluded32_3
    · exact excluded32_4
    · exact excluded32_5
    · exact excluded32_6
    · exact (hj rfl).elim
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6825000000000], [60000000000]) (some (7, 2, 9))
      (some (7, 2, 9)) (.next ([6750000000000], [690000000000]) (some (7, 2, 9)) (some (7, 2, 9))
      (.next ([1260000000000], [135000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next
      ([120000000000], [15000000000]) (some (7, 2, 9)) (some (7, 2, 9)) (.next ([6495000000000],
      [885000000000]) (some (7, 2, 9)) (some (8, 2, 9)) (.next ([6315000000000], [945000000000])
      (some (8, 2, 9)) (some (8, 2, 9)) (.next ([5985000000000], [1080000000000]) (some (8, 2, 9))
      (some (8, 2, 9)) (.next ([5730000000000], [1275000000000]) (some (8, 2, 9)) (some (8, 2, 9))
      (.next ([5550000000000], [1335000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next
      ([195000000000], [60000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([3615000000000],
      [1155000000000]) (some (8, 2, 9)) (some (8, 2, 9)) fan33Owner0Part2)))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4770000000000, 9000000000000], [105000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([3240000000000], [1635000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1635000000000], [2595000000000, -9000000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1530000000000, 9000000000000], [7470000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1530000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-105000000000, 9000000000000],
      [4875000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1635000000000], [4875000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2595000000000, 9000000000000], [4230000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7470000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked33 : StepValid model33 9000000000000 step33 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded33_0
    · exact (hj rfl).elim
    · exact excluded33_2
    · exact excluded33_3
    · exact excluded33_4
    · exact excluded33_5
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1845000000000, -9000000000000], [1530000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([3750000000000], [5565000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1905000000000, 9000000000000], [4035000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1530000000000, 9000000000000],
      [5121000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([819000000000], [4746000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([375000000000], [5565000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([0], [5121000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-1530000000000, -9000000000000], [3375000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-5565000000000], [9315000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-4035000000000,
      9000000000000], [5940000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next ([-5121000000000],
      [6651000000000, 9000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-4746000000000],
      [5565000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-5565000000000], [5940000000000])
      (some (4, 1, 4)) (some (4, 2, 4)) (.terminal (some (4, 2, 4)) (some (0, 2, 4)) (some (4, 2,
      4))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_9 : ExcludedOn (model34.B 9 ++ [step34.q]) 9000000000000 (model34.caps 9)
    (model34.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked34 : StepValid model34 9000000000000 step34 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded34_0
    · exact excluded34_1
    · exact excluded34_2
    · exact excluded34_3
    · exact excluded34_4
    · exact excluded34_5
    · exact excluded34_6
    · exact excluded34_7
    · exact (hj rfl).elim
    · exact excluded34_9
theorem next34 : model34.insert step34 = model35 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded35_0 : ExcludedOn (model35.B 0 ++ [step35.q]) 9000000000000 (model35.caps 0)
    (model35.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4590000000000], [90000000000]) (some (4, 0, 2))
      (some (5, 0, 2)) (.next ([2340000000000], [99000000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([4170000000000], [210000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next
      ([3909000000000, 9000000000000], [375000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next
      ([4410000000000, 9000000000000], [720000000000, -9000000000000]) (some (5, 0, 2)) (some (5, 0,
      2)) (.next ([4656000000000], [2313000000000]) (some (5, 0, 2)) (some (6, 0, 2)) (.next
      ([2880000000000], [2250000000000]) (some (6, 0, 2)) (some (6, 0, 2)) (.next ([2367000000000],
      [2379000000000]) (some (6, 0, 2)) (some (6, 0, 2)) (.next ([1731000000000], [2550000000000])
      (some (6, 0, 2)) (some (6, 0, 2)) fan35Owner3Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_7 : ExcludedOn (model35.B 7 ++ [step35.q]) 9000000000000 (model35.caps 7)
    (model35.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_9 : ExcludedOn (model35.B 9 ++ [step35.q]) 9000000000000 (model35.caps 9)
    (model35.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked35 : StepValid model35 9000000000000 step35 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded35_0
    · exact excluded35_1
    · exact excluded35_2
    · exact excluded35_3
    · exact excluded35_4
    · exact excluded35_5
    · exact excluded35_6
    · exact excluded35_7
    · exact (hj rfl).elim
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3675000000000], [2265000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([3300000000000], [5121000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([1905000000000, 9000000000000], [4035000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1530000000000, 9000000000000], [5121000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([819000000000], [4746000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([375000000000], [5565000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [5121000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-2265000000000], [5940000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5121000000000], [8421000000000]) (some (0, 1, 2))
      (some (0, 1, 4)) (.next ([-4035000000000, 9000000000000], [5940000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5121000000000], [6651000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-4746000000000], [5565000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-5565000000000], [5940000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3885000000000], [1740000000000]) (some (0, 0,
      4)) (some (0, 1, 4)) (.next ([5700000000000], [3300000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([2946000000000], [2379000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([996000000000], [5250000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([375000000000],
      [2361000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([585000000000], [5115000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([375000000000], [6246000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([75000000000], [3300000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([0], [5625000000000]) (some (0, 1, 2)) (some (0, 4, 2)) (.next ([-1740000000000],
      [5625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3300000000000], [9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2379000000000], [5325000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5250000000000], [6246000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-2361000000000], [2736000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-5115000000000], [5700000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next
      ([-6246000000000], [6621000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3300000000000], [3375000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked36 : StepValid model36 9000000000000 step36 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded36_0
    · exact excluded36_1
    · exact excluded36_2
    · exact (hj rfl).elim
    · exact excluded36_4
    · exact excluded36_5
    · exact excluded36_6
    · exact excluded36_7
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4590000000000], [669000000000]) (some (3, 0, 1))
      (some (4, 0, 1)) (.next ([4320000000000], [711000000000]) (some (4, 0, 1)) (some (4, 0, 1))
      (.next ([1839000000000], [750000000000]) (some (4, 0, 1)) (some (4, 0, 5)) (.next
      ([3879000000000], [5700000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1731000000000],
      [2550000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([750000000000], [1290000000000])
      (some (4, 0, 5)) (some (4, 0, 5)) (.next ([2040000000000], [4950000000000]) (some (4, 0, 5))
      (some (4, 0, 5)) (.next ([1530000000000, 9000000000000], [5700000000000]) (some (4, 0, 5))
      (some (4, 0, 5)) (.next ([441000000000], [4590000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      (.next ([0], [5700000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([-669000000000],
      [5259000000000]) (some (0, 0, 5)) (some (0, 0, 5)) (.next ([-711000000000], [5031000000000])
      (some (0, 0, 5)) (some (0, 1, 5)) (.next ([-750000000000], [2589000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([-5700000000000], [9579000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([-2550000000000], [4281000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-1290000000000], [2040000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4950000000000], [6990000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5700000000000,
      0], [7230000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4590000000000], [5031000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1,
      5)) (some (0, 1, 3)) (some (0, 1, 5))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_8 : ExcludedOn (model37.B 8 ++ [step37.q]) 9000000000000 (model37.caps 8)
    (model37.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked37 : StepValid model37 9000000000000 step37 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded37_0
    · exact excluded37_1
    · exact (hj rfl).elim
    · exact excluded37_3
    · exact excluded37_4
    · exact excluded37_5
    · exact excluded37_6
    · exact excluded37_7
    · exact excluded37_8
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded38_0 : ExcludedOn (model38.B 0 ++ [step38.q]) 9000000000000 (model38.caps 0)
    (model38.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5940000000000, 9000000000000], [3501000000000,
      -9000000000000]) (some (4, 0, 1)) (some (4, 0, 2)) (.next ([1530000000000, 9000000000000],
      [1530000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([4410000000000],
      [5031000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1635000000000], [2595000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([2880000000000, -9000000000000],
      [5031000000000, 0]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1635000000000],
      [4125000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([729000000000], [7806000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([105000000000, -9000000000000], [5655000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0], [1530000000000, 9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-3501000000000, 9000000000000], [9441000000000])
      (some (4, 0, 2)) (some (4, 0, 3)) (.next ([-1530000000000, -9000000000000], [3060000000000,
      18000000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([-5031000000000], [9441000000000])
      (some (4, 0, 3)) (some (4, 0, 3)) (.next ([-2595000000000, 9000000000000], [4230000000000,
      -9000000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([-5031000000000, 0],
      [7911000000000, -9000000000000]) (some (4, 0, 3)) (some (4, 1, 3)) (.next ([-4125000000000],
      [5760000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next ([-7806000000000], [8535000000000])
      (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-5655000000000, -9000000000000], [5760000000000,
      0]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0,
      1, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_8 : ExcludedOn (model38.B 8 ++ [step38.q]) 9000000000000 (model38.caps 8)
    (model38.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_9 : ExcludedOn (model38.B 9 ++ [step38.q]) 9000000000000 (model38.caps 9)
    (model38.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked38 : StepValid model38 9000000000000 step38 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded38_0
    · exact excluded38_1
    · exact (hj rfl).elim
    · exact excluded38_3
    · exact excluded38_4
    · exact excluded38_5
    · exact excluded38_6
    · exact excluded38_7
    · exact excluded38_8
    · exact excluded38_9
theorem next38 : model38.insert step38 = model39 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded39_0 : ExcludedOn (model39.B 0 ++ [step39.q]) 9000000000000 (model39.caps 0)
    (model39.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4284000000000, 9000000000000], [621000000000])
      (some (4, 0, 1)) (some (4, 0, 2)) (.next ([2754000000000], [621000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) (some
      (4, 0, 2)) (some (4, 0, 4)) (.next ([1635000000000], [2595000000000, -9000000000000]) (some
      (4, 0, 4)) (some (4, 0, 4)) (.next ([909000000000, 9000000000000], [1845000000000,
      -9000000000000]) (some (4, 0, 4)) none (.next ([1635000000000], [4125000000000]) none none
      (.next ([1014000000000], [7500000000000]) none none (.next ([105000000000, -9000000000000],
      [5655000000000, 9000000000000]) none none (.next ([0], [1530000000000, 9000000000000]) none
      none (.next ([-621000000000], [4905000000000, 9000000000000]) none none (.next
      ([-621000000000], [3375000000000]) none none (.next ([-1530000000000, -9000000000000],
      [3060000000000, 18000000000000]) (some (0, 0, 4)) (some (0, 0, 4)) (.next ([-2595000000000,
      9000000000000], [4230000000000, -9000000000000]) (some (0, 0, 4)) (some (0, 0, 4)) (.next
      ([-1845000000000, 9000000000000], [2754000000000, 0]) (some (0, 0, 4)) (some (0, 1, 4)) (.next
      ([-4125000000000], [5760000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-7500000000000], [8514000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-5655000000000,
      -9000000000000], [5760000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1,
      4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_8 : ExcludedOn (model39.B 8 ++ [step39.q]) 9000000000000 (model39.caps 8)
    (model39.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_9 : ExcludedOn (model39.B 9 ++ [step39.q]) 9000000000000 (model39.caps 9)
    (model39.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked39 : StepValid model39 9000000000000 step39 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded39_0
    · exact excluded39_1
    · exact excluded39_2
    · exact excluded39_3
    · exact excluded39_4
    · exact excluded39_5
    · exact excluded39_6
    · exact (hj rfl).elim
    · exact excluded39_8
    · exact excluded39_9
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext170000180000
end ConwaySoifer.Simplified.Certificates
