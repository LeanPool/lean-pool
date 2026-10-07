/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext255000260000
import Mathlib.Tactic.FinCases

/-!
# Sext 255000 260000 4

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
namespace Sext255000260000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner4Part0 : FanWitness := (.next ([-156000000000], [1830000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-900000000000], [6906000000000]) (some (0, 1, 3)) (some (0, 7, 3))
    (.next ([-1656000000000], [7213500000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next
    ([-1830000000000], [6705000000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-2031000000000],
    [7326000000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-1875000000000], [6006000000000])
    (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-1836000000000], [5250000000000]) (some (0, 7, 3))
    (some (0, 7, 3)) (.next ([-2574000000000], [6750000000000]) (some (0, 7, 3)) (some (0, 7, 3))
    (.next ([-2182500000000], [5557500000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next
    ([-2295000000000], [5295000000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-3330000000000],
    [7057500000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-738000000000], [1500000000000])
    (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-3705000000000], [7170000000000]) (some (0, 7, 3))
    (some (0, 7, 3)) (.next ([-448500000000], [756000000000]) (some (0, 7, 3)) (some (0, 7, 3))
    (.next ([-2949000000000, 9000000000000], [4869000000000]) (some (0, 7, 3)) (some (0, 7, 4))
    (.next ([-711000000000], [1131000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
    ([-5031000000000], [7326000000000, 9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
    ([-262500000000], [375000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-1494000000000],
    [1807500000000]) (some (0, 7, 4)) (some (0, 7, 5)) (.next ([-3711000000000, 9000000000000],
    [4131000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-6705000000000], [7170000000000,
    9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3262500000000, 9000000000000],
    [3375000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1869000000000], [1920000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3000000000000, 9000000000000], [3000000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.terminal (some (0, 7, 5)) (some (0, 7, 6)) (some (0, 7,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner4Part1 : FanWitness := (.next ([4875000000000], [1830000000000]) (some (6, 1, 7))
    (some (6, 1, 7)) (.next ([5295000000000], [2031000000000]) (some (6, 1, 7)) (some (6, 1, 7))
    (.next ([4131000000000], [1875000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([3414000000000], [1836000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([4176000000000],
    [2574000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([3375000000000], [2182500000000])
    (some (6, 1, 2)) (some (6, 1, 2)) (.next ([3000000000000], [2295000000000]) (some (6, 1, 2))
    (some (6, 1, 2)) (.next ([3727500000000], [3330000000000]) (some (6, 1, 2)) (some (6, 1, 2))
    (.next ([762000000000], [738000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
    ([3465000000000], [3705000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([307500000000],
    [448500000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1920000000000, 9000000000000],
    [2949000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([420000000000],
    [711000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2295000000000, 9000000000000],
    [5031000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([112500000000], [262500000000]) (some
    (6, 1, 3)) (some (6, 1, 3)) (.next ([313500000000], [1494000000000]) (some (6, 1, 3)) (some (6,
    1, 3)) (.next ([420000000000, 9000000000000], [3711000000000, -9000000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([465000000000, 9000000000000], [6705000000000]) (some (6, 1, 3)) (some
    (6, 1, 3)) (.next ([112500000000, 9000000000000], [3262500000000, -9000000000000]) (some (6, 1,
    3)) (some (6, 1, 3)) (.next ([51000000000], [1869000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([0, 9000000000000], [3000000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([0], [5031000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([-162000000000],
    [5406000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-375000000000], [5244000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) fan33Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner5Part0 : FanWitness := (.next ([3442500000000], [2625000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([4125000000000], [3510000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([1365000000000], [1215000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([1830000000000], [2295000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([2295000000000,
    9000000000000], [5340000000000, 0]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([727500000000],
    [1897500000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1500000000000], [4237500000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1545000000000], [4875000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([45000000000], [637500000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([0, 9000000000000], [1830000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([0, 0], [2295000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-285000000000, 9000000000000], [6705000000000, 0]) (some (0, 1, 3)) (some (0, 2, 3)) (.next
    ([-330000000000, 9000000000000], [6067500000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-2580000000000], [6705000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2625000000000],
    [6067500000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3510000000000], [7635000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1215000000000], [2580000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([-2295000000000], [4125000000000]) (some (0, 2, 3)) (some (0, 2, 3))
    (.next ([-5340000000000, 0], [7635000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3))
    (.next ([-1897500000000], [2625000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-4237500000000], [5737500000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4875000000000],
    [6420000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-637500000000], [682500000000])
    (some (0, 2, 3)) (some (0, 2, 5)) (.next ([-1830000000000, 9000000000000], [1830000000000, 0])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6420000000000, 9000000000000], [285000000000,
      -9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) (.next ([5737500000000, 9000000000000],
      [330000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4125000000000],
      [2580000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3442500000000], [2625000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1365000000000], [1215000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([3969000000000], [5340000000000]) (some (5, 1, 2)) (some (5, 1, 3))
      (.next ([2295000000000, 9000000000000], [5340000000000, 0]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([727500000000], [1897500000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([1344000000000], [6067500000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1389000000000],
      [6705000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([45000000000], [637500000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 0], [2295000000000, 9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-285000000000, 9000000000000], [6705000000000, 0]) (some (5, 1,
      3)) (some (5, 2, 3)) (.next ([-330000000000, 9000000000000], [6067500000000, 0]) (some (5, 2,
      3)) (some (5, 2, 3)) (.next ([-2580000000000], [6705000000000]) (some (5, 2, 3)) (some (5, 2,
      3)) (.next ([-2625000000000], [6067500000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-1215000000000], [2580000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-5340000000000], [9309000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-5340000000000,
      0], [7635000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-1897500000000], [2625000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-6067500000000], [7411500000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-6705000000000], [8094000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-637500000000],
      [682500000000]) (some (5, 2, 3)) (some (5, 2, 5)) (.terminal (some (5, 2, 5)) (some (0, 2, 5))
      (some (5, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked32 : StepValid model32 9000000000000 step32 0 1 200 := by
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
    · exact (hj rfl).elim
    · exact excluded32_5
    · exact excluded32_6
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5244000000000], [162000000000]) (some (6, 0, 7))
      (some (6, 1, 7)) (.next ([4869000000000], [375000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([1674000000000], [156000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([6006000000000], [900000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([5557500000000],
      [1656000000000]) (some (6, 1, 7)) (some (6, 1, 7)) fan33Owner4Part1)))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6420000000000, 9000000000000], [285000000000,
      -9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) (.next ([5737500000000, 9000000000000],
      [330000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4125000000000],
      [2580000000000]) (some (5, 1, 2)) (some (5, 1, 2)) fan33Owner5Part0)))) (den := 9000000000000)
      (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked33 : StepValid model33 9000000000000 step33 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded33_1
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

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4410000000000, -9000000000000], [2295000000000,
      9000000000000]) (some (3, 4, 1)) none (.next ([2295000000000], [1785000000000]) none none
      (.next ([2625000000000], [2295000000000]) none none (.next ([2295000000000, 9000000000000],
      [2295000000000, 9000000000000]) none none (.next ([2295000000000, 9000000000000],
      [4410000000000, -9000000000000]) none none (.next ([330000000000, -9000000000000],
      [4590000000000, 9000000000000]) none none (.next ([0, 9000000000000], [2625000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0], [2295000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-2295000000000, -9000000000000],
      [6705000000000, 0]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([-1785000000000],
      [4080000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2295000000000], [4920000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2295000000000, -9000000000000], [4590000000000,
      18000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-4410000000000, 9000000000000],
      [6705000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-4590000000000, -9000000000000],
      [4920000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2625000000000, 9000000000000],
      [2625000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1,
      3)) (some (4, 1, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5737500000000, 9000000000000], [705000000000,
      -9000000000000]) (some (2, 4, 1)) (some (3, 4, 1)) (.next ([6705000000000], [2295000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([3442500000000], [3000000000000]) (some (3, 4, 1))
      (some (3, 4, 1)) (.next ([2295000000000, 9000000000000], [2295000000000, 9000000000000]) (some
      (3, 4, 1)) (some (3, 4, 1)) (.next ([4410000000000, -9000000000000], [4590000000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1147500000000, -9000000000000],
      [3000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([262500000000], [5737500000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([0, 9000000000000], [6705000000000, -9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([0, 0], [2295000000000, 9000000000000]) (some (0, 4,
      1)) (some (0, 4, 1)) (.next ([-705000000000, 9000000000000], [6442500000000, 0]) (some (0, 4,
      1)) (some (0, 4, 2)) (.next ([-2295000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([-3000000000000], [6442500000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-2295000000000, -9000000000000], [4590000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-4590000000000, -9000000000000], [9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-3000000000000, 0], [4147500000000, -9000000000000]) (some (0, 4, 2)) (some
      (0, 4, 2)) (.next ([-5737500000000], [6000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-6705000000000, 9000000000000], [6705000000000, 0]) (some (0, 4, 2)) (some (4, 4, 2))
      (.terminal (some (4, 1, 2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4590000000000, 9000000000000], [4410000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2295000000000, 9000000000000],
      [4410000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2295000000000,
      9000000000000], [6705000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([2295000000000], [6705000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [2295000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-4410000000000,
      9000000000000], [9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-4410000000000,
      9000000000000], [6705000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6705000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next
      ([-6705000000000], [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded34_8 : ExcludedOn (model34.B 8 ++ [step34.q]) 9000000000000 (model34.caps 8)
    (model34.ord 8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded34_9 : ExcludedOn (model34.B 9 ++ [step34.q]) 9000000000000 (model34.caps 9)
    (model34.ord 9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked34 : StepValid model34 9000000000000 step34 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded34_1
    · exact excluded34_2
    · exact excluded34_3
    · exact excluded34_4
    · exact excluded34_5
    · exact excluded34_6
    · exact excluded34_7
    · exact excluded34_8
    · exact excluded34_9
theorem next34 : model34.insert step34 = model35 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext255000260000
end ConwaySoifer.Simplified.Certificates
