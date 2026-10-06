/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint110000120000
import Mathlib.Tactic.FinCases

/-!
# Sint 110000 120000 2

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
namespace Sint110000120000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part0 : FanWitness := (.next ([-409200000000, 5280000000000], [5199600000000,
    -2640000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-699600000000, 2640000000000],
    [8044200000000, -5280000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-620400000000,
    -2640000000000], [6205800000000, 5280000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([-699600000000, 2640000000000], [6290400000000, 2640000000000]) (some (8, 3, 5)) (some (8, 3,
    5)) (.next ([-699600000000, 2640000000000], [5780400000000, 2640000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-45000000000], [360000000000]) (some (8, 3, 5)) (some (8, 3, 5))
    (.next ([-1280400000000, -2640000000000], [9205800000000, 5280000000000]) (some (8, 3, 5)) (some
    (8, 3, 6)) (.next ([-980400000000, -2640000000000], [6520800000000, 5280000000000]) (some (8, 3,
    6)) (some (8, 3, 6)) (.next ([-910800000000, -5280000000000], [5915400000000, 2640000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-135000000000], [795000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([-1280400000000, -2640000000000], [6580800000000, 5280000000000]) (some
    (8, 3, 6)) (some (8, 3, 6)) (.next ([-1270800000000, -5280000000000], [6230400000000,
    2640000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-1280400000000, -2640000000000],
    [6070800000000, 5280000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-1570800000000,
    -5280000000000], [6290400000000, 2640000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-1570800000000, -5280000000000], [5780400000000, 2640000000000]) (some (8, 3, 6)) (some (8, 3,
    6)) (.next ([-285000000000], [660000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-290400000000, -2640000000000], [580800000000, 5280000000000]) (some (8, 3, 6)) (some (8, 3,
    6)) (.next ([-450000000000], [750000000000]) (some (8, 3, 6)) (some (8, 4, 6)) (.next
    ([-5490000000000], [7635000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-6285000000000],
    [8295000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-6000000000000], [7635000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-6240000000000], [7935000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-240000000000], [300000000000]) (some (8, 4, 6)) (some (8, 4, 8))
    (.next ([-5334600000000, 2640000000000], [5585400000000, 2640000000000]) (some (8, 4, 8)) (some
    (8, 4, 8)) (.terminal (some (8, 4, 8)) (some (8, 4, 8)) (some (8, 4,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part1 : FanWitness := (.next ([7925400000000, 2640000000000], [1280400000000,
    2640000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([5540400000000, 2640000000000],
    [980400000000, 2640000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([5004600000000,
    -2640000000000], [910800000000, 5280000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([660000000000], [135000000000]) (some (8, 2, 4)) (some (8, 2, 5)) (.next ([5300400000000,
    2640000000000], [1280400000000, 2640000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([4959600000000, -2640000000000], [1270800000000, 5280000000000]) (some (8, 2, 5)) (some (8, 2,
    5)) (.next ([4790400000000, 2640000000000], [1280400000000, 2640000000000]) (some (8, 2, 5))
    (some (8, 2, 5)) (.next ([4719600000000, -2640000000000], [1570800000000, 5280000000000]) (some
    (8, 2, 5)) (some (8, 2, 5)) (.next ([4209600000000, -2640000000000], [1570800000000,
    5280000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([375000000000], [285000000000]) (some
    (8, 2, 5)) (some (8, 2, 5)) (.next ([290400000000, 2640000000000], [290400000000,
    2640000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([300000000000], [450000000000]) (some
    (8, 2, 5)) (some (8, 3, 5)) (.next ([2145000000000], [5490000000000]) (some (8, 3, 5)) (some (8,
    3, 5)) (.next ([2010000000000], [6285000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([1635000000000], [6000000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([1695000000000],
    [6240000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([60000000000], [240000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([250800000000, 5280000000000], [5334600000000,
    -2640000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([0], [510000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-39600000000, 2640000000000], [5915400000000, 2640000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([-109200000000, 5280000000000], [5649600000000,
    -2640000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-409200000000, 5280000000000],
    [8334600000000, -2640000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-399600000000,
    2640000000000], [6230400000000, 2640000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([-409200000000, 5280000000000], [5709600000000, -2640000000000]) (some (8, 3, 5)) (some (8, 3,
    5)) fan20Owner0Part0))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([990000000000, 9000000000000], [990000000000,
      9000000000000]) (some (2, 3, 1)) (some (2, 3, 2)) (.next ([2580000000000], [6420000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2580000000000], [7410000000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1590000000000, -9000000000000], [6420000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [990000000000, 9000000000000]) (some (0, 3,
      2)) (some (3, 3, 2)) (.next ([-990000000000, -9000000000000], [1980000000000, 18000000000000])
      (some (3, 3, 2)) (some (3, 3, 2)) (.next ([-6420000000000], [9000000000000]) (some (3, 3, 2))
      (some (3, 3, 2)) (.next ([-7410000000000, -9000000000000], [9990000000000, 9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-6420000000000, 0], [8010000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      2)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked16 : StepValid model16 9000000000000 step16 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded16_0
    · exact excluded16_1
    · exact excluded16_2
    · exact excluded16_3
    · exact excluded16_4
    · exact excluded16_5
    · exact excluded16_6
    · exact excluded16_7
    · exact excluded16_8
    · exact (hj rfl).elim
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded17_0 : ExcludedOn (model17.B 0 ++ [step17.q]) 9000000000000 (model17.caps 0)
    (model17.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([990000000000, 9000000000000], [990000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2370000000000], [6135000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2370000000000], [7125000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1380000000000, -9000000000000], [8115000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-990000000000, -9000000000000],
      [1980000000000, 18000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-6135000000000,
      9000000000000], [8505000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-7125000000000], [9495000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8115000000000,
      -9000000000000], [9495000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6630000000000], [1875000000000]) (some (0, 0,
      4)) (some (0, 1, 4)) (.next ([1980000000000], [645000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([5640000000000, -9000000000000], [1875000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([2625000000000, 0], [990000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([990000000000, -9000000000000], [1635000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([750000000000], [6525000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([750000000000], [8505000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [2625000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1875000000000], [8505000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-645000000000], [2625000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1875000000000, 0], [7515000000000, -9000000000000]) (some (0, 2,
      4)) (some (0, 2, 4)) (.next ([-990000000000, -9000000000000], [3615000000000, 9000000000000])
      (some (0, 2, 4)) (some (0, 4, 4)) (.next ([-1635000000000, -9000000000000], [2625000000000])
      (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-6525000000000], [7275000000000]) (some (0, 4, 4))
      (some (0, 4, 4)) (.next ([-8505000000000], [9255000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.terminal (some (0, 4, 3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_9 : ExcludedOn (model17.B 9 ++ [step17.q]) 9000000000000 (model17.caps 9)
    (model17.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked17 : StepValid model17 9000000000000 step17 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded17_0
    · exact excluded17_1
    · exact excluded17_2
    · exact excluded17_3
    · exact excluded17_4
    · exact excluded17_5
    · exact (hj rfl).elim
    · exact excluded17_7
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded18_0 : ExcludedOn (model18.B 0 ++ [step18.q]) 9000000000000 (model18.caps 0)
    (model18.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6930000000000], [750000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([5940000000000, -9000000000000], [750000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([1980000000000], [645000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([2625000000000, 0], [990000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([990000000000, -9000000000000], [1635000000000, 9000000000000]) (some (0, 1, 4)) (some
      (0, 1, 4)) (.next ([1875000000000], [5700000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1875000000000], [7680000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [2625000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-750000000000], [7680000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-750000000000, 0], [6690000000000, -9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-645000000000], [2625000000000]) (some (0, 2, 4))
      (some (0, 4, 4)) (.next ([-990000000000, -9000000000000], [3615000000000, 9000000000000])
      (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-1635000000000, -9000000000000], [2625000000000])
      (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-5700000000000], [7575000000000]) (some (0, 4, 4))
      (some (0, 4, 4)) (.next ([-7680000000000], [9555000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.terminal (some (0, 4, 3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_9 : ExcludedOn (model18.B 9 ++ [step18.q]) 9000000000000 (model18.caps 9)
    (model18.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7680000000000], [2070000000000]) (some (3, 0,
      1)) (some (3, 1, 2)) (.next ([6690000000000, -9000000000000], [2070000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([1590000000000, -9000000000000], [990000000000, 9000000000000])
      (some (3, 1, 2)) (some (3, 1, 3)) (.next ([510000000000], [7170000000000]) (some (3, 1, 3))
      (some (3, 1, 3)) (.next ([0], [2580000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2070000000000], [9750000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2070000000000], [8760000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-990000000000, -9000000000000], [2580000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-7170000000000], [7680000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked18 : StepValid model18 9000000000000 step18 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded18_0
    · exact excluded18_1
    · exact excluded18_2
    · exact excluded18_3
    · exact excluded18_4
    · exact excluded18_5
    · exact (hj rfl).elim
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_0 : ExcludedOn (model19.B 0 ++ [step19.q]) 9000000000000 (model19.caps 0)
    (model19.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000, 0], [990000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([3375000000000], [660000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4065000000000], [1935000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([2385000000000, -9000000000000], [1650000000000, 9000000000000])
      (some (3, 1, 2)) (some (4, 1, 2)) (.next ([3405000000000], [4035000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1965000000000], [3375000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([0, 0], [990000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next
      ([-990000000000, -9000000000000], [6990000000000, 9000000000000]) (some (4, 1, 3)) (some (4,
      1, 3)) (.next ([-660000000000], [4035000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-1935000000000], [6000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-1650000000000,
      -9000000000000], [4035000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-4035000000000], [7440000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next
      ([-3375000000000], [5340000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (0, 2, 3)) (some (4, 2, 3))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_9 : ExcludedOn (model19.B 9 ++ [step19.q]) 9000000000000 (model19.caps 9)
    (model19.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked19 : StepValid model19 9000000000000 step19 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded19_0
    · exact excluded19_1
    · exact excluded19_2
    · exact excluded19_3
    · exact excluded19_4
    · exact excluded19_5
    · exact excluded19_6
    · exact excluded19_7
    · exact (hj rfl).elim
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5875800000000, 5280000000000], [39600000000,
      -2640000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([5540400000000, 2640000000000],
      [109200000000, -5280000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next ([7925400000000,
      2640000000000], [409200000000, -5280000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next
      ([5830800000000, 5280000000000], [399600000000, -2640000000000]) (some (8, 2, 4)) (some (8, 2,
      4)) (.next ([5300400000000, 2640000000000], [409200000000, -5280000000000]) (some (8, 2, 4))
      (some (8, 2, 4)) (.next ([4790400000000, 2640000000000], [409200000000, -5280000000000]) (some
      (8, 2, 4)) (some (8, 2, 4)) (.next ([7344600000000, -2640000000000], [699600000000,
      -2640000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([5585400000000, 2640000000000],
      [620400000000, 2640000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([5590800000000,
      5280000000000], [699600000000, -2640000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
      ([5080800000000, 5280000000000], [699600000000, -2640000000000]) (some (8, 2, 4)) (some (8, 2,
      4)) (.next ([315000000000], [45000000000]) (some (8, 2, 4)) (some (8, 2, 4))
      fan20Owner0Part1))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8010000000000, 0], [615000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([6000000000000, 0], [990000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3375000000000], [660000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2385000000000, -9000000000000], [1650000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1965000000000], [3375000000000])
      (some (4, 1, 2)) (some (4, 1, 4)) (.next ([375000000000], [1635000000000]) (some (4, 1, 4))
      (some (4, 1, 4)) (.next ([375000000000], [7635000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([0, 0], [990000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([-615000000000, -9000000000000], [8625000000000, 9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([-990000000000, -9000000000000], [6990000000000, 9000000000000]) (some (0, 1,
      4)) (some (0, 1, 4)) (.next ([-660000000000], [4035000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-1650000000000, -9000000000000], [4035000000000, 0]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([-3375000000000], [5340000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next
      ([-1635000000000], [2010000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-7635000000000], [8010000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1365000000000], [930000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([4440000000000], [3570000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([2145000000000], [4935000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1365000000000], [8010000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [4935000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-930000000000], [2295000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3570000000000], [8010000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-4935000000000], [7080000000000]) (some (0, 1, 2)) (some (0, 3, 2))
      (.next ([-8010000000000], [9375000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_9 : ExcludedOn (model20.B 9 ++ [step20.q]) 9000000000000 (model20.caps 9)
    (model20.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked20 : StepValid model20 9000000000000 step20 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded20_0
    · exact excluded20_1
    · exact excluded20_2
    · exact (hj rfl).elim
    · exact excluded20_4
    · exact excluded20_5
    · exact excluded20_6
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000, 0], [990000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 4, 2)) (.next ([3375000000000], [660000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([6000000000000], [3000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([2385000000000, -9000000000000], [1650000000000, 9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1965000000000], [3375000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([375000000000], [3660000000000]) (some (3, 4, 2)) (some (3, 4, 3))
      (.next ([0, 0], [990000000000, 9000000000000]) (some (3, 4, 3)) (some (3, 4, 3)) (.next
      ([-990000000000, -9000000000000], [6990000000000, 9000000000000]) (some (0, 4, 3)) (some (0,
      4, 3)) (.next ([-660000000000], [4035000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3000000000000], [9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1650000000000,
      -9000000000000], [4035000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3375000000000], [5340000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3660000000000], [4035000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_9 : ExcludedOn (model21.B 9 ++ [step21.q]) 9000000000000 (model21.caps 9)
    (model21.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked21 : StepValid model21 9000000000000 step21 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded21_0
    · exact excluded21_1
    · exact excluded21_2
    · exact excluded21_3
    · exact excluded21_4
    · exact (hj rfl).elim
    · exact excluded21_6
    · exact excluded21_7
    · exact excluded21_8
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2070000000000], [240000000000, 9000000000000])
      (some (5, 5, 3)) (some (5, 5, 4)) (.next ([1875000000000], [495000000000]) (some (5, 5, 4))
      (some (5, 5, 4)) (.next ([825000000000], [300000000000]) (some (5, 5, 4)) (some (5, 5, 4))
      (.next ([5250000000000, 0], [3750000000000, -9000000000000]) (some (5, 5, 4)) (some (5, 5, 4))
      (.next ([4500000000000], [3420000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([5250000000000], [4740000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([990000000000,
      9000000000000], [990000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([3375000000000], [4245000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([4260000000000,
      -9000000000000], [5730000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([750000000000], [1320000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([495000000000,
      9000000000000], [1380000000000, -9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([0,
      0], [990000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-240000000000,
      -9000000000000], [2310000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next
      ([-495000000000], [2370000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-300000000000],
      [1125000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-3750000000000, 9000000000000],
      [9000000000000, -9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-3420000000000],
      [7920000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4740000000000], [9990000000000])
      (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-990000000000, -9000000000000], [1980000000000,
      18000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4245000000000], [7620000000000])
      (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-5730000000000, -9000000000000], [9990000000000])
      (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-1320000000000], [2070000000000]) (some (5, 3, 4))
      (some (5, 3, 5)) (.next ([-1380000000000, 9000000000000], [1875000000000]) (some (5, 3, 5))
      (some (5, 3, 5)) (.terminal (some (5, 3, 5)) (some (5, 3, 5)) (some (5, 3,
      5))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_9 : ExcludedOn (model22.B 9 ++ [step22.q]) 9000000000000 (model22.caps 9)
    (model22.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked22 : StepValid model22 9000000000000 step22 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded22_0
    · exact excluded22_1
    · exact excluded22_2
    · exact excluded22_3
    · exact excluded22_4
    · exact (hj rfl).elim
    · exact excluded22_6
    · exact excluded22_7
    · exact excluded22_8
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2070000000000], [240000000000, 9000000000000])
      (some (5, 5, 3)) (some (5, 5, 4)) (.next ([1875000000000], [495000000000]) (some (5, 5, 4))
      (some (5, 5, 4)) (.next ([825000000000], [300000000000]) (some (5, 5, 4)) (some (5, 5, 4))
      (.next ([5040000000000, 0], [3870000000000, -9000000000000]) (some (5, 5, 4)) (some (5, 5, 4))
      (.next ([4290000000000], [3540000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([5040000000000], [4860000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([990000000000,
      9000000000000], [990000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([3165000000000], [4365000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([4050000000000,
      -9000000000000], [5850000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([750000000000], [1320000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([495000000000,
      9000000000000], [1380000000000, -9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([0,
      0], [990000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-240000000000,
      -9000000000000], [2310000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next
      ([-495000000000], [2370000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-300000000000],
      [1125000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-3870000000000, 9000000000000],
      [8910000000000, -9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-3540000000000],
      [7830000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4860000000000], [9900000000000])
      (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-990000000000, -9000000000000], [1980000000000,
      18000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4365000000000], [7530000000000])
      (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-5850000000000, -9000000000000], [9900000000000])
      (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-1320000000000], [2070000000000]) (some (5, 3, 4))
      (some (5, 3, 5)) (.next ([-1380000000000, 9000000000000], [1875000000000]) (some (5, 3, 5))
      (some (5, 3, 5)) (.terminal (some (5, 3, 5)) (some (5, 3, 5)) (some (5, 3,
      5))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_8 : ExcludedOn (model23.B 8 ++ [step23.q]) 9000000000000 (model23.caps 8)
    (model23.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_9 : ExcludedOn (model23.B 9 ++ [step23.q]) 9000000000000 (model23.caps 9)
    (model23.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked23 : StepValid model23 9000000000000 step23 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded23_0
    · exact excluded23_1
    · exact excluded23_2
    · exact excluded23_3
    · exact excluded23_4
    · exact (hj rfl).elim
    · exact excluded23_6
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint110000120000
end ConwaySoifer.Simplified.Certificates
