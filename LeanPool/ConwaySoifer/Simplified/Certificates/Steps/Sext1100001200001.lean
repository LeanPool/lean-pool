/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext110000120000
import Mathlib.Tactic.FinCases

/-!
# Sext 110000 120000 1

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
namespace Sext110000120000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part0 : FanWitness := (.next ([-5535000000000], [10170000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) (.next ([-375000000000], [660000000000]) (some (9, 4, 8)) (some (9, 4, 8))
    (.next ([-758400000000, -2640000000000], [1048800000000, 5280000000000]) (some (9, 4, 8)) (some
    (9, 4, 8)) (.next ([-4209600000000, 2640000000000], [5780400000000, 2640000000000]) (some (9, 4,
    8)) (some (9, 4, 8)) (.next ([-4719600000000, 2640000000000], [6290400000000, 2640000000000])
    (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4500000000000], [5958000000000]) (some (9, 4, 8))
    (some (9, 4, 8)) (.next ([-5010000000000], [6468000000000]) (some (9, 4, 8)) (some (9, 4, 8))
    (.next ([-4790400000000, -2640000000000], [6070800000000, 5280000000000]) (some (9, 4, 8)) (some
    (9, 4, 8)) (.next ([-4959600000000, 2640000000000], [6230400000000, 2640000000000]) (some (9, 4,
    8)) (some (9, 4, 8)) (.next ([-5300400000000, -2640000000000], [6580800000000, 5280000000000])
    (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5250000000000], [6408000000000]) (some (9, 4, 8))
    (some (9, 4, 8)) (.next ([-660000000000], [795000000000]) (some (9, 4, 8)) (some (9, 4, 8))
    (.next ([-5004600000000, 2640000000000], [5915400000000, 2640000000000]) (some (9, 4, 8)) (some
    (9, 4, 8)) (.next ([-5540400000000, -2640000000000], [6520800000000, 5280000000000]) (some (9,
    4, 8)) (some (9, 4, 8)) (.next ([-5295000000000], [6093000000000]) (some (9, 4, 8)) (some (9, 4,
    8)) (.next ([-315000000000], [360000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-5080800000000, -5280000000000], [5780400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 5,
    8)) (.next ([-5590800000000, -5280000000000], [6290400000000, 2640000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-5585400000000, -2640000000000], [6205800000000, 5280000000000]) (some
    (9, 5, 8)) (some (9, 5, 8)) (.next ([-4790400000000, -2640000000000], [5199600000000,
    -2640000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5300400000000, -2640000000000],
    [5709600000000, -2640000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5830800000000,
    -5280000000000], [6230400000000, 2640000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-5540400000000, -2640000000000], [5649600000000, -2640000000000]) (some (9, 5, 8)) (some (9,
    5, 8)) (.next ([-5875800000000, -5280000000000], [5915400000000, 2640000000000]) (some (9, 5,
    8)) (some (9, 5, 8)) (.terminal (some (9, 5, 8)) (some (9, 5, 8)) (some (9, 5,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part1 : FanWitness := (.next ([135000000000], [660000000000]) (some (9, 3, 5)) (some
    (9, 3, 5)) (.next ([910800000000, 5280000000000], [5004600000000, -2640000000000]) (some (9, 3,
    5)) (some (9, 3, 5)) (.next ([980400000000, 2640000000000], [5540400000000, 2640000000000])
    (some (9, 3, 5)) (some (9, 3, 6)) (.next ([798000000000], [5295000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([45000000000], [315000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([699600000000, -2640000000000], [5080800000000, 5280000000000]) (some (9, 3, 6)) (some (9, 3,
    6)) (.next ([699600000000, -2640000000000], [5590800000000, 5280000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([620400000000, 2640000000000], [5585400000000, 2640000000000]) (some
    (9, 3, 6)) (some (9, 3, 6)) (.next ([409200000000, -5280000000000], [4790400000000,
    2640000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([409200000000, -5280000000000],
    [5300400000000, 2640000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([399600000000,
    -2640000000000], [5830800000000, 5280000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([109200000000, -5280000000000], [5540400000000, 2640000000000]) (some (9, 3, 6)) (some (9, 3,
    6)) (.next ([39600000000, -2640000000000], [5875800000000, 5280000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([0, 0], [871200000000, 7920000000000]) (some (9, 3, 6)) (some (9, 3,
    6)) (.next ([-250800000000, -5280000000000], [5585400000000, 2640000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([-699600000000, 2640000000000], [5284200000000, -5280000000000]) (some
    (9, 3, 6)) (some (9, 3, 6)) (.next ([-1280400000000, -2640000000000], [6445800000000,
    5280000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-1458000000000], [6333000000000])
    (some (9, 3, 6)) (some (9, 4, 6)) (.next ([-1570800000000, -5280000000000], [6155400000000,
    2640000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-300000000000], [750000000000]) (some
    (9, 4, 6)) (some (9, 4, 6)) (.next ([-4875000000000], [9885000000000]) (some (9, 4, 6)) (some
    (9, 4, 7)) (.next ([-290400000000, -2640000000000], [580800000000, 5280000000000]) (some (9, 4,
    7)) (some (9, 4, 7)) (.next ([-5175000000000], [10125000000000]) (some (9, 4, 7)) (some (9, 4,
    7)) (.next ([-4875000000000], [9375000000000]) (some (9, 4, 7)) (some (9, 4, 7))
    fan13Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part0 : FanWitness := (.next ([-6468000000000], [9468000000000]) (some (9, 4, 8))
    (some (9, 4, 8)) (.next ([-6580800000000, -5280000000000], [9290400000000, 2640000000000]) (some
    (9, 4, 8)) (some (9, 4, 8)) (.next ([-758400000000, -2640000000000], [1048800000000,
    5280000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4209600000000, 2640000000000],
    [5780400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4719600000000,
    2640000000000], [6290400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-4500000000000], [5958000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5010000000000],
    [6468000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4790400000000, -2640000000000],
    [6070800000000, 5280000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4959600000000,
    2640000000000], [6230400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-5300400000000, -2640000000000], [6580800000000, 5280000000000]) (some (9, 4, 8)) (some (9, 4,
    8)) (.next ([-5250000000000], [6408000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-660000000000], [795000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5004600000000,
    2640000000000], [5915400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-5540400000000, -2640000000000], [6520800000000, 5280000000000]) (some (9, 4, 8)) (some (9, 4,
    8)) (.next ([-5295000000000], [6093000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-315000000000], [360000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5080800000000,
    -5280000000000], [5780400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 5, 8)) (.next
    ([-5590800000000, -5280000000000], [6290400000000, 2640000000000]) (some (9, 5, 8)) (some (9, 5,
    8)) (.next ([-5585400000000, -2640000000000], [6205800000000, 5280000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-4790400000000, -2640000000000], [5199600000000, -2640000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5300400000000, -2640000000000], [5709600000000,
    -2640000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5830800000000, -5280000000000],
    [6230400000000, 2640000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5540400000000,
    -2640000000000], [5649600000000, -2640000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-5875800000000, -5280000000000], [5915400000000, 2640000000000]) (some (9, 5, 8)) (some (9, 5,
    8)) (.terminal (some (9, 5, 8)) (some (9, 5, 8)) (some (9, 5, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner0Part1 : FanWitness := (.next ([135000000000], [660000000000]) (some (9, 9, 5)) (some
    (9, 9, 5)) (.next ([910800000000, 5280000000000], [5004600000000, -2640000000000]) (some (9, 9,
    5)) (some (9, 9, 5)) (.next ([980400000000, 2640000000000], [5540400000000, 2640000000000])
    (some (9, 9, 5)) (some (9, 9, 6)) (.next ([798000000000], [5295000000000]) (some (9, 9, 6))
    (some (9, 9, 6)) (.next ([45000000000], [315000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next
    ([699600000000, -2640000000000], [5080800000000, 5280000000000]) (some (9, 9, 6)) (some (9, 9,
    6)) (.next ([699600000000, -2640000000000], [5590800000000, 5280000000000]) (some (9, 9, 6))
    (some (9, 9, 6)) (.next ([620400000000, 2640000000000], [5585400000000, 2640000000000]) (some
    (9, 9, 6)) (some (9, 9, 6)) (.next ([409200000000, -5280000000000], [4790400000000,
    2640000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([409200000000, -5280000000000],
    [5300400000000, 2640000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([399600000000,
    -2640000000000], [5830800000000, 5280000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next
    ([109200000000, -5280000000000], [5540400000000, 2640000000000]) (some (9, 9, 6)) (some (9, 9,
    6)) (.next ([39600000000, -2640000000000], [5875800000000, 5280000000000]) (some (9, 9, 6))
    (some (9, 9, 6)) (.next ([0, 0], [871200000000, 7920000000000]) (some (9, 9, 6)) (some (9, 9,
    6)) (.next ([-60000000000], [8310000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([-375000000000], [8670000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-250800000000,
    -5280000000000], [5585400000000, 2640000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([-510000000000], [8010000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-60000000000],
    [300000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-300000000000], [750000000000]) (some
    (9, 3, 6)) (some (9, 4, 6)) (.next ([-290400000000, -2640000000000], [580800000000,
    5280000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-375000000000], [660000000000]) (some
    (9, 4, 7)) (some (9, 4, 7)) (.next ([-6290400000000, -2640000000000], [9580800000000,
    5280000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5709600000000, 2640000000000],
    [8419200000000, -5280000000000]) (some (9, 4, 8)) (some (9, 4, 8))
    fan14Owner0Part0))))))))))))))))))))))))

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([990000000000, 9000000000000], [990000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([3705000000000], [4635000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3705000000000], [5625000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2715000000000, -9000000000000], [6615000000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [990000000000, 9000000000000]) none none
      (.next ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (3, 3, 0))
      (some (3, 3, 0)) (.next ([-4635000000000, 9000000000000], [8340000000000, -9000000000000])
      (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-5625000000000], [9330000000000]) (some (3, 1, 0))
      (some (3, 1, 0)) (.next ([-6615000000000, -9000000000000], [9330000000000, 0]) (some (3, 1,
      0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0)))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_4 : ExcludedOn (model8.B 4 ++ [step8.q]) 9000000000000 (model8.caps 4) (model8.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6285000000000, 9000000000000], [2385000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([5295000000000], [3375000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1545000000000], [1830000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([990000000000, 9000000000000], [7125000000000, 0]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([0, 0], [990000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-2385000000000, 9000000000000], [8670000000000, 0]) (some (0, 1, 3)) (some (0, 2,
      3)) (.next ([-3375000000000], [8670000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-1830000000000], [3375000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-7125000000000,
      0], [8115000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [330000000000]) (some (2, 0, 1))
      (some (2, 0, 2)) (.next ([3705000000000], [4635000000000, -9000000000000]) (some (2, 0, 2))
      (some (2, 0, 2)) (.next ([660000000000, 9000000000000], [2715000000000, -9000000000000]) (some
      (2, 0, 2)) (some (3, 0, 2)) (.next ([990000000000, 9000000000000], [8010000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-330000000000], [3705000000000])
      (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-4635000000000, 9000000000000], [8340000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2715000000000, 9000000000000],
      [3375000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-8010000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_8 : ExcludedOn (model8.B 8 ++ [step8.q]) 9000000000000 (model8.caps 8) (model8.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_9 : ExcludedOn (model8.B 9 ++ [step8.q]) 9000000000000 (model8.caps 9) (model8.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked8 : StepValid model8 9000000000000 step8 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded8_1
    · exact excluded8_2
    · exact excluded8_3
    · exact excluded8_4
    · exact excluded8_5
    · exact excluded8_6
    · exact excluded8_7
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_0 : ExcludedOn (model9.B 0 ++ [step9.q]) 9000000000000 (model9.caps 0) (model9.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6420000000000], [1590000000000, -9000000000000])
      (some (1, 3, 1)) (some (2, 3, 1)) (.next ([7410000000000, 9000000000000], [2580000000000])
      (some (2, 3, 1)) (some (2, 3, 1)) (.next ([6420000000000], [2580000000000]) (some (2, 3, 1))
      (some (2, 3, 1)) (.next ([990000000000, 9000000000000], [990000000000, 9000000000000]) (some
      (2, 3, 1)) (some (3, 3, 1)) (.next ([0], [990000000000, 9000000000000]) (some (3, 3, 1)) (some
      (3, 3, 1)) (.next ([-1590000000000, 9000000000000], [8010000000000, -9000000000000]) (some (3,
      3, 1)) (some (3, 3, 1)) (.next ([-2580000000000, 0], [9990000000000, 9000000000000]) (some (3,
      0, 1)) (some (3, 0, 1)) (.next ([-2580000000000], [9000000000000]) (some (3, 0, 1)) (some (3,
      0, 1)) (.next ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (3, 0,
      1)) (some (3, 0, 1)) (.terminal (some (3, 0, 1)) (some (3, 1, 1)) (some (3, 1, 1)))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_9 : ExcludedOn (model9.B 9 ++ [step9.q]) 9000000000000 (model9.caps 9) (model9.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked9 : StepValid model9 9000000000000 step9 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded9_0
    · exact excluded9_1
    · exact excluded9_2
    · exact excluded9_3
    · exact excluded9_4
    · exact excluded9_5
    · exact excluded9_6
    · exact excluded9_7
    · exact (hj rfl).elim
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_0 : ExcludedOn (model10.B 0 ++ [step10.q]) 9000000000000 (model10.caps 0)
    (model10.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7080000000000], [795000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([990000000000, 9000000000000], [1590000000000, -9000000000000]) (some
      (0, 1, 3)) (some (0, 1, 3)) (.next ([1785000000000, 0], [6885000000000, -9000000000000]) (some
      (0, 1, 3)) (some (0, 1, 3)) (.next ([1785000000000], [7875000000000]) (some (0, 1, 3)) (some
      (0, 1, 3)) (.next ([0], [2580000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-795000000000], [7875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1590000000000,
      9000000000000], [2580000000000]) (some (0, 1, 3)) (some (0, 3, 3)) (.next ([-6885000000000,
      9000000000000], [8670000000000, -9000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next
      ([-7875000000000], [9660000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some (0, 3,
      2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_9 : ExcludedOn (model10.B 9 ++ [step10.q]) 9000000000000 (model10.caps 9)
    (model10.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked10 : StepValid model10 9000000000000 step10 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded10_0
    · exact excluded10_1
    · exact excluded10_2
    · exact (hj rfl).elim
    · exact excluded10_4
    · exact excluded10_5
    · exact excluded10_6
    · exact excluded10_7
    · exact excluded10_8
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_0 : ExcludedOn (model11.B 0 ++ [step11.q]) 9000000000000 (model11.caps 0)
    (model11.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8208000000000, 9000000000000], [1260000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([7218000000000], [2250000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([6228000000000, -9000000000000], [2250000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([990000000000, 9000000000000], [990000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (3, 3, 1)) (some (3, 3, 1)) (.next ([-1260000000000, 9000000000000],
      [9468000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-2250000000000],
      [9468000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2250000000000, 0],
      [8478000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-990000000000,
      -9000000000000], [1980000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal
      (some (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_4 : ExcludedOn (model11.B 4 ++ [step11.q]) 9000000000000 (model11.caps 4)
    (model11.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_8 : ExcludedOn (model11.B 8 ++ [step11.q]) 9000000000000 (model11.caps 8)
    (model11.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_9 : ExcludedOn (model11.B 9 ++ [step11.q]) 9000000000000 (model11.caps 9)
    (model11.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked11 : StepValid model11 9000000000000 step11 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded11_0
    · exact excluded11_1
    · exact excluded11_2
    · exact (hj rfl).elim
    · exact excluded11_4
    · exact excluded11_5
    · exact excluded11_6
    · exact excluded11_7
    · exact excluded11_8
    · exact excluded11_9
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_0 : ExcludedOn (model12.B 0 ++ [step12.q]) 9000000000000 (model12.caps 0)
    (model12.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_3 : ExcludedOn (model12.B 3 ++ [step12.q]) 9000000000000 (model12.caps 3)
    (model12.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5472000000000], [2028000000000]) (some (3, 5,
      5)) (some (4, 5, 5)) (.next ([6930000000000, 9000000000000], [2820000000000, -9000000000000])
      (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1260000000000, -9000000000000], [522000000000,
      9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1125000000000], [660000000000])
      (some (4, 5, 2)) (some (4, 5, 3)) (.next ([5940000000000], [3810000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([4815000000000], [3150000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([4950000000000, -9000000000000], [3810000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([990000000000, 9000000000000], [990000000000, 9000000000000]) (some (4, 5, 3)) (some
      (4, 5, 3)) (.next ([465000000000], [657000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([468000000000], [1782000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([330000000000,
      9000000000000], [1785000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [990000000000,
      9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-2028000000000], [7500000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2820000000000, 9000000000000], [9750000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-522000000000, -9000000000000], [1782000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-660000000000], [1785000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-3810000000000], [9750000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-3150000000000], [7965000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-3810000000000], [8760000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (0, 5, 3)) (some (5,
      5, 3)) (.next ([-657000000000], [1122000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-1782000000000], [2250000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-1785000000000,
      0], [2115000000000, 9000000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.terminal (some (5, 5,
      3)) (some (5, 5, 3)) (some (5, 5, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_8 : ExcludedOn (model12.B 8 ++ [step12.q]) 9000000000000 (model12.caps 8)
    (model12.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_9 : ExcludedOn (model12.B 9 ++ [step12.q]) 9000000000000 (model12.caps 9)
    (model12.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked12 : StepValid model12 9000000000000 step12 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded12_0
    · exact excluded12_1
    · exact excluded12_2
    · exact excluded12_3
    · exact (hj rfl).elim
    · exact excluded12_5
    · exact excluded12_6
    · exact excluded12_7
    · exact excluded12_8
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_0 : ExcludedOn (model13.B 0 ++ [step13.q]) 9000000000000 (model13.caps 0)
    (model13.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5334600000000, -2640000000000], [250800000000,
      5280000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([4584600000000, -2640000000000],
      [699600000000, -2640000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([5165400000000,
      2640000000000], [1280400000000, 2640000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
      ([4875000000000], [1458000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([4584600000000,
      -2640000000000], [1570800000000, 5280000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
      ([450000000000], [300000000000]) (some (8, 9, 5)) (some (9, 9, 5)) (.next ([5010000000000],
      [4875000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next ([290400000000, 2640000000000],
      [290400000000, 2640000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([4950000000000],
      [5175000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([4500000000000], [4875000000000])
      (some (9, 3, 5)) (some (9, 3, 5)) (.next ([4635000000000], [5535000000000]) (some (9, 3, 5))
      (some (9, 3, 5)) (.next ([285000000000], [375000000000]) (some (9, 3, 5)) (some (9, 3, 5))
      (.next ([290400000000, 2640000000000], [758400000000, 2640000000000]) (some (9, 3, 5)) (some
      (9, 3, 5)) (.next ([1570800000000, 5280000000000], [4209600000000, -2640000000000]) (some (9,
      3, 5)) (some (9, 3, 5)) (.next ([1570800000000, 5280000000000], [4719600000000,
      -2640000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1458000000000], [4500000000000])
      (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1458000000000], [5010000000000]) (some (9, 3, 5))
      (some (9, 3, 5)) (.next ([1280400000000, 2640000000000], [4790400000000, 2640000000000]) (some
      (9, 3, 5)) (some (9, 3, 5)) (.next ([1270800000000, 5280000000000], [4959600000000,
      -2640000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1280400000000, 2640000000000],
      [5300400000000, 2640000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1158000000000],
      [5250000000000]) (some (9, 3, 5)) (some (9, 3, 5)) fan13Owner0Part1)))))))))))))))))))))) (den
      :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_3 : ExcludedOn (model13.B 3 ++ [step13.q]) 9000000000000 (model13.caps 3)
    (model13.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5397000000000], [2343000000000]) (some (3, 5,
      5)) (some (4, 5, 5)) (.next ([6855000000000, 9000000000000], [3135000000000, -9000000000000])
      (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1458000000000, 9000000000000], [792000000000,
      -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1125000000000], [660000000000])
      (some (4, 5, 2)) (some (4, 5, 3)) (.next ([5865000000000], [4125000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([4740000000000], [3465000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([4875000000000, -9000000000000], [4125000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([990000000000, 9000000000000], [990000000000, 9000000000000]) (some (4, 5, 3)) (some
      (4, 5, 3)) (.next ([465000000000], [657000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([468000000000], [1782000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([330000000000,
      9000000000000], [1785000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [990000000000,
      9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-2343000000000], [7740000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3135000000000, 9000000000000], [9990000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-792000000000, 9000000000000], [2250000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-660000000000], [1785000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-4125000000000], [9990000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-3465000000000], [8205000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-4125000000000], [9000000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (0, 5, 3)) (some (5,
      5, 3)) (.next ([-657000000000], [1122000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-1782000000000], [2250000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-1785000000000,
      0], [2115000000000, 9000000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.terminal (some (5, 5,
      3)) (some (5, 5, 3)) (some (5, 5, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_6 : ExcludedOn (model13.B 6 ++ [step13.q]) 9000000000000 (model13.caps 6)
    (model13.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_7 : ExcludedOn (model13.B 7 ++ [step13.q]) 9000000000000 (model13.caps 7)
    (model13.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_8 : ExcludedOn (model13.B 8 ++ [step13.q]) 9000000000000 (model13.caps 8)
    (model13.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_9 : ExcludedOn (model13.B 9 ++ [step13.q]) 9000000000000 (model13.caps 9)
    (model13.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked13 : StepValid model13 9000000000000 step13 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded13_0
    · exact excluded13_1
    · exact excluded13_2
    · exact excluded13_3
    · exact (hj rfl).elim
    · exact excluded13_5
    · exact excluded13_6
    · exact excluded13_7
    · exact excluded13_8
    · exact excluded13_9
theorem next13 : model13.insert step13 = model14 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded14_0 : ExcludedOn (model14.B 0 ++ [step14.q]) 9000000000000 (model14.caps 0)
    (model14.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8250000000000], [60000000000]) (some (8, 9, 5))
      (some (8, 9, 5)) (.next ([8295000000000], [375000000000]) (some (8, 9, 5)) (some (8, 9, 5))
      (.next ([5334600000000, -2640000000000], [250800000000, 5280000000000]) (some (8, 9, 5)) (some
      (8, 9, 5)) (.next ([7500000000000], [510000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
      ([240000000000], [60000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([450000000000],
      [300000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([290400000000, 2640000000000],
      [290400000000, 2640000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([285000000000],
      [375000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([3290400000000, 2640000000000],
      [6290400000000, 2640000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([2709600000000,
      -2640000000000], [5709600000000, -2640000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next
      ([3000000000000], [6468000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([2709600000000,
      -2640000000000], [6580800000000, 5280000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next
      ([290400000000, 2640000000000], [758400000000, 2640000000000]) (some (0, 9, 5)) (some (0, 9,
      5)) (.next ([1570800000000, 5280000000000], [4209600000000, -2640000000000]) (some (0, 9, 5))
      (some (0, 9, 5)) (.next ([1570800000000, 5280000000000], [4719600000000, -2640000000000])
      (some (0, 9, 5)) (some (9, 9, 5)) (.next ([1458000000000], [4500000000000]) (some (9, 9, 5))
      (some (9, 9, 5)) (.next ([1458000000000], [5010000000000]) (some (9, 9, 5)) (some (9, 9, 5))
      (.next ([1280400000000, 2640000000000], [4790400000000, 2640000000000]) (some (9, 9, 5)) (some
      (9, 9, 5)) (.next ([1270800000000, 5280000000000], [4959600000000, -2640000000000]) (some (9,
      9, 5)) (some (9, 9, 5)) (.next ([1280400000000, 2640000000000], [5300400000000,
      2640000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next ([1158000000000], [5250000000000])
      (some (9, 9, 5)) (some (9, 9, 5)) fan14Owner0Part1)))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_3 : ExcludedOn (model14.B 3 ++ [step14.q]) 9000000000000 (model14.caps 3)
    (model14.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_7 : ExcludedOn (model14.B 7 ++ [step14.q]) 9000000000000 (model14.caps 7)
    (model14.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_8 : ExcludedOn (model14.B 8 ++ [step14.q]) 9000000000000 (model14.caps 8)
    (model14.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_9 : ExcludedOn (model14.B 9 ++ [step14.q]) 9000000000000 (model14.caps 9)
    (model14.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked14 : StepValid model14 9000000000000 step14 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded14_0
    · exact excluded14_1
    · exact excluded14_2
    · exact excluded14_3
    · exact (hj rfl).elim
    · exact excluded14_5
    · exact excluded14_6
    · exact excluded14_7
    · exact excluded14_8
    · exact excluded14_9
theorem next14 : model14.insert step14 = model15 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded15_0 : ExcludedOn (model15.B 0 ++ [step15.q]) 9000000000000 (model15.caps 0)
    (model15.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_1 : ExcludedOn (model15.B 1 ++ [step15.q]) 9000000000000 (model15.caps 1)
    (model15.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_2 : ExcludedOn (model15.B 2 ++ [step15.q]) 9000000000000 (model15.caps 2)
    (model15.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_3 : ExcludedOn (model15.B 3 ++ [step15.q]) 9000000000000 (model15.caps 3)
    (model15.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1260000000000, -9000000000000], [522000000000,
      9000000000000]) (some (3, 5, 2)) (some (5, 5, 2)) (.next ([1125000000000], [660000000000])
      (some (5, 5, 2)) (some (5, 5, 3)) (.next ([990000000000, 9000000000000], [990000000000,
      9000000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([465000000000], [657000000000])
      (some (5, 5, 3)) (some (5, 5, 3)) (.next ([2250000000000], [6750000000000]) (some (5, 5, 3))
      (some (5, 5, 3)) (.next ([1785000000000], [6093000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([468000000000], [1782000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([330000000000, 9000000000000], [1785000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([990000000000, 9000000000000], [6228000000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2,
      3)) (.next ([0], [990000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-522000000000, -9000000000000], [1782000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-660000000000], [1785000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-990000000000,
      -9000000000000], [1980000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-657000000000], [1122000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-6750000000000],
      [9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-6093000000000], [7878000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1782000000000], [2250000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([-1785000000000, 0], [2115000000000, 9000000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([-6228000000000, 9000000000000], [7218000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 2, 3)) (some (5, 2,
      3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_5 : ExcludedOn (model15.B 5 ++ [step15.q]) 9000000000000 (model15.caps 5)
    (model15.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_7 : ExcludedOn (model15.B 7 ++ [step15.q]) 9000000000000 (model15.caps 7)
    (model15.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_9 : ExcludedOn (model15.B 9 ++ [step15.q]) 9000000000000 (model15.caps 9)
    (model15.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked15 : StepValid model15 9000000000000 step15 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded15_0
    · exact excluded15_1
    · exact excluded15_2
    · exact excluded15_3
    · exact excluded15_4
    · exact excluded15_5
    · exact excluded15_6
    · exact excluded15_7
    · exact (hj rfl).elim
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext110000120000
end ConwaySoifer.Simplified.Certificates
