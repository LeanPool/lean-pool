/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown135000140000
import Mathlib.Tactic.FinCases

/-!
# Aown 135000 140000 1

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
namespace Aown135000140000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan9Owner0Part0 : FanWitness := (.next ([-288300000000, -2580000000000], [1446600000000,
    5160000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-687000000000], [2599500000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2276700000000, 2580000000000], [7833300000000,
    2580000000000]) (some (0, 3, 6)) (some (0, 3, 7)) (.next ([-2689200000000, 2580000000000],
    [7848300000000, 2580000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-2973300000000,
    -2580000000000], [8181600000000, 5160000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-3385800000000, -2580000000000], [8196600000000, 5160000000000]) (some (0, 3, 7)) (some (0, 3,
    7)) (.next ([-3321600000000, -5160000000000], [7833300000000, 2580000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.next ([-3435000000000], [7545000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-3734100000000, -5160000000000], [7848300000000, 2580000000000]) (some (0, 3, 7)) (some
    (0, 3, 7)) (.next ([-348300000000, -2580000000000], [696600000000, 5160000000000]) (some (0, 3,
    7)) (some (0, 3, 7)) (.next ([-3847500000000], [7560000000000]) (some (0, 3, 7)) (some (1, 3,
    7)) (.next ([-4114200000000, 2580000000000], [7848300000000, 2580000000000]) (some (1, 3, 7))
    (some (1, 3, 7)) (.next ([-4810800000000, -2580000000000], [8196600000000, 5160000000000]) (some
    (1, 3, 7)) (some (1, 3, 7)) (.next ([-5159100000000, -5160000000000], [7848300000000,
    2580000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-5272500000000], [7560000000000])
    (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-288300000000, -2580000000000], [401700000000,
    -2580000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-6026700000000, 2580000000000],
    [7161300000000, 2580000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-6723300000000,
    -2580000000000], [7509600000000, 5160000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next
    ([-2145000000000], [2250000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-2542500000000],
    [2662500000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-397500000000], [412500000000])
    (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-3967500000000], [4087500000000]) (some (1, 3, 7))
    (some (1, 3, 7)) (.next ([-7071600000000, -5160000000000], [7161300000000, 2580000000000]) (some
    (1, 3, 7)) (some (1, 3, 7)) (.next ([-1822500000000], [1837500000000]) (some (1, 3, 7)) (some
    (1, 3, 7)) (.terminal (some (1, 3, 7)) (some (1, 3, 7)) (some (1, 3,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan9Owner0Part1 : FanWitness := (.next ([348300000000, 2580000000000], [348300000000,
    2580000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([3712500000000], [3847500000000])
    (some (7, 1, 3)) (some (7, 2, 3)) (.next ([3734100000000, 5160000000000], [4114200000000,
    -2580000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([3385800000000, 2580000000000],
    [4810800000000, 2580000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([2689200000000,
    -2580000000000], [5159100000000, 5160000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next
    ([2287500000000], [5272500000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([113400000000,
    -5160000000000], [288300000000, 2580000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next
    ([1134600000000, 5160000000000], [6026700000000, -2580000000000]) (some (7, 2, 3)) (some (7, 8,
    3)) (.next ([786300000000, 2580000000000], [6723300000000, 2580000000000]) (some (0, 8, 3))
    (some (0, 8, 3)) (.next ([105000000000], [2145000000000]) (some (0, 8, 3)) (some (0, 8, 3))
    (.next ([120000000000], [2542500000000]) (some (0, 8, 3)) (some (0, 8, 4)) (.next
    ([15000000000], [397500000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([120000000000],
    [3967500000000]) (some (0, 8, 4)) (some (0, 8, 5)) (.next ([89700000000, -2580000000000],
    [7071600000000, 5160000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([15000000000],
    [1822500000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([0, 0], [1044900000000,
    7740000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([-26700000000, 2580000000000],
    [7728300000000, 2580000000000]) (some (0, 8, 5)) (some (0, 8, 6)) (.next ([-312000000000],
    [7185000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-567000000000], [6567000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-723300000000, -2580000000000], [8076600000000,
    5160000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1071600000000, -5160000000000],
    [7728300000000, 2580000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-672000000000],
    [4422000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1185000000000], [7440000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-687000000000], [4024500000000]) (some (0, 3, 6))
    (some (0, 3, 6)) fan9Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan10Owner0Part0 : FanWitness := (.next ([-687000000000], [2599500000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-2276700000000, 2580000000000], [7833300000000, 2580000000000]) (some
    (0, 3, 6)) (some (0, 3, 7)) (.next ([-2689200000000, 2580000000000], [7848300000000,
    2580000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-2973300000000, -2580000000000],
    [8181600000000, 5160000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-2649000000000],
    [7275000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-3385800000000, -2580000000000],
    [8196600000000, 5160000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-3321600000000,
    -5160000000000], [7833300000000, 2580000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-3734100000000, -5160000000000], [7848300000000, 2580000000000]) (some (0, 3, 7)) (some (0, 3,
    7)) (.next ([-348300000000, -2580000000000], [696600000000, 5160000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.next ([-4114200000000, 2580000000000], [7848300000000, 2580000000000]) (some
    (0, 3, 7)) (some (1, 3, 7)) (.next ([-4810800000000, -2580000000000], [8196600000000,
    5160000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-5159100000000, -5160000000000],
    [7848300000000, 2580000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-3525000000000],
    [5298000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-2535300000000, -2580000000000],
    [3783600000000, 5160000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-3937500000000],
    [5313000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-6026700000000, 2580000000000],
    [7161300000000, 2580000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-6723300000000,
    -2580000000000], [7509600000000, 5160000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next
    ([-2535300000000, -2580000000000], [2738700000000, -2580000000000]) (some (1, 3, 7)) (some (1,
    3, 7)) (.next ([-2145000000000], [2250000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next
    ([-2542500000000], [2662500000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-397500000000],
    [412500000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-3967500000000], [4087500000000])
    (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-7071600000000, -5160000000000], [7161300000000,
    2580000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-1822500000000], [1837500000000])
    (some (1, 3, 7)) (some (1, 3, 7)) (.terminal (some (1, 3, 7)) (some (1, 3, 7)) (some (1, 3,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan10Owner0Part1 : FanWitness := (.next ([3734100000000, 5160000000000], [4114200000000,
    -2580000000000]) (some (7, 1, 3)) (some (7, 2, 3)) (.next ([3385800000000, 2580000000000],
    [4810800000000, 2580000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([2689200000000,
    -2580000000000], [5159100000000, 5160000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next
    ([1773000000000], [3525000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([1248300000000,
    2580000000000], [2535300000000, 2580000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next
    ([1375500000000], [3937500000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([1134600000000,
    5160000000000], [6026700000000, -2580000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next
    ([786300000000, 2580000000000], [6723300000000, 2580000000000]) (some (0, 2, 3)) (some (0, 2,
    3)) (.next ([203400000000, -5160000000000], [2535300000000, 2580000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([105000000000], [2145000000000]) (some (0, 2, 3)) (some (0, 8, 3))
    (.next ([120000000000], [2542500000000]) (some (0, 8, 3)) (some (0, 8, 4)) (.next
    ([15000000000], [397500000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next ([120000000000],
    [3967500000000]) (some (0, 8, 4)) (some (0, 8, 5)) (.next ([89700000000, -2580000000000],
    [7071600000000, 5160000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([15000000000],
    [1822500000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([0, 0], [1044900000000,
    7740000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([-26700000000, 2580000000000],
    [7728300000000, 2580000000000]) (some (0, 8, 5)) (some (0, 8, 6)) (.next ([-49500000000],
    [5362500000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-567000000000], [6567000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-723300000000, -2580000000000], [8076600000000,
    5160000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1071600000000, -5160000000000],
    [7728300000000, 2580000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-672000000000],
    [4422000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-687000000000], [4024500000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1275000000000], [5193000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) fan10Owner0Part0))))))))))))))))))))))))

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1590000000000, 9000000000000], [405000000000,
      -9000000000000]) none none (.next ([1215000000000, 9000000000000], [1215000000000,
      9000000000000]) none none (.next ([780000000000, -9000000000000], [840000000000,
      9000000000000]) none none (.next ([1995000000000], [4290000000000]) none none (.next
      ([1215000000000, 9000000000000], [3450000000000, -9000000000000]) none none (.next ([0],
      [5880000000000, 9000000000000]) none none (.next ([-405000000000, 9000000000000],
      [1995000000000]) none none (.next ([-1215000000000, -9000000000000], [2430000000000,
      18000000000000]) none none (.next ([-840000000000, -9000000000000], [1620000000000, 0]) none
      none (.next ([-4290000000000], [6285000000000]) none none (.next ([-3450000000000,
      9000000000000], [4665000000000, 0]) none none (.terminal none none none))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8160750000000, 0], [607500000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7785000000000, -9000000000000],
      [1215000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2535000000000, 0],
      [1215000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([548250000000],
      [464250000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([780000000000, -9000000000000],
      [840000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([231750000000,
      -9000000000000], [375750000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next
      ([1620000000000], [4470000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1620000000000],
      [7005000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([607500000000], [5018250000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([607500000000], [7553250000000]) (some (0, 4, 1))
      (some (0, 4, 2)) (.next ([405000000000, -9000000000000], [8220000000000, 9000000000000]) (some
      (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0], [1215000000000, 9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-607500000000, -9000000000000], [8768250000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1215000000000, -9000000000000], [9000000000000,
      0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1215000000000, -9000000000000],
      [3750000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-464250000000],
      [1012500000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-840000000000, -9000000000000],
      [1620000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-375750000000, -9000000000000],
      [607500000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4470000000000],
      [6090000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-7005000000000], [8625000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5018250000000], [5625750000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-7553250000000], [8160750000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-8220000000000, -9000000000000], [8625000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.terminal (some (0, 1, 3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded8_4 : ExcludedOn (model8.B 4 ++ [step8.q]) 9000000000000 (model8.caps 4) (model8.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded8_8 : ExcludedOn (model8.B 8 ++ [step8.q]) 9000000000000 (model8.caps 8) (model8.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded8_9 : ExcludedOn (model8.B 9 ++ [step8.q]) 9000000000000 (model8.caps 9) (model8.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked8 : StepValid model8 9000000000000 step8 0 1 200 := by
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
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7701600000000, 5160000000000], [26700000000,
      -2580000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([6873000000000], [312000000000])
      (some (7, 1, 3)) (some (7, 1, 3)) (.next ([6000000000000], [567000000000]) (some (7, 1, 3))
      (some (7, 1, 3)) (.next ([7353300000000, 2580000000000], [723300000000, 2580000000000]) (some
      (7, 1, 3)) (some (7, 1, 3)) (.next ([6656700000000, -2580000000000], [1071600000000,
      5160000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([3750000000000], [672000000000])
      (some (7, 1, 3)) (some (7, 1, 3)) (.next ([6255000000000], [1185000000000]) (some (7, 1, 3))
      (some (7, 1, 3)) (.next ([3337500000000], [687000000000]) (some (7, 1, 3)) (some (7, 1, 3))
      (.next ([1158300000000, 2580000000000], [288300000000, 2580000000000]) (some (7, 1, 3)) (some
      (7, 1, 3)) (.next ([1912500000000], [687000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
      ([5556600000000, 5160000000000], [2276700000000, -2580000000000]) (some (7, 1, 3)) (some (7,
      1, 3)) (.next ([5159100000000, 5160000000000], [2689200000000, -2580000000000]) (some (7, 1,
      3)) (some (7, 1, 3)) (.next ([5208300000000, 2580000000000], [2973300000000, 2580000000000])
      (some (7, 1, 3)) (some (7, 1, 3)) (.next ([4810800000000, 2580000000000], [3385800000000,
      2580000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([4511700000000, -2580000000000],
      [3321600000000, 5160000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([4110000000000],
      [3435000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([4114200000000, -2580000000000],
      [3734100000000, 5160000000000]) (some (7, 1, 3)) (some (7, 1, 3))
      fan9Owner0Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7725000000000, -9000000000000], [465000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([1215000000000, 9000000000000],
      [1215000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([1965000000000,
      9000000000000], [6975000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next
      ([750000000000], [8190000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [1215000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-465000000000,
      -9000000000000], [8190000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-1215000000000,
      -9000000000000], [2430000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-6975000000000, 9000000000000], [8940000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8190000000000], [8940000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded9_8 : ExcludedOn (model9.B 8 ++ [step9.q]) 9000000000000 (model9.caps 8) (model9.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded9_9 : ExcludedOn (model9.B 9 ++ [step9.q]) 9000000000000 (model9.caps 9) (model9.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked9 : StepValid model9 9000000000000 step9 0 1 200 := by
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
    · exact (hj rfl).elim
    · exact excluded9_7
    · exact excluded9_8
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_0 : ExcludedOn (model10.B 0 ++ [step10.q]) 9000000000000 (model10.caps 0)
    (model10.ord 0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7701600000000, 5160000000000], [26700000000,
      -2580000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([5313000000000], [49500000000])
      (some (7, 1, 3)) (some (7, 1, 3)) (.next ([6000000000000], [567000000000]) (some (7, 1, 3))
      (some (7, 1, 3)) (.next ([7353300000000, 2580000000000], [723300000000, 2580000000000]) (some
      (7, 1, 3)) (some (7, 1, 3)) (.next ([6656700000000, -2580000000000], [1071600000000,
      5160000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([3750000000000], [672000000000])
      (some (7, 1, 3)) (some (7, 1, 3)) (.next ([3337500000000], [687000000000]) (some (7, 1, 3))
      (some (7, 1, 3)) (.next ([3918000000000], [1275000000000]) (some (7, 1, 3)) (some (7, 1, 3))
      (.next ([1912500000000], [687000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
      ([5556600000000, 5160000000000], [2276700000000, -2580000000000]) (some (7, 1, 3)) (some (7,
      1, 3)) (.next ([5159100000000, 5160000000000], [2689200000000, -2580000000000]) (some (7, 1,
      3)) (some (7, 1, 3)) (.next ([5208300000000, 2580000000000], [2973300000000, 2580000000000])
      (some (7, 1, 3)) (some (7, 1, 3)) (.next ([4626000000000], [2649000000000]) (some (7, 1, 3))
      (some (7, 1, 3)) (.next ([4810800000000, 2580000000000], [3385800000000, 2580000000000]) (some
      (7, 1, 3)) (some (7, 1, 3)) (.next ([4511700000000, -2580000000000], [3321600000000,
      5160000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([4114200000000, -2580000000000],
      [3734100000000, 5160000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([348300000000,
      2580000000000], [348300000000, 2580000000000]) (some (7, 1, 3)) (some (7, 1, 3))
      fan10Owner0Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8160750000000, 0], [607500000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6813000000000], [552000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7785000000000, -9000000000000], [1215000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([4466250000000], [1739250000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6813000000000], [3087000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([2535000000000, 0], [1215000000000, 9000000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([5598000000000, -9000000000000], [4302000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([231750000000, -9000000000000], [375750000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([607500000000], [5018250000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([607500000000], [7553250000000]) (some (0, 4, 1))
      (some (0, 4, 2)) (.next ([0, 0], [1215000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([-607500000000, -9000000000000], [8768250000000, 9000000000000]) (some (0, 4, 2))
      (some (0, 4, 3)) (.next ([-552000000000], [7365000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-1215000000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 3)) (some (0, 4,
      3)) (.next ([-1739250000000], [6205500000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3087000000000], [9900000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1215000000000,
      -9000000000000], [3750000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-4302000000000, -9000000000000], [9900000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-375750000000, -9000000000000], [607500000000, 0]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-5018250000000], [5625750000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-7553250000000], [8160750000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded10_9 : ExcludedOn (model10.B 9 ++ [step10.q]) 9000000000000 (model10.caps 9)
    (model10.ord 9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked10 : StepValid model10 9000000000000 step10 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded10_0
    · exact excluded10_1
    · exact excluded10_2
    · exact excluded10_3
    · exact excluded10_4
    · exact excluded10_5
    · exact (hj rfl).elim
    · exact excluded10_7
    · exact excluded10_8
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown135000140000
end ConwaySoifer.Simplified.Certificates
