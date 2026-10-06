/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown310000320000
import Mathlib.Tactic.FinCases

/-!
# Aown 310000 320000 1

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
namespace Aown310000320000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan8Owner0Part0 : FanWitness := (.next ([-330000000000], [1725000000000]) (some (0, 10, 10))
    (some (0, 10, 10)) (.next ([-447600000000, 2040000000000], [1712400000000, 2040000000000]) (some
    (0, 10, 10)) (some (0, 10, 10)) (.next ([-632400000000, -2040000000000], [2344800000000,
    4080000000000]) (some (0, 10, 10)) (some (0, 10, 10)) (.next ([-184800000000, -4080000000000],
    [632400000000, 2040000000000]) (some (0, 10, 10)) (some (0, 10, 10)) (.next ([-514800000000,
    -4080000000000], [1277400000000, 2040000000000]) (some (0, 10, 10)) (some (0, 10, 10)) (.next
    ([-619800000000, -4080000000000], [1382400000000, 2040000000000]) (some (0, 10, 10)) (some (0,
    10, 10)) (.next ([-1277400000000, -2040000000000], [2659800000000, 4080000000000]) (some (0, 10,
    10)) (some (0, 10, 10)) (.next ([-315000000000], [645000000000]) (some (0, 10, 10)) (some (0,
    10, 10)) (.next ([-645000000000], [1290000000000]) (some (0, 10, 10)) (some (1, 10, 10)) (.next
    ([-330000000000], [645000000000]) (some (1, 10, 10)) (some (1, 10, 7)) (.next ([-1382400000000,
    -2040000000000], [2659800000000, 4080000000000]) (some (1, 10, 7)) (some (2, 10, 7)) (.next
    ([-762600000000, 2040000000000], [1382400000000, 2040000000000]) (some (2, 10, 7)) (some (2, 10,
    7)) (.next ([-435000000000], [750000000000]) (some (2, 10, 7)) (some (2, 10, 7)) (.next
    ([-5925000000000], [10020000000000]) (some (2, 10, 7)) (some (2, 10, 7)) (.next
    ([-6030000000000], [10020000000000]) (some (2, 10, 7)) (some (2, 10, 7)) (.next
    ([-4647600000000, 2040000000000], [7360200000000, -4080000000000]) (some (2, 10, 7)) (some (2,
    10, 7)) (.next ([-6360000000000], [9705000000000]) (some (2, 10, 7)) (some (2, 10, 7)) (.next
    ([-6675000000000], [9375000000000]) (some (2, 10, 7)) (some (2, 10, 7)) (.next ([-1712400000000,
    -2040000000000], [2344800000000, 4080000000000]) (some (2, 10, 7)) (some (2, 10, 7)) (.next
    ([-6360000000000], [8625000000000]) (some (2, 10, 7)) (some (2, 10, 7)) (.next ([-5912400000000,
    -2040000000000], [7992600000000, -2040000000000]) (some (2, 10, 7)) (some (2, 10, 7)) (.next
    ([-1395000000000], [1830000000000]) (some (2, 10, 7)) (some (2, 10, 7)) (.next
    ([-1395000000000], [1725000000000]) (some (2, 10, 7)) (some (2, 10, 7)) (.next ([-1909800000000,
    -4080000000000], [2027400000000, 2040000000000]) (some (2, 10, 7)) (some (2, 10, 7)) (.terminal
    (some (2, 10, 7)) (some (2, 10, 7)) (some (2, 10, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan8Owner0Part1 : FanWitness := (.next ([1712400000000, 2040000000000], [632400000000,
    2040000000000]) (some (7, 2, 10)) (some (7, 2, 10)) (.next ([447600000000, -2040000000000],
    [184800000000, 4080000000000]) (some (7, 2, 10)) (some (7, 2, 10)) (.next ([762600000000,
    -2040000000000], [514800000000, 4080000000000]) (some (7, 2, 10)) (some (8, 2, 10)) (.next
    ([762600000000, -2040000000000], [619800000000, 4080000000000]) (some (8, 2, 10)) (some (8, 3,
    10)) (.next ([1382400000000, 2040000000000], [1277400000000, 2040000000000]) (some (8, 3, 10))
    (some (8, 3, 10)) (.next ([330000000000], [315000000000]) (some (8, 3, 10)) (some (8, 3, 10))
    (.next ([645000000000], [645000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
    ([315000000000], [330000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([1277400000000,
    2040000000000], [1382400000000, 2040000000000]) (some (8, 3, 10)) (some (9, 3, 10)) (.next
    ([619800000000, 4080000000000], [762600000000, -2040000000000]) (some (9, 3, 10)) (some (9, 3,
    10)) (.next ([315000000000], [435000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next
    ([4095000000000], [5925000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([3990000000000],
    [6030000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([2712600000000, -2040000000000],
    [4647600000000, -2040000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([3345000000000],
    [6360000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([2700000000000], [6675000000000])
    (some (9, 3, 10)) (some (9, 4, 10)) (.next ([632400000000, 2040000000000], [1712400000000,
    2040000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next ([2265000000000], [6360000000000])
    (some (9, 4, 10)) (some (9, 4, 10)) (.next ([2080200000000, -4080000000000], [5912400000000,
    2040000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next ([435000000000], [1395000000000])
    (some (9, 4, 10)) (some (9, 10, 10)) (.next ([330000000000], [1395000000000]) (some (9, 10, 10))
    (some (9, 10, 10)) (.next ([117600000000, -2040000000000], [1909800000000, 4080000000000]) (some
    (9, 10, 10)) (some (9, 10, 10)) (.next ([12600000000, -2040000000000], [2014800000000,
    4080000000000]) (some (9, 10, 10)) (some (9, 10, 10)) (.next ([-117600000000, 2040000000000],
    [2027400000000, 2040000000000]) (some (9, 10, 10)) (some (0, 10, 10))
    fan8Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner2Part0 : FanWitness := (.next ([210000000000], [45000000000]) (some (0, 4, 2)) (some
    (0, 4, 2)) (.next ([6255000000000, 0], [2160000000000, 9000000000000]) (some (0, 4, 2)) (some
    (0, 4, 2)) (.next ([6210000000000, 0], [2415000000000, 9000000000000]) (some (0, 4, 2)) (some
    (0, 4, 2)) (.next ([6210000000000, -9000000000000], [2790000000000, 9000000000000]) (some (0, 4,
    2)) (some (0, 4, 2)) (.next ([2232000000000, -9000000000000], [1143000000000, 9000000000000])
    (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3960000000000], [2295000000000]) (some (0, 4, 2))
    (some (0, 4, 2)) (.next ([1857000000000], [1143000000000]) (some (0, 4, 2)) (some (0, 4, 2))
    (.next ([1647000000000], [1098000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
    ([3705000000000], [2505000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3330000000000, 0],
    [2880000000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([585000000000,
    -9000000000000], [6768000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([0,
    0], [6120000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-648000000000],
    [7353000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-45000000000], [255000000000]) (some
    (0, 4, 3)) (some (0, 4, 3)) (.next ([-2160000000000, -9000000000000], [8415000000000,
    9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2415000000000, -9000000000000],
    [8625000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2790000000000,
    -9000000000000], [9000000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1143000000000,
    -9000000000000], [3375000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2295000000000],
    [6255000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1143000000000], [3000000000000])
    (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1098000000000], [2745000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([-2505000000000], [6210000000000]) (some (0, 2, 3)) (some (0, 2, 3))
    (.next ([-2880000000000, 9000000000000], [6210000000000, -9000000000000]) (some (0, 2, 3)) (some
    (0, 2, 3)) (.next ([-6768000000000, -9000000000000], [7353000000000]) (some (0, 2, 3)) (some (0,
    2, 3)) (.terminal (some (0, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner2Part0 : FanWitness := (.next ([6255000000000, 0], [2160000000000, 9000000000000])
    (some (0, 4, 2)) (some (0, 4, 2)) (.next ([6210000000000, 0], [2415000000000, 9000000000000])
    (some (0, 4, 2)) (some (0, 4, 2)) (.next ([6210000000000, -9000000000000], [2790000000000,
    9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3960000000000], [2295000000000])
    (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3705000000000], [2505000000000]) (some (0, 4, 2))
    (some (0, 4, 2)) (.next ([3330000000000, 0], [2880000000000, -9000000000000]) (some (0, 4, 2))
    (some (0, 4, 3)) (.next ([3177000000000], [3978000000000]) (some (0, 4, 3)) (some (0, 4, 3))
    (.next ([2277000000000], [3195000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
    ([2232000000000], [3450000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2232000000000,
    -9000000000000], [3825000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1035000000000,
    -9000000000000], [2943000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0,
    0], [6120000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0,
    -9000000000000], [375000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2160000000000,
    -9000000000000], [8415000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next
    ([-2415000000000, -9000000000000], [8625000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2,
    3)) (.next ([-2790000000000, -9000000000000], [9000000000000, 0]) (some (0, 2, 3)) (some (0, 2,
    3)) (.next ([-2295000000000], [6255000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-2505000000000], [6210000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2880000000000,
    9000000000000], [6210000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-3978000000000], [7155000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3195000000000],
    [5472000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3450000000000], [5682000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3825000000000, 0], [6057000000000, -9000000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2943000000000, -9000000000000], [3978000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2, 3)) (some (4, 2, 0)) (some (4, 2,
    3)))))))))))))))))))))))))))

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1909800000000, 4080000000000], [117600000000,
      -2040000000000]) (some (7, 2, 10)) (some (7, 2, 10)) (.next ([1395000000000], [330000000000])
      (some (7, 2, 10)) (some (7, 2, 10)) (.next ([1264800000000, 4080000000000], [447600000000,
      -2040000000000]) (some (7, 2, 10)) (some (7, 2, 10)) fan8Owner0Part1)))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2790000000000, 9000000000000], [1710000000000,
      -9000000000000]) none none (.next ([3720000000000, 0], [2415000000000, 9000000000000]) (some
      (0, 3, 2)) (some (0, 3, 2)) (.next ([2790000000000, 9000000000000], [2790000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([375000000000], [555000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([375000000000], [7845000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0], [7290000000000, 9000000000000]) (some (0, 3,
      2)) (some (0, 3, 2)) (.next ([-1710000000000, 9000000000000], [4500000000000, 0]) (some (0, 3,
      2)) (some (0, 3, 2)) (.next ([-2415000000000, -9000000000000], [6135000000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2790000000000, -9000000000000], [5580000000000,
      18000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-555000000000, 9000000000000],
      [930000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next ([-7845000000000],
      [8220000000000]) (some (3, 1, 2)) none (.terminal none none none))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded8_0
    · exact excluded8_1
    · exact excluded8_2
    · exact excluded8_3
    · exact excluded8_4
    · exact excluded8_5
    · exact (hj rfl).elim
    · exact excluded8_7
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_0 : ExcludedOn (model9.B 0 ++ [step9.q]) 9000000000000 (model9.caps 0) (model9.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2790000000000, 9000000000000], [1995000000000,
      -9000000000000]) (some (2, 0, 1)) (some (3, 0, 2)) (.next ([2790000000000, 9000000000000],
      [3420000000000, -18000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1425000000000,
      -9000000000000], [2790000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0,
      0], [6210000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([-1995000000000, 9000000000000], [4785000000000, 0]) (some (0, 0, 2)) (some (0, 0, 2)) (.next
      ([-3420000000000, 18000000000000], [6210000000000, -9000000000000]) (some (0, 0, 2)) (some (0,
      4, 2)) (.next ([-2790000000000, -9000000000000], [4215000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.terminal (some (0, 4, 2)) (some (0, 1, 2)) (some (0, 4, 2))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_8 : ExcludedOn (model9.B 8 ++ [step9.q]) 9000000000000 (model9.caps 8) (model9.ord
    8) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded9_2
    · exact excluded9_3
    · exact excluded9_4
    · exact excluded9_5
    · exact excluded9_6
    · exact excluded9_7
    · exact excluded9_8
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_0 : ExcludedOn (model10.B 0 ++ [step10.q]) 9000000000000 (model10.caps 0)
    (model10.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2790000000000, 9000000000000], [1995000000000,
      -9000000000000]) none none (.next ([2790000000000, 9000000000000], [2232000000000,
      -9000000000000]) none none (.next ([2790000000000, 9000000000000], [2790000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0], [7575000000000, 9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1995000000000, 9000000000000], [4785000000000, 0])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2232000000000, 9000000000000], [5022000000000, 0])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2790000000000, -9000000000000], [5580000000000,
      18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) none
      none))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded10_3
    · exact excluded10_4
    · exact excluded10_5
    · exact excluded10_6
    · exact (hj rfl).elim
    · exact excluded10_8
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_3 : ExcludedOn (model11.B 3 ++ [step11.q]) 9000000000000 (model11.caps 3)
    (model11.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_4 : ExcludedOn (model11.B 4 ++ [step11.q]) 9000000000000 (model11.caps 4)
    (model11.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5985000000000, -9000000000000], [765000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([4815000000000, 9000000000000],
      [3960000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([2790000000000,
      9000000000000], [2790000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([2025000000000], [6750000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [2790000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-765000000000,
      -9000000000000], [6750000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-3960000000000,
      9000000000000], [8775000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2790000000000,
      -9000000000000], [5580000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-6750000000000], [8775000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6750000000000], [225000000000]) (some (4, 0, 1))
      (some (4, 0, 2)) (.next ([5280000000000], [375000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([2490000000000, -9000000000000], [375000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([3960000000000, -9000000000000], [3015000000000, 9000000000000]) (some (4, 0, 2))
      (some (4, 0, 3)) (.next ([2790000000000, 9000000000000], [2790000000000, 9000000000000]) (some
      (4, 0, 3)) (some (4, 0, 3)) (.next ([2565000000000, 9000000000000], [4185000000000,
      -9000000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([2415000000000, 9000000000000],
      [5655000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([1095000000000], [5505000000000])
      (some (4, 0, 3)) (some (4, 0, 3)) (.next ([0, 0], [2790000000000, 9000000000000]) (some (4, 0,
      3)) (some (4, 0, 3)) (.next ([-225000000000], [6975000000000]) (some (4, 0, 3)) (some (4, 1,
      3)) (.next ([-375000000000], [5655000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-375000000000], [2865000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-3015000000000, -9000000000000], [6975000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-2790000000000, -9000000000000], [5580000000000, 18000000000000]) (some (4, 1, 3)) (some (4,
      1, 3)) (.next ([-4185000000000, 9000000000000], [6750000000000]) (some (4, 1, 3)) (some (4, 1,
      3)) (.next ([-5655000000000, 0], [8070000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-5505000000000], [6600000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal
      (some (0, 1, 3)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded11_1
    · exact excluded11_2
    · exact excluded11_3
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
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_3 : ExcludedOn (model12.B 3 ++ [step12.q]) 9000000000000 (model12.caps 3)
    (model12.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_4 : ExcludedOn (model12.B 4 ++ [step12.q]) 9000000000000 (model12.caps 4)
    (model12.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3978000000000], [1692000000000]) (some (2, 0,
      1)) (some (4, 0, 2)) (.next ([2790000000000, 9000000000000], [2232000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([3330000000000, 0], [2880000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([2790000000000, 9000000000000], [6210000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1188000000000, -9000000000000],
      [2790000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0],
      [6210000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-1692000000000],
      [5670000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2232000000000, 9000000000000],
      [5022000000000, 0]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2880000000000, 9000000000000],
      [6210000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-6210000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2790000000000,
      -9000000000000], [3978000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded12_3
    · exact excluded12_4
    · exact excluded12_5
    · exact excluded12_6
    · exact excluded12_7
    · exact excluded12_8
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4437000000000, 9000000000000], [585000000000,
      -9000000000000]) none none (.next ([2232000000000, -9000000000000], [1143000000000,
      9000000000000]) none none (.next ([5022000000000], [3138000000000]) none none (.next
      ([2790000000000, 9000000000000], [1995000000000, -9000000000000]) none none (.next
      ([2790000000000, 9000000000000], [2790000000000, 9000000000000]) none none (.next ([0],
      [7575000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-585000000000,
      9000000000000], [5022000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1143000000000,
      -9000000000000], [3375000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3138000000000], [8160000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1995000000000,
      9000000000000], [4785000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2790000000000,
      -9000000000000], [5580000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal
      (some (3, 1, 2)) none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6705000000000], [648000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) fan13Owner2Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_3 : ExcludedOn (model13.B 3 ++ [step13.q]) 9000000000000 (model13.caps 3)
    (model13.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_6 : ExcludedOn (model13.B 6 ++ [step13.q]) 9000000000000 (model13.caps 6)
    (model13.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_7 : ExcludedOn (model13.B 7 ++ [step13.q]) 9000000000000 (model13.caps 7)
    (model13.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded13_1
    · exact excluded13_2
    · exact excluded13_3
    · exact excluded13_4
    · exact excluded13_5
    · exact excluded13_6
    · exact excluded13_7
    · exact excluded13_8
    · exact excluded13_9
theorem next13 : model13.insert step13 = model14 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7812000000000, 9000000000000], [1035000000000,
      -9000000000000]) none none (.next ([2790000000000, 9000000000000], [1995000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2790000000000, 9000000000000],
      [2790000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2232000000000,
      -9000000000000], [3825000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([237000000000],
      [8610000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0], [7575000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1035000000000, 9000000000000],
      [8847000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1995000000000, 9000000000000],
      [4785000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2790000000000,
      -9000000000000], [5580000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3825000000000, 0], [6057000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-8610000000000], [8847000000000]) (some (3, 1, 2)) none (.terminal none none
      none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([375000000000, -9000000000000], [0,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) fan14Owner2Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_3 : ExcludedOn (model14.B 3 ++ [step14.q]) 9000000000000 (model14.caps 3)
    (model14.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3978000000000, 0], [2385000000000,
      -9000000000000]) (some (1, 0, 3)) (some (2, 0, 3)) (.next ([2790000000000, 9000000000000],
      [2790000000000, 9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([3978000000000],
      [5175000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([1188000000000, -9000000000000],
      [7965000000000, 9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([0], [2790000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 3, 3)) (.next ([-2385000000000, 9000000000000],
      [6363000000000, -9000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-2790000000000,
      -9000000000000], [5580000000000, 18000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-5175000000000], [9153000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-7965000000000,
      -9000000000000], [9153000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3,
      1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_7 : ExcludedOn (model14.B 7 ++ [step14.q]) 9000000000000 (model14.caps 7)
    (model14.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded14_1
    · exact excluded14_2
    · exact excluded14_3
    · exact excluded14_4
    · exact excluded14_5
    · exact excluded14_6
    · exact excluded14_7
    · exact excluded14_8
    · exact excluded14_9
theorem next14 : model14.insert step14 = model15 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown310000320000
end ConwaySoifer.Simplified.Certificates
