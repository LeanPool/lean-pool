/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext140000150000
import Mathlib.Tactic.FinCases

/-!
# Sext 140000 150000 1

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
namespace Sext140000150000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan8Owner0Part0 : FanWitness := (.next ([420000000000], [420000000000]) (some (5, 6, 2)) (some
    (6, 6, 2)) (.next ([687000000000, 2550000000000], [777000000000, 2550000000000]) (some (6, 6,
    2)) (some (6, 6, 2)) (.next ([750000000000], [930000000000]) (some (6, 6, 2)) (some (6, 6, 2))
    (.next ([330000000000], [420000000000]) (some (6, 6, 2)) (some (6, 6, 3)) (.next
    ([420000000000], [1590000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([330000000000],
    [1680000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([27000000000, 2550000000000],
    [1107000000000, 2550000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([0], [90000000000])
    (some (6, 6, 3)) (some (6, 6, 3)) (.next ([-63000000000, 2550000000000], [1107000000000,
    2550000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([-90000000000], [1170000000000]) (some
    (6, 6, 3)) (some (6, 6, 3)) (.next ([-420000000000], [2010000000000]) (some (6, 6, 3)) (some (6,
    6, 3)) (.next ([-2133000000000], [9000000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next
    ([-3036000000000, 2550000000000], [8286000000000, -5100000000000]) (some (6, 2, 3)) (some (6, 2,
    3)) (.next ([-3813000000000], [9750000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
    ([-3723000000000], [8580000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-4143000000000],
    [9420000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-4143000000000], [9330000000000])
    (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-420000000000], [840000000000]) (some (6, 2, 3))
    (some (6, 2, 3)) (.next ([-777000000000, -2550000000000], [1464000000000, 5100000000000]) (some
    (6, 2, 3)) (some (6, 2, 4)) (.next ([-930000000000], [1680000000000]) (some (6, 2, 4)) (some (6,
    2, 4)) (.next ([-420000000000], [750000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-1590000000000], [2010000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1680000000000],
    [2010000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1107000000000, -2550000000000],
    [1134000000000, 5100000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.terminal (some (6, 2, 4))
    (some (6, 2, 4)) (some (6, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part0 : FanWitness := (.next ([-960000000000], [5835000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-1380000000000], [6675000000000]) (some (8, 3, 5)) (some (8, 3, 5))
    (.next ([-1380000000000], [6585000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([-180000000000], [720000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-210000000000],
    [465000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-420000000000], [840000000000]) (some
    (8, 3, 5)) (some (8, 4, 5)) (.next ([-5160000000000], [9750000000000]) (some (8, 4, 5)) (some
    (8, 4, 6)) (.next ([-777000000000, -2550000000000], [1464000000000, 5100000000000]) (some (8, 4,
    6)) (some (8, 4, 6)) (.next ([-5415000000000], [10035000000000]) (some (8, 4, 6)) (some (8, 4,
    6)) (.next ([-420000000000], [750000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-5880000000000], [10290000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-3795000000000],
    [5640000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-4080000000000], [5670000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-4455000000000], [5970000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-4545000000000], [5970000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    (.next ([-4740000000000], [6000000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-4335000000000], [5460000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-4830000000000],
    [6000000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-4995000000000], [5790000000000])
    (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-5085000000000], [5790000000000]) (some (8, 4, 6))
    (some (8, 4, 6)) (.next ([-4875000000000], [5550000000000]) (some (8, 4, 6)) (some (8, 4, 6))
    (.next ([-255000000000], [285000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next
    ([-5160000000000], [5580000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.next ([-1107000000000,
    -2550000000000], [1134000000000, 5100000000000]) (some (8, 4, 6)) (some (8, 4, 6)) (.terminal
    (some (8, 4, 6)) (some (8, 4, 6)) (some (8, 4, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part1 : FanWitness := (.next ([420000000000], [420000000000]) (some (8, 8, 4)) (some
    (8, 8, 4)) (.next ([4590000000000], [5160000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next
    ([687000000000, 2550000000000], [777000000000, 2550000000000]) (some (8, 2, 4)) (some (8, 2, 4))
    (.next ([4620000000000], [5415000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([330000000000], [420000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([4410000000000],
    [5880000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1845000000000], [3795000000000])
    (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1590000000000], [4080000000000]) (some (8, 2, 4))
    (some (8, 2, 4)) (.next ([1515000000000], [4455000000000]) (some (8, 2, 4)) (some (8, 2, 4))
    (.next ([1425000000000], [4545000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([1260000000000], [4740000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1125000000000],
    [4335000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1170000000000], [4830000000000])
    (some (8, 2, 4)) (some (8, 2, 5)) (.next ([795000000000], [4995000000000]) (some (8, 2, 5))
    (some (8, 2, 5)) (.next ([705000000000], [5085000000000]) (some (8, 2, 5)) (some (8, 2, 5))
    (.next ([675000000000], [4875000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([30000000000], [255000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([420000000000],
    [5160000000000]) (some (8, 2, 5)) (some (8, 3, 5)) (.next ([27000000000, 2550000000000],
    [1107000000000, 2550000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([0], [90000000000])
    (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-45000000000], [5415000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-63000000000, 2550000000000], [1107000000000, 2550000000000]) (some
    (8, 3, 5)) (some (8, 3, 5)) (.next ([-339000000000, -5100000000000], [5022000000000,
    2550000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-1050000000000], [7005000000000])
    (some (8, 3, 5)) (some (8, 3, 5)) fan15Owner0Part0))))))))))))))))))))))))

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1044000000000, 5100000000000], [63000000000,
      -2550000000000]) (some (4, 6, 2)) (some (5, 6, 2)) (.next ([1080000000000], [90000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([1590000000000], [420000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([6867000000000], [2133000000000]) (some (5, 6, 2)) (some (5, 6, 2))
      (.next ([5250000000000, -2550000000000], [3036000000000, -2550000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([5937000000000], [3813000000000]) (some (5, 6, 2)) (some (5, 6, 2))
      (.next ([4857000000000], [3723000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([5277000000000], [4143000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([5187000000000],
      [4143000000000]) (some (5, 6, 2)) (some (5, 6, 2)) fan8Owner0Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded8_5
    · exact excluded8_6
    · exact excluded8_7
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [3960000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([1260000000000, 9000000000000], [1260000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([4875000000000], [5220000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3615000000000, -9000000000000], [6480000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-3960000000000, 9000000000000],
      [8835000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-1260000000000,
      -9000000000000], [2520000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-5220000000000], [10095000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-6480000000000, -9000000000000], [10095000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0))
      (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5385000000000, 9000000000000], [2520000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([4125000000000], [3780000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1173000000000], [2607000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([1260000000000, 9000000000000], [6732000000000, 0]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-2520000000000, 9000000000000], [7905000000000, 0]) (some (0, 1, 3)) (some (0, 2,
      3)) (.next ([-3780000000000], [7905000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-2607000000000], [3780000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-6732000000000,
      0], [7992000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3780000000000], [1095000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([4875000000000], [3960000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([1260000000000, 9000000000000], [7740000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([165000000000, 9000000000000], [3615000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1095000000000], [4875000000000])
      (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3960000000000, 9000000000000], [8835000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-7740000000000, 9000000000000],
      [9000000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3615000000000, 9000000000000],
      [3780000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_8 : ExcludedOn (model9.B 8 ++ [step9.q]) 9000000000000 (model9.caps 8) (model9.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_9 : ExcludedOn (model9.B 9 ++ [step9.q]) 9000000000000 (model9.caps 9) (model9.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked9 : StepValid model9 9000000000000 step9 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded9_1
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

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4590000000000], [3990000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([1260000000000, 9000000000000], [1260000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([4590000000000], [5250000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3330000000000, -9000000000000], [6510000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-3990000000000, 9000000000000],
      [8580000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-1260000000000,
      -9000000000000], [2520000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-5250000000000], [9840000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-6510000000000,
      -9000000000000], [9840000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5670000000000, 9000000000000], [2490000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([4410000000000], [3750000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1428000000000], [2322000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([1260000000000, 9000000000000], [6732000000000, 0]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-2490000000000, 9000000000000], [8160000000000, 0]) (some (0, 1, 3)) (some (0, 2,
      3)) (.next ([-3750000000000], [8160000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-2322000000000], [3750000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-6732000000000,
      0], [7992000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3750000000000], [840000000000]) (some (2, 0, 1))
      (some (2, 0, 2)) (.next ([4590000000000], [3990000000000, -9000000000000]) (some (2, 0, 2))
      (some (2, 0, 2)) (.next ([1260000000000, 9000000000000], [7740000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([420000000000, 9000000000000], [3330000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-840000000000], [4590000000000])
      (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3990000000000, 9000000000000], [8580000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-7740000000000, 9000000000000],
      [9000000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3330000000000, 9000000000000],
      [3750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_9 : ExcludedOn (model10.B 9 ++ [step10.q]) 9000000000000 (model10.caps 9)
    (model10.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked10 : StepValid model10 9000000000000 step10 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded10_1
    · exact excluded10_2
    · exact excluded10_3
    · exact excluded10_4
    · exact excluded10_5
    · exact excluded10_6
    · exact excluded10_7
    · exact excluded10_8
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4335000000000], [3780000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([1260000000000, 9000000000000], [1260000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([4335000000000], [5040000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3075000000000, -9000000000000], [6300000000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [1260000000000, 9000000000000]) none
      none (.next ([-3780000000000, 9000000000000], [8115000000000, -9000000000000]) (some (3, 3,
      0)) (some (3, 3, 0)) (.next ([-1260000000000, -9000000000000], [2520000000000,
      18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-5040000000000], [9375000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-6300000000000, -9000000000000], [9375000000000,
      0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3,
      1, 0))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5925000000000, 9000000000000], [2700000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([4665000000000], [3960000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1893000000000], [2067000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([1260000000000, 9000000000000], [6732000000000, 0]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-2700000000000, 9000000000000], [8625000000000, 0]) (some (0, 1, 3)) (some (0, 2,
      3)) (.next ([-3960000000000], [8625000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-2067000000000], [3960000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-6732000000000,
      0], [7992000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3960000000000], [375000000000]) (some (2, 0, 1))
      (some (2, 0, 2)) (.next ([4335000000000], [3780000000000, -9000000000000]) (some (2, 0, 2))
      (some (2, 0, 2)) (.next ([885000000000, 9000000000000], [3075000000000, -9000000000000]) (some
      (2, 0, 2)) (some (3, 0, 2)) (.next ([1260000000000, 9000000000000], [7740000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-375000000000], [4335000000000])
      (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3780000000000, 9000000000000], [8115000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3075000000000, 9000000000000],
      [3960000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-7740000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_4 : ExcludedOn (model12.B 4 ++ [step12.q]) 9000000000000 (model12.caps 4)
    (model12.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded12_9 : ExcludedOn (model12.B 9 ++ [step12.q]) 9000000000000 (model12.caps 9)
    (model12.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded12_4
    · exact excluded12_5
    · exact excluded12_6
    · exact excluded12_7
    · exact (hj rfl).elim
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_0 : ExcludedOn (model13.B 0 ++ [step13.q]) 9000000000000 (model13.caps 0)
    (model13.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6375000000000], [1107000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([1260000000000, 9000000000000], [2115000000000, -9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2268000000000, 0], [6222000000000, -9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2268000000000], [7482000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([0], [3375000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1107000000000], [7482000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2115000000000,
      9000000000000], [3375000000000]) (some (0, 1, 3)) (some (0, 3, 3)) (.next ([-6222000000000,
      9000000000000], [8490000000000, -9000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next
      ([-7482000000000], [9750000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some (0, 3,
      2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_9 : ExcludedOn (model13.B 9 ++ [step13.q]) 9000000000000 (model13.caps 9)
    (model13.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded13_4
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
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8010000000000, 9000000000000], [1410000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([6750000000000], [2670000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5490000000000, -9000000000000], [2670000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1260000000000, 9000000000000], [1260000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (3, 3, 1)) (some (3, 3, 1)) (.next ([-1410000000000, 9000000000000],
      [9420000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-2670000000000],
      [9420000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2670000000000, 0],
      [8160000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1260000000000,
      -9000000000000], [2520000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal
      (some (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded14_4
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5370000000000], [45000000000]) (some (6, 8, 4))
      (some (7, 8, 4)) (.next ([1044000000000, 5100000000000], [63000000000, -2550000000000]) (some
      (7, 8, 4)) (some (7, 8, 4)) (.next ([4683000000000, -2550000000000], [339000000000,
      5100000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([5955000000000], [1050000000000])
      (some (7, 8, 4)) (some (7, 8, 4)) (.next ([4875000000000], [960000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([5295000000000], [1380000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      (.next ([5205000000000], [1380000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([540000000000], [180000000000]) (some (7, 8, 4)) (some (8, 8, 4)) (.next ([255000000000],
      [210000000000]) (some (8, 8, 4)) (some (8, 8, 4)) fan15Owner0Part1)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5835000000000], [1125000000000]) (some (3, 5,
      5)) (some (4, 5, 5)) (.next ([7515000000000, 9000000000000], [2115000000000, -9000000000000])
      (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1518000000000], [750000000000]) (some (4, 5, 2))
      (some (4, 5, 2)) (.next ([6255000000000], [3375000000000]) (some (4, 5, 2)) (some (4, 5, 2))
      (.next ([4737000000000], [2625000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([1410000000000, -9000000000000], [840000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5,
      3)) (.next ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([402000000000], [1098000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([258000000000, -9000000000000], [750000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([420000000000], [2250000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0],
      [1260000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-1125000000000],
      [6960000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2115000000000, 9000000000000],
      [9630000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-750000000000], [2268000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3375000000000], [9630000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-2625000000000], [7362000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-840000000000, -9000000000000], [2250000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-1260000000000, -9000000000000], [2520000000000, 18000000000000]) (some (0, 5, 3))
      (some (5, 5, 3)) (.next ([-1098000000000], [1500000000000]) (some (5, 5, 3)) (some (5, 5, 3))
      (.next ([-750000000000], [1008000000000, -9000000000000]) (some (5, 5, 3)) (some (5, 5, 3))
      (.next ([-2250000000000], [2670000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.terminal (some
      (5, 5, 3)) (some (5, 5, 3)) (some (5, 5, 3))))))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_5 : ExcludedOn (model15.B 5 ++ [step15.q]) 9000000000000 (model15.caps 5)
    (model15.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded15_8 : ExcludedOn (model15.B 8 ++ [step15.q]) 9000000000000 (model15.caps 8)
    (model15.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_9 : ExcludedOn (model15.B 9 ++ [step15.q]) 9000000000000 (model15.caps 9)
    (model15.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded15_5
    · exact excluded15_6
    · exact excluded15_7
    · exact excluded15_8
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext140000150000
end ConwaySoifer.Simplified.Certificates
