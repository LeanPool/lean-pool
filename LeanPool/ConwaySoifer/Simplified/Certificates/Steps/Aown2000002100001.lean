/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown200000210000
import Mathlib.Tactic.FinCases

/-!
# Aown 200000 210000 1

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
namespace Aown200000210000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan8Owner0Part0 : FanWitness := (.next ([375000000000], [375000000000]) (some (8, 2, 10)) (some
    (8, 2, 10)) (.next ([501000000000, -2370000000000], [573000000000, 4740000000000]) (some (8, 2,
    10)) (some (9, 3, 10)) (.next ([375000000000], [600000000000]) (some (9, 3, 10)) (some (9, 3,
    10)) (.next ([225000000000], [1350000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next
    ([126000000000, -2370000000000], [1323000000000, 4740000000000]) (some (9, 3, 10)) (some (9, 3,
    10)) (.next ([0], [1350000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([-99000000000,
    -2370000000000], [1548000000000, 4740000000000]) (some (0, 3, 10)) (some (0, 4, 10)) (.next
    ([-675000000000], [8025000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-1050000000000],
    [8775000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-1275000000000], [9000000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-225000000000], [1575000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([-1176000000000, 2370000000000], [7452000000000, -4740000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-2025000000000], [9375000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([-2250000000000], [9375000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    (.next ([-2124000000000, -2370000000000], [7926000000000, -2370000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([-2625000000000], [9000000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    (.next ([-2625000000000], [8775000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-375000000000], [975000000000]) (some (0, 4, 10)) (some (0, 10, 10)) (.next ([-348000000000,
    -4740000000000], [849000000000, 2370000000000]) (some (0, 10, 10)) (some (0, 10, 10)) (.next
    ([-375000000000], [750000000000]) (some (0, 10, 10)) (some (0, 10, 10)) (.next ([-573000000000,
    -4740000000000], [1074000000000, 2370000000000]) (some (0, 10, 10)) (some (1, 10, 10)) (.next
    ([-600000000000], [975000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-1350000000000], [1575000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-1323000000000, -4740000000000], [1449000000000, 2370000000000]) (some (1, 10, 10)) (some (1,
    10, 10)) (.terminal (some (1, 10, 10)) (some (1, 10, 10)) (some (1, 10,
    10)))))))))))))))))))))))))))

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1449000000000, 2370000000000], [99000000000,
      2370000000000]) (some (10, 1, 10)) (some (10, 2, 10)) (.next ([7350000000000], [675000000000])
      (some (10, 2, 10)) (some (10, 2, 10)) (.next ([7725000000000], [1050000000000]) (some (8, 2,
      10)) (some (8, 2, 10)) (.next ([7725000000000], [1275000000000]) (some (8, 2, 10)) (some (8,
      2, 10)) (.next ([1350000000000], [225000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([6276000000000, -2370000000000], [1176000000000, -2370000000000]) (some (8, 2, 10)) (some (8,
      2, 10)) (.next ([7350000000000], [2025000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([7125000000000], [2250000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([5802000000000,
      -4740000000000], [2124000000000, 2370000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([6375000000000], [2625000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([6150000000000], [2625000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([600000000000],
      [375000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([501000000000, -2370000000000],
      [348000000000, 4740000000000]) (some (8, 2, 10)) (some (8, 2, 10))
      fan8Owner0Part0)))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([450000000000, -9000000000000], [150000000000,
      9000000000000]) none none (.next ([1800000000000, 9000000000000], [1800000000000,
      9000000000000]) none none (.next ([2250000000000], [2850000000000]) none none (.next
      ([1800000000000, 9000000000000], [2700000000000, -9000000000000]) none none (.next
      ([1200000000000, 9000000000000], [2250000000000]) none none (.next ([0], [6300000000000,
      9000000000000]) none none (.next ([-150000000000, -9000000000000], [600000000000, 0]) none
      none (.next ([-1800000000000, -9000000000000], [3600000000000, 18000000000000]) none none
      (.next ([-2850000000000], [5100000000000]) none none (.next ([-2700000000000, 9000000000000],
      [4500000000000, 0]) none none (.next ([-2250000000000], [3450000000000, 9000000000000]) none
      none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([450000000000, -9000000000000], [150000000000,
      9000000000000]) (some (2, 4, 1)) (some (3, 4, 2)) (.next ([2250000000000], [5550000000000,
      -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1800000000000, 9000000000000],
      [5400000000000, -18000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([2250000000000],
      [7350000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1800000000000, 9000000000000],
      [7200000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([450000000000,
      -9000000000000], [7350000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0],
      [7200000000000, -9000000000000]) (some (3, 4, 2)) (some (4, 4, 2)) (.next ([-150000000000,
      -9000000000000], [600000000000, 0]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-5550000000000,
      9000000000000], [7800000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-5400000000000, 18000000000000], [7200000000000, -9000000000000]) (some (4, 0, 2)) (some (4,
      0, 2)) (.next ([-7350000000000], [9600000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next
      ([-7200000000000, 9000000000000], [9000000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-7350000000000, 0], [7800000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.terminal (some (4, 1, 2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2400000000000, -9000000000000], [1800000000000,
      9000000000000]) (some (2, 0, 1)) (some (3, 0, 2)) (.next ([1800000000000, 9000000000000],
      [3000000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1800000000000,
      9000000000000], [5400000000000, -18000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([1800000000000, 9000000000000], [7200000000000, -9000000000000]) (some (3, 0, 2)) (some (3,
      0, 2)) (.next ([0, 0], [7200000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2))
      (.next ([-1800000000000, -9000000000000], [4200000000000]) (some (0, 0, 2)) (some (0, 0, 2))
      (.next ([-3000000000000, 9000000000000], [4800000000000, 0]) (some (0, 0, 2)) (some (0, 0, 2))
      (.next ([-5400000000000, 18000000000000], [7200000000000, -9000000000000]) (some (0, 0, 2))
      (some (0, 4, 2)) (.next ([-7200000000000, 9000000000000], [9000000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 1, 2)) (some (0, 4, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([1800000000000, 9000000000000], [1800000000000,
      9000000000000]) none none (.next ([1800000000000, 9000000000000], [3000000000000,
      -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([1800000000000, 9000000000000],
      [4500000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([0],
      [6600000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1800000000000,
      -9000000000000], [3600000000000, 18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-3000000000000, 9000000000000], [4800000000000, 0]) (some (0, 1, 3)) (some (1, 1, 3)) (.next
      ([-4500000000000, 9000000000000], [6300000000000, 0]) (some (1, 1, 3)) (some (1, 1, 3))
      (.terminal (some (1, 1, 3)) none none))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7050000000000, 9000000000000], [1440000000000,
      -9000000000000]) none none (.next ([3450000000000, -9000000000000], [3240000000000, 0]) (some
      (3, 1, 2)) (some (3, 1, 2)) (.next ([1800000000000, 9000000000000], [1800000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1800000000000, 9000000000000],
      [3000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([450000000000],
      [8040000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0], [6600000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1440000000000, 9000000000000],
      [8490000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3240000000000, 0],
      [6690000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1800000000000,
      -9000000000000], [3600000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3000000000000, 9000000000000], [4800000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-8040000000000], [8490000000000]) (some (3, 1, 2)) none (.terminal none none
      none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3240000000000], [510000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7350000000000, 0], [1200000000000, 9000000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7200000000000, -9000000000000], [1800000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5325000000000, 0], [1800000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3600000000000], [2640000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([3450000000000, -9000000000000], [3240000000000, 0]) (some (0, 1, 1))
      (some (0, 1, 1)) (.next ([1440000000000, -9000000000000], [2310000000000, 9000000000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1575000000000], [3240000000000]) (some (0, 1, 1))
      (some (0, 1, 1)) (.next ([600000000000], [1425000000000]) (some (0, 1, 1)) (some (0, 1, 1))
      (.next ([600000000000], [6750000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([0, 0],
      [1800000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-510000000000],
      [3750000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-1200000000000, -9000000000000],
      [8550000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1800000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1800000000000, -9000000000000], [7125000000000, 9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-2640000000000], [6240000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-3240000000000, 0], [6690000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-2310000000000, -9000000000000], [3750000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-3240000000000], [4815000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-1425000000000], [2025000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-6750000000000], [7350000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_3 : ExcludedOn (model11.B 3 ++ [step11.q]) 9000000000000 (model11.caps 3)
    (model11.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1800000000000, 9000000000000], [1800000000000,
      9000000000000]) (some (1, 0, 3)) (some (2, 0, 3)) (.next ([3750000000000, 0], [3960000000000,
      -9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([3750000000000], [5760000000000])
      (some (2, 0, 3)) (some (2, 0, 3)) (.next ([1950000000000, -9000000000000], [7560000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([0], [1800000000000, 9000000000000])
      (some (2, 0, 3)) (some (2, 3, 3)) (.next ([-1800000000000, -9000000000000], [3600000000000,
      18000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-3960000000000, 9000000000000],
      [7710000000000, -9000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-5760000000000],
      [9510000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-7560000000000, -9000000000000],
      [9510000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3, 1)) (some (0, 3,
      1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_4 : ExcludedOn (model11.B 4 ++ [step11.q]) 9000000000000 (model11.caps 4)
    (model11.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7050000000000, 9000000000000], [1350000000000,
      -9000000000000]) none none (.next ([3450000000000, -9000000000000], [3150000000000, 0]) none
      none (.next ([1800000000000, 9000000000000], [1800000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1800000000000, 9000000000000], [3000000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([450000000000], [7950000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0], [6600000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-1350000000000, 9000000000000], [8400000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-3150000000000, 0], [6600000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-1800000000000, -9000000000000], [3600000000000, 18000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-3000000000000, 9000000000000], [4800000000000, 0]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-7950000000000], [8400000000000]) (some (3, 1, 2)) none
      (.terminal none none none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7350000000000, 0], [1200000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3150000000000], [600000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7200000000000, -9000000000000], [1800000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5325000000000, 0], [1800000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3600000000000], [2550000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3450000000000, -9000000000000], [3150000000000, 0])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1350000000000, -9000000000000], [2400000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1575000000000], [3150000000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([600000000000], [1425000000000]) (some (0, 1, 1))
      (some (0, 1, 1)) (.next ([600000000000], [6750000000000]) (some (0, 1, 1)) (some (0, 1, 2))
      (.next ([0, 0], [1800000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-1200000000000, -9000000000000], [8550000000000, 9000000000000]) (some (0, 1, 2)) (some (0,
      1, 3)) (.next ([-600000000000], [3750000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1800000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-1800000000000, -9000000000000], [7125000000000, 9000000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-2550000000000], [6150000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-3150000000000, 0], [6600000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-2400000000000, -9000000000000], [3750000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-3150000000000], [4725000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-1425000000000], [2025000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-6750000000000], [7350000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_3 : ExcludedOn (model12.B 3 ++ [step12.q]) 9000000000000 (model12.caps 3)
    (model12.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1800000000000, 9000000000000], [1800000000000,
      9000000000000]) (some (1, 0, 3)) (some (2, 0, 3)) (.next ([3750000000000, 0], [4050000000000,
      -9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([3750000000000], [5850000000000])
      (some (2, 0, 3)) (some (2, 0, 3)) (.next ([1950000000000, -9000000000000], [7650000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([0], [1800000000000, 9000000000000])
      (some (2, 0, 3)) (some (2, 3, 3)) (.next ([-1800000000000, -9000000000000], [3600000000000,
      18000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-4050000000000, 9000000000000],
      [7800000000000, -9000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-5850000000000],
      [9600000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-7650000000000, -9000000000000],
      [9600000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3, 1)) (some (0, 3,
      1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded12_1
    · exact excluded12_2
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5925000000000, 9000000000000], [600000000000,
      -9000000000000]) none none (.next ([6525000000000], [675000000000]) none none (.next
      ([1800000000000, 9000000000000], [1800000000000, 9000000000000]) none none (.next
      ([2325000000000, -9000000000000], [2400000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([1800000000000, 9000000000000], [3000000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([0], [6600000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-600000000000, 9000000000000], [6525000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-675000000000], [7200000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1800000000000,
      -9000000000000], [3600000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2400000000000, 0], [4725000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-3000000000000, 9000000000000], [4800000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7350000000000, 0], [1200000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7200000000000, -9000000000000],
      [1800000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5325000000000, 0],
      [1800000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2475000000000],
      [1800000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2400000000000], [2475000000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([2325000000000, -9000000000000], [2400000000000, 0])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([600000000000], [1425000000000]) (some (0, 1, 1))
      (some (0, 1, 1)) (.next ([450000000000], [2400000000000]) (some (0, 1, 1)) (some (0, 1, 2))
      (.next ([600000000000, -9000000000000], [4275000000000, 9000000000000]) (some (0, 1, 2)) (some
      (0, 1, 2)) (.next ([600000000000], [6750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([0, 0], [1800000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-1200000000000, -9000000000000], [8550000000000, 9000000000000]) (some (0, 1, 2)) (some (0,
      1, 3)) (.next ([-1800000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some
      (0, 1, 3)) (.next ([-1800000000000, -9000000000000], [7125000000000, 9000000000000]) (some (0,
      1, 3)) (some (0, 1, 3)) (.next ([-1800000000000], [4275000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-2475000000000], [4875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2400000000000, 0], [4725000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-1425000000000], [2025000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2400000000000], [2850000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4275000000000,
      -9000000000000], [4875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6750000000000],
      [7350000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1,
      0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5175000000000, 9000000000000], [585000000000,
      -9000000000000]) none none (.next ([5760000000000], [1425000000000]) none none (.next
      ([1800000000000, 9000000000000], [1800000000000, 9000000000000]) none none (.next
      ([1575000000000, -9000000000000], [2385000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([0], [6600000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-585000000000, 9000000000000], [5760000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-1425000000000], [7185000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1800000000000,
      -9000000000000], [3600000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2385000000000, 0], [3960000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) none none))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2085000000000], [300000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7350000000000, 0], [1200000000000, 9000000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7200000000000, -9000000000000], [1800000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5325000000000, 0], [1800000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1725000000000], [1785000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([2385000000000], [3240000000000]) (some (0, 1, 1)) (some (0, 1, 1))
      (.next ([1575000000000, -9000000000000], [2385000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1))
      (.next ([600000000000], [1425000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next
      ([585000000000, -9000000000000], [5040000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1,
      2)) (.next ([600000000000], [6750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0, 0],
      [1800000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-300000000000],
      [2385000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-1200000000000, -9000000000000],
      [8550000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1800000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1800000000000, -9000000000000], [7125000000000, 9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-1785000000000], [3510000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-3240000000000], [5625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2385000000000,
      0], [3960000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1425000000000], [2025000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5040000000000,
      -9000000000000], [5625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6750000000000],
      [7350000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1,
      0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_3 : ExcludedOn (model14.B 3 ++ [step14.q]) 9000000000000 (model14.caps 3)
    (model14.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded15_1 : ExcludedOn (model15.B 1 ++ [step15.q]) 9000000000000 (model15.caps 1)
    (model15.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000, 9000000000000], [750000000000,
      -9000000000000]) none none (.next ([1950000000000, -9000000000000], [600000000000,
      9000000000000]) none none (.next ([3750000000000], [3600000000000]) none none (.next
      ([1800000000000, 9000000000000], [1800000000000, 9000000000000]) none none (.next
      ([1800000000000, 9000000000000], [3000000000000, -9000000000000]) none none (.next ([0],
      [6600000000000, 9000000000000]) none none (.next ([-750000000000, 9000000000000],
      [3750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-600000000000, -9000000000000],
      [2550000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3600000000000],
      [7350000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1800000000000, -9000000000000],
      [3600000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3000000000000,
      9000000000000], [4800000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) none none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded15_2 : ExcludedOn (model15.B 2 ++ [step15.q]) 9000000000000 (model15.caps 2)
    (model15.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7350000000000, 0], [1200000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7200000000000, -9000000000000],
      [1800000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1500000000000],
      [450000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1950000000000, -9000000000000],
      [600000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([450000000000,
      -9000000000000], [150000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next
      ([2550000000000], [5250000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([600000000000],
      [1425000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([750000000000, -9000000000000],
      [7050000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 2)) (.next ([600000000000],
      [6750000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([75000000000], [2475000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0], [1800000000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-1200000000000, -9000000000000], [8550000000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1800000000000, -9000000000000], [9000000000000,
      0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-450000000000], [1950000000000]) (some (0, 4,
      3)) (some (0, 4, 3)) (.next ([-600000000000, -9000000000000], [2550000000000, 0]) (some (0, 1,
      3)) (some (0, 1, 3)) (.next ([-150000000000, -9000000000000], [600000000000, 0]) (some (0, 1,
      3)) (some (0, 1, 3)) (.next ([-5250000000000], [7800000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-1425000000000], [2025000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-7050000000000, -9000000000000], [7800000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-6750000000000], [7350000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-2475000000000], [2550000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_3 : ExcludedOn (model15.B 3 ++ [step15.q]) 9000000000000 (model15.caps 3)
    (model15.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_8 : ExcludedOn (model15.B 8 ++ [step15.q]) 9000000000000 (model15.caps 8)
    (model15.ord 8) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded15_1
    · exact excluded15_2
    · exact excluded15_3
    · exact excluded15_4
    · exact excluded15_5
    · exact excluded15_6
    · exact excluded15_7
    · exact excluded15_8
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown200000210000
end ConwaySoifer.Simplified.Certificates
