/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown320000330000
import Mathlib.Tactic.FinCases

/-!
# Aown 320000 330000 1

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
namespace Aown320000330000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan9Owner2Part0 : FanWitness := (.next ([5415000000000, 0], [2880000000000, 9000000000000])
    (some (0, 4, 1)) (some (0, 4, 1)) (.next ([375000000000], [345000000000]) (some (0, 4, 1)) (some
    (0, 4, 1)) (.next ([2340000000000], [3795000000000]) (some (0, 4, 1)) (some (0, 4, 2)) (.next
    ([1965000000000], [3450000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1815000000000],
    [3750000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([1965000000000, 0], [4155000000000,
    -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1800000000000, -9000000000000],
    [4125000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1770000000000], [4320000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1245000000000, -9000000000000], [3075000000000,
    9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1095000000000], [4125000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0], [4845000000000, 9000000000000]) (some (0, 1,
    3)) (some (0, 1, 3)) (.next ([-15000000000, -9000000000000], [375000000000, 0]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-2505000000000, -9000000000000], [8640000000000, 9000000000000]) (some
    (0, 1, 3)) (some (0, 1, 3)) (.next ([-2880000000000, -9000000000000], [9000000000000, 0]) (some
    (0, 1, 3)) (some (0, 1, 3)) (.next ([-2880000000000, -9000000000000], [8295000000000,
    9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-345000000000], [720000000000]) (some
    (0, 1, 3)) (some (0, 1, 3)) (.next ([-3795000000000], [6135000000000]) (some (0, 1, 3)) (some
    (0, 1, 3)) (.next ([-3450000000000], [5415000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-3750000000000], [5565000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4155000000000,
    9000000000000], [6120000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-4125000000000, 0], [5925000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-4320000000000], [6090000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3075000000000,
    -9000000000000], [4320000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4125000000000],
    [5220000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1, 0))
    (some (4, 1, 3)))))))))))))))))))))))))))

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2880000000000, 9000000000000], [1890000000000,
      -9000000000000]) none none (.next ([2880000000000, 9000000000000], [2070000000000,
      -9000000000000]) none none (.next ([2880000000000, 9000000000000], [2880000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0], [7650000000000, 9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1890000000000, 9000000000000], [4770000000000, 0])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2070000000000, 9000000000000], [4950000000000, 0])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2880000000000, -9000000000000], [5760000000000,
      18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) none
      none))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded8_6
    · exact (hj rfl).elim
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8805000000000], [90000000000]) none none (.next
      ([7560000000000, 9000000000000], [1245000000000, -9000000000000]) none none (.next
      ([2880000000000, 9000000000000], [1890000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([2880000000000, 9000000000000], [2880000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([1800000000000, -9000000000000], [4125000000000, 0]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([0], [7650000000000, 9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-90000000000], [8895000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-1245000000000, 9000000000000], [8805000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-1890000000000, 9000000000000], [4770000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2880000000000, -9000000000000], [5760000000000, 18000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-4125000000000, 0], [5925000000000, -9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.terminal (some (3, 1, 2)) none none))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([360000000000, -9000000000000], [15000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6135000000000, 0], [2505000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6120000000000, -9000000000000],
      [2880000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) fan9Owner2Part0)))) (den :=
      9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4320000000000, 0], [1995000000000,
      -9000000000000]) (some (1, 0, 3)) (some (2, 0, 3)) (.next ([2880000000000, 9000000000000],
      [2880000000000, 9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([4320000000000],
      [4875000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([1440000000000, -9000000000000],
      [7755000000000, 9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([0], [2880000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 3, 3)) (.next ([-1995000000000, 9000000000000],
      [6315000000000, -9000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-2880000000000,
      -9000000000000], [5760000000000, 18000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-4875000000000], [9195000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-7755000000000,
      -9000000000000], [9195000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3,
      1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6120000000000, -9000000000000], [210000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([5550000000000, 9000000000000],
      [3450000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([2880000000000,
      9000000000000], [2880000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([2670000000000], [6330000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [2880000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-210000000000,
      -9000000000000], [6330000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-3450000000000,
      9000000000000], [9000000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2880000000000,
      -9000000000000], [5760000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-6330000000000], [9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5385000000000], [375000000000]) (some (4, 0, 1))
      (some (4, 0, 2)) (.next ([2505000000000, -9000000000000], [375000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([3450000000000, -9000000000000], [2880000000000, 9000000000000])
      (some (4, 0, 2)) (some (4, 0, 3)) (.next ([2880000000000, 9000000000000], [2880000000000,
      9000000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([2880000000000, 9000000000000],
      [3450000000000, -9000000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([2505000000000,
      9000000000000], [5760000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([570000000000],
      [5385000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([0, 0], [2880000000000,
      9000000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([-375000000000], [5760000000000])
      (some (4, 0, 3)) (some (4, 1, 3)) (.next ([-375000000000], [2880000000000, -9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2880000000000, -9000000000000], [6330000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2880000000000, -9000000000000], [5760000000000,
      18000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-3450000000000, 9000000000000],
      [6330000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-5760000000000, 0],
      [8265000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5385000000000],
      [5955000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1,
      4)) (some (0, 1, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded11_0 : ExcludedOn (model11.B 0 ++ [step11.q]) 9000000000000 (model11.caps 0)
    (model11.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4050000000000], [1641000000000]) (some (2, 0,
      1)) (some (4, 0, 2)) (.next ([2880000000000, 9000000000000], [2070000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([3309000000000, 0], [2811000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([2880000000000, 9000000000000], [6120000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1170000000000, -9000000000000],
      [2880000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0],
      [6120000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-1641000000000],
      [5691000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2070000000000, 9000000000000],
      [4950000000000, 0]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2811000000000, 9000000000000],
      [6120000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-6120000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2880000000000,
      -9000000000000], [4050000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5265000000000, 9000000000000], [360000000000,
      -9000000000000]) none none (.next ([2745000000000, -9000000000000], [495000000000,
      9000000000000]) none none (.next ([5625000000000], [2385000000000]) none none (.next
      ([2880000000000, 9000000000000], [1890000000000, -9000000000000]) none none (.next
      ([2880000000000, 9000000000000], [2880000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([0], [7650000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-360000000000, 9000000000000], [5625000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-495000000000, -9000000000000], [3240000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2385000000000], [8010000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1890000000000,
      9000000000000], [4770000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2880000000000,
      -9000000000000], [5760000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal
      (some (3, 1, 2)) none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6549000000000], [66000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([360000000000, -9000000000000], [15000000000, 9000000000000]) (some
      (0, 3, 1)) (some (0, 3, 1)) (.next ([6135000000000, 0], [2505000000000, 9000000000000]) (some
      (0, 3, 1)) (some (0, 3, 1)) (.next ([6120000000000, -9000000000000], [2880000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3684000000000], [2451000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3309000000000, 0], [2811000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([360000000000, -9000000000000], [6255000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [6189000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-66000000000], [6615000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-15000000000, -9000000000000], [375000000000, 0])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2505000000000, -9000000000000], [8640000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 1, 2)) (.next ([-2880000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2451000000000],
      [6135000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2811000000000, 9000000000000],
      [6120000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6255000000000,
      -9000000000000], [6615000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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

end Aown320000330000
end ConwaySoifer.Simplified.Certificates
