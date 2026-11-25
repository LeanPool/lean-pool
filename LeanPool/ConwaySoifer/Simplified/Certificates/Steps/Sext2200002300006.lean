/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

import LeanPool.ConwaySoifer.Certificates.FanCertificate

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext220000230000
public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext2200002300006

/-!
# Sext 220000 230000 6

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

prepare_fan_cache ConwaySoifer.Simplified.Certificates.Sext220000230000.model0

-- Generated checkpoints are proposals; all acceptance proofs are checked by the kernel.

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext220000230000

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 15) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded48_3 : ExcludedOn (model48.B 3 ++ [step48.q]) 9000000000000 (model48.caps 3)
    (model48.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3450000000000], [111000000000]) (some (5, 0, 4))
      (some (6, 0, 4)) (.next ([3540000000000], [186000000000]) (some (6, 0, 4)) (some (6, 0, 4))
      (.next ([5064000000000], [372000000000]) (some (6, 0, 4)) (some (6, 0, 4)) (.next
      ([1014000000000], [111000000000]) (some (6, 0, 4)) (some (6, 0, 4)) (.next ([1104000000000],
      [186000000000]) (some (6, 0, 4)) (some (6, 0, 4)) (.next ([3939000000000], [1386000000000])
      (some (6, 0, 4)) (some (6, 0, 4)) (.next ([3936000000000], [1500000000000]) (some (6, 0, 4))
      (some (6, 0, 4)) (.next ([3774000000000], [1476000000000]) (some (6, 0, 4)) (some (6, 0, 4))
      (.next ([3480000000000, 9000000000000], [1956000000000, -9000000000000]) (some (6, 0, 4))
      (some (6, 0, 7)) (.next ([90000000000], [75000000000]) (some (6, 0, 7)) (some (6, 0, 7))
      (.next ([2355000000000, 9000000000000], [2970000000000, -9000000000000]) (some (6, 0, 7))
      (some (6, 0, 7)) (.next ([2190000000000, 9000000000000], [3060000000000, -9000000000000])
      (some (6, 0, 7)) (some (6, 0, 7)) (.next ([3564000000000], [5145000000000]) (some (6, 0, 7))
      (some (6, 0, 7)) (.next ([1980000000000, 9000000000000], [5145000000000]) (some (6, 0, 7))
      (some (6, 0, 7)) (.next ([1500000000000], [3936000000000]) (some (6, 0, 7)) (some (6, 0, 7))
      (.next ([2064000000000], [5436000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
      ([291000000000], [1209000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([480000000000,
      9000000000000], [5436000000000]) (some (6, 0, 7)) (some (6, 1, 7)) (.next ([291000000000],
      [3645000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([375000000000], [4950000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([210000000000], [5040000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) (.next ([180000000000], [4770000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([105000000000], [4935000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      fan48Owner3Part0)))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded48_9 : ExcludedOn (model48.B 9 ++ [step48.q]) 9000000000000 (model48.caps 9)
    (model48.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked48 : StepValid model48 9000000000000 step48 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded48_0
    · exact excluded48_1
    · exact (hj rfl).elim
    · exact excluded48_3
    · exact excluded48_4
    · exact excluded48_5
    · exact excluded48_6
    · exact excluded48_7
    · exact excluded48_8
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded49_0 : ExcludedOn (model49.B 0 ++ [step49.q]) 9000000000000 (model49.caps 0)
    (model49.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 15) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded49_1 : ExcludedOn (model49.B 1 ++ [step49.q]) 9000000000000 (model49.caps 1)
    (model49.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded49_2 : ExcludedOn (model49.B 2 ++ [step49.q]) 9000000000000 (model49.caps 2)
    (model49.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6855000000000, 9000000000000], [165000000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4125000000000], [651000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1584000000000], [561000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([4875000000000], [2145000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([2640000000000, 9000000000000], [2145000000000, -9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1980000000000], [2235000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([1980000000000, 9000000000000], [5436000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([660000000000], [4125000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [5436000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-165000000000, 9000000000000],
      [7020000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-651000000000],
      [4776000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-561000000000], [2145000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2145000000000], [7020000000000]) (some (0, 1, 3))
      (some (4, 1, 3)) (.next ([-2145000000000, 9000000000000], [4785000000000, 0]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-2235000000000], [4215000000000]) (some (4, 1, 3)) (some (4, 2, 3))
      (.next ([-5436000000000, 0], [7416000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-4125000000000], [4785000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some
      (4, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded49_4 : ExcludedOn (model49.B 4 ++ [step49.q]) 9000000000000 (model49.caps 4)
    (model49.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded49_6 : ExcludedOn (model49.B 6 ++ [step49.q]) 9000000000000 (model49.caps 6)
    (model49.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded49_7 : ExcludedOn (model49.B 7 ++ [step49.q]) 9000000000000 (model49.caps 7)
    (model49.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded49_8 : ExcludedOn (model49.B 8 ++ [step49.q]) 9000000000000 (model49.caps 8)
    (model49.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded49_9 : ExcludedOn (model49.B 9 ++ [step49.q]) 9000000000000 (model49.caps 9)
    (model49.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked49 : StepValid model49 9000000000000 step49 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded49_0
    · exact excluded49_1
    · exact excluded49_2
    · exact (hj rfl).elim
    · exact excluded49_4
    · exact excluded49_5
    · exact excluded49_6
    · exact excluded49_7
    · exact excluded49_8
    · exact excluded49_9
theorem next49 : model49.insert step49 = model50 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded50_0 : ExcludedOn (model50.B 0 ++ [step50.q]) 9000000000000 (model50.caps 0)
    (model50.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6705000000000], [120000000000]) (some (11, 15,
      7)) (some (12, 15, 8)) (.next ([6705000000000], [201000000000]) (some (12, 15, 8)) (some (12,
      15, 8)) (.next ([6471000000000], [279000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([1539000000000], [81000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6516000000000], [399000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6330000000000], [420000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6516000000000], [480000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6375000000000], [540000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([3015000000000], [285000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6375000000000], [621000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([1539000000000], [162000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6285000000000], [690000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([2850000000000], [330000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([255000000000], [30000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next ([6315000000000],
      [750000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next ([2769000000000], [330000000000])
      (some (12, 15, 8)) (some (12, 15, 8)) (.next ([6165000000000], [855000000000]) (some (12, 15,
      8)) (some (15, 15, 8)) fan50Owner0Part7))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded50_1 : ExcludedOn (model50.B 1 ++ [step50.q]) 9000000000000 (model50.caps 1)
    (model50.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded50_2 : ExcludedOn (model50.B 2 ++ [step50.q]) 9000000000000 (model50.caps 2)
    (model50.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded50_3 : ExcludedOn (model50.B 3 ++ [step50.q]) 9000000000000 (model50.caps 3)
    (model50.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3450000000000], [111000000000]) (some (6, 0, 8))
      (some (7, 0, 8)) (.next ([3540000000000], [186000000000]) (some (7, 0, 8)) (some (7, 0, 8))
      (.next ([1014000000000], [111000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
      ([1104000000000], [186000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([2430000000000],
      [570000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([2265000000000], [660000000000])
      (some (7, 0, 4)) (some (7, 0, 4)) (.next ([4620000000000], [1485000000000]) (some (7, 0, 4))
      (some (7, 0, 4)) (.next ([2355000000000], [825000000000]) (some (7, 0, 4)) (some (7, 0, 4))
      (.next ([3936000000000], [1500000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next
      ([2190000000000], [915000000000]) (some (7, 0, 4)) (some (7, 0, 4)) (.next ([2814000000000],
      [1296000000000]) (some (7, 0, 4)) (some (7, 0, 5)) (.next ([3480000000000, 9000000000000],
      [1956000000000, -9000000000000]) (some (7, 0, 5)) (some (7, 0, 5)) (.next ([4125000000000],
      [3000000000000]) (some (7, 0, 5)) (some (7, 0, 5)) (.next ([4620000000000, 9000000000000],
      [3630000000000, -9000000000000]) (some (7, 0, 5)) (some (7, 0, 5)) (.next ([3105000000000],
      [2505000000000]) (some (7, 0, 5)) (some (7, 0, 5)) fan50Owner3Part1)))))))))))))))) (den :=
      9000000000000)
      (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded50_5 : ExcludedOn (model50.B 5 ++ [step50.q]) 9000000000000 (model50.caps 5)
    (model50.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded50_6 : ExcludedOn (model50.B 6 ++ [step50.q]) 9000000000000 (model50.caps 6)
    (model50.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded50_7 : ExcludedOn (model50.B 7 ++ [step50.q]) 9000000000000 (model50.caps 7)
    (model50.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded50_8 : ExcludedOn (model50.B 8 ++ [step50.q]) 9000000000000 (model50.caps 8)
    (model50.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded50_9 : ExcludedOn (model50.B 9 ++ [step50.q]) 9000000000000 (model50.caps 9)
    (model50.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked50 : StepValid model50 9000000000000 step50 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded50_0
    · exact excluded50_1
    · exact excluded50_2
    · exact excluded50_3
    · exact (hj rfl).elim
    · exact excluded50_5
    · exact excluded50_6
    · exact excluded50_7
    · exact excluded50_8
    · exact excluded50_9
theorem next50 : model50.insert step50 = model51 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded51_0 : ExcludedOn (model51.B 0 ++ [step51.q]) 9000000000000 (model51.caps 0)
    (model51.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6705000000000], [120000000000]) (some (11, 15,
      7)) (some (12, 15, 8)) (.next ([6705000000000], [201000000000]) (some (12, 15, 8)) (some (12,
      15, 8)) (.next ([6471000000000], [279000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([1539000000000], [81000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6516000000000], [399000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6330000000000], [420000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6516000000000], [480000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6375000000000], [540000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6375000000000], [621000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([1539000000000], [162000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6285000000000], [690000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([255000000000], [30000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next ([6315000000000],
      [750000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next ([6165000000000], [855000000000])
      (some (12, 15, 8)) (some (12, 15, 8)) (.next ([6195000000000], [915000000000]) (some (12, 15,
      8)) (some (12, 15, 8)) (.next ([6084000000000], [936000000000]) (some (12, 15, 8)) (some (12,
      15, 8)) (.next ([6114000000000], [996000000000]) (some (12, 15, 8)) (some (12, 15, 8))
      fan51Owner0Part7))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded51_1 : ExcludedOn (model51.B 1 ++ [step51.q]) 9000000000000 (model51.caps 1)
    (model51.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded51_2 : ExcludedOn (model51.B 2 ++ [step51.q]) 9000000000000 (model51.caps 2)
    (model51.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded51_3 : ExcludedOn (model51.B 3 ++ [step51.q]) 9000000000000 (model51.caps 3)
    (model51.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3450000000000], [111000000000]) (some (6, 0, 8))
      (some (7, 0, 8)) (.next ([3540000000000], [186000000000]) (some (7, 0, 8)) (some (7, 0, 8))
      (.next ([1014000000000], [111000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
      ([1104000000000], [186000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([2355000000000],
      [825000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([3936000000000], [1500000000000])
      (some (7, 0, 8)) (some (7, 0, 8)) (.next ([2190000000000], [915000000000]) (some (7, 0, 8))
      (some (7, 0, 8)) (.next ([3564000000000], [1551000000000]) (some (7, 0, 8)) (some (7, 0, 8))
      (.next ([3480000000000, 9000000000000], [1956000000000, -9000000000000]) (some (7, 0, 8))
      (some (7, 0, 8)) (.next ([4365000000000], [2490000000000]) (some (7, 0, 8)) (some (7, 0, 8))
      (.next ([3855000000000], [2760000000000]) (some (7, 0, 5)) (some (7, 0, 5)) (.next
      ([2175000000000], [1575000000000]) (some (7, 0, 5)) (some (7, 8, 5)) (.next ([4125000000000],
      [3000000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([2010000000000], [1665000000000])
      (some (7, 8, 5)) (some (7, 8, 5)) (.next ([90000000000], [75000000000]) (some (7, 8, 5)) (some
      (7, 8, 5)) fan51Owner3Part1)))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded51_5 : ExcludedOn (model51.B 5 ++ [step51.q]) 9000000000000 (model51.caps 5)
    (model51.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6615000000000, 0], [405000000000,
      -9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan51Owner5Part0)) (den := 9000000000000)
      (fuel
      := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded51_6 : ExcludedOn (model51.B 6 ++ [step51.q]) 9000000000000 (model51.caps 6)
    (model51.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded51_7 : ExcludedOn (model51.B 7 ++ [step51.q]) 9000000000000 (model51.caps 7)
    (model51.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded51_8 : ExcludedOn (model51.B 8 ++ [step51.q]) 9000000000000 (model51.caps 8)
    (model51.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded51_9 : ExcludedOn (model51.B 9 ++ [step51.q]) 9000000000000 (model51.caps 9)
    (model51.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked51 : StepValid model51 9000000000000 step51 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded51_0
    · exact excluded51_1
    · exact excluded51_2
    · exact excluded51_3
    · exact (hj rfl).elim
    · exact excluded51_5
    · exact excluded51_6
    · exact excluded51_7
    · exact excluded51_8
    · exact excluded51_9
theorem next51 : model51.insert step51 = model52 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded52_0 : ExcludedOn (model52.B 0 ++ [step52.q]) 9000000000000 (model52.caps 0)
    (model52.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6705000000000], [120000000000]) (some (15, 2,
      7)) (some (15, 3, 8)) (.next ([6705000000000], [201000000000]) (some (15, 3, 8)) (some (15, 3,
      8)) (.next ([7890000000000], [315000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next
      ([6471000000000], [279000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next ([7920000000000],
      [375000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next ([1539000000000], [81000000000])
      (some (15, 3, 8)) (some (15, 3, 8)) (.next ([6516000000000], [399000000000]) (some (15, 3, 8))
      (some (15, 3, 8)) (.next ([6330000000000], [420000000000]) (some (15, 3, 8)) (some (15, 3, 8))
      (.next ([6516000000000], [480000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next
      ([7890000000000], [660000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next ([6375000000000],
      [540000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next ([6375000000000], [621000000000])
      (some (15, 3, 8)) (some (15, 3, 8)) (.next ([1539000000000], [162000000000]) (some (15, 3, 8))
      (some (15, 3, 8)) (.next ([6285000000000], [690000000000]) (some (15, 3, 8)) (some (15, 3, 8))
      (.next ([255000000000], [30000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next
      ([6315000000000], [750000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next ([7701000000000],
      [939000000000]) (some (15, 3, 8)) (some (15, 3, 8)) fan52Owner0Part7))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded52_1 : ExcludedOn (model52.B 1 ++ [step52.q]) 9000000000000 (model52.caps 1)
    (model52.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded52_2 : ExcludedOn (model52.B 2 ++ [step52.q]) 9000000000000 (model52.caps 2)
    (model52.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([4125000000000], [651000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([2640000000000, 9000000000000], [2145000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3564000000000], [3171000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([4245000000000, 9000000000000], [4755000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1605000000000], [2610000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1980000000000, 9000000000000], [5436000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([2265000000000], [6735000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([660000000000], [4125000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0],
      [5436000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-651000000000], [4776000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-2145000000000, 9000000000000], [4785000000000, 0])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3171000000000], [6735000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-4755000000000, 9000000000000], [9000000000000, 0]) (some (0, 4, 3))
      (some (4, 4, 3)) (.next ([-2610000000000], [4215000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-5436000000000, 0], [7416000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-6735000000000], [9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-4125000000000], [4785000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded52_4 : ExcludedOn (model52.B 4 ++ [step52.q]) 9000000000000 (model52.caps 4)
    (model52.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6735000000000], [285000000000, -9000000000000])
      (some (6, 0, 6)) (some (6, 1, 6)) (.next ([4110000000000], [285000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([5610000000000], [750000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([6735000000000], [2265000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([750000000000], [255000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4605000000000],
      [1785000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2625000000000], [1980000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1980000000000], [2010000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([1125000000000], [1515000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([1230000000000], [1755000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([2205000000000], [4410000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1980000000000,
      9000000000000], [4410000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1980000000000,
      9000000000000], [4635000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan52Owner4Part0)))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded52_5 : ExcludedOn (model52.B 5 ++ [step52.q]) 9000000000000 (model52.caps 5)
    (model52.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded52_6 : ExcludedOn (model52.B 6 ++ [step52.q]) 9000000000000 (model52.caps 6)
    (model52.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded52_7 : ExcludedOn (model52.B 7 ++ [step52.q]) 9000000000000 (model52.caps 7)
    (model52.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded52_8 : ExcludedOn (model52.B 8 ++ [step52.q]) 9000000000000 (model52.caps 8)
    (model52.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded52_9 : ExcludedOn (model52.B 9 ++ [step52.q]) 9000000000000 (model52.caps 9)
    (model52.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked52 : StepValid model52 9000000000000 step52 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded52_0
    · exact excluded52_1
    · exact excluded52_2
    · exact (hj rfl).elim
    · exact excluded52_4
    · exact excluded52_5
    · exact excluded52_6
    · exact excluded52_7
    · exact excluded52_8
    · exact excluded52_9
theorem next52 : model52.insert step52 = model53 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded53_0 : ExcludedOn (model53.B 0 ++ [step53.q]) 9000000000000 (model53.caps 0)
    (model53.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6705000000000], [120000000000]) (some (11, 15,
      7)) (some (12, 15, 8)) (.next ([6705000000000], [201000000000]) (some (12, 15, 8)) (some (12,
      15, 8)) (.next ([6471000000000], [279000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([7950000000000], [345000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([8205000000000], [375000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([7860000000000], [375000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([1539000000000], [81000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6516000000000], [399000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6330000000000], [420000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([8295000000000], [564000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6516000000000], [480000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6375000000000], [540000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([8295000000000], [705000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6375000000000], [621000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([1539000000000], [162000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([6285000000000], [690000000000]) (some (12, 15, 8)) (some (12, 15, 8)) (.next
      ([255000000000], [30000000000]) (some (12, 15, 8)) (some (12, 15, 8))
      fan53Owner0Part7))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded53_1 : ExcludedOn (model53.B 1 ++ [step53.q]) 9000000000000 (model53.caps 1)
    (model53.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded53_2 : ExcludedOn (model53.B 2 ++ [step53.q]) 9000000000000 (model53.caps 2)
    (model53.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded53_3 : ExcludedOn (model53.B 3 ++ [step53.q]) 9000000000000 (model53.caps 3)
    (model53.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded53_4 : ExcludedOn (model53.B 4 ++ [step53.q]) 9000000000000 (model53.caps 4)
    (model53.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([5535000000000], [465000000000]) (some (5, 0, 6))
      (some (5, 1, 6)) (.next ([5610000000000], [750000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([6000000000000], [1080000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([5280000000000], [1470000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([750000000000],
      [255000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4605000000000], [1785000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1590000000000], [1080000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([2625000000000], [1980000000000]) (some (5, 1, 2)) (some (5, 6, 2))
      (.next ([1980000000000], [2010000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([3525000000000], [4455000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([1230000000000],
      [1755000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([2205000000000], [4410000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([1980000000000, 9000000000000], [4410000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) fan53Owner4Part0)))))))))))))) (den := 9000000000000) (fuel
      := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded53_6 : ExcludedOn (model53.B 6 ++ [step53.q]) 9000000000000 (model53.caps 6)
    (model53.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded53_7 : ExcludedOn (model53.B 7 ++ [step53.q]) 9000000000000 (model53.caps 7)
    (model53.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded53_8 : ExcludedOn (model53.B 8 ++ [step53.q]) 9000000000000 (model53.caps 8)
    (model53.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded53_9 : ExcludedOn (model53.B 9 ++ [step53.q]) 9000000000000 (model53.caps 9)
    (model53.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked53 : StepValid model53 9000000000000 step53 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded53_0
    · exact excluded53_1
    · exact excluded53_2
    · exact excluded53_3
    · exact excluded53_4
    · exact (hj rfl).elim
    · exact excluded53_6
    · exact excluded53_7
    · exact excluded53_8
    · exact excluded53_9
theorem next53 : model53.insert step53 = model54 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded54_0 : ExcludedOn (model54.B 0 ++ [step54.q]) 9000000000000 (model54.caps 0)
    (model54.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 4 15) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded54_1 : ExcludedOn (model54.B 1 ++ [step54.q]) 9000000000000 (model54.caps 1)
    (model54.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded54_3 : ExcludedOn (model54.B 3 ++ [step54.q]) 9000000000000 (model54.caps 3)
    (model54.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([7689000000000], [1020000000000]) (some (3, 0,
      5)) (some (4, 0, 5)) fan54Owner3Part0)) (den := 9000000000000) (fuel :=
      12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded54_4 : ExcludedOn (model54.B 4 ++ [step54.q]) 9000000000000 (model54.caps 4)
    (model54.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded54_5 : ExcludedOn (model54.B 5 ++ [step54.q]) 9000000000000 (model54.caps 5)
    (model54.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded54_6 : ExcludedOn (model54.B 6 ++ [step54.q]) 9000000000000 (model54.caps 6)
    (model54.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded54_7 : ExcludedOn (model54.B 7 ++ [step54.q]) 9000000000000 (model54.caps 7)
    (model54.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded54_8 : ExcludedOn (model54.B 8 ++ [step54.q]) 9000000000000 (model54.caps 8)
    (model54.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded54_9 : ExcludedOn (model54.B 9 ++ [step54.q]) 9000000000000 (model54.caps 9)
    (model54.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked54 : StepValid model54 9000000000000 step54 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded54_0
    · exact excluded54_1
    · exact (hj rfl).elim
    · exact excluded54_3
    · exact excluded54_4
    · exact excluded54_5
    · exact excluded54_6
    · exact excluded54_7
    · exact excluded54_8
    · exact excluded54_9
theorem next54 : model54.insert step54 = model55 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded55_0 : ExcludedOn (model55.B 0 ++ [step55.q]) 9000000000000 (model55.caps 0)
    (model55.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([6705000000000], [120000000000]) (some (15, 2,
      7)) (some (15, 3, 8)) (.next ([6705000000000], [201000000000]) (some (15, 3, 8)) (some (15, 3,
      8)) (.next ([6471000000000], [279000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next
      ([1539000000000], [81000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next ([6516000000000],
      [399000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next ([6330000000000], [420000000000])
      (some (15, 3, 8)) (some (15, 3, 8)) (.next ([6516000000000], [480000000000]) (some (15, 3, 8))
      (some (15, 3, 8)) (.next ([6375000000000], [540000000000]) (some (15, 3, 8)) (some (15, 3, 8))
      (.next ([6375000000000], [621000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next
      ([1539000000000], [162000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next ([6285000000000],
      [690000000000]) (some (15, 3, 8)) (some (15, 3, 8)) (.next ([255000000000], [30000000000])
      (some (15, 3, 8)) (some (15, 3, 8)) (.next ([6315000000000], [750000000000]) (some (15, 3, 8))
      (some (15, 3, 8)) (.next ([6165000000000], [855000000000]) (some (15, 3, 8)) (some (15, 3, 8))
      (.next ([6195000000000], [915000000000]) (some (15, 3, 8)) (some (15, 3, 8))
      fan55Owner0Part7))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded55_1 : ExcludedOn (model55.B 1 ++ [step55.q]) 9000000000000 (model55.caps 1)
    (model55.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([3060000000000], [750000000000]) (some (5, 5, 1))
      (some (5, 5, 2)) (.next ([2970000000000], [855000000000]) (some (5, 5, 2)) (some (5, 5, 2))
      (.next ([6315000000000, 9000000000000], [3060000000000, -9000000000000]) (some (5, 5, 2))
      (some (5, 5, 2)) (.next ([1080000000000, -9000000000000], [750000000000, 0]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([990000000000, -9000000000000], [855000000000, 0]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([1980000000000, 9000000000000], [1980000000000, 9000000000000]) (some
      (5, 1, 2)) (some (5, 1, 2)) (.next ([4335000000000], [5040000000000]) (some (5, 1, 2)) (some
      (5, 1, 2)) (.next ([2355000000000, -9000000000000], [5040000000000, 0]) (some (5, 1, 2)) (some
      (5, 1, 2)) (.next ([1230000000000, 9000000000000], [3810000000000]) (some (5, 1, 2)) (some (5,
      1, 2)) (.next ([1125000000000, 9000000000000], [3825000000000]) (some (5, 1, 2)) (some (5, 1,
      2)) (.next ([15000000000], [90000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([0],
      [1980000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-750000000000],
      [3810000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([-855000000000], [3825000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-3060000000000, 9000000000000], [9375000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-750000000000, 0], [1830000000000, -9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-855000000000, 0], [1845000000000, -9000000000000])
      (some (5, 1, 3)) (some (5, 1, 4)) (.next ([-1980000000000, -9000000000000], [3960000000000,
      18000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([-5040000000000], [9375000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([-5040000000000, 0], [7395000000000,
      -9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([-3810000000000], [5040000000000,
      9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([-3825000000000], [4950000000000,
      9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([-90000000000], [105000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.terminal (some (5, 1, 5)) (some (5, 1, 5)) (some (5, 1,
      5))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded55_3 : ExcludedOn (model55.B 3 ++ [step55.q]) 9000000000000 (model55.caps 3)
    (model55.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan (.next ([8625000000000], [480000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) fan55Owner3Part0)) (den := 9000000000000) (fuel :=
      12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  certify_fan

theorem excluded55_4 : ExcludedOn (model55.B 4 ++ [step55.q]) 9000000000000 (model55.caps 4)
    (model55.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded55_5 : ExcludedOn (model55.B 5 ++ [step55.q]) 9000000000000 (model55.caps 5)
    (model55.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded55_6 : ExcludedOn (model55.B 6 ++ [step55.q]) 9000000000000 (model55.caps 6)
    (model55.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded55_7 : ExcludedOn (model55.B 7 ++ [step55.q]) 9000000000000 (model55.caps 7)
    (model55.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded55_8 : ExcludedOn (model55.B 8 ++ [step55.q]) 9000000000000 (model55.caps 8)
    (model55.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem excluded55_9 : ExcludedOn (model55.B 9 ++ [step55.q]) 9000000000000 (model55.caps 9)
    (model55.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => rfl

theorem checked55 : StepValid model55 9000000000000 step55 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded55_0
    · exact excluded55_1
    · exact (hj rfl).elim
    · exact excluded55_3
    · exact excluded55_4
    · exact excluded55_5
    · exact excluded55_6
    · exact excluded55_7
    · exact excluded55_8
    · exact excluded55_9
theorem next55 : model55.insert step55 = model56 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

end Sext220000230000
end ConwaySoifer.Simplified.Certificates
