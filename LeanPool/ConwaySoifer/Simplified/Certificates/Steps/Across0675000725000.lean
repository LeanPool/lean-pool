/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across067500072500
import Mathlib.Tactic.FinCases

/-!
# Across 067500 072500 0

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
namespace Across067500072500

theorem excluded0_0 : ExcludedOn (model0.B 0 ++ [step0.q]) 9000000000000 (model0.caps 0) (model0.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([187818750000, 2782500000000], [187818750000,
      2782500000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1605637500000, 5565000000000],
      [7582181250000, -2782500000000]) (some (6, 1, 3)) (some (6, 2, 4)) (.next ([1417818750000,
      2782500000000], [7394362500000, -5565000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
      ([1417818750000, 2782500000000], [7957818750000, 2782500000000]) (some (6, 2, 4)) (some (6, 2,
      4)) (.next ([1042181250000, -2782500000000], [7582181250000, -2782500000000]) (some (6, 2, 4))
      (some (6, 2, 4)) (.next ([1042181250000, -2782500000000], [8145637500000, 5565000000000])
      (some (6, 2, 4)) (some (6, 2, 4)) (.next ([854362500000, -5565000000000], [7957818750000,
      2782500000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([0, 0], [563456250000,
      8347500000000]) (some (6, 2, 4)) (some (6, 2, 6)) (.next ([-187818750000, -2782500000000],
      [375637500000, 5565000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([-7582181250000,
      2782500000000], [9187818750000, 2782500000000]) (some (6, 2, 6)) (some (6, 3, 6)) (.next
      ([-7394362500000, 5565000000000], [8812181250000, -2782500000000]) (some (1, 3, 6)) (some (1,
      3, 6)) (.next ([-7957818750000, -2782500000000], [9375637500000, 5565000000000]) (some (1, 3,
      6)) (some (1, 3, 6)) (.next ([-7582181250000, 2782500000000], [8624362500000, -5565000000000])
      (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-8145637500000, -5565000000000], [9187818750000,
      2782500000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-7957818750000, -2782500000000],
      [8812181250000, -2782500000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.terminal (some (1, 3, 6))
      (some (1, 3, 6)) (some (1, 3, 6))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded0_1 : ExcludedOn (model0.B 1 ++ [step0.q]) 9000000000000 (model0.caps 1) (model0.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_2 : ExcludedOn (model0.B 2 ++ [step0.q]) 9000000000000 (model0.caps 2) (model0.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_4 : ExcludedOn (model0.B 4 ++ [step0.q]) 9000000000000 (model0.caps 4) (model0.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_5 : ExcludedOn (model0.B 5 ++ [step0.q]) 9000000000000 (model0.caps 5) (model0.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_6 : ExcludedOn (model0.B 6 ++ [step0.q]) 9000000000000 (model0.caps 6) (model0.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_7 : ExcludedOn (model0.B 7 ++ [step0.q]) 9000000000000 (model0.caps 7) (model0.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_8 : ExcludedOn (model0.B 8 ++ [step0.q]) 9000000000000 (model0.caps 8) (model0.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_9 : ExcludedOn (model0.B 9 ++ [step0.q]) 9000000000000 (model0.caps 9) (model0.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked0 : StepValid model0 9000000000000 step0 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded0_0
    · exact excluded0_1
    · exact excluded0_2
    · exact (hj rfl).elim
    · exact excluded0_4
    · exact excluded0_5
    · exact excluded0_6
    · exact excluded0_7
    · exact excluded0_8
    · exact excluded0_9
theorem next0 : model0.insert step0 = model1 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded1_1 : ExcludedOn (model1.B 1 ++ [step1.q]) 9000000000000 (model1.caps 1) (model1.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8392500000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([607500000000, 9000000000000],
      [607500000000, 9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([1215000000000,
      9000000000000], [7785000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([607500000000], [8392500000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [607500000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, -9000000000000],
      [8392500000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-607500000000, -9000000000000],
      [1215000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7785000000000,
      9000000000000], [9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8392500000000],
      [9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0)) (some (3, 1,
      0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_2 : ExcludedOn (model1.B 2 ++ [step1.q]) 9000000000000 (model1.caps 2) (model1.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_3 : ExcludedOn (model1.B 3 ++ [step1.q]) 9000000000000 (model1.caps 3) (model1.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8392500000000], [607500000000]) (some (1, 0, 3))
      (some (2, 0, 3)) (.next ([7785000000000, -9000000000000], [1215000000000, 9000000000000])
      (some (2, 0, 3)) (some (2, 0, 3)) (.next ([1230000000000], [607500000000, 9000000000000])
      (some (2, 0, 3)) (some (2, 3, 3)) (.next ([622500000000], [7770000000000]) (some (2, 3, 3))
      (some (2, 3, 3)) (.next ([0], [607500000000, 9000000000000]) (some (2, 3, 1)) (some (2, 3, 1))
      (.next ([-607500000000], [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-1215000000000, -9000000000000], [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-607500000000, -9000000000000], [1837500000000, 9000000000000]) (some (0, 3, 1)) (some (0,
      3, 1)) (.next ([-7770000000000], [8392500000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal
      (some (0, 3, 1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded1_4 : ExcludedOn (model1.B 4 ++ [step1.q]) 9000000000000 (model1.caps 4) (model1.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_5 : ExcludedOn (model1.B 5 ++ [step1.q]) 9000000000000 (model1.caps 5) (model1.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_6 : ExcludedOn (model1.B 6 ++ [step1.q]) 9000000000000 (model1.caps 6) (model1.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_7 : ExcludedOn (model1.B 7 ++ [step1.q]) 9000000000000 (model1.caps 7) (model1.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_8 : ExcludedOn (model1.B 8 ++ [step1.q]) 9000000000000 (model1.caps 8) (model1.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_9 : ExcludedOn (model1.B 9 ++ [step1.q]) 9000000000000 (model1.caps 9) (model1.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked1 : StepValid model1 9000000000000 step1 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded1_1
    · exact excluded1_2
    · exact excluded1_3
    · exact excluded1_4
    · exact excluded1_5
    · exact excluded1_6
    · exact excluded1_7
    · exact excluded1_8
    · exact excluded1_9
theorem next1 : model1.insert step1 = model2 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded2_0 : ExcludedOn (model2.B 0 ++ [step2.q]) 9000000000000 (model2.caps 0) (model2.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7428750000000], [1267500000000]) (some (5, 1,
      5)) (some (5, 1, 5)) (.next ([7804387500000, 5565000000000], [1687181250000, -2782500000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([795318750000, 2782500000000], [187818750000,
      2782500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([7616568750000, 2782500000000],
      [2062818750000, 2782500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([7053112500000,
      -5565000000000], [2062818750000, 2782500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([7240931250000, -2782500000000], [2250637500000, 5565000000000]) (some (4, 1, 5)) (some (4,
      1, 5)) (.next ([419681250000, -2782500000000], [375637500000, 5565000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([187818750000, 2782500000000], [187818750000, 2782500000000]) (some
      (4, 1, 5)) (some (4, 1, 5)) (.next ([375637500000, 5565000000000], [419681250000,
      -2782500000000]) (some (4, 1, 5)) (some (4, 2, 5)) (.next ([187818750000, 2782500000000],
      [795318750000, 2782500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([0, 0],
      [563456250000, 8347500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1267500000000],
      [8696250000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1687181250000, 2782500000000],
      [9491568750000, 2782500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-187818750000,
      -2782500000000], [983137500000, 5565000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-2062818750000, -2782500000000], [9679387500000, 5565000000000]) (some (0, 2, 5)) (some (0,
      2, 5)) (.next ([-2062818750000, -2782500000000], [9115931250000, -2782500000000]) (some (0, 2,
      5)) (some (0, 2, 5)) (.next ([-2250637500000, -5565000000000], [9491568750000, 2782500000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-375637500000, -5565000000000], [795318750000,
      2782500000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-187818750000, -2782500000000],
      [375637500000, 5565000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-419681250000,
      2782500000000], [795318750000, 2782500000000]) (some (0, 5, 5)) (some (1, 5, 5)) (.next
      ([-795318750000, -2782500000000], [983137500000, 5565000000000]) (some (1, 5, 5)) (some (1, 5,
      5)) (.terminal (some (1, 5, 5)) (some (1, 5, 5)) (some (1, 5, 5))))))))))))))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded2_1 : ExcludedOn (model2.B 1 ++ [step2.q]) 9000000000000 (model2.caps 1) (model2.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([607500000000, 9000000000000], [607500000000,
      9000000000000]) none none (.next ([911250000000, 9000000000000], [1571250000000]) none none
      (.next ([303750000000, 0], [963750000000, -9000000000000]) none none (.next ([303750000000],
      [1571250000000]) none none (.next ([0, 0], [607500000000, 9000000000000]) none none (.next
      ([-607500000000, -9000000000000], [1215000000000, 18000000000000]) none none (.next
      ([-1571250000000], [2482500000000, 9000000000000]) none none (.next ([-963750000000,
      9000000000000], [1267500000000, -9000000000000]) none none (.next ([-1571250000000],
      [1875000000000]) none none (.terminal none none none))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded2_2 : ExcludedOn (model2.B 2 ++ [step2.q]) 9000000000000 (model2.caps 2) (model2.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7125000000000], [303750000000]) (some (0, 0, 2))
      (some (0, 0, 2)) (.next ([6517500000000, -9000000000000], [303750000000, 0]) (some (0, 0, 2))
      (some (0, 0, 2)) (.next ([8392500000000, -9000000000000], [607500000000, 9000000000000]) (some
      (0, 0, 2)) (some (0, 0, 2)) (.next ([7125000000000, 0], [911250000000, 9000000000000]) (some
      (0, 0, 2)) (some (0, 0, 2)) (.next ([607500000000, 9000000000000], [607500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [5107500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3892500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1571250000000],
      [2625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([303750000000, 0], [963750000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([607500000000, 9000000000000],
      [3892500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [607500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-303750000000],
      [7428750000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-303750000000, 0], [6821250000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-607500000000, -9000000000000],
      [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-911250000000, -9000000000000],
      [8036250000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-607500000000,
      -9000000000000], [1215000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-5107500000000, -9000000000000], [9607500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 3)) (.next ([-4500000000000, 0], [8392500000000, -9000000000000]) (some (0, 4, 3)) (some
      (0, 4, 3)) (.next ([-2625000000000], [4196250000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-963750000000, 9000000000000], [1267500000000, -9000000000000]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-3892500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0,
      2, 3)) (.terminal (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2, 3)))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded2_3 : ExcludedOn (model2.B 3 ++ [step2.q]) 9000000000000 (model2.caps 3) (model2.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_4 : ExcludedOn (model2.B 4 ++ [step2.q]) 9000000000000 (model2.caps 4) (model2.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_5 : ExcludedOn (model2.B 5 ++ [step2.q]) 9000000000000 (model2.caps 5) (model2.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_6 : ExcludedOn (model2.B 6 ++ [step2.q]) 9000000000000 (model2.caps 6) (model2.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_8 : ExcludedOn (model2.B 8 ++ [step2.q]) 9000000000000 (model2.caps 8) (model2.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_9 : ExcludedOn (model2.B 9 ++ [step2.q]) 9000000000000 (model2.caps 9) (model2.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked2 : StepValid model2 9000000000000 step2 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded2_0
    · exact excluded2_1
    · exact excluded2_2
    · exact excluded2_3
    · exact excluded2_4
    · exact excluded2_5
    · exact excluded2_6
    · exact (hj rfl).elim
    · exact excluded2_8
    · exact excluded2_9
theorem next2 : model2.insert step2 = model3 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded3_0 : ExcludedOn (model3.B 0 ++ [step3.q]) 9000000000000 (model3.caps 0) (model3.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8625637500000, 5565000000000], [217181250000,
      -2782500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([8437818750000, 2782500000000],
      [592818750000, 2782500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([7874362500000,
      -5565000000000], [592818750000, 2782500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([8062181250000, -2782500000000], [780637500000, 5565000000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([795318750000, 2782500000000], [187818750000, 2782500000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([419681250000, -2782500000000], [375637500000, 5565000000000]) (some
      (4, 1, 5)) (some (4, 1, 5)) (.next ([187818750000, 2782500000000], [187818750000,
      2782500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([375637500000, 5565000000000],
      [419681250000, -2782500000000]) (some (4, 1, 5)) (some (4, 2, 5)) (.next ([187818750000,
      2782500000000], [795318750000, 2782500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([202500000000], [8047500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([0, 0],
      [563456250000, 8347500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-217181250000,
      2782500000000], [8842818750000, 2782500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-592818750000, -2782500000000], [9030637500000, 5565000000000]) (some (0, 2, 5)) (some (0,
      2, 5)) (.next ([-592818750000, -2782500000000], [8467181250000, -2782500000000]) (some (0, 2,
      5)) (some (0, 2, 5)) (.next ([-780637500000, -5565000000000], [8842818750000, 2782500000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-187818750000, -2782500000000], [983137500000,
      5565000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-375637500000, -5565000000000],
      [795318750000, 2782500000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-187818750000,
      -2782500000000], [375637500000, 5565000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next
      ([-419681250000, 2782500000000], [795318750000, 2782500000000]) (some (0, 5, 5)) (some (1, 5,
      5)) (.next ([-795318750000, -2782500000000], [983137500000, 5565000000000]) (some (1, 5, 5))
      (some (1, 5, 5)) (.next ([-8047500000000], [8250000000000]) (some (1, 5, 5)) (some (1, 5, 5))
      (.terminal (some (1, 5, 4)) (some (1, 5, 4)) (some (1, 5, 4))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8595000000000, 0], [262500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([8392500000000, -9000000000000],
      [607500000000, 9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([607500000000,
      9000000000000], [607500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4500000000000, 0], [5107500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([3892500000000, -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([142500000000, -9000000000000], [202500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([750000000000], [4095000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([607500000000, 9000000000000], [3892500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([345000000000, 0], [7642500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([345000000000], [8250000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [607500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-262500000000,
      -9000000000000], [8857500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-607500000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-607500000000, -9000000000000], [1215000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-5107500000000, -9000000000000], [9607500000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8392500000000, -9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-202500000000, -9000000000000], [345000000000, 0]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-4095000000000], [4845000000000]) (some (0, 4, 3)) (some (0,
      4, 3)) (.next ([-3892500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-7642500000000, 9000000000000], [7987500000000, -9000000000000]) (some (0, 2,
      3)) (some (0, 2, 3)) (.next ([-8250000000000], [8595000000000]) (some (0, 2, 3)) (some (0, 2,
      3)) (.terminal (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2, 3))))))))))))))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded3_3 : ExcludedOn (model3.B 3 ++ [step3.q]) 9000000000000 (model3.caps 3) (model3.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded3_4 : ExcludedOn (model3.B 4 ++ [step3.q]) 9000000000000 (model3.caps 4) (model3.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded3_5 : ExcludedOn (model3.B 5 ++ [step3.q]) 9000000000000 (model3.caps 5) (model3.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded3_6 : ExcludedOn (model3.B 6 ++ [step3.q]) 9000000000000 (model3.caps 6) (model3.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded3_7 : ExcludedOn (model3.B 7 ++ [step3.q]) 9000000000000 (model3.caps 7) (model3.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([648750000000], [821250000000]) (some (3, 5, 2))
      (some (4, 5, 3)) (.next ([142500000000, -9000000000000], [202500000000, 9000000000000]) (some
      (4, 5, 3)) (some (4, 5, 3)) (.next ([303750000000, 0], [963750000000, -9000000000000]) (some
      (4, 5, 3)) (some (4, 5, 3)) (.next ([1571250000000], [6517500000000, -9000000000000]) (some
      (4, 5, 3)) (some (4, 5, 3)) (.next ([1571250000000], [7125000000000]) (some (4, 5, 3)) (some
      (4, 5, 3)) (.next ([963750000000, -9000000000000], [7125000000000]) (some (4, 5, 3)) (some (4,
      5, 3)) (.next ([750000000000], [7987500000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5,
      3)) (.next ([750000000000], [8595000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([607500000000, 9000000000000], [7785000000000, -18000000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([607500000000, 9000000000000], [8392500000000, -9000000000000]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([142500000000, -9000000000000], [8595000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([0, 0], [8392500000000, -9000000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([-821250000000], [1470000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-202500000000, -9000000000000], [345000000000, 0]) (some (0, 5, 3)) (some (5, 5, 3)) (.next
      ([-963750000000, 9000000000000], [1267500000000, -9000000000000]) (some (5, 1, 3)) (some (5,
      1, 3)) (.next ([-6517500000000, 9000000000000], [8088750000000, -9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-7125000000000], [8696250000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([-7125000000000, 0], [8088750000000, -9000000000000]) (some (5, 1, 3)) (some (5,
      1, 3)) (.next ([-7987500000000, 9000000000000], [8737500000000, -9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-8595000000000], [9345000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([-7785000000000, 18000000000000], [8392500000000, -9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-8392500000000, 9000000000000], [9000000000000, 0]) (some (5, 1,
      3)) (some (5, 2, 3)) (.next ([-8595000000000, 0], [8737500000000, -9000000000000]) (some (5,
      2, 3)) (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 2, 3)) (some (5, 2,
      3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

theorem excluded3_8 : ExcludedOn (model3.B 8 ++ [step3.q]) 9000000000000 (model3.caps 8) (model3.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded3_9 : ExcludedOn (model3.B 9 ++ [step3.q]) 9000000000000 (model3.caps 9) (model3.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked3 : StepValid model3 9000000000000 step3 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded3_0
    · exact (hj rfl).elim
    · exact excluded3_2
    · exact excluded3_3
    · exact excluded3_4
    · exact excluded3_5
    · exact excluded3_6
    · exact excluded3_7
    · exact excluded3_8
    · exact excluded3_9
theorem next3 : model3.insert step3 = model4 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded4_0 : ExcludedOn (model4.B 0 ++ [step4.q]) 9000000000000 (model4.caps 0) (model4.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_2 : ExcludedOn (model4.B 2 ++ [step4.q]) 9000000000000 (model4.caps 2) (model4.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8392500000000, -9000000000000], [607500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([6015000000000], [2985000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([5407500000000, -9000000000000], [2985000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([6015000000000, 0], [3592500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([607500000000, 9000000000000], [607500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [5107500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3892500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([607500000000, 9000000000000],
      [2377500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([607500000000,
      9000000000000], [3892500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      0], [607500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-607500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-2985000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2985000000000,
      0], [8392500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-3592500000000, -9000000000000], [9607500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-607500000000, -9000000000000], [1215000000000, 18000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-5107500000000, -9000000000000], [9607500000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8392500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2377500000000, 9000000000000],
      [2985000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3892500000000, 9000000000000],
      [4500000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4, 3)) (some (0, 2,
      0)) (some (0, 4, 3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded4_3 : ExcludedOn (model4.B 3 ++ [step4.q]) 9000000000000 (model4.caps 3) (model4.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_4 : ExcludedOn (model4.B 4 ++ [step4.q]) 9000000000000 (model4.caps 4) (model4.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_5 : ExcludedOn (model4.B 5 ++ [step4.q]) 9000000000000 (model4.caps 5) (model4.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_6 : ExcludedOn (model4.B 6 ++ [step4.q]) 9000000000000 (model4.caps 6) (model4.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_7 : ExcludedOn (model4.B 7 ++ [step4.q]) 9000000000000 (model4.caps 7) (model4.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5407500000000, -9000000000000], [607500000000,
      9000000000000]) (some (3, 1, 2)) (some (4, 1, 3)) (.next ([1571250000000], [1110000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([303750000000, 0], [963750000000, -9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([607500000000, 9000000000000], [2377500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1571250000000], [6517500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1571250000000], [7125000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([963750000000, -9000000000000], [7125000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([607500000000, 9000000000000], [7785000000000,
      -18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([607500000000, 9000000000000],
      [8392500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [8392500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-607500000000,
      -9000000000000], [6015000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1110000000000],
      [2681250000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-963750000000, 9000000000000],
      [1267500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2377500000000,
      9000000000000], [2985000000000, 0]) (some (0, 1, 3)) (some (1, 1, 3)) (.next ([-6517500000000,
      9000000000000], [8088750000000, -9000000000000]) (some (1, 1, 3)) (some (1, 5, 3)) (.next
      ([-7125000000000], [8696250000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-7125000000000,
      0], [8088750000000, -9000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next
      ([-7785000000000, 18000000000000], [8392500000000, -9000000000000]) (some (1, 5, 3)) (some (1,
      5, 3)) (.next ([-8392500000000, 9000000000000], [9000000000000, 0]) (some (1, 5, 3)) (some (1,
      5, 3)) (.terminal (some (1, 5, 3)) (some (1, 2, 3)) (some (1, 5, 3))))))))))))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded4_8 : ExcludedOn (model4.B 8 ++ [step4.q]) 9000000000000 (model4.caps 8) (model4.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_9 : ExcludedOn (model4.B 9 ++ [step4.q]) 9000000000000 (model4.caps 9) (model4.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked4 : StepValid model4 9000000000000 step4 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded4_0
    · exact (hj rfl).elim
    · exact excluded4_2
    · exact excluded4_3
    · exact excluded4_4
    · exact excluded4_5
    · exact excluded4_6
    · exact excluded4_7
    · exact excluded4_8
    · exact excluded4_9
theorem next4 : model4.insert step4 = model5 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Across067500072500
end ConwaySoifer.Simplified.Certificates
