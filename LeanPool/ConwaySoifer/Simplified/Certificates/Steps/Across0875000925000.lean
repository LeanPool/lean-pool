/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across087500092500
import Mathlib.Tactic.FinCases

/-!
# Across 087500 092500 0

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
namespace Across087500092500

theorem excluded0_0 : ExcludedOn (model0.B 0 ++ [step0.q]) 9000000000000 (model0.caps 0) (model0.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7850718750000, 2722500000000], [911062500000,
      -5445000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([8088937500000, 5445000000000],
      [1149281250000, -2722500000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([7374281250000,
      -2722500000000], [1149281250000, -2722500000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([7850718750000, 2722500000000], [1625718750000, 2722500000000]) (some (6, 1, 3)) (some (6, 1,
      3)) (.next ([7136062500000, -5445000000000], [1625718750000, 2722500000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([7374281250000, -2722500000000], [1863937500000, 5445000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([238218750000, 2722500000000], [238218750000,
      2722500000000]) (some (6, 1, 3)) (some (6, 1, 6)) (.next ([0, 0], [714656250000,
      8167500000000]) (some (6, 1, 6)) (some (6, 2, 6)) (.next ([-911062500000, 5445000000000],
      [8761781250000, -2722500000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([-1149281250000,
      2722500000000], [9238218750000, 2722500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
      ([-1149281250000, 2722500000000], [8523562500000, -5445000000000]) (some (0, 2, 6)) (some (0,
      2, 6)) (.next ([-1625718750000, -2722500000000], [9476437500000, 5445000000000]) (some (0, 2,
      6)) (some (0, 2, 6)) (.next ([-1625718750000, -2722500000000], [8761781250000,
      -2722500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1863937500000, -5445000000000],
      [9238218750000, 2722500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-238218750000,
      -2722500000000], [476437500000, 5445000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.terminal
      (some (0, 2, 6)) (some (1, 3, 6)) (some (1, 3, 6))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded0_1 : ExcludedOn (model0.B 1 ++ [step0.q]) 9000000000000 (model0.caps 1) (model0.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8212500000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([787500000000, 9000000000000],
      [787500000000, 9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([1575000000000,
      9000000000000], [7425000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([787500000000], [8212500000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [787500000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, -9000000000000],
      [8212500000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-787500000000, -9000000000000],
      [1575000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7425000000000,
      9000000000000], [9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8212500000000],
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8212500000000], [787500000000]) (some (1, 0, 3))
      (some (2, 0, 3)) (.next ([7612500000000], [787500000000, 9000000000000]) (some (2, 0, 3))
      (some (2, 0, 3)) (.next ([6825000000000], [1387500000000]) (some (2, 0, 3)) (some (2, 0, 3))
      (.next ([7425000000000, -9000000000000], [1575000000000, 9000000000000]) (some (2, 0, 1))
      (some (2, 0, 1)) (.next ([0], [787500000000, 9000000000000]) (some (2, 0, 1)) (some (2, 3, 1))
      (.next ([-787500000000], [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-787500000000, -9000000000000], [8400000000000, 9000000000000]) (some (0, 3, 1)) (some (0,
      3, 1)) (.next ([-1387500000000], [8212500000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-1575000000000, -9000000000000], [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1))
      (.terminal (some (0, 3, 1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_1 : ExcludedOn (model2.B 1 ++ [step2.q]) 9000000000000 (model2.caps 1) (model2.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7031250000000, 0], [1181250000000,
      -9000000000000]) (some (3, 1, 1)) (some (3, 1, 2)) (.next ([7818750000000, 9000000000000],
      [1968750000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([7031250000000], [1968750000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([787500000000, 9000000000000], [787500000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([0, 0], [787500000000,
      9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-1181250000000, 9000000000000],
      [8212500000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-1968750000000],
      [9787500000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1968750000000],
      [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-787500000000, -9000000000000],
      [1575000000000, 18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3))
      (some (1, 1, 3)) (some (1, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded2_2 : ExcludedOn (model2.B 2 ++ [step2.q]) 9000000000000 (model2.caps 2) (model2.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8212500000000, -9000000000000], [787500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([6243750000000, -9000000000000],
      [787500000000, 9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7031250000000, 0],
      [1181250000000, -9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([2531250000000],
      [1968750000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([787500000000, 9000000000000],
      [787500000000, 9000000000000]) (some (0, 0, 2)) (some (0, 0, 4)) (.next ([4500000000000, 0],
      [5287500000000, 9000000000000]) (some (0, 0, 4)) (some (0, 1, 4)) (.next ([3712500000000,
      -9000000000000], [4500000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([787500000000,
      9000000000000], [3712500000000, -9000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([0,
      0], [787500000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-787500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-787500000000,
      -9000000000000], [7031250000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-1181250000000, 9000000000000], [8212500000000, -9000000000000]) (some (0, 2, 4)) (some (0,
      2, 4)) (.next ([-1968750000000], [4500000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-787500000000, -9000000000000], [1575000000000, 18000000000000]) (some (0, 2, 4)) (some (0,
      2, 4)) (.next ([-5287500000000, -9000000000000], [9787500000000, 9000000000000]) (some (0, 2,
      4)) (some (0, 2, 4)) (.next ([-4500000000000, 0], [8212500000000, -9000000000000]) (some (0,
      2, 4)) (some (0, 2, 4)) (.next ([-3712500000000, 9000000000000], [4500000000000, 0]) (some (0,
      2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 0)) (some (0, 2,
      4))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8426437500000, 5445000000000], [436781250000,
      -2722500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([8188218750000, 2722500000000],
      [913218750000, 2722500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([7473562500000,
      -5445000000000], [913218750000, 2722500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([7711781250000, -2722500000000], [1151437500000, 5445000000000]) (some (4, 1, 5)) (some (4,
      1, 5)) (.next ([1025718750000, 2722500000000], [238218750000, 2722500000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([549281250000, -2722500000000], [476437500000, 5445000000000]) (some
      (4, 1, 5)) (some (4, 1, 5)) (.next ([238218750000, 2722500000000], [238218750000,
      2722500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([476437500000, 5445000000000],
      [549281250000, -2722500000000]) (some (4, 1, 5)) (some (4, 2, 5)) (.next ([238218750000,
      2722500000000], [1025718750000, 2722500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([112500000000], [7837500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([0, 0],
      [714656250000, 8167500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-436781250000,
      2722500000000], [8863218750000, 2722500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-913218750000, -2722500000000], [9101437500000, 5445000000000]) (some (0, 2, 5)) (some (0,
      2, 5)) (.next ([-913218750000, -2722500000000], [8386781250000, -2722500000000]) (some (0, 2,
      5)) (some (0, 2, 5)) (.next ([-1151437500000, -5445000000000], [8863218750000, 2722500000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-238218750000, -2722500000000], [1263937500000,
      5445000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-476437500000, -5445000000000],
      [1025718750000, 2722500000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-238218750000,
      -2722500000000], [476437500000, 5445000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next
      ([-549281250000, 2722500000000], [1025718750000, 2722500000000]) (some (0, 5, 5)) (some (1, 5,
      5)) (.next ([-1025718750000, -2722500000000], [1263937500000, 5445000000000]) (some (1, 5, 5))
      (some (1, 5, 5)) (.next ([-7837500000000], [7950000000000]) (some (1, 5, 5)) (some (1, 5, 5))
      (.terminal (some (1, 5, 4)) (some (1, 5, 4)) (some (1, 5, 4))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8325000000000, 0], [412500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([8212500000000, -9000000000000],
      [787500000000, 9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([262500000000,
      -9000000000000], [112500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([787500000000, 9000000000000], [787500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([4500000000000, 0], [5287500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([3712500000000, -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([1050000000000], [3825000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([787500000000, 9000000000000], [3712500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([375000000000, 0], [7162500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([375000000000], [7950000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [787500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-412500000000,
      -9000000000000], [8737500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-787500000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-112500000000, -9000000000000], [375000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-787500000000, -9000000000000], [1575000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-5287500000000, -9000000000000], [9787500000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8212500000000, -9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-3825000000000], [4875000000000]) (some (0, 4, 3)) (some (0,
      4, 3)) (.next ([-3712500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-7162500000000, 9000000000000], [7537500000000, -9000000000000]) (some (0, 2,
      3)) (some (0, 2, 3)) (.next ([-7950000000000], [8325000000000]) (some (0, 2, 3)) (some (0, 2,
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7406250000000], [918750000000]) (some (0, 4, 2))
      (some (0, 4, 3)) (.next ([7031250000000, 0], [1181250000000, -9000000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([262500000000, -9000000000000], [112500000000, 9000000000000]) (some
      (0, 4, 3)) (some (0, 4, 3)) (.next ([787500000000, 9000000000000], [1181250000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([1050000000000], [7537500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([1050000000000], [8325000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([787500000000, 9000000000000], [7425000000000,
      -18000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([787500000000, 9000000000000],
      [8212500000000, -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([0],
      [1968750000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-918750000000], [8325000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1181250000000, 9000000000000], [8212500000000,
      -9000000000000]) (some (0, 4, 3)) (some (4, 4, 3)) (.next ([-112500000000, -9000000000000],
      [375000000000, 0]) (some (4, 4, 3)) (some (4, 4, 3)) (.next ([-1181250000000, 9000000000000],
      [1968750000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-7537500000000, 9000000000000],
      [8587500000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-8325000000000],
      [9375000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-7425000000000, 18000000000000],
      [8212500000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-8212500000000,
      9000000000000], [9000000000000, 0]) (some (4, 1, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8212500000000, -9000000000000], [787500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([5625000000000], [3375000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([4837500000000, -9000000000000], [3375000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([5625000000000, 0], [4162500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([787500000000, 9000000000000], [787500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [5287500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3712500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([787500000000, 9000000000000],
      [2587500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([787500000000,
      9000000000000], [3712500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      0], [787500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-787500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-3375000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3375000000000,
      0], [8212500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4162500000000, -9000000000000], [9787500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-787500000000, -9000000000000], [1575000000000, 18000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-5287500000000, -9000000000000], [9787500000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8212500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2587500000000, 9000000000000],
      [3375000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3712500000000, 9000000000000],
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7031250000000, 0], [1181250000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([3656250000000], [1968750000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([787500000000, 9000000000000], [1181250000000,
      -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([787500000000, 9000000000000],
      [2587500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([787500000000,
      9000000000000], [7425000000000, -18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([787500000000, 9000000000000], [8212500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([0], [1968750000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1181250000000,
      9000000000000], [8212500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1968750000000], [5625000000000]) (some (0, 1, 3)) (some (1, 1, 3)) (.next ([-1181250000000,
      9000000000000], [1968750000000]) (some (1, 1, 3)) (some (1, 1, 3)) (.next ([-2587500000000,
      9000000000000], [3375000000000, 0]) (some (1, 1, 3)) (some (1, 1, 3)) (.next ([-7425000000000,
      18000000000000], [8212500000000, -9000000000000]) (some (1, 1, 3)) (some (1, 4, 3)) (.next
      ([-8212500000000, 9000000000000], [9000000000000, 0]) (some (1, 4, 3)) (some (1, 4, 3))
      (.terminal (some (1, 4, 3)) (some (1, 2, 0)) (some (1, 4, 3))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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

end Across087500092500
end ConwaySoifer.Simplified.Certificates
