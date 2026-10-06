/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across022500027500
import Mathlib.Tactic.FinCases

/-!
# Across 022500 027500 0

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
namespace Across022500027500

theorem excluded0_0 : ExcludedOn (model0.B 0 ++ [step0.q]) 9000000000000 (model0.caps 0) (model0.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([65643750000, 2917500000000], [65643750000,
      2917500000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([536287500000, 5835000000000],
      [8529356250000, -2917500000000]) (some (6, 1, 3)) (some (6, 2, 4)) (.next ([470643750000,
      2917500000000], [8463712500000, -5835000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
      ([470643750000, 2917500000000], [8660643750000, 2917500000000]) (some (6, 2, 4)) (some (6, 2,
      4)) (.next ([339356250000, -2917500000000], [8529356250000, -2917500000000]) (some (6, 2, 4))
      (some (6, 2, 4)) (.next ([339356250000, -2917500000000], [8726287500000, 5835000000000]) (some
      (6, 2, 4)) (some (6, 2, 4)) (.next ([273712500000, -5835000000000], [8660643750000,
      2917500000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([0, 0], [196931250000,
      8752500000000]) (some (6, 2, 4)) (some (6, 2, 6)) (.next ([-65643750000, -2917500000000],
      [131287500000, 5835000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([-8529356250000,
      2917500000000], [9065643750000, 2917500000000]) (some (6, 2, 6)) (some (6, 3, 6)) (.next
      ([-8463712500000, 5835000000000], [8934356250000, -2917500000000]) (some (1, 3, 6)) (some (1,
      3, 6)) (.next ([-8660643750000, -2917500000000], [9131287500000, 5835000000000]) (some (1, 3,
      6)) (some (1, 3, 6)) (.next ([-8529356250000, 2917500000000], [8868712500000, -5835000000000])
      (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-8726287500000, -5835000000000], [9065643750000,
      2917500000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-8660643750000, -2917500000000],
      [8934356250000, -2917500000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.terminal (some (1, 3, 6))
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8797500000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([202500000000, 9000000000000],
      [202500000000, 9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([405000000000,
      9000000000000], [8595000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([202500000000], [8797500000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [202500000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, -9000000000000],
      [8797500000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-202500000000, -9000000000000],
      [405000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8595000000000,
      9000000000000], [9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8797500000000],
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8797500000000], [202500000000]) (some (1, 0, 3))
      (some (2, 0, 3)) (.next ([8595000000000, -9000000000000], [405000000000, 9000000000000]) (some
      (2, 0, 3)) (some (2, 0, 3)) (.next ([405000000000], [202500000000, 9000000000000]) (some (2,
      0, 3)) (some (2, 3, 3)) (.next ([202500000000], [8595000000000]) (some (2, 3, 3)) (some (2, 3,
      3)) (.next ([0], [202500000000, 9000000000000]) (some (2, 3, 1)) (some (2, 3, 1)) (.next
      ([-202500000000], [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-405000000000,
      -9000000000000], [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-202500000000,
      -9000000000000], [607500000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-8595000000000], [8797500000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3,
      1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8100000000000], [1102500000000]) (some (5, 1,
      5)) (some (5, 1, 5)) (.next ([8231287500000, 5835000000000], [1239356250000, -2917500000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([8165643750000, 2917500000000], [1370643750000,
      2917500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([7968712500000, -5835000000000],
      [1370643750000, 2917500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([8034356250000,
      -2917500000000], [1436287500000, 5835000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([268143750000, 2917500000000], [65643750000, 2917500000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([131287500000, 5835000000000], [136856250000, -2917500000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([65643750000, 2917500000000], [268143750000, 2917500000000]) (some
      (0, 1, 5)) (some (0, 2, 5)) (.next ([0, 0], [196931250000, 8752500000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-1102500000000], [9202500000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-1239356250000, 2917500000000], [9470643750000, 2917500000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-1370643750000, -2917500000000], [9536287500000, 5835000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1370643750000, -2917500000000], [9339356250000,
      -2917500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1436287500000, -5835000000000],
      [9470643750000, 2917500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-65643750000,
      -2917500000000], [333787500000, 5835000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next
      ([-136856250000, 2917500000000], [268143750000, 2917500000000]) (some (0, 5, 5)) (some (0, 5,
      5)) (.next ([-268143750000, -2917500000000], [333787500000, 5835000000000]) (some (0, 5, 5))
      (some (1, 5, 5)) (.terminal (some (1, 5, 5)) (some (1, 5, 5)) (some (1, 5,
      5))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

theorem excluded2_1 : ExcludedOn (model2.B 1 ++ [step2.q]) 9000000000000 (model2.caps 1) (model2.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([202500000000, 9000000000000], [202500000000,
      9000000000000]) none none (.next ([607500000000, 9000000000000], [900000000000]) none none
      (.next ([405000000000, 0], [697500000000, -9000000000000]) none none (.next ([405000000000],
      [900000000000]) none none (.next ([0, 0], [202500000000, 9000000000000]) none none (.next
      ([-202500000000, -9000000000000], [405000000000, 18000000000000]) none none (.next
      ([-900000000000], [1507500000000, 9000000000000]) none none (.next ([-697500000000,
      9000000000000], [1102500000000, -9000000000000]) none none (.next ([-900000000000],
      [1305000000000]) none none (.terminal none none none))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded2_2 : ExcludedOn (model2.B 2 ++ [step2.q]) 9000000000000 (model2.caps 2) (model2.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8797500000000, -9000000000000], [202500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7695000000000], [405000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7492500000000, -9000000000000], [405000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7695000000000, 0], [607500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([202500000000, 9000000000000], [202500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [4702500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4297500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([405000000000, 0],
      [697500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([900000000000],
      [3195000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([202500000000, 9000000000000],
      [4297500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [202500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-202500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-405000000000], [8100000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-405000000000,
      0], [7897500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-607500000000,
      -9000000000000], [8302500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-202500000000, -9000000000000], [405000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-4702500000000, -9000000000000], [9202500000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8797500000000, -9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-697500000000, 9000000000000], [1102500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3195000000000], [4095000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4297500000000, 9000000000000], [4500000000000, 0])
      (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2,
      3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8797500000000, -9000000000000], [202500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7380000000000], [1620000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7177500000000, -9000000000000], [1620000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7380000000000, 0], [1822500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([202500000000, 9000000000000], [202500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [4702500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4297500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([202500000000, 9000000000000],
      [1417500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([202500000000,
      9000000000000], [4297500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      0], [202500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-202500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1620000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1620000000000,
      0], [8797500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1822500000000, -9000000000000], [9202500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-202500000000, -9000000000000], [405000000000, 18000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-4702500000000, -9000000000000], [9202500000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8797500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1417500000000, 9000000000000],
      [1620000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4297500000000, 9000000000000],
      [4500000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4, 3)) (some (0, 2,
      0)) (some (0, 4, 3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7177500000000, -9000000000000], [202500000000,
      9000000000000]) (some (3, 1, 2)) (some (4, 1, 3)) (.next ([900000000000], [315000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([405000000000, 0], [697500000000, -9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([202500000000, 9000000000000], [1417500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([900000000000], [7492500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([900000000000], [7695000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([697500000000, -9000000000000], [7695000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([202500000000, 9000000000000], [8595000000000,
      -18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([202500000000, 9000000000000],
      [8797500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [8797500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-202500000000,
      -9000000000000], [7380000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-315000000000],
      [1215000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-697500000000, 9000000000000],
      [1102500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1417500000000,
      9000000000000], [1620000000000, 0]) (some (0, 1, 3)) (some (1, 1, 3)) (.next ([-7492500000000,
      9000000000000], [8392500000000, -9000000000000]) (some (1, 1, 3)) (some (1, 5, 3)) (.next
      ([-7695000000000], [8595000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-7695000000000,
      0], [8392500000000, -9000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next
      ([-8595000000000, 18000000000000], [8797500000000, -9000000000000]) (some (1, 5, 3)) (some (1,
      5, 3)) (.next ([-8797500000000, 9000000000000], [9000000000000, 0]) (some (1, 5, 3)) (some (1,
      5, 3)) (.terminal (some (1, 5, 3)) (some (1, 2, 3)) (some (1, 5, 3))))))))))))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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

theorem excluded4_1 : ExcludedOn (model4.B 1 ++ [step4.q]) 9000000000000 (model4.caps 1) (model4.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([202500000000, 9000000000000], [202500000000,
      9000000000000]) none none (.next ([202500000000, 9000000000000], [1417500000000,
      -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([202500000000, 9000000000000],
      [8493750000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([0],
      [1822500000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-202500000000,
      -9000000000000], [405000000000, 18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1417500000000, 9000000000000], [1620000000000, 0]) (some (0, 1, 3)) (some (1, 1, 3)) (.next
      ([-8493750000000, 9000000000000], [8696250000000, 0]) (some (1, 1, 3)) (some (1, 1, 3))
      (.terminal (some (1, 1, 3)) none none))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded4_2 : ExcludedOn (model4.B 2 ++ [step4.q]) 9000000000000 (model4.caps 2) (model4.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
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
    · exact excluded4_1
    · exact excluded4_2
    · exact excluded4_3
    · exact excluded4_4
    · exact excluded4_5
    · exact excluded4_6
    · exact (hj rfl).elim
    · exact excluded4_8
    · exact excluded4_9
theorem next4 : model4.insert step4 = model5 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded5_1 : ExcludedOn (model5.B 1 ++ [step5.q]) 9000000000000 (model5.caps 1) (model5.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([697500000000, -9000000000000], [101250000000,
      0]) none none (.next ([1001250000000], [720000000000]) none none (.next ([202500000000,
      9000000000000], [202500000000, 9000000000000]) none none (.next ([202500000000,
      9000000000000], [1417500000000, -9000000000000]) none none (.next ([101250000000,
      9000000000000], [1001250000000]) none none (.next ([0], [1822500000000, 9000000000000]) none
      none (.next ([-101250000000, 0], [798750000000, -9000000000000]) none none (.next
      ([-720000000000], [1721250000000]) none none (.next ([-202500000000, -9000000000000],
      [405000000000, 18000000000000]) none none (.next ([-1417500000000, 9000000000000],
      [1620000000000, 0]) none none (.next ([-1001250000000], [1102500000000, 9000000000000]) none
      none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded5_2 : ExcludedOn (model5.B 2 ++ [step5.q]) 9000000000000 (model5.caps 2) (model5.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8100000000000, 0], [101250000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([8797500000000, -9000000000000],
      [202500000000, 9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([697500000000,
      -9000000000000], [101250000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([202500000000,
      9000000000000], [202500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4500000000000, 0], [4702500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4297500000000, -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([1001250000000], [3600000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([202500000000,
      9000000000000], [4297500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([101250000000, 0], [7796250000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([101250000000], [7998750000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [202500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-101250000000,
      -9000000000000], [8201250000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-202500000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-101250000000, 0], [798750000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-202500000000, -9000000000000], [405000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-4702500000000, -9000000000000], [9202500000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8797500000000, -9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-3600000000000], [4601250000000]) (some (0, 4, 3)) (some (0,
      4, 3)) (.next ([-4297500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-7796250000000, 9000000000000], [7897500000000, -9000000000000]) (some (0, 2,
      3)) (some (0, 2, 3)) (.next ([-7998750000000], [8100000000000]) (some (0, 2, 3)) (some (0, 2,
      3)) (.terminal (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2, 3))))))))))))))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded5_3 : ExcludedOn (model5.B 3 ++ [step5.q]) 9000000000000 (model5.caps 3) (model5.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded5_4 : ExcludedOn (model5.B 4 ++ [step5.q]) 9000000000000 (model5.caps 4) (model5.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded5_5 : ExcludedOn (model5.B 5 ++ [step5.q]) 9000000000000 (model5.caps 5) (model5.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded5_6 : ExcludedOn (model5.B 6 ++ [step5.q]) 9000000000000 (model5.caps 6) (model5.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded5_7 : ExcludedOn (model5.B 7 ++ [step5.q]) 9000000000000 (model5.caps 7) (model5.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([697500000000, -9000000000000], [101250000000,
      0]) (some (3, 5, 2)) (some (4, 5, 3)) (.next ([405000000000, 0], [697500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([101250000000, -9000000000000],
      [202500000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1001250000000],
      [7796250000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1001250000000], [8100000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([900000000000], [7391250000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([900000000000], [7695000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([798750000000, -9000000000000], [8100000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([697500000000, -9000000000000], [7695000000000]) (some (4, 1, 3)) (some (5, 1, 3))
      (.next ([202500000000, 9000000000000], [8493750000000, -9000000000000]) (some (5, 1, 3)) (some
      (5, 1, 3)) (.next ([202500000000, 9000000000000], [8797500000000, -9000000000000]) (some (5,
      1, 3)) (some (5, 1, 3)) (.next ([0, 0], [8797500000000, -9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-101250000000, 0], [798750000000, -9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-697500000000, 9000000000000], [1102500000000, -9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-202500000000, -9000000000000], [303750000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-7796250000000], [8797500000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-8100000000000], [9101250000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([-7391250000000], [8291250000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-7695000000000], [8595000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-8100000000000,
      0], [8898750000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-7695000000000, 0], [8392500000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([-8493750000000, 9000000000000], [8696250000000, 0]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([-8797500000000, 9000000000000], [9000000000000, 0]) (some (5, 1, 3)) (some (5, 2, 3))
      (.terminal (some (5, 2, 3)) (some (5, 2, 3)) (some (5, 2, 3))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded5_8 : ExcludedOn (model5.B 8 ++ [step5.q]) 9000000000000 (model5.caps 8) (model5.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded5_9 : ExcludedOn (model5.B 9 ++ [step5.q]) 9000000000000 (model5.caps 9) (model5.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked5 : StepValid model5 9000000000000 step5 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded5_1
    · exact excluded5_2
    · exact excluded5_3
    · exact excluded5_4
    · exact excluded5_5
    · exact excluded5_6
    · exact excluded5_7
    · exact excluded5_8
    · exact excluded5_9
theorem next5 : model5.insert step5 = model6 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded6_1 : ExcludedOn (model6.B 1 ++ [step6.q]) 9000000000000 (model6.caps 1) (model6.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([303750000000, 9000000000000], [71250000000,
      -9000000000000]) none none (.next ([172500000000, -9000000000000], [101250000000,
      9000000000000]) none none (.next ([375000000000], [1518750000000]) none none (.next
      ([202500000000, 9000000000000], [1417500000000, -9000000000000]) none none (.next ([0],
      [1822500000000, 9000000000000]) none none (.next ([-71250000000, 9000000000000],
      [375000000000]) none none (.next ([-101250000000, -9000000000000], [273750000000, 0]) none
      none (.next ([-1518750000000], [1893750000000]) none none (.next ([-1417500000000,
      9000000000000], [1620000000000, 0]) none none (.terminal none none none))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded6_2 : ExcludedOn (model6.B 2 ++ [step6.q]) 9000000000000 (model6.caps 2) (model6.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8797500000000, -9000000000000], [202500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([172500000000, -9000000000000],
      [101250000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([375000000000],
      [4398750000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([202500000000, 9000000000000],
      [4297500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([273750000000, 0],
      [8422500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([273750000000],
      [8625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([71250000000, -9000000000000],
      [8827500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [202500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-202500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-101250000000,
      -9000000000000], [273750000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4398750000000], [4773750000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-4297500000000,
      9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-8422500000000,
      9000000000000], [8696250000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8625000000000], [8898750000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-8827500000000,
      -9000000000000], [8898750000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded6_3 : ExcludedOn (model6.B 3 ++ [step6.q]) 9000000000000 (model6.caps 3) (model6.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded6_4 : ExcludedOn (model6.B 4 ++ [step6.q]) 9000000000000 (model6.caps 4) (model6.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded6_5 : ExcludedOn (model6.B 5 ++ [step6.q]) 9000000000000 (model6.caps 5) (model6.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded6_6 : ExcludedOn (model6.B 6 ++ [step6.q]) 9000000000000 (model6.caps 6) (model6.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded6_7 : ExcludedOn (model6.B 7 ++ [step6.q]) 9000000000000 (model6.caps 7) (model6.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded6_8 : ExcludedOn (model6.B 8 ++ [step6.q]) 9000000000000 (model6.caps 8) (model6.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded6_9 : ExcludedOn (model6.B 9 ++ [step6.q]) 9000000000000 (model6.caps 9) (model6.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked6 : StepValid model6 9000000000000 step6 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded6_1
    · exact excluded6_2
    · exact excluded6_3
    · exact excluded6_4
    · exact excluded6_5
    · exact excluded6_6
    · exact excluded6_7
    · exact excluded6_8
    · exact excluded6_9
theorem next6 : model6.insert step6 = model7 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Across022500027500
end ConwaySoifer.Simplified.Certificates
