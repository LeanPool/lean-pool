/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across027500032500
import Mathlib.Tactic.FinCases

/-!
# Across 027500 032500 0

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
namespace Across027500032500

theorem excluded0_0 : ExcludedOn (model0.B 0 ++ [step0.q]) 9000000000000 (model0.caps 0) (model0.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8074818750000, 2902500000000], [1340362500000,
      -5805000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next ([8154637500000, 5805000000000],
      [1420181250000, -2902500000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([7915181250000,
      -2902500000000], [1420181250000, -2902500000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([8074818750000, 2902500000000], [1579818750000, 2902500000000]) (some (5, 1, 6)) (some (5, 1,
      6)) (.next ([7835362500000, -5805000000000], [1579818750000, 2902500000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([7915181250000, -2902500000000], [1659637500000, 5805000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([79818750000, 2902500000000], [79818750000,
      2902500000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0], [239456250000,
      8707500000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-1340362500000, 5805000000000],
      [9415181250000, -2902500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1420181250000,
      2902500000000], [9574818750000, 2902500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
      ([-1420181250000, 2902500000000], [9335362500000, -5805000000000]) (some (0, 2, 6)) (some (0,
      2, 6)) (.next ([-1579818750000, -2902500000000], [9654637500000, 5805000000000]) (some (0, 2,
      6)) (some (0, 2, 6)) (.next ([-1579818750000, -2902500000000], [9415181250000,
      -2902500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1659637500000, -5805000000000],
      [9574818750000, 2902500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-79818750000,
      -2902500000000], [159637500000, 5805000000000]) (some (0, 2, 6)) (some (0, 6, 6)) (.terminal
      (some (0, 6, 6)) (some (1, 6, 6)) (some (1, 6, 6))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded0_1 : ExcludedOn (model0.B 1 ++ [step0.q]) 9000000000000 (model0.caps 1) (model0.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([247500000000, 9000000000000], [247500000000,
      9000000000000]) none none (.next ([742500000000, 9000000000000], [1005000000000]) none none
      (.next ([495000000000, 0], [757500000000, -9000000000000]) none none (.next ([495000000000],
      [1005000000000]) none none (.next ([0, 0], [247500000000, 9000000000000]) none none (.next
      ([-247500000000, -9000000000000], [495000000000, 18000000000000]) none none (.next
      ([-1005000000000], [1747500000000, 9000000000000]) none none (.next ([-757500000000,
      9000000000000], [1252500000000, -9000000000000]) none none (.next ([-1005000000000],
      [1500000000000]) none none (.terminal none none none))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded0_2 : ExcludedOn (model0.B 2 ++ [step0.q]) 9000000000000 (model0.caps 2) (model0.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8752500000000, -9000000000000], [247500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7500000000000], [495000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7252500000000, -9000000000000], [495000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7500000000000, 0], [742500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([247500000000, 9000000000000], [247500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [4747500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4252500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([495000000000, 0],
      [757500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1005000000000],
      [3000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([247500000000, 9000000000000],
      [4252500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [247500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-247500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-495000000000], [7995000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-495000000000,
      0], [7747500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-742500000000,
      -9000000000000], [8242500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-247500000000, -9000000000000], [495000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-4747500000000, -9000000000000], [9247500000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8752500000000, -9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-757500000000, 9000000000000], [1252500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3000000000000], [4005000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4252500000000, 9000000000000], [4500000000000, 0])
      (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2,
      3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

theorem excluded0_3 : ExcludedOn (model0.B 3 ++ [step0.q]) 9000000000000 (model0.caps 3) (model0.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded0_3
    · exact excluded0_4
    · exact excluded0_5
    · exact excluded0_6
    · exact (hj rfl).elim
    · exact excluded0_8
    · exact excluded0_9
theorem next0 : model0.insert step0 = model1 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded1_0 : ExcludedOn (model1.B 0 ++ [step1.q]) 9000000000000 (model1.caps 0) (model1.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_2 : ExcludedOn (model1.B 2 ++ [step1.q]) 9000000000000 (model1.caps 2) (model1.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8752500000000, -9000000000000], [247500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7020000000000], [1980000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([6772500000000, -9000000000000], [1980000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7020000000000, 0], [2227500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([247500000000, 9000000000000], [247500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [4747500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4252500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([247500000000, 9000000000000],
      [1732500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([247500000000,
      9000000000000], [4252500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      0], [247500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-247500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1980000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1980000000000,
      0], [8752500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-2227500000000, -9000000000000], [9247500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-247500000000, -9000000000000], [495000000000, 18000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-4747500000000, -9000000000000], [9247500000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8752500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1732500000000, 9000000000000],
      [1980000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4252500000000, 9000000000000],
      [4500000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4, 3)) (some (0, 2,
      0)) (some (0, 4, 3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded1_3 : ExcludedOn (model1.B 3 ++ [step1.q]) 9000000000000 (model1.caps 3) (model1.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6772500000000, -9000000000000], [247500000000,
      9000000000000]) (some (3, 1, 2)) (some (4, 1, 3)) (.next ([1005000000000], [480000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([495000000000, 0], [757500000000, -9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([247500000000, 9000000000000], [1732500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1005000000000], [7252500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1005000000000], [7500000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([757500000000, -9000000000000], [7500000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([247500000000, 9000000000000], [8505000000000,
      -18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([247500000000, 9000000000000],
      [8752500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [8752500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-247500000000,
      -9000000000000], [7020000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-480000000000],
      [1485000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-757500000000, 9000000000000],
      [1252500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1732500000000,
      9000000000000], [1980000000000, 0]) (some (0, 1, 3)) (some (1, 1, 3)) (.next ([-7252500000000,
      9000000000000], [8257500000000, -9000000000000]) (some (1, 1, 3)) (some (1, 5, 3)) (.next
      ([-7500000000000], [8505000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-7500000000000,
      0], [8257500000000, -9000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next
      ([-8505000000000, 18000000000000], [8752500000000, -9000000000000]) (some (1, 5, 3)) (some (1,
      5, 3)) (.next ([-8752500000000, 9000000000000], [9000000000000, 0]) (some (1, 5, 3)) (some (1,
      5, 3)) (.terminal (some (1, 5, 3)) (some (1, 2, 3)) (some (1, 5, 3))))))))))))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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
    · exact excluded1_0
    · exact (hj rfl).elim
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

theorem excluded2_1 : ExcludedOn (model2.B 1 ++ [step2.q]) 9000000000000 (model2.caps 1) (model2.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([753750000000, -9000000000000], [123750000000,
      0]) none none (.next ([1125000000000], [978750000000]) none none (.next ([247500000000,
      9000000000000], [247500000000, 9000000000000]) none none (.next ([247500000000,
      9000000000000], [1732500000000, -9000000000000]) none none (.next ([123750000000,
      9000000000000], [1125000000000]) none none (.next ([0], [2227500000000, 9000000000000]) none
      none (.next ([-123750000000, 0], [877500000000, -9000000000000]) none none (.next
      ([-978750000000], [2103750000000]) none none (.next ([-247500000000, -9000000000000],
      [495000000000, 18000000000000]) none none (.next ([-1732500000000, 9000000000000],
      [1980000000000, 0]) none none (.next ([-1125000000000], [1248750000000, 9000000000000]) none
      none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded2_2 : ExcludedOn (model2.B 2 ++ [step2.q]) 9000000000000 (model2.caps 2) (model2.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7998750000000, 0], [123750000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([8752500000000, -9000000000000],
      [247500000000, 9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([753750000000,
      -9000000000000], [123750000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([247500000000,
      9000000000000], [247500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4500000000000, 0], [4747500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4252500000000, -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([1125000000000], [3498750000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([247500000000,
      9000000000000], [4252500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([123750000000, 0], [7627500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([123750000000], [7875000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [247500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-123750000000,
      -9000000000000], [8122500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-247500000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-123750000000, 0], [877500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-247500000000, -9000000000000], [495000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-4747500000000, -9000000000000], [9247500000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8752500000000, -9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-3498750000000], [4623750000000]) (some (0, 4, 3)) (some (0,
      4, 3)) (.next ([-4252500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-7627500000000, 9000000000000], [7751250000000, -9000000000000]) (some (0, 2,
      3)) (some (0, 2, 3)) (.next ([-7875000000000], [7998750000000]) (some (0, 2, 3)) (some (0, 2,
      3)) (.terminal (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2, 3))))))))))))))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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

theorem excluded2_7 : ExcludedOn (model2.B 7 ++ [step2.q]) 9000000000000 (model2.caps 7) (model2.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([753750000000, -9000000000000], [123750000000,
      0]) (some (3, 5, 2)) (some (4, 5, 3)) (.next ([495000000000, 0], [757500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([120000000000], [498750000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1125000000000], [7751250000000, -9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1125000000000], [7998750000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([1005000000000], [7252500000000, -9000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([1005000000000], [7500000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([877500000000, -9000000000000], [7998750000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([757500000000, -9000000000000], [7500000000000]) (some (4, 1, 3)) (some (5, 1, 3))
      (.next ([247500000000, 9000000000000], [8505000000000, -18000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([247500000000, 9000000000000], [8752500000000, -9000000000000]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 0], [8752500000000, -9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-123750000000, 0], [877500000000, -9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-757500000000, 9000000000000], [1252500000000, -9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-498750000000], [618750000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-7751250000000, 9000000000000], [8876250000000, -9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-7998750000000], [9123750000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-7252500000000, 9000000000000], [8257500000000, -9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-7500000000000], [8505000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-7998750000000, 0], [8876250000000, -9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-7500000000000, 0], [8257500000000, -9000000000000]) (some (5,
      1, 3)) (some (5, 1, 3)) (.next ([-8505000000000, 18000000000000], [8752500000000,
      -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-8752500000000, 9000000000000],
      [9000000000000, 0]) (some (5, 1, 3)) (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 2,
      3)) (some (5, 2, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded2_1
    · exact excluded2_2
    · exact excluded2_3
    · exact excluded2_4
    · exact excluded2_5
    · exact excluded2_6
    · exact excluded2_7
    · exact excluded2_8
    · exact excluded2_9
theorem next2 : model2.insert step2 = model3 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded3_1 : ExcludedOn (model3.B 1 ++ [step3.q]) 9000000000000 (model3.caps 1) (model3.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([330000000000, 9000000000000], [45000000000,
      -9000000000000]) none none (.next ([247500000000, 9000000000000], [247500000000,
      9000000000000]) none none (.next ([127500000000, -9000000000000], [165000000000,
      9000000000000]) none none (.next ([375000000000], [1897500000000]) none none (.next
      ([247500000000, 9000000000000], [1732500000000, -9000000000000]) none none (.next ([0],
      [2227500000000, 9000000000000]) none none (.next ([-45000000000, 9000000000000],
      [375000000000]) none none (.next ([-247500000000, -9000000000000], [495000000000,
      18000000000000]) none none (.next ([-165000000000, -9000000000000], [292500000000, 0]) none
      none (.next ([-1897500000000], [2272500000000]) none none (.next ([-1732500000000,
      9000000000000], [1980000000000, 0]) none none (.terminal none none none))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8752500000000, -9000000000000], [247500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([247500000000, 9000000000000],
      [247500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0],
      [4747500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4252500000000,
      -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([127500000000,
      -9000000000000], [165000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([375000000000], [4417500000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([247500000000,
      9000000000000], [4252500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([292500000000, 0], [8377500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([292500000000], [8625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([45000000000,
      -9000000000000], [8872500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      0], [247500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-247500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-247500000000,
      -9000000000000], [495000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4747500000000, -9000000000000], [9247500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 3)) (.next ([-4500000000000, 0], [8752500000000, -9000000000000]) (some (0, 4, 3)) (some
      (0, 4, 3)) (.next ([-165000000000, -9000000000000], [292500000000, 0]) (some (0, 4, 3)) (some
      (0, 4, 3)) (.next ([-4417500000000], [4792500000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-4252500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8377500000000, 9000000000000], [8670000000000, -9000000000000]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-8625000000000], [8917500000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8872500000000, -9000000000000], [8917500000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.terminal (some (0, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded3_1
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

end Across027500032500
end ConwaySoifer.Simplified.Certificates
