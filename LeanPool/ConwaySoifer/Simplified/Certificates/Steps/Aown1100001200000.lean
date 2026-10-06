/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown110000120000
import Mathlib.Tactic.FinCases

/-!
# Aown 110000 120000 0

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
namespace Aown110000120000

theorem excluded0_1 : ExcludedOn (model0.B 1 ++ [step0.q]) 9000000000000 (model0.caps 1) (model0.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_2 : ExcludedOn (model0.B 2 ++ [step0.q]) 9000000000000 (model0.caps 2) (model0.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8010000000000], [990000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([8010000000000, -9000000000000], [990000000000, 9000000000000]) (some
      (0, 3, 1)) (some (0, 3, 1)) (.next ([7020000000000, -9000000000000], [990000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([7020000000000, -9000000000000],
      [1980000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([990000000000,
      9000000000000], [990000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0,
      9000000000000], [8010000000000, -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0,
      0], [990000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-990000000000],
      [9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([-990000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-990000000000, -9000000000000],
      [8010000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-1980000000000,
      -9000000000000], [9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-990000000000,
      -9000000000000], [1980000000000, 18000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next
      ([-8010000000000, 9000000000000], [8010000000000, 0]) (some (3, 3, 2)) (some (3, 3, 2))
      (.terminal (some (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded0_3 : ExcludedOn (model0.B 3 ++ [step0.q]) 9000000000000 (model0.caps 3) (model0.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_4 : ExcludedOn (model0.B 4 ++ [step0.q]) 9000000000000 (model0.caps 4) (model0.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_5 : ExcludedOn (model0.B 5 ++ [step0.q]) 9000000000000 (model0.caps 5) (model0.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_6 : ExcludedOn (model0.B 6 ++ [step0.q]) 9000000000000 (model0.caps 6) (model0.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8010000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([990000000000, 9000000000000],
      [990000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1980000000000,
      9000000000000], [7020000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([990000000000], [8010000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [990000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, -9000000000000],
      [8010000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-990000000000, -9000000000000],
      [1980000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-7020000000000,
      9000000000000], [9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-8010000000000],
      [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1,
      3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_7 : ExcludedOn (model0.B 7 ++ [step0.q]) 9000000000000 (model0.caps 7) (model0.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_8 : ExcludedOn (model0.B 8 ++ [step0.q]) 9000000000000 (model0.caps 8) (model0.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_9 : ExcludedOn (model0.B 9 ++ [step0.q]) 9000000000000 (model0.caps 9) (model0.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked0 : StepValid model0 9000000000000 step0 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded0_1
    · exact excluded0_2
    · exact excluded0_3
    · exact excluded0_4
    · exact excluded0_5
    · exact excluded0_6
    · exact excluded0_7
    · exact excluded0_8
    · exact excluded0_9
theorem next0 : model0.insert step0 = model1 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded1_0 : ExcludedOn (model1.B 0 ++ [step1.q]) 9000000000000 (model1.caps 0) (model1.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1280400000000, 2640000000000], [290400000000,
      2640000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([699600000000, -2640000000000],
      [580800000000, 5280000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([290400000000,
      2640000000000], [290400000000, 2640000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
      ([580800000000, 5280000000000], [699600000000, -2640000000000]) (some (5, 1, 5)) (some (5, 2,
      5)) (.next ([2605800000000, 5280000000000], [6684600000000, -2640000000000]) (some (5, 2, 5))
      (some (5, 2, 5)) (.next ([2315400000000, 2640000000000], [6394200000000, -5280000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([2315400000000, 2640000000000], [7265400000000,
      2640000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([290400000000, 2640000000000],
      [1280400000000, 2640000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([1035000000000],
      [6975000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([0, 0], [871200000000,
      7920000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-290400000000, -2640000000000],
      [1570800000000, 5280000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-580800000000,
      -5280000000000], [1280400000000, 2640000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-290400000000, -2640000000000], [580800000000, 5280000000000]) (some (0, 2, 5)) (some (0, 3,
      5)) (.next ([-699600000000, 2640000000000], [1280400000000, 2640000000000]) (some (0, 3, 5))
      (some (1, 3, 5)) (.next ([-6684600000000, 2640000000000], [9290400000000, 2640000000000])
      (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-6394200000000, 5280000000000], [8709600000000,
      -2640000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-7265400000000, -2640000000000],
      [9580800000000, 5280000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-1280400000000,
      -2640000000000], [1570800000000, 5280000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-6975000000000], [8010000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.terminal (some (1, 3,
      5)) (some (1, 5, 5)) (some (1, 5, 5))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded1_1 : ExcludedOn (model1.B 1 ++ [step1.q]) 9000000000000 (model1.caps 1) (model1.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([990000000000, 9000000000000], [990000000000,
      9000000000000]) none none (.next ([2475000000000], [4500000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([990000000000, 9000000000000], [3510000000000, -9000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([990000000000, 9000000000000], [6975000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0, 0], [5985000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-4500000000000], [6975000000000]) (some (3, 1, 2)) none (.next
      ([-3510000000000, 9000000000000], [4500000000000, 0]) none none (.next ([-6975000000000],
      [7965000000000, 9000000000000]) none none (.terminal none none none))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded1_3 : ExcludedOn (model1.B 3 ++ [step1.q]) 9000000000000 (model1.caps 3) (model1.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded1_4 : ExcludedOn (model1.B 4 ++ [step1.q]) 9000000000000 (model1.caps 4) (model1.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded1_5 : ExcludedOn (model1.B 5 ++ [step1.q]) 9000000000000 (model1.caps 5) (model1.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded1_6 : ExcludedOn (model1.B 6 ++ [step1.q]) 9000000000000 (model1.caps 6) (model1.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded1_7 : ExcludedOn (model1.B 7 ++ [step1.q]) 9000000000000 (model1.caps 7) (model1.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6975000000000], [1035000000000, -9000000000000])
      (some (2, 0, 1)) (some (3, 0, 2)) (.next ([6975000000000], [2025000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([5985000000000, -9000000000000], [2025000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([990000000000, 9000000000000], [7020000000000, -18000000000000])
      (some (3, 0, 2)) (some (4, 0, 2)) (.next ([990000000000, 9000000000000], [8010000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0], [8010000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-1035000000000, 9000000000000],
      [8010000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2025000000000],
      [9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2025000000000, 0],
      [8010000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-7020000000000,
      18000000000000], [8010000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-8010000000000, 9000000000000], [9000000000000, 0]) (some (4, 0, 2)) (some (4, 1, 2))
      (.terminal (some (4, 1, 2)) (some (0, 1, 2)) (some (4, 1, 2))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded1_8 : ExcludedOn (model1.B 8 ++ [step1.q]) 9000000000000 (model1.caps 8) (model1.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded1_9 : ExcludedOn (model1.B 9 ++ [step1.q]) 9000000000000 (model1.caps 9) (model1.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked1 : StepValid model1 9000000000000 step1 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded1_0
    · exact excluded1_1
    · exact (hj rfl).elim
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
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8045400000000, 2640000000000], [169200000000,
      -5280000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([8335800000000, 5280000000000],
      [459600000000, -2640000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([6765000000000],
      [750000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([8045400000000, 2640000000000],
      [1040400000000, 2640000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([7464600000000,
      -2640000000000], [1330800000000, 5280000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([1280400000000, 2640000000000], [290400000000, 2640000000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([699600000000, -2640000000000], [580800000000, 5280000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([290400000000, 2640000000000], [290400000000, 2640000000000]) (some
      (4, 1, 5)) (some (4, 1, 5)) (.next ([580800000000, 5280000000000], [699600000000,
      -2640000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([290400000000, 2640000000000],
      [1280400000000, 2640000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([0, 0],
      [871200000000, 7920000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-169200000000,
      5280000000000], [8214600000000, -2640000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-459600000000, 2640000000000], [8795400000000, 2640000000000]) (some (0, 2, 5)) (some (0, 2,
      5)) (.next ([-750000000000], [7515000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-1040400000000, -2640000000000], [9085800000000, 5280000000000]) (some (0, 2, 5)) (some (0,
      2, 5)) (.next ([-1330800000000, -5280000000000], [8795400000000, 2640000000000]) (some (0, 2,
      5)) (some (0, 2, 5)) (.next ([-290400000000, -2640000000000], [1570800000000, 5280000000000])
      (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-580800000000, -5280000000000], [1280400000000,
      2640000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-290400000000, -2640000000000],
      [580800000000, 5280000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-699600000000,
      2640000000000], [1280400000000, 2640000000000]) (some (0, 5, 5)) (some (1, 5, 5)) (.next
      ([-1280400000000, -2640000000000], [1570800000000, 5280000000000]) (some (1, 5, 5)) (some (1,
      5, 5)) (.terminal (some (1, 5, 5)) (some (1, 5, 5)) (some (1, 5, 5)))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded2_1 : ExcludedOn (model2.B 1 ++ [step2.q]) 9000000000000 (model2.caps 1) (model2.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([990000000000, 9000000000000], [990000000000,
      9000000000000]) none none (.next ([495000000000, 9000000000000], [1245000000000]) none none
      (.next ([1245000000000], [3750000000000]) none none (.next ([990000000000, 9000000000000],
      [3510000000000, -9000000000000]) none none (.next ([0], [5490000000000, 9000000000000]) none
      none (.next ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) none none
      (.next ([-1245000000000], [1740000000000, 9000000000000]) none none (.next ([-3750000000000],
      [4995000000000]) none none (.next ([-3510000000000, 9000000000000], [4500000000000, 0]) none
      none (.terminal none none none))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded2_3 : ExcludedOn (model2.B 3 ++ [step2.q]) 9000000000000 (model2.caps 3) (model2.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_4 : ExcludedOn (model2.B 4 ++ [step2.q]) 9000000000000 (model2.caps 4) (model2.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_5 : ExcludedOn (model2.B 5 ++ [step2.q]) 9000000000000 (model2.caps 5) (model2.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_6 : ExcludedOn (model2.B 6 ++ [step2.q]) 9000000000000 (model2.caps 6) (model2.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_7 : ExcludedOn (model2.B 7 ++ [step2.q]) 9000000000000 (model2.caps 7) (model2.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([255000000000, -9000000000000], [240000000000,
      9000000000000]) (some (2, 4, 1)) (some (3, 4, 2)) (.next ([1245000000000], [7260000000000,
      -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1245000000000], [8250000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([990000000000, 9000000000000], [8010000000000,
      -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([255000000000, -9000000000000],
      [8250000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0], [8010000000000,
      -9000000000000]) (some (3, 4, 2)) (some (4, 4, 2)) (.next ([-240000000000, -9000000000000],
      [495000000000, 0]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-7260000000000, 9000000000000],
      [8505000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-8250000000000],
      [9495000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-8010000000000, 9000000000000],
      [9000000000000, 0]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-8250000000000, 0],
      [8505000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2))
      (some (4, 1, 2)) (some (4, 1, 2))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded2_8 : ExcludedOn (model2.B 8 ++ [step2.q]) 9000000000000 (model2.caps 8) (model2.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_9 : ExcludedOn (model2.B 9 ++ [step2.q]) 9000000000000 (model2.caps 9) (model2.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked2 : StepValid model2 9000000000000 step2 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded2_0
    · exact excluded2_1
    · exact (hj rfl).elim
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

theorem excluded3_0 : ExcludedOn (model3.B 0 ++ [step3.q]) 9000000000000 (model3.caps 0) (model3.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_1 : ExcludedOn (model3.B 1 ++ [step3.q]) 9000000000000 (model3.caps 1) (model3.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_3 : ExcludedOn (model3.B 3 ++ [step3.q]) 9000000000000 (model3.caps 3) (model3.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_5 : ExcludedOn (model3.B 5 ++ [step3.q]) 9000000000000 (model3.caps 5) (model3.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_6 : ExcludedOn (model3.B 6 ++ [step3.q]) 9000000000000 (model3.caps 6) (model3.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_7 : ExcludedOn (model3.B 7 ++ [step3.q]) 9000000000000 (model3.caps 7) (model3.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_8 : ExcludedOn (model3.B 8 ++ [step3.q]) 9000000000000 (model3.caps 8) (model3.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_9 : ExcludedOn (model3.B 9 ++ [step3.q]) 9000000000000 (model3.caps 9) (model3.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked3 : StepValid model3 9000000000000 step3 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded3_0
    · exact excluded3_1
    · exact excluded3_2
    · exact excluded3_3
    · exact (hj rfl).elim
    · exact excluded3_5
    · exact excluded3_6
    · exact excluded3_7
    · exact excluded3_8
    · exact excluded3_9
theorem next3 : model3.insert step3 = model4 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded4_0 : ExcludedOn (model4.B 0 ++ [step4.q]) 9000000000000 (model4.caps 0) (model4.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7430400000000, 2640000000000], [1279200000000,
      -5280000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([7720800000000, 5280000000000],
      [1569600000000, -2640000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([6849600000000,
      -2640000000000], [1569600000000, -2640000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([7430400000000, 2640000000000], [2150400000000, 2640000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([6150000000000], [2850000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([699600000000, -2640000000000], [580800000000, 5280000000000]) (some (5, 1, 3)) (some (5, 1,
      5)) (.next ([290400000000, 2640000000000], [290400000000, 2640000000000]) (some (5, 1, 5))
      (some (5, 1, 5)) (.next ([580800000000, 5280000000000], [699600000000, -2640000000000]) (some
      (5, 1, 5)) (some (5, 2, 5)) (.next ([290400000000, 2640000000000], [1280400000000,
      2640000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([0, 0], [871200000000,
      7920000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-1279200000000, 5280000000000],
      [8709600000000, -2640000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-1569600000000,
      2640000000000], [9290400000000, 2640000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-1569600000000, 2640000000000], [8419200000000, -5280000000000]) (some (0, 2, 5)) (some (0,
      2, 5)) (.next ([-2150400000000, -2640000000000], [9580800000000, 5280000000000]) (some (0, 2,
      5)) (some (0, 2, 5)) (.next ([-2850000000000], [9000000000000]) (some (0, 2, 5)) (some (0, 2,
      5)) (.next ([-580800000000, -5280000000000], [1280400000000, 2640000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-290400000000, -2640000000000], [580800000000, 5280000000000]) (some
      (0, 2, 5)) (some (0, 3, 5)) (.next ([-699600000000, 2640000000000], [1280400000000,
      2640000000000]) (some (0, 3, 5)) (some (1, 3, 5)) (.next ([-1280400000000, -2640000000000],
      [1570800000000, 5280000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.terminal (some (1, 3, 5))
      (some (1, 3, 5)) (some (1, 3, 5))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded4_1 : ExcludedOn (model4.B 1 ++ [step4.q]) 9000000000000 (model4.caps 1) (model4.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_2 : ExcludedOn (model4.B 2 ++ [step4.q]) 9000000000000 (model4.caps 2) (model4.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_4 : ExcludedOn (model4.B 4 ++ [step4.q]) 9000000000000 (model4.caps 4) (model4.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_5 : ExcludedOn (model4.B 5 ++ [step4.q]) 9000000000000 (model4.caps 5) (model4.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_6 : ExcludedOn (model4.B 6 ++ [step4.q]) 9000000000000 (model4.caps 6) (model4.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_7 : ExcludedOn (model4.B 7 ++ [step4.q]) 9000000000000 (model4.caps 7) (model4.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_8 : ExcludedOn (model4.B 8 ++ [step4.q]) 9000000000000 (model4.caps 8) (model4.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_9 : ExcludedOn (model4.B 9 ++ [step4.q]) 9000000000000 (model4.caps 9) (model4.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked4 : StepValid model4 9000000000000 step4 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded4_0
    · exact excluded4_1
    · exact excluded4_2
    · exact (hj rfl).elim
    · exact excluded4_4
    · exact excluded4_5
    · exact excluded4_6
    · exact excluded4_7
    · exact excluded4_8
    · exact excluded4_9
theorem next4 : model4.insert step4 = model5 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded5_1 : ExcludedOn (model5.B 1 ++ [step5.q]) 9000000000000 (model5.caps 1) (model5.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7740000000000, 9000000000000], [792000000000,
      -9000000000000]) none none (.next ([5760000000000, -9000000000000], [1782000000000, 0]) none
      none (.next ([990000000000, 9000000000000], [990000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([2250000000000], [6282000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([990000000000, 9000000000000], [3510000000000, -9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.next ([0], [5490000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-792000000000, 9000000000000], [8532000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-1782000000000, 0], [7542000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-6282000000000], [8532000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-3510000000000, 9000000000000], [4500000000000, 0]) (some (3, 1, 2)) (some (3, 1, 3))
      (.terminal (some (3, 1, 3)) none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded5_2 : ExcludedOn (model5.B 2 ++ [step5.q]) 9000000000000 (model5.caps 2) (model5.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8250000000000, 0], [495000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([8010000000000, -9000000000000],
      [990000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1557000000000],
      [225000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6000000000000], [1287000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1782000000000], [468000000000]) (some (0, 1, 1))
      (some (0, 1, 1)) (.next ([5760000000000, -9000000000000], [1782000000000, 0]) (some (0, 1, 1))
      (some (0, 1, 1)) (.next ([2025000000000, 0], [990000000000, 9000000000000]) (some (0, 1, 1))
      (some (0, 1, 1)) (.next ([255000000000, -9000000000000], [240000000000, 9000000000000]) (some
      (0, 1, 1)) (some (0, 1, 1)) (.next ([792000000000, -9000000000000], [1458000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([495000000000], [5730000000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([495000000000], [7755000000000]) (some (0, 1, 1))
      (some (0, 1, 2)) (.next ([0, 0], [990000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-495000000000, -9000000000000], [8745000000000, 9000000000000]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([-990000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-225000000000], [1782000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-1287000000000], [7287000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-468000000000], [2250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1782000000000,
      0], [7542000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-990000000000,
      -9000000000000], [3015000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-240000000000, -9000000000000], [495000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1458000000000, -9000000000000], [2250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-5730000000000], [6225000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-7755000000000], [8250000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded5_3 : ExcludedOn (model5.B 3 ++ [step5.q]) 9000000000000 (model5.caps 3) (model5.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2250000000000], [78000000000]) (some (1, 0, 3))
      (some (2, 0, 3)) (.next ([7140000000000], [990000000000, 9000000000000]) (some (2, 0, 3))
      (some (2, 0, 3)) (.next ([2250000000000], [7218000000000]) (some (2, 0, 3)) (some (2, 0, 3))
      (.next ([1260000000000, -9000000000000], [8208000000000, 9000000000000]) (some (2, 0, 3))
      (some (2, 0, 3)) (.next ([0], [990000000000, 9000000000000]) (some (2, 0, 3)) (some (2, 3, 3))
      (.next ([-78000000000], [2328000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next
      ([-990000000000, -9000000000000], [8130000000000, 9000000000000]) (some (0, 3, 1)) (some (0,
      3, 1)) (.next ([-7218000000000], [9468000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-8208000000000, -9000000000000], [9468000000000]) (some (0, 3, 1)) (some (0, 3, 1))
      (.terminal (some (0, 3, 1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded5_4 : ExcludedOn (model5.B 4 ++ [step5.q]) 9000000000000 (model5.caps 4) (model5.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_5 : ExcludedOn (model5.B 5 ++ [step5.q]) 9000000000000 (model5.caps 5) (model5.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_6 : ExcludedOn (model5.B 6 ++ [step5.q]) 9000000000000 (model5.caps 6) (model5.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_7 : ExcludedOn (model5.B 7 ++ [step5.q]) 9000000000000 (model5.caps 7) (model5.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_8 : ExcludedOn (model5.B 8 ++ [step5.q]) 9000000000000 (model5.caps 8) (model5.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_9 : ExcludedOn (model5.B 9 ++ [step5.q]) 9000000000000 (model5.caps 9) (model5.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked5 : StepValid model5 9000000000000 step5 0 1 100 := by
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
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7740000000000, 9000000000000], [765000000000,
      -9000000000000]) none none (.next ([5760000000000, -9000000000000], [1755000000000, 0]) none
      none (.next ([990000000000, 9000000000000], [990000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([2250000000000], [6255000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([990000000000, 9000000000000], [3510000000000, -9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.next ([0], [5490000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-765000000000, 9000000000000], [8505000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-1755000000000, 0], [7515000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-6255000000000], [8505000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-3510000000000, 9000000000000], [4500000000000, 0]) (some (3, 1, 2)) (some (3, 1, 3))
      (.terminal (some (3, 1, 3)) none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded6_2 : ExcludedOn (model6.B 2 ++ [step6.q]) 9000000000000 (model6.caps 2) (model6.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8250000000000, 0], [495000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([8010000000000, -9000000000000],
      [990000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1530000000000],
      [225000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6000000000000], [1260000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1755000000000], [495000000000]) (some (0, 1, 1))
      (some (0, 1, 1)) (.next ([5760000000000, -9000000000000], [1755000000000, 0]) (some (0, 1, 1))
      (some (0, 1, 1)) (.next ([2025000000000, 0], [990000000000, 9000000000000]) (some (0, 1, 1))
      (some (0, 1, 1)) (.next ([255000000000, -9000000000000], [240000000000, 9000000000000]) (some
      (0, 1, 1)) (some (0, 1, 1)) (.next ([765000000000, -9000000000000], [1485000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([495000000000], [5730000000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([495000000000], [7755000000000]) (some (0, 1, 1))
      (some (0, 1, 2)) (.next ([0, 0], [990000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-495000000000, -9000000000000], [8745000000000, 9000000000000]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([-990000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-225000000000], [1755000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-1260000000000], [7260000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-495000000000], [2250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1755000000000,
      0], [7515000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-990000000000,
      -9000000000000], [3015000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-240000000000, -9000000000000], [495000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1485000000000, -9000000000000], [2250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-5730000000000], [6225000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-7755000000000], [8250000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded6_3 : ExcludedOn (model6.B 3 ++ [step6.q]) 9000000000000 (model6.caps 3) (model6.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2250000000000], [105000000000]) (some (1, 0, 3))
      (some (2, 0, 3)) (.next ([7140000000000], [990000000000, 9000000000000]) (some (2, 0, 3))
      (some (2, 0, 3)) (.next ([2250000000000], [7245000000000]) (some (2, 0, 3)) (some (2, 0, 3))
      (.next ([1260000000000, -9000000000000], [8235000000000, 9000000000000]) (some (2, 0, 3))
      (some (2, 0, 3)) (.next ([0], [990000000000, 9000000000000]) (some (2, 0, 3)) (some (2, 3, 3))
      (.next ([-105000000000], [2355000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next
      ([-990000000000, -9000000000000], [8130000000000, 9000000000000]) (some (0, 3, 1)) (some (0,
      3, 1)) (.next ([-7245000000000], [9495000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-8235000000000, -9000000000000], [9495000000000]) (some (0, 3, 1)) (some (0, 3, 1))
      (.terminal (some (0, 3, 1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded6_4 : ExcludedOn (model6.B 4 ++ [step6.q]) 9000000000000 (model6.caps 4) (model6.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_5 : ExcludedOn (model6.B 5 ++ [step6.q]) 9000000000000 (model6.caps 5) (model6.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_6 : ExcludedOn (model6.B 6 ++ [step6.q]) 9000000000000 (model6.caps 6) (model6.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_7 : ExcludedOn (model6.B 7 ++ [step6.q]) 9000000000000 (model6.caps 7) (model6.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_8 : ExcludedOn (model6.B 8 ++ [step6.q]) 9000000000000 (model6.caps 8) (model6.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_9 : ExcludedOn (model6.B 9 ++ [step6.q]) 9000000000000 (model6.caps 9) (model6.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked6 : StepValid model6 9000000000000 step6 0 1 100 := by
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

theorem excluded7_1 : ExcludedOn (model7.B 1 ++ [step7.q]) 9000000000000 (model7.caps 1) (model7.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5670000000000, 9000000000000], [330000000000,
      -9000000000000]) none none (.next ([3690000000000, -9000000000000], [1320000000000, 0]) none
      none (.next ([990000000000, 9000000000000], [990000000000, 9000000000000]) none none (.next
      ([990000000000, 9000000000000], [3510000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([180000000000], [5820000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [5490000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-330000000000,
      9000000000000], [6000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1320000000000,
      0], [5010000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-990000000000,
      -9000000000000], [1980000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3510000000000, 9000000000000], [4500000000000, 0]) (some (3, 1, 2)) none (.next
      ([-5820000000000], [6000000000000]) none none (.terminal none none none))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded7_2 : ExcludedOn (model7.B 2 ++ [step7.q]) 9000000000000 (model7.caps 2) (model7.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8250000000000, 0], [495000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([8010000000000, -9000000000000],
      [990000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3930000000000],
      [825000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3690000000000, -9000000000000],
      [1320000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([2025000000000, 0],
      [990000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1320000000000],
      [975000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([255000000000, -9000000000000],
      [240000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1320000000000],
      [3000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([495000000000], [5730000000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([330000000000, -9000000000000], [3990000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-495000000000, -9000000000000],
      [8745000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-990000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-825000000000], [4755000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1320000000000,
      0], [5010000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-990000000000,
      -9000000000000], [3015000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-975000000000], [2295000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-240000000000,
      -9000000000000], [495000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-3000000000000], [4320000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-5730000000000], [6225000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3990000000000,
      -9000000000000], [4320000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded7_3 : ExcludedOn (model7.B 3 ++ [step7.q]) 9000000000000 (model7.caps 3) (model7.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_4 : ExcludedOn (model7.B 4 ++ [step7.q]) 9000000000000 (model7.caps 4) (model7.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_5 : ExcludedOn (model7.B 5 ++ [step7.q]) 9000000000000 (model7.caps 5) (model7.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_6 : ExcludedOn (model7.B 6 ++ [step7.q]) 9000000000000 (model7.caps 6) (model7.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_7 : ExcludedOn (model7.B 7 ++ [step7.q]) 9000000000000 (model7.caps 7) (model7.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3690000000000, -9000000000000], [1320000000000,
      0]) (some (2, 4, 1)) (some (3, 4, 2)) (.next ([6000000000000], [3330000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([6000000000000], [4320000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([5010000000000, -9000000000000], [4320000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([990000000000, 9000000000000], [7020000000000,
      -18000000000000]) (some (3, 0, 2)) (some (4, 0, 2)) (.next ([990000000000, 9000000000000],
      [8010000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0],
      [8010000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-1320000000000,
      0], [5010000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-3330000000000, 9000000000000], [9330000000000, -9000000000000]) (some (4, 0, 2)) (some (4,
      0, 2)) (.next ([-4320000000000], [10320000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-4320000000000, 0], [9330000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([-7020000000000, 18000000000000], [8010000000000, -9000000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([-8010000000000, 9000000000000], [9000000000000, 0]) (some (4, 0, 2))
      (some (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (4, 1, 2)) (some (4, 1, 2)))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded7_8 : ExcludedOn (model7.B 8 ++ [step7.q]) 9000000000000 (model7.caps 8) (model7.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_9 : ExcludedOn (model7.B 9 ++ [step7.q]) 9000000000000 (model7.caps 9) (model7.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked7 : StepValid model7 9000000000000 step7 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded7_1
    · exact excluded7_2
    · exact excluded7_3
    · exact excluded7_4
    · exact excluded7_5
    · exact excluded7_6
    · exact excluded7_7
    · exact excluded7_8
    · exact excluded7_9
theorem next7 : model7.insert step7 = model8 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown110000120000
end ConwaySoifer.Simplified.Certificates
