/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across032500037500
import Mathlib.Tactic.FinCases

/-!
# Across 032500 037500 0

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
namespace Across032500037500

theorem excluded0_0 : ExcludedOn (model0.B 0 ++ [step0.q]) 9000000000000 (model0.caps 0) (model0.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([93843750000, 2887500000000], [93843750000,
      2887500000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([772687500000, 5775000000000],
      [8321156250000, -2887500000000]) (some (6, 1, 3)) (some (6, 2, 4)) (.next ([678843750000,
      2887500000000], [8227312500000, -5775000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
      ([678843750000, 2887500000000], [8508843750000, 2887500000000]) (some (6, 2, 4)) (some (6, 2,
      4)) (.next ([491156250000, -2887500000000], [8321156250000, -2887500000000]) (some (6, 2, 4))
      (some (6, 2, 4)) (.next ([491156250000, -2887500000000], [8602687500000, 5775000000000]) (some
      (6, 2, 4)) (some (6, 2, 4)) (.next ([397312500000, -5775000000000], [8508843750000,
      2887500000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([0, 0], [281531250000,
      8662500000000]) (some (6, 2, 4)) (some (6, 2, 6)) (.next ([-93843750000, -2887500000000],
      [187687500000, 5775000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([-8321156250000,
      2887500000000], [9093843750000, 2887500000000]) (some (6, 2, 6)) (some (6, 3, 6)) (.next
      ([-8227312500000, 5775000000000], [8906156250000, -2887500000000]) (some (1, 3, 6)) (some (1,
      3, 6)) (.next ([-8508843750000, -2887500000000], [9187687500000, 5775000000000]) (some (1, 3,
      6)) (some (1, 3, 6)) (.next ([-8321156250000, 2887500000000], [8812312500000, -5775000000000])
      (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-8602687500000, -5775000000000], [9093843750000,
      2887500000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-8508843750000, -2887500000000],
      [8906156250000, -2887500000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.terminal (some (1, 3, 6))
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8707500000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([292500000000, 9000000000000],
      [292500000000, 9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([585000000000,
      9000000000000], [8415000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([292500000000], [8707500000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [292500000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, -9000000000000],
      [8707500000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-292500000000, -9000000000000],
      [585000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8415000000000,
      9000000000000], [9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8707500000000],
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8707500000000], [292500000000]) (some (1, 0, 3))
      (some (2, 0, 3)) (.next ([8415000000000, -9000000000000], [585000000000, 9000000000000]) (some
      (2, 0, 3)) (some (2, 0, 3)) (.next ([585000000000], [292500000000, 9000000000000]) (some (2,
      0, 3)) (some (2, 3, 3)) (.next ([292500000000], [8415000000000]) (some (2, 3, 3)) (some (2, 3,
      3)) (.next ([0], [292500000000, 9000000000000]) (some (2, 3, 1)) (some (2, 3, 1)) (.next
      ([-292500000000], [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-585000000000,
      -9000000000000], [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-292500000000,
      -9000000000000], [877500000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-8415000000000], [8707500000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3,
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7875000000000], [1222500000000]) (some (5, 1,
      5)) (some (5, 1, 5)) (.next ([8062687500000, 5775000000000], [1421156250000, -2887500000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([7968843750000, 2887500000000], [1608843750000,
      2887500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([7687312500000, -5775000000000],
      [1608843750000, 2887500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([7781156250000,
      -2887500000000], [1702687500000, 5775000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([386343750000, 2887500000000], [93843750000, 2887500000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([187687500000, 5775000000000], [198656250000, -2887500000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([93843750000, 2887500000000], [386343750000, 2887500000000]) (some
      (0, 1, 5)) (some (0, 2, 5)) (.next ([0, 0], [281531250000, 8662500000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-1222500000000], [9097500000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-1421156250000, 2887500000000], [9483843750000, 2887500000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-1608843750000, -2887500000000], [9577687500000, 5775000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1608843750000, -2887500000000], [9296156250000,
      -2887500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1702687500000, -5775000000000],
      [9483843750000, 2887500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-93843750000,
      -2887500000000], [480187500000, 5775000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next
      ([-198656250000, 2887500000000], [386343750000, 2887500000000]) (some (0, 5, 5)) (some (0, 5,
      5)) (.next ([-386343750000, -2887500000000], [480187500000, 5775000000000]) (some (0, 5, 5))
      (some (1, 5, 5)) (.terminal (some (1, 5, 5)) (some (1, 5, 5)) (some (1, 5,
      5))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

theorem excluded2_1 : ExcludedOn (model2.B 1 ++ [step2.q]) 9000000000000 (model2.caps 1) (model2.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([292500000000, 9000000000000], [292500000000,
      9000000000000]) none none (.next ([682500000000, 9000000000000], [1125000000000]) none none
      (.next ([390000000000, 0], [832500000000, -9000000000000]) none none (.next ([390000000000],
      [1125000000000]) none none (.next ([0, 0], [292500000000, 9000000000000]) none none (.next
      ([-292500000000, -9000000000000], [585000000000, 18000000000000]) none none (.next
      ([-1125000000000], [1807500000000, 9000000000000]) none none (.next ([-832500000000,
      9000000000000], [1222500000000, -9000000000000]) none none (.next ([-1125000000000],
      [1515000000000]) none none (.terminal none none none))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded2_2 : ExcludedOn (model2.B 2 ++ [step2.q]) 9000000000000 (model2.caps 2) (model2.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8707500000000, -9000000000000], [292500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7485000000000], [390000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7192500000000, -9000000000000], [390000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7485000000000, 0], [682500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([292500000000, 9000000000000], [292500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [4792500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4207500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([390000000000, 0],
      [832500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1125000000000],
      [2985000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([292500000000, 9000000000000],
      [4207500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [292500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-292500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-390000000000], [7875000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-390000000000,
      0], [7582500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-682500000000,
      -9000000000000], [8167500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-292500000000, -9000000000000], [585000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-4792500000000, -9000000000000], [9292500000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8707500000000, -9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-832500000000, 9000000000000], [1222500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2985000000000], [4110000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4207500000000, 9000000000000], [4500000000000, 0])
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8812687500000, 5775000000000], [101156250000,
      -2887500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([8718843750000, 2887500000000],
      [288843750000, 2887500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([8437312500000,
      -5775000000000], [288843750000, 2887500000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([8531156250000, -2887500000000], [382687500000, 5775000000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([386343750000, 2887500000000], [93843750000, 2887500000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([187687500000, 5775000000000], [198656250000, -2887500000000]) (some
      (4, 1, 5)) (some (4, 1, 5)) (.next ([93843750000, 2887500000000], [386343750000,
      2887500000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([97500000000], [8527500000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([0, 0], [281531250000, 8662500000000]) (some (0, 2,
      5)) (some (0, 2, 5)) (.next ([-101156250000, 2887500000000], [8913843750000, 2887500000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-288843750000, -2887500000000], [9007687500000,
      5775000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-288843750000, -2887500000000],
      [8726156250000, -2887500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-382687500000,
      -5775000000000], [8913843750000, 2887500000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-93843750000, -2887500000000], [480187500000, 5775000000000]) (some (0, 2, 5)) (some (0, 5,
      5)) (.next ([-198656250000, 2887500000000], [386343750000, 2887500000000]) (some (0, 5, 5))
      (some (0, 5, 5)) (.next ([-386343750000, -2887500000000], [480187500000, 5775000000000]) (some
      (0, 5, 5)) (some (1, 5, 5)) (.next ([-8527500000000], [8625000000000]) (some (1, 5, 5)) (some
      (1, 5, 5)) (.terminal (some (1, 5, 4)) (some (1, 5, 4)) (some (1, 5, 4)))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8805000000000, 0], [112500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([8707500000000, -9000000000000],
      [292500000000, 9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([292500000000,
      9000000000000], [292500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4500000000000, 0], [4792500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4207500000000, -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([82500000000, -9000000000000], [97500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([375000000000], [4305000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([292500000000, 9000000000000], [4207500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([180000000000, 0], [8332500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([180000000000], [8625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [292500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-112500000000,
      -9000000000000], [8917500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-292500000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-292500000000, -9000000000000], [585000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-4792500000000, -9000000000000], [9292500000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8707500000000, -9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-97500000000, -9000000000000], [180000000000, 0]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-4305000000000], [4680000000000]) (some (0, 4, 3)) (some (0,
      4, 3)) (.next ([-4207500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-8332500000000, 9000000000000], [8512500000000, -9000000000000]) (some (0, 2,
      3)) (some (0, 2, 3)) (.next ([-8625000000000], [8805000000000]) (some (0, 2, 3)) (some (0, 2,
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
  apply ExclusionHint.sound (.witnessedFan (.next ([570000000000], [750000000000]) (some (3, 5, 2))
      (some (4, 5, 3)) (.next ([390000000000, 0], [832500000000, -9000000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([1125000000000], [7192500000000, -9000000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([1125000000000], [7485000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([832500000000, -9000000000000], [7485000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([375000000000], [8512500000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([375000000000], [8805000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([292500000000, 9000000000000], [8415000000000, -18000000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([292500000000, 9000000000000], [8707500000000, -9000000000000]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([82500000000, -9000000000000], [8805000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([0, 0], [8707500000000, -9000000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([-750000000000], [1320000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-832500000000, 9000000000000], [1222500000000, -9000000000000]) (some (0, 5, 3)) (some (5,
      5, 3)) (.next ([-7192500000000, 9000000000000], [8317500000000, -9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-7485000000000], [8610000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([-7485000000000, 0], [8317500000000, -9000000000000]) (some (5, 1, 3)) (some (5,
      1, 3)) (.next ([-8512500000000, 9000000000000], [8887500000000, -9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-8805000000000], [9180000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([-8415000000000, 18000000000000], [8707500000000, -9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-8707500000000, 9000000000000], [9000000000000, 0]) (some (5, 1,
      3)) (some (5, 2, 3)) (.next ([-8805000000000, 0], [8887500000000, -9000000000000]) (some (5,
      2, 3)) (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 2, 3)) (some (5, 2,
      3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8707500000000, -9000000000000], [292500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([6750000000000], [2250000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([6457500000000, -9000000000000], [2250000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([6750000000000, 0], [2542500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([292500000000, 9000000000000], [292500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [4792500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4207500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([292500000000, 9000000000000],
      [1957500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([292500000000,
      9000000000000], [4207500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      0], [292500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-292500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-2250000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2250000000000,
      0], [8707500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-2542500000000, -9000000000000], [9292500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-292500000000, -9000000000000], [585000000000, 18000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-4792500000000, -9000000000000], [9292500000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8707500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1957500000000, 9000000000000],
      [2250000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4207500000000, 9000000000000],
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6457500000000, -9000000000000], [292500000000,
      9000000000000]) (some (3, 1, 2)) (some (4, 1, 3)) (.next ([1125000000000], [735000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([390000000000, 0], [832500000000, -9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([292500000000, 9000000000000], [1957500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([832500000000, -9000000000000],
      [7485000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([292500000000, 9000000000000],
      [8415000000000, -18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([292500000000,
      9000000000000], [8707500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0,
      0], [8707500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-292500000000,
      -9000000000000], [6750000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-735000000000],
      [1860000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-832500000000, 9000000000000],
      [1222500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1957500000000,
      9000000000000], [2250000000000, 0]) (some (0, 1, 3)) (some (1, 1, 3)) (.next ([-7485000000000,
      0], [8317500000000, -9000000000000]) (some (1, 1, 3)) (some (1, 5, 3)) (.next
      ([-8415000000000, 18000000000000], [8707500000000, -9000000000000]) (some (1, 5, 3)) (some (1,
      5, 3)) (.next ([-8707500000000, 9000000000000], [9000000000000, 0]) (some (1, 5, 3)) (some (1,
      5, 3)) (.terminal (some (1, 5, 3)) (some (1, 2, 3)) (some (1, 5, 3))))))))))))))))))) (den :=
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

end Across032500037500
end ConwaySoifer.Simplified.Certificates
