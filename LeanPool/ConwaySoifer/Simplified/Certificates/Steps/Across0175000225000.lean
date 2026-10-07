/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across017500022500
import Mathlib.Tactic.FinCases

/-!
# Across 017500 022500 0

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
namespace Across017500022500

theorem excluded0_0 : ExcludedOn (model0.B 0 ++ [step0.q]) 9000000000000 (model0.caps 0) (model0.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8301318750000, 2932500000000], [1041112500000,
      -5865000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next ([8352637500000, 5865000000000],
      [1092431250000, -2932500000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([8198681250000,
      -2932500000000], [1092431250000, -2932500000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([8301318750000, 2932500000000], [1195068750000, 2932500000000]) (some (5, 1, 6)) (some (5, 1,
      6)) (.next ([8147362500000, -5865000000000], [1195068750000, 2932500000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([8198681250000, -2932500000000], [1246387500000, 5865000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([51318750000, 2932500000000], [51318750000,
      2932500000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0], [153956250000,
      8797500000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-1041112500000, 5865000000000],
      [9342431250000, -2932500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1092431250000,
      2932500000000], [9445068750000, 2932500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
      ([-1092431250000, 2932500000000], [9291112500000, -5865000000000]) (some (0, 2, 6)) (some (0,
      2, 6)) (.next ([-1195068750000, -2932500000000], [9496387500000, 5865000000000]) (some (0, 2,
      6)) (some (0, 2, 6)) (.next ([-1195068750000, -2932500000000], [9342431250000,
      -2932500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1246387500000, -5865000000000],
      [9445068750000, 2932500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-51318750000,
      -2932500000000], [102637500000, 5865000000000]) (some (0, 2, 6)) (some (0, 6, 6)) (.terminal
      (some (0, 6, 6)) (some (1, 6, 6)) (some (1, 6, 6))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded0_1 : ExcludedOn (model0.B 1 ++ [step0.q]) 9000000000000 (model0.caps 1) (model0.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([157500000000, 9000000000000], [157500000000,
      9000000000000]) none none (.next ([551250000000, 9000000000000], [750000000000]) none none
      (.next ([393750000000, 0], [592500000000, -9000000000000]) none none (.next ([393750000000],
      [750000000000]) none none (.next ([0, 0], [157500000000, 9000000000000]) none none (.next
      ([-157500000000, -9000000000000], [315000000000, 18000000000000]) none none (.next
      ([-750000000000], [1301250000000, 9000000000000]) none none (.next ([-592500000000,
      9000000000000], [986250000000, -9000000000000]) none none (.next ([-750000000000],
      [1143750000000]) none none (.terminal none none none))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded0_2 : ExcludedOn (model0.B 2 ++ [step0.q]) 9000000000000 (model0.caps 2) (model0.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8842500000000, -9000000000000], [157500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7856250000000], [393750000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7698750000000, -9000000000000], [393750000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7856250000000, 0], [551250000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([157500000000, 9000000000000], [157500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [4657500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4342500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([393750000000, 0],
      [592500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([750000000000],
      [3356250000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([157500000000, 9000000000000],
      [4342500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [157500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-157500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-393750000000], [8250000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-393750000000,
      0], [8092500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-551250000000,
      -9000000000000], [8407500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-157500000000, -9000000000000], [315000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-4657500000000, -9000000000000], [9157500000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8842500000000, -9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-592500000000, 9000000000000], [986250000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3356250000000], [4106250000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4342500000000, 9000000000000], [4500000000000, 0])
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8842500000000, -9000000000000], [157500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7740000000000], [1260000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7582500000000, -9000000000000], [1260000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7740000000000, 0], [1417500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([157500000000, 9000000000000], [157500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [4657500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4342500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([157500000000, 9000000000000],
      [1102500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([157500000000,
      9000000000000], [4342500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      0], [157500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-157500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1260000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1260000000000,
      0], [8842500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1417500000000, -9000000000000], [9157500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-157500000000, -9000000000000], [315000000000, 18000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-4657500000000, -9000000000000], [9157500000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8842500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1102500000000, 9000000000000],
      [1260000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4342500000000, 9000000000000],
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7582500000000, -9000000000000], [157500000000,
      9000000000000]) (some (3, 1, 2)) (some (4, 1, 3)) (.next ([750000000000], [116250000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([393750000000, 0], [592500000000, -9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([157500000000, 9000000000000], [1102500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([750000000000], [7698750000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([750000000000], [7856250000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([592500000000, -9000000000000], [7856250000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([157500000000, 9000000000000], [8685000000000,
      -18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([157500000000, 9000000000000],
      [8842500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [8842500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-157500000000,
      -9000000000000], [7740000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-116250000000],
      [866250000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-592500000000, 9000000000000],
      [986250000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1102500000000,
      9000000000000], [1260000000000, 0]) (some (0, 1, 3)) (some (1, 1, 3)) (.next ([-7698750000000,
      9000000000000], [8448750000000, -9000000000000]) (some (1, 1, 3)) (some (1, 5, 3)) (.next
      ([-7856250000000], [8606250000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-7856250000000,
      0], [8448750000000, -9000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next
      ([-8685000000000, 18000000000000], [8842500000000, -9000000000000]) (some (1, 5, 3)) (some (1,
      5, 3)) (.next ([-8842500000000, 9000000000000], [9000000000000, 0]) (some (1, 5, 3)) (some (1,
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
  apply ExclusionHint.sound (.witnessedFan (.next ([637500000000, -9000000000000], [105000000000,
      0]) none none (.next ([900000000000], [465000000000]) none none (.next ([157500000000,
      9000000000000], [157500000000, 9000000000000]) none none (.next ([157500000000,
      9000000000000], [1102500000000, -9000000000000]) none none (.next ([52500000000,
      9000000000000], [900000000000]) none none (.next ([0], [1417500000000, 9000000000000]) none
      none (.next ([-105000000000, 0], [742500000000, -9000000000000]) none none (.next
      ([-465000000000], [1365000000000]) none none (.next ([-157500000000, -9000000000000],
      [315000000000, 18000000000000]) none none (.next ([-1102500000000, 9000000000000],
      [1260000000000, 0]) none none (.next ([-900000000000], [952500000000, 9000000000000]) none
      none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded2_2 : ExcludedOn (model2.B 2 ++ [step2.q]) 9000000000000 (model2.caps 2) (model2.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8205000000000, 0], [52500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([8842500000000, -9000000000000], [157500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([637500000000, -9000000000000],
      [105000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([157500000000, 9000000000000],
      [157500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0],
      [4657500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4342500000000,
      -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([900000000000],
      [3705000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([157500000000, 9000000000000],
      [4342500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([105000000000, 0],
      [7942500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([105000000000],
      [8100000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0], [157500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-52500000000, -9000000000000],
      [8257500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-157500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-105000000000,
      0], [742500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-157500000000,
      -9000000000000], [315000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4657500000000, -9000000000000], [9157500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 3)) (.next ([-4500000000000, 0], [8842500000000, -9000000000000]) (some (0, 4, 3)) (some
      (0, 4, 3)) (.next ([-3705000000000], [4605000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-4342500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-7942500000000, 9000000000000], [8047500000000, -9000000000000]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-8100000000000], [8205000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal
      (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2, 3))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([637500000000, -9000000000000], [105000000000,
      0]) (some (3, 5, 2)) (some (4, 5, 3)) (.next ([393750000000, 0], [592500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([150000000000], [348750000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([900000000000], [8047500000000, -9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([900000000000], [8205000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([750000000000], [7698750000000, -9000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([750000000000], [7856250000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([742500000000, -9000000000000], [8205000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([592500000000, -9000000000000], [7856250000000]) (some (4, 1, 3)) (some (5, 1, 3))
      (.next ([157500000000, 9000000000000], [8685000000000, -18000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([157500000000, 9000000000000], [8842500000000, -9000000000000]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 0], [8842500000000, -9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-105000000000, 0], [742500000000, -9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-592500000000, 9000000000000], [986250000000, -9000000000000]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([-348750000000], [498750000000]) (some (5, 1, 3)) (some
      (5, 1, 3)) (.next ([-8047500000000, 9000000000000], [8947500000000, -9000000000000]) (some (5,
      1, 3)) (some (5, 1, 3)) (.next ([-8205000000000], [9105000000000]) (some (5, 1, 3)) (some (5,
      1, 3)) (.next ([-7698750000000, 9000000000000], [8448750000000, -9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-7856250000000], [8606250000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([-8205000000000, 0], [8947500000000, -9000000000000]) (some (5, 1, 3)) (some (5,
      1, 3)) (.next ([-7856250000000, 0], [8448750000000, -9000000000000]) (some (5, 1, 3)) (some
      (5, 1, 3)) (.next ([-8685000000000, 18000000000000], [8842500000000, -9000000000000]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([-8842500000000, 9000000000000], [9000000000000, 0]) (some
      (5, 1, 3)) (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 2, 3)) (some (5, 2,
      3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([262500000000, 9000000000000], [112500000000,
      -9000000000000]) none none (.next ([157500000000, 9000000000000], [157500000000,
      9000000000000]) none none (.next ([375000000000], [1155000000000]) none none (.next
      ([157500000000, 9000000000000], [1102500000000, -9000000000000]) none none (.next ([0],
      [1417500000000, 9000000000000]) none none (.next ([-112500000000, 9000000000000],
      [375000000000]) none none (.next ([-157500000000, -9000000000000], [315000000000,
      18000000000000]) none none (.next ([-1155000000000], [1530000000000]) none none (.next
      ([-1102500000000, 9000000000000], [1260000000000, 0]) none none (.terminal none none
      none))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8842500000000, -9000000000000], [157500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([217500000000, -9000000000000],
      [52500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([157500000000,
      9000000000000], [157500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4500000000000, 0], [4657500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4342500000000, -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([375000000000], [4395000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([157500000000,
      9000000000000], [4342500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([270000000000, 0], [8467500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([270000000000], [8625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([112500000000,
      -9000000000000], [8782500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      0], [157500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-157500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-52500000000,
      -9000000000000], [270000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-157500000000,
      -9000000000000], [315000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4657500000000, -9000000000000], [9157500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 3)) (.next ([-4500000000000, 0], [8842500000000, -9000000000000]) (some (0, 4, 3)) (some
      (0, 4, 3)) (.next ([-4395000000000], [4770000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-4342500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8467500000000, 9000000000000], [8737500000000, -9000000000000]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-8625000000000], [8895000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8782500000000, -9000000000000], [8895000000000]) (some (0, 2, 3)) (some (0, 2, 3))
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8887500000000, 9000000000000], [217500000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([8730000000000], [375000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([8572500000000, -9000000000000], [375000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([157500000000, 9000000000000], [157500000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 3)) (.next ([0, 0], [157500000000,
      9000000000000]) (some (3, 0, 3)) (some (3, 0, 3)) (.next ([-217500000000, 9000000000000],
      [9105000000000]) (some (3, 0, 3)) (some (3, 1, 3)) (.next ([-375000000000], [9105000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-375000000000], [8947500000000, -9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-157500000000, -9000000000000], [315000000000,
      18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1,
      3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Across017500022500
end ConwaySoifer.Simplified.Certificates
