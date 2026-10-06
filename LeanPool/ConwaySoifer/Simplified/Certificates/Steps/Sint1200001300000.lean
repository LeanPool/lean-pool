/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint120000130000
import Mathlib.Tactic.FinCases

/-!
# Sint 120000 130000 0

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
namespace Sint120000130000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan6Owner0Part0 : FanWitness := (.next ([266400000000, 5220000000000], [5221800000000,
    -2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([86400000000, 5220000000000],
    [5311800000000, -2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([0, 0],
    [939600000000, 7830000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-46800000000,
    2610000000000], [5848200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-226800000000, 2610000000000], [5938200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-45000000000], [585000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-673200000000, -2610000000000], [6161400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-766800000000, 2610000000000], [5893200000000, 2610000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-853200000000, -2610000000000], [6251400000000, 5220000000000]) (some
    (7, 3, 5)) (some (7, 3, 5)) (.next ([-986400000000, -5220000000000], [5848200000000,
    2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-1166400000000, -5220000000000],
    [5938200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-1393200000000,
    -2610000000000], [6206400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-2295000000000], [9810000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-2385000000000],
    [9720000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-2340000000000], [9135000000000])
    (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-1706400000000, -5220000000000], [5893200000000,
    2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-313200000000, -2610000000000],
    [626400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-4321800000000,
    2610000000000], [8188200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 4, 6)) (.next
    ([-4008600000000, 5220000000000], [7561800000000, -2610000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-4948200000000, -2610000000000], [8501400000000, 5220000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-4321800000000, 2610000000000], [7248600000000, -5220000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-675000000000], [720000000000]) (some (7, 4, 6)) (some (7,
    4, 6)) (.next ([-5221800000000, 2610000000000], [5488200000000, 2610000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5311800000000, 2610000000000], [5398200000000, 2610000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.terminal (some (7, 4, 6)) (some (7, 4, 6)) (some (7, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan7Owner0Part0 : FanWitness := (.next ([266400000000, 5220000000000], [5221800000000,
    -2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([86400000000, 5220000000000],
    [5311800000000, -2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([0, 0],
    [939600000000, 7830000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-46800000000,
    2610000000000], [5848200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-226800000000, 2610000000000], [5938200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-45000000000], [585000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-673200000000, -2610000000000], [6161400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-766800000000, 2610000000000], [5893200000000, 2610000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-853200000000, -2610000000000], [6251400000000, 5220000000000]) (some
    (7, 3, 5)) (some (7, 3, 5)) (.next ([-986400000000, -5220000000000], [5848200000000,
    2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-1166400000000, -5220000000000],
    [5938200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-1393200000000,
    -2610000000000], [6206400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-1706400000000, -5220000000000], [5893200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-4785000000000], [10185000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-4875000000000], [10095000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-313200000000,
    -2610000000000], [626400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-4830000000000], [9510000000000]) (some (7, 3, 5)) (some (7, 4, 6)) (.next ([-4696800000000,
    2610000000000], [6073200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-4383600000000, 5220000000000], [5446800000000, -2610000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-5323200000000, -2610000000000], [6386400000000, 5220000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-4696800000000, 2610000000000], [5133600000000, -5220000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-675000000000], [720000000000]) (some (7, 4, 6)) (some (7,
    4, 6)) (.next ([-5221800000000, 2610000000000], [5488200000000, 2610000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5311800000000, 2610000000000], [5398200000000, 2610000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.terminal (some (7, 4, 6)) (some (7, 4, 6)) (some (7, 4,
    6)))))))))))))))))))))))))))

theorem excluded0_0 : ExcludedOn (model0.B 0 ++ [step0.q]) 9000000000000 (model0.caps 0) (model0.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8398200000000, 2610000000000], [313200000000,
      2610000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([7458600000000, -5220000000000],
      [313200000000, 2610000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([7771800000000,
      -2610000000000], [626400000000, 5220000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([313200000000, 2610000000000], [313200000000, 2610000000000]) (some (5, 6, 3)) (some (6, 6,
      3)) (.next ([626400000000, 5220000000000], [7771800000000, -2610000000000]) (some (6, 6, 3))
      (some (6, 6, 4)) (.next ([313200000000, 2610000000000], [7458600000000, -5220000000000]) (some
      (6, 2, 4)) (some (6, 2, 4)) (.next ([313200000000, 2610000000000], [8398200000000,
      2610000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([0, 0], [939600000000,
      7830000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-313200000000, -2610000000000],
      [8711400000000, 5220000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-313200000000,
      -2610000000000], [7771800000000, -2610000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
      ([-626400000000, -5220000000000], [8398200000000, 2610000000000]) (some (6, 2, 4)) (some (6,
      2, 4)) (.next ([-313200000000, -2610000000000], [626400000000, 5220000000000]) (some (6, 2,
      4)) (some (6, 2, 4)) (.next ([-7771800000000, 2610000000000], [8398200000000, 2610000000000])
      (some (6, 2, 4)) (some (6, 3, 5)) (.next ([-7458600000000, 5220000000000], [7771800000000,
      -2610000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-8398200000000, -2610000000000],
      [8711400000000, 5220000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.terminal (some (6, 3, 5))
      (some (6, 3, 5)) (some (6, 3, 5))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded0_1 : ExcludedOn (model0.B 1 ++ [step0.q]) 9000000000000 (model0.caps 1) (model0.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_2 : ExcludedOn (model0.B 2 ++ [step0.q]) 9000000000000 (model0.caps 2) (model0.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_3 : ExcludedOn (model0.B 3 ++ [step0.q]) 9000000000000 (model0.caps 3) (model0.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_5 : ExcludedOn (model0.B 5 ++ [step0.q]) 9000000000000 (model0.caps 5) (model0.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_6 : ExcludedOn (model0.B 6 ++ [step0.q]) 9000000000000 (model0.caps 6) (model0.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded0_7 : ExcludedOn (model0.B 7 ++ [step0.q]) 9000000000000 (model0.caps 7) (model0.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded0_0
    · exact excluded0_1
    · exact excluded0_2
    · exact excluded0_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7303200000000, 2610000000000], [1383600000000,
      -5220000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([7616400000000, 5220000000000],
      [1696800000000, -2610000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([6676800000000,
      -2610000000000], [1696800000000, -2610000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([7303200000000, 2610000000000], [2323200000000, 2610000000000]) (some (6, 1, 3)) (some (6, 1,
      3)) (.next ([6363600000000, -5220000000000], [2323200000000, 2610000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([6676800000000, -2610000000000], [2636400000000, 5220000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([313200000000, 2610000000000], [313200000000,
      2610000000000]) (some (6, 1, 3)) (some (6, 1, 6)) (.next ([0, 0], [939600000000,
      7830000000000]) (some (6, 1, 6)) (some (6, 2, 6)) (.next ([-1383600000000, 5220000000000],
      [8686800000000, -2610000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([-1696800000000,
      2610000000000], [9313200000000, 2610000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
      ([-1696800000000, 2610000000000], [8373600000000, -5220000000000]) (some (0, 2, 6)) (some (0,
      2, 6)) (.next ([-2323200000000, -2610000000000], [9626400000000, 5220000000000]) (some (0, 2,
      6)) (some (0, 2, 6)) (.next ([-2323200000000, -2610000000000], [8686800000000,
      -2610000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2636400000000, -5220000000000],
      [9313200000000, 2610000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-313200000000,
      -2610000000000], [626400000000, 5220000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.terminal
      (some (0, 2, 6)) (some (1, 3, 6)) (some (1, 3, 6))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded1_1 : ExcludedOn (model1.B 1 ++ [step1.q]) 9000000000000 (model1.caps 1) (model1.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded1_2 : ExcludedOn (model1.B 2 ++ [step1.q]) 9000000000000 (model1.caps 2) (model1.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded1_4 : ExcludedOn (model1.B 4 ++ [step1.q]) 9000000000000 (model1.caps 4) (model1.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded1_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_1 : ExcludedOn (model2.B 1 ++ [step2.q]) 9000000000000 (model2.caps 1) (model2.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_2 : ExcludedOn (model2.B 2 ++ [step2.q]) 9000000000000 (model2.caps 2) (model2.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_3 : ExcludedOn (model2.B 3 ++ [step2.q]) 9000000000000 (model2.caps 3) (model2.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded2_4 : ExcludedOn (model2.B 4 ++ [step2.q]) 9000000000000 (model2.caps 4) (model2.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([915000000000, 0], [165000000000, 9000000000000])
      (some (4, 0, 1)) (some (4, 1, 1)) (.next ([6930000000000], [2070000000000]) (some (4, 1, 1))
      (some (4, 1, 2)) (.next ([5850000000000, -9000000000000], [2070000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([6930000000000, 0], [3150000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([6015000000000], [2985000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some (4, 1, 2)) (some
      (4, 1, 4)) (.next ([165000000000, 9000000000000], [915000000000]) (some (4, 1, 4)) (some (4,
      1, 4)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (4, 1, 4)) (some (4, 1, 4))
      (.next ([-165000000000, -9000000000000], [1080000000000, 9000000000000]) (some (4, 1, 4))
      (some (4, 1, 4)) (.next ([-2070000000000], [9000000000000]) (some (4, 1, 4)) (some (4, 1, 4))
      (.next ([-2070000000000], [7920000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-3150000000000, -9000000000000], [10080000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-2985000000000], [9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-1080000000000, -9000000000000], [2160000000000, 18000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-915000000000], [1080000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1,
      4))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
    · exact excluded2_2
    · exact excluded2_3
    · exact excluded2_4
    · exact excluded2_5
    · exact excluded2_6
    · exact excluded2_7
    · exact (hj rfl).elim
    · exact excluded2_9
theorem next2 : model2.insert step2 = model3 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded3_1 : ExcludedOn (model3.B 1 ++ [step3.q]) 9000000000000 (model3.caps 1) (model3.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6660000000000, 9000000000000], [3420000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([5580000000000], [4500000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1080000000000, 9000000000000], [1080000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4500000000000, -9000000000000],
      [4500000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3420000000000, 9000000000000],
      [10080000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4500000000000],
      [10080000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1080000000000, -9000000000000],
      [2160000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4500000000000,
      0], [9000000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3420000000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([7920000000000, -9000000000000],
      [1080000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4500000000000,
      -9000000000000], [4500000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([1080000000000], [3420000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1080000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, -9000000000000],
      [3420000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-1080000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-4500000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3420000000000],
      [4500000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_3 : ExcludedOn (model3.B 3 ++ [step3.q]) 9000000000000 (model3.caps 3) (model3.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6990000000000], [1080000000000, 9000000000000])
      (some (1, 0, 3)) (some (2, 0, 3)) (.next ([2490000000000], [930000000000]) (some (2, 0, 3))
      (some (2, 0, 3)) (.next ([3420000000000], [4500000000000]) (some (2, 0, 1)) (some (2, 0, 1))
      (.next ([2340000000000, -9000000000000], [5580000000000, 9000000000000]) (some (2, 0, 1))
      (some (2, 0, 1)) (.next ([0], [1080000000000, 9000000000000]) (some (2, 0, 1)) (some (2, 3,
      1)) (.next ([-1080000000000, -9000000000000], [8070000000000, 9000000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([-930000000000], [3420000000000]) (some (0, 3, 1)) (some (0, 3, 1))
      (.next ([-4500000000000], [7920000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-5580000000000, -9000000000000], [7920000000000]) (some (0, 3, 1)) (some (0, 3, 1))
      (.terminal (some (0, 3, 1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded3_4 : ExcludedOn (model3.B 4 ++ [step3.q]) 9000000000000 (model3.caps 4) (model3.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_5 : ExcludedOn (model3.B 5 ++ [step3.q]) 9000000000000 (model3.caps 5) (model3.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_6 : ExcludedOn (model3.B 6 ++ [step3.q]) 9000000000000 (model3.caps 6) (model3.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded3_7 : ExcludedOn (model3.B 7 ++ [step3.q]) 9000000000000 (model3.caps 7) (model3.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded4_1 : ExcludedOn (model4.B 1 ++ [step4.q]) 9000000000000 (model4.caps 1) (model4.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6705000000000, 9000000000000], [2835000000000,
      -9000000000000]) (some (3, 3, 1)) none (.next ([5625000000000], [3915000000000]) none none
      (.next ([4545000000000, -9000000000000], [3915000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-2835000000000, 9000000000000], [9540000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-3915000000000], [9540000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-3915000000000, 0], [8460000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-1080000000000, -9000000000000], [2160000000000, 18000000000000]) (some (3, 1, 0))
      (some (3, 1, 3)) (.terminal (some (3, 1, 3)) (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded4_2 : ExcludedOn (model4.B 2 ++ [step4.q]) 9000000000000 (model4.caps 2) (model4.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7920000000000, -9000000000000], [1080000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2835000000000, -9000000000000],
      [540000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4545000000000,
      -9000000000000], [3915000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([540000000000],
      [3375000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1080000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-540000000000, -9000000000000],
      [3375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3915000000000, 0],
      [8460000000000, -9000000000000]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-3375000000000],
      [3915000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded4_3 : ExcludedOn (model4.B 3 ++ [step4.q]) 9000000000000 (model4.caps 3) (model4.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6990000000000], [1080000000000, 9000000000000])
      (some (1, 0, 3)) (some (2, 0, 3)) (.next ([1905000000000], [1470000000000]) (some (2, 0, 3))
      (some (2, 0, 3)) (.next ([3375000000000], [5085000000000]) (some (2, 0, 1)) (some (2, 0, 1))
      (.next ([2295000000000, -9000000000000], [6165000000000, 9000000000000]) (some (2, 0, 1))
      (some (2, 0, 1)) (.next ([0], [1080000000000, 9000000000000]) (some (2, 0, 1)) (some (2, 3,
      1)) (.next ([-1080000000000, -9000000000000], [8070000000000, 9000000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([-1470000000000], [3375000000000]) (some (0, 3, 1)) (some (0, 3, 1))
      (.next ([-5085000000000], [8460000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-6165000000000, -9000000000000], [8460000000000]) (some (0, 3, 1)) (some (0, 3, 1))
      (.terminal (some (0, 3, 1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded4_1
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

theorem excluded5_1 : ExcludedOn (model5.B 1 ++ [step5.q]) 9000000000000 (model5.caps 1) (model5.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6615000000000, 9000000000000], [2745000000000,
      -9000000000000]) (some (3, 3, 1)) none (.next ([5535000000000], [3825000000000]) none none
      (.next ([4455000000000, -9000000000000], [3825000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-2745000000000, 9000000000000], [9360000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-3825000000000], [9360000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-3825000000000, 0], [8280000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-1080000000000, -9000000000000], [2160000000000, 18000000000000]) (some (3, 1, 0))
      (some (3, 1, 3)) (.terminal (some (3, 1, 3)) (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded5_2 : ExcludedOn (model5.B 2 ++ [step5.q]) 9000000000000 (model5.caps 2) (model5.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7920000000000, -9000000000000], [1080000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2745000000000, -9000000000000],
      [720000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4455000000000,
      -9000000000000], [3825000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([360000000000],
      [3465000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1080000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-720000000000, -9000000000000],
      [3465000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3825000000000, 0],
      [8280000000000, -9000000000000]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-3465000000000],
      [3825000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded5_3 : ExcludedOn (model5.B 3 ++ [step5.q]) 9000000000000 (model5.caps 3) (model5.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6990000000000], [1080000000000, 9000000000000])
      (some (1, 0, 3)) (some (2, 0, 3)) (.next ([1815000000000], [1650000000000]) (some (2, 0, 3))
      (some (2, 0, 3)) (.next ([3465000000000], [5175000000000]) (some (2, 0, 1)) (some (2, 0, 1))
      (.next ([2385000000000, -9000000000000], [6255000000000, 9000000000000]) (some (2, 0, 1))
      (some (2, 0, 1)) (.next ([0], [1080000000000, 9000000000000]) (some (2, 0, 1)) (some (2, 3,
      1)) (.next ([-1080000000000, -9000000000000], [8070000000000, 9000000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([-1650000000000], [3465000000000]) (some (0, 3, 1)) (some (0, 3, 1))
      (.next ([-5175000000000], [8640000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-6255000000000, -9000000000000], [8640000000000]) (some (0, 3, 1)) (some (0, 3, 1))
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded6_0 : ExcludedOn (model6.B 0 ++ [step6.q]) 9000000000000 (model6.caps 0) (model6.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5801400000000, 5220000000000], [46800000000,
      -2610000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([5711400000000, 5220000000000],
      [226800000000, -2610000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([540000000000],
      [45000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([5488200000000, 2610000000000],
      [673200000000, 2610000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([5126400000000,
      5220000000000], [766800000000, -2610000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([5398200000000, 2610000000000], [853200000000, 2610000000000]) (some (0, 7, 4)) (some (0, 7,
      4)) (.next ([4861800000000, -2610000000000], [986400000000, 5220000000000]) (some (0, 7, 4))
      (some (0, 7, 4)) (.next ([4771800000000, -2610000000000], [1166400000000, 5220000000000])
      (some (0, 7, 4)) (some (0, 7, 5)) (.next ([4813200000000, 2610000000000], [1393200000000,
      2610000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([7515000000000], [2295000000000])
      (some (0, 7, 5)) (some (0, 7, 5)) (.next ([7335000000000], [2385000000000]) (some (0, 7, 5))
      (some (0, 7, 5)) (.next ([6795000000000], [2340000000000]) (some (0, 7, 5)) (some (0, 7, 5))
      (.next ([4186800000000, -2610000000000], [1706400000000, 5220000000000]) (some (0, 7, 5))
      (some (7, 7, 5)) (.next ([313200000000, 2610000000000], [313200000000, 2610000000000]) (some
      (7, 7, 5)) (some (7, 7, 5)) (.next ([3866400000000, 5220000000000], [4321800000000,
      -2610000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([3553200000000, 2610000000000],
      [4008600000000, -5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([3553200000000,
      2610000000000], [4948200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
      ([2926800000000, -2610000000000], [4321800000000, -2610000000000]) (some (7, 3, 5)) (some (7,
      3, 5)) (.next ([45000000000], [675000000000]) (some (7, 3, 5)) (some (7, 3, 5))
      fan6Owner0Part0)))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded6_1 : ExcludedOn (model6.B 1 ++ [step6.q]) 9000000000000 (model6.caps 1) (model6.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_2 : ExcludedOn (model6.B 2 ++ [step6.q]) 9000000000000 (model6.caps 2) (model6.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_3 : ExcludedOn (model6.B 3 ++ [step6.q]) 9000000000000 (model6.caps 3) (model6.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded6_8 : ExcludedOn (model6.B 8 ++ [step6.q]) 9000000000000 (model6.caps 8) (model6.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5850000000000, -9000000000000], [1080000000000,
      9000000000000]) (some (0, 0, 3)) (some (0, 1, 3)) (.next ([5760000000000], [4365000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([4680000000000, -9000000000000], [4365000000000, 0])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2565000000000], [3195000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3,
      2)) (.next ([-1080000000000, -9000000000000], [6930000000000, 0]) (some (0, 3, 2)) (some (0,
      3, 2)) (.next ([-4365000000000], [10125000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-4365000000000, 0], [9045000000000, -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3195000000000], [5760000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded6_0
    · exact excluded6_1
    · exact excluded6_2
    · exact excluded6_3
    · exact (hj rfl).elim
    · exact excluded6_5
    · exact excluded6_6
    · exact excluded6_7
    · exact excluded6_8
    · exact excluded6_9
theorem next6 : model6.insert step6 = model7 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded7_0 : ExcludedOn (model7.B 0 ++ [step7.q]) 9000000000000 (model7.caps 0) (model7.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5801400000000, 5220000000000], [46800000000,
      -2610000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([5711400000000, 5220000000000],
      [226800000000, -2610000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([540000000000],
      [45000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([5488200000000, 2610000000000],
      [673200000000, 2610000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([5126400000000,
      5220000000000], [766800000000, -2610000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([5398200000000, 2610000000000], [853200000000, 2610000000000]) (some (0, 7, 4)) (some (0, 7,
      4)) (.next ([4861800000000, -2610000000000], [986400000000, 5220000000000]) (some (0, 7, 4))
      (some (0, 7, 4)) (.next ([4771800000000, -2610000000000], [1166400000000, 5220000000000])
      (some (0, 7, 4)) (some (0, 7, 5)) (.next ([4813200000000, 2610000000000], [1393200000000,
      2610000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([4186800000000, -2610000000000],
      [1706400000000, 5220000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([5400000000000],
      [4785000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([5220000000000], [4875000000000])
      (some (0, 7, 5)) (some (0, 7, 5)) (.next ([313200000000, 2610000000000], [313200000000,
      2610000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([4680000000000], [4830000000000])
      (some (0, 7, 5)) (some (0, 7, 5)) (.next ([1376400000000, 5220000000000], [4696800000000,
      -2610000000000]) (some (0, 7, 5)) (some (7, 7, 5)) (.next ([1063200000000, 2610000000000],
      [4383600000000, -5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([1063200000000,
      2610000000000], [5323200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
      ([436800000000, -2610000000000], [4696800000000, -2610000000000]) (some (7, 3, 5)) (some (7,
      3, 5)) (.next ([45000000000], [675000000000]) (some (7, 3, 5)) (some (7, 3, 5))
      fan7Owner0Part0)))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded7_1 : ExcludedOn (model7.B 1 ++ [step7.q]) 9000000000000 (model7.caps 1) (model7.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_2 : ExcludedOn (model7.B 2 ++ [step7.q]) 9000000000000 (model7.caps 2) (model7.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_3 : ExcludedOn (model7.B 3 ++ [step7.q]) 9000000000000 (model7.caps 3) (model7.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_5 : ExcludedOn (model7.B 5 ++ [step7.q]) 9000000000000 (model7.caps 5) (model7.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1080000000000, 9000000000000], [1080000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([3990000000000, 0], [4680000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3990000000000], [5760000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2910000000000, -9000000000000], [6840000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-1080000000000, -9000000000000],
      [2160000000000, 18000000000000]) (some (3, 1, 3)) (some (3, 2, 3)) (.next ([-4680000000000,
      9000000000000], [8670000000000, -9000000000000]) (some (3, 2, 3)) (some (3, 2, 3)) (.next
      ([-5760000000000], [9750000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-6840000000000,
      -9000000000000], [9750000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded7_6 : ExcludedOn (model7.B 6 ++ [step7.q]) 9000000000000 (model7.caps 6) (model7.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded7_7 : ExcludedOn (model7.B 7 ++ [step7.q]) 9000000000000 (model7.caps 7) (model7.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded7_0
    · exact excluded7_1
    · exact excluded7_2
    · exact excluded7_3
    · exact (hj rfl).elim
    · exact excluded7_5
    · exact excluded7_6
    · exact excluded7_7
    · exact excluded7_8
    · exact excluded7_9
theorem next7 : model7.insert step7 = model8 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint120000130000
end ConwaySoifer.Simplified.Certificates
