/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown135000140000
import Mathlib.Tactic.FinCases

/-!
# Aown 135000 140000 0

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
namespace Aown135000140000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan1Owner0Part0 : FanWitness := (.next ([348300000000, 2580000000000], [348300000000,
    2580000000000]) (some (7, 1, 7)) (some (7, 1, 7)) (.next ([126600000000, 5160000000000],
    [221700000000, -2580000000000]) (some (7, 1, 7)) (some (7, 2, 7)) (.next ([3231600000000,
    5160000000000], [6116700000000, -2580000000000]) (some (7, 2, 7)) (some (7, 2, 7)) (.next
    ([2883300000000, 2580000000000], [5768400000000, -5160000000000]) (some (0, 2, 7)) (some (0, 2,
    7)) (.next ([2883300000000, 2580000000000], [6813300000000, 2580000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([348300000000, 2580000000000], [918300000000, 2580000000000]) (some (0,
    2, 7)) (some (0, 2, 7)) (.next ([2186700000000, -2580000000000], [6116700000000,
    -2580000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([2186700000000, -2580000000000],
    [7161600000000, 5160000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([1965000000000],
    [7035000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([1838400000000, -5160000000000],
    [6813300000000, 2580000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([0, 0],
    [1044900000000, 7740000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-221700000000,
    2580000000000], [918300000000, 2580000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-348300000000, -2580000000000], [1266600000000, 5160000000000]) (some (0, 2, 7)) (some (0, 2,
    7)) (.next ([-126600000000, -5160000000000], [348300000000, 2580000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-348300000000, -2580000000000], [696600000000, 5160000000000]) (some
    (0, 2, 7)) (some (0, 3, 7)) (.next ([-221700000000, 2580000000000], [348300000000,
    2580000000000]) (some (0, 3, 7)) (some (1, 3, 7)) (.next ([-6116700000000, 2580000000000],
    [9348300000000, 2580000000000]) (some (1, 3, 7)) (some (1, 4, 7)) (.next ([-5768400000000,
    5160000000000], [8651700000000, -2580000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-6813300000000, -2580000000000], [9696600000000, 5160000000000]) (some (1, 4, 7)) (some (1, 4,
    7)) (.next ([-918300000000, -2580000000000], [1266600000000, 5160000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-6116700000000, 2580000000000], [8303400000000, -5160000000000]) (some
    (1, 4, 7)) (some (1, 4, 7)) (.next ([-7161600000000, -5160000000000], [9348300000000,
    2580000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-7035000000000], [9000000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-6813300000000, -2580000000000], [8651700000000,
    -2580000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.terminal (some (1, 4, 7)) (some (1, 7, 7))
    (some (1, 7, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan2Owner0Part0 : FanWitness := (.next ([6983250000000], [1409250000000]) (some (6, 1, 7)) (some
    (6, 1, 7)) (.next ([7204950000000, -2580000000000], [1535850000000, 5160000000000]) (some (6, 1,
    7)) (some (6, 1, 7)) (.next ([696600000000, 5160000000000], [221700000000, -2580000000000])
    (some (6, 1, 7)) (some (6, 1, 7)) (.next ([918300000000, 2580000000000], [348300000000,
    2580000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([221700000000, -2580000000000],
    [126600000000, 5160000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([348300000000,
    2580000000000], [348300000000, 2580000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([126600000000, 5160000000000], [221700000000, -2580000000000]) (some (0, 1, 7)) (some (0, 2,
    7)) (.next ([348300000000, 2580000000000], [918300000000, 2580000000000]) (some (0, 2, 7)) (some
    (0, 2, 7)) (.next ([221700000000, -2580000000000], [696600000000, 5160000000000]) (some (0, 2,
    7)) (some (0, 2, 7)) (.next ([0, 0], [1044900000000, 7740000000000]) (some (0, 2, 7)) (some (0,
    2, 7)) (.next ([-142650000000, 5160000000000], [8044200000000, -2580000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-490950000000, 2580000000000], [8740800000000, 2580000000000]) (some
    (0, 2, 7)) (some (0, 2, 7)) (.next ([-490950000000, 2580000000000], [7695900000000,
    -5160000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-1187550000000, -2580000000000],
    [9089100000000, 5160000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-1187550000000,
    -2580000000000], [8044200000000, -2580000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-1409250000000], [8392500000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-1535850000000,
    -5160000000000], [8740800000000, 2580000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-221700000000, 2580000000000], [918300000000, 2580000000000]) (some (0, 2, 7)) (some (0, 7,
    7)) (.next ([-348300000000, -2580000000000], [1266600000000, 5160000000000]) (some (0, 7, 7))
    (some (0, 7, 7)) (.next ([-126600000000, -5160000000000], [348300000000, 2580000000000]) (some
    (0, 7, 7)) (some (0, 7, 7)) (.next ([-348300000000, -2580000000000], [696600000000,
    5160000000000]) (some (0, 7, 7)) (some (0, 7, 7)) (.next ([-221700000000, 2580000000000],
    [348300000000, 2580000000000]) (some (0, 7, 7)) (some (1, 7, 7)) (.next ([-918300000000,
    -2580000000000], [1266600000000, 5160000000000]) (some (1, 7, 7)) (some (1, 7, 7)) (.next
    ([-696600000000, -5160000000000], [918300000000, 2580000000000]) (some (1, 7, 7)) (some (1, 7,
    7)) (.terminal (some (1, 7, 7)) (some (1, 7, 7)) (some (1, 7, 7)))))))))))))))))))))))))))

theorem excluded0_1 : ExcludedOn (model0.B 1 ++ [step0.q]) 9000000000000 (model0.caps 1) (model0.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_2 : ExcludedOn (model0.B 2 ++ [step0.q]) 9000000000000 (model0.caps 2) (model0.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7785000000000, -9000000000000], [645000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([1215000000000, 9000000000000],
      [1215000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([1785000000000,
      9000000000000], [7215000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next
      ([570000000000], [8430000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [1215000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-645000000000,
      -9000000000000], [8430000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-1215000000000,
      -9000000000000], [2430000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-7215000000000, 9000000000000], [9000000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8430000000000], [9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded0_6 : ExcludedOn (model0.B 6 ++ [step0.q]) 9000000000000 (model0.caps 6) (model0.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7215000000000, -9000000000000], [1215000000000,
      9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([1215000000000, 9000000000000],
      [1215000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1215000000000,
      9000000000000], [7215000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0,
      0], [1215000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1215000000000,
      -9000000000000], [8430000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1215000000000,
      -9000000000000], [2430000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next
      ([-7215000000000, 9000000000000], [8430000000000]) (some (3, 1, 3)) (some (3, 1, 3))
      (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([696600000000, 5160000000000], [221700000000,
      -2580000000000]) (some (7, 1, 7)) (some (7, 1, 7)) (.next ([918300000000, 2580000000000],
      [348300000000, 2580000000000]) (some (7, 1, 7)) (some (7, 1, 7)) (.next ([221700000000,
      -2580000000000], [126600000000, 5160000000000]) (some (7, 1, 7)) (some (7, 1, 7))
      fan1Owner0Part0)))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded1_1 : ExcludedOn (model1.B 1 ++ [step1.q]) 9000000000000 (model1.caps 1) (model1.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1215000000000, 9000000000000], [1215000000000,
      9000000000000]) none none (.next ([1965000000000], [4500000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([1215000000000, 9000000000000], [3285000000000, -9000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([1215000000000, 9000000000000], [6465000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0, 0], [5250000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-1215000000000, -9000000000000], [2430000000000, 18000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-4500000000000], [6465000000000]) (some (3, 1, 2)) none (.next
      ([-3285000000000, 9000000000000], [4500000000000, 0]) none none (.next ([-6465000000000],
      [7680000000000, 9000000000000]) none none (.terminal none none none))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6465000000000], [1320000000000, -9000000000000])
      (some (2, 0, 1)) (some (3, 0, 2)) (.next ([6465000000000], [2535000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([5250000000000, -9000000000000], [2535000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1215000000000, 9000000000000], [6570000000000, -18000000000000])
      (some (3, 0, 2)) (some (4, 0, 2)) (.next ([1215000000000, 9000000000000], [7785000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0], [7785000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-1320000000000, 9000000000000],
      [7785000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2535000000000],
      [9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2535000000000, 0],
      [7785000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-6570000000000,
      18000000000000], [7785000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-7785000000000, 9000000000000], [9000000000000, 0]) (some (4, 0, 2)) (some (4, 1, 2))
      (.terminal (some (4, 1, 2)) (some (0, 1, 2)) (some (4, 1, 2))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7901550000000, 2580000000000], [142650000000,
      -5160000000000]) (some (7, 1, 7)) (some (7, 1, 7)) (.next ([8249850000000, 5160000000000],
      [490950000000, -2580000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([7204950000000,
      -2580000000000], [490950000000, -2580000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([7901550000000, 2580000000000], [1187550000000, 2580000000000]) (some (6, 1, 7)) (some (6, 1,
      7)) (.next ([6856650000000, -5160000000000], [1187550000000, 2580000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) fan2Owner0Part0)))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_1 : ExcludedOn (model2.B 1 ++ [step2.q]) 9000000000000 (model2.caps 1) (model2.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1215000000000, 9000000000000], [1215000000000,
      9000000000000]) none none (.next ([231750000000, -9000000000000], [375750000000,
      9000000000000]) none none (.next ([1446750000000], [3660750000000]) none none (.next
      ([1215000000000, 9000000000000], [3285000000000, -9000000000000]) none none (.next ([0],
      [5715000000000, 9000000000000]) none none (.next ([-1215000000000, -9000000000000],
      [2430000000000, 18000000000000]) none none (.next ([-375750000000, -9000000000000],
      [607500000000, 0]) none none (.next ([-3660750000000], [5107500000000]) none none (.next
      ([-3285000000000, 9000000000000], [4500000000000, 0]) none none (.terminal none none
      none))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
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

theorem excluded2_7 : ExcludedOn (model2.B 7 ++ [step2.q]) 9000000000000 (model2.caps 7) (model2.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([231750000000, -9000000000000], [375750000000,
      9000000000000]) (some (2, 4, 1)) (some (3, 4, 2)) (.next ([1446750000000], [6945750000000,
      -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1215000000000, 9000000000000],
      [6570000000000, -18000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1446750000000],
      [8160750000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1215000000000, 9000000000000],
      [7785000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([231750000000,
      -9000000000000], [8160750000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0],
      [7785000000000, -9000000000000]) (some (3, 4, 2)) (some (4, 4, 2)) (.next ([-375750000000,
      -9000000000000], [607500000000, 0]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-6945750000000,
      9000000000000], [8392500000000, -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-6570000000000, 18000000000000], [7785000000000, -9000000000000]) (some (4, 0, 2)) (some (4,
      0, 2)) (.next ([-8160750000000], [9607500000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next
      ([-7785000000000, 9000000000000], [9000000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-8160750000000, 0], [8392500000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.terminal (some (4, 1, 2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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
    0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8160750000000, 0], [607500000000,
      9000000000000]) (some (0, 0, 4)) (some (0, 0, 4)) (.next ([7785000000000, -9000000000000],
      [1215000000000, 9000000000000]) (some (0, 0, 4)) (some (0, 1, 4)) (.next ([2535000000000, 0],
      [1215000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([4335000000000],
      [4665000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([4335000000000, 0], [5880000000000,
      9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([231750000000, -9000000000000],
      [375750000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1800000000000],
      [4665000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1446750000000], [3825750000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1215000000000, 9000000000000], [3450000000000,
      -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([607500000000], [5018250000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([607500000000], [7553250000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([0, 0], [1215000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-607500000000, -9000000000000], [8768250000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-1215000000000, -9000000000000], [9000000000000, 0]) (some (0, 1,
      4)) (some (0, 1, 4)) (.next ([-1215000000000, -9000000000000], [3750000000000, 9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-4665000000000], [9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5880000000000, -9000000000000], [10215000000000, 9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-375750000000, -9000000000000], [607500000000, 0])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4665000000000], [6465000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-3825750000000], [5272500000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-3450000000000, 9000000000000], [4665000000000, 0]) (some (0, 1, 3)) (some (0, 4, 3))
      (.next ([-5018250000000], [5625750000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-7553250000000], [8160750000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 200 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3120000000000, -9000000000000], [1215000000000,
      9000000000000]) (some (2, 0, 1)) (some (3, 0, 2)) (.next ([1215000000000, 9000000000000],
      [3450000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1215000000000,
      9000000000000], [6570000000000, -18000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([1215000000000, 9000000000000], [7785000000000, -9000000000000]) (some (3, 0, 2)) (some (3,
      0, 2)) (.next ([0, 0], [7785000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2))
      (.next ([-1215000000000, -9000000000000], [4335000000000]) (some (0, 0, 2)) (some (0, 0, 2))
      (.next ([-3450000000000, 9000000000000], [4665000000000, 0]) (some (0, 0, 2)) (some (0, 0, 2))
      (.next ([-6570000000000, 18000000000000], [7785000000000, -9000000000000]) (some (0, 0, 2))
      (some (0, 4, 2)) (.next ([-7785000000000, 9000000000000], [9000000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 1, 2)) (some (0, 4, 2))))))))))))) (den
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

theorem excluded4_1 : ExcludedOn (model4.B 1 ++ [step4.q]) 9000000000000 (model4.caps 1) (model4.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7590000000000, 9000000000000], [972000000000,
      -9000000000000]) none none (.next ([5160000000000, -9000000000000], [2187000000000, 0]) none
      none (.next ([1215000000000, 9000000000000], [1215000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1215000000000, 9000000000000], [3450000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1710000000000], [6852000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0], [5880000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-972000000000, 9000000000000], [8562000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-2187000000000, 0], [7347000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-1215000000000, -9000000000000], [2430000000000, 18000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-3450000000000, 9000000000000], [4665000000000, 0]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-6852000000000], [8562000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.terminal (some (3, 1, 2)) none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded4_2 : ExcludedOn (model4.B 2 ++ [step4.q]) 9000000000000 (model4.caps 2) (model4.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2097000000000], [90000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([8160750000000, 0], [607500000000, 9000000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7785000000000, -9000000000000], [1215000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2187000000000], [438000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([5535750000000], [1579500000000]) (some (0, 4, 1)) (some (0, 4, 1))
      (.next ([5160000000000, -9000000000000], [2187000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1))
      (.next ([2535000000000, 0], [1215000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1))
      (.next ([972000000000, -9000000000000], [1653000000000, 9000000000000]) (some (0, 1, 1)) (some
      (0, 1, 1)) (.next ([607500000000], [5018250000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next
      ([607500000000], [7553250000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([0, 0],
      [1215000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-90000000000],
      [2187000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-607500000000, -9000000000000],
      [8768250000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1215000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-438000000000], [2625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1579500000000],
      [7115250000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2187000000000, 0],
      [7347000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1215000000000,
      -9000000000000], [3750000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1653000000000, -9000000000000], [2625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-5018250000000], [5625750000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-7553250000000], [8160750000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded4_3 : ExcludedOn (model4.B 3 ++ [step4.q]) 9000000000000 (model4.caps 3) (model4.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1215000000000, 9000000000000], [1215000000000,
      9000000000000]) (some (1, 0, 3)) (some (2, 0, 3)) (.next ([2625000000000, 0], [5598000000000,
      -9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([2625000000000], [6813000000000])
      (some (2, 0, 3)) (some (2, 0, 3)) (.next ([1410000000000, -9000000000000], [8028000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([0], [1215000000000, 9000000000000])
      (some (2, 0, 3)) (some (2, 3, 3)) (.next ([-1215000000000, -9000000000000], [2430000000000,
      18000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-5598000000000, 9000000000000],
      [8223000000000, -9000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-6813000000000],
      [9438000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-8028000000000, -9000000000000],
      [9438000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3, 1)) (some (0, 3,
      1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5962500000000], [202500000000]) none none (.next
      ([5677500000000, 9000000000000], [285000000000, -9000000000000]) none none (.next
      ([3247500000000, -9000000000000], [1500000000000, 0]) none none (.next ([1215000000000,
      9000000000000], [1215000000000, 9000000000000]) none none (.next ([1215000000000,
      9000000000000], [3450000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([0], [5880000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-202500000000], [6165000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-285000000000,
      9000000000000], [5962500000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1500000000000,
      0], [4747500000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-1215000000000, -9000000000000], [2430000000000, 18000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-3450000000000, 9000000000000], [4665000000000, 0]) (some (3, 1, 2)) none
      (.terminal none none none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded5_2 : ExcludedOn (model5.B 2 ++ [step5.q]) 9000000000000 (model5.caps 2) (model5.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8160750000000, 0], [607500000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7785000000000, -9000000000000],
      [1215000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3623250000000],
      [892500000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1500000000000], [502500000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([3247500000000, -9000000000000], [1500000000000, 0])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([2535000000000, 0], [1215000000000, 9000000000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([231750000000, -9000000000000], [375750000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([607500000000], [5018250000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([607500000000], [7553250000000]) (some (0, 1, 1))
      (some (0, 1, 2)) (.next ([285000000000, -9000000000000], [4252500000000, 9000000000000]) (some
      (0, 1, 2)) (some (0, 1, 2)) (.next ([0, 0], [1215000000000, 9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-607500000000, -9000000000000], [8768250000000, 9000000000000])
      (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-1215000000000, -9000000000000], [9000000000000,
      0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-892500000000], [4515750000000]) (some (0, 1,
      3)) (some (0, 1, 3)) (.next ([-502500000000], [2002500000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-1500000000000, 0], [4747500000000, -9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-1215000000000, -9000000000000], [3750000000000, 9000000000000]) (some (0, 1,
      3)) (some (0, 1, 3)) (.next ([-375750000000, -9000000000000], [607500000000, 0]) (some (0, 1,
      3)) (some (0, 1, 3)) (.next ([-5018250000000], [5625750000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-7553250000000], [8160750000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-4252500000000, -9000000000000], [4537500000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.terminal (some (0, 1, 3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4252500000000, 9000000000000], [285000000000,
      -9000000000000]) none none (.next ([4537500000000], [1627500000000]) none none (.next
      ([1822500000000, -9000000000000], [1500000000000, 0]) none none (.next ([1215000000000,
      9000000000000], [1215000000000, 9000000000000]) none none (.next ([1215000000000,
      9000000000000], [3450000000000, -9000000000000]) none none (.next ([0], [5880000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-285000000000, 9000000000000],
      [4537500000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1627500000000], [6165000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1500000000000, 0], [3322500000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1215000000000, -9000000000000],
      [2430000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3450000000000,
      9000000000000], [4665000000000, 0]) (some (3, 1, 2)) none (.terminal none none
      none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

theorem excluded6_2 : ExcludedOn (model6.B 2 ++ [step6.q]) 9000000000000 (model6.caps 2) (model6.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8160750000000, 0], [607500000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7785000000000, -9000000000000],
      [1215000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2198250000000],
      [892500000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2535000000000, 0], [1215000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1822500000000, -9000000000000],
      [1500000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1500000000000],
      [1927500000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([231750000000, -9000000000000],
      [375750000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1500000000000],
      [4462500000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([607500000000], [5018250000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([607500000000], [7553250000000]) (some (0, 1, 1))
      (some (0, 1, 2)) (.next ([285000000000, -9000000000000], [5677500000000, 9000000000000]) (some
      (0, 1, 2)) (some (0, 1, 2)) (.next ([0, 0], [1215000000000, 9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-607500000000, -9000000000000], [8768250000000, 9000000000000])
      (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-1215000000000, -9000000000000], [9000000000000,
      0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-892500000000], [3090750000000]) (some (0, 1,
      3)) (some (0, 1, 3)) (.next ([-1215000000000, -9000000000000], [3750000000000, 9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1500000000000, 0], [3322500000000,
      -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1927500000000], [3427500000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-375750000000, -9000000000000], [607500000000, 0])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4462500000000], [5962500000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-5018250000000], [5625750000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-7553250000000], [8160750000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-5677500000000, -9000000000000], [5962500000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.terminal (some (0, 1, 3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded7_1 : ExcludedOn (model7.B 1 ++ [step7.q]) 9000000000000 (model7.caps 1) (model7.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3840000000000, 9000000000000], [300000000000,
      -9000000000000]) none none (.next ([4140000000000], [2040000000000]) none none (.next
      ([1215000000000, 9000000000000], [1215000000000, 9000000000000]) none none (.next
      ([1410000000000, -9000000000000], [1515000000000, 0]) none none (.next ([1215000000000,
      9000000000000], [3450000000000, -9000000000000]) none none (.next ([0], [5880000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-300000000000, 9000000000000],
      [4140000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2040000000000], [6180000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1215000000000, -9000000000000], [2430000000000,
      18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1515000000000, 0],
      [2925000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3450000000000,
      9000000000000], [4665000000000, 0]) (some (3, 1, 2)) none (.terminal none none
      none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

theorem excluded7_2 : ExcludedOn (model7.B 2 ++ [step7.q]) 9000000000000 (model7.caps 2) (model7.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8160750000000, 0], [607500000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7785000000000, -9000000000000],
      [1215000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2535000000000, 0],
      [1215000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1785750000000],
      [907500000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1410000000000, -9000000000000],
      [1515000000000, 0]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1515000000000],
      [2325000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([231750000000, -9000000000000],
      [375750000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([1515000000000],
      [4860000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([607500000000], [5018250000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([607500000000], [7553250000000]) (some (0, 1, 1))
      (some (0, 1, 2)) (.next ([300000000000, -9000000000000], [6075000000000, 9000000000000]) (some
      (0, 1, 2)) (some (0, 1, 2)) (.next ([0, 0], [1215000000000, 9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-607500000000, -9000000000000], [8768250000000, 9000000000000])
      (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-1215000000000, -9000000000000], [9000000000000,
      0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1215000000000, -9000000000000],
      [3750000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-907500000000],
      [2693250000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1515000000000, 0],
      [2925000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2325000000000],
      [3840000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-375750000000, -9000000000000],
      [607500000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4860000000000],
      [6375000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5018250000000], [5625750000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-7553250000000], [8160750000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-6075000000000, -9000000000000], [6375000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (4, 1, 0)) (some (4, 1,
      3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

theorem excluded7_3 : ExcludedOn (model7.B 3 ++ [step7.q]) 9000000000000 (model7.caps 3) (model7.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded7_4 : ExcludedOn (model7.B 4 ++ [step7.q]) 9000000000000 (model7.caps 4) (model7.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded7_5 : ExcludedOn (model7.B 5 ++ [step7.q]) 9000000000000 (model7.caps 5) (model7.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded7_6 : ExcludedOn (model7.B 6 ++ [step7.q]) 9000000000000 (model7.caps 6) (model7.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded7_7 : ExcludedOn (model7.B 7 ++ [step7.q]) 9000000000000 (model7.caps 7) (model7.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded7_8 : ExcludedOn (model7.B 8 ++ [step7.q]) 9000000000000 (model7.caps 8) (model7.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded7_9 : ExcludedOn (model7.B 9 ++ [step7.q]) 9000000000000 (model7.caps 9) (model7.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked7 : StepValid model7 9000000000000 step7 0 1 200 := by
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

end Aown135000140000
end ConwaySoifer.Simplified.Certificates
