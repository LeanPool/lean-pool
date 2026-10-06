/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across112500117500
import Mathlib.Tactic.FinCases

/-!
# Across 112500 117500 0

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
namespace Across112500117500

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan3Owner0Part0 : FanWitness := (.next ([7443750000000], [1556250000000]) (some (4, 1, 6)) (some
    (4, 1, 6)) (.next ([7570687500000, 5295000000000], [1727156250000, -2647500000000]) (some (4, 1,
    6)) (some (4, 1, 6)) (.next ([595687500000, 5295000000000], [170906250000, -2647500000000])
    (some (4, 1, 6)) (some (4, 1, 6)) (.next ([7272843750000, 2647500000000], [2322843750000,
    2647500000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([6379312500000, -5295000000000],
    [2322843750000, 2647500000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([766593750000,
    2647500000000], [297843750000, 2647500000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next
    ([714656250000, -2647500000000], [595687500000, 5295000000000]) (some (4, 1, 6)) (some (4, 1,
    6)) (.next ([297843750000, 2647500000000], [297843750000, 2647500000000]) (some (4, 1, 6)) (some
    (4, 1, 6)) (.next ([468750000000], [543750000000]) (some (4, 1, 6)) (some (4, 2, 6)) (.next
    ([297843750000, 2647500000000], [766593750000, 2647500000000]) (some (4, 2, 6)) (some (0, 2, 6))
    (.next ([297843750000, 2647500000000], [1310343750000, 2647500000000]) (some (0, 2, 6)) (some
    (0, 2, 6)) (.next ([0, 0], [893531250000, 7942500000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-1012500000000], [7987500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1556250000000], [9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1727156250000,
    2647500000000], [9297843750000, 2647500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-170906250000, 2647500000000], [766593750000, 2647500000000]) (some (0, 2, 6)) (some (0, 2,
    6)) (.next ([-2322843750000, -2647500000000], [9595687500000, 5295000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-2322843750000, -2647500000000], [8702156250000, -2647500000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-297843750000, -2647500000000], [1064437500000,
    5295000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-595687500000, -5295000000000],
    [1310343750000, 2647500000000]) (some (0, 2, 6)) (some (0, 6, 6)) (.next ([-297843750000,
    -2647500000000], [595687500000, 5295000000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next
    ([-543750000000], [1012500000000]) (some (0, 6, 6)) (some (1, 6, 6)) (.next ([-766593750000,
    -2647500000000], [1064437500000, 5295000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next
    ([-1310343750000, -2647500000000], [1608187500000, 5295000000000]) (some (1, 6, 6)) (some (1, 6,
    6)) (.terminal (some (1, 6, 6)) (some (1, 6, 6)) (some (1, 6, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan4Owner0Part0 : FanWitness := (.next ([1310343750000, 2647500000000], [297843750000,
    2647500000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([595687500000, 5295000000000],
    [170906250000, -2647500000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([766593750000,
    2647500000000], [297843750000, 2647500000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next
    ([714656250000, -2647500000000], [595687500000, 5295000000000]) (some (4, 1, 6)) (some (4, 1,
    6)) (.next ([297843750000, 2647500000000], [297843750000, 2647500000000]) (some (4, 1, 6)) (some
    (4, 1, 6)) (.next ([468750000000], [543750000000]) (some (4, 1, 6)) (some (4, 2, 6)) (.next
    ([297843750000, 2647500000000], [766593750000, 2647500000000]) (some (4, 2, 6)) (some (0, 2, 6))
    (.next ([297843750000, 2647500000000], [1310343750000, 2647500000000]) (some (0, 2, 6)) (some
    (0, 2, 6)) (.next ([262500000000], [7481250000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([0, 0], [893531250000, 7942500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-281250000000], [8493750000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-452156250000,
    2647500000000], [8791593750000, 2647500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1047843750000, -2647500000000], [9089437500000, 5295000000000]) (some (0, 2, 6)) (some (0, 2,
    6)) (.next ([-1047843750000, -2647500000000], [8195906250000, -2647500000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-1345687500000, -5295000000000], [8791593750000, 2647500000000]) (some
    (0, 2, 6)) (some (0, 2, 6)) (.next ([-297843750000, -2647500000000], [1608187500000,
    5295000000000]) (some (0, 2, 6)) (some (0, 6, 6)) (.next ([-170906250000, 2647500000000],
    [766593750000, 2647500000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next ([-297843750000,
    -2647500000000], [1064437500000, 5295000000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next
    ([-595687500000, -5295000000000], [1310343750000, 2647500000000]) (some (0, 6, 6)) (some (0, 6,
    6)) (.next ([-297843750000, -2647500000000], [595687500000, 5295000000000]) (some (0, 6, 6))
    (some (0, 6, 6)) (.next ([-543750000000], [1012500000000]) (some (0, 6, 6)) (some (1, 6, 6))
    (.next ([-766593750000, -2647500000000], [1064437500000, 5295000000000]) (some (1, 6, 6)) (some
    (1, 6, 6)) (.next ([-1310343750000, -2647500000000], [1608187500000, 5295000000000]) (some (1,
    6, 6)) (some (1, 6, 6)) (.next ([-7481250000000], [7743750000000]) (some (1, 6, 6)) (some (1, 6,
    6)) (.terminal (some (1, 6, 4)) (some (1, 6, 4)) (some (1, 6, 4)))))))))))))))))))))))))))

theorem excluded0_0 : ExcludedOn (model0.B 0 ++ [step0.q]) 9000000000000 (model0.caps 0) (model0.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7929093750000, 2647500000000], [773062500000,
      -5295000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([8226937500000, 5295000000000],
      [1070906250000, -2647500000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([7333406250000,
      -2647500000000], [1070906250000, -2647500000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([7929093750000, 2647500000000], [1666593750000, 2647500000000]) (some (6, 1, 3)) (some (6, 1,
      3)) (.next ([7035562500000, -5295000000000], [1666593750000, 2647500000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([7333406250000, -2647500000000], [1964437500000, 5295000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([297843750000, 2647500000000], [297843750000,
      2647500000000]) (some (6, 1, 3)) (some (6, 1, 6)) (.next ([0, 0], [893531250000,
      7942500000000]) (some (6, 1, 6)) (some (6, 2, 6)) (.next ([-773062500000, 5295000000000],
      [8702156250000, -2647500000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([-1070906250000,
      2647500000000], [9297843750000, 2647500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
      ([-1070906250000, 2647500000000], [8404312500000, -5295000000000]) (some (0, 2, 6)) (some (0,
      2, 6)) (.next ([-1666593750000, -2647500000000], [9595687500000, 5295000000000]) (some (0, 2,
      6)) (some (0, 2, 6)) (.next ([-1666593750000, -2647500000000], [8702156250000,
      -2647500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1964437500000, -5295000000000],
      [9297843750000, 2647500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-297843750000,
      -2647500000000], [595687500000, 5295000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.terminal
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
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_2 : ExcludedOn (model1.B 2 ++ [step1.q]) 9000000000000 (model1.caps 2) (model1.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded1_3 : ExcludedOn (model1.B 3 ++ [step1.q]) 9000000000000 (model1.caps 3) (model1.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7631250000000], [900000000000]) (some (1, 0, 3))
      (some (2, 0, 3)) (.next ([7631250000000], [1012500000000, 9000000000000]) (some (2, 0, 1))
      (some (2, 0, 1)) (.next ([7518750000000, -9000000000000], [1012500000000, 9000000000000])
      (some (2, 0, 1)) (some (2, 0, 1)) (.next ([0], [1012500000000, 9000000000000]) (some (2, 0,
      1)) (some (2, 3, 1)) (.next ([-900000000000], [8531250000000]) (some (0, 3, 1)) (some (0, 3,
      1)) (.next ([-1012500000000, -9000000000000], [8643750000000, 9000000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([-1012500000000, -9000000000000], [8531250000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.terminal (some (0, 3, 1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded1_4 : ExcludedOn (model1.B 4 ++ [step1.q]) 9000000000000 (model1.caps 4) (model1.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8531250000000], [468750000000]) (some (2, 0, 3))
      (some (2, 1, 3)) (.next ([7518750000000, -9000000000000], [1481250000000, 9000000000000])
      (some (2, 1, 3)) (some (2, 1, 3)) (.next ([1012500000000, 9000000000000], [1012500000000,
      9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([543750000000, 9000000000000],
      [7987500000000, -9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([0, 0],
      [1012500000000, 9000000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next ([-468750000000],
      [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1481250000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1012500000000,
      -9000000000000], [2025000000000, 18000000000000]) (some (0, 1, 3)) (some (0, 3, 3)) (.next
      ([-7987500000000, 9000000000000], [8531250000000]) (some (0, 3, 3)) (some (0, 3, 3))
      (.terminal (some (0, 3, 2)) (some (0, 3, 2)) (some (0, 3, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded1_5 : ExcludedOn (model1.B 5 ++ [step1.q]) 9000000000000 (model1.caps 5) (model1.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded2_1 : ExcludedOn (model2.B 1 ++ [step2.q]) 9000000000000 (model2.caps 1) (model2.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7987500000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([1012500000000, 9000000000000],
      [1012500000000, 9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([2025000000000,
      9000000000000], [6975000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([1012500000000], [7987500000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [1012500000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, -9000000000000],
      [7987500000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1012500000000,
      -9000000000000], [2025000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-6975000000000, 9000000000000], [9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-7987500000000], [9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded2_2 : ExcludedOn (model2.B 2 ++ [step2.q]) 9000000000000 (model2.caps 2) (model2.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded2_3 : ExcludedOn (model2.B 3 ++ [step2.q]) 9000000000000 (model2.caps 3) (model2.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7987500000000], [1012500000000]) (some (1, 0,
      3)) (some (2, 0, 3)) (.next ([7631250000000], [1012500000000, 9000000000000]) (some (2, 0, 3))
      (some (2, 0, 3)) (.next ([6618750000000], [1368750000000]) (some (2, 0, 3)) (some (2, 0, 3))
      (.next ([6975000000000, -9000000000000], [2025000000000, 9000000000000]) (some (2, 0, 1))
      (some (2, 0, 1)) (.next ([0], [1012500000000, 9000000000000]) (some (2, 0, 1)) (some (2, 3,
      1)) (.next ([-1012500000000], [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-1012500000000, -9000000000000], [8643750000000, 9000000000000]) (some (0, 3, 1)) (some (0,
      3, 1)) (.next ([-1368750000000], [7987500000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-2025000000000, -9000000000000], [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1))
      (.terminal (some (0, 3, 1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded3_0 : ExcludedOn (model3.B 0 ++ [step3.q]) 9000000000000 (model3.caps 0) (model3.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6975000000000], [1012500000000]) (some (6, 1,
      6)) (some (6, 1, 6)) fan3Owner0Part0)) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 200
      (by decide +kernel)
  decide +kernel

theorem excluded3_1 : ExcludedOn (model3.B 1 ++ [step3.q]) 9000000000000 (model3.caps 1) (model3.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1012500000000, 9000000000000], [1012500000000,
      9000000000000]) none none (.next ([1012500000000, 9000000000000], [2025000000000]) none none
      (.next ([0, 0], [1012500000000, 9000000000000]) none none (.next ([-1012500000000,
      -9000000000000], [2025000000000, 18000000000000]) none none (.next ([-2025000000000],
      [3037500000000, 9000000000000]) none none (.terminal none none none))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7987500000000, -9000000000000], [1012500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([6975000000000, 0], [1012500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([1012500000000, 9000000000000],
      [1012500000000, 9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([2025000000000],
      [2475000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [5512500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3487500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1012500000000, 9000000000000],
      [3487500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [1012500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1012500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1012500000000, -9000000000000], [7987500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-1012500000000, -9000000000000], [2025000000000, 18000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-2475000000000], [4500000000000]) (some (0, 4, 2)) (some (0, 4,
      3)) (.next ([-5512500000000, -9000000000000], [10012500000000, 9000000000000]) (some (0, 2,
      3)) (some (0, 2, 3)) (.next ([-4500000000000, 0], [7987500000000, -9000000000000]) (some (0,
      2, 3)) (some (0, 2, 3)) (.next ([-3487500000000, 9000000000000], [4500000000000, 0]) (some (0,
      2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2,
      3))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
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
    · exact excluded3_1
    · exact excluded3_2
    · exact excluded3_3
    · exact excluded3_4
    · exact excluded3_5
    · exact excluded3_6
    · exact (hj rfl).elim
    · exact excluded3_8
    · exact excluded3_9
theorem next3 : model3.insert step3 = model4 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded4_0 : ExcludedOn (model4.B 0 ++ [step4.q]) 9000000000000 (model4.caps 0) (model4.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8212500000000], [281250000000]) (some (4, 1, 6))
      (some (4, 1, 6)) (.next ([8339437500000, 5295000000000], [452156250000, -2647500000000]) (some
      (4, 1, 6)) (some (4, 1, 6)) (.next ([8041593750000, 2647500000000], [1047843750000,
      2647500000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([7148062500000, -5295000000000],
      [1047843750000, 2647500000000]) (some (4, 1, 6)) (some (4, 1, 6)) (.next ([7445906250000,
      -2647500000000], [1345687500000, 5295000000000]) (some (4, 1, 6)) (some (4, 1, 6))
      fan4Owner0Part0)))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_2 : ExcludedOn (model4.B 2 ++ [step4.q]) 9000000000000 (model4.caps 2) (model4.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8250000000000, 0], [506250000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7987500000000, -9000000000000],
      [1012500000000, 9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([1012500000000,
      9000000000000], [1012500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4500000000000, 0], [5512500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([3487500000000, -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([1256250000000], [3750000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1012500000000,
      9000000000000], [3487500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([506250000000, 0], [6731250000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([506250000000], [7743750000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [1012500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-506250000000,
      -9000000000000], [8756250000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1012500000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-1012500000000, -9000000000000], [2025000000000, 18000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5512500000000, -9000000000000], [10012500000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [7987500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3750000000000], [5006250000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3487500000000, 9000000000000], [4500000000000, 0])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-6731250000000, 9000000000000], [7237500000000,
      -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-7743750000000], [8250000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2,
      3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([243750000000, -9000000000000], [262500000000,
      9000000000000]) (some (3, 5, 2)) (some (4, 5, 3)) (.next ([2025000000000], [5962500000000,
      -9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([2025000000000], [6975000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1256250000000], [7237500000000, -9000000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1256250000000], [8250000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([1012500000000, -9000000000000], [6975000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([1012500000000, 9000000000000], [7987500000000, -9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([243750000000, -9000000000000], [8250000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0, 0], [1012500000000, -9000000000000]) (some (0,
      5, 3)) (some (0, 5, 3)) (.next ([-262500000000, -9000000000000], [506250000000, 0]) (some (0,
      5, 3)) (some (0, 5, 3)) (.next ([-5962500000000, 9000000000000], [7987500000000,
      -9000000000000]) (some (0, 1, 3)) (some (5, 1, 3)) (.next ([-6975000000000], [9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-7237500000000, 9000000000000], [8493750000000,
      -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-8250000000000], [9506250000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-6975000000000, 0], [7987500000000,
      -9000000000000]) (some (5, 1, 3)) (some (5, 2, 3)) (.next ([-7987500000000, 9000000000000],
      [9000000000000, 0]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-8250000000000, 0],
      [8493750000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.terminal (some (5, 2, 3))
      (some (5, 2, 3)) (some (5, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
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

theorem excluded5_0 : ExcludedOn (model5.B 0 ++ [step5.q]) 9000000000000 (model5.caps 0) (model5.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded5_2 : ExcludedOn (model5.B 2 ++ [step5.q]) 9000000000000 (model5.caps 2) (model5.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7987500000000, -9000000000000], [1012500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([5175000000000], [3825000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([4162500000000, -9000000000000], [3825000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([5175000000000, 0], [4837500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([1012500000000, 9000000000000], [1012500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [5512500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3487500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1012500000000, 9000000000000],
      [2812500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1012500000000,
      9000000000000], [3487500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      0], [1012500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1012500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-3825000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3825000000000,
      0], [7987500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4837500000000, -9000000000000], [10012500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-1012500000000, -9000000000000], [2025000000000, 18000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-5512500000000, -9000000000000], [10012500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [7987500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2812500000000, 9000000000000],
      [3825000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3487500000000, 9000000000000],
      [4500000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4, 3)) (some (0, 2,
      0)) (some (0, 4, 3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4162500000000, -9000000000000], [1012500000000,
      9000000000000]) (some (3, 0, 2)) (some (4, 1, 3)) (.next ([2025000000000], [1800000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1012500000000, 9000000000000], [2812500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([2025000000000], [5962500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([2025000000000], [6975000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1012500000000, 9000000000000], [6975000000000,
      -18000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1012500000000, -9000000000000],
      [6975000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1012500000000, 9000000000000],
      [7987500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [1012500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1012500000000,
      -9000000000000], [5175000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1800000000000],
      [3825000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2812500000000, 9000000000000],
      [3825000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5962500000000, 9000000000000],
      [7987500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 5, 3)) (.next ([-6975000000000],
      [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6975000000000, 18000000000000],
      [7987500000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6975000000000,
      0], [7987500000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-7987500000000, 9000000000000], [9000000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3))
      (.terminal (some (0, 5, 3)) (some (0, 2, 3)) (some (0, 5, 3))))))))))))))))))))) (den :=
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
    · exact excluded5_0
    · exact (hj rfl).elim
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

end Across112500117500
end ConwaySoifer.Simplified.Certificates
