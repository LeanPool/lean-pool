/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across012500017500
import Mathlib.Tactic.FinCases

/-!
# Across 012500 017500 0

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
namespace Across012500017500

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan4Owner0Part0 : FanWitness := (.next ([7875000000000], [900000000000]) (some (5, 1, 3)) (some
    (5, 1, 3)) (.next ([298687500000, 5895000000000], [113156250000, -2947500000000]) (some (5, 1,
    3)) (some (5, 1, 3)) (.next ([261843750000, 2947500000000], [186843750000, 2947500000000]) (some
    (5, 1, 3)) (some (5, 1, 3)) (.next ([36843750000, 2947500000000], [36843750000, 2947500000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([188156250000, -2947500000000], [223687500000,
    5895000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([151312500000, -5895000000000],
    [186843750000, 2947500000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([150000000000],
    [375000000000]) (some (0, 2, 3)) (some (0, 6, 3)) (.next ([0, 0], [110531250000, 8842500000000])
    (some (0, 6, 3)) (some (0, 6, 4)) (.next ([-76312500000, 5895000000000], [8738156250000,
    -2947500000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-113156250000, 2947500000000],
    [8811843750000, 2947500000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-186843750000,
    -2947500000000], [8848687500000, 5895000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-223687500000, -5895000000000], [8811843750000, 2947500000000]) (some (0, 6, 4)) (some (0, 6,
    4)) (.next ([-375000000000], [8625000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-601312500000, 5895000000000], [8888156250000, -2947500000000]) (some (0, 3, 4)) (some (0, 3,
    4)) (.next ([-638156250000, 2947500000000], [8961843750000, 2947500000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([-711843750000, -2947500000000], [8998687500000, 5895000000000]) (some
    (0, 3, 4)) (some (0, 3, 4)) (.next ([-748687500000, -5895000000000], [8961843750000,
    2947500000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-900000000000], [8775000000000])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-113156250000, 2947500000000], [411843750000,
    2947500000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-186843750000, -2947500000000],
    [448687500000, 5895000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-36843750000,
    -2947500000000], [73687500000, 5895000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([-223687500000, -5895000000000], [411843750000, 2947500000000]) (some (0, 3, 4)) (some (1, 3,
    4)) (.next ([-186843750000, -2947500000000], [338156250000, -2947500000000]) (some (1, 3, 4))
    (some (1, 3, 4)) (.next ([-375000000000], [525000000000]) (some (1, 3, 4)) (some (1, 3, 4))
    (.terminal (some (1, 3, 4)) (some (1, 3, 4)) (some (1, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan5Owner0Part0 : FanWitness := (.next ([8286843750000, 2947500000000], [601312500000,
    -5895000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8323687500000, 5895000000000],
    [638156250000, -2947500000000]) (some (4, 1, 3)) (some (5, 1, 3)) (.next ([8286843750000,
    2947500000000], [711843750000, 2947500000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([8213156250000, -2947500000000], [748687500000, 5895000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([5250000000000], [712500000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([36843750000, 2947500000000], [36843750000, 2947500000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([150000000000], [375000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([111187500000,
    5895000000000], [2925656250000, -2947500000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next
    ([74343750000, 2947500000000], [2999343750000, 2947500000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([0, 0], [110531250000, 8842500000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-76312500000, 5895000000000], [8738156250000, -2947500000000]) (some (0, 2, 4)) (some (0, 2,
    4)) (.next ([-113156250000, 2947500000000], [8811843750000, 2947500000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-186843750000, -2947500000000], [8848687500000, 5895000000000]) (some
    (0, 2, 4)) (some (0, 6, 4)) (.next ([-223687500000, -5895000000000], [8811843750000,
    2947500000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-187500000000], [5812500000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-601312500000, 5895000000000], [8888156250000,
    -2947500000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-638156250000, 2947500000000],
    [8961843750000, 2947500000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-711843750000,
    -2947500000000], [8998687500000, 5895000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([-748687500000, -5895000000000], [8961843750000, 2947500000000]) (some (0, 3, 4)) (some (0, 3,
    4)) (.next ([-712500000000], [5962500000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([-36843750000, -2947500000000], [73687500000, 5895000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([-375000000000], [525000000000]) (some (0, 3, 4)) (some (1, 3, 4)) (.next
    ([-2925656250000, 2947500000000], [3036843750000, 2947500000000]) (some (1, 3, 4)) (some (1, 3,
    4)) (.next ([-2999343750000, -2947500000000], [3073687500000, 5895000000000]) (some (1, 3, 4))
    (some (1, 3, 4)) (.terminal (some (1, 3, 4)) (some (1, 3, 4)) (some (1, 3,
    4)))))))))))))))))))))))))))

theorem excluded0_0 : ExcludedOn (model0.B 0 ++ [step0.q]) 9000000000000 (model0.caps 0) (model0.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8361843750000, 2947500000000], [1051312500000,
      -5895000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next ([8398687500000, 5895000000000],
      [1088156250000, -2947500000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([8288156250000,
      -2947500000000], [1088156250000, -2947500000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([8361843750000, 2947500000000], [1161843750000, 2947500000000]) (some (5, 1, 6)) (some (5, 1,
      6)) (.next ([8251312500000, -5895000000000], [1161843750000, 2947500000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([8288156250000, -2947500000000], [1198687500000, 5895000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([36843750000, 2947500000000], [36843750000,
      2947500000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0], [110531250000,
      8842500000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-1051312500000, 5895000000000],
      [9413156250000, -2947500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1088156250000,
      2947500000000], [9486843750000, 2947500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
      ([-1088156250000, 2947500000000], [9376312500000, -5895000000000]) (some (0, 2, 6)) (some (0,
      2, 6)) (.next ([-1161843750000, -2947500000000], [9523687500000, 5895000000000]) (some (0, 2,
      6)) (some (0, 2, 6)) (.next ([-1161843750000, -2947500000000], [9413156250000,
      -2947500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1198687500000, -5895000000000],
      [9486843750000, 2947500000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-36843750000,
      -2947500000000], [73687500000, 5895000000000]) (some (0, 2, 6)) (some (0, 6, 6)) (.terminal
      (some (0, 6, 6)) (some (1, 6, 6)) (some (1, 6, 6))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded0_1 : ExcludedOn (model0.B 1 ++ [step0.q]) 9000000000000 (model0.caps 1) (model0.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([112500000000, 9000000000000], [112500000000,
      9000000000000]) none none (.next ([562500000000, 9000000000000], [675000000000]) none none
      (.next ([450000000000, 0], [562500000000, -9000000000000]) none none (.next ([450000000000],
      [675000000000]) none none (.next ([0, 0], [112500000000, 9000000000000]) none none (.next
      ([-112500000000, -9000000000000], [225000000000, 18000000000000]) none none (.next
      ([-675000000000], [1237500000000, 9000000000000]) none none (.next ([-562500000000,
      9000000000000], [1012500000000, -9000000000000]) none none (.next ([-675000000000],
      [1125000000000]) none none (.terminal none none none))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded0_2 : ExcludedOn (model0.B 2 ++ [step0.q]) 9000000000000 (model0.caps 2) (model0.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8887500000000, -9000000000000], [112500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7875000000000], [450000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7762500000000, -9000000000000], [450000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7875000000000, 0], [562500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([112500000000, 9000000000000], [112500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [4612500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4387500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([450000000000, 0],
      [562500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([675000000000],
      [3375000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([112500000000, 9000000000000],
      [4387500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0],
      [112500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-112500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-450000000000], [8325000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-450000000000,
      0], [8212500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-562500000000,
      -9000000000000], [8437500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-112500000000, -9000000000000], [225000000000, 18000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-4612500000000, -9000000000000], [9112500000000, 9000000000000]) (some (0, 4,
      2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8887500000000, -9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-562500000000, 9000000000000], [1012500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3375000000000], [4050000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4387500000000, 9000000000000], [4500000000000, 0])
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8887500000000, -9000000000000], [112500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7875000000000], [1125000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7762500000000, -9000000000000], [1125000000000, 0])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7875000000000, 0], [1237500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([112500000000, 9000000000000], [112500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [4612500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4387500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([112500000000, 9000000000000],
      [1012500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([112500000000,
      9000000000000], [4387500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      0], [112500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-112500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1125000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1125000000000,
      0], [8887500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1237500000000, -9000000000000], [9112500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-112500000000, -9000000000000], [225000000000, 18000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-4612500000000, -9000000000000], [9112500000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-4500000000000, 0], [8887500000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1012500000000, 9000000000000],
      [1125000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4387500000000, 9000000000000],
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7762500000000, -9000000000000], [112500000000,
      9000000000000]) (some (3, 1, 2)) (some (4, 1, 3)) (.next ([450000000000, 0], [562500000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([112500000000, 9000000000000],
      [1012500000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([675000000000],
      [7762500000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([675000000000],
      [7875000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([562500000000, -9000000000000],
      [7875000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([112500000000, 9000000000000],
      [8775000000000, -18000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([112500000000,
      9000000000000], [8887500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([0], [675000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-112500000000,
      -9000000000000], [7875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-562500000000,
      9000000000000], [1012500000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1012500000000, 9000000000000], [1125000000000, 0]) (some (0, 1, 3)) (some (1, 1, 3)) (.next
      ([-7762500000000, 9000000000000], [8437500000000, -9000000000000]) (some (1, 1, 3)) (some (1,
      5, 3)) (.next ([-7875000000000], [8550000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next
      ([-7875000000000, 0], [8437500000000, -9000000000000]) (some (1, 5, 3)) (some (1, 5, 3))
      (.next ([-8775000000000, 18000000000000], [8887500000000, -9000000000000]) (some (1, 5, 3))
      (some (1, 5, 3)) (.next ([-8887500000000, 9000000000000], [9000000000000, 0]) (some (1, 5, 3))
      (some (1, 5, 3)) (.terminal (some (1, 5, 3)) (some (1, 2, 3)) (some (1, 5,
      3))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([562500000000, -9000000000000], [75000000000, 0])
      none none (.next ([750000000000], [450000000000]) none none (.next ([112500000000,
      9000000000000], [112500000000, 9000000000000]) none none (.next ([112500000000,
      9000000000000], [1012500000000, -9000000000000]) none none (.next ([37500000000,
      9000000000000], [750000000000]) none none (.next ([0], [1237500000000, 9000000000000]) none
      none (.next ([-75000000000, 0], [637500000000, -9000000000000]) none none (.next
      ([-450000000000], [1200000000000]) none none (.next ([-112500000000, -9000000000000],
      [225000000000, 18000000000000]) none none (.next ([-1012500000000, 9000000000000],
      [1125000000000, 0]) none none (.next ([-750000000000], [787500000000, 9000000000000]) none
      none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded2_2 : ExcludedOn (model2.B 2 ++ [step2.q]) 9000000000000 (model2.caps 2) (model2.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8325000000000, 0], [37500000000, 9000000000000])
      (some (0, 0, 2)) (some (0, 0, 2)) (.next ([8887500000000, -9000000000000], [112500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 4, 2)) (.next ([562500000000, -9000000000000],
      [75000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([112500000000, 9000000000000],
      [112500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0],
      [4612500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4387500000000,
      -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([750000000000],
      [3825000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([112500000000, 9000000000000],
      [4387500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([75000000000, 0],
      [8137500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([75000000000],
      [8250000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0, 0], [112500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-37500000000, -9000000000000],
      [8362500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-112500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-75000000000,
      0], [637500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-112500000000,
      -9000000000000], [225000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4612500000000, -9000000000000], [9112500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 3)) (.next ([-4500000000000, 0], [8887500000000, -9000000000000]) (some (0, 4, 3)) (some
      (0, 4, 3)) (.next ([-3825000000000], [4575000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-4387500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8137500000000, 9000000000000], [8212500000000, -9000000000000]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-8250000000000], [8325000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal
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
  apply ExclusionHint.sound (.witnessedFan (.next ([562500000000, -9000000000000], [75000000000, 0])
      (some (3, 5, 2)) (some (4, 5, 3)) (.next ([450000000000, 0], [562500000000, -9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([75000000000], [450000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([750000000000], [8212500000000, -9000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([750000000000], [8325000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([675000000000], [7762500000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([675000000000], [7875000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([637500000000, -9000000000000], [8325000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([562500000000, -9000000000000], [7875000000000]) (some (4, 1, 3)) (some (5, 1, 3)) (.next
      ([112500000000, 9000000000000], [8775000000000, -18000000000000]) (some (5, 1, 3)) (some (5,
      1, 3)) (.next ([112500000000, 9000000000000], [8887500000000, -9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([0, 0], [8887500000000, -9000000000000]) (some (5, 1, 3)) (some
      (5, 1, 3)) (.next ([-75000000000, 0], [637500000000, -9000000000000]) (some (5, 1, 3)) (some
      (5, 1, 3)) (.next ([-562500000000, 9000000000000], [1012500000000, -9000000000000]) (some (5,
      1, 3)) (some (5, 1, 3)) (.next ([-450000000000], [525000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([-8212500000000, 9000000000000], [8962500000000, -9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-8325000000000], [9075000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([-7762500000000, 9000000000000], [8437500000000, -9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-7875000000000], [8550000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([-8325000000000, 0], [8962500000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([-7875000000000, 0], [8437500000000, -9000000000000]) (some (5, 1, 3)) (some (5,
      1, 3)) (.next ([-8775000000000, 18000000000000], [8887500000000, -9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-8887500000000, 9000000000000], [9000000000000, 0]) (some (5, 1,
      3)) (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 2, 3)) (some (5, 2,
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
      -9000000000000]) none none (.next ([112500000000, 9000000000000], [112500000000,
      9000000000000]) none none (.next ([375000000000], [975000000000]) none none (.next
      ([112500000000, 9000000000000], [1012500000000, -9000000000000]) none none (.next ([0],
      [1237500000000, 9000000000000]) none none (.next ([-112500000000, 9000000000000],
      [375000000000]) none none (.next ([-112500000000, -9000000000000], [225000000000,
      18000000000000]) none none (.next ([-975000000000], [1350000000000]) none none (.next
      ([-1012500000000, 9000000000000], [1125000000000, 0]) none none (.terminal none none
      none))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 200
      (by decide +kernel)
  decide +kernel

theorem excluded3_2 : ExcludedOn (model3.B 2 ++ [step3.q]) 9000000000000 (model3.caps 2) (model3.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8887500000000, -9000000000000], [112500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([112500000000, 9000000000000],
      [112500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0],
      [4612500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4387500000000,
      -9000000000000], [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([375000000000],
      [4350000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([112500000000, 9000000000000],
      [4387500000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([112500000000,
      -9000000000000], [8737500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      0], [112500000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-112500000000,
      -9000000000000], [9000000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-112500000000,
      -9000000000000], [225000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4612500000000, -9000000000000], [9112500000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 3)) (.next ([-4500000000000, 0], [8887500000000, -9000000000000]) (some (0, 4, 3)) (some
      (0, 4, 3)) (.next ([-4350000000000], [4725000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-4387500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8737500000000, -9000000000000], [8850000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.terminal (some (0, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))) (den :=
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

theorem excluded4_0 : ExcludedOn (model4.B 0 ++ [step4.q]) 9000000000000 (model4.caps 0) (model4.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8661843750000, 2947500000000], [76312500000,
      -5895000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8698687500000, 5895000000000],
      [113156250000, -2947500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8661843750000,
      2947500000000], [186843750000, 2947500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([8588156250000, -2947500000000], [223687500000, 5895000000000]) (some (4, 1, 3)) (some (4, 1,
      3)) (.next ([8250000000000], [375000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([8286843750000, 2947500000000], [601312500000, -5895000000000]) (some (4, 1, 3)) (some (4, 1,
      3)) (.next ([8323687500000, 5895000000000], [638156250000, -2947500000000]) (some (4, 1, 3))
      (some (5, 1, 3)) (.next ([8286843750000, 2947500000000], [711843750000, 2947500000000]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([8213156250000, -2947500000000], [748687500000,
      5895000000000]) (some (5, 1, 3)) (some (5, 1, 3)) fan4Owner0Part0)))))))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded4_1 : ExcludedOn (model4.B 1 ++ [step4.q]) 9000000000000 (model4.caps 1) (model4.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded4_2 : ExcludedOn (model4.B 2 ++ [step4.q]) 9000000000000 (model4.caps 2) (model4.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([112500000000, 9000000000000], [112500000000,
      9000000000000]) (some (3, 0, 3)) (some (3, 1, 3)) (.next ([487500000000, 9000000000000],
      [8662500000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([375000000000],
      [8775000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([262500000000, -9000000000000],
      [8775000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0], [112500000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-112500000000, -9000000000000],
      [225000000000, 18000000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-8662500000000,
      9000000000000], [9150000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-8775000000000], [9150000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-8775000000000,
      0], [9037500000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 3, 3)) (some (0, 3, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded4_7 : ExcludedOn (model4.B 7 ++ [step4.q]) 9000000000000 (model4.caps 7) (model4.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded4_7
    · exact excluded4_8
    · exact excluded4_9
theorem next4 : model4.insert step4 = model5 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded5_0 : ExcludedOn (model5.B 0 ++ [step5.q]) 9000000000000 (model5.caps 0) (model5.ord
    0) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8661843750000, 2947500000000], [76312500000,
      -5895000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8698687500000, 5895000000000],
      [113156250000, -2947500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([8661843750000,
      2947500000000], [186843750000, 2947500000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([8588156250000, -2947500000000], [223687500000, 5895000000000]) (some (4, 1, 3)) (some (4, 1,
      3)) (.next ([5625000000000], [187500000000]) (some (4, 1, 3)) (some (4, 1, 3))
      fan5Owner0Part0)))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded5_1 : ExcludedOn (model5.B 1 ++ [step5.q]) 9000000000000 (model5.caps 1) (model5.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5887500000000, -9000000000000], [150000000000,
      9000000000000]) none none (.next ([6000000000000], [1162500000000]) none none (.next
      ([112500000000, 9000000000000], [112500000000, 9000000000000]) none none (.next
      ([112500000000, 9000000000000], [1012500000000, -9000000000000]) none none (.next
      ([75000000000, 9000000000000], [5925000000000, -9000000000000]) none none (.next ([0],
      [1237500000000, 9000000000000]) none none (.next ([-150000000000, -9000000000000],
      [6037500000000, 0]) none none (.next ([-1162500000000], [7162500000000]) none none (.next
      ([-112500000000, -9000000000000], [225000000000, 18000000000000]) none none (.next
      ([-1012500000000, 9000000000000], [1125000000000, 0]) none none (.next ([-5925000000000,
      9000000000000], [6000000000000]) none none (.terminal none none none))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded5_2 : ExcludedOn (model5.B 2 ++ [step5.q]) 9000000000000 (model5.caps 2) (model5.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
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

theorem excluded5_7 : ExcludedOn (model5.B 7 ++ [step5.q]) 9000000000000 (model5.caps 7) (model5.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded5_0
    · exact excluded5_1
    · exact excluded5_2
    · exact excluded5_3
    · exact excluded5_4
    · exact excluded5_5
    · exact (hj rfl).elim
    · exact excluded5_7
    · exact excluded5_8
    · exact excluded5_9
theorem next5 : model5.insert step5 = model6 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Across012500017500
end ConwaySoifer.Simplified.Certificates
