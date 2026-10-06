/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext240000250000
import Mathlib.Tactic.FinCases

/-!
# Sext 240000 250000 5

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
namespace Sext240000250000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner2Part0 : FanWitness := (.next ([240000000000], [648000000000]) (some (0, 3, 4)) (some
    (0, 3, 4)) (.next ([1338000000000], [4935000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([930000000000], [3750000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([180000000000],
    [2013000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([450000000000], [5175000000000])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([0], [5625000000000]) (some (0, 3, 4)) (some (0, 3,
    4)) (.next ([-60000000000], [1365000000000]) (some (0, 3, 4)) (some (0, 3, 5)) (.next
    ([-225000000000, 9000000000000], [1665000000000, -9000000000000]) (some (0, 3, 5)) (some (0, 3,
    5)) (.next ([-855000000000], [5115000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-1215000000000, 9000000000000], [6615000000000, 0]) (some (0, 3, 5)) (some (0, 6, 5)) (.next
    ([-2520000000000, 9000000000000], [6555000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-2487000000000], [6375000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3375000000000],
    [6615000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4185000000000], [8010000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2385000000000], [3825000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-1737000000000], [2487000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-2385000000000], [3375000000000]) (some (0, 6, 5)) (some (1, 6, 5)) (.next
    ([-4680000000000], [6555000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-5625000000000,
    0], [7785000000000, 9000000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-648000000000],
    [888000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-4935000000000], [6273000000000])
    (some (1, 6, 5)) (some (2, 6, 5)) (.next ([-3750000000000], [4680000000000]) (some (2, 6, 5))
    (some (2, 6, 5)) (.next ([-2013000000000], [2193000000000]) (some (2, 6, 5)) (some (2, 6, 5))
    (.next ([-5175000000000], [5625000000000]) (some (2, 6, 5)) (some (2, 6, 5)) (.terminal (some
    (2, 6, 5)) (some (2, 6, 0)) (some (2, 6, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner2Part0 : FanWitness := (.next ([3240000000000], [3375000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([4263000000000], [4680000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([750000000000], [1737000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([990000000000], [2385000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([1875000000000],
    [4680000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([2160000000000, 9000000000000],
    [5625000000000, 0]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([240000000000], [648000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([930000000000], [3750000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([180000000000], [2013000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([0], [5625000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-60000000000],
    [1365000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-1215000000000, 9000000000000],
    [6615000000000, 0]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2487000000000], [8763000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-3375000000000], [9003000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-2487000000000], [6375000000000]) (some (0, 3, 6)) (some (0, 4, 6))
    (.next ([-3375000000000], [6615000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-4680000000000], [8943000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1737000000000],
    [2487000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-2385000000000], [3375000000000])
    (some (0, 4, 6)) (some (1, 4, 6)) (.next ([-4680000000000], [6555000000000]) (some (1, 4, 6))
    (some (1, 4, 6)) (.next ([-5625000000000, 0], [7785000000000, 9000000000000]) (some (1, 4, 6))
    (some (1, 4, 6)) (.next ([-648000000000], [888000000000]) (some (1, 4, 6)) (some (1, 4, 6))
    (.next ([-3750000000000], [4680000000000]) (some (1, 4, 6)) (some (2, 4, 6)) (.next
    ([-2013000000000], [2193000000000]) (some (2, 4, 6)) (some (2, 4, 6)) (.terminal (some (2, 4,
    6)) (some (2, 6, 0)) (some (2, 6, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner2Part0 : FanWitness := (.next ([240000000000], [648000000000]) (some (0, 3, 4)) (some
    (0, 3, 4)) (.next ([930000000000], [3750000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([375000000000], [2505000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([180000000000],
    [2013000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([393000000000], [6000000000000])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([0], [5625000000000]) (some (0, 3, 4)) (some (0, 3,
    4)) (.next ([-60000000000], [1365000000000]) (some (0, 3, 4)) (some (0, 3, 5)) (.next
    ([-495000000000], [6240000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1215000000000,
    9000000000000], [6615000000000, 0]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1800000000000],
    [6180000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-2520000000000, 9000000000000],
    [6555000000000, 0]) (some (0, 3, 5)) (some (0, 6, 5)) (.next ([-2487000000000], [6375000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-345000000000, 9000000000000], [720000000000,
    -9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3375000000000], [6615000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-5250000000000], [8130000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-1737000000000], [2487000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-2385000000000], [3375000000000]) (some (0, 6, 5)) (some (1, 6, 5)) (.next
    ([-4680000000000], [6555000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-5625000000000,
    0], [7785000000000, 9000000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-648000000000],
    [888000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-3750000000000], [4680000000000])
    (some (1, 6, 5)) (some (2, 6, 5)) (.next ([-2505000000000], [2880000000000]) (some (2, 6, 5))
    (some (2, 6, 5)) (.next ([-2013000000000], [2193000000000]) (some (2, 6, 5)) (some (2, 6, 5))
    (.next ([-6000000000000], [6393000000000]) (some (2, 6, 5)) (some (2, 6, 5)) (.terminal (some
    (2, 6, 5)) (some (2, 6, 0)) (some (2, 6, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner1Part0 : FanWitness := (.next ([2385000000000], [1080000000000, -9000000000000]) (some
    (4, 5, 2)) (some (4, 5, 2)) (.next ([3015000000000, -9000000000000], [1440000000000, 0]) (some
    (4, 5, 2)) (some (4, 5, 2)) (.next ([5250000000000], [4110000000000]) (some (4, 5, 2)) (some (4,
    5, 2)) (.next ([2160000000000, 9000000000000], [2160000000000, 9000000000000]) (some (4, 5, 2))
    (some (4, 5, 2)) (.next ([4185000000000], [4230000000000]) (some (4, 5, 2)) (some (4, 5, 2))
    (.next ([2385000000000], [3240000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([1785000000000, 9000000000000], [6495000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([120000000000], [945000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([720000000000,
    9000000000000], [6615000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([225000000000,
    -9000000000000], [5400000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([0],
    [2160000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([-375000000000],
    [6495000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next ([-375000000000, 0], [4335000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1440000000000], [6615000000000])
    (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-1080000000000, 9000000000000], [3465000000000,
    -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1440000000000, 0], [4455000000000,
    -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-4110000000000], [9360000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2160000000000, -9000000000000], [4320000000000,
    18000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-4230000000000], [8415000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3240000000000], [5625000000000]) (some (0, 1, 4))
    (some (5, 1, 4)) (.next ([-6495000000000], [8280000000000, 9000000000000]) (some (5, 1, 4))
    (some (5, 1, 4)) (.next ([-945000000000], [1065000000000]) (some (5, 1, 4)) (some (5, 1, 4))
    (.next ([-6615000000000], [7335000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1, 4))
    (.next ([-5400000000000, -9000000000000], [5625000000000, 0]) (some (5, 1, 4)) (some (5, 1, 4))
    (.terminal (some (5, 1, 4)) (some (5, 1, 4)) (some (5, 1, 4)))))))))))))))))))))))))))

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1305000000000], [60000000000]) (some (0, 2, 6))
      (some (0, 2, 6)) (.next ([1440000000000, 0], [225000000000, -9000000000000]) (some (0, 2, 6))
      (some (0, 3, 6)) (.next ([4260000000000], [855000000000]) (some (0, 3, 4)) (some (0, 3, 4))
      (.next ([5400000000000, 9000000000000], [1215000000000, -9000000000000]) (some (0, 3, 4))
      (some (0, 3, 4)) (.next ([4035000000000, 9000000000000], [2520000000000, -9000000000000])
      (some (0, 3, 4)) (some (0, 3, 4)) (.next ([3888000000000], [2487000000000]) (some (0, 3, 4))
      (some (0, 3, 4)) (.next ([3240000000000], [3375000000000]) (some (0, 3, 4)) (some (0, 3, 4))
      (.next ([3825000000000], [4185000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
      ([1440000000000], [2385000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([750000000000],
      [1737000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([990000000000], [2385000000000])
      (some (0, 3, 4)) (some (0, 3, 4)) (.next ([1875000000000], [4680000000000]) (some (0, 3, 4))
      (some (0, 3, 4)) (.next ([2160000000000, 9000000000000], [5625000000000, 0]) (some (0, 3, 4))
      (some (0, 3, 4)) fan40Owner2Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_9 : ExcludedOn (model40.B 9 ++ [step40.q]) 9000000000000 (model40.caps 9)
    (model40.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked40 : StepValid model40 9000000000000 step40 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded40_0
    · exact (hj rfl).elim
    · exact excluded40_2
    · exact excluded40_3
    · exact excluded40_4
    · exact excluded40_5
    · exact excluded40_6
    · exact excluded40_7
    · exact excluded40_8
    · exact excluded40_9
theorem next40 : model40.insert step40 = model41 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded41_0 : ExcludedOn (model41.B 0 ++ [step41.q]) 9000000000000 (model41.caps 0)
    (model41.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1305000000000], [60000000000]) (some (0, 2, 6))
      (some (0, 2, 6)) (.next ([5400000000000, 9000000000000], [1215000000000, -9000000000000])
      (some (0, 2, 6)) (some (0, 3, 6)) (.next ([6276000000000], [2487000000000]) (some (0, 3, 6))
      (some (0, 3, 6)) (.next ([5628000000000], [3375000000000]) (some (0, 3, 6)) (some (0, 3, 6))
      (.next ([3888000000000], [2487000000000]) (some (0, 3, 6)) (some (0, 3, 6))
      fan41Owner2Part0)))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_4 : ExcludedOn (model41.B 4 ++ [step41.q]) 9000000000000 (model41.caps 4)
    (model41.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_8 : ExcludedOn (model41.B 8 ++ [step41.q]) 9000000000000 (model41.caps 8)
    (model41.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_9 : ExcludedOn (model41.B 9 ++ [step41.q]) 9000000000000 (model41.caps 9)
    (model41.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked41 : StepValid model41 9000000000000 step41 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded41_0
    · exact excluded41_1
    · exact excluded41_2
    · exact excluded41_3
    · exact excluded41_4
    · exact excluded41_5
    · exact excluded41_6
    · exact (hj rfl).elim
    · exact excluded41_8
    · exact excluded41_9
theorem next41 : model41.insert step41 = model42 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded42_0 : ExcludedOn (model42.B 0 ++ [step42.q]) 9000000000000 (model42.caps 0)
    (model42.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1305000000000], [60000000000]) (some (0, 2, 6))
      (some (0, 2, 6)) (.next ([5745000000000], [495000000000]) (some (0, 2, 6)) (some (0, 3, 6))
      (.next ([5400000000000, 9000000000000], [1215000000000, -9000000000000]) (some (0, 3, 6))
      (some (0, 3, 6)) (.next ([4380000000000], [1800000000000]) (some (0, 3, 6)) (some (0, 3, 6))
      (.next ([4035000000000, 9000000000000], [2520000000000, -9000000000000]) (some (0, 3, 6))
      (some (0, 3, 6)) (.next ([3888000000000], [2487000000000]) (some (0, 3, 6)) (some (0, 3, 6))
      (.next ([375000000000, 0], [345000000000, -9000000000000]) (some (0, 3, 6)) (some (0, 3, 6))
      (.next ([3240000000000], [3375000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
      ([2880000000000], [5250000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([750000000000],
      [1737000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([990000000000], [2385000000000])
      (some (0, 3, 4)) (some (0, 3, 4)) (.next ([1875000000000], [4680000000000]) (some (0, 3, 4))
      (some (0, 3, 4)) (.next ([2160000000000, 9000000000000], [5625000000000, 0]) (some (0, 3, 4))
      (some (0, 3, 4)) fan42Owner2Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_3 : ExcludedOn (model42.B 3 ++ [step42.q]) 9000000000000 (model42.caps 3)
    (model42.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_5 : ExcludedOn (model42.B 5 ++ [step42.q]) 9000000000000 (model42.caps 5)
    (model42.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_6 : ExcludedOn (model42.B 6 ++ [step42.q]) 9000000000000 (model42.caps 6)
    (model42.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_7 : ExcludedOn (model42.B 7 ++ [step42.q]) 9000000000000 (model42.caps 7)
    (model42.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2763000000000], [117000000000]) (some (0, 3, 1))
      (some (0, 3, 2)) (.next ([6495000000000], [720000000000, -9000000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([6495000000000], [2880000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([2160000000000, 9000000000000], [4452000000000, -9000000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([0], [6612000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-117000000000], [2880000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-720000000000,
      9000000000000], [7215000000000, -9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next
      ([-2880000000000], [9375000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4452000000000,
      9000000000000], [6612000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2))
      (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_8 : ExcludedOn (model42.B 8 ++ [step42.q]) 9000000000000 (model42.caps 8)
    (model42.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_9 : ExcludedOn (model42.B 9 ++ [step42.q]) 9000000000000 (model42.caps 9)
    (model42.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked42 : StepValid model42 9000000000000 step42 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded42_0
    · exact (hj rfl).elim
    · exact excluded42_2
    · exact excluded42_3
    · exact excluded42_4
    · exact excluded42_5
    · exact excluded42_6
    · exact excluded42_7
    · exact excluded42_8
    · exact excluded42_9
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6120000000000], [375000000000]) (some (4, 5, 1))
      (some (4, 5, 2)) (.next ([3960000000000, -9000000000000], [375000000000, 0]) (some (4, 5, 2))
      (some (4, 5, 2)) (.next ([5175000000000], [1440000000000]) (some (4, 5, 2)) (some (4, 5, 2))
      fan43Owner1Part0))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_2 : ExcludedOn (model43.B 2 ++ [step43.q]) 9000000000000 (model43.caps 2)
    (model43.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_3 : ExcludedOn (model43.B 3 ++ [step43.q]) 9000000000000 (model43.caps 3)
    (model43.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_4 : ExcludedOn (model43.B 4 ++ [step43.q]) 9000000000000 (model43.caps 4)
    (model43.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_6 : ExcludedOn (model43.B 6 ++ [step43.q]) 9000000000000 (model43.caps 6)
    (model43.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5535000000000, 9000000000000], [225000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2385000000000], [1080000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([3375000000000], [2385000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([2160000000000, 9000000000000], [6840000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2160000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-225000000000, 9000000000000],
      [5760000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1080000000000, 9000000000000],
      [3465000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2385000000000],
      [5760000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6840000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_7 : ExcludedOn (model43.B 7 ++ [step43.q]) 9000000000000 (model43.caps 7)
    (model43.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_8 : ExcludedOn (model43.B 8 ++ [step43.q]) 9000000000000 (model43.caps 8)
    (model43.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_9 : ExcludedOn (model43.B 9 ++ [step43.q]) 9000000000000 (model43.caps 9)
    (model43.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked43 : StepValid model43 9000000000000 step43 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded43_1
    · exact excluded43_2
    · exact excluded43_3
    · exact excluded43_4
    · exact excluded43_5
    · exact excluded43_6
    · exact excluded43_7
    · exact excluded43_8
    · exact excluded43_9
theorem next43 : model43.insert step43 = model44 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext240000250000
end ConwaySoifer.Simplified.Certificates
