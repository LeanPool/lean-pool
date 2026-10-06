/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext150000160000
import Mathlib.Tactic.FinCases

/-!
# Sext 150000 160000 5

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
namespace Sext150000160000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner0Part0 : FanWitness := (.next ([0], [600000000000]) (some (7, 3, 5)) (some (7, 3, 5))
    (.next ([-75000000000], [4050000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-375000000000], [6375000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-825000000000],
    [6000000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-825000000000], [5700000000000])
    (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-900000000000], [4500000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-300000000000], [1350000000000]) (some (7, 3, 5)) (some (7, 3, 5))
    (.next ([-1275000000000], [5325000000000]) (some (7, 3, 5)) (some (7, 4, 5)) (.next
    ([-3525000000000], [8925000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-3525000000000],
    [8325000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-375000000000], [825000000000])
    (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-4875000000000], [9975000000000]) (some (7, 4, 5))
    (some (7, 4, 6)) (.next ([-3450000000000], [5625000000000]) (some (7, 4, 6)) (some (7, 4, 6))
    (.next ([-4050000000000], [6225000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-4275000000000], [6075000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4875000000000],
    [6675000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-1350000000000], [1650000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4725000000000], [5700000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5325000000000], [6300000000000]) (some (7, 4, 6)) (some (7, 4, 6))
    (.next ([-5100000000000], [5925000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-4350000000000], [4875000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4950000000000],
    [5475000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5925000000000], [6375000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-1200000000000], [1275000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.terminal (some (7, 4, 6)) (some (7, 4, 6)) (some (7, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner3Part0 : FanWitness := (.next ([4200000000000], [750000000000]) (some (4, 5, 5)) (some
    (4, 5, 5)) (.next ([3150000000000, -9000000000000], [675000000000, 9000000000000]) (some (4, 5,
    2)) (some (4, 5, 2)) (.next ([6225000000000, 9000000000000], [3225000000000, -9000000000000])
    (some (4, 5, 2)) (some (4, 5, 2)) (.next ([4875000000000], [4575000000000]) (some (4, 5, 2))
    (some (4, 5, 2)) (.next ([1350000000000, 9000000000000], [1350000000000, 9000000000000]) (some
    (4, 5, 2)) (some (4, 5, 2)) (.next ([2025000000000, 9000000000000], [2475000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([3525000000000, -9000000000000],
    [4575000000000]) (some (4, 5, 2)) (some (4, 5, 3)) (.next ([975000000000, 9000000000000],
    [4950000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([675000000000], [3825000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([300000000000], [4200000000000]) (some (4, 5, 3))
    (some (4, 5, 3)) (.next ([0], [1350000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3))
    (.next ([-375000000000], [4950000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-375000000000], [3600000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-450000000000], [3900000000000]) (some (0, 5, 3)) (some (1, 5, 3)) (.next ([-750000000000],
    [4950000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-675000000000, -9000000000000],
    [3825000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-3225000000000, 9000000000000],
    [9450000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-4575000000000], [9450000000000])
    (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-1350000000000, -9000000000000], [2700000000000,
    18000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-2475000000000, 9000000000000],
    [4500000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-4575000000000], [8100000000000,
    -9000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-4950000000000, 0], [5925000000000,
    9000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-3825000000000], [4500000000000])
    (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-4200000000000], [4500000000000]) (some (1, 5, 3))
    (some (1, 5, 3)) (.terminal (some (1, 5, 3)) (some (5, 5, 3)) (some (5, 5,
    3)))))))))))))))))))))))))))

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2700000000000], [375000000000]) (some (5, 0, 1))
      (some (5, 1, 1)) (.next ([3675000000000], [1650000000000]) (some (5, 1, 1)) (some (5, 1, 1))
      (.next ([3075000000000], [2625000000000]) (some (5, 1, 1)) (some (5, 1, 2)) (.next
      ([4425000000000], [4950000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([375000000000],
      [600000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1350000000000], [2325000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1350000000000, 9000000000000], [5325000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([750000000000], [3300000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([375000000000], [2700000000000, -9000000000000]) (some (5, 1, 2))
      (some (5, 1, 5)) (.next ([375000000000], [4050000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([0], [5325000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-375000000000],
      [3075000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1650000000000], [5325000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2625000000000], [5700000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([-4950000000000], [9375000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([-600000000000], [975000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-2325000000000], [3675000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-5325000000000], [6675000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-3300000000000], [4050000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2700000000000,
      9000000000000], [3075000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4050000000000], [4425000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1,
      5)) (some (0, 1, 5)) (some (0, 1, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4050000000000], [375000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([4950000000000], [975000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([3450000000000], [1875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([4950000000000], [4425000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5325000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-375000000000], [4425000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-975000000000], [5925000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([-1875000000000], [5325000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4425000000000], [9375000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_9 : ExcludedOn (model40.B 9 ++ [step40.q]) 9000000000000 (model40.caps 9)
    (model40.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded40_1
    · exact excluded40_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3975000000000], [75000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([6000000000000], [375000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([5175000000000], [825000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([4875000000000], [825000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3600000000000],
      [900000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1050000000000], [300000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([4050000000000], [1275000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([5400000000000], [3525000000000]) (some (6, 7, 4)) (some (7, 7, 4))
      (.next ([4800000000000], [3525000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
      ([450000000000], [375000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([5100000000000],
      [4875000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([2175000000000], [3450000000000])
      (some (7, 3, 4)) (some (7, 3, 4)) (.next ([2175000000000], [4050000000000]) (some (7, 3, 4))
      (some (7, 3, 4)) (.next ([1800000000000], [4275000000000]) (some (7, 3, 4)) (some (7, 3, 4))
      (.next ([1800000000000], [4875000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
      ([300000000000], [1350000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([975000000000],
      [4725000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([975000000000], [5325000000000])
      (some (7, 3, 4)) (some (7, 3, 4)) (.next ([825000000000], [5100000000000]) (some (7, 3, 4))
      (some (7, 3, 4)) (.next ([525000000000], [4350000000000]) (some (7, 3, 4)) (some (7, 3, 5))
      (.next ([525000000000], [4950000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
      ([450000000000], [5925000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([75000000000],
      [1200000000000]) (some (7, 3, 5)) (some (7, 3, 5)) fan41Owner0Part0))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4575000000000], [375000000000]) (some (3, 5, 5))
      (some (4, 5, 5)) (.next ([3225000000000, -9000000000000], [375000000000]) (some (4, 5, 5))
      (some (4, 5, 5)) (.next ([3450000000000], [450000000000]) (some (4, 5, 5)) (some (4, 5, 5))
      fan41Owner3Part0)))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_7 : ExcludedOn (model41.B 7 ++ [step41.q]) 9000000000000 (model41.caps 7)
    (model41.ord 7) 0 1 100 := by
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded41_5
    · exact excluded41_6
    · exact excluded41_7
    · exact excluded41_8
    · exact excluded41_9
theorem next41 : model41.insert step41 = model42 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded42_0 : ExcludedOn (model42.B 0 ++ [step42.q]) 9000000000000 (model42.caps 0)
    (model42.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_3 : ExcludedOn (model42.B 3 ++ [step42.q]) 9000000000000 (model42.caps 3)
    (model42.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4575000000000], [375000000000]) (some (3, 1, 5))
      (some (4, 1, 5)) (.next ([3225000000000, -9000000000000], [375000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([3450000000000], [450000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([3150000000000, -9000000000000], [675000000000, 9000000000000]) (some (4, 1, 5)) (some
      (4, 1, 5)) (.next ([5445000000000], [1350000000000, 9000000000000]) (some (4, 1, 5)) (some (4,
      1, 5)) (.next ([5070000000000], [4950000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([1350000000000, 9000000000000], [1350000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([2025000000000, 9000000000000], [2475000000000, -9000000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([1620000000000], [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([975000000000, 9000000000000], [4950000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([675000000000], [3825000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0],
      [1350000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-375000000000],
      [4950000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-375000000000], [3600000000000,
      -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-450000000000], [3900000000000])
      (some (0, 1, 5)) (some (1, 1, 5)) (.next ([-675000000000, -9000000000000], [3825000000000])
      (some (1, 1, 5)) (some (1, 2, 5)) (.next ([-1350000000000, -9000000000000], [6795000000000,
      9000000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-4950000000000], [10020000000000])
      (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-1350000000000, -9000000000000], [2700000000000,
      18000000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-2475000000000, 9000000000000],
      [4500000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-4500000000000], [6120000000000])
      (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-4950000000000, 0], [5925000000000, 9000000000000])
      (some (1, 2, 5)) (some (1, 5, 5)) (.next ([-3825000000000], [4500000000000]) (some (1, 5, 5))
      (some (1, 5, 5)) (.terminal (some (1, 5, 5)) (some (1, 5, 3)) (some (1, 5,
      5))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_5 : ExcludedOn (model42.B 5 ++ [step42.q]) 9000000000000 (model42.caps 5)
    (model42.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_6 : ExcludedOn (model42.B 6 ++ [step42.q]) 9000000000000 (model42.caps 6)
    (model42.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_7 : ExcludedOn (model42.B 7 ++ [step42.q]) 9000000000000 (model42.caps 7)
    (model42.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_8 : ExcludedOn (model42.B 8 ++ [step42.q]) 9000000000000 (model42.caps 8)
    (model42.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_9 : ExcludedOn (model42.B 9 ++ [step42.q]) 9000000000000 (model42.caps 9)
    (model42.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded42_1
    · exact (hj rfl).elim
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

theorem excluded43_0 : ExcludedOn (model43.B 0 ++ [step43.q]) 9000000000000 (model43.caps 0)
    (model43.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7275000000000, 9000000000000], [2400000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([5925000000000], [3750000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4575000000000, -9000000000000], [3750000000000, 0])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2400000000000, 9000000000000],
      [9675000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3750000000000], [9675000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3750000000000, 0], [8325000000000,
      -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 3)) (.terminal (some (3, 1, 3))
      (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_3 : ExcludedOn (model43.B 3 ++ [step43.q]) 9000000000000 (model43.caps 3)
    (model43.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_4 : ExcludedOn (model43.B 4 ++ [step43.q]) 9000000000000 (model43.caps 4)
    (model43.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_6 : ExcludedOn (model43.B 6 ++ [step43.q]) 9000000000000 (model43.caps 6)
    (model43.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked43 : StepValid model43 9000000000000 step43 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded43_0
    · exact excluded43_1
    · exact (hj rfl).elim
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

theorem excluded44_1 : ExcludedOn (model44.B 1 ++ [step44.q]) 9000000000000 (model44.caps 1)
    (model44.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_2 : ExcludedOn (model44.B 2 ++ [step44.q]) 9000000000000 (model44.caps 2)
    (model44.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_3 : ExcludedOn (model44.B 3 ++ [step44.q]) 9000000000000 (model44.caps 3)
    (model44.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_4 : ExcludedOn (model44.B 4 ++ [step44.q]) 9000000000000 (model44.caps 4)
    (model44.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_5 : ExcludedOn (model44.B 5 ++ [step44.q]) 9000000000000 (model44.caps 5)
    (model44.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5100000000000], [2025000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([5100000000000, 9000000000000], [2550000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3750000000000], [3900000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([525000000000], [1350000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1050000000000], [2850000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([1875000000000], [6075000000000]) (some (3, 1, 2)) (some (3, 1, 4)) (.next ([1350000000000,
      9000000000000], [6600000000000, 0]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0,
      9000000000000], [525000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0,
      0], [1350000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-2025000000000], [7125000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-2550000000000,
      9000000000000], [7650000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3900000000000], [7650000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-1350000000000], [1875000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-2850000000000], [3900000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6075000000000], [7950000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6600000000000,
      0], [7950000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-525000000000,
      9000000000000], [525000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_6 : ExcludedOn (model44.B 6 ++ [step44.q]) 9000000000000 (model44.caps 6)
    (model44.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3900000000000], [1350000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([5250000000000], [3750000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([1350000000000, 9000000000000], [7650000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 9000000000000], [3900000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1350000000000, 9000000000000]) (some (3, 0,
      2)) (some (3, 0, 2)) (.next ([-1350000000000], [5250000000000]) (some (3, 0, 2)) (some (3, 1,
      2)) (.next ([-3750000000000, 9000000000000], [9000000000000, -9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-7650000000000, 9000000000000], [9000000000000, 0]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-3900000000000, 9000000000000], [3900000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_7 : ExcludedOn (model44.B 7 ++ [step44.q]) 9000000000000 (model44.caps 7)
    (model44.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_8 : ExcludedOn (model44.B 8 ++ [step44.q]) 9000000000000 (model44.caps 8)
    (model44.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_9 : ExcludedOn (model44.B 9 ++ [step44.q]) 9000000000000 (model44.caps 9)
    (model44.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked44 : StepValid model44 9000000000000 step44 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded44_1
    · exact excluded44_2
    · exact excluded44_3
    · exact excluded44_4
    · exact excluded44_5
    · exact excluded44_6
    · exact excluded44_7
    · exact excluded44_8
    · exact excluded44_9
theorem next44 : model44.insert step44 = model45 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded45_1 : ExcludedOn (model45.B 1 ++ [step45.q]) 9000000000000 (model45.caps 1)
    (model45.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_2 : ExcludedOn (model45.B 2 ++ [step45.q]) 9000000000000 (model45.caps 2)
    (model45.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_3 : ExcludedOn (model45.B 3 ++ [step45.q]) 9000000000000 (model45.caps 3)
    (model45.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_4 : ExcludedOn (model45.B 4 ++ [step45.q]) 9000000000000 (model45.caps 4)
    (model45.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_5 : ExcludedOn (model45.B 5 ++ [step45.q]) 9000000000000 (model45.caps 5)
    (model45.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [1125000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([6000000000000, 9000000000000], [1650000000000, -9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4650000000000], [3000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1050000000000], [1950000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([525000000000], [1350000000000]) (some (3, 1, 2)) (some (3, 1, 4)) (.next
      ([1875000000000], [6075000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([1350000000000,
      9000000000000], [6600000000000, 0]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0,
      9000000000000], [525000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0,
      0], [1350000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-1125000000000], [7125000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1650000000000,
      9000000000000], [7650000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3000000000000], [7650000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-1950000000000], [3000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-1350000000000], [1875000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6075000000000], [7950000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6600000000000,
      0], [7950000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-525000000000,
      9000000000000], [525000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_6 : ExcludedOn (model45.B 6 ++ [step45.q]) 9000000000000 (model45.caps 6)
    (model45.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000], [1350000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([4350000000000], [4650000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([1350000000000, 9000000000000], [7650000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 9000000000000], [3000000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1350000000000, 9000000000000]) (some (3, 0,
      2)) (some (3, 0, 2)) (.next ([-1350000000000], [4350000000000]) (some (3, 0, 2)) (some (3, 1,
      2)) (.next ([-4650000000000, 9000000000000], [9000000000000, -9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-7650000000000, 9000000000000], [9000000000000, 0]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-3000000000000, 9000000000000], [3000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_7 : ExcludedOn (model45.B 7 ++ [step45.q]) 9000000000000 (model45.caps 7)
    (model45.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_8 : ExcludedOn (model45.B 8 ++ [step45.q]) 9000000000000 (model45.caps 8)
    (model45.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_9 : ExcludedOn (model45.B 9 ++ [step45.q]) 9000000000000 (model45.caps 9)
    (model45.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked45 : StepValid model45 9000000000000 step45 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded45_1
    · exact excluded45_2
    · exact excluded45_3
    · exact excluded45_4
    · exact excluded45_5
    · exact excluded45_6
    · exact excluded45_7
    · exact excluded45_8
    · exact excluded45_9
theorem next45 : model45.insert step45 = model46 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded46_1 : ExcludedOn (model46.B 1 ++ [step46.q]) 9000000000000 (model46.caps 1)
    (model46.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2250000000000], [5220000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2250000000000], [6570000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([900000000000, -9000000000000], [7920000000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [1350000000000, 9000000000000]) none
      none (.next ([-1350000000000, -9000000000000], [2700000000000, 18000000000000]) none none
      (.next ([-5220000000000, 9000000000000], [7470000000000, -9000000000000]) (some (3, 3, 0))
      (some (3, 3, 0)) (.next ([-6570000000000], [8820000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-7920000000000, -9000000000000], [8820000000000, 0]) (some (3, 1, 0)) (some (3, 1,
      0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_2 : ExcludedOn (model46.B 2 ++ [step46.q]) 9000000000000 (model46.caps 2)
    (model46.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_3 : ExcludedOn (model46.B 3 ++ [step46.q]) 9000000000000 (model46.caps 3)
    (model46.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_4 : ExcludedOn (model46.B 4 ++ [step46.q]) 9000000000000 (model46.caps 4)
    (model46.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_5 : ExcludedOn (model46.B 5 ++ [step46.q]) 9000000000000 (model46.caps 5)
    (model46.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8100000000000], [555000000000]) (some (4, 0, 4))
      (some (4, 1, 4)) (.next ([8100000000000, 9000000000000], [1080000000000, -9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([6750000000000], [2430000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([525000000000], [1350000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([1875000000000], [6075000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([1350000000000, 9000000000000], [6600000000000, 0]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([0, 9000000000000], [525000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([0, 0], [1350000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-555000000000], [8655000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1080000000000,
      9000000000000], [9180000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-2430000000000], [9180000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-1350000000000], [1875000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6075000000000], [7950000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6600000000000,
      0], [7950000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-525000000000,
      9000000000000], [525000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 4, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_6 : ExcludedOn (model46.B 6 ++ [step46.q]) 9000000000000 (model46.caps 6)
    (model46.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1530000000000, 9000000000000], [900000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2250000000000], [5220000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1350000000000, 9000000000000],
      [7650000000000, -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([180000000000],
      [2250000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-900000000000, 9000000000000],
      [2430000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-5220000000000, 9000000000000],
      [7470000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7650000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2250000000000], [2430000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_7 : ExcludedOn (model46.B 7 ++ [step46.q]) 9000000000000 (model46.caps 7)
    (model46.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_8 : ExcludedOn (model46.B 8 ++ [step46.q]) 9000000000000 (model46.caps 8)
    (model46.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_9 : ExcludedOn (model46.B 9 ++ [step46.q]) 9000000000000 (model46.caps 9)
    (model46.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked46 : StepValid model46 9000000000000 step46 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded46_1
    · exact excluded46_2
    · exact excluded46_3
    · exact excluded46_4
    · exact excluded46_5
    · exact excluded46_6
    · exact excluded46_7
    · exact excluded46_8
    · exact excluded46_9
theorem next46 : model46.insert step46 = model47 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded47_0 : ExcludedOn (model47.B 0 ++ [step47.q]) 9000000000000 (model47.caps 0)
    (model47.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_1 : ExcludedOn (model47.B 1 ++ [step47.q]) 9000000000000 (model47.caps 1)
    (model47.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_2 : ExcludedOn (model47.B 2 ++ [step47.q]) 9000000000000 (model47.caps 2)
    (model47.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_3 : ExcludedOn (model47.B 3 ++ [step47.q]) 9000000000000 (model47.caps 3)
    (model47.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4575000000000], [375000000000]) (some (3, 5, 2))
      (some (5, 5, 2)) (.next ([3225000000000, -9000000000000], [375000000000]) (some (5, 5, 2))
      (some (5, 5, 2)) (.next ([3450000000000], [450000000000]) (some (5, 5, 2)) (some (5, 5, 2))
      (.next ([4950000000000], [825000000000]) (some (5, 5, 2)) (some (5, 5, 2)) (.next
      ([3150000000000, -9000000000000], [675000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1,
      2)) (.next ([1350000000000, 9000000000000], [1350000000000, 9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([4500000000000], [4725000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([2025000000000, 9000000000000], [2475000000000, -9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([1350000000000, 9000000000000], [4050000000000, -9000000000000])
      (some (5, 1, 2)) (some (5, 1, 3)) (.next ([975000000000, 9000000000000], [4950000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([675000000000], [3825000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([0], [1350000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([-375000000000], [4950000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-375000000000], [3600000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-450000000000], [3900000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-825000000000],
      [5775000000000]) (some (5, 1, 3)) (some (5, 2, 3)) (.next ([-675000000000, -9000000000000],
      [3825000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-4725000000000],
      [9225000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2475000000000, 9000000000000],
      [4500000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-4050000000000, 9000000000000],
      [5400000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-4950000000000, 0],
      [5925000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-3825000000000],
      [4500000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 2,
      3)) (some (5, 2, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_4 : ExcludedOn (model47.B 4 ++ [step47.q]) 9000000000000 (model47.caps 4)
    (model47.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_5 : ExcludedOn (model47.B 5 ++ [step47.q]) 9000000000000 (model47.caps 5)
    (model47.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_6 : ExcludedOn (model47.B 6 ++ [step47.q]) 9000000000000 (model47.caps 6)
    (model47.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_7 : ExcludedOn (model47.B 7 ++ [step47.q]) 9000000000000 (model47.caps 7)
    (model47.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_9 : ExcludedOn (model47.B 9 ++ [step47.q]) 9000000000000 (model47.caps 9)
    (model47.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked47 : StepValid model47 9000000000000 step47 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded47_0
    · exact excluded47_1
    · exact excluded47_2
    · exact excluded47_3
    · exact excluded47_4
    · exact excluded47_5
    · exact excluded47_6
    · exact excluded47_7
    · exact (hj rfl).elim
    · exact excluded47_9
theorem next47 : model47.insert step47 = model48 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext150000160000
end ConwaySoifer.Simplified.Certificates
