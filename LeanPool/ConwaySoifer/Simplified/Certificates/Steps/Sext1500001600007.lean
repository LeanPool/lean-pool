/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext150000160000
import Mathlib.Tactic.FinCases

/-!
# Sext 150000 160000 7

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
def fan56Owner3Part0 : FanWitness := (.next ([-75000000000], [4125000000000]) (some (7, 7, 5)) (some
    (7, 7, 5)) (.next ([-375000000000], [4950000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next
    ([-450000000000], [5250000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-375000000000],
    [4350000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-375000000000], [4125000000000])
    (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-375000000000], [3600000000000, -9000000000000])
    (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-975000000000], [8550000000000]) (some (7, 7, 5))
    (some (7, 7, 5)) (.next ([-450000000000], [3900000000000, -9000000000000]) (some (7, 4, 5))
    (some (7, 4, 5)) (.next ([-675000000000], [5250000000000]) (some (7, 4, 5)) (some (7, 4, 5))
    (.next ([-600000000000], [4425000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([-600000000000], [4200000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-675000000000],
    [3900000000000, -9000000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-900000000000],
    [4425000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-900000000000, -9000000000000],
    [4425000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-75000000000], [300000000000]) (some
    (7, 4, 5)) (some (7, 4, 5)) (.next ([-1350000000000, -9000000000000], [2700000000000,
    18000000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-5850000000000, 0], [10350000000000,
    9000000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-4500000000000, 9000000000000],
    [7650000000000, -9000000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-3075000000000,
    9000000000000], [4875000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-5850000000000],
    [9000000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-4950000000000, 0], [5925000000000,
    9000000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-5250000000000, 0], [6150000000000,
    9000000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-5250000000000, 0], [5925000000000,
    9000000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-4425000000000], [4875000000000])
    (some (7, 4, 5)) (some (7, 4, 5)) (.terminal (some (7, 4, 5)) (some (7, 4, 5)) (some (7, 4,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan56Owner3Part1 : FanWitness := (.next ([4575000000000], [375000000000]) (some (6, 7, 4)) (some
    (6, 7, 4)) (.next ([4800000000000], [450000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
    ([3975000000000], [375000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3750000000000],
    [375000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3225000000000, -9000000000000],
    [375000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([7575000000000], [975000000000]) (some
    (6, 7, 4)) (some (6, 7, 4)) (.next ([3450000000000, -9000000000000], [450000000000]) (some (6,
    7, 4)) (some (6, 7, 4)) (.next ([4575000000000], [675000000000]) (some (6, 7, 4)) (some (6, 7,
    4)) (.next ([3825000000000], [600000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
    ([3600000000000], [600000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3225000000000,
    -9000000000000], [675000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3525000000000],
    [900000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3525000000000, -9000000000000],
    [900000000000, 9000000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([225000000000],
    [75000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1350000000000, 9000000000000],
    [1350000000000, 9000000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([4500000000000,
    9000000000000], [5850000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3150000000000],
    [4500000000000, -9000000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1800000000000,
    9000000000000], [3075000000000, -9000000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
    ([3150000000000], [5850000000000]) (some (6, 7, 4)) (some (6, 7, 5)) (.next ([975000000000,
    9000000000000], [4950000000000]) (some (6, 7, 5)) (some (7, 7, 5)) (.next ([900000000000,
    9000000000000], [5250000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([675000000000,
    9000000000000], [5250000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([450000000000],
    [4425000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([0], [1350000000000, 9000000000000])
    (some (7, 7, 5)) (some (7, 7, 5)) fan56Owner3Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan57Owner3Part0 : FanWitness := (.next ([900000000000, 9000000000000], [5250000000000]) (some
    (7, 2, 5)) (some (7, 2, 5)) (.next ([675000000000, 9000000000000], [5250000000000]) (some (7, 2,
    5)) (some (7, 2, 5)) (.next ([450000000000], [4425000000000]) (some (7, 2, 5)) (some (7, 2, 5))
    (.next ([0], [1350000000000, 9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([-75000000000], [4125000000000]) (some (7, 2, 5)) (some (7, 3, 5)) (.next ([-375000000000],
    [4950000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-450000000000], [5250000000000])
    (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-375000000000], [4350000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-375000000000], [4125000000000]) (some (7, 3, 5)) (some (7, 3, 5))
    (.next ([-375000000000], [3600000000000, -9000000000000]) (some (7, 3, 5)) (some (7, 4, 5))
    (.next ([-450000000000], [3900000000000, -9000000000000]) (some (7, 4, 5)) (some (7, 4, 5))
    (.next ([-675000000000], [5250000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([-675000000000], [3900000000000, -9000000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([-900000000000, -9000000000000], [4425000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([-75000000000], [300000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-2325000000000],
    [7200000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-1425000000000, 9000000000000],
    [2775000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-3225000000000], [5250000000000])
    (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-3150000000000], [4950000000000]) (some (2, 4, 5))
    (some (2, 4, 5)) (.next ([-3450000000000], [5250000000000]) (some (2, 4, 5)) (some (2, 4, 5))
    (.next ([-4950000000000, 0], [5925000000000, 9000000000000]) (some (2, 4, 5)) (some (2, 4, 5))
    (.next ([-5250000000000, 0], [6150000000000, 9000000000000]) (some (2, 4, 5)) (some (2, 4, 5))
    (.next ([-5250000000000, 0], [5925000000000, 9000000000000]) (some (2, 4, 5)) (some (2, 4, 5))
    (.next ([-4425000000000], [4875000000000]) (some (2, 4, 5)) (some (2, 4, 5)) (.terminal (some
    (2, 4, 5)) (some (2, 4, 5)) (some (2, 4, 5)))))))))))))))))))))))))))

theorem excluded56_0 : ExcludedOn (model56.B 0 ++ [step56.q]) 9000000000000 (model56.caps 0)
    (model56.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_1 : ExcludedOn (model56.B 1 ++ [step56.q]) 9000000000000 (model56.caps 1)
    (model56.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_2 : ExcludedOn (model56.B 2 ++ [step56.q]) 9000000000000 (model56.caps 2)
    (model56.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_3 : ExcludedOn (model56.B 3 ++ [step56.q]) 9000000000000 (model56.caps 3)
    (model56.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4050000000000], [75000000000]) (some (5, 7, 4))
      (some (6, 7, 4)) fan56Owner3Part1)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded56_4 : ExcludedOn (model56.B 4 ++ [step56.q]) 9000000000000 (model56.caps 4)
    (model56.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1800000000000, -9000000000000], [1350000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([3450000000000], [6000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1650000000000, 9000000000000], [4650000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1350000000000, 9000000000000],
      [5325000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([975000000000], [5025000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([300000000000], [6000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([0], [5325000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-1350000000000, -9000000000000], [3150000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-6000000000000], [9450000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-4650000000000,
      9000000000000], [6300000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next ([-5325000000000],
      [6675000000000, 9000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-5025000000000],
      [6000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-6000000000000], [6300000000000])
      (some (4, 1, 4)) (some (4, 2, 4)) (.terminal (some (4, 2, 4)) (some (0, 2, 4)) (some (4, 2,
      4))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded56_5 : ExcludedOn (model56.B 5 ++ [step56.q]) 9000000000000 (model56.caps 5)
    (model56.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_6 : ExcludedOn (model56.B 6 ++ [step56.q]) 9000000000000 (model56.caps 6)
    (model56.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_7 : ExcludedOn (model56.B 7 ++ [step56.q]) 9000000000000 (model56.caps 7)
    (model56.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_9 : ExcludedOn (model56.B 9 ++ [step56.q]) 9000000000000 (model56.caps 9)
    (model56.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked56 : StepValid model56 9000000000000 step56 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded56_0
    · exact excluded56_1
    · exact excluded56_2
    · exact excluded56_3
    · exact excluded56_4
    · exact excluded56_5
    · exact excluded56_6
    · exact excluded56_7
    · exact (hj rfl).elim
    · exact excluded56_9
theorem next56 : model56.insert step56 = model57 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded57_0 : ExcludedOn (model57.B 0 ++ [step57.q]) 9000000000000 (model57.caps 0)
    (model57.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_1 : ExcludedOn (model57.B 1 ++ [step57.q]) 9000000000000 (model57.caps 1)
    (model57.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_2 : ExcludedOn (model57.B 2 ++ [step57.q]) 9000000000000 (model57.caps 2)
    (model57.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_3 : ExcludedOn (model57.B 3 ++ [step57.q]) 9000000000000 (model57.caps 3)
    (model57.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4050000000000], [75000000000]) (some (5, 2, 4))
      (some (7, 2, 4)) (.next ([4575000000000], [375000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      (.next ([4800000000000], [450000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([3975000000000], [375000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([3750000000000],
      [375000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([3225000000000, -9000000000000],
      [375000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([3450000000000, -9000000000000],
      [450000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([4575000000000], [675000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([3225000000000, -9000000000000], [675000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([3525000000000, -9000000000000], [900000000000,
      9000000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([225000000000], [75000000000]) (some
      (7, 2, 4)) (some (7, 2, 4)) (.next ([4875000000000], [2325000000000]) (some (7, 2, 4)) (some
      (7, 2, 4)) (.next ([1350000000000, 9000000000000], [1425000000000, -9000000000000]) (some (7,
      2, 4)) (some (7, 2, 4)) (.next ([2025000000000], [3225000000000]) (some (7, 2, 4)) (some (7,
      2, 4)) (.next ([1800000000000], [3150000000000]) (some (7, 2, 4)) (some (7, 2, 5)) (.next
      ([1800000000000], [3450000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([975000000000,
      9000000000000], [4950000000000]) (some (7, 2, 5)) (some (7, 2, 5))
      fan57Owner3Part0)))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded57_4 : ExcludedOn (model57.B 4 ++ [step57.q]) 9000000000000 (model57.caps 4)
    (model57.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_5 : ExcludedOn (model57.B 5 ++ [step57.q]) 9000000000000 (model57.caps 5)
    (model57.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_6 : ExcludedOn (model57.B 6 ++ [step57.q]) 9000000000000 (model57.caps 6)
    (model57.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_7 : ExcludedOn (model57.B 7 ++ [step57.q]) 9000000000000 (model57.caps 7)
    (model57.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_9 : ExcludedOn (model57.B 9 ++ [step57.q]) 9000000000000 (model57.caps 9)
    (model57.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked57 : StepValid model57 9000000000000 step57 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded57_0
    · exact excluded57_1
    · exact excluded57_2
    · exact excluded57_3
    · exact excluded57_4
    · exact excluded57_5
    · exact excluded57_6
    · exact excluded57_7
    · exact (hj rfl).elim
    · exact excluded57_9
theorem next57 : model57.insert step57 = model58 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded58_0 : ExcludedOn (model58.B 0 ++ [step58.q]) 9000000000000 (model58.caps 0)
    (model58.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_1 : ExcludedOn (model58.B 1 ++ [step58.q]) 9000000000000 (model58.caps 1)
    (model58.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_2 : ExcludedOn (model58.B 2 ++ [step58.q]) 9000000000000 (model58.caps 2)
    (model58.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_4 : ExcludedOn (model58.B 4 ++ [step58.q]) 9000000000000 (model58.caps 4)
    (model58.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [2925000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([3075000000000], [5325000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([1650000000000, 9000000000000], [4650000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1350000000000, 9000000000000], [5325000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([975000000000], [5025000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([300000000000], [6000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [5325000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-2925000000000], [6300000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5325000000000], [8400000000000]) (some (0, 1, 2))
      (some (0, 1, 4)) (.next ([-4650000000000, 9000000000000], [6300000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5325000000000], [6675000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5025000000000], [6000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-6000000000000], [6300000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded58_5 : ExcludedOn (model58.B 5 ++ [step58.q]) 9000000000000 (model58.caps 5)
    (model58.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_6 : ExcludedOn (model58.B 6 ++ [step58.q]) 9000000000000 (model58.caps 6)
    (model58.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_7 : ExcludedOn (model58.B 7 ++ [step58.q]) 9000000000000 (model58.caps 7)
    (model58.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_8 : ExcludedOn (model58.B 8 ++ [step58.q]) 9000000000000 (model58.caps 8)
    (model58.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5925000000000], [3075000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([3150000000000], [2775000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([375000000000], [5850000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([75000000000], [3075000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [5850000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-3075000000000], [9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2775000000000], [5925000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-5850000000000], [6225000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3075000000000], [3150000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded58_9 : ExcludedOn (model58.B 9 ++ [step58.q]) 9000000000000 (model58.caps 9)
    (model58.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked58 : StepValid model58 9000000000000 step58 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded58_0
    · exact excluded58_1
    · exact excluded58_2
    · exact (hj rfl).elim
    · exact excluded58_4
    · exact excluded58_5
    · exact excluded58_6
    · exact excluded58_7
    · exact excluded58_8
    · exact excluded58_9
theorem next58 : model58.insert step58 = model59 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded59_0 : ExcludedOn (model59.B 0 ++ [step59.q]) 9000000000000 (model59.caps 0)
    (model59.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_1 : ExcludedOn (model59.B 1 ++ [step59.q]) 9000000000000 (model59.caps 1)
    (model59.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_2 : ExcludedOn (model59.B 2 ++ [step59.q]) 9000000000000 (model59.caps 2)
    (model59.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_4 : ExcludedOn (model59.B 4 ++ [step59.q]) 9000000000000 (model59.caps 4)
    (model59.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000], [1125000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([2175000000000], [1350000000000, -9000000000000]) (some (4, 1,
      2)) (some (4, 1, 2)) (.next ([4875000000000], [3150000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([2175000000000], [2700000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([1650000000000, 9000000000000], [4650000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([1350000000000, 9000000000000], [5325000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([975000000000], [5025000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([300000000000], [6000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [5325000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1125000000000], [4125000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1350000000000, 9000000000000], [3525000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 4)) (.next ([-3150000000000], [8025000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2700000000000], [4875000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-4650000000000, 9000000000000], [6300000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5325000000000], [6675000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5025000000000], [6000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-6000000000000], [6300000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded59_5 : ExcludedOn (model59.B 5 ++ [step59.q]) 9000000000000 (model59.caps 5)
    (model59.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_6 : ExcludedOn (model59.B 6 ++ [step59.q]) 9000000000000 (model59.caps 6)
    (model59.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_7 : ExcludedOn (model59.B 7 ++ [step59.q]) 9000000000000 (model59.caps 7)
    (model59.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_8 : ExcludedOn (model59.B 8 ++ [step59.q]) 9000000000000 (model59.caps 8)
    (model59.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_9 : ExcludedOn (model59.B 9 ++ [step59.q]) 9000000000000 (model59.caps 9)
    (model59.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked59 : StepValid model59 9000000000000 step59 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded59_0
    · exact excluded59_1
    · exact excluded59_2
    · exact (hj rfl).elim
    · exact excluded59_4
    · exact excluded59_5
    · exact excluded59_6
    · exact excluded59_7
    · exact excluded59_8
    · exact excluded59_9
theorem next59 : model59.insert step59 = model60 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded60_0 : ExcludedOn (model60.B 0 ++ [step60.q]) 9000000000000 (model60.caps 0)
    (model60.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_1 : ExcludedOn (model60.B 1 ++ [step60.q]) 9000000000000 (model60.caps 1)
    (model60.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_3 : ExcludedOn (model60.B 3 ++ [step60.q]) 9000000000000 (model60.caps 3)
    (model60.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [375000000000]) (some (3, 0, 2))
      (some (4, 0, 2)) (.next ([5475000000000, 9000000000000], [825000000000, -9000000000000]) (some
      (4, 0, 2)) (some (4, 0, 5)) (.next ([4425000000000], [1050000000000]) (some (4, 0, 5)) (some
      (4, 0, 5)) (.next ([4125000000000], [2175000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
      ([2250000000000], [1425000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([4050000000000],
      [5925000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1800000000000, 9000000000000],
      [3075000000000, -9000000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1875000000000],
      [6300000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1350000000000, 9000000000000],
      [5925000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([375000000000], [1800000000000])
      (some (4, 0, 5)) (some (4, 0, 5)) (.next ([450000000000], [4425000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([0], [5925000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([-375000000000], [4875000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-825000000000,
      9000000000000], [6300000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1050000000000],
      [5475000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2175000000000], [6300000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1425000000000], [3675000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([-5925000000000], [9975000000000]) (some (0, 1, 5)) (some (0, 2, 5))
      (.next ([-3075000000000, 9000000000000], [4875000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-6300000000000], [8175000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-5925000000000, 0], [7275000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-1800000000000], [2175000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-4425000000000], [4875000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 3)) (some (0, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded60_4 : ExcludedOn (model60.B 4 ++ [step60.q]) 9000000000000 (model60.caps 4)
    (model60.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_5 : ExcludedOn (model60.B 5 ++ [step60.q]) 9000000000000 (model60.caps 5)
    (model60.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_6 : ExcludedOn (model60.B 6 ++ [step60.q]) 9000000000000 (model60.caps 6)
    (model60.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_7 : ExcludedOn (model60.B 7 ++ [step60.q]) 9000000000000 (model60.caps 7)
    (model60.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_8 : ExcludedOn (model60.B 8 ++ [step60.q]) 9000000000000 (model60.caps 8)
    (model60.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_9 : ExcludedOn (model60.B 9 ++ [step60.q]) 9000000000000 (model60.caps 9)
    (model60.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked60 : StepValid model60 9000000000000 step60 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded60_0
    · exact excluded60_1
    · exact (hj rfl).elim
    · exact excluded60_3
    · exact excluded60_4
    · exact excluded60_5
    · exact excluded60_6
    · exact excluded60_7
    · exact excluded60_8
    · exact excluded60_9
theorem next60 : model60.insert step60 = model61 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded61_0 : ExcludedOn (model61.B 0 ++ [step61.q]) 9000000000000 (model61.caps 0)
    (model61.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_1 : ExcludedOn (model61.B 1 ++ [step61.q]) 9000000000000 (model61.caps 1)
    (model61.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_2 : ExcludedOn (model61.B 2 ++ [step61.q]) 9000000000000 (model61.caps 2)
    (model61.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [900000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([3075000000000], [2325000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([5100000000000, 9000000000000], [4350000000000, -9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([2025000000000, 9000000000000], [2025000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3750000000000], [5700000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1350000000000, 9000000000000], [4950000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([675000000000], [3375000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([0], [4950000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-900000000000],
      [4275000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-2325000000000], [5400000000000])
      (some (0, 4, 3)) (some (4, 4, 3)) (.next ([-4350000000000, 9000000000000], [9450000000000, 0])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2025000000000, 9000000000000], [4050000000000, 0])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-5700000000000], [9450000000000]) (some (4, 1, 3))
      (some (4, 2, 3)) (.next ([-4950000000000, 0], [6300000000000, 9000000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-3375000000000], [4050000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.terminal (some (4, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded61_4 : ExcludedOn (model61.B 4 ++ [step61.q]) 9000000000000 (model61.caps 4)
    (model61.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8550000000000], [75000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5250000000000], [1950000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([2550000000000], [1050000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([5250000000000], [3300000000000]) (some (3, 1, 2)) (some (3, 1, 4)) (.next
      ([1650000000000, 9000000000000], [4650000000000, -9000000000000]) (some (3, 1, 4)) (some (3,
      1, 4)) (.next ([1350000000000, 9000000000000], [5325000000000]) (some (3, 1, 4)) (some (3, 1,
      4)) (.next ([975000000000], [5025000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([300000000000], [6000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [5325000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-75000000000], [8625000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1950000000000, 9000000000000], [7200000000000,
      -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1050000000000], [3600000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3300000000000], [8550000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-4650000000000, 9000000000000], [6300000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5325000000000], [6675000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5025000000000], [6000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-6000000000000], [6300000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded61_5 : ExcludedOn (model61.B 5 ++ [step61.q]) 9000000000000 (model61.caps 5)
    (model61.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_6 : ExcludedOn (model61.B 6 ++ [step61.q]) 9000000000000 (model61.caps 6)
    (model61.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_7 : ExcludedOn (model61.B 7 ++ [step61.q]) 9000000000000 (model61.caps 7)
    (model61.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_8 : ExcludedOn (model61.B 8 ++ [step61.q]) 9000000000000 (model61.caps 8)
    (model61.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_9 : ExcludedOn (model61.B 9 ++ [step61.q]) 9000000000000 (model61.caps 9)
    (model61.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked61 : StepValid model61 9000000000000 step61 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded61_0
    · exact excluded61_1
    · exact excluded61_2
    · exact (hj rfl).elim
    · exact excluded61_4
    · exact excluded61_5
    · exact excluded61_6
    · exact excluded61_7
    · exact excluded61_8
    · exact excluded61_9
theorem next61 : model61.insert step61 = model62 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded62_0 : ExcludedOn (model62.B 0 ++ [step62.q]) 9000000000000 (model62.caps 0)
    (model62.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_1 : ExcludedOn (model62.B 1 ++ [step62.q]) 9000000000000 (model62.caps 1)
    (model62.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5925000000000, 9000000000000], [3075000000000,
      -9000000000000]) (some (4, 0, 1)) (some (4, 0, 2)) (.next ([4575000000000], [4425000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([3225000000000, -9000000000000],
      [4425000000000, 0]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1500000000000], [2775000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1500000000000], [4125000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1200000000000], [7500000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([150000000000, -9000000000000], [5475000000000, 9000000000000]) (some
      (4, 0, 2)) (some (4, 0, 2)) (.next ([0], [1350000000000, 9000000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([-3075000000000, 9000000000000], [9000000000000]) (some (4, 0, 2))
      (some (4, 0, 3)) (.next ([-4425000000000], [9000000000000]) (some (4, 0, 3)) (some (4, 0, 3))
      (.next ([-1350000000000, -9000000000000], [2700000000000, 18000000000000]) (some (4, 0, 3))
      (some (4, 0, 3)) (.next ([-4425000000000, 0], [7650000000000, -9000000000000]) (some (4, 0,
      3)) (some (4, 0, 3)) (.next ([-2775000000000, 9000000000000], [4275000000000, -9000000000000])
      (some (4, 0, 3)) (some (4, 0, 4)) (.next ([-4125000000000], [5625000000000]) (some (4, 0, 4))
      (some (4, 1, 4)) (.next ([-7500000000000], [8700000000000]) (some (4, 1, 4)) (some (4, 1, 4))
      (.next ([-5475000000000, -9000000000000], [5625000000000, 0]) (some (0, 1, 4)) (some (0, 1,
      4)) (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded62_3 : ExcludedOn (model62.B 3 ++ [step62.q]) 9000000000000 (model62.caps 3)
    (model62.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_4 : ExcludedOn (model62.B 4 ++ [step62.q]) 9000000000000 (model62.caps 4)
    (model62.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_5 : ExcludedOn (model62.B 5 ++ [step62.q]) 9000000000000 (model62.caps 5)
    (model62.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_6 : ExcludedOn (model62.B 6 ++ [step62.q]) 9000000000000 (model62.caps 6)
    (model62.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_7 : ExcludedOn (model62.B 7 ++ [step62.q]) 9000000000000 (model62.caps 7)
    (model62.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_8 : ExcludedOn (model62.B 8 ++ [step62.q]) 9000000000000 (model62.caps 8)
    (model62.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_9 : ExcludedOn (model62.B 9 ++ [step62.q]) 9000000000000 (model62.caps 9)
    (model62.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked62 : StepValid model62 9000000000000 step62 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded62_0
    · exact excluded62_1
    · exact (hj rfl).elim
    · exact excluded62_3
    · exact excluded62_4
    · exact excluded62_5
    · exact excluded62_6
    · exact excluded62_7
    · exact excluded62_8
    · exact excluded62_9
theorem next62 : model62.insert step62 = model63 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded63_0 : ExcludedOn (model63.B 0 ++ [step63.q]) 9000000000000 (model63.caps 0)
    (model63.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_1 : ExcludedOn (model63.B 1 ++ [step63.q]) 9000000000000 (model63.caps 1)
    (model63.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5550000000000], [750000000000]) (some (4, 0, 1))
      (some (4, 0, 2)) (.next ([4200000000000, -9000000000000], [750000000000, 0]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([4875000000000], [4800000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([1350000000000, 9000000000000], [1350000000000, 9000000000000]) (some (4, 0, 2)) (some
      (4, 0, 2)) (.next ([1500000000000], [2775000000000, -9000000000000]) (some (4, 0, 2)) (some
      (4, 0, 2)) (.next ([1500000000000], [4125000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([600000000000, 9000000000000], [6300000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([150000000000, -9000000000000], [5475000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 0,
      2)) (.next ([0], [1350000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-750000000000], [6300000000000]) (some (4, 0, 2)) (some (4, 0, 3)) (.next ([-750000000000,
      0], [4950000000000, -9000000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next
      ([-4800000000000], [9675000000000]) (some (4, 0, 3)) none (.next ([-1350000000000,
      -9000000000000], [2700000000000, 18000000000000]) none none (.next ([-2775000000000,
      9000000000000], [4275000000000, -9000000000000]) none none (.next ([-4125000000000],
      [5625000000000]) (some (0, 0, 4)) (some (0, 1, 4)) (.next ([-6300000000000], [6900000000000,
      9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-5475000000000, -9000000000000],
      [5625000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1, 4)) (some (0, 1,
      4)) (some (0, 1, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded63_3 : ExcludedOn (model63.B 3 ++ [step63.q]) 9000000000000 (model63.caps 3)
    (model63.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_4 : ExcludedOn (model63.B 4 ++ [step63.q]) 9000000000000 (model63.caps 4)
    (model63.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_5 : ExcludedOn (model63.B 5 ++ [step63.q]) 9000000000000 (model63.caps 5)
    (model63.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_6 : ExcludedOn (model63.B 6 ++ [step63.q]) 9000000000000 (model63.caps 6)
    (model63.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_7 : ExcludedOn (model63.B 7 ++ [step63.q]) 9000000000000 (model63.caps 7)
    (model63.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6300000000000], [2100000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([6300000000000], [3450000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([2700000000000], [3450000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([1350000000000, 9000000000000], [2250000000000, -9000000000000]) (some (0, 3, 2))
      (some (3, 3, 2)) (.next ([0], [3600000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([-2100000000000, 9000000000000], [8400000000000, -9000000000000]) (some (3, 3, 2)) (some (3,
      3, 2)) (.next ([-3450000000000], [9750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3450000000000], [6150000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2250000000000,
      9000000000000], [3600000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2))
      (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded63_8 : ExcludedOn (model63.B 8 ++ [step63.q]) 9000000000000 (model63.caps 8)
    (model63.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_9 : ExcludedOn (model63.B 9 ++ [step63.q]) 9000000000000 (model63.caps 9)
    (model63.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked63 : StepValid model63 9000000000000 step63 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded63_0
    · exact excluded63_1
    · exact (hj rfl).elim
    · exact excluded63_3
    · exact excluded63_4
    · exact excluded63_5
    · exact excluded63_6
    · exact excluded63_7
    · exact excluded63_8
    · exact excluded63_9
theorem next63 : model63.insert step63 = model64 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext150000160000
end ConwaySoifer.Simplified.Certificates
