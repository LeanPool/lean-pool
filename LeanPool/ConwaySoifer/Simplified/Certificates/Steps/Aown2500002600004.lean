/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown250000260000
import Mathlib.Tactic.FinCases

/-!
# Aown 250000 260000 4

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
namespace Aown250000260000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner2Part0 : FanWitness := (.next ([1500000000000], [3750000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([1875000000000, 0], [4875000000000, -9000000000000]) (some (6, 1, 4))
    (some (6, 1, 5)) (.next ([375000000000, 0], [1125000000000, -9000000000000]) (some (6, 1, 5))
    (some (6, 1, 5)) (.next ([75000000000], [1050000000000]) (some (6, 1, 5)) (some (6, 1, 5))
    (.next ([0, 0], [4125000000000, 9000000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([0,
    -9000000000000], [375000000000, 0]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-2325000000000],
    [9450000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-2250000000000, -9000000000000],
    [9000000000000, 0]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-2250000000000, -9000000000000],
    [8325000000000, 9000000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-3075000000000],
    [9825000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-2625000000000, -9000000000000],
    [7875000000000, 9000000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-3450000000000, 0],
    [10200000000000, -9000000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-3450000000000],
    [9525000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-3825000000000], [9075000000000])
    (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-300000000000], [675000000000]) (some (6, 1, 5))
    (some (6, 1, 5)) (.next ([-375000000000], [750000000000]) (some (6, 1, 5)) (some (6, 1, 5))
    (.next ([-450000000000], [825000000000]) (some (6, 1, 5)) (some (6, 2, 5)) (.next
    ([-4125000000000], [7125000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-4500000000000],
    [6750000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-4200000000000], [6075000000000])
    (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-3750000000000], [5250000000000]) (some (6, 2, 5))
    (some (6, 2, 5)) (.next ([-4875000000000, 9000000000000], [6750000000000, -9000000000000]) (some
    (6, 2, 5)) (some (6, 2, 5)) (.next ([-1125000000000, 9000000000000], [1500000000000,
    -9000000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-1050000000000], [1125000000000])
    (some (6, 2, 5)) (some (6, 2, 5)) (.terminal (some (6, 2, 5)) (some (6, 2, 0)) (some (6, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part0 : FanWitness := (.next ([-2625000000000], [8625000000000]) (some (0, 4, 9))
    (some (0, 4, 9)) (.next ([-1875000000000], [6000000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    (.next ([-375000000000], [1125000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next
    ([-2700000000000], [6075000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-375000000000],
    [750000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([-3375000000000], [6375000000000])
    (some (0, 4, 9)) (some (1, 4, 9)) (.next ([-375000000000], [675000000000]) (some (1, 4, 9))
    (some (1, 4, 9)) (.next ([-3000000000000], [4875000000000]) (some (1, 4, 9)) (some (1, 4, 9))
    (.next ([-4200000000000], [6375000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next
    ([-750000000000], [1125000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-4575000000000],
    [6750000000000]) (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-3375000000000], [4875000000000])
    (some (1, 4, 9)) (some (1, 4, 9)) (.next ([-6000000000000], [8625000000000]) (some (1, 4, 9))
    (some (1, 4, 9)) (.next ([-1875000000000], [2625000000000]) (some (1, 4, 9)) (some (1, 4, 9))
    (.next ([-5325000000000], [7125000000000]) (some (1, 4, 9)) (some (1, 5, 9)) (.next
    ([-4500000000000], [6000000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4875000000000],
    [6375000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5700000000000], [7125000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-3450000000000], [4200000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-3750000000000], [4500000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-6000000000000], [6750000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-6075000000000], [6750000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-3750000000000],
    [4125000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4125000000000], [4500000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.terminal (some (1, 5, 9)) (some (1, 5, 9)) (some (1, 5,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part1 : FanWitness := (.next ([375000000000], [750000000000]) (some (9, 3, 5)) (some
    (9, 3, 5)) (.next ([2175000000000], [4575000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([1500000000000], [3375000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([2625000000000],
    [6000000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([750000000000], [1875000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1800000000000], [5325000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([1500000000000], [4500000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([1500000000000], [4875000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([1425000000000], [5700000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([750000000000],
    [3450000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([750000000000], [3750000000000])
    (some (9, 3, 5)) (some (9, 3, 6)) (.next ([750000000000], [6000000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([675000000000], [6075000000000]) (some (9, 3, 6)) (some (9, 3, 6))
    (.next ([375000000000], [3750000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([375000000000], [4125000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([0],
    [1500000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-375000000000], [6000000000000])
    (some (9, 3, 6)) (some (9, 4, 6)) (.next ([-375000000000], [2625000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-1125000000000], [7125000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([-1125000000000], [6750000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next
    ([-1125000000000], [6375000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1500000000000],
    [7875000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1875000000000], [8250000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1500000000000], [6375000000000]) (some (0, 4, 6))
    (some (0, 4, 9)) fan33Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner2Part0 : FanWitness := (.next ([375000000000, 0], [1125000000000, -9000000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([75000000000], [1050000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([0, 0], [4125000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([0, -9000000000000], [1500000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0,
    -9000000000000], [375000000000, 0]) (some (0, 1, 5)) (some (6, 1, 5)) (.next ([-2250000000000,
    -9000000000000], [9000000000000, 0]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-1500000000000],
    [5625000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-2250000000000, -9000000000000],
    [8325000000000, 9000000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-2625000000000],
    [8250000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-2625000000000, -9000000000000],
    [7875000000000, 9000000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-375000000000,
    -9000000000000], [1125000000000, 0]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-3750000000000,
    0], [9000000000000, -9000000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-300000000000],
    [675000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-3750000000000], [8325000000000])
    (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-375000000000], [750000000000]) (some (6, 1, 5))
    (some (6, 1, 5)) (.next ([-4125000000000], [7875000000000]) (some (6, 1, 5)) (some (6, 2, 5))
    (.next ([-450000000000], [825000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next
    ([-4125000000000], [7125000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-4500000000000],
    [6750000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-4200000000000], [6075000000000])
    (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-3750000000000], [5250000000000]) (some (6, 2, 5))
    (some (6, 2, 5)) (.next ([-4875000000000, 9000000000000], [6750000000000, -9000000000000]) (some
    (6, 2, 5)) (some (6, 2, 5)) (.next ([-1125000000000, 9000000000000], [1500000000000,
    -9000000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-1050000000000], [1125000000000])
    (some (6, 2, 5)) (some (6, 2, 5)) (.terminal (some (6, 2, 5)) (some (6, 2, 0)) (some (6, 2,
    5)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([375000000000, -9000000000000], [0,
      9000000000000]) (some (0, 6, 2)) (some (6, 6, 2)) (.next ([7125000000000], [2325000000000])
      (some (6, 6, 2)) (some (6, 6, 2)) (.next ([6750000000000, -9000000000000], [2250000000000,
      9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([6075000000000, 0], [2250000000000,
      9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([6750000000000], [3075000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([5250000000000, 0], [2625000000000, 9000000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([6750000000000, -9000000000000], [3450000000000, 0])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([6075000000000], [3450000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) (.next ([5250000000000], [3825000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([375000000000], [300000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([375000000000], [375000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([375000000000],
      [450000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([3000000000000], [4125000000000])
      (some (6, 1, 3)) (some (6, 1, 4)) (.next ([2250000000000], [4500000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([1875000000000], [4200000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      fan32Owner2Part0))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked32 : StepValid model32 9000000000000 step32 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded32_0
    · exact excluded32_1
    · exact excluded32_2
    · exact (hj rfl).elim
    · exact excluded32_4
    · exact excluded32_5
    · exact excluded32_6
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [375000000000]) (some (9, 1, 5))
      (some (9, 2, 5)) (.next ([2250000000000], [375000000000]) (some (9, 2, 5)) (some (9, 2, 5))
      (.next ([6000000000000], [1125000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
      ([5625000000000], [1125000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([5250000000000],
      [1125000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([6375000000000], [1500000000000])
      (some (9, 2, 5)) (some (9, 2, 5)) (.next ([6375000000000], [1875000000000]) (some (9, 2, 5))
      (some (9, 2, 5)) (.next ([4875000000000], [1500000000000]) (some (9, 2, 5)) (some (9, 2, 5))
      (.next ([6000000000000], [2625000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
      ([4125000000000], [1875000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([750000000000],
      [375000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([3375000000000], [2700000000000])
      (some (9, 2, 5)) (some (9, 2, 5)) (.next ([375000000000], [375000000000]) (some (9, 2, 5))
      (some (9, 2, 5)) (.next ([3000000000000], [3375000000000]) (some (9, 2, 5)) (some (9, 3, 5))
      (.next ([300000000000], [375000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
      ([1875000000000], [3000000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([2175000000000],
      [4200000000000]) (some (9, 3, 5)) (some (9, 3, 5)) fan33Owner0Part1)))))))))))))))))) (den :=
      9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1500000000000, -9000000000000], [0,
      9000000000000]) (some (0, 6, 2)) (some (0, 6, 2)) (.next ([375000000000, -9000000000000], [0,
      9000000000000]) (some (0, 6, 2)) (some (0, 6, 2)) (.next ([6750000000000, -9000000000000],
      [2250000000000, 9000000000000]) (some (0, 6, 2)) (some (0, 6, 2)) (.next ([4125000000000],
      [1500000000000]) (some (0, 6, 2)) (some (0, 6, 2)) (.next ([6075000000000, 0], [2250000000000,
      9000000000000]) (some (0, 6, 2)) (some (0, 6, 2)) (.next ([5625000000000], [2625000000000])
      (some (0, 6, 2)) (some (0, 6, 2)) (.next ([5250000000000, 0], [2625000000000, 9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([750000000000, -9000000000000], [375000000000,
      9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([5250000000000, -9000000000000],
      [3750000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([375000000000], [300000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([4575000000000], [3750000000000]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([375000000000], [375000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([3750000000000], [4125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([375000000000], [450000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3000000000000],
      [4125000000000]) (some (0, 1, 3)) (some (0, 1, 4)) (.next ([2250000000000], [4500000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1875000000000], [4200000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([1500000000000], [3750000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([1875000000000, 0], [4875000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 5))
      fan33Owner2Part0)))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked33 : StepValid model33 9000000000000 step33 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded33_0
    · exact excluded33_1
    · exact excluded33_2
    · exact (hj rfl).elim
    · exact excluded33_4
    · exact excluded33_5
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown250000260000
end ConwaySoifer.Simplified.Certificates
