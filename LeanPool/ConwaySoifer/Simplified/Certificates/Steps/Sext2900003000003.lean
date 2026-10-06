/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext290000300000
import Mathlib.Tactic.FinCases

/-!
# Sext 290000 300000 3

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
namespace Sext290000300000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner3Part0 : FanWitness := (.next ([3540000000000], [2985000000000]) (some (6, 1, 2))
    (some (6, 1, 2)) (.next ([2610000000000], [2280000000000]) (some (6, 1, 2)) (some (6, 1, 2))
    (.next ([2610000000000, 9000000000000], [2610000000000, 9000000000000]) (some (6, 1, 2)) (some
    (6, 1, 3)) (.next ([2610000000000, 9000000000000], [3795000000000, -9000000000000]) (some (6, 1,
    3)) (some (6, 1, 3)) (.next ([1515000000000], [2610000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([1905000000000], [3915000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([2025000000000, 9000000000000], [4500000000000]) (some (6, 1, 3)) (some (6, 2, 3)) (.next
    ([1515000000000], [3465000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([0, 9000000000000],
    [1515000000000, -9000000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([0], [2610000000000,
    9000000000000]) (some (6, 2, 3)) (some (6, 2, 4)) (.next ([-855000000000], [7260000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-585000000000], [4500000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-1095000000000, -9000000000000], [5220000000000, 9000000000000]) (some
    (6, 2, 4)) (some (6, 2, 4)) (.next ([-585000000000], [1890000000000, -9000000000000]) (some (6,
    2, 4)) (some (6, 2, 4)) (.next ([-2610000000000, -9000000000000], [6405000000000]) (some (6, 2,
    4)) (some (1, 2, 4)) (.next ([-2985000000000], [6525000000000]) (some (1, 2, 4)) (some (1, 2,
    4)) (.next ([-2280000000000], [4890000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next
    ([-2610000000000, -9000000000000], [5220000000000, 18000000000000]) (some (1, 2, 4)) (some (1,
    2, 4)) (.next ([-3795000000000, 9000000000000], [6405000000000]) (some (1, 2, 4)) (some (1, 2,
    4)) (.next ([-2610000000000], [4125000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next
    ([-3915000000000], [5820000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-4500000000000,
    0], [6525000000000, 9000000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-3465000000000],
    [4980000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-1515000000000, 9000000000000],
    [1515000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.terminal (some (1, 2, 4)) (some (1, 2, 4))
    (some (1, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner2Part0 : FanWitness := (.next ([927000000000], [1140000000000]) (some (6, 1, 3)) (some
    (6, 1, 3)) (.next ([2610000000000, 9000000000000], [5415000000000, 0]) (some (6, 1, 3)) (some
    (6, 1, 3)) (.next ([1875000000000], [4515000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([975000000000], [2400000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([975000000000],
    [3540000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([948000000000], [4302000000000])
    (some (6, 1, 3)) (some (6, 1, 3)) (.next ([375000000000], [3375000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([0], [1140000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([-165000000000], [4467000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([-765000000000,
    9000000000000], [6390000000000, 0]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-765000000000],
    [4515000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-213000000000], [1140000000000])
    (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-1905000000000, 9000000000000], [6390000000000, 0])
    (some (6, 1, 4)) (some (6, 2, 4)) (.next ([-1692000000000, 9000000000000], [5250000000000, 0])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1692000000000], [4302000000000]) (some (6, 2, 4))
    (some (6, 3, 4)) (.next ([-2640000000000, 0], [5250000000000, 9000000000000]) (some (6, 3, 4))
    (some (6, 3, 4)) (.next ([-3375000000000], [6390000000000]) (some (6, 3, 4)) (some (6, 3, 4))
    (.next ([-1140000000000], [2067000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-5415000000000, 0], [8025000000000, 9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-4515000000000], [6390000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-2400000000000],
    [3375000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-3540000000000], [4515000000000])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-4302000000000], [5250000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([-3375000000000], [3750000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.terminal (some (0, 3, 4)) (some (0, 3, 4)) (some (0, 3, 4)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6405000000000], [855000000000]) (some (4, 1, 2))
      (some (6, 1, 2)) (.next ([3915000000000], [585000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([4125000000000], [1095000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([1305000000000, -9000000000000], [585000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([3795000000000, -9000000000000], [2610000000000, 9000000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) fan24Owner3Part0))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_9 : ExcludedOn (model24.B 9 ++ [step24.q]) 9000000000000 (model24.caps 9)
    (model24.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked24 : StepValid model24 9000000000000 step24 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded24_0
    · exact excluded24_1
    · exact excluded24_2
    · exact excluded24_3
    · exact excluded24_4
    · exact excluded24_5
    · exact excluded24_6
    · exact excluded24_7
    · exact (hj rfl).elim
    · exact excluded24_9
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4605000000000], [60000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([5520000000000], [585000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([2085000000000], [915000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([2610000000000, 9000000000000], [2055000000000, -9000000000000]) (some (5, 1, 2)) (some (5,
      1, 2)) (.next ([3000000000000], [2520000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([2610000000000, 9000000000000], [3585000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([855000000000], [1665000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1080000000000],
      [3585000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([90000000000, 9000000000000],
      [2910000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0],
      [3585000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-60000000000], [4665000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-585000000000], [6105000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-915000000000], [3000000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-2055000000000, 9000000000000], [4665000000000]) (some (0, 1, 3)) (some (0, 1, 5))
      (.next ([-2520000000000], [5520000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-3585000000000], [6195000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-1665000000000], [2520000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-3585000000000], [4665000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2910000000000,
      9000000000000], [3000000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5))
      (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3540000000000], [855000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([4395000000000], [4605000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([3795000000000], [4350000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([45000000000], [4605000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [4350000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-855000000000], [4395000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-4605000000000], [9000000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-4350000000000], [8145000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4605000000000], [4650000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_9 : ExcludedOn (model25.B 9 ++ [step25.q]) 9000000000000 (model25.caps 9)
    (model25.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked25 : StepValid model25 9000000000000 step25 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded25_0
    · exact excluded25_1
    · exact excluded25_2
    · exact (hj rfl).elim
    · exact excluded25_4
    · exact excluded25_5
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2610000000000], [420000000000]) (some (3, 0, 1))
      (some (4, 0, 1)) (.next ([5985000000000], [1020000000000]) (some (4, 0, 1)) (some (4, 0, 5))
      (.next ([4125000000000], [2880000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
      ([3375000000000], [2610000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([2610000000000],
      [2280000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([2610000000000, 9000000000000],
      [3795000000000, -9000000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([2610000000000,
      9000000000000], [4395000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1515000000000],
      [2610000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([2010000000000], [4395000000000])
      (some (4, 0, 5)) (some (4, 0, 5)) (.next ([0, 9000000000000], [1515000000000, -9000000000000])
      (some (4, 0, 5)) (some (4, 1, 5)) (.next ([0, 9000000000000], [3375000000000, -9000000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [4395000000000]) (some (4, 1, 3)) (some (4, 1,
      3)) (.next ([-420000000000], [3030000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1020000000000], [7005000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2880000000000], [7005000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2610000000000], [5985000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2280000000000], [4890000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3795000000000,
      9000000000000], [6405000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4395000000000,
      0], [7005000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2610000000000], [4125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-4395000000000], [6405000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1515000000000,
      9000000000000], [1515000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3375000000000,
      9000000000000], [3375000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3))
      (some (0, 1, 3)) (some (0, 1, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_9 : ExcludedOn (model26.B 9 ++ [step26.q]) 9000000000000 (model26.caps 9)
    (model26.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked26 : StepValid model26 9000000000000 step26 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded26_0
    · exact excluded26_1
    · exact (hj rfl).elim
    · exact excluded26_3
    · exact excluded26_4
    · exact excluded26_5
    · exact excluded26_6
    · exact excluded26_7
    · exact excluded26_8
    · exact excluded26_9
theorem next26 : model26.insert step26 = model27 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4302000000000], [165000000000]) (some (4, 0, 3))
      (some (6, 1, 3)) (.next ([5625000000000, 9000000000000], [765000000000, -9000000000000]) (some
      (6, 1, 3)) (some (6, 1, 3)) (.next ([3750000000000], [765000000000]) (some (6, 1, 3)) (some
      (6, 1, 3)) (.next ([927000000000], [213000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([4485000000000, 9000000000000], [1905000000000, -9000000000000]) (some (6, 1, 3)) (some (6,
      1, 3)) (.next ([3558000000000, 9000000000000], [1692000000000, -9000000000000]) (some (6, 1,
      3)) (some (6, 1, 3)) (.next ([2610000000000], [1692000000000]) (some (6, 1, 3)) (some (6, 1,
      3)) (.next ([2610000000000, 9000000000000], [2640000000000, 0]) (some (6, 1, 3)) (some (6, 1,
      3)) (.next ([3015000000000], [3375000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      fan27Owner2Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([975000000000], [540000000000]) (some (3, 0, 1))
      (some (4, 0, 1)) (.next ([4125000000000], [2880000000000]) (some (4, 0, 1)) (some (4, 0, 1))
      (.next ([3585000000000], [2820000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next
      ([2610000000000], [2280000000000]) (some (4, 0, 1)) (some (4, 0, 5)) (.next ([3585000000000],
      [4395000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([2610000000000, 9000000000000],
      [3795000000000, -9000000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([2610000000000,
      9000000000000], [4395000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1515000000000],
      [2610000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([2010000000000], [4395000000000])
      (some (4, 0, 5)) (some (4, 0, 5)) (.next ([0, 9000000000000], [1515000000000, -9000000000000])
      (some (4, 0, 5)) (some (4, 1, 5)) (.next ([0], [4395000000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([-540000000000], [1515000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-2880000000000], [7005000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-2820000000000], [6405000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-2280000000000], [4890000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4395000000000], [7980000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3795000000000,
      9000000000000], [6405000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4395000000000,
      0], [7005000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-2610000000000], [4125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4395000000000], [6405000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1515000000000,
      9000000000000], [1515000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1, 5))
      (some (0, 1, 3)) (some (0, 1, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_8 : ExcludedOn (model27.B 8 ++ [step27.q]) 9000000000000 (model27.caps 8)
    (model27.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_9 : ExcludedOn (model27.B 9 ++ [step27.q]) 9000000000000 (model27.caps 9)
    (model27.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked27 : StepValid model27 9000000000000 step27 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded27_1
    · exact excluded27_2
    · exact excluded27_3
    · exact excluded27_4
    · exact excluded27_5
    · exact excluded27_6
    · exact excluded27_7
    · exact excluded27_8
    · exact excluded27_9
theorem next27 : model27.insert step27 = model28 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext290000300000
end ConwaySoifer.Simplified.Certificates
