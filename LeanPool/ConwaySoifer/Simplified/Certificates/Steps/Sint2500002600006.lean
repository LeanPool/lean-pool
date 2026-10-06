/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint250000260000
import Mathlib.Tactic.FinCases

/-!
# Sint 250000 260000 6

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
namespace Sint250000260000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner4Part0 : FanWitness := (.next ([1500000000000], [5250000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([1050000000000], [5250000000000]) (some (5, 1, 6)) (some (5, 1, 6))
    (.next ([1125000000000], [8100000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([150000000000], [1350000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([150000000000],
    [2250000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0], [2250000000000,
    9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, -9000000000000], [3000000000000,
    0]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-375000000000], [2850000000000]) (some (0, 1, 6))
    (some (0, 2, 6)) (.next ([-1125000000000, -9000000000000], [8100000000000, 0]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-750000000000, -9000000000000], [5250000000000, 0]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-1200000000000], [6750000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-1125000000000], [5100000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1350000000000], [5400000000000]) (some (0, 2, 6)) (some (0, 6, 6)) (.next ([-750000000000],
    [2250000000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next ([-2250000000000, -9000000000000],
    [6300000000000, 9000000000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next ([-2250000000000,
    -9000000000000], [5400000000000, 0]) (some (0, 6, 6)) (some (0, 6, 6)) (.next ([-4050000000000],
    [9225000000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next ([-3000000000000], [5250000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2700000000000], [3825000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-5250000000000], [6750000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-5250000000000], [6300000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-8100000000000], [9225000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-1350000000000],
    [1500000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2250000000000], [2400000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.terminal (some (0, 6, 5)) (some (0, 6, 5)) (some (0, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner5Part0 : FanWitness := (.next ([4875000000000], [1575000000000]) (some (5, 1, 2))
    (some (5, 1, 3)) (.next ([5850000000000, -9000000000000], [2025000000000, 9000000000000]) (some
    (5, 1, 3)) (some (5, 1, 3)) (.next ([3600000000000], [1650000000000]) (some (5, 1, 3)) (some (5,
    1, 3)) (.next ([4875000000000, 0], [2250000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
    5)) (.next ([4200000000000, -9000000000000], [2250000000000, 9000000000000]) (some (5, 1, 5))
    (some (5, 1, 5)) (.next ([5100000000000], [3000000000000]) (some (5, 1, 5)) (some (5, 1, 5))
    (.next ([1950000000000], [1875000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([1875000000000], [2625000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2250000000000],
    [4500000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([225000000000], [1425000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([225000000000], [7875000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([0], [4875000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-375000000000, -9000000000000], [2625000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-1575000000000], [6450000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2025000000000,
    -9000000000000], [7875000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1650000000000],
    [5250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2250000000000, -9000000000000],
    [7125000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2250000000000,
    -9000000000000], [6450000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3000000000000],
    [8100000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1875000000000], [3825000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2625000000000], [4500000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4500000000000], [6750000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-1425000000000], [1650000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-7875000000000], [8100000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
    5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner6Part0 : FanWitness := (.next ([-900000000000], [8775000000000]) (some (7, 4, 5))
    (some (7, 4, 5)) (.next ([-750000000000, -9000000000000], [6750000000000, 9000000000000]) (some
    (7, 4, 5)) (some (7, 4, 5)) (.next ([-525000000000], [3900000000000]) (some (7, 4, 5)) (some (7,
    4, 5)) (.next ([-412500000000], [3000000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([-787500000000], [4125000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-1875000000000,
    -9000000000000], [7500000000000, 9000000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([-1912500000000], [6412500000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-375000000000],
    [1125000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-3150000000000, -9000000000000],
    [8775000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-3150000000000], [7500000000000])
    (some (7, 4, 5)) (some (7, 4, 7)) (.next ([-2775000000000], [6375000000000]) (some (2, 4, 7))
    (some (2, 4, 7)) (.next ([-2250000000000, -9000000000000], [4500000000000, 18000000000000])
    (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-2625000000000, -9000000000000], [4875000000000])
    (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-2625000000000, 9000000000000], [4500000000000])
    (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-2250000000000, 9000000000000], [3750000000000,
    -9000000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-4162500000000, -9000000000000],
    [6412500000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-2362500000000], [3375000000000])
    (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-3000000000000], [4125000000000]) (some (2, 4, 7))
    (some (2, 4, 7)) (.next ([-4500000000000], [6000000000000]) (some (2, 4, 7)) (some (2, 4, 7))
    (.next ([-6525000000000, 9000000000000], [7875000000000]) (some (2, 4, 7)) (some (2, 4, 7))
    (.next ([-4125000000000], [4875000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next
    ([-3000000000000, 9000000000000], [3375000000000, -9000000000000]) (some (2, 4, 7)) (some (2, 4,
    7)) (.next ([-4162500000000, 9000000000000], [4500000000000]) (some (2, 4, 7)) (some (2, 4, 7))
    (.next ([-5250000000000], [5625000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.terminal (some
    (2, 4, 7)) (some (2, 4, 7)) (some (2, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner6Part1 : FanWitness := (.next ([3375000000000], [525000000000]) (some (7, 2, 5)) (some
    (7, 2, 5)) (.next ([2587500000000], [412500000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([3337500000000], [787500000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([5625000000000],
    [1875000000000, 9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([4500000000000],
    [1912500000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([750000000000], [375000000000]) (some
    (7, 2, 5)) (some (7, 2, 5)) (.next ([5625000000000, -9000000000000], [3150000000000,
    9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([4350000000000], [3150000000000])
    (some (7, 2, 5)) (some (7, 2, 5)) (.next ([3600000000000], [2775000000000]) (some (7, 2, 5))
    (some (7, 2, 5)) (.next ([2250000000000, 9000000000000], [2250000000000, 9000000000000]) (some
    (7, 2, 5)) (some (7, 2, 5)) (.next ([2250000000000, -9000000000000], [2625000000000,
    9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([1875000000000, 9000000000000],
    [2625000000000, -9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([1500000000000, 0],
    [2250000000000, -9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([2250000000000,
    -9000000000000], [4162500000000, 9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([1012500000000], [2362500000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([1125000000000],
    [3000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([1500000000000], [4500000000000])
    (some (7, 2, 5)) (some (7, 2, 5)) (.next ([1350000000000, 9000000000000], [6525000000000,
    -9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([750000000000], [4125000000000])
    (some (7, 2, 5)) (some (7, 2, 5)) (.next ([375000000000, 0], [3000000000000, -9000000000000])
    (some (7, 2, 5)) (some (7, 2, 5)) (.next ([337500000000, 9000000000000], [4162500000000,
    -9000000000000]) (some (7, 2, 5)) (some (7, 3, 5)) (.next ([375000000000], [5250000000000])
    (some (7, 3, 5)) (some (7, 3, 5)) (.next ([0], [1537500000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-375000000000], [4875000000000]) (some (7, 3, 5)) (some (7, 4, 5))
    fan49Owner6Part0))))))))))))))))))))))))

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6750000000000, -9000000000000], [2250000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3750000000000, -9000000000000],
      [1500000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1500000000000,
      -9000000000000], [6000000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([750000000000],
      [5250000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [2250000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-2250000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-1500000000000,
      -9000000000000], [5250000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6000000000000,
      0], [7500000000000, -9000000000000]) (some (0, 1, 2)) (some (3, 1, 2)) (.next
      ([-5250000000000], [6000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_3 : ExcludedOn (model48.B 3 ++ [step48.q]) 9000000000000 (model48.caps 3)
    (model48.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5325000000000], [1875000000000, 9000000000000])
      (some (3, 0, 5)) (some (4, 0, 5)) (.next ([5325000000000], [2250000000000, 9000000000000])
      (some (4, 0, 5)) (some (4, 0, 5)) (.next ([5250000000000], [3000000000000]) (some (4, 0, 5))
      (some (4, 0, 5)) (.next ([1875000000000], [1125000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      (.next ([4200000000000], [2625000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([4200000000000], [3000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2325000000000],
      [2925000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1950000000000], [2925000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([3000000000000, -9000000000000], [5250000000000,
      9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([2250000000000], [4875000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([375000000000], [4950000000000]) (some (4, 1, 3))
      (some (4, 5, 3)) (.next ([0], [2250000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5,
      3)) (.next ([-1875000000000, -9000000000000], [7200000000000, 9000000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-2250000000000, -9000000000000], [7575000000000, 9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3000000000000], [8250000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-1125000000000], [3000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-2625000000000], [6825000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-3000000000000], [7200000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-2925000000000], [5250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-2925000000000], [4875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5250000000000,
      -9000000000000], [8250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4875000000000],
      [7125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4950000000000], [5325000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
      3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_9 : ExcludedOn (model48.B 9 ++ [step48.q]) 9000000000000 (model48.caps 9)
    (model48.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked48 : StepValid model48 9000000000000 step48 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded48_1
    · exact excluded48_2
    · exact excluded48_3
    · exact excluded48_4
    · exact excluded48_5
    · exact excluded48_6
    · exact excluded48_7
    · exact excluded48_8
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded49_1 : ExcludedOn (model49.B 1 ++ [step49.q]) 9000000000000 (model49.caps 1)
    (model49.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_2 : ExcludedOn (model49.B 2 ++ [step49.q]) 9000000000000 (model49.caps 2)
    (model49.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_3 : ExcludedOn (model49.B 3 ++ [step49.q]) 9000000000000 (model49.caps 3)
    (model49.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_4 : ExcludedOn (model49.B 4 ++ [step49.q]) 9000000000000 (model49.caps 4)
    (model49.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 6)) (some (5, 1, 6)) (.next ([2475000000000], [375000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([6975000000000, -9000000000000], [1125000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4500000000000, -9000000000000],
      [750000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([5550000000000],
      [1200000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3975000000000], [1125000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4050000000000], [1350000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([1500000000000], [750000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([4050000000000, 0], [2250000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([3150000000000, -9000000000000], [2250000000000, 9000000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([5175000000000], [4050000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([2250000000000], [3000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([1125000000000], [2700000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan49Owner4Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2250000000000, -9000000000000], [375000000000,
      9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan49Owner5Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_6 : ExcludedOn (model49.B 6 ++ [step49.q]) 9000000000000 (model49.caps 6)
    (model49.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [375000000000]) (some (7, 2, 4))
      (some (7, 2, 5)) (.next ([7875000000000], [900000000000]) (some (7, 2, 5)) (some (7, 2, 5))
      (.next ([6000000000000], [750000000000, 9000000000000]) (some (7, 2, 5)) (some (7, 2, 5))
      fan49Owner6Part1)))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_7 : ExcludedOn (model49.B 7 ++ [step49.q]) 9000000000000 (model49.caps 7)
    (model49.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_8 : ExcludedOn (model49.B 8 ++ [step49.q]) 9000000000000 (model49.caps 8)
    (model49.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_9 : ExcludedOn (model49.B 9 ++ [step49.q]) 9000000000000 (model49.caps 9)
    (model49.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked49 : StepValid model49 9000000000000 step49 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded49_1
    · exact excluded49_2
    · exact excluded49_3
    · exact excluded49_4
    · exact excluded49_5
    · exact excluded49_6
    · exact excluded49_7
    · exact excluded49_8
    · exact excluded49_9
theorem next49 : model49.insert step49 = model50 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded50_1 : ExcludedOn (model50.B 1 ++ [step50.q]) 9000000000000 (model50.caps 1)
    (model50.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6375000000000, 0], [375000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([5175000000000, 0], [2250000000000,
      9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([3000000000000], [2625000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([3750000000000], [3750000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([675000000000], [1200000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([2550000000000], [5625000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next
      ([1875000000000], [4500000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([750000000000,
      -9000000000000], [2625000000000, 0]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([0, 0],
      [2250000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-375000000000,
      -9000000000000], [6750000000000, 9000000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next
      ([-2250000000000, -9000000000000], [7425000000000, 9000000000000]) (some (4, 2, 0)) (some (4,
      2, 0)) (.next ([-2625000000000], [5625000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next
      ([-3750000000000], [7500000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next
      ([-1200000000000], [1875000000000]) (some (1, 2, 0)) (some (1, 2, 0)) (.next
      ([-5625000000000], [8175000000000]) (some (1, 2, 0)) (some (1, 2, 0)) (.next
      ([-4500000000000], [6375000000000]) (some (1, 2, 0)) (some (1, 2, 0)) (.next ([-2625000000000,
      0], [3375000000000, -9000000000000]) (some (1, 2, 0)) (some (1, 2, 0)) (.terminal (some (1, 2,
      0)) (some (1, 2, 4)) (some (1, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_2 : ExcludedOn (model50.B 2 ++ [step50.q]) 9000000000000 (model50.caps 2)
    (model50.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6750000000000, -9000000000000], [2250000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2625000000000], [3375000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([750000000000, -9000000000000], [2625000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([375000000000, -9000000000000], [5625000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [2250000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-2250000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-3375000000000],
      [6000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2625000000000, 0],
      [3375000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5625000000000,
      -9000000000000], [6000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_3 : ExcludedOn (model50.B 3 ++ [step50.q]) 9000000000000 (model50.caps 3)
    (model50.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_4 : ExcludedOn (model50.B 4 ++ [step50.q]) 9000000000000 (model50.caps 4)
    (model50.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_5 : ExcludedOn (model50.B 5 ++ [step50.q]) 9000000000000 (model50.caps 5)
    (model50.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_6 : ExcludedOn (model50.B 6 ++ [step50.q]) 9000000000000 (model50.caps 6)
    (model50.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_7 : ExcludedOn (model50.B 7 ++ [step50.q]) 9000000000000 (model50.caps 7)
    (model50.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_8 : ExcludedOn (model50.B 8 ++ [step50.q]) 9000000000000 (model50.caps 8)
    (model50.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_9 : ExcludedOn (model50.B 9 ++ [step50.q]) 9000000000000 (model50.caps 9)
    (model50.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked50 : StepValid model50 9000000000000 step50 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded50_1
    · exact excluded50_2
    · exact excluded50_3
    · exact excluded50_4
    · exact excluded50_5
    · exact excluded50_6
    · exact excluded50_7
    · exact excluded50_8
    · exact excluded50_9
theorem next50 : model50.insert step50 = model51 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint250000260000
end ConwaySoifer.Simplified.Certificates
