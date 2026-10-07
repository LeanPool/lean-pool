/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint100000110000
import Mathlib.Tactic.FinCases

/-!
# Sint 100000 110000 4

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
namespace Sint100000110000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner4Part0 : FanWitness := (.next ([7470000000000, -9000000000000], [900000000000,
    9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([6150000000000, 0], [900000000000,
    9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4470000000000], [900000000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([3600000000000], [750000000000]) (some (4, 1, 5)) (some (4,
    1, 5)) (.next ([1350000000000], [300000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([6150000000000], [2220000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2700000000000,
    -9000000000000], [1650000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([3150000000000], [3900000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1800000000000],
    [3600000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([900000000000], [3000000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([750000000000], [4020000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([0, 0], [900000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([0, -9000000000000], [3000000000000, 0]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-900000000000, -9000000000000], [8370000000000, 0]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-900000000000, -9000000000000], [7050000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2,
    5)) (.next ([-900000000000], [5370000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-750000000000], [4350000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-300000000000],
    [1650000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-2220000000000], [8370000000000])
    (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-1650000000000, -9000000000000], [4350000000000, 0])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3900000000000], [7050000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-3600000000000], [5400000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-3000000000000], [3900000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-4020000000000], [4770000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
    4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner6Part0 : FanWitness := (.next ([4125000000000], [825000000000]) (some (5, 0, 3)) (some
    (5, 0, 3)) (.next ([4275000000000], [1350000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next
    ([3600000000000], [1500000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([2700000000000,
    -9000000000000], [1500000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next ([3375000000000,
    -9000000000000], [2250000000000, 9000000000000]) (some (4, 0, 3)) (some (4, 0, 5)) (.next
    ([4650000000000], [4350000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([900000000000,
    9000000000000], [900000000000, 9000000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([750000000000, 0], [4500000000000, -9000000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([525000000000], [3525000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next ([750000000000],
    [5400000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0, 0], [900000000000,
    9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-150000000000, -9000000000000],
    [6300000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-450000000000,
    9000000000000], [4725000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-600000000000, 9000000000000], [5100000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-825000000000], [4950000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1350000000000],
    [5625000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1500000000000], [5100000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1500000000000], [4200000000000, -9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2250000000000, -9000000000000], [5625000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4350000000000], [9000000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-900000000000, -9000000000000], [1800000000000, 18000000000000]) (some
    (0, 2, 5)) (some (0, 2, 5)) (.next ([-4500000000000, 9000000000000], [5250000000000,
    -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3525000000000], [4050000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5400000000000], [6150000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1350000000000, 0], [150000000000,
      9000000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([1305000000000, 0], [450000000000,
      9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([525000000000], [225000000000])
      (some (0, 5, 4)) (some (0, 5, 4)) (.next ([5625000000000], [3600000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([270000000000], [180000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([5175000000000], [3870000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([750000000000], [600000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([1125000000000, 0],
      [900000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([4725000000000,
      -9000000000000], [5625000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([450000000000], [855000000000]) (some (0, 5, 4)) (some (5, 5, 4)) (.next ([0, 0],
      [900000000000, 9000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-150000000000,
      -9000000000000], [1500000000000, 9000000000000]) (some (5, 5, 0)) (some (5, 5, 0)) (.next
      ([-450000000000, -9000000000000], [1755000000000, 9000000000000]) (some (5, 5, 0)) (some (5,
      5, 0)) (.next ([-225000000000], [750000000000]) (some (5, 5, 0)) (some (5, 5, 0)) (.next
      ([-3600000000000], [9225000000000]) (some (5, 5, 0)) (some (5, 5, 0)) (.next ([-180000000000],
      [450000000000]) (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-3870000000000], [9045000000000])
      (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-600000000000], [1350000000000]) (some (5, 3, 0))
      (some (5, 3, 0)) (.next ([-900000000000, -9000000000000], [2025000000000, 9000000000000])
      (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-5625000000000, -9000000000000], [10350000000000,
      0]) (some (5, 3, 0)) (some (5, 3, 0)) (.next ([-855000000000], [1305000000000]) (some (5, 3,
      0)) (some (5, 3, 0)) (.terminal (some (5, 3, 0)) (some (5, 3, 0)) (some (5, 3,
      0))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6150000000000, 0], [900000000000,
      9000000000000]) (some (0, 0, 4)) (some (0, 1, 4)) (.next ([4500000000000], [900000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([3600000000000, -9000000000000], [1800000000000,
      9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([3375000000000], [4275000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([2475000000000, -9000000000000], [4275000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1125000000000], [3150000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([1875000000000], [7650000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([750000000000], [4500000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [6150000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-900000000000, -9000000000000],
      [7050000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-900000000000],
      [5400000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1800000000000, -9000000000000],
      [5400000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4275000000000], [7650000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4275000000000, 0], [6750000000000,
      -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3150000000000], [4275000000000])
      (some (0, 2, 4)) (some (0, 4, 4)) (.next ([-7650000000000], [9525000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-4500000000000], [5250000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.terminal (some (0, 4, 0)) (some (0, 4, 0)) (some (0, 4, 0))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded32_3
    · exact excluded32_4
    · exact excluded32_5
    · exact (hj rfl).elim
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7800000000000], [270000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([7245000000000], [900000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 4, 4)) (.next ([7875000000000], [1125000000000]) (some (3, 4, 4)) (some (3, 4, 4))
      (.next ([6945000000000], [1200000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([900000000000], [300000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([630000000000],
      [8370000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0], [900000000000, 9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-270000000000], [8070000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-900000000000, -9000000000000], [8145000000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1125000000000], [9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-1200000000000], [8145000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-300000000000], [1200000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-8370000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4,
      2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) fan33Owner4Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8370000000000], [630000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([6150000000000, 0], [900000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([4500000000000], [900000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([7470000000000, -9000000000000], [1530000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([5520000000000], [2850000000000]) (some (4, 1, 2)) (some (4, 1, 4))
      (.next ([750000000000], [4500000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([270000000000], [3600000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [6150000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-630000000000], [9000000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-900000000000, -9000000000000], [7050000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-900000000000], [5400000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1530000000000, -9000000000000], [9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2850000000000], [8370000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-4500000000000], [5250000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-3600000000000], [3870000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded33_1
    · exact excluded33_2
    · exact excluded33_3
    · exact excluded33_4
    · exact excluded33_5
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6150000000000], [150000000000, 9000000000000])
      (some (5, 0, 2)) (some (5, 0, 3)) (.next ([4275000000000, 0], [450000000000, -9000000000000])
      (some (5, 0, 3)) (some (5, 0, 3)) (.next ([4500000000000, 9000000000000], [600000000000,
      -9000000000000]) (some (5, 0, 3)) (some (5, 0, 3)) fan34Owner6Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_8 : ExcludedOn (model34.B 8 ++ [step34.q]) 9000000000000 (model34.caps 8)
    (model34.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_9 : ExcludedOn (model34.B 9 ++ [step34.q]) 9000000000000 (model34.caps 9)
    (model34.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked34 : StepValid model34 9000000000000 step34 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded34_0
    · exact (hj rfl).elim
    · exact excluded34_2
    · exact excluded34_3
    · exact excluded34_4
    · exact excluded34_5
    · exact excluded34_6
    · exact excluded34_7
    · exact excluded34_8
    · exact excluded34_9
theorem next34 : model34.insert step34 = model35 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6375000000000], [75000000000]) (some (4, 0, 1))
      (some (4, 0, 2)) (.next ([5250000000000], [1200000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([4350000000000, -9000000000000], [1200000000000, 0]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([1125000000000, 0], [900000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([4200000000000], [4950000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([1500000000000], [2775000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1500000000000],
      [3900000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([600000000000, -9000000000000],
      [4800000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0],
      [1125000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-75000000000], [6450000000000])
      (some (4, 0, 2)) (some (4, 0, 3)) (.next ([-1200000000000], [6450000000000]) (some (4, 0, 3))
      (some (4, 0, 3)) (.next ([-1200000000000, 0], [5550000000000, -9000000000000]) (some (4, 0,
      3)) (some (4, 0, 3)) (.next ([-900000000000, -9000000000000], [2025000000000, 9000000000000])
      (some (4, 0, 3)) none (.next ([-4950000000000], [9150000000000]) none none (.next
      ([-2775000000000], [4275000000000]) none none (.next ([-3900000000000], [5400000000000]) none
      none (.next ([-4800000000000, -9000000000000], [5400000000000, 0]) (some (0, 1, 4)) (some (0,
      1, 4)) (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8100000000000, -9000000000000], [900000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4350000000000, -9000000000000],
      [1200000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1200000000000],
      [2550000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([300000000000, -9000000000000],
      [3450000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [900000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-900000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next
      ([-1200000000000, 0], [5550000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-2550000000000], [3750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3450000000000, -9000000000000], [3750000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_7 : ExcludedOn (model35.B 7 ++ [step35.q]) 9000000000000 (model35.caps 7)
    (model35.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([900000000000, -9000000000000], [0,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([6450000000000], [2850000000000,
      -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([5550000000000], [2850000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([6450000000000], [3750000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([5550000000000, -9000000000000], [3750000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([900000000000], [900000000000]) (some (0, 4, 3)) (some (4, 4, 3))
      (.next ([0, 9000000000000], [900000000000, -9000000000000]) (some (4, 4, 3)) (some (4, 4, 3))
      (.next ([0, 0], [900000000000, 9000000000000]) (some (4, 4, 3)) (some (4, 4, 3)) (.next ([0,
      -9000000000000], [900000000000]) (some (4, 4, 3)) (some (4, 4, 3)) (.next ([-2850000000000,
      9000000000000], [9300000000000, -9000000000000]) (some (4, 4, 3)) (some (4, 4, 3)) (.next
      ([-2850000000000], [8400000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3750000000000], [10200000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3750000000000, 0], [9300000000000, -9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-900000000000], [1800000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-900000000000, 9000000000000], [900000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal
      (some (4, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_8 : ExcludedOn (model35.B 8 ++ [step35.q]) 9000000000000 (model35.caps 8)
    (model35.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_9 : ExcludedOn (model35.B 9 ++ [step35.q]) 9000000000000 (model35.caps 9)
    (model35.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked35 : StepValid model35 9000000000000 step35 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded35_1
    · exact excluded35_2
    · exact excluded35_3
    · exact excluded35_4
    · exact excluded35_5
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint100000110000
end ConwaySoifer.Simplified.Certificates
