/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown300000310000
import Mathlib.Tactic.FinCases

/-!
# Aown 300000 310000 2

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
namespace Aown300000310000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner0Part0 : FanWitness := (.next ([-750000000000], [3615000000000]) (some (0, 8, 5))
    (some (0, 8, 6)) (.next ([-1905000000000], [6405000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-1950000000000], [6450000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-1365000000000], [3975000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-600000000000],
    [1350000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1350000000000], [3015000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-750000000000], [1665000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-1425000000000], [3150000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-2700000000000], [5850000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-600000000000], [1200000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-6000000000000],
    [9375000000000]) (some (0, 8, 6)) (some (1, 8, 6)) (.next ([-6150000000000], [9375000000000])
    (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-3390000000000], [5100000000000]) (some (1, 8, 6))
    (some (1, 8, 6)) (.next ([-3540000000000], [5250000000000]) (some (1, 8, 6)) (some (1, 8, 6))
    (.next ([-3615000000000], [5100000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next
    ([-4575000000000], [6225000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-4725000000000],
    [6225000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-6750000000000], [8775000000000])
    (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-4740000000000], [5850000000000]) (some (1, 8, 6))
    (some (1, 8, 6)) (.next ([-6150000000000], [7425000000000]) (some (1, 8, 6)) (some (1, 8, 6))
    (.next ([-4515000000000], [5040000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next
    ([-1950000000000], [2100000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-5400000000000],
    [5760000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-5325000000000], [5625000000000])
    (some (1, 8, 6)) (some (1, 8, 6)) (.terminal (some (1, 8, 6)) (some (1, 8, 6)) (some (1, 8,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner0Part1 : FanWitness := (.next ([600000000000], [600000000000]) (some (6, 3, 8)) (some
    (6, 3, 8)) (.next ([3375000000000], [6000000000000]) (some (6, 3, 8)) (some (6, 3, 8)) (.next
    ([3225000000000], [6150000000000]) (some (6, 3, 8)) (some (6, 3, 8)) (.next ([1710000000000],
    [3390000000000]) (some (6, 3, 8)) (some (6, 3, 8)) (.next ([1710000000000], [3540000000000])
    (some (6, 3, 8)) (some (7, 3, 8)) (.next ([1485000000000], [3615000000000]) (some (7, 3, 8))
    (some (7, 3, 8)) (.next ([1650000000000], [4575000000000]) (some (7, 3, 8)) (some (7, 3, 8))
    (.next ([1500000000000], [4725000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([2025000000000], [6750000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([1110000000000],
    [4740000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([1275000000000], [6150000000000])
    (some (7, 3, 8)) (some (7, 3, 8)) (.next ([525000000000], [4515000000000]) (some (7, 3, 8))
    (some (7, 3, 8)) (.next ([150000000000], [1950000000000]) (some (7, 3, 8)) (some (7, 3, 8))
    (.next ([360000000000], [5400000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([300000000000], [5325000000000]) (some (7, 3, 8)) (some (7, 8, 8)) (.next ([0],
    [1950000000000]) (some (7, 8, 8)) (some (7, 8, 8)) (.next ([-240000000000], [5490000000000])
    (some (0, 8, 8)) (some (0, 8, 8)) (.next ([-300000000000], [4275000000000]) (some (0, 8, 8))
    (some (0, 8, 8)) (.next ([-450000000000], [4725000000000]) (some (0, 8, 5)) (some (0, 8, 5))
    (.next ([-600000000000], [5700000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next
    ([-900000000000], [7665000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([-750000000000],
    [5850000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([-600000000000], [3615000000000])
    (some (0, 8, 5)) (some (0, 8, 5)) (.next ([-600000000000], [3390000000000]) (some (0, 8, 5))
    (some (0, 8, 5)) fan16Owner0Part0))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [240000000000]) (some (6, 1, 8))
      (some (6, 1, 8)) (.next ([3975000000000], [300000000000]) (some (6, 1, 8)) (some (6, 1, 8))
      (.next ([4275000000000], [450000000000]) (some (6, 1, 8)) (some (6, 1, 8)) (.next
      ([5100000000000], [600000000000]) (some (6, 1, 8)) (some (6, 1, 8)) (.next ([6765000000000],
      [900000000000]) (some (6, 1, 8)) (some (6, 1, 8)) (.next ([5100000000000], [750000000000])
      (some (6, 1, 8)) (some (6, 1, 8)) (.next ([3015000000000], [600000000000]) (some (6, 1, 8))
      (some (6, 1, 8)) (.next ([2790000000000], [600000000000]) (some (6, 1, 8)) (some (6, 1, 8))
      (.next ([2865000000000], [750000000000]) (some (6, 1, 8)) (some (6, 1, 8)) (.next
      ([4500000000000], [1905000000000]) (some (6, 1, 8)) (some (6, 1, 8)) (.next ([4500000000000],
      [1950000000000]) (some (6, 1, 8)) (some (6, 1, 8)) (.next ([2610000000000], [1365000000000])
      (some (6, 1, 8)) (some (6, 1, 8)) (.next ([750000000000], [600000000000]) (some (6, 1, 8))
      (some (6, 1, 8)) (.next ([1665000000000], [1350000000000]) (some (6, 1, 8)) (some (6, 2, 8))
      (.next ([915000000000], [750000000000]) (some (6, 2, 8)) (some (6, 2, 8)) (.next
      ([1725000000000], [1425000000000]) (some (6, 2, 8)) (some (6, 3, 8)) (.next ([3150000000000],
      [2700000000000]) (some (6, 3, 8)) (some (6, 3, 8)) fan16Owner0Part1)))))))))))))))))) (den :=
      9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3600000000000, 0], [1725000000000,
      9000000000000]) none none (.next ([2700000000000, 9000000000000], [2100000000000,
      -9000000000000]) (some (2, 3, 2)) (some (2, 3, 2)) (.next ([2700000000000, 9000000000000],
      [2700000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([75000000000,
      9000000000000], [900000000000, -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0],
      [7500000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1725000000000,
      -9000000000000], [5325000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2100000000000, 9000000000000], [4800000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next
      ([-2700000000000, -9000000000000], [5400000000000, 18000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-900000000000, 9000000000000], [975000000000]) (some (3, 1, 2)) none
      (.terminal none none none))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_9 : ExcludedOn (model16.B 9 ++ [step16.q]) 9000000000000 (model16.caps 9)
    (model16.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked16 : StepValid model16 9000000000000 step16 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded16_0
    · exact excluded16_1
    · exact excluded16_2
    · exact excluded16_3
    · exact excluded16_4
    · exact excluded16_5
    · exact (hj rfl).elim
    · exact excluded16_7
    · exact excluded16_8
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded17_0 : ExcludedOn (model17.B 0 ++ [step17.q]) 9000000000000 (model17.caps 0)
    (model17.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2700000000000, 9000000000000], [2100000000000,
      -9000000000000]) none none (.next ([3075000000000, 0], [2700000000000, 9000000000000]) (some
      (0, 3, 2)) (some (0, 3, 2)) (.next ([2700000000000, 9000000000000], [2700000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0], [7500000000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2100000000000, 9000000000000], [4800000000000, 0])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2700000000000, -9000000000000], [5775000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2700000000000, -9000000000000],
      [5400000000000, 18000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.terminal (some (3, 3, 2))
      none none))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_9 : ExcludedOn (model17.B 9 ++ [step17.q]) 9000000000000 (model17.caps 9)
    (model17.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked17 : StepValid model17 9000000000000 step17 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded17_0
    · exact excluded17_1
    · exact excluded17_2
    · exact excluded17_3
    · exact excluded17_4
    · exact excluded17_5
    · exact (hj rfl).elim
    · exact excluded17_7
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6300000000000, 9000000000000], [2925000000000,
      -9000000000000]) (some (3, 0, 3)) (some (3, 1, 3)) (.next ([2700000000000, 9000000000000],
      [2700000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3600000000000],
      [5625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([900000000000, -9000000000000],
      [5625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0], [2700000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2925000000000, 9000000000000],
      [9225000000000, 0]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2700000000000,
      -9000000000000], [5400000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-5625000000000], [9225000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5625000000000,
      0], [6525000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 3, 3)) (some (0, 3, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000], [300000000000]) (some (3, 0, 1))
      (some (3, 0, 2)) (.next ([4425000000000], [750000000000]) (some (3, 0, 2)) (some (3, 0, 2))
      (.next ([5400000000000], [975000000000]) (some (3, 0, 2)) (some (4, 0, 2)) (.next
      ([2925000000000, 9000000000000], [2700000000000, -9000000000000]) (some (4, 0, 2)) (some (4,
      0, 2)) (.next ([450000000000], [525000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([2700000000000, 9000000000000], [5925000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([1725000000000, 9000000000000], [6375000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([225000000000], [5400000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0],
      [2700000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-300000000000],
      [5700000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-750000000000], [5175000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-975000000000], [6375000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([-2700000000000, 9000000000000], [5625000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([-525000000000], [975000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-5925000000000, 0], [8625000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 3))
      (.next ([-6375000000000, 0], [8100000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-5400000000000], [5625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some
      (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_9 : ExcludedOn (model18.B 9 ++ [step18.q]) 9000000000000 (model18.caps 9)
    (model18.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked18 : StepValid model18 9000000000000 step18 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded18_1
    · exact excluded18_2
    · exact excluded18_3
    · exact excluded18_4
    · exact excluded18_5
    · exact excluded18_6
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown300000310000
end ConwaySoifer.Simplified.Certificates
