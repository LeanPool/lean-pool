/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint150000160000
import Mathlib.Tactic.FinCases

/-!
# Sint 150000 160000 2

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
namespace Sint150000160000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part0 : FanWitness := (.next ([1206000000000, 5040000000000], [5172000000000,
    -2520000000000]) (some (6, 6, 5)) (some (6, 6, 5)) (.next ([900000000000], [4725000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([825000000000], [6000000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([306000000000, 5040000000000], [4797000000000, -2520000000000]) (some
    (6, 3, 5)) (some (6, 3, 5)) (.next ([72000000000, -2520000000000], [5172000000000,
    -2520000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([0], [675000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([-75000000000], [5625000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-75000000000], [1275000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-369000000000, 5040000000000], [4797000000000, -2520000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-750000000000], [5625000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-828000000000, -2520000000000], [5931000000000, 5040000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-1275000000000], [5550000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-1503000000000, -2520000000000], [5931000000000, 5040000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-1950000000000], [5550000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-4725000000000], [10275000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-381000000000,
    -5040000000000], [828000000000, 2520000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-4725000000000], [9600000000000]) (some (6, 3, 5)) (some (6, 4, 5)) (.next ([-828000000000,
    -2520000000000], [1581000000000, 5040000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-447000000000, 2520000000000], [753000000000, 2520000000000]) (some (6, 4, 5)) (some (6, 4,
    5)) (.next ([-5172000000000, 2520000000000], [6378000000000, 2520000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.next ([-4725000000000], [5625000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-6000000000000], [6825000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-4797000000000, 2520000000000], [5103000000000, 2520000000000]) (some (6, 4, 5)) (some (6, 4,
    5)) (.next ([-5172000000000, 2520000000000], [5244000000000, -5040000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.terminal (some (6, 4, 5)) (some (6, 4, 0)) (some (6, 4,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part1 : FanWitness := (.next ([1206000000000, 5040000000000], [5172000000000,
    -2520000000000]) (some (6, 6, 5)) (some (6, 6, 5)) (.next ([900000000000], [4725000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([825000000000], [6000000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([306000000000, 5040000000000], [4797000000000, -2520000000000]) (some
    (6, 3, 5)) (some (6, 3, 5)) (.next ([72000000000, -2520000000000], [5172000000000,
    -2520000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([0], [675000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([-75000000000], [5625000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-75000000000], [1275000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-369000000000, 5040000000000], [4797000000000, -2520000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-750000000000], [5625000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-828000000000, -2520000000000], [5931000000000, 5040000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-1275000000000], [5550000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-1503000000000, -2520000000000], [5931000000000, 5040000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-1950000000000], [5550000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-4725000000000], [10275000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-4725000000000],
    [9600000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-381000000000, -5040000000000],
    [828000000000, 2520000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-828000000000,
    -2520000000000], [1581000000000, 5040000000000]) (some (6, 3, 5)) (some (6, 4, 5)) (.next
    ([-447000000000, 2520000000000], [753000000000, 2520000000000]) (some (6, 4, 5)) (some (6, 4,
    5)) (.next ([-5172000000000, 2520000000000], [6378000000000, 2520000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.next ([-4725000000000], [5625000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-6000000000000], [6825000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-4797000000000, 2520000000000], [5103000000000, 2520000000000]) (some (6, 4, 5)) (some (6, 4,
    5)) (.next ([-5172000000000, 2520000000000], [5244000000000, -5040000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.terminal (some (6, 4, 5)) (some (6, 4, 0)) (some (6, 4,
    5)))))))))))))))))))))))))))

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6525000000000, 9000000000000], [2925000000000,
      -9000000000000]) (some (3, 3, 1)) none (.next ([5175000000000], [4275000000000]) none none
      (.next ([1350000000000, 9000000000000], [1350000000000, 9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.next ([3825000000000, -9000000000000], [4275000000000, 0]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.next ([0, 0], [1350000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-2925000000000, 9000000000000], [9450000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-4275000000000], [9450000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-1350000000000, -9000000000000], [2700000000000, 18000000000000]) (some (3, 1, 0)) (some (3,
      1, 0)) (.next ([-4275000000000, 0], [8100000000000, -9000000000000]) (some (3, 1, 0)) (some
      (3, 1, 0)) (.terminal (some (3, 1, 0)) (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7650000000000, -9000000000000], [1350000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2925000000000, -9000000000000],
      [900000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3825000000000,
      -9000000000000], [4275000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([450000000000],
      [3825000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1350000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-900000000000, -9000000000000],
      [3825000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4275000000000, 0],
      [8100000000000, -9000000000000]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-3825000000000],
      [4275000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6600000000000], [1350000000000, 9000000000000])
      (some (2, 0, 4)) (some (3, 0, 4)) (.next ([6150000000000], [1575000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([1125000000000], [450000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([1875000000000], [1950000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next
      ([3825000000000], [4725000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2475000000000,
      -9000000000000], [6075000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next
      ([2250000000000], [5850000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [1350000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 4, 2)) (.next ([-1350000000000,
      -9000000000000], [7950000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1575000000000], [7725000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-450000000000],
      [1575000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1950000000000], [3825000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4725000000000], [8550000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-6075000000000, -9000000000000], [8550000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5850000000000], [8100000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded16_1
    · exact excluded16_2
    · exact excluded16_3
    · exact excluded16_4
    · exact excluded16_5
    · exact excluded16_6
    · exact excluded16_7
    · exact excluded16_8
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7275000000000, -9000000000000], [900000000000,
      9000000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([2430000000000], [570000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([5325000000000, 0], [1350000000000, 9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([5775000000000], [2850000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([2325000000000], [2430000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([1080000000000, -9000000000000], [1920000000000, 9000000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([1020000000000], [5175000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([450000000000], [8175000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-900000000000,
      -9000000000000], [8175000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-570000000000], [3000000000000]) (some (0, 1, 4)) (some (0, 4, 4)) (.next ([-1350000000000,
      -9000000000000], [6675000000000, 9000000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next
      ([-2850000000000], [8625000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next
      ([-2430000000000], [4755000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1920000000000,
      -9000000000000], [3000000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-5175000000000], [6195000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-8175000000000], [8625000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8175000000000], [375000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([2175000000000], [450000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([6825000000000, -9000000000000], [1725000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1575000000000, 0], [1350000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 4)) (.next ([1125000000000], [1050000000000]) (some (4, 1, 4)) (some (4, 1, 4))
      (.next ([825000000000, -9000000000000], [1800000000000, 9000000000000]) (some (4, 1, 4)) (some
      (4, 1, 4)) (.next ([1200000000000], [6975000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next
      ([75000000000], [5925000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [1575000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-375000000000], [8550000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-450000000000], [2625000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1725000000000, -9000000000000], [8550000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1350000000000, -9000000000000], [2925000000000, 9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1050000000000], [2175000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1800000000000, -9000000000000], [2625000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-6975000000000], [8175000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-5925000000000], [6000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8550000000000], [825000000000]) (some (3, 0, 1))
      (some (3, 0, 2)) (.next ([7200000000000, -9000000000000], [2175000000000, 9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([525000000000, 9000000000000],
      [8025000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-825000000000],
      [9375000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2175000000000, -9000000000000],
      [9375000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-8025000000000,
      9000000000000], [8550000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.terminal (some (0, 1, 3))
      (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded17_1
    · exact excluded17_2
    · exact excluded17_3
    · exact excluded17_4
    · exact excluded17_5
    · exact excluded17_6
    · exact excluded17_7
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded18_0 : ExcludedOn (model18.B 0 ++ [step18.q]) 9000000000000 (model18.caps 0)
    (model18.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2175000000000], [5850000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2175000000000], [7200000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([825000000000, -9000000000000], [8550000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-5850000000000,
      9000000000000], [8025000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-7200000000000], [9375000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8550000000000,
      -9000000000000], [9375000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8400000000000], [225000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([2175000000000], [450000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([6825000000000], [1800000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([5475000000000, -9000000000000], [1800000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([1575000000000, 0], [1350000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([1125000000000], [1050000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([825000000000,
      -9000000000000], [1800000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([825000000000], [6450000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [1575000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-225000000000], [8625000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-450000000000], [2625000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1800000000000], [8625000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1800000000000, 0], [7275000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2,
      4)) (.next ([-1350000000000, -9000000000000], [2925000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 4, 4)) (.next ([-1050000000000], [2175000000000]) (some (0, 4, 4)) (some (0, 4, 4))
      (.next ([-1800000000000, -9000000000000], [2625000000000]) (some (0, 4, 4)) (some (0, 4, 4))
      (.next ([-6450000000000], [7275000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.terminal (some
      (0, 4, 3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded18_0
    · exact excluded18_1
    · exact excluded18_2
    · exact excluded18_3
    · exact excluded18_4
    · exact excluded18_5
    · exact (hj rfl).elim
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_0 : ExcludedOn (model19.B 0 ++ [step19.q]) 9000000000000 (model19.caps 0)
    (model19.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (2830) (4053) (405300) (.witnessedFan (.next
      ([5550000000000], [75000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([1200000000000],
      [75000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([4428000000000, 2520000000000],
      [369000000000, -5040000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([4875000000000],
      [750000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([5103000000000, 2520000000000],
      [828000000000, 2520000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([4275000000000],
      [1275000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([4428000000000, 2520000000000],
      [1503000000000, 2520000000000]) (some (0, 6, 4)) (some (0, 6, 5)) (.next ([3600000000000],
      [1950000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([5550000000000], [4725000000000])
      (some (0, 6, 5)) (some (0, 6, 5)) (.next ([447000000000, -2520000000000], [381000000000,
      5040000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([4875000000000], [4725000000000])
      (some (0, 6, 5)) (some (0, 6, 5)) (.next ([753000000000, 2520000000000], [828000000000,
      2520000000000]) (some (0, 6, 5)) (some (6, 6, 5)) (.next ([306000000000, 5040000000000],
      [447000000000, -2520000000000]) (some (6, 6, 5)) (some (6, 6, 5))
      fan19Owner0Part0)))))))))))))) (.witnessedFan (.next ([5550000000000], [75000000000]) (some
      (0, 6, 4)) (some (0, 6, 4)) (.next ([1200000000000], [75000000000]) (some (0, 6, 4)) (some (0,
      6, 4)) (.next ([4428000000000, 2520000000000], [369000000000, -5040000000000]) (some (0, 6,
      4)) (some (0, 6, 4)) (.next ([4875000000000], [750000000000]) (some (0, 6, 4)) (some (0, 6,
      4)) (.next ([5103000000000, 2520000000000], [828000000000, 2520000000000]) (some (0, 6, 4))
      (some (0, 6, 4)) (.next ([4275000000000], [1275000000000]) (some (0, 6, 4)) (some (0, 6, 4))
      (.next ([4428000000000, 2520000000000], [1503000000000, 2520000000000]) (some (0, 6, 4)) (some
      (0, 6, 5)) (.next ([3600000000000], [1950000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
      ([5550000000000], [4725000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([4875000000000],
      [4725000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([447000000000, -2520000000000],
      [381000000000, 5040000000000]) (some (0, 6, 5)) (some (6, 6, 5)) (.next ([753000000000,
      2520000000000], [828000000000, 2520000000000]) (some (6, 6, 5)) (some (6, 6, 5)) (.next
      ([306000000000, 5040000000000], [447000000000, -2520000000000]) (some (6, 6, 5)) (some (6, 6,
      5)) fan19Owner0Part1))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2175000000000], [450000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([1575000000000, 0], [1350000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1125000000000], [1050000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3450000000000], [4425000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([3450000000000], [6000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([825000000000,
      -9000000000000], [1800000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([2100000000000, -9000000000000], [7350000000000, 9000000000000]) (some (4, 1, 2)) (some (4,
      1, 3)) (.next ([1275000000000], [5550000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([0], [1575000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next ([-450000000000],
      [2625000000000]) (some (4, 1, 4)) (some (4, 2, 4)) (.next ([-1350000000000, -9000000000000],
      [2925000000000, 9000000000000]) (some (4, 2, 4)) (some (4, 2, 4)) (.next ([-1050000000000],
      [2175000000000]) (some (4, 2, 4)) (some (4, 2, 4)) (.next ([-4425000000000], [7875000000000])
      (some (4, 2, 4)) (some (4, 2, 4)) (.next ([-6000000000000], [9450000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1800000000000, -9000000000000], [2625000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-7350000000000, -9000000000000], [9450000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-5550000000000], [6825000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_9 : ExcludedOn (model19.B 9 ++ [step19.q]) 9000000000000 (model19.caps 9)
    (model19.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked19 : StepValid model19 9000000000000 step19 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded19_0
    · exact excluded19_1
    · exact excluded19_2
    · exact excluded19_3
    · exact (hj rfl).elim
    · exact excluded19_5
    · exact excluded19_6
    · exact excluded19_7
    · exact excluded19_8
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000], [450000000000]) (some (3, 0, 4))
      (some (3, 4, 4)) (.next ([5325000000000, 0], [1350000000000, 9000000000000]) (some (3, 4, 4))
      (some (3, 4, 4)) (.next ([3450000000000], [1650000000000]) (some (3, 4, 4)) (some (3, 4, 4))
      (.next ([5325000000000], [4650000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([1650000000000, -9000000000000], [1800000000000, 9000000000000]) (some (3, 4, 2)) (some (3,
      4, 2)) (.next ([1875000000000], [3000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0,
      0], [1350000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 3)) (.next ([-450000000000],
      [3450000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1350000000000, -9000000000000],
      [6675000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1650000000000],
      [5100000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4650000000000], [9975000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1800000000000, -9000000000000], [3450000000000,
      0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3000000000000], [4875000000000]) (some (0, 4,
      3)) (some (0, 4, 3)) (.terminal (some (0, 4, 3)) (some (0, 4, 3)) (some (0, 4,
      3))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_9 : ExcludedOn (model20.B 9 ++ [step20.q]) 9000000000000 (model20.caps 9)
    (model20.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked20 : StepValid model20 9000000000000 step20 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded20_0
    · exact excluded20_1
    · exact excluded20_2
    · exact excluded20_3
    · exact excluded20_4
    · exact (hj rfl).elim
    · exact excluded20_6
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1800000000000], [375000000000]) (some (4, 4, 2))
      (some (4, 4, 3)) (.next ([975000000000, 9000000000000], [825000000000, -9000000000000]) (some
      (4, 4, 3)) (some (4, 4, 3)) (.next ([4500000000000, 0], [3825000000000, -9000000000000]) (some
      (4, 4, 3)) (some (4, 4, 3)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([4500000000000], [5175000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([2700000000000], [4800000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([3150000000000, -9000000000000], [6525000000000, 9000000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([450000000000, -9000000000000], [1725000000000,
      9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-375000000000], [2175000000000])
      (some (4, 1, 3)) (some (4, 2, 3)) (.next ([-825000000000, 9000000000000], [1800000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-3825000000000, 9000000000000], [8325000000000,
      -9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-5175000000000],
      [9675000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-4800000000000], [7500000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-6525000000000, -9000000000000], [9675000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-1725000000000, -9000000000000], [2175000000000])
      (some (4, 2, 3)) (some (4, 2, 4)) (.terminal (some (4, 2, 4)) (some (4, 2, 4)) (some (4, 2,
      4))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_9 : ExcludedOn (model21.B 9 ++ [step21.q]) 9000000000000 (model21.caps 9)
    (model21.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked21 : StepValid model21 9000000000000 step21 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded21_0
    · exact excluded21_1
    · exact excluded21_2
    · exact excluded21_3
    · exact excluded21_4
    · exact (hj rfl).elim
    · exact excluded21_6
    · exact excluded21_7
    · exact excluded21_8
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1800000000000], [375000000000]) (some (0, 4, 2))
      (some (0, 4, 3)) (.next ([5850000000000, -9000000000000], [1350000000000, 9000000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([6825000000000], [2175000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([975000000000, 9000000000000], [825000000000, -9000000000000]) (some
      (0, 4, 3)) (some (0, 4, 3)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([450000000000, -9000000000000],
      [1725000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-375000000000],
      [2175000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1350000000000, -9000000000000],
      [7200000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2175000000000], [9000000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-825000000000, 9000000000000], [1800000000000])
      (some (0, 4, 3)) (some (4, 4, 3)) (.next ([-1350000000000, -9000000000000], [2700000000000,
      18000000000000]) (some (4, 4, 3)) (some (4, 4, 3)) (.next ([-1725000000000, -9000000000000],
      [2175000000000]) (some (4, 4, 3)) (some (4, 4, 3)) (.terminal (some (4, 4, 0)) (some (4, 2,
      0)) (some (4, 4, 0))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked22 : StepValid model22 9000000000000 step22 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded22_0
    · exact excluded22_1
    · exact excluded22_2
    · exact excluded22_3
    · exact excluded22_4
    · exact excluded22_5
    · exact excluded22_6
    · exact excluded22_7
    · exact excluded22_8
    · exact (hj rfl).elim
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000], [450000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5325000000000, 0], [1350000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([5775000000000], [3450000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([1650000000000, -9000000000000], [1800000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1875000000000], [3000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([900000000000], [5325000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-450000000000],
      [3450000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-1350000000000, -9000000000000],
      [6675000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-3450000000000],
      [9225000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-1800000000000, -9000000000000],
      [3450000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-3000000000000],
      [4875000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next ([-5325000000000], [6225000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2, 3)) (some (0, 2, 4)) (some (4, 2,
      4))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_9 : ExcludedOn (model23.B 9 ++ [step23.q]) 9000000000000 (model23.caps 9)
    (model23.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked23 : StepValid model23 9000000000000 step23 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded23_0
    · exact excluded23_1
    · exact excluded23_2
    · exact excluded23_3
    · exact excluded23_4
    · exact excluded23_5
    · exact excluded23_6
    · exact excluded23_7
    · exact (hj rfl).elim
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint150000160000
end ConwaySoifer.Simplified.Certificates
