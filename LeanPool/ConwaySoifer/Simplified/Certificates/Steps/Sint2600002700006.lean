/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint260000270000
import Mathlib.Tactic.FinCases

/-!
# Sint 260000 270000 6

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
namespace Sint260000270000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner4Part0 : FanWitness := (.next ([930000000000], [6465000000000]) (some (5, 1, 6)) (some
    (5, 1, 6)) (.next ([840000000000], [6660000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([60000000000], [975000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([375000000000],
    [6930000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0], [2340000000000,
    9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, -9000000000000], [4125000000000,
    0]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-90000000000, -9000000000000], [4680000000000,
    0]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-570000000000], [7440000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-525000000000, -9000000000000], [5625000000000, 0]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-90000000000], [555000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-1605000000000], [7500000000000]) (some (0, 2, 6)) (some (0, 3, 6)) (.next
    ([-1500000000000, -9000000000000], [6660000000000, 0]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-2340000000000, -9000000000000], [7395000000000, 9000000000000]) (some (0, 3, 5)) (some (0, 3,
    5)) (.next ([-525000000000], [1500000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-435000000000], [945000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1500000000000],
    [2535000000000]) (some (0, 3, 5)) (some (0, 4, 5)) (.next ([-4125000000000], [6465000000000])
    (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-4680000000000], [6930000000000]) (some (0, 4, 5))
    (some (0, 4, 5)) (.next ([-1410000000000], [1980000000000]) (some (0, 4, 5)) (some (0, 4, 5))
    (.next ([-5625000000000], [7440000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next
    ([-6465000000000], [7395000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-6660000000000],
    [7500000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-975000000000], [1035000000000])
    (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-6930000000000], [7305000000000]) (some (0, 4, 5))
    (some (0, 6, 5)) (.terminal (some (0, 6, 5)) (some (0, 6, 5)) (some (0, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner5Part0 : FanWitness := (.next ([1995000000000], [2160000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([2160000000000], [2340000000000]) (some (0, 1, 4)) (some (0, 1, 5))
    (.next ([2718000000000], [4320000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([2340000000000], [3750000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2160000000000],
    [3660000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2448000000000], [4500000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([165000000000], [1500000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([0], [4788000000000]) (some (0, 1, 5)) (some (0, 1, 6)) (.next
    ([-90000000000, -9000000000000], [2070000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next
    ([-180000000000, -9000000000000], [2340000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1500000000000], [8160000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1707000000000],
    [6495000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2340000000000, -9000000000000],
    [7128000000000, 9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2340000000000,
    -9000000000000], [6495000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3840000000000,
    -9000000000000], [8160000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3372000000000],
    [6660000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2250000000000], [4425000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2160000000000], [4155000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-2340000000000], [4500000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-4320000000000], [7038000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-3750000000000], [6090000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3660000000000],
    [5820000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4500000000000], [6948000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1500000000000], [1665000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.terminal (some (0, 2, 6)) (some (0, 2, 6)) (some (0, 2,
    6)))))))))))))))))))))))))))

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_3 : ExcludedOn (model48.B 3 ++ [step48.q]) 9000000000000 (model48.caps 3)
    (model48.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7500000000000, -9000000000000], [0,
      9000000000000]) (some (3, 0, 5)) (some (4, 0, 5)) (.next ([1035000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 5)) (some (4, 5, 5)) (.next ([6552000000000], [663000000000])
      (some (4, 5, 5)) (some (4, 5, 5)) (.next ([5802000000000], [750000000000]) (some (4, 5, 2))
      (some (4, 5, 2)) (.next ([7650000000000], [2190000000000]) (some (4, 5, 2)) (some (4, 5, 2))
      (.next ([2340000000000], [1035000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([4275000000000], [3375000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1098000000000],
      [1527000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([2625000000000], [4212000000000])
      (some (4, 5, 2)) (some (4, 5, 3)) (.next ([2340000000000], [7500000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([285000000000, -9000000000000], [6552000000000, 9000000000000]) (some
      (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [2340000000000, 9000000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([0, -9000000000000], [7500000000000]) (some (0, 5, 3)) (some (0, 5,
      3)) (.next ([0, -9000000000000], [1035000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-663000000000], [7215000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-750000000000],
      [6552000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2190000000000], [9840000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1035000000000], [3375000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-3375000000000], [7650000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-1527000000000], [2625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-4212000000000], [6837000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-7500000000000], [9840000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6552000000000,
      -9000000000000], [6837000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5,
      3)) (some (0, 5, 3)) (some (0, 5, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 6)) (some (5, 1, 6)) (.next ([4590000000000, -9000000000000],
      [90000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([6870000000000],
      [570000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([5100000000000, -9000000000000],
      [525000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([465000000000],
      [90000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([5895000000000], [1605000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([5160000000000, -9000000000000], [1500000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([5055000000000, 0], [2340000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([975000000000], [525000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([510000000000], [435000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([1035000000000], [1500000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([2340000000000], [4125000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([2250000000000], [4680000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([570000000000],
      [1410000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1815000000000], [5625000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) fan48Owner4Part0)))))))))))))))) (den := 9000000000000)
      (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1980000000000, -9000000000000], [90000000000,
      9000000000000]) (some (6, 0, 2)) (some (6, 1, 2)) (.next ([2160000000000, -9000000000000],
      [180000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([6660000000000],
      [1500000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4788000000000], [1707000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4788000000000, 0], [2340000000000, 9000000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4155000000000, -9000000000000], [2340000000000,
      9000000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([4320000000000, -9000000000000],
      [3840000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3288000000000],
      [3372000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2175000000000], [2250000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) fan48Owner5Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [2565000000000]) none none
      (.next ([3510000000000, 0], [2340000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([2535000000000, -9000000000000], [2565000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([945000000000], [7440000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2565000000000],
      [7440000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2340000000000, -9000000000000],
      [5850000000000, 9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2565000000000, 0],
      [5100000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7440000000000],
      [8385000000000]) (some (3, 1, 0)) none (.terminal none none none))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_2 : ExcludedOn (model49.B 2 ++ [step49.q]) 9000000000000 (model49.caps 2)
    (model49.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [210000000000]) (some (0, 0, 1))
      (some (0, 0, 1)) (.next ([6660000000000, -9000000000000], [2775000000000, 0]) (some (0, 0, 1))
      (some (0, 3, 1)) (.next ([2565000000000], [1560000000000]) (some (0, 3, 1)) (some (0, 3, 1))
      (.next ([2535000000000, -9000000000000], [2565000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1))
      (.next ([0], [2775000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-210000000000],
      [4335000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-2775000000000, 0],
      [9435000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1560000000000],
      [4125000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2565000000000, 0],
      [5100000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2))
      (some (0, 1, 0)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_3 : ExcludedOn (model49.B 3 ++ [step49.q]) 9000000000000 (model49.caps 3)
    (model49.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_4 : ExcludedOn (model49.B 4 ++ [step49.q]) 9000000000000 (model49.caps 4)
    (model49.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_6 : ExcludedOn (model49.B 6 ++ [step49.q]) 9000000000000 (model49.caps 6)
    (model49.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_7 : ExcludedOn (model49.B 7 ++ [step49.q]) 9000000000000 (model49.caps 7)
    (model49.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_8 : ExcludedOn (model49.B 8 ++ [step49.q]) 9000000000000 (model49.caps 8)
    (model49.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Sint260000270000
end ConwaySoifer.Simplified.Certificates
