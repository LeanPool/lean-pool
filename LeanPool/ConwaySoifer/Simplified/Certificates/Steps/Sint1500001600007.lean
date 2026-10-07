/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint150000160000
import Mathlib.Tactic.FinCases

/-!
# Sint 150000 160000 7

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
def fan56Owner6Part0 : FanWitness := (.next ([0, 0], [1350000000000, 9000000000000]) (some (7, 2,
    7)) (some (7, 2, 7)) (.next ([0, -9000000000000], [5100000000000, 9000000000000]) (some (7, 2,
    7)) (some (7, 3, 7)) (.next ([-150000000000], [975000000000]) (some (7, 3, 7)) (some (7, 3, 7))
    (.next ([-975000000000, -9000000000000], [5925000000000, 9000000000000]) (some (7, 3, 7)) (some
    (7, 3, 7)) (.next ([-1125000000000], [4500000000000]) (some (7, 3, 7)) (some (7, 3, 7)) (.next
    ([-2370000000000], [9375000000000]) (some (7, 3, 7)) (some (7, 3, 7)) (.next ([-2220000000000],
    [8400000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-2820000000000], [6375000000000])
    (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-2970000000000], [6150000000000]) (some (1, 3, 7))
    (some (1, 3, 7)) (.next ([-1350000000000, -9000000000000], [2700000000000, 18000000000000])
    (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-2475000000000, -9000000000000], [4500000000000])
    (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-225000000000], [375000000000]) (some (1, 3, 7))
    (some (1, 3, 7)) (.next ([-5970000000000, 9000000000000], [9750000000000]) (some (1, 3, 7))
    (some (1, 3, 7)) (.next ([-2400000000000, 9000000000000], [3750000000000, -9000000000000]) (some
    (1, 3, 7)) (some (1, 3, 7)) (.next ([-3750000000000], [5100000000000]) (some (1, 3, 7)) (some
    (1, 3, 7)) (.next ([-2250000000000], [3000000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next
    ([-7320000000000], [9750000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-2025000000000],
    [2625000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-3000000000000, 9000000000000],
    [3600000000000]) (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-3225000000000], [3825000000000])
    (some (1, 3, 7)) (some (1, 3, 7)) (.next ([-3000000000000], [3450000000000]) (some (1, 3, 7))
    (some (1, 3, 7)) (.next ([-7320000000000], [8400000000000, -9000000000000]) (some (1, 3, 7))
    (some (1, 3, 7)) (.next ([-3225000000000, 9000000000000], [3600000000000, -9000000000000]) (some
    (1, 3, 7)) (some (1, 3, 7)) (.next ([-3150000000000, 9000000000000], [3375000000000]) (some (1,
    3, 7)) (some (1, 3, 7)) (.terminal (some (1, 3, 7)) (some (1, 3, 7)) (some (1, 3,
    7)))))))))))))))))))))))))))

theorem excluded56_1 : ExcludedOn (model56.B 1 ++ [step56.q]) 9000000000000 (model56.caps 1)
    (model56.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5970000000000, -9000000000000], [600000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 2)) (.next ([4125000000000], [1500000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3375000000000, 0], [1350000000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2775000000000, -9000000000000], [1500000000000, 0])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4125000000000], [3195000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1695000000000], [3375000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([1875000000000], [5625000000000]) (some (0, 1, 2)) (some (4, 1, 2)) (.next
      ([750000000000], [6570000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [3375000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-600000000000, -9000000000000],
      [6570000000000, 0]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([-1500000000000],
      [5625000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-1350000000000, -9000000000000],
      [4725000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-1500000000000, 0],
      [4275000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-3195000000000],
      [7320000000000]) (some (4, 1, 0)) (some (4, 1, 0)) (.next ([-3375000000000], [5070000000000])
      (some (4, 1, 0)) (some (4, 1, 0)) (.next ([-5625000000000], [7500000000000]) (some (4, 1, 0))
      (some (4, 1, 0)) (.next ([-6570000000000], [7320000000000]) (some (4, 1, 0)) (some (4, 1, 0))
      (.terminal (some (4, 1, 0)) (some (4, 1, 0)) (some (4, 1, 0))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded56_2 : ExcludedOn (model56.B 2 ++ [step56.q]) 9000000000000 (model56.caps 2)
    (model56.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5970000000000, -9000000000000], [600000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([7650000000000, -9000000000000],
      [1350000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([6570000000000],
      [1680000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5220000000000, -9000000000000],
      [3030000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0],
      [1350000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-600000000000,
      -9000000000000], [6570000000000, 0]) (some (0, 3, 1)) (some (0, 3, 2)) (.next
      ([-1350000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-1680000000000], [8250000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3030000000000, -9000000000000], [8250000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded56_3 : ExcludedOn (model56.B 3 ++ [step56.q]) 9000000000000 (model56.caps 3)
    (model56.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_4 : ExcludedOn (model56.B 4 ++ [step56.q]) 9000000000000 (model56.caps 4)
    (model56.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_5 : ExcludedOn (model56.B 5 ++ [step56.q]) 9000000000000 (model56.caps 5)
    (model56.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_6 : ExcludedOn (model56.B 6 ++ [step56.q]) 9000000000000 (model56.caps 6)
    (model56.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5100000000000], [0, 9000000000000]) (some (7, 1,
      3)) (some (7, 1, 4)) (.next ([825000000000], [150000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([4950000000000], [975000000000, 9000000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([3375000000000], [1125000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([7005000000000], [2370000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([6180000000000],
      [2220000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3555000000000], [2820000000000])
      (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3180000000000], [2970000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([1350000000000, 9000000000000], [1350000000000, 9000000000000]) (some
      (7, 1, 4)) (some (7, 1, 4)) (.next ([2025000000000, -9000000000000], [2475000000000,
      9000000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([150000000000], [225000000000])
      (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3780000000000, 9000000000000], [5970000000000,
      -9000000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([1350000000000, 0], [2400000000000,
      -9000000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([1350000000000], [3750000000000])
      (some (7, 1, 4)) (some (7, 1, 4)) (.next ([750000000000], [2250000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([2430000000000], [7320000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([600000000000], [2025000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([600000000000, 9000000000000], [3000000000000, -9000000000000]) (some (7, 1, 4)) (some (7, 1,
      4)) (.next ([600000000000], [3225000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([450000000000], [3000000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([1080000000000,
      -9000000000000], [7320000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([375000000000, 0],
      [3225000000000, -9000000000000]) (some (7, 1, 4)) (some (7, 1, 7)) (.next ([225000000000,
      9000000000000], [3150000000000, -9000000000000]) (some (7, 1, 7)) (some (7, 2, 7))
      fan56Owner6Part0)))))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded56_7 : ExcludedOn (model56.B 7 ++ [step56.q]) 9000000000000 (model56.caps 7)
    (model56.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_8 : ExcludedOn (model56.B 8 ++ [step56.q]) 9000000000000 (model56.caps 8)
    (model56.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_9 : ExcludedOn (model56.B 9 ++ [step56.q]) 9000000000000 (model56.caps 9)
    (model56.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked56 : StepValid model56 9000000000000 step56 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded56_1
    · exact excluded56_2
    · exact excluded56_3
    · exact excluded56_4
    · exact excluded56_5
    · exact excluded56_6
    · exact excluded56_7
    · exact excluded56_8
    · exact excluded56_9
theorem next56 : model56.insert step56 = model57 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint150000160000
end ConwaySoifer.Simplified.Certificates
