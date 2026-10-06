/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown110000120000
import Mathlib.Tactic.FinCases

/-!
# Aown 110000 120000 2

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
namespace Aown110000120000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner3Part0 : FanWitness := (.next ([7140000000000], [990000000000, 9000000000000]) (some
    (4, 5, 2)) (some (4, 5, 2)) (.next ([7230000000000], [1110000000000]) (some (4, 5, 2)) (some (4,
    5, 2)) (.next ([6840000000000], [1080000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([6810000000000], [1500000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1170000000000],
    [330000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([960000000000], [360000000000]) (some
    (4, 1, 2)) (some (4, 1, 2)) (.next ([180000000000, -9000000000000], [330000000000]) (some (4, 1,
    2)) (some (4, 1, 3)) (.next ([1320000000000], [6180000000000]) (some (4, 1, 3)) (some (4, 1, 3))
    (.next ([330000000000, -9000000000000], [7170000000000, 9000000000000]) (some (4, 1, 3)) (some
    (4, 1, 3)) (.next ([90000000000], [8250000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([0], [990000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-180000000000],
    [7350000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-750000000000], [7020000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-900000000000, -9000000000000], [8250000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-990000000000, -9000000000000], [8130000000000,
    9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1110000000000], [8340000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1080000000000], [7920000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-1500000000000], [8310000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-330000000000], [1500000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-360000000000], [1320000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-330000000000],
    [510000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6180000000000],
    [7500000000000]) (some (0, 1, 3)) (some (5, 1, 3)) (.next ([-7170000000000, -9000000000000],
    [7500000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-8250000000000], [8340000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.terminal (some (5, 1, 3)) (some (5, 1, 3)) (some (5, 1,
    3)))))))))))))))))))))))))))

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7170000000000], [180000000000]) (some (3, 5, 1))
      (some (4, 5, 1)) (.next ([6270000000000], [750000000000]) (some (4, 5, 1)) (some (4, 5, 1))
      (.next ([7350000000000, -9000000000000], [900000000000, 9000000000000]) (some (4, 5, 1)) (some
      (4, 5, 2)) fan16Owner3Part0)))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8250000000000], [90000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([7410000000000], [510000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([7830000000000, 0], [660000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([7260000000000, -9000000000000], [1080000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([990000000000, 9000000000000], [990000000000, 9000000000000]) (some
      (4, 1, 2)) (some (4, 1, 2)) (.next ([900000000000, 9000000000000], [7350000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([330000000000], [6510000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([330000000000], [7500000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [990000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-90000000000], [8340000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-510000000000], [7920000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-660000000000, -9000000000000], [8490000000000, 9000000000000]) (some (0, 1, 2)) (some (0,
      1, 4)) (.next ([-1080000000000, -9000000000000], [8340000000000, 0]) (some (0, 1, 4)) (some
      (0, 1, 4)) (.next ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (0,
      1, 4)) (some (0, 2, 4)) (.next ([-7350000000000, 9000000000000], [8250000000000]) (some (0, 2,
      4)) (some (0, 2, 4)) (.next ([-6510000000000, 9000000000000], [6840000000000, -9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-7500000000000], [7830000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
      4))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6090000000000, -9000000000000], [990000000000,
      9000000000000]) (some (0, 0, 3)) (some (0, 1, 3)) (.next ([1500000000000], [750000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1500000000000], [7830000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([510000000000, -9000000000000], [7830000000000, 0]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([0, 0], [990000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 3,
      3)) (.next ([-990000000000, -9000000000000], [7080000000000, 0]) (some (0, 3, 3)) (some (0, 3,
      3)) (.next ([-750000000000], [2250000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next
      ([-7830000000000], [9330000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-7830000000000,
      0], [8340000000000, -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some (0, 3,
      2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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

end Aown110000120000
end ConwaySoifer.Simplified.Certificates
