/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext150000160000
import Mathlib.Tactic.FinCases

/-!
# Sext 150000 160000 8

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
def fan64Owner3Part0 : FanWitness := (.next ([3075000000000], [600000000000]) (some (4, 0, 5)) (some
    (4, 0, 5)) (.next ([4125000000000], [2175000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([2175000000000, 0], [1350000000000, -9000000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([4875000000000], [3750000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([2175000000000],
    [2700000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([2700000000000], [4125000000000])
    (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1800000000000, 9000000000000], [3900000000000,
    -9000000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1350000000000, 9000000000000],
    [5925000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([375000000000], [1800000000000])
    (some (4, 0, 5)) (some (4, 0, 5)) (.next ([450000000000], [5250000000000]) (some (4, 0, 5))
    (some (4, 1, 5)) (.next ([0], [5925000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([-225000000000], [5475000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-375000000000],
    [3525000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-825000000000, 9000000000000],
    [6300000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-600000000000], [3675000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2175000000000], [6300000000000]) (some (0, 1, 5))
    (some (0, 2, 5)) (.next ([-1350000000000, 9000000000000], [3525000000000, -9000000000000]) (some
    (0, 2, 5)) (some (0, 2, 5)) (.next ([-3750000000000], [8625000000000]) (some (0, 2, 3)) (some
    (0, 2, 3)) (.next ([-2700000000000], [4875000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-4125000000000], [6825000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3900000000000,
    9000000000000], [5700000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5925000000000, 0],
    [7275000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1800000000000],
    [2175000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5250000000000], [5700000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2,
    3)))))))))))))))))))))))))))

theorem excluded64_1 : ExcludedOn (model64.B 1 ++ [step64.q]) 9000000000000 (model64.caps 1)
    (model64.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_2 : ExcludedOn (model64.B 2 ++ [step64.q]) 9000000000000 (model64.caps 2)
    (model64.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4425000000000], [525000000000]) (some (0, 5, 2))
      (some (0, 5, 2)) (.next ([5475000000000, 9000000000000], [825000000000, -9000000000000]) (some
      (0, 5, 2)) (some (0, 5, 2)) (.next ([2700000000000], [975000000000]) (some (0, 5, 2)) (some
      (0, 5, 2)) (.next ([4125000000000], [2175000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
      ([1350000000000], [825000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([2250000000000],
      [1875000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([3450000000000], [4200000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([750000000000, 0], [1350000000000, -9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1350000000000, 9000000000000], [3075000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([1350000000000, 9000000000000],
      [4950000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1275000000000],
      [5550000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0], [4950000000000]) (some (0, 1,
      3)) (some (0, 1, 3)) (.next ([-525000000000], [4950000000000]) (some (0, 1, 3)) (some (0, 1,
      4)) (.next ([-825000000000, 9000000000000], [6300000000000, 0]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-975000000000], [3675000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-2175000000000], [6300000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-825000000000],
      [2175000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1875000000000], [4125000000000])
      (some (0, 2, 4)) (some (5, 2, 4)) (.next ([-4200000000000], [7650000000000]) (some (5, 2, 4))
      (some (5, 2, 4)) (.next ([-1350000000000, 9000000000000], [2100000000000, -9000000000000])
      (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-3075000000000, 9000000000000], [4425000000000, 0])
      (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-4950000000000, 0], [6300000000000, 9000000000000])
      (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-5550000000000], [6825000000000]) (some (5, 2, 4))
      (some (5, 2, 4)) (.terminal (some (5, 2, 4)) (some (5, 2, 0)) (some (5, 2,
      4))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded64_3 : ExcludedOn (model64.B 3 ++ [step64.q]) 9000000000000 (model64.caps 3)
    (model64.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [225000000000]) (some (3, 0, 2))
      (some (4, 0, 2)) (.next ([3150000000000], [375000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([5475000000000, 9000000000000], [825000000000, -9000000000000]) (some (4, 0, 2)) (some
      (4, 0, 5)) fan64Owner3Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded64_4 : ExcludedOn (model64.B 4 ++ [step64.q]) 9000000000000 (model64.caps 4)
    (model64.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_5 : ExcludedOn (model64.B 5 ++ [step64.q]) 9000000000000 (model64.caps 5)
    (model64.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_6 : ExcludedOn (model64.B 6 ++ [step64.q]) 9000000000000 (model64.caps 6)
    (model64.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_7 : ExcludedOn (model64.B 7 ++ [step64.q]) 9000000000000 (model64.caps 7)
    (model64.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_8 : ExcludedOn (model64.B 8 ++ [step64.q]) 9000000000000 (model64.caps 8)
    (model64.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_9 : ExcludedOn (model64.B 9 ++ [step64.q]) 9000000000000 (model64.caps 9)
    (model64.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked64 : StepValid model64 9000000000000 step64 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded64_1
    · exact excluded64_2
    · exact excluded64_3
    · exact excluded64_4
    · exact excluded64_5
    · exact excluded64_6
    · exact excluded64_7
    · exact excluded64_8
    · exact excluded64_9
theorem next64 : model64.insert step64 = model65 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext150000160000
end ConwaySoifer.Simplified.Certificates
