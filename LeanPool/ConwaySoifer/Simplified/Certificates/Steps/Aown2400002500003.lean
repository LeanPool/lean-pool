/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown240000250000
import Mathlib.Tactic.FinCases

/-!
# Aown 240000 250000 3

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
namespace Aown240000250000

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5760000000000], [375000000000]) (some (4, 0, 1))
      (some (4, 0, 2)) (.next ([5160000000000, 9000000000000], [1728000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([3000000000000], [3888000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([135000000000], [240000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([2160000000000, 9000000000000], [6000000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([1785000000000, 9000000000000], [6135000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([753000000000], [2760000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0],
      [2160000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-375000000000],
      [6135000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-1728000000000, 9000000000000],
      [6888000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-3888000000000], [6888000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-240000000000], [375000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-6000000000000, 0], [8160000000000, 9000000000000]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([-6135000000000, 0], [7920000000000, 9000000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-2760000000000], [3513000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.terminal (some (0, 1, 3)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_8 : ExcludedOn (model24.B 8 ++ [step24.q]) 9000000000000 (model24.caps 8)
    (model24.ord 8) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded24_1
    · exact excluded24_2
    · exact excluded24_3
    · exact excluded24_4
    · exact excluded24_5
    · exact excluded24_6
    · exact excluded24_7
    · exact excluded24_8
    · exact excluded24_9
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3135000000000, 9000000000000], [465000000000,
      -9000000000000]) none none (.next ([1440000000000, 0], [345000000000, 9000000000000]) none
      none (.next ([1440000000000, -9000000000000], [1185000000000, 9000000000000]) none none (.next
      ([2160000000000, 9000000000000], [2160000000000, 9000000000000]) none none (.next
      ([3600000000000], [3840000000000]) none none (.next ([2160000000000, 9000000000000],
      [2655000000000, -9000000000000]) none none (.next ([600000000000], [1185000000000]) none none
      (.next ([720000000000, 9000000000000], [1815000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([0], [6975000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-465000000000, 9000000000000], [3600000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-345000000000, -9000000000000], [1785000000000, 9000000000000]) (some (4, 2, 3)) (some (4,
      2, 3)) (.next ([-1185000000000, -9000000000000], [2625000000000, 0]) (some (4, 2, 3)) (some
      (4, 2, 3)) (.next ([-2160000000000, -9000000000000], [4320000000000, 18000000000000]) (some
      (4, 2, 3)) (some (4, 2, 3)) (.next ([-3840000000000], [7440000000000]) (some (4, 2, 3)) (some
      (4, 2, 3)) (.next ([-2655000000000, 9000000000000], [4815000000000, 0]) (some (4, 2, 3)) (some
      (4, 2, 3)) (.next ([-1185000000000], [1785000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-1815000000000], [2535000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.terminal (some (4, 2, 3)) none none))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([360000000000, -9000000000000], [15000000000,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next ([435000000000, -9000000000000],
      [285000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1080000000000],
      [1275000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2370000000000], [4755000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2025000000000], [4830000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([1920000000000], [4830000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([1650000000000, 0], [5190000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 4))
      (.next ([75000000000], [270000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([75000000000], [375000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([465000000000,
      -9000000000000], [7560000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([0,
      0], [3810000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-15000000000,
      -9000000000000], [375000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-285000000000,
      -9000000000000], [720000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-1275000000000], [2355000000000]) (some (0, 5, 4)) (some (0, 1, 4)) (.next
      ([-4755000000000], [7125000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-4830000000000], [6855000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-4830000000000], [6750000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-5190000000000,
      9000000000000], [6840000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-270000000000], [345000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-375000000000],
      [450000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-7560000000000, -9000000000000],
      [8025000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (5, 2,
      0)) (some (5, 2, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded25_1
    · exact excluded25_2
    · exact excluded25_3
    · exact excluded25_4
    · exact excluded25_5
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown240000250000
end ConwaySoifer.Simplified.Certificates
