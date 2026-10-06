/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext170000180000
import Mathlib.Tactic.FinCases

/-!
# Sext 170000 180000 5

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
namespace Sext170000180000

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5760000000000], [3486000000000]) (some (4, 0,
      1)) (some (4, 0, 2)) (.next ([1530000000000, 9000000000000], [1530000000000, 9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1635000000000], [2595000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1635000000000], [4125000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([1530000000000, 9000000000000], [5121000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([105000000000, -9000000000000], [5655000000000, 9000000000000]) (some
      (4, 0, 2)) (some (4, 0, 2)) (.next ([0], [1530000000000, 9000000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([-3486000000000], [9246000000000]) (some (4, 0, 2)) none (.next
      ([-1530000000000, -9000000000000], [3060000000000, 18000000000000]) none none (.next
      ([-2595000000000, 9000000000000], [4230000000000, -9000000000000]) none none (.next
      ([-4125000000000], [5760000000000]) (some (0, 0, 4)) (some (0, 1, 4)) (.next
      ([-5121000000000], [6651000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-5655000000000, -9000000000000], [5760000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4590000000000], [90000000000]) (some (0, 0, 4))
      (some (0, 0, 4)) (.next ([4320000000000], [711000000000]) (some (0, 0, 4)) (some (0, 1, 4))
      (.next ([3879000000000], [5121000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1971000000000, 9000000000000], [3060000000000, -9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([1530000000000, 9000000000000], [5121000000000, 0]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([441000000000], [4590000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [5121000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-90000000000], [4680000000000])
      (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-711000000000], [5031000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-5121000000000], [9000000000000]) (some (0, 1, 3)) (some (0, 4, 3))
      (.next ([-3060000000000, 9000000000000], [5031000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-5121000000000, 0], [6651000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-4590000000000], [5031000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some
      (0, 4, 3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5121000000000], [2349000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([5121000000000], [3879000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([2616000000000], [3009000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([1530000000000, 9000000000000], [2100000000000, -9000000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([1746000000000], [2754000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([1491000000000], [3879000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([621000000000], [4095000000000, -9000000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([621000000000], [5625000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0],
      [3630000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2349000000000, 9000000000000],
      [7470000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-3879000000000],
      [9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-3009000000000], [5625000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2100000000000, 9000000000000], [3630000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2754000000000], [4500000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-3879000000000], [5370000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-4095000000000, 9000000000000], [4716000000000, -9000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-5625000000000], [6246000000000]) (some (4, 1, 3)) (some (4, 2, 3))
      (.terminal (some (4, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_9 : ExcludedOn (model40.B 9 ++ [step40.q]) 9000000000000 (model40.caps 9)
    (model40.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked40 : StepValid model40 9000000000000 step40 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded40_1
    · exact excluded40_2
    · exact excluded40_3
    · exact excluded40_4
    · exact excluded40_5
    · exact excluded40_6
    · exact excluded40_7
    · exact excluded40_8
    · exact excluded40_9
theorem next40 : model40.insert step40 = model41 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext170000180000
end ConwaySoifer.Simplified.Certificates
