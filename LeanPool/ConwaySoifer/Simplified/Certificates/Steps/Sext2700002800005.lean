/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext270000280000
import Mathlib.Tactic.FinCases

/-!
# Sext 270000 280000 5

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
namespace Sext270000280000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner2Part0 : FanWitness := (.next ([6570000000000], [2430000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([4179000000000, 9000000000000], [2196000000000, -9000000000000]) (some
    (0, 5, 3)) (some (0, 5, 3)) (.next ([2805000000000, 9000000000000], [1944000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2319000000000, -9000000000000],
    [2055000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2430000000000,
    9000000000000], [2430000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([4140000000000, -9000000000000], [4860000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([1821000000000], [2805000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1749000000000], [4626000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([375000000000],
    [4374000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([195000000000], [4179000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0, 9000000000000], [6570000000000, -9000000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0, 0], [2430000000000, 9000000000000]) (some (0, 5,
    3)) (some (0, 5, 3)) (.next ([-252000000000], [1626000000000]) (some (0, 5, 3)) (some (0, 5, 4))
    (.next ([-2430000000000], [9000000000000]) (some (0, 5, 4)) (some (1, 5, 4)) (.next
    ([-2196000000000, 9000000000000], [6375000000000, 0]) (some (1, 5, 4)) (some (1, 5, 4)) (.next
    ([-1944000000000, 9000000000000], [4749000000000, 0]) (some (1, 5, 4)) (some (1, 5, 4)) (.next
    ([-2055000000000, -9000000000000], [4374000000000]) (some (1, 5, 4)) (some (1, 5, 4)) (.next
    ([-2430000000000, -9000000000000], [4860000000000, 18000000000000]) (some (1, 5, 4)) (some (1,
    5, 4)) (.next ([-4860000000000, -9000000000000], [9000000000000]) (some (1, 5, 4)) (some (1, 5,
    4)) (.next ([-2805000000000], [4626000000000]) (some (1, 5, 4)) (some (1, 5, 4)) (.next
    ([-4626000000000], [6375000000000]) (some (1, 5, 4)) (some (1, 5, 4)) (.next ([-4374000000000],
    [4749000000000]) (some (1, 5, 4)) (some (1, 5, 4)) (.next ([-4179000000000], [4374000000000])
    (some (1, 5, 4)) (some (1, 5, 4)) (.next ([-6570000000000, 9000000000000], [6570000000000, 0])
    (some (1, 5, 4)) (some (5, 5, 4)) (.terminal (some (5, 3, 4)) (some (5, 3, 0)) (some (5, 3,
    4)))))))))))))))))))))))))))

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000], [300000000000, -9000000000000])
      (some (3, 4, 1)) none (.next ([2730000000000], [1215000000000]) none none (.next
      ([4140000000000, -9000000000000], [2430000000000, 9000000000000]) none none (.next
      ([2430000000000, 9000000000000], [2430000000000, 9000000000000]) none none (.next
      ([2625000000000], [2730000000000]) none none (.next ([2430000000000, 9000000000000],
      [4140000000000, -9000000000000]) none none (.next ([195000000000, -9000000000000],
      [5160000000000, 9000000000000]) none none (.next ([0], [2430000000000, 9000000000000]) (some
      (4, 0, 2)) (some (4, 0, 2)) (.next ([-300000000000, 9000000000000], [2925000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 3)) (.next ([-1215000000000], [3945000000000])
      (some (4, 0, 3)) (some (4, 1, 3)) (.next ([-2430000000000, -9000000000000], [6570000000000,
      0]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2430000000000, -9000000000000],
      [4860000000000, 18000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2730000000000],
      [5355000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-4140000000000, 9000000000000],
      [6570000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-5160000000000, -9000000000000],
      [5355000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1,
      3)) (some (4, 1, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1374000000000], [252000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) fan40Owner2Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4860000000000, 9000000000000], [4140000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2430000000000, 9000000000000],
      [4140000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2430000000000,
      9000000000000], [6570000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([2430000000000], [6570000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [2430000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-4140000000000,
      9000000000000], [9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-4140000000000,
      9000000000000], [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6570000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next
      ([-6570000000000], [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Sext270000280000
end ConwaySoifer.Simplified.Certificates
