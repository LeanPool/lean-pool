/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Across117500122500
import Mathlib.Tactic.FinCases

/-!
# Across 117500 122500 0

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
namespace Across117500122500

theorem excluded0_1 : ExcludedOn (model0.B 1 ++ [step0.q]) 9000000000000 (model0.caps 1) (model0.ord
    1) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7942500000000], [750000000000]) (some (3, 1, 1))
      (some (3, 1, 2)) (.next ([6885000000000, -9000000000000], [750000000000, 0]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1057500000000, 9000000000000], [1057500000000, 9000000000000]) (some
      (3, 1, 2)) (some (3, 1, 2)) (.next ([307500000000, 9000000000000], [8692500000000]) (some (3,
      1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1057500000000, 9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.next ([-750000000000], [8692500000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-750000000000, 0], [7635000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-1057500000000, -9000000000000], [2115000000000, 18000000000000]) (some (3, 1, 0)) (some (3,
      1, 3)) (.next ([-8692500000000], [9000000000000, 9000000000000]) (some (3, 1, 3)) none
      (.terminal none (some (1, 1, 3)) none))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded0_2 : ExcludedOn (model0.B 2 ++ [step0.q]) 9000000000000 (model0.caps 2) (model0.ord
    2) 0 1 200 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6885000000000, -9000000000000], [750000000000,
      0]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([7942500000000, -9000000000000], [1057500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([1057500000000, 0], [307500000000,
      9000000000000]) (some (0, 0, 2)) (some (0, 0, 2)) (.next ([750000000000], [307500000000])
      (some (0, 0, 2)) (some (0, 4, 2)) (.next ([1057500000000, 9000000000000], [1057500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4500000000000, 0], [5557500000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3442500000000, -9000000000000],
      [4500000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3442500000000],
      [5250000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1057500000000, 9000000000000],
      [3442500000000, -9000000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([0, 9000000000000],
      [750000000000, 0]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([0, 0], [1057500000000,
      9000000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([-750000000000, 0], [7635000000000,
      -9000000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([-1057500000000, -9000000000000],
      [9000000000000, 0]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([-307500000000, -9000000000000],
      [1365000000000, 9000000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([-307500000000],
      [1057500000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([-1057500000000, -9000000000000],
      [2115000000000, 18000000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([-5557500000000,
      -9000000000000], [10057500000000, 9000000000000]) (some (0, 2, 2)) (some (0, 2, 3)) (.next
      ([-4500000000000, 0], [7942500000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.next ([-5250000000000], [8692500000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3442500000000, 9000000000000], [4500000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-750000000000, 0], [750000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.terminal (some (0, 2, 3)) (some (0, 2, 0)) (some (0, 2, 3))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 200 (by decide +kernel)
  decide +kernel

theorem excluded0_3 : ExcludedOn (model0.B 3 ++ [step0.q]) 9000000000000 (model0.caps 3) (model0.ord
    3) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_4 : ExcludedOn (model0.B 4 ++ [step0.q]) 9000000000000 (model0.caps 4) (model0.ord
    4) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_5 : ExcludedOn (model0.B 5 ++ [step0.q]) 9000000000000 (model0.caps 5) (model0.ord
    5) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_6 : ExcludedOn (model0.B 6 ++ [step0.q]) 9000000000000 (model0.caps 6) (model0.ord
    6) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_7 : ExcludedOn (model0.B 7 ++ [step0.q]) 9000000000000 (model0.caps 7) (model0.ord
    7) 0 1 200 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_8 : ExcludedOn (model0.B 8 ++ [step0.q]) 9000000000000 (model0.caps 8) (model0.ord
    8) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem excluded0_9 : ExcludedOn (model0.B 9 ++ [step0.q]) 9000000000000 (model0.caps 9) (model0.ord
    9) 0 1 200 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      200 (by decide +kernel)
  decide +kernel

theorem checked0 : StepValid model0 9000000000000 step0 0 1 200 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded0_1
    · exact excluded0_2
    · exact excluded0_3
    · exact excluded0_4
    · exact excluded0_5
    · exact excluded0_6
    · exact excluded0_7
    · exact excluded0_8
    · exact excluded0_9
theorem next0 : model0.insert step0 = model1 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Across117500122500
end ConwaySoifer.Simplified.Certificates
