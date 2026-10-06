/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown260000270000
import Mathlib.Tactic.FinCases

/-!
# Aown 260000 270000 3

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
namespace Aown260000270000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner2Part0 : FanWitness := (.next ([4875000000000], [1962000000000]) (some (0, 5, 2))
    (some (0, 5, 2)) (.next ([285000000000], [195000000000]) (some (0, 5, 2)) (some (0, 5, 2))
    (.next ([3030000000000], [3750000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next
    ([2535000000000], [4125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2250000000000],
    [3930000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2250000000000, 0], [4410000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([180000000000], [600000000000]) (some
    (0, 5, 4)) (some (0, 5, 4)) (.next ([285000000000, -9000000000000], [6552000000000,
    9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([0, 0], [4590000000000,
    9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-57000000000], [1845000000000]) (some
    (0, 5, 4)) (some (0, 5, 4)) (.next ([-177000000000], [2340000000000]) (some (0, 1, 4)) (some (0,
    1, 4)) (.next ([-1560000000000, -9000000000000], [8340000000000, 9000000000000]) (some (0, 1,
    4)) (some (0, 1, 4)) (.next ([-2055000000000, -9000000000000], [8715000000000, 9000000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-657000000000], [2625000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([-2340000000000, -9000000000000], [9000000000000, 0]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-2340000000000, -9000000000000], [8520000000000, 9000000000000]) (some
    (0, 2, 4)) (some (0, 2, 4)) (.next ([-1962000000000], [6837000000000]) (some (0, 2, 4)) (some
    (0, 2, 4)) (.next ([-195000000000], [480000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-3750000000000], [6780000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4125000000000],
    [6660000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3930000000000], [6180000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4410000000000, 9000000000000], [6660000000000,
    -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-600000000000], [780000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6552000000000, -9000000000000], [6837000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (5, 2, 0)) (some (5, 2,
    4)))))))))))))))))))))))))))

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4503000000000, 9000000000000], [285000000000,
      -9000000000000]) none none (.next ([2448000000000, -9000000000000], [177000000000,
      9000000000000]) none none (.next ([4788000000000], [2625000000000]) none none (.next
      ([2340000000000, 9000000000000], [2340000000000, 9000000000000]) none none (.next ([0],
      [7128000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-285000000000,
      9000000000000], [4788000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-177000000000,
      -9000000000000], [2625000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2625000000000], [7413000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2340000000000,
      -9000000000000], [4680000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal
      (some (3, 1, 2)) none none))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1788000000000], [57000000000]) (some (0, 5, 2))
      (some (0, 5, 2)) (.next ([2163000000000], [177000000000]) (some (0, 5, 2)) (some (0, 5, 2))
      (.next ([6780000000000, 0], [1560000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2))
      (.next ([6660000000000, 0], [2055000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2))
      (.next ([1968000000000], [657000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
      ([6660000000000, -9000000000000], [2340000000000, 9000000000000]) (some (0, 5, 2)) (some (0,
      5, 2)) (.next ([6180000000000, 0], [2340000000000, 9000000000000]) (some (0, 5, 2)) (some (0,
      5, 2)) fan24Owner2Part0)))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Aown260000270000
end ConwaySoifer.Simplified.Certificates
