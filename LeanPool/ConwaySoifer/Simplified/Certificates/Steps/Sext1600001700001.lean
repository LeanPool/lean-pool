/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext160000170000
import Mathlib.Tactic.FinCases

/-!
# Sext 160000 170000 1

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
namespace Sext160000170000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan8Owner0Part0 : FanWitness := (.next ([375000000000], [6270000000000]) (some (0, 8, 3)) (some
    (0, 8, 3)) (.next ([23400000000, 2490000000000], [1253400000000, 2490000000000]) (some (0, 8,
    3)) (some (0, 8, 4)) (.next ([0], [660000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([-81600000000, 2490000000000], [7148400000000, 2490000000000]) (some (0, 8, 4)) (some (0, 8,
    4)) (.next ([-480000000000], [7410000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([-878400000000, -2490000000000], [7546800000000, 4980000000000]) (some (0, 8, 4)) (some (0, 8,
    4)) (.next ([-1140000000000], [7410000000000]) (some (0, 8, 4)) (some (0, 8, 4)) (.next
    ([-1276800000000, -4980000000000], [7148400000000, 2490000000000]) (some (0, 8, 4)) (some (0, 8,
    4)) (.next ([-261600000000, 2490000000000], [1058400000000, 2490000000000]) (some (0, 8, 4))
    (some (0, 8, 4)) (.next ([-375000000000], [1515000000000]) (some (0, 8, 4)) (some (0, 8, 4))
    (.next ([-136800000000, -4980000000000], [398400000000, 2490000000000]) (some (0, 8, 4)) (some
    (0, 8, 4)) (.next ([-4050000000000], [8655000000000]) (some (0, 8, 4)) (some (1, 8, 5)) (.next
    ([-773400000000, -2490000000000], [1651800000000, 4980000000000]) (some (1, 8, 5)) (some (1, 8,
    5)) (.next ([-2010000000000], [4230000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next
    ([-456600000000, 2490000000000], [878400000000, 2490000000000]) (some (1, 3, 5)) (some (1, 3,
    5)) (.next ([-4928400000000, -2490000000000], [9076800000000, 4980000000000]) (some (1, 3, 5))
    (some (1, 3, 5)) (.next ([-5190000000000], [8940000000000]) (some (1, 3, 5)) (some (1, 3, 5))
    (.next ([-5326800000000, -4980000000000], [8678400000000, 2490000000000]) (some (1, 3, 5)) (some
    (1, 3, 5)) (.next ([-5190000000000], [8280000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
    ([-1058400000000, -2490000000000], [1456800000000, 4980000000000]) (some (1, 3, 5)) (some (8, 3,
    6)) (.next ([-855000000000], [1140000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-796800000000, -4980000000000], [1058400000000, 2490000000000]) (some (8, 3, 6)) (some (8, 3,
    6)) (.next ([-6270000000000], [6645000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-1253400000000, -2490000000000], [1276800000000, 4980000000000]) (some (8, 3, 6)) (some (8, 3,
    6)) (.terminal (some (8, 3, 6)) (some (8, 3, 6)) (some (8, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan9Owner0Part0 : FanWitness := (.next ([23400000000, 2490000000000], [1253400000000,
    2490000000000]) (some (0, 8, 3)) (some (0, 8, 4)) (.next ([0], [660000000000]) (some (0, 8, 4))
    (some (0, 8, 4)) (.next ([-81600000000, 2490000000000], [7148400000000, 2490000000000]) (some
    (0, 8, 4)) (some (0, 8, 4)) (.next ([-480000000000], [7410000000000]) (some (0, 8, 4)) (some (0,
    8, 4)) (.next ([-878400000000, -2490000000000], [7546800000000, 4980000000000]) (some (0, 8, 4))
    (some (0, 8, 4)) (.next ([-1140000000000], [7410000000000]) (some (0, 8, 4)) (some (0, 8, 4))
    (.next ([-1276800000000, -4980000000000], [7148400000000, 2490000000000]) (some (0, 8, 4)) (some
    (0, 8, 4)) (.next ([-261600000000, 2490000000000], [1058400000000, 2490000000000]) (some (0, 8,
    4)) (some (0, 8, 4)) (.next ([-375000000000], [1515000000000]) (some (0, 8, 4)) (some (0, 8, 4))
    (.next ([-136800000000, -4980000000000], [398400000000, 2490000000000]) (some (0, 8, 4)) (some
    (0, 8, 4)) (.next ([-773400000000, -2490000000000], [1651800000000, 4980000000000]) (some (0, 8,
    4)) (some (1, 8, 5)) (.next ([-456600000000, 2490000000000], [878400000000, 2490000000000])
    (some (1, 8, 5)) (some (1, 8, 5)) (.next ([-261600000000, 2490000000000], [398400000000,
    2490000000000]) (some (1, 8, 5)) (some (1, 8, 5)) (.next ([-6465000000000], [9660000000000])
    (some (1, 8, 5)) (some (2, 8, 6)) (.next ([-6863400000000, -2490000000000], [9796800000000,
    4980000000000]) (some (2, 8, 6)) (some (2, 8, 6)) (.next ([-1058400000000, -2490000000000],
    [1456800000000, 4980000000000]) (some (2, 8, 6)) (some (2, 8, 6)) (.next ([-7125000000000],
    [9660000000000]) (some (2, 8, 6)) (some (2, 8, 6)) (.next ([-855000000000], [1140000000000])
    (some (2, 8, 6)) (some (2, 8, 6)) (.next ([-796800000000, -4980000000000], [1058400000000,
    2490000000000]) (some (2, 8, 6)) (some (2, 8, 6)) (.next ([-7125000000000], [9000000000000])
    (some (2, 8, 6)) (some (2, 8, 6)) (.next ([-6863400000000, -2490000000000], [8601600000000,
    -2490000000000]) (some (2, 8, 6)) (some (2, 8, 6)) (.next ([-2730000000000], [3015000000000])
    (some (2, 8, 6)) (some (8, 8, 6)) (.next ([-6270000000000], [6645000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([-1253400000000, -2490000000000], [1276800000000, 4980000000000]) (some
    (8, 3, 6)) (some (8, 3, 6)) (.terminal (some (8, 3, 6)) (some (8, 3, 6)) (some (8, 3,
    6)))))))))))))))))))))))))))

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7066800000000, 4980000000000], [81600000000,
      -2490000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([6930000000000], [480000000000])
      (some (6, 8, 3)) (some (6, 8, 3)) (.next ([6668400000000, 2490000000000], [878400000000,
      2490000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([6270000000000], [1140000000000])
      (some (6, 8, 3)) (some (6, 8, 3)) (.next ([5871600000000, -2490000000000], [1276800000000,
      4980000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([796800000000, 4980000000000],
      [261600000000, -2490000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([1140000000000],
      [375000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([261600000000, -2490000000000],
      [136800000000, 4980000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([4605000000000],
      [4050000000000]) (some (6, 8, 3)) (some (7, 8, 3)) (.next ([878400000000, 2490000000000],
      [773400000000, 2490000000000]) (some (7, 8, 3)) (some (7, 8, 3)) (.next ([2220000000000],
      [2010000000000]) (some (7, 8, 3)) (some (7, 8, 3)) (.next ([421800000000, 4980000000000],
      [456600000000, -2490000000000]) (some (7, 8, 3)) (some (7, 8, 3)) (.next ([4148400000000,
      2490000000000], [4928400000000, 2490000000000]) (some (7, 8, 3)) (some (7, 8, 3)) (.next
      ([3750000000000], [5190000000000]) (some (7, 8, 3)) (some (7, 8, 3)) (.next ([3351600000000,
      -2490000000000], [5326800000000, 4980000000000]) (some (7, 8, 3)) (some (7, 8, 3)) (.next
      ([3090000000000], [5190000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next ([398400000000,
      2490000000000], [1058400000000, 2490000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next
      ([285000000000], [855000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next ([261600000000,
      -2490000000000], [796800000000, 4980000000000]) (some (0, 8, 3)) (some (0, 8, 3))
      fan8Owner0Part0)))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_4 : ExcludedOn (model8.B 4 ++ [step8.q]) 9000000000000 (model8.caps 4) (model8.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_8 : ExcludedOn (model8.B 8 ++ [step8.q]) 9000000000000 (model8.caps 8) (model8.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_9 : ExcludedOn (model8.B 9 ++ [step8.q]) 9000000000000 (model8.caps 9) (model8.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7665000000000], [375000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([375000000000], [75000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5250000000000, 0], [3030000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5250000000000], [4470000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1680000000000], [2415000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1605000000000],
      [2865000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1440000000000, 9000000000000],
      [6675000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1065000000000,
      9000000000000], [6600000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0,
      0], [1440000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-375000000000],
      [8040000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-75000000000], [450000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-3030000000000, 9000000000000], [8280000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-4470000000000], [9720000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2415000000000], [4095000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-2865000000000], [4470000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-6675000000000, 9000000000000], [8115000000000, 0]) (some (0, 1, 2)) (some (0, 1, 4))
      (.next ([-6600000000000, 9000000000000], [7665000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked8 : StepValid model8 9000000000000 step8 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded8_0
    · exact excluded8_1
    · exact excluded8_2
    · exact excluded8_3
    · exact excluded8_4
    · exact (hj rfl).elim
    · exact excluded8_6
    · exact excluded8_7
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_0 : ExcludedOn (model9.B 0 ++ [step9.q]) 9000000000000 (model9.caps 0) (model9.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7066800000000, 4980000000000], [81600000000,
      -2490000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([6930000000000], [480000000000])
      (some (6, 8, 3)) (some (6, 8, 3)) (.next ([6668400000000, 2490000000000], [878400000000,
      2490000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([6270000000000], [1140000000000])
      (some (6, 8, 3)) (some (6, 8, 3)) (.next ([5871600000000, -2490000000000], [1276800000000,
      4980000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([796800000000, 4980000000000],
      [261600000000, -2490000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([1140000000000],
      [375000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([261600000000, -2490000000000],
      [136800000000, 4980000000000]) (some (6, 8, 3)) (some (6, 8, 3)) (.next ([878400000000,
      2490000000000], [773400000000, 2490000000000]) (some (6, 8, 3)) (some (7, 8, 3)) (.next
      ([421800000000, 4980000000000], [456600000000, -2490000000000]) (some (7, 8, 3)) (some (7, 8,
      3)) (.next ([136800000000, 4980000000000], [261600000000, -2490000000000]) (some (7, 8, 3))
      (some (7, 8, 3)) (.next ([3195000000000], [6465000000000]) (some (0, 8, 3)) (some (0, 8, 3))
      (.next ([2933400000000, 2490000000000], [6863400000000, 2490000000000]) (some (0, 8, 3)) (some
      (0, 8, 3)) (.next ([398400000000, 2490000000000], [1058400000000, 2490000000000]) (some (0, 8,
      3)) (some (0, 8, 3)) (.next ([2535000000000], [7125000000000]) (some (0, 8, 3)) (some (0, 8,
      3)) (.next ([285000000000], [855000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next
      ([261600000000, -2490000000000], [796800000000, 4980000000000]) (some (0, 8, 3)) (some (0, 8,
      3)) (.next ([1875000000000], [7125000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next
      ([1738200000000, -4980000000000], [6863400000000, 2490000000000]) (some (0, 8, 3)) (some (0,
      8, 3)) (.next ([285000000000], [2730000000000]) (some (0, 8, 3)) (some (0, 8, 3)) (.next
      ([375000000000], [6270000000000]) (some (0, 8, 3)) (some (0, 8, 3))
      fan9Owner0Part0)))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_8 : ExcludedOn (model9.B 8 ++ [step9.q]) 9000000000000 (model9.caps 8) (model9.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_9 : ExcludedOn (model9.B 9 ++ [step9.q]) 9000000000000 (model9.caps 9) (model9.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7665000000000], [375000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([6465000000000, 0], [1095000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([375000000000], [75000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([6465000000000], [2535000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([960000000000], [1200000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([885000000000],
      [1650000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1440000000000, 9000000000000],
      [6675000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1065000000000,
      9000000000000], [6600000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0,
      0], [1440000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-375000000000],
      [8040000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1095000000000, 9000000000000],
      [7560000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-75000000000],
      [450000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2535000000000], [9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1200000000000], [2160000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1650000000000], [2535000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-6675000000000, 9000000000000], [8115000000000, 0]) (some (0, 1, 2)) (some (0, 1, 4))
      (.next ([-6600000000000, 9000000000000], [7665000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked9 : StepValid model9 9000000000000 step9 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded9_0
    · exact excluded9_1
    · exact excluded9_2
    · exact excluded9_3
    · exact excluded9_4
    · exact (hj rfl).elim
    · exact excluded9_6
    · exact excluded9_7
    · exact excluded9_8
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_0 : ExcludedOn (model10.B 0 ++ [step10.q]) 9000000000000 (model10.caps 0)
    (model10.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_9 : ExcludedOn (model10.B 9 ++ [step10.q]) 9000000000000 (model10.caps 9)
    (model10.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked10 : StepValid model10 9000000000000 step10 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded10_0
    · exact excluded10_1
    · exact excluded10_2
    · exact excluded10_3
    · exact (hj rfl).elim
    · exact excluded10_5
    · exact excluded10_6
    · exact excluded10_7
    · exact excluded10_8
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_0 : ExcludedOn (model11.B 0 ++ [step11.q]) 9000000000000 (model11.caps 0)
    (model11.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_3 : ExcludedOn (model11.B 3 ++ [step11.q]) 9000000000000 (model11.caps 3)
    (model11.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1440000000000], [0, 9000000000000]) (some (2, 4,
      4)) (some (3, 4, 4)) (.next ([5760000000000, 9000000000000], [3810000000000, -9000000000000])
      (some (3, 4, 4)) (some (3, 4, 4)) (.next ([4320000000000], [3810000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) (some
      (3, 4, 2)) (some (3, 4, 2)) (.next ([4320000000000], [5250000000000]) (some (3, 4, 2)) (some
      (3, 4, 2)) (.next ([2880000000000, -9000000000000], [5250000000000]) (some (3, 4, 2)) (some
      (3, 4, 2)) (.next ([0, 9000000000000], [1440000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([0], [1440000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0,
      -9000000000000], [1440000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-3810000000000, 9000000000000], [9570000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-3810000000000], [8130000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1440000000000,
      -9000000000000], [2880000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-5250000000000], [9570000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-5250000000000], [8130000000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1440000000000, 0], [1440000000000, 9000000000000]) (some (0, 4, 2)) (some (4, 4, 2))
      (.terminal (some (4, 4, 2)) (some (4, 4, 2)) (some (4, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_8 : ExcludedOn (model11.B 8 ++ [step11.q]) 9000000000000 (model11.caps 8)
    (model11.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_9 : ExcludedOn (model11.B 9 ++ [step11.q]) 9000000000000 (model11.caps 9)
    (model11.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked11 : StepValid model11 9000000000000 step11 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded11_0
    · exact excluded11_1
    · exact excluded11_2
    · exact excluded11_3
    · exact (hj rfl).elim
    · exact excluded11_5
    · exact excluded11_6
    · exact excluded11_7
    · exact excluded11_8
    · exact excluded11_9
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [3270000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([5250000000000], [4710000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) (some
      (0, 3, 2)) (some (0, 3, 2)) (.next ([3810000000000, -9000000000000], [6150000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1440000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-3270000000000, 9000000000000],
      [8520000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-4710000000000],
      [9960000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1440000000000, -9000000000000],
      [2880000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-6150000000000,
      -9000000000000], [9960000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_3 : ExcludedOn (model12.B 3 ++ [step12.q]) 9000000000000 (model12.caps 3)
    (model12.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_4 : ExcludedOn (model12.B 4 ++ [step12.q]) 9000000000000 (model12.caps 4)
    (model12.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4530000000000], [720000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([2790000000000], [780000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5190000000000, 9000000000000], [2850000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([3750000000000], [4290000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([720000000000], [1215000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([1575000000000], [2715000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1440000000000,
      9000000000000], [6465000000000, 0]) (some (0, 1, 2)) (some (0, 1, 4)) (.next ([720000000000,
      9000000000000], [5250000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0, 0],
      [1440000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-720000000000],
      [5250000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-780000000000], [3570000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2850000000000, 9000000000000], [8040000000000, 0])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4290000000000], [8040000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1215000000000], [1935000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-2715000000000], [4290000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6465000000000, 0], [7905000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-5250000000000, 0], [5970000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4290000000000], [960000000000]) (some (2, 0, 1))
      (some (2, 0, 2)) (.next ([5250000000000], [3270000000000, -9000000000000]) (some (2, 0, 2))
      (some (2, 0, 2)) (.next ([1440000000000, 9000000000000], [7560000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([480000000000, 9000000000000], [3810000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1440000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-960000000000], [5250000000000])
      (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3270000000000, 9000000000000], [8520000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-7560000000000, 9000000000000],
      [9000000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3810000000000, 9000000000000],
      [4290000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_8 : ExcludedOn (model12.B 8 ++ [step12.q]) 9000000000000 (model12.caps 8)
    (model12.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_9 : ExcludedOn (model12.B 9 ++ [step12.q]) 9000000000000 (model12.caps 9)
    (model12.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked12 : StepValid model12 9000000000000 step12 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded12_1
    · exact excluded12_2
    · exact excluded12_3
    · exact excluded12_4
    · exact excluded12_5
    · exact excluded12_6
    · exact excluded12_7
    · exact excluded12_8
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_0 : ExcludedOn (model13.B 0 ++ [step13.q]) 9000000000000 (model13.caps 0)
    (model13.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_3 : ExcludedOn (model13.B 3 ++ [step13.q]) 9000000000000 (model13.caps 3)
    (model13.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2325000000000, -9000000000000], [1440000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([4335000000000], [4680000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2010000000000, 9000000000000], [3240000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1440000000000, 9000000000000],
      [5175000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([570000000000], [4680000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([75000000000], [4605000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([0], [5175000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-1440000000000, -9000000000000], [3765000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-4680000000000], [9015000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-3240000000000,
      9000000000000], [5250000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next ([-5175000000000],
      [6615000000000, 9000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-4680000000000],
      [5250000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-4605000000000], [4680000000000])
      (some (4, 1, 4)) (some (4, 1, 4)) (.terminal (some (4, 1, 4)) (some (0, 2, 4)) (some (4, 2,
      4))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_6 : ExcludedOn (model13.B 6 ++ [step13.q]) 9000000000000 (model13.caps 6)
    (model13.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_7 : ExcludedOn (model13.B 7 ++ [step13.q]) 9000000000000 (model13.caps 7)
    (model13.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_9 : ExcludedOn (model13.B 9 ++ [step13.q]) 9000000000000 (model13.caps 9)
    (model13.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked13 : StepValid model13 9000000000000 step13 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded13_0
    · exact excluded13_1
    · exact excluded13_2
    · exact excluded13_3
    · exact excluded13_4
    · exact excluded13_5
    · exact excluded13_6
    · exact excluded13_7
    · exact (hj rfl).elim
    · exact excluded13_9
theorem next13 : model13.insert step13 = model14 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded14_0 : ExcludedOn (model14.B 0 ++ [step14.q]) 9000000000000 (model14.caps 0)
    (model14.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_3 : ExcludedOn (model14.B 3 ++ [step14.q]) 9000000000000 (model14.caps 3)
    (model14.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1440000000000], [0, 9000000000000]) (some (2, 4,
      2)) (some (3, 4, 2)) (.next ([5040000000000], [3735000000000]) (some (3, 4, 2)) (some (3, 4,
      2)) (.next ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([5040000000000, 9000000000000], [5175000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([3600000000000], [3735000000000, -9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([3600000000000], [5175000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([0, 9000000000000], [1440000000000]) (some (3, 4, 2)) (some (4, 4, 2)) (.next ([0],
      [1440000000000, 9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([0, -9000000000000],
      [1440000000000, 9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-3735000000000],
      [8775000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-1440000000000, -9000000000000],
      [2880000000000, 18000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-5175000000000,
      0], [10215000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-3735000000000, 9000000000000], [7335000000000, -9000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([-5175000000000], [8775000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-1440000000000, 0], [1440000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.terminal (some (4, 1, 2)) (some (4, 2, 2)) (some (4, 2, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2385000000000, -9000000000000], [1215000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([4395000000000], [4455000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2010000000000, 9000000000000], [3240000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1440000000000, 9000000000000],
      [5175000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([570000000000], [4680000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([225000000000], [3600000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([225000000000], [8775000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([75000000000], [4605000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [5175000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1215000000000, -9000000000000],
      [3600000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-4455000000000], [8850000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-3240000000000, 9000000000000], [5250000000000])
      (some (4, 1, 2)) (some (4, 1, 4)) (.next ([-5175000000000], [6615000000000, 9000000000000])
      (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-4680000000000], [5250000000000]) (some (4, 1, 4))
      (some (4, 1, 4)) (.next ([-3600000000000], [3825000000000]) (some (4, 1, 4)) (some (4, 1, 4))
      (.next ([-8775000000000], [9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-4605000000000], [4680000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_7 : ExcludedOn (model14.B 7 ++ [step14.q]) 9000000000000 (model14.caps 7)
    (model14.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_9 : ExcludedOn (model14.B 9 ++ [step14.q]) 9000000000000 (model14.caps 9)
    (model14.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked14 : StepValid model14 9000000000000 step14 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded14_0
    · exact excluded14_1
    · exact excluded14_2
    · exact excluded14_3
    · exact excluded14_4
    · exact excluded14_5
    · exact excluded14_6
    · exact excluded14_7
    · exact (hj rfl).elim
    · exact excluded14_9
theorem next14 : model14.insert step14 = model15 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded15_0 : ExcludedOn (model15.B 0 ++ [step15.q]) 9000000000000 (model15.caps 0)
    (model15.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_1 : ExcludedOn (model15.B 1 ++ [step15.q]) 9000000000000 (model15.caps 1)
    (model15.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_2 : ExcludedOn (model15.B 2 ++ [step15.q]) 9000000000000 (model15.caps 2)
    (model15.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4680000000000], [4245000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([2010000000000, 9000000000000], [3240000000000, -9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([930000000000], [2310000000000, -9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1440000000000, 9000000000000], [5175000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([930000000000], [3750000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([570000000000], [4680000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([75000000000], [4605000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [5175000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4245000000000], [8925000000000])
      (some (0, 1, 2)) (some (0, 1, 4)) (.next ([-3240000000000, 9000000000000], [5250000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2310000000000, 9000000000000], [3240000000000,
      -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-5175000000000], [6615000000000,
      9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3750000000000], [4680000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-4680000000000], [5250000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-4605000000000], [4680000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_5 : ExcludedOn (model15.B 5 ++ [step15.q]) 9000000000000 (model15.caps 5)
    (model15.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_7 : ExcludedOn (model15.B 7 ++ [step15.q]) 9000000000000 (model15.caps 7)
    (model15.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_8 : ExcludedOn (model15.B 8 ++ [step15.q]) 9000000000000 (model15.caps 8)
    (model15.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5175000000000], [225000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([165000000000], [60000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([5250000000000, 0], [3240000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([5250000000000], [4680000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1440000000000, 9000000000000], [3795000000000, -9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([1215000000000, 9000000000000], [3960000000000, -9000000000000]) (some (0, 1,
      4)) (some (0, 1, 4)) (.next ([75000000000], [4455000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([15000000000], [4680000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [5235000000000]) (some (0, 1, 4)) (some (0, 4, 4)) (.next ([-225000000000], [5400000000000])
      (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-60000000000], [225000000000]) (some (0, 4, 4))
      (some (0, 4, 4)) (.next ([-3240000000000, 9000000000000], [8490000000000, -9000000000000])
      (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-4680000000000], [9930000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-3795000000000, 9000000000000], [5235000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-3960000000000, 9000000000000], [5175000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-4455000000000], [4530000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-4680000000000], [4695000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some
      (0, 4, 3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_9 : ExcludedOn (model15.B 9 ++ [step15.q]) 9000000000000 (model15.caps 9)
    (model15.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked15 : StepValid model15 9000000000000 step15 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded15_0
    · exact excluded15_1
    · exact excluded15_2
    · exact (hj rfl).elim
    · exact excluded15_4
    · exact excluded15_5
    · exact excluded15_6
    · exact excluded15_7
    · exact excluded15_8
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext160000170000
end ConwaySoifer.Simplified.Certificates
