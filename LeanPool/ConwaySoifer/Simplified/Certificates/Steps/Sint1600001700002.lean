/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint160000170000
import Mathlib.Tactic.FinCases

/-!
# Sint 160000 170000 2

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
namespace Sint160000170000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan17Owner0Part0 : FanWitness := (.next ([-81600000000, 2490000000000], [1253400000000,
    2490000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-561600000000, 2490000000000],
    [5108400000000, 2490000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-261600000000,
    2490000000000], [1058400000000, 2490000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-1620000000000], [5370000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-480000000000],
    [1515000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-1815000000000], [5085000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-660000000000], [1320000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-1560000000000], [3000000000000]) (some (8, 5, 7)) (some (8, 5, 7))
    (.next ([-5745000000000], [10350000000000]) (some (8, 5, 7)) (some (8, 5, 7)) (.next
    ([-960000000000], [1710000000000]) (some (8, 5, 7)) (some (8, 5, 7)) (.next ([-4185000000000],
    [7350000000000]) (some (8, 5, 7)) (some (8, 5, 7)) (.next ([-285000000000], [480000000000])
    (some (8, 5, 7)) (some (8, 5, 7)) (.next ([-3201600000000, 2490000000000], [4523400000000,
    2490000000000]) (some (8, 5, 7)) (some (8, 6, 7)) (.next ([-2803200000000, 4980000000000],
    [3726600000000, -2490000000000]) (some (8, 6, 7)) (some (8, 6, 7)) (.next ([-3600000000000],
    [4785000000000]) (some (8, 6, 7)) (some (8, 6, 7)) (.next ([-1140000000000], [1515000000000])
    (some (8, 6, 7)) (some (8, 6, 7)) (.next ([-796800000000, -4980000000000], [1058400000000,
    2490000000000]) (some (8, 6, 7)) (some (8, 6, 7)) (.next ([-5895000000000], [7230000000000])
    (some (8, 6, 7)) (some (8, 6, 7)) (.next ([-4080000000000], [4980000000000]) (some (8, 6, 7))
    (some (8, 6, 7)) (.next ([-6270000000000], [7410000000000]) (some (8, 6, 7)) (some (8, 6, 7))
    (.next ([-2940000000000], [3465000000000]) (some (8, 6, 7)) (some (8, 6, 7)) (.next
    ([-6668400000000, -2490000000000], [7546800000000, 4980000000000]) (some (8, 6, 7)) (some (8, 6,
    7)) (.next ([-3120000000000], [3270000000000]) (some (8, 6, 7)) (some (8, 6, 7)) (.next
    ([-7066800000000, -4980000000000], [7148400000000, 2490000000000]) (some (8, 6, 7)) (some (8, 6,
    7)) (.terminal (some (8, 6, 7)) (some (8, 6, 7)) (some (8, 6, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan17Owner0Part1 : FanWitness := (.next ([796800000000, 4980000000000], [261600000000,
    -2490000000000]) (some (7, 8, 7)) (some (7, 8, 7)) (.next ([3750000000000], [1620000000000])
    (some (7, 8, 7)) (some (7, 8, 7)) (.next ([1035000000000], [480000000000]) (some (7, 8, 7))
    (some (7, 8, 7)) (.next ([3270000000000], [1815000000000]) (some (7, 8, 7)) (some (7, 8, 7))
    (.next ([660000000000], [660000000000]) (some (7, 8, 7)) (some (7, 8, 7)) (.next
    ([1440000000000], [1560000000000]) (some (7, 8, 7)) (some (7, 8, 7)) (.next ([4605000000000],
    [5745000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next ([750000000000], [960000000000]) (some
    (0, 8, 7)) (some (0, 8, 7)) (.next ([3165000000000], [4185000000000]) (some (0, 8, 7)) (some (0,
    8, 7)) (.next ([195000000000], [285000000000]) (some (0, 8, 7)) (some (8, 8, 7)) (.next
    ([1321800000000, 4980000000000], [3201600000000, -2490000000000]) (some (8, 8, 7)) (some (8, 8,
    7)) (.next ([923400000000, 2490000000000], [2803200000000, -4980000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([1185000000000], [3600000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([375000000000], [1140000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([261600000000, -2490000000000], [796800000000, 4980000000000]) (some (8, 4, 7)) (some (8, 4,
    7)) (.next ([1335000000000], [5895000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([900000000000], [4080000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([1140000000000],
    [6270000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([525000000000], [2940000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([878400000000, 2490000000000], [6668400000000,
    2490000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([150000000000], [3120000000000]) (some
    (8, 4, 7)) (some (8, 4, 7)) (.next ([81600000000, -2490000000000], [7066800000000,
    4980000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-105000000000], [4335000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-180000000000], [6930000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) fan17Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part0 : FanWitness := (.next ([-81600000000, 2490000000000], [1253400000000,
    2490000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-561600000000, 2490000000000],
    [5108400000000, 2490000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-261600000000,
    2490000000000], [1058400000000, 2490000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-2145000000000], [7665000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-2340000000000],
    [8040000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-1620000000000], [5370000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-2601600000000, 2490000000000], [8438400000000,
    2490000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-480000000000], [1515000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-1815000000000], [5085000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-3398400000000, -2490000000000], [8836800000000, 4980000000000]) (some
    (1, 4, 7)) (some (1, 4, 7)) (.next ([-3660000000000], [8700000000000]) (some (1, 4, 7)) (some
    (1, 5, 7)) (.next ([-3855000000000], [8415000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next
    ([-1710000000000], [3480000000000]) (some (1, 5, 7)) (some (1, 5, 7)) (.next ([-660000000000],
    [1320000000000]) (some (1, 5, 7)) (some (1, 5, 8)) (.next ([-1560000000000], [3000000000000])
    (some (1, 5, 8)) (some (1, 5, 8)) (.next ([-960000000000], [1710000000000]) (some (1, 5, 8))
    (some (2, 5, 8)) (.next ([-285000000000], [480000000000]) (some (2, 5, 8)) (some (2, 5, 8))
    (.next ([-2040000000000], [3330000000000]) (some (2, 5, 8)) (some (3, 6, 8)) (.next
    ([-1140000000000], [1515000000000]) (some (3, 6, 8)) (some (3, 6, 8)) (.next ([-796800000000,
    -4980000000000], [1058400000000, 2490000000000]) (some (3, 6, 8)) (some (3, 6, 8)) (.next
    ([-5895000000000], [7230000000000]) (some (3, 6, 8)) (some (3, 6, 8)) (.next ([-6270000000000],
    [7410000000000]) (some (3, 6, 8)) (some (3, 6, 8)) (.next ([-6668400000000, -2490000000000],
    [7546800000000, 4980000000000]) (some (3, 6, 8)) (some (3, 6, 8)) (.next ([-7066800000000,
    -4980000000000], [7148400000000, 2490000000000]) (some (3, 6, 8)) (some (3, 6, 8)) (.terminal
    (some (3, 6, 8)) (some (3, 6, 8)) (some (3, 6, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part1 : FanWitness := (.next ([796800000000, 4980000000000], [261600000000,
    -2490000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([5520000000000], [2145000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([5700000000000], [2340000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([3750000000000], [1620000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([5836800000000, 4980000000000], [2601600000000, -2490000000000]) (some (8, 3, 7)) (some
    (8, 3, 7)) (.next ([1035000000000], [480000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([3270000000000], [1815000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([5438400000000,
    2490000000000], [3398400000000, 2490000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([5040000000000], [3660000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([4560000000000],
    [3855000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([1770000000000], [1710000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([660000000000], [660000000000]) (some (8, 3, 7)) (some
    (8, 3, 7)) (.next ([1440000000000], [1560000000000]) (some (8, 3, 7)) (some (8, 4, 7)) (.next
    ([750000000000], [960000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([195000000000],
    [285000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([1290000000000], [2040000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([375000000000], [1140000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([261600000000, -2490000000000], [796800000000, 4980000000000]) (some
    (8, 4, 7)) (some (8, 4, 7)) (.next ([1335000000000], [5895000000000]) (some (8, 4, 7)) (some (8,
    4, 7)) (.next ([1140000000000], [6270000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([878400000000, 2490000000000], [6668400000000, 2490000000000]) (some (8, 4, 7)) (some (8, 4,
    7)) (.next ([81600000000, -2490000000000], [7066800000000, 4980000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-105000000000], [4335000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-180000000000], [6930000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    fan18Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner4Part0 : FanWitness := (.next ([3435000000000, -9000000000000], [1920000000000,
    9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3435000000000, -9000000000000],
    [1965000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3210000000000,
    -9000000000000], [2190000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([2385000000000], [2775000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1905000000000],
    [5355000000000]) (some (5, 1, 3)) (some (6, 1, 3)) (.next ([1860000000000], [5400000000000])
    (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1635000000000], [5400000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([45000000000], [225000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([0, 0], [1440000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([-195000000000], [4875000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([-240000000000],
    [4875000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-240000000000], [4650000000000])
    (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-480000000000], [5355000000000]) (some (6, 1, 4))
    (some (6, 1, 5)) (.next ([-525000000000], [5400000000000]) (some (6, 1, 5)) (some (6, 1, 5))
    (.next ([-750000000000], [5400000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next
    ([-1440000000000, -9000000000000], [6600000000000, 9000000000000]) (some (6, 1, 5)) (some (6, 1,
    5)) (.next ([-1920000000000, -9000000000000], [5355000000000, 0]) (some (6, 1, 5)) (some (6, 1,
    5)) (.next ([-1965000000000, -9000000000000], [5400000000000, 0]) (some (6, 1, 5)) (some (6, 2,
    5)) (.next ([-2190000000000, -9000000000000], [5400000000000, 0]) (some (6, 2, 5)) (some (6, 2,
    5)) (.next ([-2775000000000], [5160000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next
    ([-5355000000000], [7260000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-5400000000000],
    [7260000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-5400000000000], [7035000000000])
    (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-225000000000], [270000000000]) (some (6, 2, 5))
    (some (6, 2, 5)) (.terminal (some (6, 2, 5)) (some (0, 2, 5)) (some (6, 2,
    5)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3225000000000], [15000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5355000000000], [150000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3240000000000], [750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([3975000000000, 0], [1440000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([5355000000000], [4125000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1800000000000,
      -9000000000000], [2190000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([3915000000000, -9000000000000], [5565000000000, 9000000000000]) (some (4, 1, 2)) (some (4,
      1, 3)) (.next ([2115000000000], [3375000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([0], [3975000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next ([-15000000000],
      [3240000000000]) (some (4, 1, 4)) (some (4, 2, 4)) (.next ([-150000000000], [5505000000000])
      (some (4, 2, 4)) (some (4, 2, 4)) (.next ([-750000000000], [3990000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1440000000000, -9000000000000], [5415000000000, 9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4125000000000], [9480000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2190000000000, -9000000000000], [3990000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-5565000000000, -9000000000000], [9480000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3375000000000], [5490000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded16_0
    · exact excluded16_1
    · exact excluded16_2
    · exact excluded16_3
    · exact (hj rfl).elim
    · exact excluded16_5
    · exact excluded16_6
    · exact excluded16_7
    · exact excluded16_8
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded17_0 : ExcludedOn (model17.B 0 ++ [step17.q]) 9000000000000 (model17.caps 0)
    (model17.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4230000000000], [105000000000]) (some (7, 8, 6))
      (some (7, 8, 6)) (.next ([6750000000000], [180000000000]) (some (7, 8, 6)) (some (7, 8, 6))
      (.next ([1171800000000, 4980000000000], [81600000000, -2490000000000]) (some (7, 8, 6)) (some
      (7, 8, 6)) (.next ([4546800000000, 4980000000000], [561600000000, -2490000000000]) (some (7,
      8, 6)) (some (7, 8, 7)) fan17Owner0Part1))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3225000000000], [15000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5400000000000], [150000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3240000000000], [750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([3975000000000, 0], [1440000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([5400000000000], [4125000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1800000000000,
      -9000000000000], [2190000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([3960000000000, -9000000000000], [5565000000000, 9000000000000]) (some (4, 1, 2)) (some (4,
      1, 3)) (.next ([2160000000000], [3375000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([0], [3975000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next ([-15000000000],
      [3240000000000]) (some (4, 1, 4)) (some (4, 2, 4)) (.next ([-150000000000], [5550000000000])
      (some (4, 2, 4)) (some (4, 2, 4)) (.next ([-750000000000], [3990000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1440000000000, -9000000000000], [5415000000000, 9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4125000000000], [9525000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2190000000000, -9000000000000], [3990000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-5565000000000, -9000000000000], [9525000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3375000000000], [5535000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_9 : ExcludedOn (model17.B 9 ++ [step17.q]) 9000000000000 (model17.caps 9)
    (model17.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked17 : StepValid model17 9000000000000 step17 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded17_0
    · exact excluded17_1
    · exact excluded17_2
    · exact excluded17_3
    · exact (hj rfl).elim
    · exact excluded17_5
    · exact excluded17_6
    · exact excluded17_7
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded18_0 : ExcludedOn (model18.B 0 ++ [step18.q]) 9000000000000 (model18.caps 0)
    (model18.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4230000000000], [105000000000]) (some (8, 3, 6))
      (some (8, 3, 6)) (.next ([6750000000000], [180000000000]) (some (8, 3, 6)) (some (8, 3, 6))
      (.next ([1171800000000, 4980000000000], [81600000000, -2490000000000]) (some (8, 3, 6)) (some
      (8, 3, 6)) (.next ([4546800000000, 4980000000000], [561600000000, -2490000000000]) (some (8,
      3, 6)) (some (8, 3, 7)) fan18Owner0Part1))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_9 : ExcludedOn (model18.B 9 ++ [step18.q]) 9000000000000 (model18.caps 9)
    (model18.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked18 : StepValid model18 9000000000000 step18 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded18_0
    · exact excluded18_1
    · exact excluded18_2
    · exact (hj rfl).elim
    · exact excluded18_4
    · exact excluded18_5
    · exact excluded18_6
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_0 : ExcludedOn (model19.B 0 ++ [step19.q]) 9000000000000 (model19.caps 0)
    (model19.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3225000000000], [15000000000]) (some (3, 0, 4))
      (some (3, 4, 4)) (.next ([3240000000000], [750000000000]) (some (0, 4, 4)) (some (0, 4, 4))
      (.next ([3975000000000, 0], [1440000000000, 9000000000000]) (some (0, 4, 4)) (some (0, 4, 4))
      (.next ([1800000000000, -9000000000000], [2190000000000, 9000000000000]) (some (0, 4, 4))
      (some (0, 4, 4)) (.next ([3240000000000], [5760000000000]) (some (0, 4, 4)) (some (0, 4, 4))
      (.next ([1440000000000, 9000000000000], [3570000000000, -9000000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([0], [3975000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-15000000000], [3240000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-750000000000],
      [3990000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1440000000000, -9000000000000],
      [5415000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2190000000000,
      -9000000000000], [3990000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-5760000000000],
      [9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3570000000000, 9000000000000],
      [5010000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4, 3)) (some (0, 4,
      3)) (some (0, 4, 3))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked19 : StepValid model19 9000000000000 step19 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded19_0
    · exact excluded19_1
    · exact excluded19_2
    · exact excluded19_3
    · exact excluded19_4
    · exact excluded19_5
    · exact excluded19_6
    · exact excluded19_7
    · exact excluded19_8
    · exact (hj rfl).elim
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1440000000000, 9000000000000], [1440000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([3825000000000], [4455000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3825000000000], [5895000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2385000000000, -9000000000000], [7335000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1440000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-1440000000000, -9000000000000],
      [2880000000000, 18000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-4455000000000,
      9000000000000], [8280000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-5895000000000], [9720000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7335000000000,
      -9000000000000], [9720000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3225000000000], [15000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([3240000000000], [750000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([3975000000000, 0], [1440000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([5175000000000], [3105000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([3735000000000, -9000000000000], [3105000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1800000000000, -9000000000000], [2190000000000, 9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([885000000000], [5040000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([870000000000], [8280000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [3975000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-15000000000], [3240000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-750000000000], [3990000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1440000000000, -9000000000000], [5415000000000, 9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3105000000000], [8280000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3105000000000, 0], [6840000000000, -9000000000000]) (some (0, 2,
      4)) (some (0, 2, 4)) (.next ([-2190000000000, -9000000000000], [3990000000000]) (some (0, 2,
      4)) (some (0, 4, 4)) (.next ([-5040000000000], [5925000000000]) (some (0, 4, 4)) (some (0, 4,
      4)) (.next ([-8280000000000], [9150000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal
      (some (0, 4, 3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_9 : ExcludedOn (model20.B 9 ++ [step20.q]) 9000000000000 (model20.caps 9)
    (model20.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked20 : StepValid model20 9000000000000 step20 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded20_0
    · exact excluded20_1
    · exact excluded20_2
    · exact excluded20_3
    · exact excluded20_4
    · exact excluded20_5
    · exact (hj rfl).elim
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1440000000000, 9000000000000], [1440000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([3825000000000], [4320000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3825000000000], [5760000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2385000000000, -9000000000000], [7200000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1440000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-1440000000000, -9000000000000],
      [2880000000000, 18000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-4320000000000,
      9000000000000], [8145000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-5760000000000], [9585000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7200000000000,
      -9000000000000], [9585000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3225000000000], [15000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([3240000000000], [750000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([3975000000000, 0], [1440000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([5175000000000], [3240000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([3735000000000, -9000000000000], [3240000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1800000000000, -9000000000000], [2190000000000, 9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([750000000000], [5175000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([735000000000], [8415000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [3975000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-15000000000], [3240000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-750000000000], [3990000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1440000000000, -9000000000000], [5415000000000, 9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3240000000000], [8415000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3240000000000, 0], [6975000000000, -9000000000000]) (some (0, 2,
      4)) (some (0, 2, 4)) (.next ([-2190000000000, -9000000000000], [3990000000000]) (some (0, 2,
      4)) (some (0, 4, 4)) (.next ([-5175000000000], [5925000000000]) (some (0, 4, 4)) (some (0, 4,
      4)) (.next ([-8415000000000], [9150000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal
      (some (0, 4, 3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_9 : ExcludedOn (model21.B 9 ++ [step21.q]) 9000000000000 (model21.caps 9)
    (model21.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked21 : StepValid model21 9000000000000 step21 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded21_0
    · exact excluded21_1
    · exact excluded21_2
    · exact excluded21_3
    · exact excluded21_4
    · exact excluded21_5
    · exact (hj rfl).elim
    · exact excluded21_7
    · exact excluded21_8
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3225000000000], [15000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([5360000000000], [960000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([3240000000000], [750000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([3920000000000, -9000000000000], [960000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([3975000000000, 0], [1440000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([3030000000000], [3080000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1800000000000,
      -9000000000000], [2190000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([3015000000000], [6320000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [3975000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-15000000000], [3240000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-960000000000], [6320000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-750000000000], [3990000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-960000000000, 0], [4880000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1440000000000, -9000000000000], [5415000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 4, 4)) (.next ([-3080000000000], [6110000000000]) (some (0, 4, 4)) (some (0, 4, 4))
      (.next ([-2190000000000, -9000000000000], [3990000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-6320000000000], [9335000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some
      (0, 4, 3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_9 : ExcludedOn (model22.B 9 ++ [step22.q]) 9000000000000 (model22.caps 9)
    (model22.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6320000000000], [3640000000000]) (some (3, 0,
      1)) (some (3, 1, 2)) (.next ([4880000000000, -9000000000000], [3640000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([350000000000], [5970000000000]) (some (3, 1, 2)) (some (3, 1,
      3)) (.next ([0], [3990000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3640000000000],
      [9960000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3640000000000], [8520000000000,
      -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5970000000000], [6320000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1,
      3))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem checked22 : StepValid model22 9000000000000 step22 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded22_0
    · exact excluded22_1
    · exact excluded22_2
    · exact excluded22_3
    · exact excluded22_4
    · exact excluded22_5
    · exact (hj rfl).elim
    · exact excluded22_7
    · exact excluded22_8
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4680000000000], [195000000000]) (some (5, 0, 2))
      (some (5, 1, 3)) (.next ([4635000000000], [240000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([4410000000000], [240000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([4875000000000], [480000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4875000000000],
      [525000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4650000000000], [750000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([5160000000000, 0], [1440000000000, 9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) fan23Owner4Part0)))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_9 : ExcludedOn (model23.B 9 ++ [step23.q]) 9000000000000 (model23.caps 9)
    (model23.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked23 : StepValid model23 9000000000000 step23 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded23_0
    · exact excluded23_1
    · exact excluded23_2
    · exact excluded23_3
    · exact excluded23_4
    · exact excluded23_5
    · exact excluded23_6
    · exact excluded23_7
    · exact (hj rfl).elim
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint160000170000
end ConwaySoifer.Simplified.Certificates
