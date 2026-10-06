/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext280000290000
import Mathlib.Tactic.FinCases

/-!
# Sext 280000 290000 5

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
namespace Sext280000290000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner4Part0 : FanWitness := (.next ([5445000000000], [1680000000000]) (some (4, 1, 2))
    (some (4, 1, 2)) (.next ([4605000000000], [1875000000000]) (some (4, 1, 2)) (some (4, 1, 2))
    (.next ([4770000000000], [2355000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
    ([840000000000], [480000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([4125000000000],
    [2520000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2520000000000, 9000000000000],
    [4911000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([840000000000, 9000000000000],
    [4605000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([645000000000,
    9000000000000], [6480000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([534000000000],
    [6591000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0, 9000000000000], [4125000000000,
    -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [4911000000000]) (some (4, 1,
    2)) (some (4, 1, 2)) (.next ([-786000000000], [7431000000000]) (some (0, 1, 2)) (some (0, 1, 2))
    (.next ([-306000000000], [1875000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([-1035000000000], [6285000000000]) (some (0, 1, 2)) (some (0, 5, 2)) (.next ([-1680000000000],
    [7125000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([-1875000000000], [6480000000000])
    (some (0, 5, 2)) (some (0, 5, 2)) (.next ([-2355000000000], [7125000000000]) (some (0, 5, 2))
    (some (0, 5, 2)) (.next ([-480000000000], [1320000000000]) (some (0, 5, 2)) (some (0, 5, 2))
    (.next ([-2520000000000], [6645000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next
    ([-4911000000000], [7431000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-4605000000000, 9000000000000], [5445000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-6480000000000], [7125000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-6591000000000], [7125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4125000000000,
    9000000000000], [4125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3))
    (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner3Part0 : FanWitness := (.next ([4965000000000], [2355000000000]) (some (4, 0, 1))
    (some (4, 0, 1)) (.next ([4395000000000], [2085000000000]) (some (4, 0, 1)) (some (4, 0, 1))
    (.next ([4125000000000], [2925000000000]) (some (4, 0, 1)) (some (4, 5, 1)) (.next
    ([5040000000000, 9000000000000], [3960000000000, -9000000000000]) (some (4, 5, 1)) (some (4, 5,
    1)) (.next ([2445000000000], [2295000000000]) (some (4, 5, 1)) (some (4, 5, 1)) (.next
    ([1680000000000], [2445000000000]) (some (4, 5, 1)) (some (4, 5, 2)) (.next ([2520000000000,
    9000000000000], [3900000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([2520000000000, 9000000000000], [4605000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([1815000000000], [4605000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([2520000000000],
    [6480000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([75000000000, 9000000000000],
    [1605000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0], [4605000000000])
    (some (4, 5, 2)) (some (4, 5, 3)) (.next ([-60000000000], [2580000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-2355000000000], [7320000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-2085000000000], [6480000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2925000000000], [7050000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3960000000000,
    9000000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2295000000000],
    [4740000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2445000000000], [4125000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3900000000000, 9000000000000], [6420000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4605000000000, 0], [7125000000000, 9000000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4605000000000], [6420000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-6480000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-1605000000000, 9000000000000], [1680000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner4Part0 : FanWitness := (.next ([5445000000000], [1680000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([840000000000], [480000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([4125000000000], [2520000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([2520000000000, 9000000000000], [3960000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([645000000000], [1035000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([2520000000000, 9000000000000], [4911000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
    ([1569000000000], [4911000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([840000000000,
    9000000000000], [4605000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
    ([534000000000], [6591000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([165000000000],
    [2355000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0, 9000000000000], [4125000000000,
    -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [4911000000000]) (some (4, 1,
    2)) (some (4, 1, 2)) (.next ([-786000000000], [7431000000000]) (some (0, 1, 2)) (some (0, 1, 2))
    (.next ([-1680000000000], [7125000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([-480000000000], [1320000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2520000000000],
    [6645000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-3960000000000, 9000000000000],
    [6480000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1035000000000], [1680000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4911000000000], [7431000000000, 9000000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4911000000000], [6480000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-4605000000000, 9000000000000], [5445000000000]) (some (0, 1, 3))
    (some (0, 5, 3)) (.next ([-6591000000000], [7125000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-2355000000000], [2520000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-4125000000000, 9000000000000], [4125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal
    (some (0, 5, 3)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner2Part0 : FanWitness := (.next ([1488000000000], [4536000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([876000000000], [3660000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([1179000000000], [5535000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([303000000000], [1875000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([489000000000],
    [4047000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([339000000000], [3360000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([36000000000], [1485000000000]) (some (0, 6, 4)) (some
    (0, 6, 4)) (.next ([0], [5535000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-495000000000, 9000000000000], [6375000000000, 0]) (some (0, 6, 4)) (some (0, 6, 5)) (.next
    ([-351000000000], [1872000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2016000000000,
    9000000000000], [6411000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2016000000000,
    9000000000000], [6024000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3015000000000],
    [6375000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4194000000000, 9000000000000],
    [6714000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-1488000000000], [2178000000000])
    (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-4536000000000], [6411000000000]) (some (0, 4, 5))
    (some (0, 4, 5)) (.next ([-2175000000000], [3015000000000]) (some (0, 4, 5)) (some (0, 4, 5))
    (.next ([-4536000000000], [6024000000000]) (some (0, 4, 5)) (some (1, 4, 5)) (.next
    ([-3660000000000], [4536000000000]) (some (1, 4, 5)) (some (1, 4, 5)) (.next ([-5535000000000],
    [6714000000000]) (some (1, 4, 5)) (some (1, 4, 5)) (.next ([-1875000000000], [2178000000000])
    (some (1, 4, 5)) (some (1, 4, 5)) (.next ([-4047000000000], [4536000000000]) (some (1, 4, 5))
    (some (1, 4, 5)) (.next ([-3360000000000], [3699000000000]) (some (1, 4, 5)) (some (1, 4, 5))
    (.next ([-1485000000000], [1521000000000]) (some (1, 4, 5)) (some (6, 4, 5)) (.terminal (some
    (6, 4, 5)) (some (6, 4, 0)) (some (6, 4, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner3Part0 : FanWitness := (.next ([4125000000000], [2925000000000]) (some (4, 0, 5))
    (some (4, 0, 5)) (.next ([2445000000000], [2295000000000]) (some (4, 0, 5)) (some (4, 0, 5))
    (.next ([1680000000000], [2445000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([2520000000000, 9000000000000], [3900000000000, -9000000000000]) (some (4, 0, 5)) (some (4, 0,
    5)) (.next ([2520000000000, 9000000000000], [4605000000000]) (some (4, 0, 5)) (some (4, 0, 5))
    (.next ([1815000000000], [4605000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([2109000000000], [6891000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next ([294000000000],
    [2286000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([75000000000, 9000000000000],
    [1605000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 5, 5)) (.next ([234000000000,
    9000000000000], [6480000000000, -9000000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next
    ([159000000000], [4875000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0],
    [4605000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-2286000000000], [9000000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2925000000000], [7050000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-2295000000000], [4740000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-2445000000000], [4125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-3900000000000, 9000000000000], [6420000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-4605000000000, 0], [7125000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-4605000000000], [6420000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6891000000000],
    [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2286000000000], [2580000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1605000000000, 9000000000000], [1680000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-6480000000000, 9000000000000], [6714000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4875000000000], [5034000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
    3)))))))))))))))))))))))))))

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6645000000000], [786000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([1569000000000], [306000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([5250000000000], [1035000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      fan40Owner4Part0)))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6300000000000, 9000000000000], [480000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([4395000000000], [3195000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1710000000000], [1290000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([3780000000000], [3000000000000]) (some (4, 1, 2)) (some (4, 1, 3))
      (.next ([1875000000000], [2520000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([2520000000000, 9000000000000], [5070000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1395000000000], [4905000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0,
      9000000000000], [1875000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0,
      0], [2520000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-480000000000,
      9000000000000], [6780000000000, 0]) (some (0, 1, 3)) (some (0, 2, 3)) (.next
      ([-3195000000000], [7590000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-1290000000000], [3000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-3000000000000], [6780000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-2520000000000], [4395000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5070000000000,
      0], [7590000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-4905000000000], [6300000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1875000000000,
      9000000000000], [1875000000000, 0]) (some (0, 2, 3)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2520000000000], [60000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) fan41Owner3Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_4 : ExcludedOn (model41.B 4 ++ [step41.q]) 9000000000000 (model41.caps 4)
    (model41.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6645000000000], [786000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan41Owner4Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [300000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([6300000000000, 9000000000000], [480000000000, -9000000000000]) (some
      (4, 1, 2)) (some (4, 1, 2)) (.next ([6480000000000], [2520000000000]) (some (4, 1, 2)) (some
      (4, 1, 2)) (.next ([1710000000000], [1290000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([3780000000000], [3000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([2520000000000,
      9000000000000], [5070000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1410000000000],
      [7590000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0, 9000000000000], [6480000000000,
      -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0, 0], [2520000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-300000000000], [6300000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-480000000000, 9000000000000], [6780000000000, 0])
      (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-2520000000000], [9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1290000000000], [3000000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-3000000000000], [6780000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-5070000000000, 0], [7590000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-7590000000000], [9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6480000000000,
      9000000000000], [6480000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_7 : ExcludedOn (model41.B 7 ++ [step41.q]) 9000000000000 (model41.caps 7)
    (model41.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_8 : ExcludedOn (model41.B 8 ++ [step41.q]) 9000000000000 (model41.caps 8)
    (model41.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_9 : ExcludedOn (model41.B 9 ++ [step41.q]) 9000000000000 (model41.caps 9)
    (model41.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked41 : StepValid model41 9000000000000 step41 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded41_1
    · exact excluded41_2
    · exact excluded41_3
    · exact excluded41_4
    · exact excluded41_5
    · exact excluded41_6
    · exact excluded41_7
    · exact excluded41_8
    · exact excluded41_9
theorem next41 : model41.insert step41 = model42 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6480000000000, -9000000000000], [234000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([4806000000000, 9000000000000],
      [4194000000000, -9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([2520000000000,
      9000000000000], [2520000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([2286000000000], [6714000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [2520000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-234000000000,
      -9000000000000], [6714000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-4194000000000, 9000000000000], [9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-2520000000000, -9000000000000], [5040000000000, 18000000000000]) (some (3, 1, 0)) (some (3,
      1, 0)) (.next ([-6714000000000], [9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal
      (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5880000000000, 9000000000000], [495000000000,
      -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([1521000000000], [351000000000])
      (some (0, 6, 4)) (some (0, 6, 4)) (.next ([4395000000000, 9000000000000], [2016000000000,
      -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([4008000000000, 9000000000000],
      [2016000000000, -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([3360000000000],
      [3015000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([2520000000000, 9000000000000],
      [4194000000000, -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([690000000000],
      [1488000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([1875000000000], [4536000000000])
      (some (0, 6, 4)) (some (0, 6, 4)) (.next ([840000000000], [2175000000000]) (some (0, 6, 4))
      (some (0, 6, 4)) fan42Owner2Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_3 : ExcludedOn (model42.B 3 ++ [step42.q]) 9000000000000 (model42.caps 3)
    (model42.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6714000000000], [2286000000000]) (some (3, 0,
      5)) (some (4, 0, 5)) fan42Owner3Part0)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_5 : ExcludedOn (model42.B 5 ++ [step42.q]) 9000000000000 (model42.caps 5)
    (model42.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_6 : ExcludedOn (model42.B 6 ++ [step42.q]) 9000000000000 (model42.caps 6)
    (model42.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_7 : ExcludedOn (model42.B 7 ++ [step42.q]) 9000000000000 (model42.caps 7)
    (model42.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_8 : ExcludedOn (model42.B 8 ++ [step42.q]) 9000000000000 (model42.caps 8)
    (model42.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_9 : ExcludedOn (model42.B 9 ++ [step42.q]) 9000000000000 (model42.caps 9)
    (model42.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked42 : StepValid model42 9000000000000 step42 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded42_1
    · exact excluded42_2
    · exact excluded42_3
    · exact excluded42_4
    · exact excluded42_5
    · exact excluded42_6
    · exact excluded42_7
    · exact excluded42_8
    · exact excluded42_9
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext280000290000
end ConwaySoifer.Simplified.Certificates
