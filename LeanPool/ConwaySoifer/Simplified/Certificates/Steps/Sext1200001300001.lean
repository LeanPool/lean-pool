/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext120000130000
import Mathlib.Tactic.FinCases

/-!
# Sext 120000 130000 1

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
namespace Sext120000130000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan10Owner0Part0 : FanWitness := (.next ([226800000000, -2610000000000], [5711400000000,
    5220000000000]) (some (7, 2, 5)) (some (7, 3, 5)) (.next ([46800000000, -2610000000000],
    [5801400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([0, 0], [939600000000,
    7830000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-86400000000, -5220000000000],
    [5398200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-266400000000,
    -5220000000000], [5488200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-45000000000], [720000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-436800000000,
    2610000000000], [5133600000000, -5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-1063200000000, -2610000000000], [6386400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-1063200000000, -2610000000000], [5446800000000, -2610000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-1376400000000, -5220000000000], [6073200000000, 2610000000000]) (some
    (7, 3, 5)) (some (7, 3, 5)) (.next ([-4680000000000], [9510000000000]) (some (7, 3, 5)) (some
    (7, 3, 5)) (.next ([-313200000000, -2610000000000], [626400000000, 5220000000000]) (some (7, 3,
    5)) (some (7, 3, 5)) (.next ([-5220000000000], [10095000000000]) (some (7, 3, 5)) (some (7, 4,
    6)) (.next ([-5400000000000], [10185000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-4186800000000, 2610000000000], [5893200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-4813200000000, -2610000000000], [6206400000000, 5220000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-4771800000000, 2610000000000], [5938200000000, 2610000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-4861800000000, 2610000000000], [5848200000000,
    2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5398200000000, -2610000000000],
    [6251400000000, 5220000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5126400000000,
    -5220000000000], [5893200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-5488200000000, -2610000000000], [6161400000000, 5220000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-4813200000000, -2610000000000], [5266800000000, -2610000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5711400000000, -5220000000000], [5938200000000, 2610000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-5801400000000, -5220000000000], [5848200000000,
    2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.terminal (some (7, 4, 6)) (some (7, 4, 6))
    (some (7, 4, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan10Owner3Part0 : FanWitness := (.next ([6840000000000, 9000000000000], [2910000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1620000000000, 9000000000000],
    [795000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1194000000000],
    [750000000000]) (some (4, 5, 2)) (some (4, 5, 3)) (.next ([5760000000000], [3990000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([4566000000000], [3240000000000]) (some (4, 5, 3))
    (some (4, 5, 3)) (.next ([4680000000000, -9000000000000], [3990000000000]) (some (4, 5, 3))
    (some (4, 5, 3)) (.next ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some
    (4, 5, 3)) (some (4, 5, 3)) (.next ([471000000000], [654000000000]) (some (4, 5, 3)) (some (4,
    5, 3)) (.next ([540000000000], [1875000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([330000000000, 9000000000000], [1944000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([114000000000, -9000000000000], [750000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0],
    [1080000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-2115000000000],
    [7335000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2910000000000, 9000000000000],
    [9750000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-795000000000, 9000000000000],
    [2415000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-750000000000], [1944000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3990000000000], [9750000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-3240000000000], [7806000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-3990000000000], [8670000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-1080000000000, -9000000000000], [2160000000000, 18000000000000]) (some (0, 5, 3))
    (some (5, 5, 3)) (.next ([-654000000000], [1125000000000]) (some (5, 5, 3)) (some (5, 5, 3))
    (.next ([-1875000000000], [2415000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
    ([-1944000000000, 0], [2274000000000, 9000000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
    ([-750000000000], [864000000000, -9000000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.terminal
    (some (5, 5, 3)) (some (5, 5, 3)) (some (5, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan11Owner0Part0 : FanWitness := (.next ([453600000000, -5220000000000], [4813200000000,
    2610000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([226800000000, -2610000000000],
    [5711400000000, 5220000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([46800000000,
    -2610000000000], [5801400000000, 5220000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([0,
    0], [939600000000, 7830000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([-45000000000],
    [7785000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-90000000000], [8505000000000])
    (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-86400000000, -5220000000000], [5398200000000,
    2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-266400000000, -5220000000000],
    [5488200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-45000000000],
    [720000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-313200000000, -2610000000000],
    [626400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-5938200000000,
    -2610000000000], [9491400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 4, 6)) (.next
    ([-5311800000000, 2610000000000], [8238600000000, -5220000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-6251400000000, -5220000000000], [9178200000000, 2610000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5938200000000, -2610000000000], [8551800000000, -2610000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4186800000000, 2610000000000], [5893200000000,
    2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4813200000000, -2610000000000],
    [6206400000000, 5220000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4771800000000,
    2610000000000], [5938200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-4861800000000, 2610000000000], [5848200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-5398200000000, -2610000000000], [6251400000000, 5220000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5126400000000, -5220000000000], [5893200000000, 2610000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-5488200000000, -2610000000000], [6161400000000,
    5220000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4813200000000, -2610000000000],
    [5266800000000, -2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5711400000000,
    -5220000000000], [5938200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-5801400000000, -5220000000000], [5848200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.terminal (some (7, 4, 6)) (some (7, 4, 6)) (some (7, 4, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner0Part0 : FanWitness := (.next ([673200000000, 2610000000000], [5488200000000,
    2610000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([453600000000, -5220000000000],
    [4813200000000, 2610000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next ([226800000000,
    -2610000000000], [5711400000000, 5220000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next
    ([46800000000, -2610000000000], [5801400000000, 5220000000000]) (some (7, 7, 5)) (some (7, 7,
    5)) (.next ([0, 0], [939600000000, 7830000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next
    ([-86400000000, -5220000000000], [5398200000000, 2610000000000]) (some (7, 7, 5)) (some (7, 7,
    5)) (.next ([-255000000000], [7920000000000]) (some (7, 7, 5)) (some (7, 3, 5)) (.next
    ([-300000000000], [8640000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-266400000000,
    -5220000000000], [5488200000000, 2610000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-45000000000], [720000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-313200000000,
    -2610000000000], [626400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-6148200000000, -2610000000000], [9626400000000, 5220000000000]) (some (7, 3, 5)) (some (7, 4,
    6)) (.next ([-5521800000000, 2610000000000], [8373600000000, -5220000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-6461400000000, -5220000000000], [9313200000000, 2610000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-4186800000000, 2610000000000], [5893200000000,
    2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4813200000000, -2610000000000],
    [6206400000000, 5220000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4771800000000,
    2610000000000], [5938200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-4861800000000, 2610000000000], [5848200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-5398200000000, -2610000000000], [6251400000000, 5220000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-5126400000000, -5220000000000], [5893200000000, 2610000000000]) (some
    (7, 4, 6)) (some (7, 4, 6)) (.next ([-5488200000000, -2610000000000], [6161400000000,
    5220000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4813200000000, -2610000000000],
    [5266800000000, -2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5711400000000,
    -5220000000000], [5938200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-5801400000000, -5220000000000], [5848200000000, 2610000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.terminal (some (7, 4, 6)) (some (7, 4, 6)) (some (7, 4, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner3Part0 : FanWitness := (.next ([1194000000000], [750000000000]) (some (4, 5, 2)) (some
    (4, 5, 3)) (.next ([5070000000000], [3390000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([3945000000000], [3861000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([1080000000000,
    9000000000000], [1080000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([4275000000000, 9000000000000], [5805000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([471000000000], [654000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([3195000000000],
    [4725000000000, -9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([3195000000000],
    [5805000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([540000000000], [1875000000000])
    (some (4, 5, 3)) (some (5, 5, 3)) (.next ([330000000000, 9000000000000], [1944000000000]) (some
    (5, 5, 3)) (some (5, 5, 3)) (.next ([114000000000, -9000000000000], [750000000000]) (some (5, 5,
    3)) (some (5, 5, 3)) (.next ([0], [1080000000000, 9000000000000]) (some (5, 5, 3)) (some (5, 5,
    3)) (.next ([-795000000000, 9000000000000], [2415000000000]) (some (5, 5, 3)) (some (5, 5, 3))
    (.next ([-750000000000], [1944000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
    ([-3390000000000], [8460000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-3861000000000],
    [7806000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1080000000000, -9000000000000],
    [2160000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-5805000000000, 0],
    [10080000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-654000000000],
    [1125000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-4725000000000, 9000000000000],
    [7920000000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-5805000000000],
    [9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1875000000000], [2415000000000])
    (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1944000000000, 0], [2274000000000, 9000000000000])
    (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-750000000000], [864000000000, -9000000000000]) (some
    (5, 2, 3)) (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 2, 3)) (some (5, 2,
    3)))))))))))))))))))))))))))

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_4 : ExcludedOn (model8.B 4 ++ [step8.q]) 9000000000000 (model8.caps 4) (model8.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_8 : ExcludedOn (model8.B 8 ++ [step8.q]) 9000000000000 (model8.caps 8) (model8.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7230000000000], [306000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([2250000000000], [270000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([1170000000000, -9000000000000], [270000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([810000000000, 9000000000000], [1440000000000, -9000000000000]) (some (0, 1, 4)) (some
      (0, 2, 4)) (.next ([1944000000000, 0], [6726000000000, -9000000000000]) (some (0, 2, 4)) (some
      (0, 2, 4)) (.next ([1944000000000], [7806000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([864000000000, -9000000000000], [7806000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([0, 0], [1080000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-306000000000], [7536000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-270000000000],
      [2520000000000]) (some (0, 2, 4)) (some (0, 4, 4)) (.next ([-270000000000, 0], [1440000000000,
      -9000000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-1440000000000, 9000000000000],
      [2250000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-6726000000000, 9000000000000],
      [8670000000000, -9000000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-7806000000000],
      [9750000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-7806000000000, 0],
      [8670000000000, -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4, 3))
      (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_9 : ExcludedOn (model8.B 9 ++ [step8.q]) 9000000000000 (model8.caps 9) (model8.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded8_4
    · exact excluded8_5
    · exact excluded8_6
    · exact excluded8_7
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_0 : ExcludedOn (model9.B 0 ++ [step9.q]) 9000000000000 (model9.caps 0) (model9.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8205000000000, 9000000000000], [1335000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([7125000000000], [2415000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([6045000000000, -9000000000000], [2415000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1080000000000, 9000000000000], [1080000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (3, 3, 1)) (some (3, 3, 1)) (.next ([-1335000000000, 9000000000000],
      [9540000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-2415000000000],
      [9540000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2415000000000, 0],
      [8460000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1080000000000,
      -9000000000000], [2160000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal
      (some (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_8 : ExcludedOn (model9.B 8 ++ [step9.q]) 9000000000000 (model9.caps 8) (model9.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_9 : ExcludedOn (model9.B 9 ++ [step9.q]) 9000000000000 (model9.caps 9) (model9.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded9_4
    · exact excluded9_5
    · exact excluded9_6
    · exact excluded9_7
    · exact excluded9_8
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_0 : ExcludedOn (model10.B 0 ++ [step10.q]) 9000000000000 (model10.caps 0)
    (model10.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5311800000000, -2610000000000], [86400000000,
      5220000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([5221800000000, -2610000000000],
      [266400000000, 5220000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([675000000000],
      [45000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([4696800000000, -2610000000000],
      [436800000000, -2610000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([5323200000000,
      2610000000000], [1063200000000, 2610000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([4383600000000, -5220000000000], [1063200000000, 2610000000000]) (some (6, 7, 4)) (some (6,
      7, 4)) (.next ([4696800000000, -2610000000000], [1376400000000, 5220000000000]) (some (6, 7,
      4)) (some (6, 7, 4)) (.next ([4830000000000], [4680000000000]) (some (6, 7, 4)) (some (7, 7,
      4)) (.next ([313200000000, 2610000000000], [313200000000, 2610000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([4875000000000], [5220000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      (.next ([4785000000000], [5400000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([1706400000000, 5220000000000], [4186800000000, -2610000000000]) (some (7, 2, 4)) (some (7,
      2, 4)) (.next ([1393200000000, 2610000000000], [4813200000000, 2610000000000]) (some (7, 2,
      4)) (some (7, 2, 4)) (.next ([1166400000000, 5220000000000], [4771800000000, -2610000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([986400000000, 5220000000000], [4861800000000,
      -2610000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([853200000000, 2610000000000],
      [5398200000000, 2610000000000]) (some (7, 2, 4)) (some (7, 2, 5)) (.next ([766800000000,
      -2610000000000], [5126400000000, 5220000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
      ([673200000000, 2610000000000], [5488200000000, 2610000000000]) (some (7, 2, 5)) (some (7, 2,
      5)) (.next ([453600000000, -5220000000000], [4813200000000, 2610000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) fan10Owner0Part0)))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5220000000000], [2115000000000]) (some (3, 5,
      5)) (some (4, 5, 5)) fan10Owner3Part0)) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_9 : ExcludedOn (model10.B 9 ++ [step10.q]) 9000000000000 (model10.caps 9)
    (model10.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7740000000000], [45000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([8415000000000], [90000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([5311800000000, -2610000000000], [86400000000, 5220000000000]) (some (6, 7, 4)) (some
      (6, 7, 4)) (.next ([5221800000000, -2610000000000], [266400000000, 5220000000000]) (some (6,
      7, 4)) (some (6, 7, 4)) (.next ([675000000000], [45000000000]) (some (6, 7, 4)) (some (6, 7,
      4)) (.next ([313200000000, 2610000000000], [313200000000, 2610000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([3553200000000, 2610000000000], [5938200000000, 2610000000000]) (some
      (0, 7, 4)) (some (0, 7, 4)) (.next ([2926800000000, -2610000000000], [5311800000000,
      -2610000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([2926800000000, -2610000000000],
      [6251400000000, 5220000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([2613600000000,
      -5220000000000], [5938200000000, 2610000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([1706400000000, 5220000000000], [4186800000000, -2610000000000]) (some (0, 7, 4)) (some (7,
      7, 4)) (.next ([1393200000000, 2610000000000], [4813200000000, 2610000000000]) (some (7, 7,
      4)) (some (7, 7, 4)) (.next ([1166400000000, 5220000000000], [4771800000000, -2610000000000])
      (some (7, 7, 4)) (some (7, 7, 4)) (.next ([986400000000, 5220000000000], [4861800000000,
      -2610000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next ([853200000000, 2610000000000],
      [5398200000000, 2610000000000]) (some (7, 7, 4)) (some (7, 7, 5)) (.next ([766800000000,
      -2610000000000], [5126400000000, 5220000000000]) (some (7, 7, 5)) (some (7, 7, 5)) (.next
      ([673200000000, 2610000000000], [5488200000000, 2610000000000]) (some (7, 7, 5)) (some (7, 7,
      5)) fan11Owner0Part0))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_9 : ExcludedOn (model11.B 9 ++ [step11.q]) 9000000000000 (model11.caps 9)
    (model11.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded12_0 : ExcludedOn (model12.B 0 ++ [step12.q]) 9000000000000 (model12.caps 0)
    (model12.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5311800000000, -2610000000000], [86400000000,
      5220000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([7665000000000], [255000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([8340000000000], [300000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([5221800000000, -2610000000000], [266400000000, 5220000000000]) (some
      (6, 7, 4)) (some (6, 7, 4)) (.next ([675000000000], [45000000000]) (some (6, 7, 4)) (some (6,
      7, 4)) (.next ([313200000000, 2610000000000], [313200000000, 2610000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([3478200000000, 2610000000000], [6148200000000, 2610000000000]) (some
      (0, 7, 4)) (some (0, 7, 4)) (.next ([2851800000000, -2610000000000], [5521800000000,
      -2610000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([2851800000000, -2610000000000],
      [6461400000000, 5220000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([1706400000000,
      5220000000000], [4186800000000, -2610000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([1393200000000, 2610000000000], [4813200000000, 2610000000000]) (some (0, 7, 4)) (some (7, 7,
      4)) (.next ([1166400000000, 5220000000000], [4771800000000, -2610000000000]) (some (7, 7, 4))
      (some (7, 7, 4)) (.next ([986400000000, 5220000000000], [4861800000000, -2610000000000]) (some
      (7, 7, 4)) (some (7, 7, 4)) (.next ([853200000000, 2610000000000], [5398200000000,
      2610000000000]) (some (7, 7, 4)) (some (7, 7, 5)) (.next ([766800000000, -2610000000000],
      [5126400000000, 5220000000000]) (some (7, 7, 5)) (some (7, 7, 5))
      fan12Owner0Part0)))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_3 : ExcludedOn (model12.B 3 ++ [step12.q]) 9000000000000 (model12.caps 3)
    (model12.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_8 : ExcludedOn (model12.B 8 ++ [step12.q]) 9000000000000 (model12.caps 8)
    (model12.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_9 : ExcludedOn (model12.B 9 ++ [step12.q]) 9000000000000 (model12.caps 9)
    (model12.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked12 : StepValid model12 9000000000000 step12 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded12_0
    · exact excluded12_1
    · exact excluded12_2
    · exact excluded12_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([1620000000000, 9000000000000], [795000000000,
      -9000000000000]) (some (3, 5, 2)) (some (5, 5, 2)) (.next ([1194000000000], [750000000000])
      (some (5, 5, 2)) (some (5, 5, 3)) (.next ([1080000000000, 9000000000000], [1080000000000,
      9000000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([471000000000], [654000000000])
      (some (5, 5, 3)) (some (5, 5, 3)) (.next ([2415000000000], [6600000000000]) (some (5, 5, 3))
      (some (5, 5, 3)) (.next ([1944000000000], [5946000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([540000000000], [1875000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([330000000000, 9000000000000], [1944000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([114000000000, -9000000000000], [750000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([0], [1080000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-795000000000, 9000000000000], [2415000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-750000000000], [1944000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1080000000000,
      -9000000000000], [2160000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-654000000000], [1125000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-6600000000000],
      [9015000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-5946000000000], [7890000000000])
      (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1875000000000], [2415000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([-1944000000000, 0], [2274000000000, 9000000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([-750000000000], [864000000000, -9000000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.terminal (some (5, 2, 3)) (some (5, 2, 3)) (some (5, 2,
      3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([1620000000000, 9000000000000], [795000000000,
      -9000000000000]) (some (3, 5, 2)) (some (4, 5, 2)) (.next ([5115000000000], [3210000000000])
      (some (4, 5, 2)) (some (4, 5, 3)) (.next ([1194000000000], [750000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([3990000000000], [3681000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some (4, 5, 3)) (some
      (4, 5, 3)) (.next ([4320000000000, 9000000000000], [5625000000000]) (some (4, 5, 3)) (some (4,
      5, 3)) (.next ([471000000000], [654000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([3240000000000], [5625000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([540000000000],
      [1875000000000]) (some (4, 5, 3)) (some (5, 5, 3)) (.next ([330000000000, 9000000000000],
      [1944000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([114000000000, -9000000000000],
      [750000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([0], [1080000000000, 9000000000000])
      (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-795000000000, 9000000000000], [2415000000000])
      (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-3210000000000], [8325000000000]) (some (5, 5, 3))
      (some (5, 5, 3)) (.next ([-750000000000], [1944000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([-3681000000000], [7671000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-1080000000000, -9000000000000], [2160000000000, 18000000000000]) (some (5, 2, 3)) (some (5,
      2, 3)) (.next ([-5625000000000, 0], [9945000000000, 9000000000000]) (some (5, 2, 3)) (some (5,
      2, 3)) (.next ([-654000000000], [1125000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-5625000000000], [8865000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-1875000000000], [2415000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1944000000000,
      0], [2274000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-750000000000],
      [864000000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.terminal (some (5, 2, 3))
      (some (5, 2, 3)) (some (5, 2, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded15_3 : ExcludedOn (model15.B 3 ++ [step15.q]) 9000000000000 (model15.caps 3)
    (model15.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1620000000000, 9000000000000], [795000000000,
      -9000000000000]) (some (3, 5, 2)) (some (4, 5, 2)) fan15Owner3Part0)) (den := 9000000000000)
      (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_5 : ExcludedOn (model15.B 5 ++ [step15.q]) 9000000000000 (model15.caps 5)
    (model15.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded15_9 : ExcludedOn (model15.B 9 ++ [step15.q]) 9000000000000 (model15.caps 9)
    (model15.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded15_3
    · exact excluded15_4
    · exact excluded15_5
    · exact excluded15_6
    · exact excluded15_7
    · exact (hj rfl).elim
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext120000130000
end ConwaySoifer.Simplified.Certificates
