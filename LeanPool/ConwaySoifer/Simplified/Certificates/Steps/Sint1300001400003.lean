/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint130000140000
import Mathlib.Tactic.FinCases

/-!
# Sint 130000 140000 3

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
namespace Sint130000140000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part0 : FanWitness := (.next ([279600000000, -2580000000000], [4539600000000,
    -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([85800000000, 5160000000000],
    [5289600000000, -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([0, 0],
    [1006200000000, 7740000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-249600000000,
    2580000000000], [5960400000000, 2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-499200000000, 5160000000000], [5334600000000, -2580000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-834600000000, 2580000000000], [6005400000000, 2580000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-920400000000, -2580000000000], [6295800000000, 5160000000000]) (some
    (7, 3, 5)) (some (7, 3, 5)) (.next ([-975000000000], [5850000000000]) (some (7, 3, 5)) (some (7,
    3, 5)) (.next ([-1320000000000], [5985000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-1505400000000, -2580000000000], [6340800000000, 5160000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-1905000000000], [6030000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-310800000000, -5160000000000], [710400000000, 2580000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-335400000000, -2580000000000], [670800000000, 5160000000000]) (some (7, 3, 5))
    (some (7, 4, 5)) (.next ([-710400000000, -2580000000000], [1405800000000, 5160000000000]) (some
    (7, 4, 5)) (some (7, 4, 5)) (.next ([-5055000000000], [9375000000000]) (some (7, 4, 5)) (some
    (7, 4, 5)) (.next ([-210000000000], [345000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([-4539600000000, 2580000000000], [5825400000000, 2580000000000]) (some (7, 4, 5)) (some (7, 4,
    6)) (.next ([-750000000000], [930000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-4204200000000, 5160000000000], [5154600000000, -2580000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-5250000000000], [6225000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-5154600000000, 2580000000000], [5585400000000, 2580000000000]) (some (7, 4, 6)) (some (7, 4,
    6)) (.next ([-540000000000], [585000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-4539600000000, 2580000000000], [4819200000000, -5160000000000]) (some (7, 4, 0)) (some (7, 4,
    0)) (.next ([-5289600000000, 2580000000000], [5375400000000, 2580000000000]) (some (7, 4, 0))
    (some (7, 4, 0)) (.terminal (some (7, 4, 0)) (some (7, 4, 0)) (some (7, 4,
    0)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner6Part0 : FanWitness := (.next ([780000000000, 9000000000000], [1095000000000,
    -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([3030000000000], [4485000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([3015000000000], [4515000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([3735000000000, -9000000000000], [6045000000000, 9000000000000]) (some
    (6, 2, 4)) (some (6, 2, 4)) (.next ([720000000000, -9000000000000], [1530000000000,
    9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([705000000000, -9000000000000],
    [1560000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([45000000000,
    9000000000000], [810000000000, -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([0,
    0], [1170000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-315000000000,
    -9000000000000], [2295000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 3, 4)) (.next
    ([-390000000000], [2265000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-270000000000],
    [1035000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-285000000000], [1020000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-3705000000000, 9000000000000], [8610000000000,
    -9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-3750000000000], [7800000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-4875000000000], [9780000000000]) (some (6, 3, 4))
    (some (6, 3, 4)) (.next ([-15000000000], [30000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-1080000000000, 9000000000000], [1890000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-1095000000000, 9000000000000], [1875000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-4485000000000], [7515000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-4515000000000],
    [7530000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-6045000000000, -9000000000000],
    [9780000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-1530000000000, -9000000000000],
    [2250000000000]) (some (6, 3, 4)) (some (6, 3, 6)) (.next ([-1560000000000, -9000000000000],
    [2265000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.next ([-810000000000, 9000000000000],
    [855000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.terminal (some (6, 3, 6)) (some (6, 3, 6))
    (some (6, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner6Part0 : FanWitness := (.next ([780000000000, 9000000000000], [1095000000000,
    -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([720000000000, -9000000000000],
    [1530000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([705000000000,
    -9000000000000], [1560000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([765000000000], [6645000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([810000000000,
    9000000000000], [7455000000000, -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([45000000000, 9000000000000], [810000000000, -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([30000000000], [6360000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([0, 0],
    [1170000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-360000000000],
    [8625000000000]) (some (6, 2, 4)) (some (6, 3, 4)) (.next ([-315000000000, -9000000000000],
    [2295000000000, 9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-360000000000],
    [2250000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-390000000000], [2265000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-1530000000000, -9000000000000], [8625000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-270000000000], [1035000000000]) (some (6, 3, 4))
    (some (6, 3, 6)) (.next ([-285000000000], [1020000000000]) (some (6, 3, 6)) (some (6, 3, 6))
    (.next ([-15000000000], [30000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.next
    ([-1080000000000, 9000000000000], [1890000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.next
    ([-1095000000000, 9000000000000], [1875000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.next
    ([-1530000000000, -9000000000000], [2250000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.next
    ([-1560000000000, -9000000000000], [2265000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.next
    ([-6645000000000], [7410000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.next ([-7455000000000,
    9000000000000], [8265000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-810000000000,
    9000000000000], [855000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-6360000000000],
    [6390000000000]) (some (1, 3, 6)) (some (2, 3, 6)) (.terminal (some (2, 3, 6)) (some (2, 3, 6))
    (some (2, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner6Part1 : FanWitness := (.next ([855000000000], [1125000000000]) (some (6, 2, 4)) (some
    (6, 2, 4)) (.next ([720000000000, -9000000000000], [1530000000000, 9000000000000]) (some (6, 2,
    4)) (some (6, 2, 4)) (.next ([705000000000, -9000000000000], [1560000000000, 9000000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([45000000000, 9000000000000], [810000000000,
    -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([810000000000, 9000000000000],
    [7455000000000, -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([765000000000],
    [6645000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([30000000000], [6360000000000]) (some
    (6, 2, 4)) (some (6, 2, 4)) (.next ([0, 0], [1170000000000, 9000000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-360000000000], [8625000000000]) (some (6, 2, 4)) (some (6, 3, 4))
    (.next ([-360000000000], [2250000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-390000000000], [2265000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-1530000000000,
    -9000000000000], [8625000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-270000000000],
    [1035000000000]) (some (6, 3, 4)) (some (6, 3, 6)) (.next ([-285000000000], [1020000000000])
    (some (6, 3, 6)) (some (6, 3, 6)) (.next ([-15000000000], [30000000000]) (some (6, 3, 6)) (some
    (6, 3, 6)) (.next ([-1080000000000, 9000000000000], [1890000000000]) (some (6, 3, 6)) (some (6,
    3, 6)) (.next ([-1095000000000, 9000000000000], [1875000000000]) (some (6, 3, 6)) (some (6, 3,
    6)) (.next ([-1125000000000], [1980000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.next
    ([-1530000000000, -9000000000000], [2250000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.next
    ([-1560000000000, -9000000000000], [2265000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.next
    ([-810000000000, 9000000000000], [855000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.next
    ([-7455000000000, 9000000000000], [8265000000000]) (some (6, 3, 6)) (some (6, 3, 6)) (.next
    ([-6645000000000], [7410000000000]) (some (2, 3, 6)) (some (2, 3, 6)) (.next ([-6360000000000],
    [6390000000000]) (some (2, 3, 6)) (some (2, 3, 6)) (.terminal (some (2, 3, 6)) (some (2, 3, 6))
    (some (2, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner6Part0 : FanWitness := (.next ([6750000000000], [2250000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([6720000000000], [2265000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([765000000000], [270000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([735000000000], [285000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([15000000000],
    [15000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([810000000000, 9000000000000],
    [1080000000000, -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([780000000000,
    9000000000000], [1095000000000, -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([720000000000, -9000000000000], [1530000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6,
    4)) (.next ([705000000000, -9000000000000], [1560000000000, 9000000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([45000000000, 9000000000000], [810000000000, -9000000000000]) (some (0,
    6, 4)) (some (0, 6, 4)) (.next ([0, 0], [1170000000000, 9000000000000]) (some (0, 6, 4)) (some
    (0, 6, 4)) (.next ([-315000000000, -9000000000000], [2295000000000, 9000000000000]) (some (0, 6,
    4)) (some (0, 6, 4)) (.next ([-1170000000000, -9000000000000], [7110000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-1980000000000], [7965000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2250000000000], [9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-2265000000000], [8985000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-270000000000],
    [1035000000000]) (some (0, 6, 4)) (some (6, 6, 4)) (.next ([-285000000000], [1020000000000])
    (some (6, 6, 4)) (some (6, 6, 4)) (.next ([-15000000000], [30000000000]) (some (6, 6, 4)) (some
    (6, 6, 4)) (.next ([-1080000000000, 9000000000000], [1890000000000]) (some (6, 6, 4)) (some (6,
    6, 4)) (.next ([-1095000000000, 9000000000000], [1875000000000]) (some (6, 6, 4)) (some (6, 6,
    4)) (.next ([-1530000000000, -9000000000000], [2250000000000]) (some (6, 6, 4)) (some (6, 6, 4))
    (.next ([-1560000000000, -9000000000000], [2265000000000]) (some (6, 6, 4)) (some (6, 6, 5))
    (.next ([-810000000000, 9000000000000], [855000000000]) (some (6, 6, 5)) (some (6, 6, 5))
    (.terminal (some (6, 6, 5)) (some (6, 3, 5)) (some (6, 6, 5)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5710800000000, 5160000000000], [249600000000,
      -2580000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([4835400000000, 2580000000000],
      [499200000000, -5160000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([5170800000000,
      5160000000000], [834600000000, -2580000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([5375400000000, 2580000000000], [920400000000, 2580000000000]) (some (0, 7, 4)) (some (0, 7,
      4)) (.next ([4875000000000], [975000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([4665000000000], [1320000000000]) (some (0, 7, 4)) (some (0, 7, 5)) (.next ([4835400000000,
      2580000000000], [1505400000000, 2580000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
      ([4125000000000], [1905000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([399600000000,
      -2580000000000], [310800000000, 5160000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
      ([335400000000, 2580000000000], [335400000000, 2580000000000]) (some (0, 7, 5)) (some (0, 7,
      5)) (.next ([695400000000, 2580000000000], [710400000000, 2580000000000]) (some (0, 7, 5))
      (some (0, 7, 5)) (.next ([4320000000000], [5055000000000]) (some (0, 7, 5)) (some (0, 7, 5))
      (.next ([135000000000], [210000000000]) (some (0, 7, 5)) (some (7, 7, 5)) (.next
      ([1285800000000, 5160000000000], [4539600000000, -2580000000000]) (some (7, 7, 5)) (some (7,
      7, 5)) (.next ([180000000000], [750000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
      ([950400000000, 2580000000000], [4204200000000, -5160000000000]) (some (7, 3, 5)) (some (7, 3,
      5)) (.next ([975000000000], [5250000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
      ([430800000000, 5160000000000], [5154600000000, -2580000000000]) (some (7, 3, 5)) (some (7, 3,
      5)) (.next ([45000000000], [540000000000]) (some (7, 3, 5)) (some (7, 3, 5))
      fan24Owner0Part0)))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2106000000000], [519000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([1596000000000], [510000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([1980000000000], [645000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([1470000000000], [510000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2115000000000,
      0], [1170000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4125000000000],
      [3375000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4125000000000], [5490000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([936000000000, -9000000000000], [1689000000000,
      9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2145000000000], [4845000000000])
      (some (5, 1, 2)) (some (5, 1, 3)) (.next ([2019000000000], [4971000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([0], [2115000000000]) (some (5, 1, 3)) (some (5, 1, 5)) (.next
      ([-519000000000], [2625000000000]) (some (5, 1, 5)) (some (5, 2, 5)) (.next ([-510000000000],
      [2106000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-645000000000], [2625000000000])
      (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-510000000000], [1980000000000]) (some (5, 2, 5))
      (some (5, 2, 5)) (.next ([-1170000000000, -9000000000000], [3285000000000, 9000000000000])
      (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-3375000000000], [7500000000000]) (some (5, 2, 5))
      (some (5, 2, 5)) (.next ([-5490000000000], [9615000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-1689000000000, -9000000000000], [2625000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-4845000000000], [6990000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-4971000000000], [6990000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded24_0
    · exact excluded24_1
    · exact excluded24_2
    · exact excluded24_3
    · exact (hj rfl).elim
    · exact excluded24_5
    · exact excluded24_6
    · exact excluded24_7
    · exact excluded24_8
    · exact excluded24_9
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [30000000000]) (some (3, 0, 4))
      (some (3, 4, 4)) (.next ([3510000000000], [615000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([5640000000000, 0], [1170000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([5640000000000], [3540000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([2340000000000, -9000000000000], [1785000000000, 9000000000000]) (some (3, 4, 2)) (some (3,
      4, 2)) (.next ([1515000000000], [3510000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0,
      0], [1170000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 3)) (.next ([-30000000000],
      [4155000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-615000000000], [4125000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1170000000000, -9000000000000], [6810000000000,
      9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3540000000000], [9180000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1785000000000, -9000000000000], [4125000000000,
      0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3510000000000], [5025000000000]) (some (0, 4,
      3)) (some (0, 4, 3)) (.terminal (some (0, 4, 3)) (some (0, 4, 3)) (some (0, 4,
      3))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded25_0
    · exact excluded25_1
    · exact excluded25_2
    · exact excluded25_3
    · exact excluded25_4
    · exact (hj rfl).elim
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_2 : ExcludedOn (model26.B 2 ++ [step26.q]) 9000000000000 (model26.caps 2)
    (model26.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1980000000000], [315000000000, 9000000000000])
      (some (6, 6, 3)) (some (6, 6, 4)) (.next ([1875000000000], [390000000000]) (some (6, 6, 4))
      (some (6, 6, 4)) (.next ([765000000000], [270000000000]) (some (6, 6, 4)) (some (6, 6, 4))
      (.next ([735000000000], [285000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
      ([4905000000000, 0], [3705000000000, -9000000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
      ([4050000000000], [3750000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([4905000000000],
      [4875000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([15000000000], [15000000000]) (some
      (6, 2, 4)) (some (6, 2, 4)) (.next ([810000000000, 9000000000000], [1080000000000,
      -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) fan26Owner6Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_9 : ExcludedOn (model26.B 9 ++ [step26.q]) 9000000000000 (model26.caps 9)
    (model26.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked26 : StepValid model26 9000000000000 step26 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded26_0
    · exact excluded26_1
    · exact excluded26_2
    · exact excluded26_3
    · exact excluded26_4
    · exact (hj rfl).elim
    · exact excluded26_6
    · exact excluded26_7
    · exact excluded26_8
    · exact excluded26_9
theorem next26 : model26.insert step26 = model27 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7470000000000, -9000000000000], [795000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([4125000000000], [780000000000])
      (some (4, 1, 2)) (some (4, 1, 4)) (.next ([5460000000000, 0], [1170000000000, 9000000000000])
      (some (4, 1, 4)) (some (4, 1, 4)) (.next ([5835000000000], [2805000000000]) (some (4, 1, 4))
      (some (4, 1, 4)) (.next ([2955000000000, -9000000000000], [1950000000000, 9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1155000000000], [3360000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([555000000000], [4125000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([375000000000], [8265000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [5460000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-795000000000, -9000000000000],
      [8265000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-780000000000], [4905000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1170000000000, -9000000000000], [6630000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2805000000000], [8640000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1950000000000, -9000000000000], [4905000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3360000000000], [4515000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-4125000000000], [4680000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-8265000000000], [8640000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (25) (52) (5200) (.witnessedFan (.next ([8265000000000],
      [360000000000]) (some (6, 2, 3)) (some (6, 2, 4)) (.next ([1980000000000], [315000000000,
      9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([1890000000000], [360000000000])
      (some (6, 2, 4)) (some (6, 2, 4)) (.next ([1875000000000], [390000000000]) (some (6, 2, 4))
      (some (6, 2, 4)) (.next ([7095000000000, -9000000000000], [1530000000000, 9000000000000])
      (some (6, 2, 4)) (some (6, 2, 4)) (.next ([765000000000], [270000000000]) (some (6, 2, 4))
      (some (6, 2, 4)) (.next ([735000000000], [285000000000]) (some (6, 2, 4)) (some (6, 2, 4))
      (.next ([15000000000], [15000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([810000000000,
      9000000000000], [1080000000000, -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4))
      fan27Owner6Part0)))))))))) (.witnessedFan (.next ([8265000000000], [360000000000]) (some (6,
      2, 3)) (some (6, 2, 4)) (.next ([1890000000000], [360000000000]) (some (6, 2, 4)) (some (6, 2,
      4)) (.next ([1875000000000], [390000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
      ([7095000000000, -9000000000000], [1530000000000, 9000000000000]) (some (6, 2, 4)) (some (6,
      2, 4)) (.next ([765000000000], [270000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
      ([735000000000], [285000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([15000000000],
      [15000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([810000000000, 9000000000000],
      [1080000000000, -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([780000000000,
      9000000000000], [1095000000000, -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4))
      fan27Owner6Part1))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_8 : ExcludedOn (model27.B 8 ++ [step27.q]) 9000000000000 (model27.caps 8)
    (model27.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_9 : ExcludedOn (model27.B 9 ++ [step27.q]) 9000000000000 (model27.caps 9)
    (model27.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked27 : StepValid model27 9000000000000 step27 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded27_1
    · exact excluded27_2
    · exact excluded27_3
    · exact excluded27_4
    · exact excluded27_5
    · exact excluded27_6
    · exact excluded27_7
    · exact excluded27_8
    · exact excluded27_9
theorem next27 : model27.insert step27 = model28 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded28_0 : ExcludedOn (model28.B 0 ++ [step28.q]) 9000000000000 (model28.caps 0)
    (model28.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1980000000000], [315000000000, 9000000000000])
      (some (5, 6, 3)) (some (5, 6, 4)) (.next ([5940000000000, -9000000000000], [1170000000000,
      9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([5985000000000], [1980000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) fan28Owner6Part0)))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_7 : ExcludedOn (model28.B 7 ++ [step28.q]) 9000000000000 (model28.caps 7)
    (model28.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_8 : ExcludedOn (model28.B 8 ++ [step28.q]) 9000000000000 (model28.caps 8)
    (model28.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked28 : StepValid model28 9000000000000 step28 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded28_0
    · exact excluded28_1
    · exact excluded28_2
    · exact excluded28_3
    · exact excluded28_4
    · exact excluded28_5
    · exact excluded28_6
    · exact excluded28_7
    · exact excluded28_8
    · exact (hj rfl).elim
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded29_0 : ExcludedOn (model29.B 0 ++ [step29.q]) 9000000000000 (model29.caps 0)
    (model29.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_1 : ExcludedOn (model29.B 1 ++ [step29.q]) 9000000000000 (model29.caps 1)
    (model29.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_2 : ExcludedOn (model29.B 2 ++ [step29.q]) 9000000000000 (model29.caps 2)
    (model29.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_3 : ExcludedOn (model29.B 3 ++ [step29.q]) 9000000000000 (model29.caps 3)
    (model29.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3510000000000], [615000000000]) (some (3, 0, 2))
      (some (3, 4, 2)) (.next ([5640000000000, 0], [1170000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([5640000000000], [3375000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([2340000000000, -9000000000000], [1785000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([1515000000000], [3510000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([135000000000], [3990000000000]) (some (3, 4, 2)) (some (3, 4, 3)) (.next ([0, 0],
      [1170000000000, 9000000000000]) (some (3, 4, 3)) (some (3, 4, 3)) (.next ([-615000000000],
      [4125000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1170000000000, -9000000000000],
      [6810000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3375000000000],
      [9015000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1785000000000, -9000000000000],
      [4125000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3510000000000],
      [5025000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3990000000000], [4125000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2,
      3))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_7 : ExcludedOn (model29.B 7 ++ [step29.q]) 9000000000000 (model29.caps 7)
    (model29.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_8 : ExcludedOn (model29.B 8 ++ [step29.q]) 9000000000000 (model29.caps 8)
    (model29.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_9 : ExcludedOn (model29.B 9 ++ [step29.q]) 9000000000000 (model29.caps 9)
    (model29.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked29 : StepValid model29 9000000000000 step29 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded29_0
    · exact excluded29_1
    · exact excluded29_2
    · exact excluded29_3
    · exact excluded29_4
    · exact (hj rfl).elim
    · exact excluded29_6
    · exact excluded29_7
    · exact excluded29_8
    · exact excluded29_9
theorem next29 : model29.insert step29 = model30 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded30_0 : ExcludedOn (model30.B 0 ++ [step30.q]) 9000000000000 (model30.caps 0)
    (model30.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_1 : ExcludedOn (model30.B 1 ++ [step30.q]) 9000000000000 (model30.caps 1)
    (model30.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_2 : ExcludedOn (model30.B 2 ++ [step30.q]) 9000000000000 (model30.caps 2)
    (model30.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_3 : ExcludedOn (model30.B 3 ++ [step30.q]) 9000000000000 (model30.caps 3)
    (model30.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [780000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5625000000000, 0], [1170000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([2925000000000], [1470000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([2955000000000, -9000000000000], [1950000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([2655000000000], [5175000000000]) (some (4, 1, 2)) (some (4, 1, 3))
      (.next ([1485000000000, -9000000000000], [6345000000000, 9000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([450000000000], [2205000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([720000000000], [4125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-780000000000], [4905000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-1170000000000, -9000000000000], [6795000000000,
      9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1470000000000], [4395000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1950000000000, -9000000000000], [4905000000000])
      (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-5175000000000], [7830000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-6345000000000, -9000000000000], [7830000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2205000000000], [2655000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-4125000000000], [4845000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_7 : ExcludedOn (model30.B 7 ++ [step30.q]) 9000000000000 (model30.caps 7)
    (model30.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_8 : ExcludedOn (model30.B 8 ++ [step30.q]) 9000000000000 (model30.caps 8)
    (model30.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_9 : ExcludedOn (model30.B 9 ++ [step30.q]) 9000000000000 (model30.caps 9)
    (model30.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked30 : StepValid model30 9000000000000 step30 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded30_0
    · exact excluded30_1
    · exact excluded30_2
    · exact excluded30_3
    · exact (hj rfl).elim
    · exact excluded30_5
    · exact excluded30_6
    · exact excluded30_7
    · exact excluded30_8
    · exact excluded30_9
theorem next30 : model30.insert step30 = model31 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded31_0 : ExcludedOn (model31.B 0 ++ [step31.q]) 9000000000000 (model31.caps 0)
    (model31.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_1 : ExcludedOn (model31.B 1 ++ [step31.q]) 9000000000000 (model31.caps 1)
    (model31.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_3 : ExcludedOn (model31.B 3 ++ [step31.q]) 9000000000000 (model31.caps 3)
    (model31.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3315000000000], [300000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([4125000000000], [780000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5625000000000, 0], [1170000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([2955000000000, -9000000000000], [1950000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([3825000000000], [4395000000000]) (some (4, 1, 2)) (some (4, 1, 3))
      (.next ([1230000000000], [2595000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([720000000000], [4125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-300000000000], [3615000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-780000000000], [4905000000000]) (some (0, 2, 3))
      (some (0, 2, 4)) (.next ([-1170000000000, -9000000000000], [6795000000000, 9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1950000000000, -9000000000000], [4905000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4395000000000], [8220000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2595000000000], [3825000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-4125000000000], [4845000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_6 : ExcludedOn (model31.B 6 ++ [step31.q]) 9000000000000 (model31.caps 6)
    (model31.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_7 : ExcludedOn (model31.B 7 ++ [step31.q]) 9000000000000 (model31.caps 7)
    (model31.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_8 : ExcludedOn (model31.B 8 ++ [step31.q]) 9000000000000 (model31.caps 8)
    (model31.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_9 : ExcludedOn (model31.B 9 ++ [step31.q]) 9000000000000 (model31.caps 9)
    (model31.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked31 : StepValid model31 9000000000000 step31 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded31_0
    · exact excluded31_1
    · exact excluded31_2
    · exact excluded31_3
    · exact (hj rfl).elim
    · exact excluded31_5
    · exact excluded31_6
    · exact excluded31_7
    · exact excluded31_8
    · exact excluded31_9
theorem next31 : model31.insert step31 = model32 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint130000140000
end ConwaySoifer.Simplified.Certificates
