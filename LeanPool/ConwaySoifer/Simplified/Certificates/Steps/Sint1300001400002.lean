/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint130000140000
import Mathlib.Tactic.FinCases

/-!
# Sint 130000 140000 2

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
def fan19Owner5Part0 : FanWitness := (.next ([6735000000000], [1875000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([1596000000000], [510000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([1980000000000], [645000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([5565000000000, -9000000000000], [1875000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([1470000000000], [510000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2115000000000, 0],
    [1170000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([936000000000,
    -9000000000000], [1689000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([810000000000, -9000000000000], [1815000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([750000000000], [6504000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([750000000000], [6630000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([240000000000],
    [8610000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [2115000000000]) (some (0, 1,
    5)) (some (0, 1, 5)) (.next ([-519000000000], [2625000000000]) (some (0, 1, 5)) (some (0, 2, 5))
    (.next ([-1875000000000], [8610000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-510000000000], [2106000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-645000000000],
    [2625000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1875000000000, 0], [7440000000000,
    -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-510000000000], [1980000000000])
    (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-1170000000000, -9000000000000], [3285000000000,
    9000000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-1689000000000, -9000000000000],
    [2625000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-1815000000000, -9000000000000],
    [2625000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-6504000000000], [7254000000000])
    (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-6630000000000], [7380000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-8610000000000], [8850000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner5Part0 : FanWitness := (.next ([6750000000000], [1890000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([1596000000000], [510000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([1980000000000], [645000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([5580000000000, -9000000000000], [1890000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([1470000000000], [510000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2115000000000, 0],
    [1170000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([936000000000,
    -9000000000000], [1689000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([810000000000, -9000000000000], [1815000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([735000000000], [6534000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([735000000000], [6660000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([225000000000],
    [8640000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [2115000000000]) (some (0, 1,
    5)) (some (0, 1, 5)) (.next ([-519000000000], [2625000000000]) (some (0, 1, 5)) (some (0, 2, 5))
    (.next ([-1890000000000], [8640000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-510000000000], [2106000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-645000000000],
    [2625000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1890000000000, 0], [7470000000000,
    -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-510000000000], [1980000000000])
    (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-1170000000000, -9000000000000], [3285000000000,
    9000000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-1689000000000, -9000000000000],
    [2625000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-1815000000000, -9000000000000],
    [2625000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-6534000000000], [7269000000000])
    (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-6660000000000], [7395000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-8640000000000], [8865000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner5Part0 : FanWitness := (.next ([5850000000000, -9000000000000], [855000000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([2106000000000], [519000000000]) (some (4, 1, 5)) (some (4,
    1, 5)) (.next ([1596000000000], [510000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([1980000000000], [645000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1470000000000],
    [510000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2115000000000, 0], [1170000000000,
    9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([936000000000, -9000000000000],
    [1689000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([810000000000,
    -9000000000000], [1815000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([1770000000000], [5769000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([1770000000000],
    [5895000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([1260000000000], [7875000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [2115000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([-855000000000], [7875000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-855000000000, 0], [6705000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-519000000000], [2625000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-510000000000],
    [2106000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-645000000000], [2625000000000])
    (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-510000000000], [1980000000000]) (some (0, 5, 5))
    (some (0, 5, 5)) (.next ([-1170000000000, -9000000000000], [3285000000000, 9000000000000]) (some
    (0, 5, 5)) (some (0, 5, 5)) (.next ([-1689000000000, -9000000000000], [2625000000000]) (some (0,
    5, 5)) (some (0, 5, 5)) (.next ([-1815000000000, -9000000000000], [2625000000000]) (some (0, 5,
    5)) (some (0, 5, 5)) (.next ([-5769000000000], [7539000000000]) (some (0, 5, 5)) (some (0, 5,
    5)) (.next ([-5895000000000], [7665000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-7875000000000], [9135000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5,
    3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner0Part0 : FanWitness := (.next ([85800000000, 5160000000000], [5289600000000,
    -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([0, 0], [1006200000000,
    7740000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-249600000000, 2580000000000],
    [5960400000000, 2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-499200000000,
    5160000000000], [8289600000000, -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-499200000000, 5160000000000], [5334600000000, -2580000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-834600000000, 2580000000000], [7954200000000, -5160000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-834600000000, 2580000000000], [6005400000000, 2580000000000]) (some
    (7, 3, 5)) (some (7, 3, 5)) (.next ([-920400000000, -2580000000000], [6295800000000,
    5160000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-1545000000000], [9360000000000])
    (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-975000000000], [5850000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-1320000000000], [5985000000000]) (some (7, 3, 5)) (some (7, 3, 5))
    (.next ([-1505400000000, -2580000000000], [6340800000000, 5160000000000]) (some (7, 3, 5)) (some
    (7, 3, 5)) (.next ([-1905000000000], [6030000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-310800000000, -5160000000000], [710400000000, 2580000000000]) (some (7, 3, 5)) (some (7, 3,
    5)) (.next ([-335400000000, -2580000000000], [670800000000, 5160000000000]) (some (7, 3, 5))
    (some (7, 4, 5)) (.next ([-710400000000, -2580000000000], [1405800000000, 5160000000000]) (some
    (7, 4, 5)) (some (7, 4, 5)) (.next ([-210000000000], [345000000000]) (some (7, 4, 5)) (some (7,
    4, 5)) (.next ([-5670000000000], [7455000000000]) (some (7, 4, 5)) (some (7, 4, 6)) (.next
    ([-6420000000000], [8385000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-6210000000000],
    [8040000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-750000000000], [930000000000])
    (some (7, 4, 6)) (some (7, 4, 7)) (.next ([-5154600000000, 2580000000000], [5585400000000,
    2580000000000]) (some (7, 4, 7)) (some (7, 4, 7)) (.next ([-540000000000], [585000000000]) (some
    (7, 4, 7)) (some (7, 4, 7)) (.next ([-5289600000000, 2580000000000], [5375400000000,
    2580000000000]) (some (7, 4, 7)) (some (7, 4, 7)) (.terminal (some (7, 4, 7)) (some (7, 4, 7))
    (some (7, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner4Part0 : FanWitness := (.next ([3045000000000], [780000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([4005000000000], [2670000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([4080000000000], [2790000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1995000000000,
    -9000000000000], [1755000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next
    ([1875000000000, -9000000000000], [1950000000000, 9000000000000]) (some (5, 1, 5)) (some (5, 1,
    5)) (.next ([75000000000], [120000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
    ([1890000000000], [3165000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([1815000000000],
    [3045000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([375000000000], [1815000000000])
    (some (5, 1, 5)) (some (5, 1, 5)) (.next ([375000000000], [7455000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([0, 0], [1170000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([-795000000000, -9000000000000], [8625000000000, 9000000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-585000000000], [3750000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-1170000000000, -9000000000000], [6810000000000, 9000000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([-780000000000], [3825000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-2670000000000], [6675000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2790000000000],
    [6870000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1755000000000, -9000000000000],
    [3750000000000, 0]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1950000000000, -9000000000000],
    [3825000000000, 0]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-120000000000], [195000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3165000000000], [5055000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-3045000000000], [4860000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-1815000000000], [2190000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-7455000000000], [7830000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
    5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6840000000000, 9000000000000], [3330000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([5670000000000], [4500000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1170000000000, 9000000000000], [1170000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4500000000000, -9000000000000],
      [4500000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1170000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3330000000000, 9000000000000],
      [10170000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4500000000000],
      [10170000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1170000000000, -9000000000000],
      [2340000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4500000000000,
      0], [9000000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3330000000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([7830000000000, -9000000000000],
      [1170000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4500000000000,
      -9000000000000], [4500000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([1170000000000], [3330000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1170000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, -9000000000000],
      [3330000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-1170000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-4500000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3330000000000],
      [4500000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6840000000000], [1170000000000, 9000000000000])
      (some (2, 0, 4)) (some (3, 0, 4)) (.next ([6255000000000], [1426500000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([2340000000000], [990000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([841500000000], [585000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([3330000000000], [4500000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2160000000000,
      -9000000000000], [5670000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next
      ([1903500000000], [5341500000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [1170000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 4, 2)) (.next ([-1170000000000,
      -9000000000000], [8010000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1426500000000], [7681500000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-990000000000],
      [3330000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-585000000000], [1426500000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4500000000000], [7830000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5670000000000, -9000000000000], [7830000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5341500000000], [7245000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded16_1
    · exact excluded16_2
    · exact excluded16_3
    · exact excluded16_4
    · exact excluded16_5
    · exact excluded16_6
    · exact excluded16_7
    · exact excluded16_8
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6795000000000, 9000000000000], [2790000000000,
      -9000000000000]) (some (3, 3, 1)) none (.next ([5625000000000], [3960000000000]) none none
      (.next ([4455000000000, -9000000000000], [3960000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1170000000000, 9000000000000], [1170000000000, 9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.next ([0, 0], [1170000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-2790000000000, 9000000000000], [9585000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-3960000000000], [9585000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-3960000000000, 0], [8415000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-1170000000000, -9000000000000], [2340000000000, 18000000000000]) (some (3, 1, 0))
      (some (3, 1, 3)) (.terminal (some (3, 1, 3)) (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7830000000000, -9000000000000], [1170000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2790000000000, -9000000000000],
      [585000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4455000000000,
      -9000000000000], [3960000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([585000000000],
      [3375000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1170000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1170000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-585000000000, -9000000000000],
      [3375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3960000000000, 0],
      [8415000000000, -9000000000000]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-3375000000000],
      [3960000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6840000000000], [1170000000000, 9000000000000])
      (some (2, 0, 4)) (some (3, 0, 4)) (.next ([6255000000000], [1426500000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([841500000000], [585000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([1800000000000], [1575000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next
      ([3375000000000], [5040000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2205000000000,
      -9000000000000], [6210000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next
      ([1948500000000], [5881500000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [1170000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 4, 2)) (.next ([-1170000000000,
      -9000000000000], [8010000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1426500000000], [7681500000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-585000000000],
      [1426500000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1575000000000], [3375000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5040000000000], [8415000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-6210000000000, -9000000000000], [8415000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5881500000000], [7830000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded17_1
    · exact excluded17_2
    · exact excluded17_3
    · exact excluded17_4
    · exact excluded17_5
    · exact excluded17_6
    · exact excluded17_7
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6660000000000, 9000000000000], [2580000000000,
      -9000000000000]) (some (3, 3, 1)) none (.next ([5490000000000], [3750000000000]) none none
      (.next ([4320000000000, -9000000000000], [3750000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1170000000000, 9000000000000], [1170000000000, 9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.next ([0, 0], [1170000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-2580000000000, 9000000000000], [9240000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-3750000000000], [9240000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-3750000000000, 0], [8070000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-1170000000000, -9000000000000], [2340000000000, 18000000000000]) (some (3, 1, 0))
      (some (3, 1, 3)) (.terminal (some (3, 1, 3)) (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7830000000000, -9000000000000], [1170000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2580000000000, -9000000000000],
      [930000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4320000000000,
      -9000000000000], [3750000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([240000000000],
      [3510000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1170000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1170000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-930000000000, -9000000000000],
      [3510000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3750000000000, 0],
      [8070000000000, -9000000000000]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-3510000000000],
      [3750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6840000000000], [1170000000000, 9000000000000])
      (some (2, 0, 4)) (some (3, 0, 4)) (.next ([6255000000000], [1426500000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([841500000000], [585000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([1590000000000], [1920000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next
      ([3510000000000], [5250000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2340000000000,
      -9000000000000], [6420000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next
      ([2083500000000], [6091500000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [1170000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 4, 2)) (.next ([-1170000000000,
      -9000000000000], [8010000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1426500000000], [7681500000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-585000000000],
      [1426500000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1920000000000], [3510000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5250000000000], [8760000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-6420000000000, -9000000000000], [8760000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-6091500000000], [8175000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded18_1
    · exact excluded18_2
    · exact excluded18_3
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
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1170000000000, 9000000000000], [1170000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2265000000000], [5955000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2265000000000], [7125000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1095000000000, -9000000000000], [8295000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1170000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-1170000000000, -9000000000000],
      [2340000000000, 18000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-5955000000000,
      9000000000000], [8220000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-7125000000000], [9390000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8295000000000,
      -9000000000000], [9390000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2106000000000], [519000000000]) (some (3, 0, 5))
      (some (4, 1, 5)) fan19Owner5Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem excluded19_9 : ExcludedOn (model19.B 9 ++ [step19.q]) 9000000000000 (model19.caps 9)
    (model19.ord 9) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded19_7
    · exact excluded19_8
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1170000000000, 9000000000000], [1170000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2250000000000], [5940000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2250000000000], [7110000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1080000000000, -9000000000000], [8280000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1170000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-1170000000000, -9000000000000],
      [2340000000000, 18000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-5940000000000,
      9000000000000], [8190000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-7110000000000], [9360000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8280000000000,
      -9000000000000], [9360000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2106000000000], [519000000000]) (some (3, 0, 5))
      (some (4, 1, 5)) fan20Owner5Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7020000000000], [855000000000]) (some (3, 0, 5))
      (some (4, 1, 5)) fan21Owner5Part0)) (den := 9000000000000)
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
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3165000000000], [585000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([5640000000000, 0], [1170000000000, 9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([3045000000000], [780000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([5310000000000], [3750000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([5115000000000], [3825000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1995000000000,
      -9000000000000], [1755000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([1875000000000, -9000000000000], [1950000000000, 9000000000000]) (some (5, 1, 2)) (some (5,
      1, 2)) (.next ([75000000000], [120000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([1890000000000], [3165000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([1815000000000],
      [3045000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([255000000000], [5640000000000])
      (some (5, 1, 3)) (some (5, 1, 4)) (.next ([0, 0], [1170000000000, 9000000000000]) (some (5, 1,
      4)) (some (5, 1, 4)) (.next ([-585000000000], [3750000000000]) (some (5, 1, 4)) (some (5, 1,
      4)) (.next ([-1170000000000, -9000000000000], [6810000000000, 9000000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([-780000000000], [3825000000000]) (some (5, 1, 4)) (some (5, 1, 4))
      (.next ([-3750000000000], [9060000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([-3825000000000], [8940000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([-1755000000000,
      -9000000000000], [3750000000000, 0]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([-1950000000000, -9000000000000], [3825000000000, 0]) (some (5, 1, 4)) (some (5, 2, 4))
      (.next ([-120000000000], [195000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-3165000000000], [5055000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-3045000000000], [4860000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-5640000000000], [5895000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.terminal (some (5, 2,
      4)) (some (0, 2, 5)) (some (5, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_9 : ExcludedOn (model22.B 9 ++ [step22.q]) 9000000000000 (model22.caps 9)
    (model22.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded22_6
    · exact excluded22_7
    · exact (hj rfl).elim
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5710800000000, 5160000000000], [249600000000,
      -2580000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next ([7790400000000, 2580000000000],
      [499200000000, -5160000000000]) (some (7, 7, 4)) (some (7, 7, 4)) (.next ([4835400000000,
      2580000000000], [499200000000, -5160000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([7119600000000, -2580000000000], [834600000000, -2580000000000]) (some (7, 2, 4)) (some (7,
      2, 4)) (.next ([5170800000000, 5160000000000], [834600000000, -2580000000000]) (some (7, 2,
      4)) (some (7, 2, 4)) (.next ([5375400000000, 2580000000000], [920400000000, 2580000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([7815000000000], [1545000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([4875000000000], [975000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      (.next ([4665000000000], [1320000000000]) (some (7, 2, 4)) (some (7, 2, 5)) (.next
      ([4835400000000, 2580000000000], [1505400000000, 2580000000000]) (some (7, 2, 5)) (some (7, 2,
      5)) (.next ([4125000000000], [1905000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
      ([399600000000, -2580000000000], [310800000000, 5160000000000]) (some (7, 2, 5)) (some (7, 2,
      5)) (.next ([335400000000, 2580000000000], [335400000000, 2580000000000]) (some (7, 2, 5))
      (some (7, 2, 5)) (.next ([695400000000, 2580000000000], [710400000000, 2580000000000]) (some
      (7, 2, 5)) (some (7, 3, 5)) (.next ([135000000000], [210000000000]) (some (7, 3, 5)) (some (7,
      3, 5)) (.next ([1785000000000], [5670000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
      ([1965000000000], [6420000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([1830000000000],
      [6210000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([180000000000], [750000000000])
      (some (7, 3, 5)) (some (7, 3, 5)) (.next ([430800000000, 5160000000000], [5154600000000,
      -2580000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([45000000000], [540000000000])
      (some (7, 3, 5)) (some (7, 3, 5)) fan23Owner0Part0)))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7830000000000, 0], [795000000000,
      9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) (.next ([3165000000000], [585000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([5640000000000, 0], [1170000000000, 9000000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) fan23Owner4Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded23_8 : ExcludedOn (model23.B 8 ++ [step23.q]) 9000000000000 (model23.caps 8)
    (model23.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6270000000000], [1560000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([1545000000000], [1005000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([3720000000000], [3105000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1545000000000], [7830000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [3105000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1560000000000], [7830000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1005000000000], [2550000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([-3105000000000], [6825000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-7830000000000], [9375000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded23_4
    · exact excluded23_5
    · exact excluded23_6
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint130000140000
end ConwaySoifer.Simplified.Certificates
