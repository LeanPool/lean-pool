/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint130000140000
import Mathlib.Tactic.FinCases

/-!
# Sint 130000 140000 5

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
def fan41Owner6Part0 : FanWitness := (.next ([435000000000], [3075000000000]) (some (6, 1, 3)) (some
    (6, 1, 3)) (.next ([555000000000], [3960000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([390000000000, 9000000000000], [3735000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1,
    3)) (.next ([0, 9000000000000], [3825000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1,
    3)) (.next ([0, 0], [1170000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([-420000000000, -9000000000000], [5850000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 2,
    3)) (.next ([-780000000000], [4905000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
    ([-1170000000000], [4995000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-2955000000000,
    9000000000000], [8220000000000, -9000000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
    ([-1950000000000, -9000000000000], [4905000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
    ([-4125000000000], [9390000000000]) (some (6, 2, 3)) (some (6, 2, 4)) (.next ([-2340000000000,
    -9000000000000], [4995000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1170000000000,
    -9000000000000], [2340000000000, 18000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-5295000000000, -9000000000000], [9390000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-2955000000000], [4395000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-3345000000000],
    [4485000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-300000000000], [390000000000])
    (some (6, 2, 4)) (some (6, 2, 6)) (.next ([-3510000000000, 9000000000000], [4260000000000,
    -9000000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([-4680000000000], [5430000000000])
    (some (6, 2, 6)) (some (6, 2, 6)) (.next ([-3375000000000], [3900000000000]) (some (6, 2, 6))
    (some (6, 2, 6)) (.next ([-3075000000000], [3510000000000]) (some (6, 2, 6)) (some (6, 2, 6))
    (.next ([-3960000000000], [4515000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next
    ([-3735000000000, 9000000000000], [4125000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-3825000000000, 9000000000000], [3825000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.terminal
    (some (0, 2, 6)) (some (0, 2, 6)) (some (0, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner6Part0 : FanWitness := (.next ([720000000000], [7500000000000]) (some (0, 6, 3)) (some
    (0, 6, 3)) (.next ([630000000000], [7200000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next
    ([195000000000], [4125000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([0, 9000000000000],
    [3825000000000, -9000000000000]) (some (0, 6, 3)) (some (6, 6, 3)) (.next ([0, 0],
    [1170000000000, 9000000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([-420000000000,
    -9000000000000], [5850000000000, 9000000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next
    ([-780000000000], [4905000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([-1170000000000],
    [4995000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next ([-3375000000000], [9000000000000])
    (some (6, 6, 3)) (some (6, 6, 3)) (.next ([-1950000000000, -9000000000000], [4905000000000])
    (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-3375000000000, 0], [7830000000000, -9000000000000])
    (some (6, 2, 3)) (some (6, 2, 4)) (.next ([-4545000000000, -9000000000000], [10170000000000,
    9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-2340000000000, -9000000000000],
    [4995000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1170000000000, -9000000000000],
    [2340000000000, 18000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-300000000000],
    [390000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-3510000000000, 9000000000000],
    [4260000000000, -9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-4680000000000],
    [5430000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-3375000000000], [3900000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-3075000000000], [3510000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-3735000000000, 9000000000000], [4125000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-7500000000000], [8220000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-7200000000000], [7830000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-4125000000000], [4320000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-3825000000000,
    9000000000000], [3825000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.terminal (some (6, 2, 4))
    (some (6, 2, 4)) (some (6, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner0Part0 : FanWitness := (.next ([-1095000000000], [6345000000000]) (some (1, 8, 6))
    (some (1, 8, 6)) (.next ([-1545000000000], [6780000000000]) (some (1, 8, 6)) (some (1, 8, 6))
    (.next ([-120000000000], [495000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next
    ([-315000000000], [1245000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-1545000000000],
    [5910000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-1905000000000], [6405000000000])
    (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-1905000000000], [5535000000000]) (some (1, 8, 6))
    (some (1, 8, 6)) (.next ([-420000000000], [1155000000000]) (some (1, 8, 6)) (some (1, 8, 6))
    (.next ([-375000000000], [930000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next
    ([-310800000000, -5160000000000], [710400000000, 2580000000000]) (some (1, 8, 6)) (some (1, 8,
    6)) (.next ([-810000000000], [1620000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next
    ([-375000000000], [735000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-4440000000000],
    [6705000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-5595000000000], [8220000000000])
    (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-5485800000000, -5160000000000], [7775400000000,
    2580000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-5175000000000], [7065000000000])
    (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-1155000000000], [1515000000000]) (some (1, 8, 6))
    (some (1, 8, 6)) (.next ([-7800000000000], [8610000000000]) (some (1, 8, 6)) (some (1, 8, 6))
    (.next ([-5490000000000], [6030000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next
    ([-750000000000], [810000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-5985000000000],
    [6405000000000]) (some (1, 8, 6)) (some (1, 8, 7)) (.next ([-7680000000000], [8115000000000])
    (some (1, 8, 7)) (some (1, 8, 7)) (.next ([-5825400000000, -2580000000000], [5920800000000,
    5160000000000]) (some (1, 8, 7)) (some (1, 8, 7)) (.next ([-8610000000000], [8670000000000])
    (some (1, 8, 7)) (some (1, 8, 7)) (.terminal (some (1, 8, 7)) (some (1, 8, 7)) (some (1, 8,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner0Part1 : FanWitness := (.next ([399600000000, -2580000000000], [310800000000,
    5160000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([810000000000], [810000000000]) (some
    (7, 2, 8)) (some (7, 3, 8)) (.next ([360000000000], [375000000000]) (some (7, 3, 8)) (some (7,
    3, 8)) (.next ([2265000000000], [4440000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([2625000000000], [5595000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([2289600000000,
    -2580000000000], [5485800000000, 5160000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([1890000000000], [5175000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([360000000000],
    [1155000000000]) (some (7, 3, 8)) (some (7, 8, 8)) (.next ([810000000000], [7800000000000])
    (some (7, 8, 8)) (some (7, 8, 8)) (.next ([540000000000], [5490000000000]) (some (7, 8, 6))
    (some (7, 8, 6)) (.next ([60000000000], [750000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next
    ([420000000000], [5985000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([435000000000],
    [7680000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([95400000000, 2580000000000],
    [5825400000000, 2580000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([60000000000],
    [8610000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([0], [870000000000]) (some (7, 8, 6))
    (some (7, 8, 6)) (.next ([-390000000000], [6045000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-390000000000], [5175000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-810000000000], [8610000000000]) (some (0, 8, 6)) (some (1, 8, 6)) (.next ([-615000000000],
    [6225000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-735000000000], [6720000000000])
    (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-834600000000, 2580000000000], [6380400000000,
    2580000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-834600000000, 2580000000000],
    [5510400000000, 2580000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-975000000000],
    [5850000000000]) (some (1, 8, 6)) (some (1, 8, 6)) fan44Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner6Part0 : FanWitness := (.next ([90000000000], [300000000000]) (some (4, 0, 6)) (some
    (4, 0, 6)) (.next ([720000000000], [3540000000000]) (some (4, 0, 6)) (some (5, 0, 6)) (.next
    ([630000000000], [3240000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([585000000000, 0],
    [3870000000000, -9000000000000]) (some (0, 0, 6)) (some (0, 0, 6)) (.next ([390000000000,
    9000000000000], [3735000000000, -9000000000000]) (some (0, 0, 6)) (some (0, 1, 6)) (.next ([0,
    9000000000000], [3825000000000, -9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([0,
    0], [1170000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-390000000000,
    9000000000000], [6375000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-585000000000,
    -9000000000000], [6210000000000, 9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-780000000000], [4905000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1170000000000],
    [4995000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1560000000000], [6375000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1560000000000], [5205000000000, -9000000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2250000000000], [5595000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-2550000000000], [5985000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-2340000000000, -9000000000000], [4995000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-1170000000000, -9000000000000], [2340000000000, 18000000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-5790000000000], [9855000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-300000000000], [390000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-3540000000000], [4260000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3240000000000],
    [3870000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3870000000000, 9000000000000],
    [4455000000000, -9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3735000000000,
    9000000000000], [4125000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3825000000000,
    9000000000000], [3825000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.terminal (some (0, 2, 6))
    (some (0, 2, 6)) (some (0, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner6Part0 : FanWitness := (.next ([2655000000000, -9000000000000], [2340000000000,
    9000000000000]) (some (4, 0, 6)) (some (4, 0, 6)) (.next ([1170000000000, 9000000000000],
    [1170000000000, 9000000000000]) (some (4, 0, 6)) (some (4, 0, 6)) (.next ([90000000000],
    [300000000000]) (some (4, 0, 6)) (some (4, 0, 6)) (.next ([1170000000000, 9000000000000],
    [4380000000000]) (some (4, 0, 6)) (some (5, 0, 6)) (.next ([720000000000], [3540000000000])
    (some (5, 0, 6)) (some (5, 0, 6)) (.next ([630000000000], [3240000000000]) (some (5, 0, 6))
    (some (5, 0, 6)) (.next ([585000000000, 0], [3870000000000, -9000000000000]) (some (0, 0, 6))
    (some (0, 0, 6)) (.next ([390000000000, 9000000000000], [3735000000000, -9000000000000]) (some
    (0, 0, 6)) (some (0, 1, 6)) (.next ([0, 9000000000000], [3825000000000, -9000000000000]) (some
    (0, 1, 6)) (some (0, 1, 6)) (.next ([0, 0], [1170000000000, 9000000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-255000000000], [5160000000000]) (some (0, 1, 6)) (some (0, 2, 6))
    (.next ([-555000000000], [5550000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-780000000000], [4905000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1170000000000],
    [4995000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3795000000000], [9420000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2340000000000, -9000000000000], [4995000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1170000000000, -9000000000000], [2340000000000,
    18000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-300000000000], [390000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4380000000000, 0], [5550000000000, 9000000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3540000000000], [4260000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-3240000000000], [3870000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-3870000000000, 9000000000000], [4455000000000, -9000000000000]) (some (0, 2, 6)) (some
    (0, 2, 6)) (.next ([-3735000000000, 9000000000000], [4125000000000]) (some (0, 2, 6)) (some (0,
    2, 6)) (.next ([-3825000000000, 9000000000000], [3825000000000]) (some (0, 2, 6)) (some (0, 2,
    6)) (.terminal (some (0, 2, 6)) (some (0, 2, 6)) (some (0, 2, 6)))))))))))))))))))))))))))

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7455000000000], [390000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([6840000000000], [1170000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 4, 4)) (.next ([6465000000000], [1545000000000]) (some (3, 4, 4)) (some (3, 4, 2))
      (.next ([1170000000000], [375000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([780000000000], [8220000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [1170000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-390000000000],
      [7845000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1170000000000, -9000000000000],
      [8010000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1545000000000],
      [8010000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-375000000000], [1545000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-8220000000000], [9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2)))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2655000000000, -9000000000000], [0,
      9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next ([3435000000000, -9000000000000],
      [390000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([7050000000000,
      -9000000000000], [1170000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([5640000000000, 0], [1170000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([4395000000000], [1170000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([5640000000000],
      [2580000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([780000000000], [390000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2985000000000], [3825000000000]) (some (4, 1, 5))
      (some (4, 1, 5)) (.next ([1170000000000], [2655000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([1815000000000], [4605000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([780000000000], [3825000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 0],
      [1170000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, -9000000000000],
      [2655000000000, 0]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-390000000000, -9000000000000],
      [3825000000000, 0]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-1170000000000,
      -9000000000000], [8220000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-1170000000000, -9000000000000], [6810000000000, 9000000000000]) (some (0, 2, 5)) (some (0,
      2, 5)) (.next ([-1170000000000], [5565000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-2580000000000], [8220000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-390000000000],
      [1170000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3825000000000], [6810000000000])
      (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2655000000000], [3825000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-4605000000000], [6420000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-3825000000000], [4605000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some
      (0, 5, 4)) (some (0, 5, 4)) (some (0, 5, 4))))))))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8220000000000], [780000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([4125000000000], [780000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5640000000000, 0], [1170000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([7050000000000, -9000000000000], [1950000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([2955000000000, -9000000000000], [1950000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 4)) (.next ([735000000000], [4125000000000]) (some (4, 1, 4))
      (some (0, 1, 4)) (.next ([0], [5640000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-780000000000], [9000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-780000000000],
      [4905000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1170000000000, -9000000000000],
      [6810000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1950000000000,
      -9000000000000], [9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1950000000000,
      -9000000000000], [4905000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4125000000000],
      [4860000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2,
      4)) (some (0, 2, 4))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded41_0 : ExcludedOn (model41.B 0 ++ [step41.q]) 9000000000000 (model41.caps 0)
    (model41.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_4 : ExcludedOn (model41.B 4 ++ [step41.q]) 9000000000000 (model41.caps 4)
    (model41.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5430000000000], [420000000000, 9000000000000])
      (some (6, 0, 2)) (some (6, 0, 3)) (.next ([4125000000000], [780000000000]) (some (6, 0, 3))
      (some (6, 0, 3)) (.next ([3825000000000], [1170000000000]) (some (6, 0, 3)) (some (6, 0, 3))
      (.next ([5265000000000, 0], [2955000000000, -9000000000000]) (some (6, 0, 3)) (some (6, 0, 3))
      (.next ([2955000000000, -9000000000000], [1950000000000, 9000000000000]) (some (6, 0, 3))
      (some (6, 0, 3)) (.next ([5265000000000], [4125000000000]) (some (6, 0, 3)) (some (6, 0, 3))
      (.next ([2655000000000, -9000000000000], [2340000000000, 9000000000000]) (some (6, 0, 3))
      (some (6, 0, 3)) (.next ([1170000000000, 9000000000000], [1170000000000, 9000000000000]) (some
      (6, 0, 3)) (some (6, 0, 3)) (.next ([4095000000000, -9000000000000], [5295000000000,
      9000000000000]) (some (6, 0, 3)) (some (6, 0, 3)) (.next ([1440000000000], [2955000000000])
      (some (6, 0, 3)) (some (6, 0, 3)) (.next ([1140000000000], [3345000000000]) (some (6, 0, 3))
      (some (6, 0, 3)) (.next ([90000000000], [300000000000]) (some (6, 0, 3)) (some (6, 0, 3))
      (.next ([750000000000, 0], [3510000000000, -9000000000000]) (some (6, 0, 3)) (some (6, 0, 3))
      (.next ([750000000000], [4680000000000]) (some (6, 0, 3)) (some (6, 1, 3)) (.next
      ([525000000000], [3375000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      fan41Owner6Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked41 : StepValid model41 9000000000000 step41 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded41_0
    · exact excluded41_1
    · exact excluded41_2
    · exact excluded41_3
    · exact excluded41_4
    · exact (hj rfl).elim
    · exact excluded41_6
    · exact excluded41_7
    · exact excluded41_8
    · exact excluded41_9
theorem next41 : model41.insert step41 = model42 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded42_0 : ExcludedOn (model42.B 0 ++ [step42.q]) 9000000000000 (model42.caps 0)
    (model42.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_3 : ExcludedOn (model42.B 3 ++ [step42.q]) 9000000000000 (model42.caps 3)
    (model42.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5430000000000], [420000000000, 9000000000000])
      (some (4, 6, 2)) (some (4, 6, 3)) (.next ([4125000000000], [780000000000]) (some (4, 6, 3))
      (some (4, 6, 3)) (.next ([3825000000000], [1170000000000]) (some (4, 6, 3)) (some (4, 6, 3))
      (.next ([5625000000000], [3375000000000]) (some (4, 6, 3)) (some (4, 6, 3)) (.next
      ([2955000000000, -9000000000000], [1950000000000, 9000000000000]) (some (4, 6, 3)) (some (4,
      6, 3)) (.next ([4455000000000, -9000000000000], [3375000000000]) (some (4, 6, 3)) (some (4, 6,
      3)) (.next ([5625000000000], [4545000000000, 9000000000000]) (some (4, 6, 3)) (some (4, 6, 3))
      (.next ([2655000000000, -9000000000000], [2340000000000, 9000000000000]) (some (4, 6, 3))
      (some (4, 6, 3)) (.next ([1170000000000, 9000000000000], [1170000000000, 9000000000000]) (some
      (4, 6, 3)) (some (4, 6, 3)) (.next ([90000000000], [300000000000]) (some (4, 6, 3)) (some (4,
      6, 3)) (.next ([750000000000, 0], [3510000000000, -9000000000000]) (some (4, 6, 3)) (some (5,
      6, 3)) (.next ([750000000000], [4680000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([525000000000], [3375000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([435000000000],
      [3075000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([390000000000, 9000000000000],
      [3735000000000, -9000000000000]) (some (0, 6, 3)) (some (0, 6, 3))
      fan42Owner6Part0)))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem checked42 : StepValid model42 9000000000000 step42 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded42_0
    · exact excluded42_1
    · exact excluded42_2
    · exact excluded42_3
    · exact excluded42_4
    · exact excluded42_5
    · exact excluded42_6
    · exact excluded42_7
    · exact excluded42_8
    · exact (hj rfl).elim
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded43_0 : ExcludedOn (model43.B 0 ++ [step43.q]) 9000000000000 (model43.caps 0)
    (model43.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_2 : ExcludedOn (model43.B 2 ++ [step43.q]) 9000000000000 (model43.caps 2)
    (model43.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_3 : ExcludedOn (model43.B 3 ++ [step43.q]) 9000000000000 (model43.caps 3)
    (model43.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_4 : ExcludedOn (model43.B 4 ++ [step43.q]) 9000000000000 (model43.caps 4)
    (model43.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [390000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([3375000000000], [585000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([5640000000000, 0], [1170000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([2205000000000, -9000000000000], [585000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([3705000000000, -9000000000000], [1560000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([5055000000000], [3960000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([915000000000], [3765000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([375000000000], [4875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5640000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-390000000000], [5265000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-585000000000], [3960000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([-1170000000000, -9000000000000], [6810000000000, 9000000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-585000000000, 0], [2790000000000, -9000000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1560000000000, -9000000000000], [5265000000000])
      (some (0, 2, 3)) (some (0, 4, 3)) (.next ([-3960000000000], [9015000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-3765000000000], [4680000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-4875000000000], [5250000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some
      (0, 4, 0)) (some (0, 4, 0)) (some (0, 4, 0))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_7 : ExcludedOn (model43.B 7 ++ [step43.q]) 9000000000000 (model43.caps 7)
    (model43.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_8 : ExcludedOn (model43.B 8 ++ [step43.q]) 9000000000000 (model43.caps 8)
    (model43.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_9 : ExcludedOn (model43.B 9 ++ [step43.q]) 9000000000000 (model43.caps 9)
    (model43.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3735000000000], [1890000000000]) (some (3, 0,
      1)) (some (3, 1, 2)) (.next ([3960000000000], [5625000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([2070000000000], [5625000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [5625000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-1890000000000], [5625000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5625000000000], [9585000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-5625000000000], [7695000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked43 : StepValid model43 9000000000000 step43 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded43_0
    · exact excluded43_1
    · exact excluded43_2
    · exact excluded43_3
    · exact excluded43_4
    · exact excluded43_5
    · exact (hj rfl).elim
    · exact excluded43_7
    · exact excluded43_8
    · exact excluded43_9
theorem next43 : model43.insert step43 = model44 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded44_0 : ExcludedOn (model44.B 0 ++ [step44.q]) 9000000000000 (model44.caps 0)
    (model44.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5655000000000], [390000000000]) (some (7, 1, 8))
      (some (7, 1, 8)) (.next ([4785000000000], [390000000000]) (some (7, 1, 8)) (some (7, 1, 8))
      (.next ([7800000000000], [810000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next
      ([5610000000000], [615000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([5985000000000],
      [735000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([5545800000000, 5160000000000],
      [834600000000, -2580000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([4675800000000,
      5160000000000], [834600000000, -2580000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next
      ([4875000000000], [975000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([5250000000000],
      [1095000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([5235000000000], [1545000000000])
      (some (7, 1, 8)) (some (7, 2, 8)) (.next ([375000000000], [120000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([930000000000], [315000000000]) (some (7, 2, 8)) (some (7, 2, 8))
      (.next ([4365000000000], [1545000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([4500000000000], [1905000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([3630000000000],
      [1905000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([735000000000], [420000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([555000000000], [375000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) fan44Owner0Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_2 : ExcludedOn (model44.B 2 ++ [step44.q]) 9000000000000 (model44.caps 2)
    (model44.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_3 : ExcludedOn (model44.B 3 ++ [step44.q]) 9000000000000 (model44.caps 3)
    (model44.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_4 : ExcludedOn (model44.B 4 ++ [step44.q]) 9000000000000 (model44.caps 4)
    (model44.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_5 : ExcludedOn (model44.B 5 ++ [step44.q]) 9000000000000 (model44.caps 5)
    (model44.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_6 : ExcludedOn (model44.B 6 ++ [step44.q]) 9000000000000 (model44.caps 6)
    (model44.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5985000000000, 9000000000000], [390000000000,
      -9000000000000]) (some (6, 0, 2)) (some (6, 0, 3)) (.next ([5625000000000], [585000000000,
      9000000000000]) (some (6, 0, 3)) (some (6, 0, 3)) (.next ([4125000000000], [780000000000])
      (some (6, 0, 3)) (some (6, 0, 3)) (.next ([3825000000000], [1170000000000]) (some (6, 0, 3))
      (some (6, 0, 3)) (.next ([4815000000000], [1560000000000]) (some (6, 0, 3)) (some (6, 0, 3))
      (.next ([3645000000000, -9000000000000], [1560000000000]) (some (6, 0, 3)) (some (6, 0, 3))
      (.next ([3345000000000], [2250000000000]) (some (6, 0, 3)) (some (6, 0, 6)) (.next
      ([3435000000000], [2550000000000]) (some (4, 0, 6)) (some (4, 0, 6)) (.next ([2655000000000,
      -9000000000000], [2340000000000, 9000000000000]) (some (4, 0, 6)) (some (4, 0, 6)) (.next
      ([1170000000000, 9000000000000], [1170000000000, 9000000000000]) (some (4, 0, 6)) (some (4, 0,
      6)) (.next ([4065000000000], [5790000000000]) (some (4, 0, 6)) (some (4, 0, 6))
      fan44Owner6Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_7 : ExcludedOn (model44.B 7 ++ [step44.q]) 9000000000000 (model44.caps 7)
    (model44.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_8 : ExcludedOn (model44.B 8 ++ [step44.q]) 9000000000000 (model44.caps 8)
    (model44.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_9 : ExcludedOn (model44.B 9 ++ [step44.q]) 9000000000000 (model44.caps 9)
    (model44.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked44 : StepValid model44 9000000000000 step44 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded44_0
    · exact (hj rfl).elim
    · exact excluded44_2
    · exact excluded44_3
    · exact excluded44_4
    · exact excluded44_5
    · exact excluded44_6
    · exact excluded44_7
    · exact excluded44_8
    · exact excluded44_9
theorem next44 : model44.insert step44 = model45 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded45_0 : ExcludedOn (model45.B 0 ++ [step45.q]) 9000000000000 (model45.caps 0)
    (model45.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_2 : ExcludedOn (model45.B 2 ++ [step45.q]) 9000000000000 (model45.caps 2)
    (model45.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_3 : ExcludedOn (model45.B 3 ++ [step45.q]) 9000000000000 (model45.caps 3)
    (model45.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_4 : ExcludedOn (model45.B 4 ++ [step45.q]) 9000000000000 (model45.caps 4)
    (model45.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_5 : ExcludedOn (model45.B 5 ++ [step45.q]) 9000000000000 (model45.caps 5)
    (model45.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_6 : ExcludedOn (model45.B 6 ++ [step45.q]) 9000000000000 (model45.caps 6)
    (model45.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4905000000000], [255000000000]) (some (6, 0, 2))
      (some (6, 0, 6)) (.next ([4995000000000], [555000000000]) (some (4, 0, 6)) (some (4, 0, 6))
      (.next ([4125000000000], [780000000000]) (some (4, 0, 6)) (some (4, 0, 6)) (.next
      ([3825000000000], [1170000000000]) (some (4, 0, 6)) (some (4, 0, 6)) (.next ([5625000000000],
      [3795000000000]) (some (4, 0, 6)) (some (4, 0, 6)) fan45Owner6Part0))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_7 : ExcludedOn (model45.B 7 ++ [step45.q]) 9000000000000 (model45.caps 7)
    (model45.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_8 : ExcludedOn (model45.B 8 ++ [step45.q]) 9000000000000 (model45.caps 8)
    (model45.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_9 : ExcludedOn (model45.B 9 ++ [step45.q]) 9000000000000 (model45.caps 9)
    (model45.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked45 : StepValid model45 9000000000000 step45 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded45_0
    · exact (hj rfl).elim
    · exact excluded45_2
    · exact excluded45_3
    · exact excluded45_4
    · exact excluded45_5
    · exact excluded45_6
    · exact excluded45_7
    · exact excluded45_8
    · exact excluded45_9
theorem next45 : model45.insert step45 = model46 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded46_1 : ExcludedOn (model46.B 1 ++ [step46.q]) 9000000000000 (model46.caps 1)
    (model46.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_2 : ExcludedOn (model46.B 2 ++ [step46.q]) 9000000000000 (model46.caps 2)
    (model46.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7830000000000, -9000000000000], [1170000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1980000000000], [375000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5475000000000, -9000000000000], [1980000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([810000000000, -9000000000000], [1545000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1170000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1170000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-375000000000],
      [2355000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1980000000000, 0],
      [7455000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1545000000000,
      -9000000000000], [2355000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_3 : ExcludedOn (model46.B 3 ++ [step46.q]) 9000000000000 (model46.caps 3)
    (model46.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2355000000000], [180000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([6840000000000], [1170000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([6465000000000], [1545000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([1170000000000], [375000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([2355000000000], [7020000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([1185000000000,
      -9000000000000], [8190000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([810000000000], [8190000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [1170000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 4, 4)) (.next ([-180000000000],
      [2535000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-1170000000000, -9000000000000],
      [8010000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1545000000000],
      [8010000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-375000000000], [1545000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-7020000000000], [9375000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-8190000000000, -9000000000000], [9375000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-8190000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_4 : ExcludedOn (model46.B 4 ++ [step46.q]) 9000000000000 (model46.caps 4)
    (model46.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_5 : ExcludedOn (model46.B 5 ++ [step46.q]) 9000000000000 (model46.caps 5)
    (model46.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_6 : ExcludedOn (model46.B 6 ++ [step46.q]) 9000000000000 (model46.caps 6)
    (model46.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_7 : ExcludedOn (model46.B 7 ++ [step46.q]) 9000000000000 (model46.caps 7)
    (model46.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_8 : ExcludedOn (model46.B 8 ++ [step46.q]) 9000000000000 (model46.caps 8)
    (model46.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_9 : ExcludedOn (model46.B 9 ++ [step46.q]) 9000000000000 (model46.caps 9)
    (model46.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked46 : StepValid model46 9000000000000 step46 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded46_1
    · exact excluded46_2
    · exact excluded46_3
    · exact excluded46_4
    · exact excluded46_5
    · exact excluded46_6
    · exact excluded46_7
    · exact excluded46_8
    · exact excluded46_9
theorem next46 : model46.insert step46 = model47 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded47_1 : ExcludedOn (model47.B 1 ++ [step47.q]) 9000000000000 (model47.caps 1)
    (model47.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4620000000000, 0], [1170000000000,
      9000000000000]) (some (4, 1, 1)) (some (4, 1, 2)) (.next ([4440000000000], [1560000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3270000000000, -9000000000000], [1560000000000, 0])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1560000000000], [2625000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([2625000000000], [4440000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3060000000000], [6000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([435000000000], [1560000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([390000000000,
      -9000000000000], [3795000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([0], [4620000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1170000000000,
      -9000000000000], [5790000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next
      ([-1560000000000], [6000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-1560000000000,
      0], [4830000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-2625000000000], [4185000000000]) (some (4, 1, 3)) none (.next ([-4440000000000],
      [7065000000000]) none none (.next ([-6000000000000], [9060000000000]) none none (.next
      ([-1560000000000], [1995000000000]) none none (.next ([-3795000000000, -9000000000000],
      [4185000000000, 0]) none none (.terminal none (some (1, 1, 4)) none))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_2 : ExcludedOn (model47.B 2 ++ [step47.q]) 9000000000000 (model47.caps 2)
    (model47.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7830000000000, -9000000000000], [1170000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3270000000000, -9000000000000],
      [1560000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1560000000000],
      [3000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([390000000000, -9000000000000],
      [4170000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1170000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1170000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next
      ([-1560000000000, 0], [4830000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-3000000000000], [4560000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-4170000000000, -9000000000000], [4560000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_3 : ExcludedOn (model47.B 3 ++ [step47.q]) 9000000000000 (model47.caps 3)
    (model47.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_4 : ExcludedOn (model47.B 4 ++ [step47.q]) 9000000000000 (model47.caps 4)
    (model47.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_5 : ExcludedOn (model47.B 5 ++ [step47.q]) 9000000000000 (model47.caps 5)
    (model47.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_6 : ExcludedOn (model47.B 6 ++ [step47.q]) 9000000000000 (model47.caps 6)
    (model47.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_7 : ExcludedOn (model47.B 7 ++ [step47.q]) 9000000000000 (model47.caps 7)
    (model47.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_8 : ExcludedOn (model47.B 8 ++ [step47.q]) 9000000000000 (model47.caps 8)
    (model47.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_9 : ExcludedOn (model47.B 9 ++ [step47.q]) 9000000000000 (model47.caps 9)
    (model47.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked47 : StepValid model47 9000000000000 step47 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded47_1
    · exact excluded47_2
    · exact excluded47_3
    · exact excluded47_4
    · exact excluded47_5
    · exact excluded47_6
    · exact excluded47_7
    · exact excluded47_8
    · exact excluded47_9
theorem next47 : model47.insert step47 = model48 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint130000140000
end ConwaySoifer.Simplified.Certificates
