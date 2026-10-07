/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext230000240000
import Mathlib.Tactic.FinCases

/-!
# Sext 230000 240000 1

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
namespace Sext230000240000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part0 : FanWitness := (.next ([-6210000000000], [8910000000000]) (some (3, 14, 9))
    (some (3, 14, 9)) (.next ([-6075000000000], [8625000000000]) (some (3, 14, 9)) (some (3, 14, 9))
    (.next ([-750000000000], [1035000000000]) (some (3, 14, 9)) (some (14, 14, 9)) (.next
    ([-1424400000000, -2280000000000], [1948800000000, 4560000000000]) (some (14, 14, 9)) (some (14,
    14, 9)) (.next ([-3135000000000], [4200000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next
    ([-525000000000], [690000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-3000000000000],
    [3720000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-1410000000000], [1725000000000])
    (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-615000000000], [750000000000]) (some (14, 5, 9))
    (some (14, 5, 9)) (.next ([-1065000000000], [1275000000000]) (some (14, 5, 9)) (some (14, 5, 9))
    (.next ([-1500000000000], [1755000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-5205000000000], [6060000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-1035000000000], [1185000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-5520000000000], [6315000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-5895000000000], [6525000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-1589400000000,
    -2280000000000], [1738800000000, 4560000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-375000000000], [405000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-5550000000000],
    [5925000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-6270000000000], [6690000000000])
    (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-5865000000000], [6180000000000]) (some (14, 5, 9))
    (some (14, 5, 9)) (.next ([-1350000000000], [1410000000000]) (some (14, 5, 9)) (some (14, 5, 9))
    (.next ([-6240000000000], [6390000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-6585000000000], [6690000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-6645000000000], [6660000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.terminal (some (14, 5,
    9)) (some (14, 5, 9)) (some (14, 5, 9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part1 : FanWitness := (.next ([-435000000000], [1065000000000]) (some (1, 14, 7))
    (some (1, 14, 7)) (.next ([-540600000000, 2280000000000], [1214400000000, 2280000000000]) (some
    (1, 14, 7)) (some (1, 14, 7)) (.next ([-135000000000], [285000000000]) (some (1, 14, 7)) (some
    (1, 14, 7)) (.next ([-315000000000], [660000000000]) (some (1, 14, 8)) (some (2, 14, 8)) (.next
    ([-4485000000000], [9060000000000]) (some (2, 14, 8)) (some (2, 14, 8)) (.next ([-690000000000],
    [1380000000000]) (some (2, 14, 8)) (some (2, 14, 8)) (.next ([-4800000000000], [9315000000000])
    (some (2, 14, 8)) (some (2, 14, 8)) (.next ([-345000000000], [660000000000]) (some (2, 14, 8))
    (some (2, 14, 8)) (.next ([-780000000000], [1440000000000]) (some (2, 14, 8)) (some (2, 14, 8))
    (.next ([-5175000000000], [9525000000000]) (some (2, 14, 8)) (some (2, 14, 8)) (.next
    ([-750000000000], [1380000000000]) (some (2, 14, 8)) (some (2, 14, 8)) (.next ([-210000000000],
    [375000000000]) (some (2, 14, 8)) (some (2, 14, 8)) (.next ([-5550000000000], [9690000000000])
    (some (2, 14, 8)) (some (2, 14, 9)) (.next ([-1214400000000, -2280000000000], [2113800000000,
    4560000000000]) (some (2, 14, 9)) (some (2, 14, 9)) (.next ([-840000000000], [1440000000000])
    (some (2, 14, 9)) (some (2, 14, 9)) (.next ([-5865000000000], [9690000000000]) (some (2, 14, 9))
    (some (2, 14, 9)) (.next ([-5925000000000], [9660000000000]) (some (2, 14, 9)) (some (2, 14, 9))
    (.next ([-690000000000], [1065000000000]) (some (2, 14, 9)) (some (2, 14, 9)) (.next
    ([-6210000000000], [9375000000000]) (some (2, 14, 9)) (some (2, 14, 9)) (.next ([-60000000000],
    [90000000000]) (some (2, 14, 9)) (some (2, 14, 9)) (.next ([-1065000000000], [1590000000000])
    (some (2, 14, 9)) (some (2, 14, 9)) (.next ([-6240000000000], [9315000000000]) (some (2, 14, 9))
    (some (2, 14, 9)) (.next ([-660000000000], [975000000000]) (some (2, 14, 9)) (some (2, 14, 9))
    (.next ([-6240000000000], [9000000000000]) (some (2, 14, 9)) (some (3, 14, 9))
    fan15Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part2 : FanWitness := (.next ([-225600000000, 2280000000000], [1559400000000,
    2280000000000]) (some (0, 14, 6)) (some (0, 14, 6)) (.next ([-1020000000000], [6930000000000])
    (some (0, 14, 6)) (some (0, 14, 6)) (.next ([-1125000000000], [7305000000000]) (some (0, 14, 6))
    (some (0, 14, 6)) (.next ([-210000000000], [1275000000000]) (some (0, 14, 6)) (some (0, 14, 6))
    (.next ([-1170000000000], [6795000000000]) (some (0, 14, 6)) (some (0, 14, 6)) (.next
    ([-315000000000], [1755000000000]) (some (0, 14, 6)) (some (0, 14, 6)) (.next ([-135000000000],
    [750000000000]) (some (0, 14, 6)) (some (0, 14, 6)) (.next ([-60000000000], [315000000000])
    (some (0, 14, 6)) (some (0, 14, 6)) (.next ([-1440000000000], [7305000000000]) (some (0, 14, 6))
    (some (0, 14, 7)) (.next ([-1500000000000], [7275000000000]) (some (0, 14, 7)) (some (0, 14, 7))
    (.next ([-435000000000], [2025000000000]) (some (0, 14, 7)) (some (0, 14, 7)) (.next
    ([-405000000000], [1815000000000]) (some (0, 14, 7)) (some (0, 14, 7)) (.next ([-1650000000000],
    [7140000000000]) (some (0, 14, 7)) (some (0, 14, 7)) (.next ([-165000000000], [690000000000])
    (some (0, 14, 7)) (some (0, 14, 7)) (.next ([-1798800000000, -4560000000000], [6764400000000,
    2280000000000]) (some (0, 14, 7)) (some (0, 14, 7)) (.next ([-135000000000], [480000000000])
    (some (0, 14, 7)) (some (0, 14, 7)) (.next ([-315000000000], [975000000000]) (some (0, 14, 7))
    (some (0, 14, 7)) (.next ([-225000000000], [690000000000]) (some (0, 14, 7)) (some (0, 14, 7))
    (.next ([-525000000000], [1590000000000]) (some (0, 14, 7)) (some (0, 14, 7)) (.next
    ([-30000000000], [90000000000]) (some (0, 14, 7)) (some (0, 14, 7)) (.next ([-690000000000],
    [1965000000000]) (some (0, 14, 7)) (some (1, 14, 7)) (.next ([-375000000000], [1065000000000])
    (some (1, 14, 7)) (some (1, 14, 7)) (.next ([-615000000000], [1650000000000]) (some (1, 14, 7))
    (some (1, 14, 7)) (.next ([-510600000000, 2280000000000], [1274400000000, 2280000000000]) (some
    (1, 14, 7)) (some (1, 14, 7)) fan15Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part3 : FanWitness := (.next ([255000000000], [1500000000000]) (some (13, 14, 5))
    (some (13, 14, 5)) (.next ([855000000000], [5205000000000]) (some (13, 14, 5)) (some (13, 14,
    5)) (.next ([150000000000], [1035000000000]) (some (13, 14, 5)) (some (13, 14, 5)) (.next
    ([795000000000], [5520000000000]) (some (13, 14, 5)) (some (13, 14, 5)) (.next ([630000000000],
    [5895000000000]) (some (13, 14, 5)) (some (13, 14, 5)) (.next ([149400000000, 2280000000000],
    [1589400000000, 2280000000000]) (some (13, 14, 5)) (some (13, 14, 5)) (.next ([30000000000],
    [375000000000]) (some (13, 14, 5)) (some (13, 14, 5)) (.next ([375000000000], [5550000000000])
    (some (13, 14, 5)) (some (13, 14, 5)) (.next ([420000000000], [6270000000000]) (some (13, 14,
    5)) (some (13, 14, 6)) (.next ([315000000000], [5865000000000]) (some (13, 14, 6)) (some (13,
    14, 6)) (.next ([60000000000], [1350000000000]) (some (13, 14, 6)) (some (13, 14, 6)) (.next
    ([150000000000], [6240000000000]) (some (13, 14, 6)) (some (13, 14, 6)) (.next ([105000000000],
    [6585000000000]) (some (13, 14, 6)) (some (13, 14, 6)) (.next ([15000000000], [6645000000000])
    (some (13, 14, 6)) (some (13, 14, 6)) (.next ([0], [315000000000]) (some (13, 14, 6)) (some (13,
    14, 6)) (.next ([-60000000000], [6615000000000]) (some (0, 14, 6)) (some (0, 14, 6)) (.next
    ([-60000000000], [1815000000000]) (some (0, 14, 6)) (some (0, 14, 6)) (.next ([-375000000000],
    [6930000000000]) (some (0, 14, 6)) (some (0, 14, 6)) (.next ([-465000000000], [6990000000000])
    (some (0, 14, 6)) (some (0, 14, 6)) (.next ([-30000000000], [405000000000]) (some (0, 14, 6))
    (some (0, 14, 6)) (.next ([-150000000000], [1875000000000]) (some (0, 14, 6)) (some (0, 14, 6))
    (.next ([-555000000000], [6930000000000]) (some (0, 14, 6)) (some (0, 14, 6)) (.next
    ([-645000000000], [6960000000000]) (some (0, 14, 6)) (some (0, 14, 6)) (.next ([-150000000000],
    [1185000000000]) (some (0, 14, 6)) (some (0, 14, 6)) fan15Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part4 : FanWitness := (.next ([630000000000], [750000000000]) (some (12, 14, 5))
    (some (12, 14, 5)) (.next ([165000000000], [210000000000]) (some (12, 14, 5)) (some (12, 14, 5))
    (.next ([4140000000000], [5550000000000]) (some (12, 14, 5)) (some (12, 14, 5)) (.next
    ([899400000000, 2280000000000], [1214400000000, 2280000000000]) (some (12, 14, 5)) (some (12,
    14, 5)) (.next ([600000000000], [840000000000]) (some (12, 14, 5)) (some (12, 14, 5)) (.next
    ([3825000000000], [5865000000000]) (some (12, 14, 5)) (some (12, 14, 5)) (.next
    ([3735000000000], [5925000000000]) (some (12, 14, 5)) (some (12, 14, 5)) (.next ([375000000000],
    [690000000000]) (some (12, 14, 5)) (some (12, 14, 5)) (.next ([3165000000000], [6210000000000])
    (some (12, 14, 5)) (some (12, 14, 5)) (.next ([30000000000], [60000000000]) (some (12, 14, 5))
    (some (12, 14, 5)) (.next ([525000000000], [1065000000000]) (some (12, 14, 5)) (some (13, 14,
    5)) (.next ([3075000000000], [6240000000000]) (some (13, 14, 5)) (some (13, 14, 5)) (.next
    ([315000000000], [660000000000]) (some (13, 14, 5)) (some (13, 14, 5)) (.next ([2760000000000],
    [6240000000000]) (some (13, 14, 5)) (some (13, 14, 5)) (.next ([2700000000000], [6210000000000])
    (some (13, 14, 5)) (some (13, 14, 5)) (.next ([2550000000000], [6075000000000]) (some (13, 14,
    5)) (some (13, 14, 5)) (.next ([285000000000], [750000000000]) (some (13, 14, 5)) (some (13, 14,
    5)) (.next ([524400000000, 2280000000000], [1424400000000, 2280000000000]) (some (13, 14, 5))
    (some (13, 14, 5)) (.next ([1065000000000], [3135000000000]) (some (13, 14, 5)) (some (13, 14,
    5)) (.next ([165000000000], [525000000000]) (some (13, 14, 5)) (some (13, 14, 5)) (.next
    ([720000000000], [3000000000000]) (some (13, 14, 5)) (some (13, 14, 5)) (.next ([315000000000],
    [1410000000000]) (some (13, 14, 5)) (some (13, 14, 5)) (.next ([135000000000], [615000000000])
    (some (13, 14, 5)) (some (13, 14, 5)) (.next ([210000000000], [1065000000000]) (some (13, 14,
    5)) (some (13, 14, 5)) fan15Owner0Part3))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner0Part5 : FanWitness := (.next ([1590000000000], [435000000000]) (some (10, 14, 5))
    (some (10, 14, 5)) (.next ([1410000000000], [405000000000]) (some (10, 14, 5)) (some (10, 14,
    5)) (.next ([5490000000000], [1650000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next
    ([525000000000], [165000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next ([4965600000000,
    -2280000000000], [1798800000000, 4560000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next
    ([345000000000], [135000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next ([660000000000],
    [315000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next ([465000000000], [225000000000])
    (some (10, 14, 5)) (some (10, 14, 5)) (.next ([1065000000000], [525000000000]) (some (10, 14,
    5)) (some (10, 14, 5)) (.next ([60000000000], [30000000000]) (some (10, 14, 5)) (some (10, 14,
    5)) (.next ([1275000000000], [690000000000]) (some (10, 14, 5)) (some (11, 14, 5)) (.next
    ([690000000000], [375000000000]) (some (11, 14, 5)) (some (11, 14, 5)) (.next ([1035000000000],
    [615000000000]) (some (11, 14, 5)) (some (11, 14, 5)) (.next ([763800000000, 4560000000000],
    [510600000000, -2280000000000]) (some (11, 14, 5)) (some (11, 14, 5)) (.next ([630000000000],
    [435000000000]) (some (11, 14, 5)) (some (11, 14, 5)) (.next ([673800000000, 4560000000000],
    [540600000000, -2280000000000]) (some (11, 14, 5)) (some (11, 14, 5)) (.next ([150000000000],
    [135000000000]) (some (11, 14, 5)) (some (11, 14, 5)) (.next ([345000000000], [315000000000])
    (some (11, 14, 5)) (some (11, 14, 5)) (.next ([4575000000000], [4485000000000]) (some (11, 14,
    5)) (some (11, 14, 5)) (.next ([690000000000], [690000000000]) (some (11, 14, 5)) (some (11, 14,
    5)) (.next ([4515000000000], [4800000000000]) (some (11, 14, 5)) (some (12, 14, 5)) (.next
    ([315000000000], [345000000000]) (some (12, 14, 5)) (some (12, 14, 5)) (.next ([660000000000],
    [780000000000]) (some (12, 14, 5)) (some (12, 14, 5)) (.next ([4350000000000], [5175000000000])
    (some (12, 14, 5)) (some (12, 14, 5)) fan15Owner0Part4))))))))))))))))))))))))

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6930000000000, -9000000000000], [1170000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2070000000000, 9000000000000],
      [2070000000000, 9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([2970000000000,
      9000000000000], [6030000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([900000000000], [8100000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [2070000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1170000000000,
      -9000000000000], [8100000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-2070000000000, -9000000000000], [4140000000000, 18000000000000]) (some (3, 1, 0)) (some (3,
      1, 0)) (.next ([-6030000000000, 9000000000000], [9000000000000]) (some (3, 1, 0)) (some (3, 1,
      0)) (.next ([-8100000000000], [9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal
      (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6030000000000, -9000000000000], [2070000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2070000000000, 9000000000000],
      [2070000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2070000000000,
      9000000000000], [6030000000000, -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0,
      0], [2070000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-2070000000000,
      -9000000000000], [8100000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([-2070000000000,
      -9000000000000], [4140000000000, 18000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next
      ([-6030000000000, 9000000000000], [8100000000000, 0]) (some (3, 3, 2)) (some (3, 3, 2))
      (.terminal (some (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8100000000000], [900000000000]) (some (1, 0, 3))
      (some (2, 0, 3)) (.next ([6030000000000, -9000000000000], [2970000000000, 9000000000000])
      (some (2, 0, 3)) (some (2, 0, 3)) (.next ([2070000000000, 9000000000000], [2070000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 3, 3)) (.next ([1170000000000, 9000000000000],
      [6930000000000, -9000000000000]) (some (2, 3, 3)) (some (2, 3, 3)) (.next ([0],
      [2070000000000, 9000000000000]) (some (2, 3, 1)) (some (2, 3, 1)) (.next ([-900000000000],
      [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-2970000000000, -9000000000000],
      [9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-2070000000000, -9000000000000],
      [4140000000000, 18000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-6930000000000,
      9000000000000], [8100000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3, 1))
      (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_4 : ExcludedOn (model8.B 4 ++ [step8.q]) 9000000000000 (model8.caps 4) (model8.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded8_1
    · exact excluded8_2
    · exact excluded8_3
    · exact excluded8_4
    · exact excluded8_5
    · exact excluded8_6
    · exact excluded8_7
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6555000000000, -9000000000000], [1380000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2070000000000, 9000000000000],
      [2070000000000, 9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([2760000000000,
      9000000000000], [5865000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([690000000000], [7935000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [2070000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1380000000000,
      -9000000000000], [7935000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-2070000000000, -9000000000000], [4140000000000, 18000000000000]) (some (3, 1, 0)) (some (3,
      1, 0)) (.next ([-5865000000000, 9000000000000], [8625000000000]) (some (3, 1, 0)) (some (3, 1,
      0)) (.next ([-7935000000000], [8625000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal
      (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7935000000000], [375000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([5865000000000, -9000000000000], [2445000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2070000000000, 9000000000000], [2070000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1695000000000, 9000000000000],
      [6240000000000, -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0],
      [2070000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-375000000000],
      [8310000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([-2445000000000, -9000000000000],
      [8310000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2070000000000, -9000000000000],
      [4140000000000, 18000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-6240000000000,
      9000000000000], [7935000000000, 0]) (some (3, 3, 2)) (some (3, 3, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8310000000000], [1065000000000]) (some (1, 0,
      3)) (some (2, 0, 3)) (.next ([6240000000000, -9000000000000], [3135000000000, 9000000000000])
      (some (2, 0, 3)) (some (2, 0, 3)) (.next ([2070000000000, 9000000000000], [2070000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 3, 3)) (.next ([1005000000000, 9000000000000],
      [7305000000000, -9000000000000]) (some (2, 3, 3)) (some (2, 3, 3)) (.next ([0],
      [2070000000000, 9000000000000]) (some (2, 3, 1)) (some (2, 3, 1)) (.next ([-1065000000000],
      [9375000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-3135000000000, -9000000000000],
      [9375000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-2070000000000, -9000000000000],
      [4140000000000, 18000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-7305000000000,
      9000000000000], [8310000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3, 1))
      (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded9_1
    · exact excluded9_2
    · exact excluded9_3
    · exact excluded9_4
    · exact excluded9_5
    · exact excluded9_6
    · exact excluded9_7
    · exact excluded9_8
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6240000000000, -9000000000000], [1635000000000,
      9000000000000]) (some (0, 3, 1)) none (.next ([2070000000000, 9000000000000], [2070000000000,
      9000000000000]) none none (.next ([2505000000000, 9000000000000], [5805000000000,
      -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next ([435000000000], [7875000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [2070000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([-1635000000000, -9000000000000], [7875000000000, 0]) (some (3,
      1, 0)) (some (3, 1, 0)) (.next ([-2070000000000, -9000000000000], [4140000000000,
      18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-5805000000000, 9000000000000],
      [8310000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7875000000000], [8310000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1,
      0))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7875000000000], [690000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([5805000000000, -9000000000000], [2760000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2070000000000, 9000000000000], [2070000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1380000000000, 9000000000000],
      [6495000000000, -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0],
      [2070000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-690000000000],
      [8565000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([-2760000000000, -9000000000000],
      [8565000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2070000000000, -9000000000000],
      [4140000000000, 18000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-6495000000000,
      9000000000000], [7875000000000, 0]) (some (3, 3, 2)) (some (3, 3, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3195000000000, 9000000000000], [6240000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2505000000000, 9000000000000],
      [5805000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2070000000000,
      9000000000000], [6930000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([1125000000000], [8310000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [2070000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-6240000000000,
      9000000000000], [9435000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-5805000000000,
      9000000000000], [8310000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6930000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next
      ([-8310000000000], [9435000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded10_1
    · exact excluded10_2
    · exact excluded10_3
    · exact excluded10_4
    · exact excluded10_5
    · exact excluded10_6
    · exact excluded10_7
    · exact excluded10_8
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2070000000000, 9000000000000], [2070000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([3105000000000], [3555000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3105000000000], [5625000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1035000000000, -9000000000000], [7695000000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [2070000000000, 9000000000000]) none
      none (.next ([-2070000000000, -9000000000000], [4140000000000, 18000000000000]) none none
      (.next ([-3555000000000, 9000000000000], [6660000000000, -9000000000000]) (some (3, 3, 0))
      (some (3, 3, 0)) (.next ([-5625000000000], [8730000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-7695000000000, -9000000000000], [8730000000000, 0]) (some (3, 1, 0)) (some (3, 1,
      0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_3 : ExcludedOn (model11.B 3 ++ [step11.q]) 9000000000000 (model11.caps 3)
    (model11.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_4 : ExcludedOn (model11.B 4 ++ [step11.q]) 9000000000000 (model11.caps 4)
    (model11.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7965000000000, 9000000000000], [1305000000000,
      -9000000000000]) (some (3, 0, 3)) (some (3, 1, 3)) (.next ([5895000000000], [3375000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3825000000000, -9000000000000], [3375000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2070000000000, 9000000000000], [2070000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0], [2070000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1305000000000, 9000000000000],
      [9270000000000, 0]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-3375000000000],
      [9270000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3375000000000, 0],
      [7200000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2070000000000,
      -9000000000000], [4140000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 3, 3)) (.terminal
      (some (0, 3, 3)) (some (0, 3, 3)) (some (0, 3, 3))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2340000000000, 9000000000000], [1035000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([3105000000000], [3555000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([2070000000000, 9000000000000],
      [6930000000000, -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([270000000000],
      [3105000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2070000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1035000000000, 9000000000000],
      [3375000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3555000000000, 9000000000000],
      [6660000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6930000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3105000000000], [3375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded11_1
    · exact excluded11_2
    · exact excluded11_3
    · exact excluded11_4
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
  apply ExclusionHint.sound (.witnessedFan (.next ([2070000000000, 9000000000000], [2070000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2760000000000], [3420000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2760000000000], [5490000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([690000000000, -9000000000000], [7560000000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [2070000000000, 9000000000000]) none
      none (.next ([-2070000000000, -9000000000000], [4140000000000, 18000000000000]) none none
      (.next ([-3420000000000, 9000000000000], [6180000000000, -9000000000000]) (some (3, 3, 0))
      (some (3, 3, 0)) (.next ([-5490000000000], [8250000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-7560000000000, -9000000000000], [8250000000000, 0]) (some (3, 1, 0)) (some (3, 1,
      0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_3 : ExcludedOn (model12.B 3 ++ [step12.q]) 9000000000000 (model12.caps 3)
    (model12.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_4 : ExcludedOn (model12.B 4 ++ [step12.q]) 9000000000000 (model12.caps 4)
    (model12.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2820000000000, 9000000000000], [690000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2760000000000], [3420000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([2070000000000, 9000000000000],
      [6930000000000, -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([750000000000],
      [2760000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2070000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-690000000000, 9000000000000],
      [3510000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3420000000000, 9000000000000],
      [6180000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6930000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2760000000000], [3510000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 14) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_6 : ExcludedOn (model13.B 6 ++ [step13.q]) 9000000000000 (model13.caps 6)
    (model13.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1155000000000, 0], [195000000000,
      9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([720000000000], [1155000000000])
      (some (2, 0, 2)) (some (2, 3, 2)) (.next ([2070000000000, 9000000000000], [6930000000000,
      -9000000000000]) (some (2, 3, 2)) (some (2, 3, 2)) (.next ([720000000000], [8085000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [2070000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-195000000000, -9000000000000],
      [1350000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-1155000000000],
      [1875000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-6930000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-8085000000000, 9000000000000],
      [8805000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2))
      (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_7 : ExcludedOn (model13.B 7 ++ [step13.q]) 9000000000000 (model13.caps 7)
    (model13.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_8 : ExcludedOn (model13.B 8 ++ [step13.q]) 9000000000000 (model13.caps 8)
    (model13.ord 8) 0 1 100 := by
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
    · exact excluded13_8
    · exact (hj rfl).elim
theorem next13 : model13.insert step13 = model14 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded14_0 : ExcludedOn (model14.B 0 ++ [step14.q]) 9000000000000 (model14.caps 0)
    (model14.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 14) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1320000000000, 0], [750000000000,
      9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2070000000000, 9000000000000],
      [6930000000000, -9000000000000]) (some (2, 0, 2)) (some (2, 3, 2)) (.next ([0, 0],
      [2070000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-750000000000,
      -9000000000000], [2070000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-6930000000000, 9000000000000], [9000000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2))
      (.terminal (some (0, 3, 2)) (some (0, 1, 2)) (some (0, 3, 2))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_7 : ExcludedOn (model14.B 7 ++ [step14.q]) 9000000000000 (model14.caps 7)
    (model14.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_8 : ExcludedOn (model14.B 8 ++ [step14.q]) 9000000000000 (model14.caps 8)
    (model14.ord 8) 0 1 100 := by
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
    · exact excluded14_8
    · exact (hj rfl).elim
theorem next14 : model14.insert step14 = model15 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded15_0 : ExcludedOn (model15.B 0 ++ [step15.q]) 9000000000000 (model15.caps 0)
    (model15.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6555000000000], [60000000000]) (some (9, 14, 5))
      (some (10, 14, 5)) (.next ([1755000000000], [60000000000]) (some (10, 14, 5)) (some (10, 14,
      5)) (.next ([6555000000000], [375000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next
      ([6525000000000], [465000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next
      ([375000000000], [30000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next ([1725000000000],
      [150000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next ([6375000000000], [555000000000])
      (some (10, 14, 5)) (some (10, 14, 5)) (.next ([6315000000000], [645000000000]) (some (10, 14,
      5)) (some (10, 14, 5)) (.next ([1035000000000], [150000000000]) (some (10, 14, 5)) (some (10,
      14, 5)) (.next ([1333800000000, 4560000000000], [225600000000, -2280000000000]) (some (10, 14,
      5)) (some (10, 14, 5)) (.next ([5910000000000], [1020000000000]) (some (10, 14, 5)) (some (10,
      14, 5)) (.next ([6180000000000], [1125000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next
      ([1065000000000], [210000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next
      ([5625000000000], [1170000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next
      ([1440000000000], [315000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next
      ([615000000000], [135000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next ([255000000000],
      [60000000000]) (some (10, 14, 5)) (some (10, 14, 5)) (.next ([5865000000000], [1440000000000])
      (some (10, 14, 5)) (some (10, 14, 5)) (.next ([5775000000000], [1500000000000]) (some (10, 14,
      5)) (some (10, 14, 5)) fan15Owner0Part5))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_7 : ExcludedOn (model15.B 7 ++ [step15.q]) 9000000000000 (model15.caps 7)
    (model15.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_8 : ExcludedOn (model15.B 8 ++ [step15.q]) 9000000000000 (model15.caps 8)
    (model15.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_9 : ExcludedOn (model15.B 9 ++ [step15.q]) 9000000000000 (model15.caps 9)
    (model15.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7125000000000], [720000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([5550000000000, 0], [1755000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([5550000000000], [3825000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([1530000000000], [1575000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1695000000000], [2130000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2070000000000,
      9000000000000], [5610000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([165000000000], [555000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1350000000000,
      9000000000000], [5775000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0,
      0], [2070000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-720000000000],
      [7845000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-1755000000000, 9000000000000],
      [7305000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-3825000000000],
      [9375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1575000000000], [3105000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2130000000000], [3825000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-5610000000000, 9000000000000], [7680000000000, 0]) (some (0, 1, 2))
      (some (0, 1, 4)) (.next ([-555000000000], [720000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-5775000000000, 9000000000000], [7125000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded15_6
    · exact excluded15_7
    · exact excluded15_8
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext230000240000
end ConwaySoifer.Simplified.Certificates
