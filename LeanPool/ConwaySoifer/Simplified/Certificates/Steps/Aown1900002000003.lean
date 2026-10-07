/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown190000200000
import Mathlib.Tactic.FinCases

/-!
# Aown 190000 200000 3

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
namespace Aown190000200000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part0 : FanWitness := (.next ([-570000000000], [945000000000]) (some (12, 6, 10))
    (some (12, 6, 10)) (.next ([-4845000000000], [7845000000000]) (some (12, 6, 10)) (some (12, 6,
    10)) (.next ([-570000000000], [885000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-5040000000000], [7665000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-390000000000], [570000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-5220000000000], [7470000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-945000000000], [1335000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-5220000000000], [7275000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-810000000000], [1095000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-5580000000000], [7260000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-5010000000000], [6375000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-5205000000000], [6570000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-945000000000], [1140000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-2220000000000], [2625000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-5955000000000], [6945000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-1320000000000], [1515000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-3435000000000], [3900000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6150000000000], [6945000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-1410000000000], [1530000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-2625000000000], [2805000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6345000000000], [6765000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-1215000000000], [1275000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6810000000000], [7005000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6525000000000], [6570000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.terminal (some (12,
    6, 10)) (some (12, 6, 10)) (some (12, 6, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part1 : FanWitness := (.next ([-2430000000000], [7215000000000]) (some (12, 6, 9))
    (some (12, 6, 9)) (.next ([-2415000000000], [7095000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    (.next ([-2625000000000], [7410000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-315000000000], [885000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-3000000000000],
    [8100000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-495000000000], [1260000000000])
    (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-375000000000], [945000000000]) (some (12, 6, 9))
    (some (12, 6, 9)) (.next ([-900000000000], [2205000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    (.next ([-690000000000], [1635000000000]) (some (12, 6, 9)) (some (12, 6, 10)) (.next
    ([-3375000000000], [7785000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-315000000000], [690000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-3570000000000], [7785000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-180000000000], [375000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next ([-885000000000],
    [1830000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next ([-3765000000000],
    [7605000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next ([-375000000000], [750000000000])
    (some (12, 6, 10)) (some (12, 6, 10)) (.next ([-3705000000000], [7275000000000]) (some (12, 6,
    10)) (some (12, 6, 10)) (.next ([-195000000000], [375000000000]) (some (12, 6, 10)) (some (12,
    6, 10)) (.next ([-3900000000000], [7470000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-4275000000000], [8160000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-3945000000000], [7410000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-375000000000], [690000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-3945000000000], [7215000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-4650000000000], [7845000000000]) (some (12, 6, 10)) (some (12, 6, 10))
    fan24Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part2 : FanWitness := (.next ([420000000000], [6345000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([60000000000], [1215000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([195000000000], [6810000000000]) (some (12, 4, 8)) (some (12, 4, 9)) (.next
    ([45000000000], [6525000000000]) (some (12, 4, 9)) (some (12, 4, 9)) (.next ([0],
    [1320000000000]) (some (12, 4, 9)) (some (12, 4, 9)) (.next ([-150000000000], [6525000000000])
    (some (12, 4, 9)) (some (12, 5, 9)) (.next ([-375000000000], [7695000000000]) (some (12, 5, 9))
    (some (12, 5, 9)) (.next ([-435000000000], [5640000000000]) (some (12, 5, 9)) (some (12, 5, 9))
    (.next ([-750000000000], [7380000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next
    ([-900000000000], [7095000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next ([-945000000000],
    [7380000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next ([-195000000000], [1515000000000])
    (some (12, 5, 9)) (some (12, 5, 9)) (.next ([-720000000000], [4830000000000]) (some (12, 5, 9))
    (some (12, 5, 9)) (.next ([-1095000000000], [7290000000000]) (some (12, 5, 9)) (some (12, 5, 9))
    (.next ([-1140000000000], [7200000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next
    ([-1470000000000], [7980000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next
    ([-1320000000000], [7005000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next
    ([-1320000000000], [6810000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next
    ([-1845000000000], [7665000000000]) (some (12, 5, 9)) (some (12, 6, 9)) (.next ([-840000000000],
    [3420000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-2040000000000], [7665000000000])
    (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-2235000000000], [7485000000000]) (some (12, 6, 9))
    (some (12, 6, 9)) (.next ([-180000000000], [570000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    (.next ([-2415000000000], [7290000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    fan24Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part3 : FanWitness := (.next ([3465000000000], [3945000000000]) (some (10, 4, 6))
    (some (10, 4, 6)) (.next ([315000000000], [375000000000]) (some (10, 4, 6)) (some (10, 4, 6))
    (.next ([3270000000000], [3945000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next
    ([3195000000000], [4650000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next ([375000000000],
    [570000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next ([3000000000000], [4845000000000])
    (some (10, 4, 6)) (some (10, 4, 6)) (.next ([315000000000], [570000000000]) (some (10, 4, 6))
    (some (10, 4, 6)) (.next ([2625000000000], [5040000000000]) (some (10, 4, 6)) (some (10, 4, 6))
    (.next ([180000000000], [390000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next
    ([2250000000000], [5220000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next ([390000000000],
    [945000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next ([2055000000000], [5220000000000])
    (some (10, 4, 6)) (some (10, 4, 6)) (.next ([285000000000], [810000000000]) (some (10, 4, 6))
    (some (10, 4, 6)) (.next ([1680000000000], [5580000000000]) (some (10, 4, 6)) (some (10, 4, 7))
    (.next ([1365000000000], [5010000000000]) (some (10, 4, 7)) (some (12, 4, 7)) (.next
    ([1365000000000], [5205000000000]) (some (12, 4, 7)) (some (12, 4, 7)) (.next ([195000000000],
    [945000000000]) (some (12, 4, 7)) (some (12, 4, 7)) (.next ([405000000000], [2220000000000])
    (some (12, 4, 7)) (some (12, 4, 7)) (.next ([990000000000], [5955000000000]) (some (12, 4, 7))
    (some (12, 4, 7)) (.next ([195000000000], [1320000000000]) (some (12, 4, 7)) (some (12, 4, 7))
    (.next ([465000000000], [3435000000000]) (some (12, 4, 7)) (some (12, 4, 7)) (.next
    ([795000000000], [6150000000000]) (some (12, 4, 7)) (some (12, 4, 7)) (.next ([120000000000],
    [1410000000000]) (some (12, 4, 7)) (some (12, 4, 7)) (.next ([180000000000], [2625000000000])
    (some (12, 4, 7)) (some (12, 4, 8)) fan24Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part4 : FanWitness := (.next ([5625000000000], [2040000000000]) (some (10, 12, 6))
    (some (10, 12, 6)) (.next ([5250000000000], [2235000000000]) (some (10, 12, 6)) (some (10, 12,
    6)) (.next ([390000000000], [180000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
    ([4875000000000], [2415000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
    ([4785000000000], [2430000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
    ([4680000000000], [2415000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
    ([4785000000000], [2625000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next ([570000000000],
    [315000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next ([5100000000000], [3000000000000])
    (some (10, 2, 6)) (some (10, 2, 6)) (.next ([765000000000], [495000000000]) (some (10, 2, 6))
    (some (10, 2, 6)) (.next ([570000000000], [375000000000]) (some (10, 2, 6)) (some (10, 2, 6))
    (.next ([1305000000000], [900000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next
    ([945000000000], [690000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([4410000000000],
    [3375000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([375000000000], [315000000000])
    (some (10, 2, 6)) (some (10, 2, 6)) (.next ([4215000000000], [3570000000000]) (some (10, 2, 6))
    (some (10, 2, 6)) (.next ([195000000000], [180000000000]) (some (10, 2, 6)) (some (10, 2, 6))
    (.next ([945000000000], [885000000000]) (some (10, 2, 6)) (some (10, 3, 6)) (.next
    ([3840000000000], [3765000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([375000000000],
    [375000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([3570000000000], [3705000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([180000000000], [195000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([3570000000000], [3900000000000]) (some (10, 3, 6)) (some (10, 4, 6))
    (.next ([3885000000000], [4275000000000]) (some (10, 4, 6)) (some (10, 4, 6))
    fan24Owner0Part3))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6375000000000], [150000000000]) (some (10, 12,
      6)) (some (10, 12, 6)) (.next ([7320000000000], [375000000000]) (some (10, 12, 6)) (some (10,
      12, 6)) (.next ([5205000000000], [435000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
      ([6630000000000], [750000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
      ([6195000000000], [900000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
      ([6435000000000], [945000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
      ([1320000000000], [195000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
      ([4110000000000], [720000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
      ([6195000000000], [1095000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
      ([6060000000000], [1140000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
      ([6510000000000], [1470000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
      ([5685000000000], [1320000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
      ([5490000000000], [1320000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
      ([5820000000000], [1845000000000]) (some (10, 12, 6)) (some (10, 12, 6)) (.next
      ([2580000000000], [840000000000]) (some (10, 12, 6)) (some (10, 12, 6))
      fan24Owner0Part4))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1635000000000], [75000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([7290000000000], [375000000000]) (some (3, 0, 1)) (some (3, 0, 1))
      (.next ([7290000000000, -9000000000000], [450000000000, 9000000000000]) (some (3, 0, 1)) (some
      (3, 0, 1)) (.next ([7365000000000], [1635000000000]) (some (3, 0, 1)) (some (3, 4, 1)) (.next
      ([5730000000000], [1560000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([6105000000000],
      [1710000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([5580000000000,
      -9000000000000], [2085000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([1260000000000], [7740000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [1710000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-75000000000],
      [1710000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-375000000000], [7665000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-450000000000, -9000000000000], [7740000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1635000000000], [9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-1560000000000], [7290000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-1710000000000, -9000000000000], [7815000000000, 9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-2085000000000, -9000000000000], [7665000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-7740000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7740000000000], [1260000000000]) (some (3, 0,
      2)) (some (3, 1, 2)) (.next ([6030000000000, -9000000000000], [2970000000000, 9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1710000000000, 9000000000000], [1710000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([450000000000, 9000000000000],
      [7290000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next ([0, 0],
      [1710000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1260000000000],
      [9000000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2970000000000, -9000000000000],
      [9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1710000000000, -9000000000000],
      [3420000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-7290000000000,
      9000000000000], [7740000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7290000000000], [375000000000]) (some (2, 4, 1))
      (some (3, 4, 1)) (.next ([2160000000000], [375000000000]) (some (3, 4, 1)) (some (3, 4, 1))
      (.next ([5730000000000], [1560000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next
      ([6105000000000], [1710000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next
      ([5580000000000, -9000000000000], [2085000000000, 9000000000000]) (some (3, 4, 2)) (some (3,
      4, 2)) (.next ([5730000000000], [2535000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([4755000000000], [2535000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([450000000000,
      -9000000000000], [375000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [1710000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-375000000000],
      [7665000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-375000000000], [2535000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1560000000000], [7290000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1710000000000, -9000000000000], [7815000000000, 9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2085000000000, -9000000000000], [7665000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2535000000000], [8265000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-2535000000000], [7290000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-375000000000], [825000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6465000000000], [900000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([6840000000000, 0], [1335000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([6030000000000, -9000000000000], [1710000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1710000000000, 9000000000000], [1710000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1710000000000, 9000000000000],
      [6030000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([375000000000],
      [4755000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([375000000000],
      [6465000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1710000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-900000000000], [7365000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1335000000000, -9000000000000], [8175000000000,
      9000000000000]) (some (0, 1, 2)) (some (0, 1, 4)) (.next ([-1710000000000, -9000000000000],
      [7740000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1710000000000,
      -9000000000000], [3420000000000, 18000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next
      ([-6030000000000, 9000000000000], [7740000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-4755000000000, 9000000000000], [5130000000000, -9000000000000]) (some (0, 2, 4)) (some (0,
      2, 4)) (.next ([-6465000000000], [6840000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal
      (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2535000000000], [918000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([4212000000000, -9000000000000], [1710000000000, 9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2535000000000], [6840000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([825000000000, -9000000000000], [6840000000000, 0]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([0, 0], [1710000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 3,
      3)) (.next ([-918000000000], [3453000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next
      ([-1710000000000, -9000000000000], [5922000000000, 0]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-6840000000000], [9375000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-6840000000000, 0], [7665000000000, -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.terminal (some (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded25_1
    · exact excluded25_2
    · exact excluded25_3
    · exact excluded25_4
    · exact excluded25_5
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown190000200000
end ConwaySoifer.Simplified.Certificates
