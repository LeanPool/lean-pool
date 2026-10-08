/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext130000140000
import Mathlib.Tactic.FinCases

/-!
# Sext 130000 140000 6

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
namespace Sext130000140000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner3Part0 : FanWitness := (.next ([7440000000000], [1950000000000]) (some (4, 0, 5))
    (some (4, 0, 5)) (.next ([1875000000000], [1170000000000]) (some (4, 0, 5)) (some (4, 0, 5))
    (.next ([3690000000000, 0], [2580000000000, -9000000000000]) (some (4, 0, 5)) (some (4, 0, 5))
    (.next ([1980000000000], [1770000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([3690000000000], [3750000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([3045000000000],
    [3765000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1815000000000], [2580000000000])
    (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1170000000000], [2415000000000]) (some (4, 0, 5))
    (some (4, 0, 5)) (.next ([1170000000000, 9000000000000], [4290000000000, -9000000000000]) (some
    (4, 0, 5)) (some (4, 0, 5)) (.next ([1170000000000, 9000000000000], [5640000000000]) (some (4,
    0, 5)) (some (4, 0, 5)) (.next ([0, 9000000000000], [1875000000000, -9000000000000]) (some (4,
    0, 5)) (some (4, 0, 5)) (.next ([0], [5640000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([-180000000000], [5640000000000]) (some (0, 0, 5)) (some (0, 0, 5)) (.next ([-1950000000000],
    [9390000000000]) (some (0, 0, 5)) (some (0, 1, 5)) (.next ([-1170000000000], [3045000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2580000000000, 9000000000000], [6270000000000,
    -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1770000000000], [3750000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3750000000000], [7440000000000]) (some (0, 1, 3))
    (some (0, 5, 3)) (.next ([-3765000000000], [6810000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-2580000000000], [4395000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2415000000000], [3585000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4290000000000,
    9000000000000], [5460000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5640000000000, 0],
    [6810000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1875000000000,
    9000000000000], [1875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3))
    (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner3Part0 : FanWitness := (.next ([1875000000000], [1170000000000]) (some (4, 0, 5))
    (some (4, 0, 5)) (.next ([3045000000000], [3765000000000]) (some (4, 0, 5)) (some (4, 0, 5))
    (.next ([3360000000000], [4815000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([1170000000000], [2415000000000]) (some (4, 0, 5)) (some (4, 5, 5)) (.next ([1995000000000],
    [5130000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([825000000000], [2715000000000])
    (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1995000000000, 9000000000000], [7005000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1170000000000, 9000000000000],
    [4290000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1170000000000,
    9000000000000], [5640000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([825000000000],
    [8175000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0, 9000000000000], [1875000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0], [5640000000000]) (some (4, 5,
    2)) (some (4, 5, 3)) (.next ([-180000000000], [5640000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-1170000000000], [3045000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-3765000000000], [6810000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4815000000000],
    [8175000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2415000000000], [3585000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5130000000000], [7125000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-2715000000000], [3540000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-7005000000000, 9000000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-4290000000000, 9000000000000], [5460000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-5640000000000, 0], [6810000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-8175000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-1875000000000, 9000000000000], [1875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal
    (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan50Owner2Part0 : FanWitness := (.next ([1560000000000], [3690000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([1320000000000], [3750000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([885000000000], [3405000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([1170000000000, 9000000000000], [5640000000000, 0]) (some (0, 3, 4)) (some (0, 6, 4)) (.next
    ([780000000000], [4125000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([780000000000,
    9000000000000], [5640000000000, 0]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([0],
    [390000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-390000000000], [5640000000000])
    (some (0, 6, 4)) (some (0, 6, 5)) (.next ([-390000000000], [4080000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-390000000000], [3690000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-735000000000], [4860000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-735000000000], [4470000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-345000000000],
    [780000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4140000000000], [9150000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2520000000000, 9000000000000], [5250000000000, 0])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2955000000000, 9000000000000], [4905000000000, 0])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2340000000000, 9000000000000], [3840000000000,
    -9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3510000000000], [5010000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3690000000000], [5250000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-3750000000000], [5070000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-3405000000000], [4290000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-5640000000000, 0], [6810000000000, 9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-4125000000000], [4905000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-5640000000000,
    0], [6420000000000, 9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.terminal (some (0, 6,
    5)) (some (0, 6, 0)) (some (0, 6, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan52Owner0Part0 : FanWitness := (.next ([0], [870000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-710400000000, -2580000000000], [7690800000000, 5160000000000]) (some (0, 3, 7)) (some
    (0, 3, 7)) (.next ([-495000000000], [4170000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-1200000000000], [7845000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-360000000000],
    [1560000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-2265000000000], [7305000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-2625000000000], [8040000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([-1365000000000], [4170000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([-3335400000000, -2580000000000], [8350800000000, 5160000000000]) (some (0, 3, 4)) (some
    (0, 3, 4)) (.next ([-3825000000000], [8505000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([-360000000000], [735000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-1545000000000],
    [3015000000000]) (some (0, 3, 4)) (some (0, 3, 5)) (.next ([-735000000000], [1200000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3630000000000], [5535000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-4500000000000], [6405000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-1545000000000], [2145000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-4365000000000], [5910000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1965000000000],
    [2625000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-5235000000000], [6780000000000])
    (some (0, 3, 5)) (some (0, 7, 5)) (.next ([-4675800000000, -5160000000000], [5510400000000,
    2580000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-5545800000000, -5160000000000],
    [6380400000000, 2580000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4830000000000],
    [5175000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-5700000000000], [6045000000000])
    (some (0, 7, 5)) (some (1, 7, 5)) (.next ([-6645000000000], [7005000000000]) (some (1, 7, 5))
    (some (1, 7, 5)) (.terminal (some (1, 7, 5)) (some (1, 7, 5)) (some (1, 7,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan53Owner1Part0 : FanWitness := (.next ([3510000000000, -9000000000000], [945000000000, 0])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3990000000000], [1500000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([2820000000000, -9000000000000], [1500000000000, 0]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([5055000000000], [4305000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([4500000000000], [4170000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([1170000000000, 9000000000000], [1170000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([1320000000000], [3510000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([1320000000000], [4680000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([225000000000, 9000000000000], [5625000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([150000000000, -9000000000000], [5850000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([0], [1170000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([-330000000000, 9000000000000], [5490000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next
    ([-945000000000], [5625000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([-135000000000],
    [690000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([-945000000000, 0], [4455000000000,
    -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1500000000000], [5490000000000])
    (some (0, 1, 4)) none (.next ([-1500000000000, 0], [4320000000000, -9000000000000]) none none
    (.next ([-4305000000000], [9360000000000]) none none (.next ([-4170000000000], [8670000000000])
    none none (.next ([-1170000000000, -9000000000000], [2340000000000, 18000000000000]) none none
    (.next ([-3510000000000, 9000000000000], [4830000000000, -9000000000000]) none none (.next
    ([-4680000000000], [6000000000000]) (some (1, 1, 5)) (some (1, 2, 5)) (.next ([-5625000000000],
    [5850000000000, 9000000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-5850000000000,
    -9000000000000], [6000000000000, 0]) (some (1, 2, 5)) (some (1, 2, 5)) (.terminal (some (1, 2,
    5)) (some (1, 2, 5)) (some (1, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan53Owner2Part0 : FanWitness := (.next ([1560000000000], [3690000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([945000000000], [3375000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([1170000000000, 9000000000000], [5640000000000, 0]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([780000000000], [4125000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([630000000000], [4305000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([195000000000],
    [3960000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([0], [390000000000]) (some (0, 3, 4))
    (some (0, 6, 4)) (.next ([-390000000000], [5640000000000]) (some (0, 6, 4)) (some (0, 6, 5))
    (.next ([-390000000000], [4080000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-390000000000], [3690000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-735000000000],
    [4860000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-735000000000], [4470000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-345000000000], [780000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-2520000000000, 9000000000000], [5250000000000, 0]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-4695000000000], [9015000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-4695000000000], [8625000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-2955000000000, 9000000000000], [4905000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-2205000000000, 9000000000000], [3150000000000, -9000000000000]) (some (0, 6, 5)) (some (0, 6,
    5)) (.next ([-3690000000000], [5250000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-3375000000000], [4320000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-5640000000000,
    0], [6810000000000, 9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4125000000000],
    [4905000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4305000000000], [4935000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3960000000000], [4155000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.terminal (some (0, 6, 5)) (some (0, 6, 0)) (some (0, 6,
    5)))))))))))))))))))))))))))

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_3 : ExcludedOn (model48.B 3 ++ [step48.q]) 9000000000000 (model48.caps 3)
    (model48.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5460000000000], [180000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) fan48Owner3Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_9 : ExcludedOn (model48.B 9 ++ [step48.q]) 9000000000000 (model48.caps 9)
    (model48.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked48 : StepValid model48 9000000000000 step48 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded48_0
    · exact excluded48_1
    · exact (hj rfl).elim
    · exact excluded48_3
    · exact excluded48_4
    · exact excluded48_5
    · exact excluded48_6
    · exact excluded48_7
    · exact excluded48_8
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded49_1 : ExcludedOn (model49.B 1 ++ [step49.q]) 9000000000000 (model49.caps 1)
    (model49.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_2 : ExcludedOn (model49.B 2 ++ [step49.q]) 9000000000000 (model49.caps 2)
    (model49.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_3 : ExcludedOn (model49.B 3 ++ [step49.q]) 9000000000000 (model49.caps 3)
    (model49.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5460000000000], [180000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) fan49Owner3Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_4 : ExcludedOn (model49.B 4 ++ [step49.q]) 9000000000000 (model49.caps 4)
    (model49.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [1170000000000]) (some (4, 0,
      5)) (some (4, 1, 5)) (.next ([4125000000000], [1515000000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([4545000000000], [2265000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([420000000000], [750000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2535000000000],
      [5640000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1170000000000, 9000000000000],
      [2955000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1170000000000],
      [3630000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1170000000000, 9000000000000],
      [5640000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1170000000000, 9000000000000],
      [7005000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 9000000000000],
      [3375000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0],
      [5640000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-1170000000000], [4545000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1515000000000], [5640000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([-2265000000000], [6810000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([-750000000000], [1170000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-5640000000000], [8175000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2955000000000,
      9000000000000], [4125000000000]) (some (0, 1, 5)) (some (0, 5, 5)) (.next ([-3630000000000],
      [4800000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-5640000000000], [6810000000000,
      9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-7005000000000, 9000000000000],
      [8175000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3375000000000, 9000000000000],
      [3375000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5,
      4)) (some (0, 5, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8175000000000], [825000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([375000000000], [1170000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([1545000000000], [6465000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1170000000000, 9000000000000], [6840000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([345000000000, 9000000000000], [7830000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1,
      4)) (.next ([0, 0], [1170000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-825000000000], [9000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1170000000000],
      [1545000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6465000000000], [8010000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6840000000000, 0], [8010000000000, 9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-7830000000000, 9000000000000], [8175000000000, 0])
      (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
      4))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded49_6 : ExcludedOn (model49.B 6 ++ [step49.q]) 9000000000000 (model49.caps 6)
    (model49.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_7 : ExcludedOn (model49.B 7 ++ [step49.q]) 9000000000000 (model49.caps 7)
    (model49.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_8 : ExcludedOn (model49.B 8 ++ [step49.q]) 9000000000000 (model49.caps 8)
    (model49.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_9 : ExcludedOn (model49.B 9 ++ [step49.q]) 9000000000000 (model49.caps 9)
    (model49.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked49 : StepValid model49 9000000000000 step49 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded49_1
    · exact excluded49_2
    · exact excluded49_3
    · exact excluded49_4
    · exact excluded49_5
    · exact excluded49_6
    · exact excluded49_7
    · exact excluded49_8
    · exact excluded49_9
theorem next49 : model49.insert step49 = model50 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded50_0 : ExcludedOn (model50.B 0 ++ [step50.q]) 9000000000000 (model50.caps 0)
    (model50.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_2 : ExcludedOn (model50.B 2 ++ [step50.q]) 9000000000000 (model50.caps 2)
    (model50.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [390000000000]) (some (0, 0, 6))
      (some (0, 1, 6)) (.next ([3690000000000], [390000000000]) (some (0, 1, 6)) (some (0, 1, 6))
      (.next ([3300000000000], [390000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
      ([4125000000000], [735000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([3735000000000],
      [735000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([435000000000], [345000000000])
      (some (0, 2, 6)) (some (0, 2, 6)) (.next ([5010000000000], [4140000000000]) (some (0, 2, 6))
      (some (0, 3, 6)) (.next ([2730000000000, 9000000000000], [2520000000000, -9000000000000])
      (some (0, 3, 6)) (some (0, 3, 6)) (.next ([1950000000000, 9000000000000], [2955000000000,
      -9000000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([1500000000000, 0], [2340000000000,
      -9000000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([1500000000000], [3510000000000])
      (some (0, 3, 4)) (some (0, 3, 4)) fan50Owner2Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_3 : ExcludedOn (model50.B 3 ++ [step50.q]) 9000000000000 (model50.caps 3)
    (model50.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_4 : ExcludedOn (model50.B 4 ++ [step50.q]) 9000000000000 (model50.caps 4)
    (model50.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_5 : ExcludedOn (model50.B 5 ++ [step50.q]) 9000000000000 (model50.caps 5)
    (model50.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_6 : ExcludedOn (model50.B 6 ++ [step50.q]) 9000000000000 (model50.caps 6)
    (model50.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_7 : ExcludedOn (model50.B 7 ++ [step50.q]) 9000000000000 (model50.caps 7)
    (model50.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_8 : ExcludedOn (model50.B 8 ++ [step50.q]) 9000000000000 (model50.caps 8)
    (model50.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_9 : ExcludedOn (model50.B 9 ++ [step50.q]) 9000000000000 (model50.caps 9)
    (model50.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked50 : StepValid model50 9000000000000 step50 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded50_0
    · exact (hj rfl).elim
    · exact excluded50_2
    · exact excluded50_3
    · exact excluded50_4
    · exact excluded50_5
    · exact excluded50_6
    · exact excluded50_7
    · exact excluded50_8
    · exact excluded50_9
theorem next50 : model50.insert step50 = model51 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded51_0 : ExcludedOn (model51.B 0 ++ [step51.q]) 9000000000000 (model51.caps 0)
    (model51.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_1 : ExcludedOn (model51.B 1 ++ [step51.q]) 9000000000000 (model51.caps 1)
    (model51.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5160000000000, 9000000000000], [330000000000,
      -9000000000000]) (some (4, 0, 1)) (some (4, 0, 2)) (.next ([3990000000000], [1500000000000])
      (some (4, 0, 2)) (some (4, 1, 2)) (.next ([2820000000000, -9000000000000], [1500000000000, 0])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1170000000000, 9000000000000], [1170000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([4680000000000, 9000000000000],
      [5490000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3510000000000, 0], [4320000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3510000000000], [5490000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [5010000000000]) (some (4, 1, 2)) (some (4, 1,
      4)) (.next ([-330000000000, 9000000000000], [5490000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-1500000000000], [5490000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-1500000000000, 0], [4320000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-1170000000000, -9000000000000], [2340000000000, 18000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5490000000000], [10170000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-4320000000000, 9000000000000], [7830000000000, -9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-5490000000000], [9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1,
      4))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded51_2 : ExcludedOn (model51.B 2 ++ [step51.q]) 9000000000000 (model51.caps 2)
    (model51.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_3 : ExcludedOn (model51.B 3 ++ [step51.q]) 9000000000000 (model51.caps 3)
    (model51.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_4 : ExcludedOn (model51.B 4 ++ [step51.q]) 9000000000000 (model51.caps 4)
    (model51.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_5 : ExcludedOn (model51.B 5 ++ [step51.q]) 9000000000000 (model51.caps 5)
    (model51.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_6 : ExcludedOn (model51.B 6 ++ [step51.q]) 9000000000000 (model51.caps 6)
    (model51.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_8 : ExcludedOn (model51.B 8 ++ [step51.q]) 9000000000000 (model51.caps 8)
    (model51.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_9 : ExcludedOn (model51.B 9 ++ [step51.q]) 9000000000000 (model51.caps 9)
    (model51.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked51 : StepValid model51 9000000000000 step51 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded51_0
    · exact excluded51_1
    · exact excluded51_2
    · exact excluded51_3
    · exact excluded51_4
    · exact excluded51_5
    · exact excluded51_6
    · exact (hj rfl).elim
    · exact excluded51_8
    · exact excluded51_9
theorem next51 : model51.insert step51 = model52 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded52_0 : ExcludedOn (model52.B 0 ++ [step52.q]) 9000000000000 (model52.caps 0)
    (model52.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6980400000000, 2580000000000], [710400000000,
      2580000000000]) (some (5, 1, 7)) (some (5, 2, 7)) (.next ([3675000000000], [495000000000])
      (some (5, 2, 7)) (some (5, 2, 7)) (.next ([6645000000000], [1200000000000]) (some (5, 2, 7))
      (some (5, 2, 7)) (.next ([1200000000000], [360000000000]) (some (5, 2, 7)) (some (5, 2, 7))
      (.next ([5040000000000], [2265000000000]) (some (5, 2, 7)) (some (5, 2, 7)) (.next
      ([5415000000000], [2625000000000]) (some (5, 2, 7)) (some (5, 2, 7)) (.next ([2805000000000],
      [1365000000000]) (some (5, 2, 7)) (some (5, 2, 7)) (.next ([5015400000000, 2580000000000],
      [3335400000000, 2580000000000]) (some (5, 2, 7)) (some (5, 2, 7)) (.next ([4680000000000],
      [3825000000000]) (some (5, 2, 7)) (some (5, 2, 7)) (.next ([375000000000], [360000000000])
      (some (5, 2, 7)) (some (5, 2, 7)) (.next ([1470000000000], [1545000000000]) (some (5, 2, 7))
      (some (5, 2, 7)) (.next ([465000000000], [735000000000]) (some (5, 2, 7)) (some (6, 2, 7))
      (.next ([1905000000000], [3630000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([1905000000000], [4500000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([600000000000],
      [1545000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1545000000000], [4365000000000])
      (some (6, 2, 7)) (some (0, 3, 7)) (.next ([660000000000], [1965000000000]) (some (0, 3, 7))
      (some (0, 3, 7)) (.next ([1545000000000], [5235000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([834600000000, -2580000000000], [4675800000000, 5160000000000]) (some (0, 3, 7)) (some
      (0, 3, 7)) (.next ([834600000000, -2580000000000], [5545800000000, 5160000000000]) (some (0,
      3, 7)) (some (0, 3, 7)) (.next ([345000000000], [4830000000000]) (some (0, 3, 7)) (some (0, 3,
      7)) (.next ([345000000000], [5700000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
      ([360000000000], [6645000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      fan52Owner0Part0)))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_2 : ExcludedOn (model52.B 2 ++ [step52.q]) 9000000000000 (model52.caps 2)
    (model52.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_3 : ExcludedOn (model52.B 3 ++ [step52.q]) 9000000000000 (model52.caps 3)
    (model52.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_4 : ExcludedOn (model52.B 4 ++ [step52.q]) 9000000000000 (model52.caps 4)
    (model52.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_5 : ExcludedOn (model52.B 5 ++ [step52.q]) 9000000000000 (model52.caps 5)
    (model52.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_6 : ExcludedOn (model52.B 6 ++ [step52.q]) 9000000000000 (model52.caps 6)
    (model52.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4170000000000, 9000000000000], [150000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([3000000000000], [1320000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1320000000000], [3510000000000, -9000000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1170000000000, 9000000000000], [7830000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1170000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-150000000000, 9000000000000],
      [4320000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1320000000000], [4320000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3510000000000, 9000000000000], [4830000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7830000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_7 : ExcludedOn (model52.B 7 ++ [step52.q]) 9000000000000 (model52.caps 7)
    (model52.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_8 : ExcludedOn (model52.B 8 ++ [step52.q]) 9000000000000 (model52.caps 8)
    (model52.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_9 : ExcludedOn (model52.B 9 ++ [step52.q]) 9000000000000 (model52.caps 9)
    (model52.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked52 : StepValid model52 9000000000000 step52 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded52_0
    · exact (hj rfl).elim
    · exact excluded52_2
    · exact excluded52_3
    · exact excluded52_4
    · exact excluded52_5
    · exact excluded52_6
    · exact excluded52_7
    · exact excluded52_8
    · exact excluded52_9
theorem next52 : model52.insert step52 = model53 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded53_1 : ExcludedOn (model53.B 1 ++ [step53.q]) 9000000000000 (model53.caps 1)
    (model53.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5160000000000, 9000000000000], [330000000000,
      -9000000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([4680000000000], [945000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([555000000000], [135000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) fan53Owner1Part0)))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_2 : ExcludedOn (model53.B 2 ++ [step53.q]) 9000000000000 (model53.caps 2)
    (model53.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [390000000000]) (some (0, 0, 6))
      (some (0, 1, 6)) (.next ([3690000000000], [390000000000]) (some (0, 1, 6)) (some (0, 1, 6))
      (.next ([3300000000000], [390000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
      ([4125000000000], [735000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([3735000000000],
      [735000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([435000000000], [345000000000])
      (some (0, 2, 6)) (some (0, 2, 6)) (.next ([2730000000000, 9000000000000], [2520000000000,
      -9000000000000]) (some (0, 2, 6)) (some (0, 3, 6)) (.next ([4320000000000], [4695000000000])
      (some (0, 3, 6)) (some (0, 3, 6)) (.next ([3930000000000], [4695000000000]) (some (0, 3, 6))
      (some (0, 3, 6)) (.next ([1950000000000, 9000000000000], [2955000000000, -9000000000000])
      (some (0, 3, 6)) (some (0, 3, 6)) (.next ([945000000000, 0], [2205000000000, -9000000000000])
      (some (0, 3, 6)) (some (0, 3, 6)) fan53Owner2Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded53_3 : ExcludedOn (model53.B 3 ++ [step53.q]) 9000000000000 (model53.caps 3)
    (model53.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_4 : ExcludedOn (model53.B 4 ++ [step53.q]) 9000000000000 (model53.caps 4)
    (model53.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_5 : ExcludedOn (model53.B 5 ++ [step53.q]) 9000000000000 (model53.caps 5)
    (model53.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_6 : ExcludedOn (model53.B 6 ++ [step53.q]) 9000000000000 (model53.caps 6)
    (model53.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_7 : ExcludedOn (model53.B 7 ++ [step53.q]) 9000000000000 (model53.caps 7)
    (model53.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [3150000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([5625000000000], [4320000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([1170000000000, 9000000000000], [4320000000000, -9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([135000000000], [4320000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([0], [5490000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next
      ([-3150000000000, 9000000000000], [8775000000000, -9000000000000]) (some (3, 3, 2)) (some (3,
      3, 2)) (.next ([-4320000000000], [9945000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4320000000000, 9000000000000], [5490000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4320000000000], [4455000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded53_8 : ExcludedOn (model53.B 8 ++ [step53.q]) 9000000000000 (model53.caps 8)
    (model53.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_9 : ExcludedOn (model53.B 9 ++ [step53.q]) 9000000000000 (model53.caps 9)
    (model53.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked53 : StepValid model53 9000000000000 step53 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded53_1
    · exact excluded53_2
    · exact excluded53_3
    · exact excluded53_4
    · exact excluded53_5
    · exact excluded53_6
    · exact excluded53_7
    · exact excluded53_8
    · exact excluded53_9
theorem next53 : model53.insert step53 = model54 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext130000140000
end ConwaySoifer.Simplified.Certificates
