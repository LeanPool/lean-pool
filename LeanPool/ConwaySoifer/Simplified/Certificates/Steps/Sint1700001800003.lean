/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint170000180000
import Mathlib.Tactic.FinCases

/-!
# Sint 170000 180000 3

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
namespace Sint170000180000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner0Part0 : FanWitness := (.next ([2040000000000], [5325000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([1275000000000], [5730000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([885000000000], [6495000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([870000000000], [7995000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([135000000000],
    [1260000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([0], [1275000000000]) (some (6, 3,
    5)) (some (6, 3, 5)) (.next ([-225000000000], [4560000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-510000000000], [6630000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-615000000000], [7980000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-990000000000],
    [8865000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-615000000000], [5325000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-990000000000], [7590000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([-1875000000000], [9375000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-1500000000000], [5835000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-2010000000000], [5460000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-375000000000],
    [885000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-1170000000000], [2670000000000])
    (some (6, 3, 5)) (some (6, 4, 5)) (.next ([-885000000000], [1785000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.next ([-390000000000], [765000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-5325000000000], [7365000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-5730000000000], [7005000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-6495000000000],
    [7380000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-7995000000000], [8865000000000])
    (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-1260000000000], [1395000000000]) (some (6, 4, 5))
    (some (6, 4, 6)) (.terminal (some (6, 4, 6)) (some (6, 4, 6)) (some (6, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner4Part0 : FanWitness := (.next ([5121000000000, 0], [1530000000000, 9000000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3060000000000, -9000000000000], [1971000000000,
    9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2880000000000], [2250000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2370000000000], [2370000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([2469000000000], [4080000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([1350000000000, -9000000000000], [3780000000000, 9000000000000]) (some (5, 1, 2)) (some
    (5, 1, 5)) (.next ([510000000000], [1869000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
    ([510000000000], [6990000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([99000000000],
    [1710000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([90000000000], [4590000000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 0], [1530000000000, 9000000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([-9000000000], [2880000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-441000000000], [5031000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-1020000000000, -9000000000000], [8520000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([-1530000000000, -9000000000000], [6651000000000, 9000000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-1971000000000, -9000000000000], [5031000000000, 0]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-2250000000000], [5130000000000]) (some (0, 1, 5)) (some (0, 2, 5))
    (.next ([-2370000000000], [4740000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-4080000000000], [6549000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3780000000000,
    -9000000000000], [5130000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1869000000000],
    [2379000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6990000000000], [7500000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1710000000000], [1809000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4590000000000], [4680000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner0Part0 : FanWitness := (.next ([1020000000000], [3990000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([1275000000000], [5730000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([885000000000], [6495000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([135000000000], [1260000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([120000000000],
    [3105000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([0], [1275000000000]) (some (6, 3,
    5)) (some (6, 3, 5)) (.next ([-225000000000], [4560000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-510000000000], [6630000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-615000000000], [5325000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-1500000000000],
    [5835000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-2010000000000], [5460000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-375000000000], [885000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([-1170000000000], [2670000000000]) (some (6, 3, 5)) (some (6, 4, 5))
    (.next ([-885000000000], [1785000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-390000000000], [765000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-5610000000000],
    [10110000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-4440000000000], [7440000000000])
    (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-3105000000000], [4500000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.next ([-2730000000000], [3615000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-3990000000000], [5010000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-5730000000000], [7005000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-6495000000000],
    [7380000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-1260000000000], [1395000000000])
    (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-3105000000000], [3225000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.terminal (some (6, 4, 5)) (some (6, 4, 5)) (some (6, 4,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner6Part0 : FanWitness := (.next ([5010000000000], [4500000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) (some
    (6, 2, 4)) (some (6, 2, 4)) (.next ([1350000000000, -9000000000000], [2025000000000,
    9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([1335000000000, -9000000000000],
    [2040000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([3480000000000,
    -9000000000000], [6030000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([1125000000000], [2040000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([2145000000000],
    [3990000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([2130000000000], [4005000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([0], [15000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-210000000000], [1755000000000]) (some (6, 2, 4)) (some (6, 3, 4)) (.next
    ([-210000000000], [1740000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-495000000000],
    [3375000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-510000000000], [3375000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-510000000000, 9000000000000], [1635000000000,
    -9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-2970000000000, 9000000000000],
    [7980000000000, -9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-2460000000000],
    [6345000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-4500000000000], [9510000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-1530000000000, -9000000000000], [3060000000000,
    18000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-2025000000000, -9000000000000],
    [3375000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-2040000000000, -9000000000000],
    [3375000000000]) (some (6, 3, 4)) (some (6, 3, 5)) (.next ([-6030000000000, -9000000000000],
    [9510000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-2040000000000], [3165000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-3990000000000], [6135000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.next ([-4005000000000], [6135000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.terminal (some (6, 3, 5)) (some (6, 3, 6)) (some (6, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner6Part0 : FanWitness := (.next ([1530000000000], [210000000000]) (some (5, 6, 4)) (some
    (5, 6, 4)) (.next ([2880000000000], [495000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([2865000000000], [510000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1125000000000, 0],
    [510000000000, -9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([4710000000000],
    [2535000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1530000000000, 9000000000000],
    [1530000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1350000000000,
    -9000000000000], [2025000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([1335000000000, -9000000000000], [2040000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6,
    4)) (.next ([1125000000000], [2040000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([630000000000], [6120000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([630000000000],
    [7650000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0], [15000000000])
    (some (5, 6, 4)) (some (5, 6, 4)) (.next ([-210000000000], [1755000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-210000000000], [1740000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-495000000000], [3375000000000]) (some (0, 6, 4)) (some (1, 6, 4)) (.next
    ([-510000000000], [3375000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-510000000000,
    9000000000000], [1635000000000, -9000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next
    ([-2535000000000], [7245000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-1530000000000,
    -9000000000000], [3060000000000, 18000000000000]) (some (1, 6, 4)) (some (6, 6, 4)) (.next
    ([-2025000000000, -9000000000000], [3375000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
    ([-2040000000000, -9000000000000], [3375000000000]) (some (6, 6, 4)) (some (6, 6, 5)) (.next
    ([-2040000000000], [3165000000000]) (some (6, 6, 5)) (some (6, 6, 5)) (.next ([-6120000000000],
    [6750000000000]) (some (6, 6, 5)) (some (6, 6, 5)) (.next ([-7650000000000, -9000000000000],
    [8280000000000, 9000000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.terminal (some (6, 3, 5))
    (some (6, 3, 5)) (some (6, 3, 5)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1530000000000, 9000000000000], [1530000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([3375000000000], [4590000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3375000000000], [6120000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1845000000000, -9000000000000], [7650000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1530000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-1530000000000, -9000000000000],
      [3060000000000, 18000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-4590000000000,
      9000000000000], [7965000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-6120000000000], [9495000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7650000000000,
      -9000000000000], [9495000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000], [510000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([3621000000000, 0], [1530000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([5625000000000], [2880000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([4095000000000, -9000000000000], [2880000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([1470000000000, -9000000000000], [2040000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([630000000000], [5505000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([741000000000], [8505000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([111000000000], [3000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [3621000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-510000000000], [3510000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1530000000000, -9000000000000], [5151000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2880000000000], [8505000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2880000000000, 0], [6975000000000,
      -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2040000000000, -9000000000000],
      [3510000000000]) (some (0, 2, 4)) (some (0, 4, 4)) (.next ([-5505000000000], [6135000000000])
      (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-8505000000000], [9246000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-3000000000000], [3111000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.terminal (some (0, 4, 0)) (some (0, 4, 0)) (some (0, 4, 0))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded24_4
    · exact excluded24_5
    · exact (hj rfl).elim
    · exact excluded24_7
    · exact excluded24_8
    · exact excluded24_9
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000], [510000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([5835000000000], [1125000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([4305000000000, -9000000000000], [1125000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([3621000000000, 0], [1530000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([1470000000000, -9000000000000], [2040000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([2385000000000], [3960000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([2496000000000], [6960000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([111000000000], [3000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [3621000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-510000000000], [3510000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1125000000000], [6960000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1125000000000, 0], [5430000000000, -9000000000000]) (some (0, 2,
      4)) (some (0, 2, 4)) (.next ([-1530000000000, -9000000000000], [5151000000000, 9000000000000])
      (some (0, 2, 4)) (some (0, 4, 4)) (.next ([-2040000000000, -9000000000000], [3510000000000])
      (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-3960000000000], [6345000000000]) (some (0, 4, 4))
      (some (0, 4, 4)) (.next ([-6960000000000], [9456000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-3000000000000], [3111000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some
      (0, 4, 0)) (some (0, 4, 0)) (some (0, 4, 0))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6960000000000, 0], [1635000000000,
      -9000000000000]) (some (4, 0, 1)) (some (4, 1, 2)) (.next ([5835000000000], [2040000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([6960000000000], [3165000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([5430000000000, -9000000000000], [3165000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1125000000000], [1125000000000]) (some (4, 1, 2)) (some (4, 1, 4))
      (.next ([405000000000, 9000000000000], [720000000000, -9000000000000]) (some (4, 1, 4)) (some
      (4, 1, 4)) (.next ([0, 0], [1530000000000, 9000000000000]) (some (4, 1, 4)) (some (4, 1, 4))
      (.next ([-1635000000000, 9000000000000], [8595000000000, -9000000000000]) (some (4, 1, 4))
      (some (4, 1, 4)) (.next ([-2040000000000], [7875000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-3165000000000], [10125000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-3165000000000], [8595000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-1125000000000], [2250000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-720000000000,
      9000000000000], [1125000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1,
      4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded25_5
    · exact (hj rfl).elim
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2871000000000], [9000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([4590000000000], [441000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5121000000000, 0], [1530000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3060000000000, -9000000000000], [1971000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([2880000000000], [2250000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([2370000000000], [2751000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1929000000000], [5031000000000]) (some (4, 1, 2)) (some (5, 1, 2)) (.next ([1350000000000,
      -9000000000000], [3780000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([99000000000], [1710000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([120000000000],
      [5130000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([90000000000], [4590000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 0], [1530000000000, 9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-9000000000], [2880000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([-441000000000], [5031000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next
      ([-1530000000000, -9000000000000], [6651000000000, 9000000000000]) (some (5, 1, 4)) (some (5,
      1, 4)) (.next ([-1971000000000, -9000000000000], [5031000000000, 0]) (some (5, 1, 4)) (some
      (5, 1, 4)) (.next ([-2250000000000], [5130000000000]) (some (5, 1, 4)) (some (5, 2, 4)) (.next
      ([-2751000000000], [5121000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-5031000000000], [6960000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-3780000000000,
      -9000000000000], [5130000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-1710000000000], [1809000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-5130000000000], [5250000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-4590000000000], [4680000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.terminal (some (5, 2,
      4)) (some (0, 2, 4)) (some (5, 2, 4))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_9 : ExcludedOn (model26.B 9 ++ [step26.q]) 9000000000000 (model26.caps 9)
    (model26.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded26_5
    · exact excluded26_6
    · exact excluded26_7
    · exact (hj rfl).elim
    · exact excluded26_9
theorem next26 : model26.insert step26 = model27 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded27_0 : ExcludedOn (model27.B 0 ++ [step27.q]) 9000000000000 (model27.caps 0)
    (model27.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4335000000000], [225000000000]) (some (6, 6, 4))
      (some (6, 6, 4)) (.next ([6120000000000], [510000000000]) (some (6, 6, 4)) (some (6, 6, 4))
      (.next ([7365000000000], [615000000000]) (some (6, 6, 4)) (some (6, 6, 5)) (.next
      ([7875000000000], [990000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([4710000000000],
      [615000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([6600000000000], [990000000000])
      (some (6, 2, 5)) (some (6, 2, 5)) (.next ([7500000000000], [1875000000000]) (some (6, 2, 5))
      (some (6, 2, 5)) (.next ([4335000000000], [1500000000000]) (some (6, 2, 5)) (some (6, 2, 5))
      (.next ([3450000000000], [2010000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next
      ([510000000000], [375000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([1500000000000],
      [1170000000000]) (some (6, 2, 5)) (some (6, 3, 5)) (.next ([900000000000], [885000000000])
      (some (6, 3, 5)) (some (6, 3, 5)) (.next ([375000000000], [390000000000]) (some (6, 3, 5))
      (some (6, 3, 5)) fan27Owner0Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2871000000000], [9000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([4590000000000], [441000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([7500000000000, 0], [1020000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      fan27Owner4Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_8 : ExcludedOn (model27.B 8 ++ [step27.q]) 9000000000000 (model27.caps 8)
    (model27.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6315000000000], [315000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([2010000000000], [1185000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([2880000000000], [4620000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([2010000000000], [7500000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [6630000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-315000000000], [6630000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1185000000000], [3195000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-4620000000000], [7500000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-7500000000000], [9510000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_9 : ExcludedOn (model27.B 9 ++ [step27.q]) 9000000000000 (model27.caps 9)
    (model27.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked27 : StepValid model27 9000000000000 step27 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded27_0
    · exact excluded27_1
    · exact excluded27_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2871000000000], [9000000000]) (some (4, 0, 2))
      (some (4, 5, 2)) (.next ([4590000000000], [441000000000]) (some (4, 5, 2)) (some (4, 5, 2))
      (.next ([5130000000000], [999000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([5121000000000, 0], [1530000000000, 9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([3060000000000, -9000000000000], [1971000000000, 9000000000000]) (some (4, 5, 2)) (some (4,
      5, 2)) (.next ([5121000000000], [3879000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([2880000000000], [2250000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1350000000000,
      -9000000000000], [3780000000000, 9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
      ([711000000000], [4320000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([99000000000],
      [1710000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([90000000000], [4590000000000])
      (some (4, 5, 2)) (some (4, 5, 3)) (.next ([0, 0], [1530000000000, 9000000000000]) (some (4, 5,
      3)) (some (4, 5, 3)) (.next ([-9000000000], [2880000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-441000000000], [5031000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next
      ([-999000000000], [6129000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1530000000000,
      -9000000000000], [6651000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-1971000000000, -9000000000000], [5031000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-3879000000000], [9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2250000000000], [5130000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3780000000000,
      -9000000000000], [5130000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-4320000000000], [5031000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-1710000000000], [1809000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-4590000000000], [4680000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded28_9 : ExcludedOn (model28.B 9 ++ [step28.q]) 9000000000000 (model28.caps 9)
    (model28.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded28_6
    · exact excluded28_7
    · exact excluded28_8
    · exact excluded28_9
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded29_0 : ExcludedOn (model29.B 0 ++ [step29.q]) 9000000000000 (model29.caps 0)
    (model29.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4335000000000], [225000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([6120000000000], [510000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      (.next ([4710000000000], [615000000000]) (some (5, 6, 4)) (some (5, 6, 5)) (.next
      ([4335000000000], [1500000000000]) (some (5, 6, 5)) (some (5, 6, 5)) (.next ([3450000000000],
      [2010000000000]) (some (5, 6, 5)) (some (5, 6, 5)) (.next ([510000000000], [375000000000])
      (some (5, 6, 5)) (some (5, 6, 5)) (.next ([1500000000000], [1170000000000]) (some (5, 6, 5))
      (some (5, 6, 5)) (.next ([900000000000], [885000000000]) (some (0, 6, 5)) (some (0, 6, 5))
      (.next ([375000000000], [390000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
      ([4500000000000], [5610000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([3000000000000],
      [4440000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([1395000000000], [3105000000000])
      (some (0, 6, 5)) (some (6, 6, 5)) (.next ([885000000000], [2730000000000]) (some (6, 3, 5))
      (some (6, 3, 5)) fan29Owner0Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (997) (1200) (120000) (.witnessedFan (.next
      ([3000000000000], [510000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([5121000000000,
      0], [1530000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([5385000000000],
      [4125000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1470000000000, -9000000000000],
      [2040000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3855000000000,
      -9000000000000], [5655000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 3)) (.next
      ([2385000000000], [3615000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([1611000000000],
      [3000000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next ([996000000000], [4389000000000])
      (some (4, 1, 4)) (some (4, 1, 4)) (.next ([0], [5121000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-510000000000], [3510000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next
      ([-1530000000000, -9000000000000], [6651000000000, 9000000000000]) (some (0, 2, 4)) (some (0,
      2, 4)) (.next ([-4125000000000], [9510000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-2040000000000, -9000000000000], [3510000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-5655000000000, -9000000000000], [9510000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3615000000000], [6000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3000000000000], [4611000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-4389000000000], [5385000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (.witnessedFan (.next
      ([3000000000000], [510000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([5121000000000,
      0], [1530000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([5385000000000],
      [4125000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2385000000000], [3615000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3855000000000, -9000000000000], [5655000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1470000000000, -9000000000000],
      [2040000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next ([1611000000000],
      [3000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([996000000000], [4389000000000])
      (some (4, 1, 4)) (some (4, 1, 4)) (.next ([0], [5121000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-510000000000], [3510000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next
      ([-1530000000000, -9000000000000], [6651000000000, 9000000000000]) (some (0, 2, 4)) (some (0,
      2, 4)) (.next ([-4125000000000], [9510000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3615000000000], [6000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-5655000000000,
      -9000000000000], [9510000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2040000000000,
      -9000000000000], [3510000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3000000000000],
      [4611000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4389000000000], [5385000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
      4)))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded29_5
    · exact excluded29_6
    · exact excluded29_7
    · exact excluded29_8
    · exact excluded29_9
theorem next29 : model29.insert step29 = model30 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded30_0 : ExcludedOn (model30.B 0 ++ [step30.q]) 9000000000000 (model30.caps 0)
    (model30.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_4 : ExcludedOn (model30.B 4 ++ [step30.q]) 9000000000000 (model30.caps 4)
    (model30.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4611000000000], [264000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([4875000000000], [510000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([5121000000000, 0], [1530000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([3345000000000, -9000000000000], [2040000000000, 9000000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([3990000000000], [4500000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([2460000000000, -9000000000000], [4500000000000, 0]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([885000000000], [3615000000000]) (some (3, 1, 4)) (some (3, 4, 4)) (.next
      ([621000000000], [8490000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0],
      [1530000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-264000000000],
      [4875000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-510000000000], [5385000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1530000000000, -9000000000000], [6651000000000,
      9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-2040000000000, -9000000000000],
      [5385000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4500000000000],
      [8490000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4500000000000, 0],
      [6960000000000, -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3615000000000],
      [4500000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-8490000000000], [9111000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4, 3)) (some (0, 4, 3)) (some (0, 4,
      3))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1545000000000], [210000000000]) (some (6, 6, 3))
      (some (6, 6, 4)) (.next ([1530000000000], [210000000000]) (some (6, 6, 4)) (some (6, 6, 4))
      (.next ([2880000000000], [495000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
      ([2865000000000], [510000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([1125000000000,
      0], [510000000000, -9000000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([5010000000000,
      0], [2970000000000, -9000000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
      ([3885000000000], [2460000000000]) (some (6, 2, 4)) (some (6, 2, 4)) fan30Owner6Part0))))))))
      (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded30_4
    · exact (hj rfl).elim
    · exact excluded30_6
    · exact excluded30_7
    · exact excluded30_8
    · exact excluded30_9
theorem next30 : model30.insert step30 = model31 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded31_0 : ExcludedOn (model31.B 0 ++ [step31.q]) 9000000000000 (model31.caps 0)
    (model31.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_6 : ExcludedOn (model31.B 6 ++ [step31.q]) 9000000000000 (model31.caps 6)
    (model31.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1545000000000], [210000000000]) (some (5, 6, 3))
      (some (5, 6, 4)) fan31Owner6Part0)) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded31_4
    · exact excluded31_5
    · exact excluded31_6
    · exact excluded31_7
    · exact excluded31_8
    · exact (hj rfl).elim
theorem next31 : model31.insert step31 = model32 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint170000180000
end ConwaySoifer.Simplified.Certificates
