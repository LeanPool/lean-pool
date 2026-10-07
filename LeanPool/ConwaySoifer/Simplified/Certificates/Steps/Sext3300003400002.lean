/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext330000340000
import Mathlib.Tactic.FinCases

/-!
# Sext 330000 340000 2

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
namespace Sext330000340000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part0 : FanWitness := (.next ([-1260000000000], [6300000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-390000000000], [1875000000000]) (some (8, 3, 5)) (some (8, 3, 5))
    (.next ([-1500000000000], [6831000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([-1485000000000], [5445000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-1620000000000],
    [5925000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-750000000000], [2610000000000])
    (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-1875000000000], [6471000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-2235000000000], [6096000000000]) (some (8, 3, 5)) (some (8, 3, 5))
    (.next ([-360000000000], [735000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([-4845000000000], [9885000000000]) (some (8, 3, 5)) (some (8, 3, 6)) (.next ([-735000000000],
    [1470000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-750000000000], [1485000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-375000000000], [735000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([-390000000000], [750000000000]) (some (8, 3, 6)) (some (8, 3, 6))
    (.next ([-5460000000000], [10056000000000]) (some (8, 3, 6)) (some (8, 3, 7)) (.next
    ([-1860000000000], [2610000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-444000000000],
    [615000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4440000000000], [5790000000000])
    (some (8, 3, 7)) (some (8, 4, 7)) (.next ([-1485000000000], [1860000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-3225000000000], [3960000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-5175000000000], [6165000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-4611000000000], [5346000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5925000000000],
    [6525000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5346000000000], [5721000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.terminal (some (8, 4, 7)) (some (8, 4, 7)) (some (8, 4,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part1 : FanWitness := (.next ([3861000000000], [2235000000000]) (some (8, 8, 4))
    (some (8, 8, 4)) (.next ([375000000000], [360000000000]) (some (8, 8, 4)) (some (8, 8, 4))
    (.next ([5040000000000], [4845000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next
    ([735000000000], [735000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([735000000000],
    [750000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([360000000000], [375000000000]) (some
    (8, 3, 4)) (some (8, 3, 4)) (.next ([360000000000], [390000000000]) (some (8, 3, 4)) (some (8,
    3, 4)) (.next ([4596000000000], [5460000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next
    ([750000000000], [1860000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([171000000000],
    [444000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([1350000000000], [4440000000000])
    (some (8, 3, 4)) (some (8, 3, 4)) (.next ([375000000000], [1485000000000]) (some (8, 3, 4))
    (some (8, 3, 4)) (.next ([735000000000], [3225000000000]) (some (8, 3, 4)) (some (8, 3, 4))
    (.next ([990000000000], [5175000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next
    ([735000000000], [4611000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([600000000000],
    [5925000000000]) (some (8, 3, 4)) (some (8, 3, 5)) (.next ([375000000000], [5346000000000])
    (some (8, 3, 5)) (some (8, 3, 5)) (.next ([0], [3585000000000]) (some (8, 3, 5)) (some (8, 3,
    5)) (.next ([-15000000000], [6096000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([-15000000000], [2235000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-750000000000],
    [6195000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-885000000000], [6660000000000])
    (some (8, 3, 5)) (some (8, 3, 5)) (.next ([-735000000000], [3960000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([-1125000000000], [5835000000000]) (some (8, 3, 5)) (some (8, 3, 5))
    fan18Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part0 : FanWitness := (.next ([-1260000000000], [6300000000000]) (some (0, 3, 8))
    (some (0, 3, 8)) (.next ([-390000000000], [1875000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    (.next ([-1500000000000], [6831000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([-1620000000000], [5925000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-750000000000],
    [2610000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-1875000000000], [6471000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-2235000000000], [6096000000000]) (some (0, 3, 8))
    (some (0, 3, 8)) (.next ([-360000000000], [735000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    (.next ([-735000000000], [1470000000000]) (some (0, 3, 8)) (some (1, 3, 8)) (.next
    ([-750000000000], [1485000000000]) (some (1, 3, 8)) (some (1, 3, 8)) (.next ([-375000000000],
    [735000000000]) (some (1, 3, 8)) (some (1, 3, 8)) (.next ([-5310000000000], [10215000000000])
    (some (1, 3, 8)) (some (2, 3, 8)) (.next ([-390000000000], [750000000000]) (some (2, 3, 8))
    (some (2, 3, 8)) (.next ([-5481000000000], [9771000000000]) (some (2, 3, 8)) (some (2, 3, 8))
    (.next ([-1860000000000], [2610000000000]) (some (2, 3, 8)) (some (2, 3, 8)) (.next
    ([-444000000000], [615000000000]) (some (2, 3, 8)) (some (2, 3, 8)) (.next ([-4440000000000],
    [5790000000000]) (some (2, 3, 8)) (some (2, 4, 8)) (.next ([-1485000000000], [1860000000000])
    (some (2, 4, 8)) (some (2, 4, 8)) (.next ([-5175000000000], [6165000000000]) (some (2, 4, 8))
    (some (2, 4, 8)) (.next ([-3690000000000], [4305000000000]) (some (2, 4, 8)) (some (2, 4, 8))
    (.next ([-4611000000000], [5346000000000]) (some (2, 4, 8)) (some (2, 4, 8)) (.next
    ([-5910000000000], [6525000000000]) (some (2, 4, 8)) (some (2, 4, 8)) (.next ([-5925000000000],
    [6525000000000]) (some (2, 4, 8)) (some (2, 4, 8)) (.next ([-5346000000000], [5721000000000])
    (some (2, 4, 8)) (some (2, 4, 8)) (.terminal (some (2, 4, 8)) (some (2, 4, 8)) (some (2, 4,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part1 : FanWitness := (.next ([3861000000000], [2235000000000]) (some (8, 3, 4))
    (some (8, 3, 4)) (.next ([375000000000], [360000000000]) (some (8, 3, 4)) (some (8, 3, 4))
    (.next ([735000000000], [735000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next
    ([735000000000], [750000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([360000000000],
    [375000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([4905000000000], [5310000000000])
    (some (8, 3, 4)) (some (8, 3, 4)) (.next ([360000000000], [390000000000]) (some (8, 3, 4)) (some
    (8, 3, 4)) (.next ([4290000000000], [5481000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next
    ([750000000000], [1860000000000]) (some (8, 3, 4)) (some (8, 3, 8)) (.next ([171000000000],
    [444000000000]) (some (8, 3, 8)) (some (8, 3, 8)) (.next ([1350000000000], [4440000000000])
    (some (8, 3, 8)) (some (8, 3, 8)) (.next ([375000000000], [1485000000000]) (some (0, 3, 8))
    (some (0, 3, 8)) (.next ([990000000000], [5175000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    (.next ([615000000000], [3690000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([735000000000], [4611000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([615000000000],
    [5910000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([600000000000], [5925000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.next ([375000000000], [5346000000000]) (some (0, 3, 8))
    (some (0, 3, 8)) (.next ([0], [2220000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([-15000000000], [6096000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-15000000000],
    [2235000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-135000000000], [4050000000000])
    (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-885000000000], [6660000000000]) (some (0, 3, 8))
    (some (0, 3, 8)) (.next ([-870000000000], [4425000000000]) (some (0, 3, 8)) (some (0, 3, 8))
    fan20Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner4Part0 : FanWitness := (.next ([1777125000000], [4678875000000]) (some (7, 1, 3))
    (some (7, 1, 3)) (.next ([1875000000000], [5346000000000]) (some (7, 1, 3)) (some (7, 1, 3))
    (.next ([885000000000], [3405000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
    ([405000000000, 9000000000000], [2970000000000, -9000000000000]) (some (7, 1, 3)) (some (7, 1,
    3)) (.next ([0], [3405000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([-30000000000],
    [5970000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([-126000000000, 9000000000000],
    [2376000000000, -9000000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([-223875000000,
    9000000000000], [1708875000000, -9000000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
    ([-1155000000000], [6501000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([-1920000000000],
    [6598875000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([-915000000000], [2565000000000])
    (some (7, 1, 3)) (some (7, 1, 3)) (.next ([-2565000000000], [5940000000000]) (some (7, 1, 3))
    (some (7, 1, 3)) (.next ([-4290000000000], [9261000000000]) (some (7, 1, 3)) (some (7, 1, 3))
    (.next ([-594000000000], [1125000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
    ([-3096000000000], [5346000000000]) (some (7, 1, 3)) (some (7, 1, 4)) (.next ([-2970000000000,
    -9000000000000], [4971000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-2040000000000],
    [3096000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-1261125000000], [1890000000000])
    (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-3193875000000], [4678875000000]) (some (7, 1, 4))
    (some (7, 1, 4)) (.next ([-5940000000000], [8346000000000]) (some (7, 1, 4)) (some (7, 1, 4))
    (.next ([-4678875000000], [6456000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([-5346000000000], [7221000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-3405000000000],
    [4290000000000]) (some (7, 1, 4)) (some (7, 1, 7)) (.next ([-2970000000000, 9000000000000],
    [3375000000000]) (some (7, 1, 7)) (some (7, 2, 7)) (.terminal (some (7, 2, 7)) (some (0, 2, 7))
    (some (7, 2, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner4Part0 : FanWitness := (.next ([0], [3405000000000]) (some (7, 1, 3)) (some (7, 1, 3))
    (.next ([-30000000000], [5970000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-1155000000000], [6501000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-915000000000],
    [4290000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-516000000000], [2250000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1920000000000], [6598875000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-1110000000000], [3375000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-915000000000], [2565000000000]) (some (0, 1, 3)) (some (0, 1, 7)) (.next
    ([-3405000000000], [8235000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-2565000000000],
    [5940000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-3405000000000], [6780000000000])
    (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-594000000000], [1125000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([-3096000000000], [5346000000000]) (some (0, 1, 7)) (some (0, 1, 7))
    (.next ([-2040000000000], [3096000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([-1261125000000], [1890000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-3193875000000],
    [4678875000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-2565000000000], [3375000000000])
    (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-3405000000000], [4290000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([-667125000000], [765000000000]) (some (0, 1, 7)) (some (0, 2, 7))
    (.next ([-1971000000000], [2250000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-1303875000000], [1485000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-2805000000000],
    [3193875000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-4290000000000], [4830000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-1485000000000], [1636125000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.terminal (some (0, 2, 7)) (some (0, 2, 7)) (some (0, 2,
    7)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6030000000000, 9000000000000], [405000000000,
      -9000000000000]) (some (2, 4, 1)) (some (3, 4, 1)) (.next ([2865000000000], [195000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([3270000000000, -9000000000000], [2970000000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2970000000000, 9000000000000],
      [2970000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2970000000000,
      9000000000000], [3270000000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next
      ([3060000000000], [3375000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([90000000000,
      -9000000000000], [3375000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [2970000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-405000000000,
      9000000000000], [6435000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-195000000000],
      [3060000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2970000000000, -9000000000000],
      [6240000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2970000000000, -9000000000000],
      [5940000000000, 18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3270000000000,
      9000000000000], [6240000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3375000000000],
      [6435000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3375000000000], [3465000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (4, 1,
      2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3750000000000], [795000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5595000000000], [4545000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4800000000000], [4545000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([2970000000000, 9000000000000], [4545000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([2175000000000, 9000000000000], [4545000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([0, 0], [2970000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-795000000000], [4545000000000]) (some (4, 1, 2)) (some (4, 2, 3)) (.next ([-4545000000000],
      [10140000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-4545000000000], [9345000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-4545000000000, 0], [7515000000000, 9000000000000])
      (some (4, 2, 3)) (some (4, 2, 4)) (.next ([-4545000000000, 0], [6720000000000, 9000000000000])
      (some (4, 2, 4)) (some (4, 2, 4)) (.terminal (some (4, 2, 4)) (some (0, 2, 4)) (some (4, 2,
      4))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6081000000000], [15000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([2220000000000], [15000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      (.next ([5445000000000], [750000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([5775000000000], [885000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([3225000000000],
      [735000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([4710000000000], [1125000000000])
      (some (7, 8, 4)) (some (7, 8, 4)) (.next ([5040000000000], [1260000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([1485000000000], [390000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      (.next ([5331000000000], [1500000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([3960000000000], [1485000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next ([4305000000000],
      [1620000000000]) (some (7, 8, 4)) (some (8, 8, 4)) (.next ([1860000000000], [750000000000])
      (some (8, 8, 4)) (some (8, 8, 4)) (.next ([4596000000000], [1875000000000]) (some (8, 8, 4))
      (some (8, 8, 4)) fan18Owner0Part1)))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7680000000000, 9000000000000], [1320000000000,
      -9000000000000]) (some (2, 4, 1)) (some (3, 4, 1)) (.next ([4710000000000], [4290000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2970000000000, 9000000000000], [2970000000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2970000000000, 9000000000000],
      [3270000000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1950000000000],
      [2760000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([1740000000000, -9000000000000],
      [4290000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0], [2970000000000,
      9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-1320000000000, 9000000000000],
      [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4290000000000], [9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2970000000000, -9000000000000], [5940000000000,
      18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3270000000000, 9000000000000],
      [6240000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2760000000000], [4710000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4290000000000], [6030000000000, -9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (4, 1, 2)) (some (4, 1,
      2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded18_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3960000000000], [2790000000000]) (some (2, 0,
      4)) (some (3, 0, 4)) (.next ([3270000000000, -9000000000000], [2970000000000, 9000000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2970000000000, 9000000000000], [2970000000000,
      9000000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([2970000000000, 9000000000000],
      [3270000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([510000000000],
      [2280000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([990000000000, -9000000000000],
      [5760000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([180000000000,
      9000000000000], [3780000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([0], [2970000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2790000000000], [6750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2970000000000,
      -9000000000000], [6240000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2970000000000,
      -9000000000000], [5940000000000, 18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3270000000000, 9000000000000], [6240000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2280000000000], [2790000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5760000000000,
      -9000000000000], [6750000000000]) (some (0, 1, 2)) (some (0, 4, 2)) (.next ([-3780000000000,
      9000000000000], [3960000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2))
      (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded19_9 : ExcludedOn (model19.B 9 ++ [step19.q]) 9000000000000 (model19.caps 9)
    (model19.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded19_3
    · exact excluded19_4
    · exact excluded19_5
    · exact excluded19_6
    · exact excluded19_7
    · exact excluded19_8
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6081000000000], [15000000000]) (some (8, 2, 4))
      (some (8, 2, 4)) (.next ([2220000000000], [15000000000]) (some (8, 2, 4)) (some (8, 2, 4))
      (.next ([3915000000000], [135000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
      ([5775000000000], [885000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([3555000000000],
      [870000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([5040000000000], [1260000000000])
      (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1485000000000], [390000000000]) (some (8, 2, 4))
      (some (8, 2, 4)) (.next ([5331000000000], [1500000000000]) (some (8, 2, 4)) (some (8, 2, 4))
      (.next ([4305000000000], [1620000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
      ([1860000000000], [750000000000]) (some (8, 2, 4)) (some (8, 3, 4)) (.next ([4596000000000],
      [1875000000000]) (some (8, 3, 4)) (some (8, 3, 4)) fan20Owner0Part1)))))))))))) (den :=
      9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8145000000000, 9000000000000], [990000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([5175000000000], [3960000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2970000000000, 9000000000000], [2970000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2205000000000, -9000000000000],
      [3960000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [2970000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-990000000000, 9000000000000],
      [9135000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3960000000000], [9135000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2970000000000, -9000000000000], [5940000000000,
      18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3960000000000, 0],
      [6165000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0))
      (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000, 0], [2070000000000,
      -9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([2625000000000], [2415000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2970000000000, 9000000000000], [2970000000000,
      9000000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([2970000000000, 9000000000000],
      [3270000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([3825000000000],
      [5040000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([855000000000, -9000000000000],
      [8010000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0], [2970000000000,
      9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-2070000000000, 9000000000000],
      [5895000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2415000000000],
      [5040000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2970000000000, -9000000000000],
      [5940000000000, 18000000000000]) (some (0, 1, 2)) (some (0, 4, 2)) (.next ([-3270000000000,
      9000000000000], [6240000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5040000000000],
      [8865000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-8010000000000, -9000000000000],
      [8865000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4,
      2)) (some (0, 4, 2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_9 : ExcludedOn (model20.B 9 ++ [step20.q]) 9000000000000 (model20.caps 9)
    (model20.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded20_3
    · exact excluded20_4
    · exact excluded20_5
    · exact excluded20_6
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5940000000000], [30000000000]) (some (7, 0, 2))
      (some (7, 1, 2)) (.next ([2250000000000], [126000000000, -9000000000000]) (some (7, 1, 2))
      (some (7, 1, 2)) (.next ([1485000000000], [223875000000, -9000000000000]) (some (7, 1, 2))
      (some (7, 1, 2)) (.next ([5346000000000], [1155000000000]) (some (7, 1, 2)) (some (7, 1, 2))
      (.next ([4678875000000], [1920000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next
      ([1650000000000], [915000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([3375000000000],
      [2565000000000]) (some (7, 1, 2)) (some (7, 1, 3)) (.next ([4971000000000], [4290000000000])
      (some (7, 1, 3)) (some (7, 1, 3)) (.next ([531000000000], [594000000000]) (some (7, 1, 3))
      (some (7, 1, 3)) (.next ([2250000000000], [3096000000000]) (some (7, 1, 3)) (some (7, 1, 3))
      (.next ([2001000000000, -9000000000000], [2970000000000, 9000000000000]) (some (7, 1, 3))
      (some (7, 1, 3)) (.next ([1056000000000], [2040000000000]) (some (7, 1, 3)) (some (7, 1, 3))
      (.next ([628875000000], [1261125000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
      ([1485000000000], [3193875000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([2406000000000],
      [5940000000000]) (some (7, 1, 3)) (some (7, 1, 3)) fan21Owner4Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_9 : ExcludedOn (model21.B 9 ++ [step21.q]) 9000000000000 (model21.caps 9)
    (model21.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded21_6
    · exact excluded21_7
    · exact (hj rfl).elim
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3270000000000, -9000000000000], [2970000000000,
      9000000000000]) (some (2, 4, 1)) (some (3, 4, 1)) (.next ([2970000000000, 9000000000000],
      [2970000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2970000000000,
      9000000000000], [3270000000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next
      ([2970000000000, 9000000000000], [5625000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next
      ([615000000000], [5625000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [2970000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2970000000000,
      -9000000000000], [6240000000000]) (some (0, 1, 2)) (some (4, 1, 2)) (.next ([-2970000000000,
      -9000000000000], [5940000000000, 18000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-3270000000000, 9000000000000], [6240000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-5625000000000, 0], [8595000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-5625000000000], [6240000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1,
      2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [3375000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([2340000000000], [3285000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1596000000000], [3375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([1686000000000], [4029000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([0],
      [4029000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-3375000000000], [9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-3285000000000], [5625000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-3375000000000], [4971000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4029000000000], [5715000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_9 : ExcludedOn (model22.B 9 ++ [step22.q]) 9000000000000 (model22.caps 9)
    (model22.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded22_5
    · exact excluded22_6
    · exact excluded22_7
    · exact excluded22_8
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5940000000000], [30000000000]) (some (7, 0, 2))
      (some (7, 1, 2)) (.next ([5346000000000], [1155000000000]) (some (7, 1, 2)) (some (7, 1, 2))
      (.next ([3375000000000], [915000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next
      ([1734000000000], [516000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([4678875000000],
      [1920000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([2265000000000], [1110000000000])
      (some (7, 1, 2)) (some (7, 1, 2)) (.next ([1650000000000], [915000000000]) (some (7, 1, 2))
      (some (7, 1, 2)) (.next ([4830000000000], [3405000000000]) (some (7, 1, 2)) (some (7, 1, 3))
      (.next ([3375000000000], [2565000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
      ([3375000000000], [3405000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([531000000000],
      [594000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([2250000000000], [3096000000000])
      (some (7, 1, 3)) (some (7, 1, 3)) (.next ([1056000000000], [2040000000000]) (some (7, 1, 3))
      (some (7, 1, 3)) (.next ([628875000000], [1261125000000]) (some (7, 1, 3)) (some (7, 1, 3))
      (.next ([1485000000000], [3193875000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
      ([810000000000], [2565000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([885000000000],
      [3405000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([97875000000], [667125000000])
      (some (7, 1, 3)) (some (7, 1, 3)) (.next ([279000000000], [1971000000000]) (some (7, 1, 3))
      (some (7, 1, 3)) (.next ([181125000000], [1303875000000]) (some (7, 1, 3)) (some (7, 1, 3))
      (.next ([388875000000], [2805000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
      ([540000000000], [4290000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([151125000000],
      [1485000000000]) (some (7, 1, 3)) (some (7, 1, 3)) fan23Owner4Part0))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_8 : ExcludedOn (model23.B 8 ++ [step23.q]) 9000000000000 (model23.caps 8)
    (model23.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4170000000000], [4830000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([1686000000000], [4029000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([885000000000], [3285000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([141000000000], [4830000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [4029000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-4830000000000], [9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-4029000000000], [5715000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-3285000000000], [4170000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4830000000000], [4971000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_9 : ExcludedOn (model23.B 9 ++ [step23.q]) 9000000000000 (model23.caps 9)
    (model23.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Sext330000340000
end ConwaySoifer.Simplified.Certificates
