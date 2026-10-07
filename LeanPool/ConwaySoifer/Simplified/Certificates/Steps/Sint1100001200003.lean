/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint110000120000
import Mathlib.Tactic.FinCases

/-!
# Sint 110000 120000 3

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
namespace Sint110000120000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part0 : FanWitness := (.next ([-409200000000, 5280000000000], [5199600000000,
    -2640000000000]) (some (0, 8, 8)) (some (0, 8, 8)) (.next ([-620400000000, -2640000000000],
    [6205800000000, 5280000000000]) (some (0, 8, 8)) (some (1, 8, 8)) (.next ([-699600000000,
    2640000000000], [6290400000000, 2640000000000]) (some (1, 8, 8)) (some (1, 8, 8)) (.next
    ([-699600000000, 2640000000000], [5780400000000, 2640000000000]) (some (1, 8, 8)) (some (1, 8,
    8)) (.next ([-45000000000], [360000000000]) (some (1, 8, 8)) (some (1, 8, 8)) (.next
    ([-980400000000, -2640000000000], [6520800000000, 5280000000000]) (some (1, 8, 8)) (some (1, 8,
    8)) (.next ([-910800000000, -5280000000000], [5915400000000, 2640000000000]) (some (1, 8, 8))
    (some (1, 8, 8)) (.next ([-135000000000], [795000000000]) (some (1, 8, 8)) (some (1, 8, 8))
    (.next ([-1280400000000, -2640000000000], [6580800000000, 5280000000000]) (some (1, 8, 8)) (some
    (1, 8, 8)) (.next ([-1270800000000, -5280000000000], [6230400000000, 2640000000000]) (some (1,
    8, 8)) (some (1, 8, 8)) (.next ([-1280400000000, -2640000000000], [6070800000000,
    5280000000000]) (some (1, 8, 8)) (some (1, 8, 8)) (.next ([-2265000000000], [8940000000000])
    (some (1, 8, 8)) (some (1, 8, 8)) (.next ([-2220000000000], [8580000000000]) (some (1, 8, 6))
    (some (1, 8, 6)) (.next ([-2505000000000], [9240000000000]) (some (1, 8, 6)) (some (1, 8, 6))
    (.next ([-1570800000000, -5280000000000], [5780400000000, 2640000000000]) (some (1, 8, 6)) (some
    (1, 8, 6)) (.next ([-3015000000000], [9240000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next
    ([-285000000000], [660000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-290400000000,
    -2640000000000], [580800000000, 5280000000000]) (some (1, 8, 6)) (some (1, 8, 6)) (.next
    ([-450000000000], [750000000000]) (some (1, 8, 6)) (some (2, 8, 6)) (.next ([-240000000000],
    [300000000000]) (some (2, 8, 6)) (some (2, 8, 6)) (.next ([-7805400000000, -2640000000000],
    [8830800000000, 5280000000000]) (some (2, 8, 6)) (some (2, 8, 7)) (.next ([-7224600000000,
    2640000000000], [7669200000000, -5280000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.next
    ([-8095800000000, -5280000000000], [8540400000000, 2640000000000]) (some (2, 8, 7)) (some (2, 8,
    7)) (.next ([-7805400000000, -2640000000000], [7959600000000, -2640000000000]) (some (2, 8, 7))
    (some (2, 8, 7)) (.terminal (some (2, 8, 7)) (some (2, 8, 7)) (some (2, 8,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part1 : FanWitness := (.next ([5540400000000, 2640000000000], [980400000000,
    2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([5004600000000, -2640000000000],
    [910800000000, 5280000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([660000000000],
    [135000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([5300400000000, 2640000000000],
    [1280400000000, 2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([4959600000000,
    -2640000000000], [1270800000000, 5280000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
    ([4790400000000, 2640000000000], [1280400000000, 2640000000000]) (some (7, 2, 8)) (some (7, 2,
    8)) (.next ([6675000000000], [2265000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
    ([6360000000000], [2220000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([6735000000000],
    [2505000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([4209600000000, -2640000000000],
    [1570800000000, 5280000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([6225000000000],
    [3015000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([375000000000], [285000000000]) (some
    (7, 2, 8)) (some (7, 2, 8)) (.next ([290400000000, 2640000000000], [290400000000,
    2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([300000000000], [450000000000]) (some
    (7, 2, 8)) (some (7, 3, 8)) (.next ([60000000000], [240000000000]) (some (7, 3, 8)) (some (7, 3,
    8)) (.next ([1025400000000, 2640000000000], [7805400000000, 2640000000000]) (some (7, 3, 8))
    (some (7, 3, 8)) (.next ([444600000000, -2640000000000], [7224600000000, -2640000000000]) (some
    (7, 3, 8)) (some (7, 3, 8)) (.next ([444600000000, -2640000000000], [8095800000000,
    5280000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([154200000000, -5280000000000],
    [7805400000000, 2640000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([0], [510000000000])
    (some (7, 3, 8)) (some (7, 8, 8)) (.next ([-39600000000, 2640000000000], [5915400000000,
    2640000000000]) (some (0, 8, 8)) (some (0, 8, 8)) (.next ([-109200000000, 5280000000000],
    [5649600000000, -2640000000000]) (some (0, 8, 8)) (some (0, 8, 8)) (.next ([-399600000000,
    2640000000000], [6230400000000, 2640000000000]) (some (0, 8, 8)) (some (0, 8, 8)) (.next
    ([-409200000000, 5280000000000], [5709600000000, -2640000000000]) (some (0, 8, 8)) (some (0, 8,
    8)) fan24Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner0Part0 : FanWitness := (.next ([-409200000000, 5280000000000], [5199600000000,
    -2640000000000]) (some (0, 8, 8)) (some (0, 8, 8)) (.next ([-620400000000, -2640000000000],
    [6205800000000, 5280000000000]) (some (0, 8, 8)) (some (1, 8, 8)) (.next ([-699600000000,
    2640000000000], [6290400000000, 2640000000000]) (some (1, 8, 8)) (some (1, 8, 8)) (.next
    ([-699600000000, 2640000000000], [5780400000000, 2640000000000]) (some (1, 8, 8)) (some (1, 8,
    8)) (.next ([-45000000000], [360000000000]) (some (1, 8, 8)) (some (1, 8, 8)) (.next
    ([-980400000000, -2640000000000], [6520800000000, 5280000000000]) (some (1, 8, 8)) (some (1, 8,
    8)) (.next ([-910800000000, -5280000000000], [5915400000000, 2640000000000]) (some (1, 8, 8))
    (some (1, 8, 8)) (.next ([-135000000000], [795000000000]) (some (1, 8, 8)) (some (1, 8, 8))
    (.next ([-1280400000000, -2640000000000], [6580800000000, 5280000000000]) (some (1, 8, 8)) (some
    (1, 8, 8)) (.next ([-1270800000000, -5280000000000], [6230400000000, 2640000000000]) (some (1,
    8, 8)) (some (1, 8, 8)) (.next ([-1280400000000, -2640000000000], [6070800000000,
    5280000000000]) (some (1, 8, 8)) (some (1, 8, 8)) (.next ([-1570800000000, -5280000000000],
    [6290400000000, 2640000000000]) (some (1, 8, 8)) (some (1, 8, 8)) (.next ([-2445000000000],
    [9330000000000]) (some (1, 8, 8)) (some (1, 8, 6)) (.next ([-2730000000000], [9990000000000])
    (some (1, 8, 6)) (some (1, 8, 6)) (.next ([-3240000000000], [9990000000000]) (some (1, 8, 6))
    (some (1, 8, 6)) (.next ([-285000000000], [660000000000]) (some (1, 8, 6)) (some (1, 8, 6))
    (.next ([-290400000000, -2640000000000], [580800000000, 5280000000000]) (some (1, 8, 6)) (some
    (1, 8, 6)) (.next ([-450000000000], [750000000000]) (some (1, 8, 6)) (some (2, 8, 6)) (.next
    ([-240000000000], [300000000000]) (some (2, 8, 6)) (some (2, 8, 6)) (.next ([-8030400000000,
    -2640000000000], [9580800000000, 5280000000000]) (some (2, 8, 6)) (some (2, 8, 7)) (.next
    ([-7449600000000, 2640000000000], [8419200000000, -5280000000000]) (some (2, 8, 7)) (some (2, 8,
    7)) (.next ([-8320800000000, -5280000000000], [9290400000000, 2640000000000]) (some (2, 8, 7))
    (some (2, 8, 7)) (.next ([-8030400000000, -2640000000000], [8709600000000, -2640000000000])
    (some (2, 8, 7)) (some (2, 8, 7)) (.next ([-5334600000000, 2640000000000], [5585400000000,
    2640000000000]) (some (2, 8, 7)) (some (2, 8, 7)) (.terminal (some (2, 8, 7)) (some (2, 8, 7))
    (some (2, 8, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner0Part1 : FanWitness := (.next ([5540400000000, 2640000000000], [980400000000,
    2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([5004600000000, -2640000000000],
    [910800000000, 5280000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([660000000000],
    [135000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([5300400000000, 2640000000000],
    [1280400000000, 2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([4959600000000,
    -2640000000000], [1270800000000, 5280000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
    ([4790400000000, 2640000000000], [1280400000000, 2640000000000]) (some (7, 2, 8)) (some (7, 2,
    8)) (.next ([4719600000000, -2640000000000], [1570800000000, 5280000000000]) (some (7, 2, 8))
    (some (7, 2, 8)) (.next ([6885000000000], [2445000000000]) (some (7, 2, 8)) (some (7, 2, 8))
    (.next ([7260000000000], [2730000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
    ([6750000000000], [3240000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([375000000000],
    [285000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([290400000000, 2640000000000],
    [290400000000, 2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([300000000000],
    [450000000000]) (some (7, 2, 8)) (some (7, 3, 8)) (.next ([60000000000], [240000000000]) (some
    (7, 3, 8)) (some (7, 3, 8)) (.next ([1550400000000, 2640000000000], [8030400000000,
    2640000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([969600000000, -2640000000000],
    [7449600000000, -2640000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next ([969600000000,
    -2640000000000], [8320800000000, 5280000000000]) (some (7, 3, 8)) (some (7, 3, 8)) (.next
    ([679200000000, -5280000000000], [8030400000000, 2640000000000]) (some (7, 3, 8)) (some (7, 3,
    8)) (.next ([250800000000, 5280000000000], [5334600000000, -2640000000000]) (some (7, 3, 8))
    (some (7, 8, 8)) (.next ([0], [510000000000]) (some (7, 8, 8)) (some (7, 8, 8)) (.next
    ([-39600000000, 2640000000000], [5915400000000, 2640000000000]) (some (0, 8, 8)) (some (0, 8,
    8)) (.next ([-109200000000, 5280000000000], [5649600000000, -2640000000000]) (some (0, 8, 8))
    (some (0, 8, 8)) (.next ([-399600000000, 2640000000000], [6230400000000, 2640000000000]) (some
    (0, 8, 8)) (some (0, 8, 8)) (.next ([-409200000000, 5280000000000], [5709600000000,
    -2640000000000]) (some (0, 8, 8)) (some (0, 8, 8)) fan26Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner5Part0 : FanWitness := (.next ([2970000000000], [1140000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([2760000000000], [1260000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([3150000000000, -9000000000000], [1890000000000, 9000000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([3270000000000, -9000000000000], [1980000000000, 9000000000000]) (some (5, 1,
    2)) (some (5, 1, 3)) (.next ([120000000000], [90000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([3000000000000], [5010000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next
    ([990000000000], [2010000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([2010000000000,
    -9000000000000], [6000000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([960000000000], [4140000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([750000000000],
    [4260000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0], [6000000000000]) (some (0, 1,
    4)) (some (0, 1, 4)) (.next ([-990000000000, -9000000000000], [6990000000000, 9000000000000])
    (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-900000000000], [5040000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-990000000000], [5250000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-1140000000000], [4110000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-1260000000000], [4020000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1890000000000,
    -9000000000000], [5040000000000]) (some (0, 2, 4)) (some (0, 2, 5)) (.next ([-1980000000000,
    -9000000000000], [5250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-90000000000],
    [210000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5010000000000], [8010000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2010000000000], [3000000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-6000000000000, -9000000000000], [8010000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4140000000000], [5100000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-4260000000000], [5010000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some
    (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner5Part0 : FanWitness := (.next ([4140000000000], [900000000000]) (some (0, 5, 5)) (some
    (0, 5, 5)) (.next ([4260000000000], [990000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next
    ([3150000000000, -9000000000000], [1890000000000, 9000000000000]) (some (0, 5, 5)) (some (0, 5,
    5)) (.next ([3270000000000, -9000000000000], [1980000000000, 9000000000000]) (some (0, 5, 5))
    (some (0, 5, 5)) (.next ([120000000000], [90000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next
    ([4230000000000], [3990000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([4110000000000],
    [3900000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([960000000000, 9000000000000],
    [2010000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([960000000000],
    [4140000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([750000000000], [4260000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([0], [6000000000000]) (some (0, 5, 4)) (some (0, 5,
    4)) (.next ([-30000000000], [9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-30000000000], [3000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-990000000000,
    -9000000000000], [6990000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-900000000000], [5040000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-990000000000],
    [5250000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1890000000000, -9000000000000],
    [5040000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1980000000000, -9000000000000],
    [5250000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-90000000000], [210000000000]) (some
    (0, 5, 4)) (some (0, 5, 4)) (.next ([-3990000000000], [8220000000000]) (some (0, 5, 4)) (some
    (0, 5, 4)) (.next ([-3900000000000], [8010000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-2010000000000, 9000000000000], [2970000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-4140000000000], [5100000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4260000000000],
    [5010000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5, 0)) (some (0, 5, 0))
    (some (0, 5, 0)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5875800000000, 5280000000000], [39600000000,
      -2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([5540400000000, 2640000000000],
      [109200000000, -5280000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([5830800000000,
      5280000000000], [399600000000, -2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([5300400000000, 2640000000000], [409200000000, -5280000000000]) (some (7, 2, 8)) (some (7, 2,
      8)) (.next ([4790400000000, 2640000000000], [409200000000, -5280000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([5585400000000, 2640000000000], [620400000000, 2640000000000]) (some
      (7, 2, 8)) (some (7, 2, 8)) (.next ([5590800000000, 5280000000000], [699600000000,
      -2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([5080800000000, 5280000000000],
      [699600000000, -2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([315000000000],
      [45000000000]) (some (7, 2, 8)) (some (7, 2, 8)) fan24Owner0Part1)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7515000000000], [750000000000]) (some (5, 1, 3))
      (some (5, 1, 4)) (.next ([6525000000000, -9000000000000], [750000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([2070000000000], [240000000000, 9000000000000]) (some (5, 1, 4))
      (some (5, 1, 5)) (.next ([1875000000000], [495000000000]) (some (5, 1, 5)) (some (5, 1, 5))
      (.next ([825000000000], [300000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
      ([990000000000, 9000000000000], [990000000000, 9000000000000]) (some (5, 1, 5)) (some (5, 2,
      5)) (.next ([750000000000], [1320000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([495000000000, 9000000000000], [1380000000000, -9000000000000]) (some (5, 2, 5)) (some (5, 2,
      5)) (.next ([1620000000000], [6390000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([1320000000000], [7515000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([240000000000,
      9000000000000], [8265000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([0, 0],
      [990000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-750000000000],
      [8265000000000]) (some (0, 2, 5)) (some (0, 3, 5)) (.next ([-750000000000], [7275000000000,
      -9000000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-240000000000, -9000000000000],
      [2310000000000, 9000000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-495000000000],
      [2370000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-300000000000], [1125000000000])
      (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-990000000000, -9000000000000], [1980000000000,
      18000000000000]) (some (0, 3, 5)) (some (1, 3, 5)) (.next ([-1320000000000], [2070000000000])
      (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-1380000000000, 9000000000000], [1875000000000])
      (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-6390000000000], [8010000000000]) (some (1, 3, 5))
      (some (1, 3, 5)) (.next ([-7515000000000], [8835000000000]) (some (1, 3, 5)) (some (1, 3, 5))
      (.next ([-8265000000000, 0], [8505000000000, 9000000000000]) (some (1, 3, 5)) (some (1, 3, 5))
      (.terminal (some (1, 3, 5)) (some (1, 3, 5)) (some (1, 3, 5))))))))))))))))))))))))))) (den :=
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
    · exact (hj rfl).elim
    · exact excluded24_2
    · exact excluded24_3
    · exact excluded24_4
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
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2070000000000], [240000000000, 9000000000000])
      (some (0, 5, 3)) (some (0, 5, 4)) (.next ([6180000000000, -9000000000000], [990000000000,
      9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([1875000000000], [495000000000])
      (some (0, 5, 4)) (some (0, 5, 4)) (.next ([5850000000000], [2070000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([6675000000000], [2370000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([825000000000], [300000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([990000000000, 9000000000000], [990000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5,
      4)) (.next ([750000000000], [1320000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([495000000000, 9000000000000], [1380000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5,
      4)) (.next ([0, 0], [990000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-240000000000, -9000000000000], [2310000000000, 9000000000000]) (some (0, 5, 4)) (some (0,
      5, 4)) (.next ([-990000000000, -9000000000000], [7170000000000]) (some (0, 5, 4)) (some (0, 5,
      4)) (.next ([-495000000000], [2370000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2070000000000], [7920000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2370000000000], [9045000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-300000000000],
      [1125000000000]) (some (0, 5, 4)) (some (5, 5, 4)) (.next ([-990000000000, -9000000000000],
      [1980000000000, 18000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-1320000000000],
      [2070000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-1380000000000, 9000000000000],
      [1875000000000]) (some (5, 5, 4)) (some (5, 5, 0)) (.terminal (some (5, 5, 0)) (some (5, 3,
      0)) (some (5, 5, 0))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact (hj rfl).elim
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5875800000000, 5280000000000], [39600000000,
      -2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([5540400000000, 2640000000000],
      [109200000000, -5280000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([5830800000000,
      5280000000000], [399600000000, -2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([5300400000000, 2640000000000], [409200000000, -5280000000000]) (some (7, 2, 8)) (some (7, 2,
      8)) (.next ([4790400000000, 2640000000000], [409200000000, -5280000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([5585400000000, 2640000000000], [620400000000, 2640000000000]) (some
      (7, 2, 8)) (some (7, 2, 8)) (.next ([5590800000000, 5280000000000], [699600000000,
      -2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([5080800000000, 5280000000000],
      [699600000000, -2640000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([315000000000],
      [45000000000]) (some (7, 2, 8)) (some (7, 2, 8)) fan26Owner0Part1)))))))))) (den :=
      9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (1633) (3294) (329400) (.witnessedFan (.next
      ([2070000000000], [240000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 5)) (.next
      ([1875000000000], [495000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([825000000000],
      [300000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([750000000000, 0], [330000000000,
      -9000000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([990000000000, 9000000000000],
      [990000000000, 9000000000000]) (some (5, 1, 5)) (some (5, 2, 5)) (.next ([885000000000,
      -9000000000000], [1485000000000, 9000000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([2370000000000], [5865000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([495000000000,
      9000000000000], [1380000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([2070000000000], [6990000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([990000000000,
      9000000000000], [7740000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([0, 0],
      [990000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-240000000000,
      -9000000000000], [2310000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 3, 5)) (.next
      ([-495000000000], [2370000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-300000000000],
      [1125000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-330000000000, 9000000000000],
      [1080000000000, -9000000000000]) (some (0, 3, 5)) (some (1, 3, 5)) (.next ([-990000000000,
      -9000000000000], [1980000000000, 18000000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-1485000000000, -9000000000000], [2370000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-5865000000000], [8235000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-1380000000000,
      9000000000000], [1875000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-6990000000000],
      [9060000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-7740000000000, 0],
      [8730000000000, 9000000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.terminal (some (1, 3, 5))
      (some (1, 3, 5)) (some (1, 3, 5))))))))))))))))))))))))) (.witnessedFan (.next
      ([2070000000000], [240000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 5)) (.next
      ([1875000000000], [495000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([750000000000, 0],
      [330000000000, -9000000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([990000000000,
      9000000000000], [990000000000, 9000000000000]) (some (5, 1, 5)) (some (5, 2, 5)) (.next
      ([750000000000], [1320000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([885000000000,
      -9000000000000], [1485000000000, 9000000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([495000000000, 9000000000000], [1380000000000, -9000000000000]) (some (5, 2, 5)) (some (5, 2,
      5)) (.next ([2370000000000], [5865000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([2070000000000], [6990000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([990000000000,
      9000000000000], [7740000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([0, 0],
      [990000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-240000000000,
      -9000000000000], [2310000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 3, 5)) (.next
      ([-495000000000], [2370000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-330000000000,
      9000000000000], [1080000000000, -9000000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
      ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (0, 3, 5)) (some (1,
      3, 5)) (.next ([-1320000000000], [2070000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-1485000000000, -9000000000000], [2370000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-1380000000000, 9000000000000], [1875000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-5865000000000], [8235000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-6990000000000], [9060000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-7740000000000,
      0], [8730000000000, 9000000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.terminal (some (1, 3,
      5)) (some (1, 3, 5)) (some (1, 3, 5)))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded26_2
    · exact excluded26_3
    · exact excluded26_4
    · exact excluded26_5
    · exact excluded26_6
    · exact excluded26_7
    · exact excluded26_8
    · exact excluded26_9
theorem next26 : model26.insert step26 = model27 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded27_0 : ExcludedOn (model27.B 0 ++ [step27.q]) 9000000000000 (model27.caps 0)
    (model27.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000, 0], [990000000000,
      9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) (.next ([4140000000000], [900000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4260000000000], [990000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) fan27Owner5Part0)))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded27_0
    · exact excluded27_1
    · exact excluded27_2
    · exact excluded27_3
    · exact (hj rfl).elim
    · exact excluded27_5
    · exact excluded27_6
    · exact excluded27_7
    · exact excluded27_8
    · exact excluded27_9
theorem next27 : model27.insert step27 = model28 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1485000000000, 0], [240000000000,
      9000000000000]) (some (4, 4, 2)) (some (4, 4, 3)) (.next ([525000000000], [225000000000])
      (some (4, 4, 3)) (some (4, 4, 3)) (.next ([6375000000000], [3615000000000]) (some (4, 4, 3))
      (some (4, 4, 3)) (.next ([5850000000000], [3390000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([1260000000000, 0], [990000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([5115000000000], [4875000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([750000000000], [735000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([4125000000000,
      -9000000000000], [4875000000000, 0]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([0, 0],
      [990000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-240000000000,
      -9000000000000], [1725000000000, 9000000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next
      ([-225000000000], [750000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-3615000000000],
      [9990000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-3390000000000], [9240000000000])
      (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-990000000000, -9000000000000], [2250000000000,
      9000000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-4875000000000], [9990000000000])
      (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-735000000000], [1485000000000]) (some (4, 2, 0))
      (some (4, 2, 0)) (.next ([-4875000000000, 0], [9000000000000, -9000000000000]) (some (4, 2,
      0)) (some (4, 2, 0)) (.terminal (some (4, 2, 0)) (some (4, 2, 4)) (some (4, 2,
      4))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3885000000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([8010000000000, -9000000000000],
      [990000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4125000000000,
      -9000000000000], [4875000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([990000000000],
      [3885000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, -9000000000000],
      [3885000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-990000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-4875000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3885000000000],
      [4875000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (2275) (3246) (324600) (.witnessedFan (.next ([375000000000,
      -9000000000000], [0, 9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next
      ([6750000000000], [1365000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([3000000000000],
      [885000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([990000000000], [375000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3885000000000], [4125000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([2895000000000, -9000000000000], [5115000000000, 9000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2520000000000], [5115000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0], [990000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 4, 2))
      (.next ([0, -9000000000000], [375000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1365000000000], [8115000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-885000000000],
      [3885000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-375000000000], [1365000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4125000000000], [8010000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5115000000000, -9000000000000], [8010000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5115000000000], [7635000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (.split
      (589225) (797975) (840714) (84071400) (.witnessedFan (.next ([7125000000000], [990000000000,
      9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([6750000000000], [1365000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([375000000000, -9000000000000], [0, 9000000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([3000000000000], [885000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([990000000000], [375000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([3885000000000], [4125000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([2895000000000, -9000000000000], [5115000000000, 9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([2520000000000], [5115000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([0], [990000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 4, 2)) (.next ([-990000000000,
      -9000000000000], [8115000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1365000000000], [8115000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0,
      -9000000000000], [375000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-885000000000],
      [3885000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-375000000000], [1365000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4125000000000], [8010000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5115000000000, -9000000000000], [8010000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5115000000000], [7635000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2)))))))))))))))))))))
      (.witnessedFan (.next ([7125000000000], [990000000000, 9000000000000]) (some (2, 0, 4)) (some
      (3, 0, 4)) (.next ([6750000000000], [1365000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next
      ([3000000000000], [885000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([375000000000,
      -9000000000000], [0, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([990000000000],
      [375000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([3885000000000], [4125000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2895000000000, -9000000000000], [5115000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2520000000000], [5115000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0], [990000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 4, 2)) (.next ([-990000000000, -9000000000000], [8115000000000, 9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1365000000000], [8115000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-885000000000], [3885000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([0, -9000000000000], [375000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-375000000000], [1365000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4125000000000],
      [8010000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5115000000000, -9000000000000],
      [8010000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5115000000000], [7635000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4,
      2))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded28_1
    · exact excluded28_2
    · exact excluded28_3
    · exact excluded28_4
    · exact excluded28_5
    · exact excluded28_6
    · exact excluded28_7
    · exact excluded28_8
    · exact excluded28_9
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded29_1 : ExcludedOn (model29.B 1 ++ [step29.q]) 9000000000000 (model29.caps 1)
    (model29.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_2 : ExcludedOn (model29.B 2 ++ [step29.q]) 9000000000000 (model29.caps 2)
    (model29.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([8010000000000, -9000000000000],
      [990000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5385000000000,
      -9000000000000], [3615000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([990000000000],
      [2625000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, -9000000000000],
      [2625000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-990000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-3615000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2625000000000],
      [3615000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_3 : ExcludedOn (model29.B 3 ++ [step29.q]) 9000000000000 (model29.caps 3)
    (model29.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([375000000000, -9000000000000], [0,
      9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([990000000000], [375000000000])
      (some (3, 0, 4)) (some (3, 1, 4)) (.next ([1740000000000], [885000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([2625000000000], [5385000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1635000000000, -9000000000000], [6375000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1260000000000], [6375000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([0], [990000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 4, 2)) (.next ([0,
      -9000000000000], [375000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-375000000000],
      [1365000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-885000000000], [2625000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5385000000000], [8010000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-6375000000000, -9000000000000], [8010000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-6375000000000], [7635000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded29_1
    · exact excluded29_2
    · exact excluded29_3
    · exact excluded29_4
    · exact excluded29_5
    · exact excluded29_6
    · exact excluded29_7
    · exact excluded29_8
    · exact excluded29_9
theorem next29 : model29.insert step29 = model30 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded30_1 : ExcludedOn (model30.B 1 ++ [step30.q]) 9000000000000 (model30.caps 1)
    (model30.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7578000000000], [297000000000]) none none (.next
      ([8103000000000], [522000000000]) none none (.next ([1485000000000, 0], [240000000000,
      9000000000000]) none none (.next ([6843000000000], [1782000000000]) (some (4, 1, 3)) (some (4,
      1, 3)) (.next ([5853000000000, -9000000000000], [1782000000000, 0]) (some (4, 1, 3)) (some (4,
      1, 3)) (.next ([525000000000], [225000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1260000000000, 0], [990000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next
      ([750000000000], [735000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([0, 0],
      [990000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-297000000000],
      [7875000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-522000000000], [8625000000000])
      (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-240000000000, -9000000000000], [1725000000000,
      9000000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-1782000000000], [8625000000000])
      (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-1782000000000, 0], [7635000000000,
      -9000000000000]) (some (4, 2, 0)) (some (4, 2, 0)) (.next ([-225000000000], [750000000000])
      (some (4, 2, 0)) (some (4, 2, 4)) (.next ([-990000000000, -9000000000000], [2250000000000,
      9000000000000]) (some (4, 2, 4)) (some (4, 2, 4)) (.next ([-735000000000], [1485000000000])
      (some (4, 2, 4)) (some (4, 2, 4)) (.terminal (some (4, 2, 4)) none none)))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_2 : ExcludedOn (model30.B 2 ++ [step30.q]) 9000000000000 (model30.caps 2)
    (model30.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8010000000000, -9000000000000], [990000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1782000000000], [375000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5853000000000, -9000000000000], [1782000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([792000000000, -9000000000000], [1365000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-990000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-375000000000],
      [2157000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1782000000000, 0],
      [7635000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1365000000000,
      -9000000000000], [2157000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_3 : ExcludedOn (model30.B 3 ++ [step30.q]) 9000000000000 (model30.caps 3)
    (model30.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2157000000000], [93000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([7125000000000], [990000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([6750000000000], [1365000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([990000000000], [375000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([2157000000000], [7218000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([1167000000000,
      -9000000000000], [8208000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([792000000000], [8208000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [990000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 4, 4)) (.next ([-93000000000],
      [2250000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-990000000000, -9000000000000],
      [8115000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1365000000000],
      [8115000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-375000000000], [1365000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-7218000000000], [9375000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-8208000000000, -9000000000000], [9375000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-8208000000000], [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_4 : ExcludedOn (model30.B 4 ++ [step30.q]) 9000000000000 (model30.caps 4)
    (model30.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_7 : ExcludedOn (model30.B 7 ++ [step30.q]) 9000000000000 (model30.caps 7)
    (model30.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded30_1
    · exact excluded30_2
    · exact excluded30_3
    · exact excluded30_4
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
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_1 : ExcludedOn (model31.B 1 ++ [step31.q]) 9000000000000 (model31.caps 1)
    (model31.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_3 : ExcludedOn (model31.B 3 ++ [step31.q]) 9000000000000 (model31.caps 3)
    (model31.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8970000000000], [30000000000]) (some (0, 0, 5))
      (some (0, 1, 5)) (.next ([2970000000000], [30000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([6000000000000, 0], [990000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 5, 5))
      fan31Owner5Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_6 : ExcludedOn (model31.B 6 ++ [step31.q]) 9000000000000 (model31.caps 6)
    (model31.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2070000000000], [240000000000, 9000000000000])
      (some (0, 5, 3)) (some (0, 5, 4)) (.next ([1875000000000], [495000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([825000000000], [300000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([6000000000000], [2970000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([5010000000000, -9000000000000], [2970000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([6000000000000], [3960000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([3930000000000], [3720000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([990000000000,
      9000000000000], [990000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([3630000000000], [4845000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([750000000000],
      [1320000000000]) (some (0, 5, 4)) (some (5, 5, 4)) (.next ([495000000000, 9000000000000],
      [1380000000000, -9000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([0, 0],
      [990000000000, 9000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-240000000000,
      -9000000000000], [2310000000000, 9000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next
      ([-495000000000], [2370000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-300000000000],
      [1125000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-2970000000000], [8970000000000])
      (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-2970000000000, 0], [7980000000000,
      -9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-3960000000000, -9000000000000],
      [9960000000000, 9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-3720000000000],
      [7650000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-990000000000, -9000000000000],
      [1980000000000, 18000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4845000000000],
      [8475000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-1320000000000], [2070000000000])
      (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-1380000000000, 9000000000000], [1875000000000])
      (some (5, 3, 4)) (some (5, 3, 0)) (.terminal (some (5, 3, 0)) (some (5, 3, 0)) (some (5, 3,
      0))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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

end Sint110000120000
end ConwaySoifer.Simplified.Certificates
