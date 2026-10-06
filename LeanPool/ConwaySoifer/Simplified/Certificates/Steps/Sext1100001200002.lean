/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext110000120000
import Mathlib.Tactic.FinCases

/-!
# Sext 110000 120000 2

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
namespace Sext110000120000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan17Owner4Part0 : FanWitness := (.next ([3135000000000], [1875000000000]) (some (5, 1, 1))
    (some (5, 1, 1)) (.next ([3060000000000], [2190000000000]) (some (5, 1, 1)) (some (5, 1, 2))
    (.next ([4830000000000], [4920000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([1740000000000, 9000000000000], [2070000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1,
    2)) (.next ([1770000000000], [2730000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([1695000000000], [3045000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1080000000000],
    [2760000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next ([990000000000],
    [3135000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1080000000000], [3750000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([750000000000], [3060000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([990000000000, 9000000000000], [6000000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([0], [6000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([-75000000000], [315000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1875000000000],
    [5010000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2190000000000], [5250000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4920000000000], [9750000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-2070000000000, 9000000000000], [3810000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-2730000000000], [4500000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-3045000000000], [4740000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-2760000000000, 9000000000000], [3840000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([-3135000000000], [4125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-3750000000000], [4830000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3060000000000],
    [3810000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-6000000000000], [6990000000000,
    9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1, 5)) (some (0, 1, 5))
    (some (0, 1, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part0 : FanWitness := (.next ([-4209600000000, 2640000000000], [5780400000000,
    2640000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4719600000000, 2640000000000],
    [6290400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4500000000000],
    [5958000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5010000000000], [6468000000000])
    (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4790400000000, -2640000000000], [6070800000000,
    5280000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4959600000000, 2640000000000],
    [6230400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5300400000000,
    -2640000000000], [6580800000000, 5280000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-5250000000000], [6408000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-660000000000],
    [795000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5004600000000, 2640000000000],
    [5915400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5540400000000,
    -2640000000000], [6520800000000, 5280000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-7925400000000, -2640000000000], [9205800000000, 5280000000000]) (some (9, 4, 8)) (some (9, 4,
    8)) (.next ([-5295000000000], [6093000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-315000000000], [360000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5080800000000,
    -5280000000000], [5780400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 5, 8)) (.next
    ([-5590800000000, -5280000000000], [6290400000000, 2640000000000]) (some (9, 5, 8)) (some (9, 5,
    8)) (.next ([-5585400000000, -2640000000000], [6205800000000, 5280000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-7344600000000, 2640000000000], [8044200000000, -5280000000000]) (some
    (9, 5, 8)) (some (9, 5, 8)) (.next ([-8215800000000, -5280000000000], [8915400000000,
    2640000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5300400000000, -2640000000000],
    [5709600000000, -2640000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5830800000000,
    -5280000000000], [6230400000000, 2640000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-7925400000000, -2640000000000], [8334600000000, -2640000000000]) (some (9, 5, 8)) (some (9,
    5, 8)) (.next ([-5540400000000, -2640000000000], [5649600000000, -2640000000000]) (some (9, 5,
    8)) (some (9, 5, 8)) (.next ([-5875800000000, -5280000000000], [5915400000000, 2640000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.terminal (some (9, 5, 8)) (some (9, 5, 8)) (some (9, 5,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part1 : FanWitness := (.next ([1280400000000, 2640000000000], [7925400000000,
    2640000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([798000000000], [5295000000000]) (some
    (0, 9, 6)) (some (0, 9, 6)) (.next ([45000000000], [315000000000]) (some (0, 9, 6)) (some (0, 9,
    6)) (.next ([699600000000, -2640000000000], [5080800000000, 5280000000000]) (some (0, 9, 6))
    (some (0, 9, 6)) (.next ([699600000000, -2640000000000], [5590800000000, 5280000000000]) (some
    (0, 9, 6)) (some (0, 9, 6)) (.next ([620400000000, 2640000000000], [5585400000000,
    2640000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([699600000000, -2640000000000],
    [7344600000000, -2640000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([699600000000,
    -2640000000000], [8215800000000, 5280000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next
    ([409200000000, -5280000000000], [5300400000000, 2640000000000]) (some (0, 9, 6)) (some (0, 9,
    6)) (.next ([399600000000, -2640000000000], [5830800000000, 5280000000000]) (some (0, 9, 6))
    (some (0, 9, 6)) (.next ([409200000000, -5280000000000], [7925400000000, 2640000000000]) (some
    (0, 9, 6)) (some (0, 9, 6)) (.next ([109200000000, -5280000000000], [5540400000000,
    2640000000000]) (some (0, 9, 6)) (some (9, 9, 6)) (.next ([39600000000, -2640000000000],
    [5875800000000, 5280000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([0, 0], [871200000000,
    7920000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([-250800000000, -5280000000000],
    [5585400000000, 2640000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([-60000000000],
    [300000000000]) (some (9, 9, 6)) (some (9, 9, 6)) (.next ([-1695000000000], [7935000000000])
    (some (9, 9, 6)) (some (9, 9, 6)) (.next ([-1635000000000], [7635000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-2010000000000], [8295000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([-2145000000000], [7635000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-300000000000], [750000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-290400000000,
    -2640000000000], [580800000000, 5280000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-375000000000], [660000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-758400000000,
    -2640000000000], [1048800000000, 5280000000000]) (some (9, 4, 8)) (some (9, 4, 8))
    fan20Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner4Part0 : FanWitness := (.next ([3135000000000], [1875000000000]) (some (4, 5, 5))
    (some (4, 5, 5)) (.next ([3060000000000], [2190000000000]) (some (4, 5, 5)) (some (4, 5, 5))
    (.next ([1980000000000, 9000000000000], [2145000000000, -9000000000000]) (some (4, 5, 5)) (some
    (4, 5, 5)) (.next ([1740000000000, 9000000000000], [2070000000000, -9000000000000]) (some (4, 5,
    5)) (some (4, 5, 5)) (.next ([2760000000000], [3885000000000]) (some (4, 5, 5)) (some (4, 5, 5))
    (.next ([2685000000000], [4200000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([990000000000], [3135000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([750000000000],
    [3060000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([990000000000, 9000000000000],
    [6000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([615000000000, 9000000000000],
    [8010000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0], [6000000000000]) (some (4, 5,
    2)) (some (4, 5, 2)) (.next ([-375000000000], [8010000000000]) (some (0, 5, 2)) (some (0, 5, 2))
    (.next ([-375000000000], [2010000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
    ([-75000000000], [315000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([-1875000000000],
    [5010000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next ([-2190000000000], [5250000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2145000000000, 9000000000000], [4125000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2070000000000, 9000000000000], [3810000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3885000000000], [6645000000000]) (some (0, 5, 3))
    (some (0, 5, 4)) (.next ([-4200000000000], [6885000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-3135000000000], [4125000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-3060000000000], [3810000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-6000000000000],
    [6990000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-8010000000000],
    [8625000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5, 4))
    (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner3Part0 : FanWitness := (.next ([5040000000000], [4020000000000]) (some (6, 1, 2))
    (some (6, 1, 2)) (.next ([990000000000, 9000000000000], [990000000000, 9000000000000]) (some (6,
    1, 2)) (some (6, 1, 2)) (.next ([90000000000], [120000000000]) (some (6, 1, 2)) (some (6, 1, 2))
    (.next ([1980000000000, 9000000000000], [3270000000000, -9000000000000]) (some (6, 1, 2)) (some
    (6, 1, 3)) (.next ([1890000000000, 9000000000000], [3150000000000, -9000000000000]) (some (6, 1,
    3)) (some (6, 1, 3)) (.next ([990000000000, 9000000000000], [3930000000000, -9000000000000])
    (some (6, 1, 3)) (some (6, 1, 4)) (.next ([990000000000], [4260000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([900000000000], [4140000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([0], [990000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([-90000000000, 9000000000000], [5250000000000]) (some (6, 1, 4)) (some (6, 2, 4)) (.next
    ([-90000000000, -9000000000000], [4140000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-210000000000], [3270000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-750000000000],
    [6000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1080000000000], [5250000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1080000000000], [4260000000000, -9000000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-3930000000000], [9180000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-4020000000000], [9060000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (6, 2, 4)) (some
    (6, 2, 4)) (.next ([-120000000000], [210000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-3270000000000, 9000000000000], [5250000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-3150000000000, 9000000000000], [5040000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-3930000000000, 9000000000000], [4920000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-4260000000000], [5250000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-4140000000000],
    [5040000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.terminal (some (6, 2, 4)) (some (6, 2, 4))
    (some (6, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner4Part0 : FanWitness := (.next ([1980000000000, 9000000000000], [2145000000000,
    -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1740000000000, 9000000000000],
    [2070000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4125000000000],
    [5340000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1065000000000], [3150000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([990000000000], [3135000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([990000000000], [3465000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([660000000000], [2475000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 5))
    (.next ([750000000000], [3060000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([660000000000], [3465000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([990000000000,
    9000000000000], [6000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [6000000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-75000000000], [315000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([-1875000000000], [5010000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-2190000000000], [5250000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2145000000000,
    9000000000000], [4125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2070000000000,
    9000000000000], [3810000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5340000000000],
    [9465000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3150000000000], [4215000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3135000000000], [4125000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-3465000000000], [4455000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-2475000000000, 9000000000000], [3135000000000, -9000000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([-3060000000000], [3810000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-3465000000000], [4125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-6000000000000],
    [6990000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1, 5))
    (some (0, 1, 5)) (some (0, 1, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner0Part0 : FanWitness := (.next ([-290400000000, -2640000000000], [580800000000,
    5280000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-375000000000], [660000000000]) (some
    (9, 4, 7)) (some (9, 4, 7)) (.next ([-758400000000, -2640000000000], [1048800000000,
    5280000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4209600000000, 2640000000000],
    [5780400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4719600000000,
    2640000000000], [6290400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-4500000000000], [5958000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5010000000000],
    [6468000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4790400000000, -2640000000000],
    [6070800000000, 5280000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-4959600000000,
    2640000000000], [6230400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-5300400000000, -2640000000000], [6580800000000, 5280000000000]) (some (9, 4, 8)) (some (9, 4,
    8)) (.next ([-5250000000000], [6408000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-660000000000], [795000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5004600000000,
    2640000000000], [5915400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-5540400000000, -2640000000000], [6520800000000, 5280000000000]) (some (9, 4, 8)) (some (9, 4,
    8)) (.next ([-5295000000000], [6093000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next
    ([-315000000000], [360000000000]) (some (9, 4, 8)) (some (9, 4, 8)) (.next ([-5080800000000,
    -5280000000000], [5780400000000, 2640000000000]) (some (9, 4, 8)) (some (9, 5, 8)) (.next
    ([-5590800000000, -5280000000000], [6290400000000, 2640000000000]) (some (9, 5, 8)) (some (9, 5,
    8)) (.next ([-5585400000000, -2640000000000], [6205800000000, 5280000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-4790400000000, -2640000000000], [5199600000000, -2640000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5300400000000, -2640000000000], [5709600000000,
    -2640000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5830800000000, -5280000000000],
    [6230400000000, 2640000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5540400000000,
    -2640000000000], [5649600000000, -2640000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-5875800000000, -5280000000000], [5915400000000, 2640000000000]) (some (9, 5, 8)) (some (9, 5,
    8)) (.terminal (some (9, 5, 8)) (some (9, 5, 8)) (some (9, 5, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner0Part1 : FanWitness := (.next ([910800000000, 5280000000000], [5004600000000,
    -2640000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([980400000000, 2640000000000],
    [5540400000000, 2640000000000]) (some (9, 3, 5)) (some (9, 3, 6)) (.next ([798000000000],
    [5295000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([45000000000], [315000000000]) (some
    (9, 3, 6)) (some (9, 3, 6)) (.next ([699600000000, -2640000000000], [5080800000000,
    5280000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([699600000000, -2640000000000],
    [5590800000000, 5280000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([620400000000,
    2640000000000], [5585400000000, 2640000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([409200000000, -5280000000000], [4790400000000, 2640000000000]) (some (9, 3, 6)) (some (9, 3,
    6)) (.next ([409200000000, -5280000000000], [5300400000000, 2640000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([399600000000, -2640000000000], [5830800000000, 5280000000000]) (some
    (9, 3, 6)) (some (9, 3, 6)) (.next ([109200000000, -5280000000000], [5540400000000,
    2640000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([39600000000, -2640000000000],
    [5875800000000, 5280000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([0, 0], [871200000000,
    7920000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-250800000000, -5280000000000],
    [5585400000000, 2640000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-290400000000,
    -2640000000000], [5320800000000, 5280000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([-290400000000, -2640000000000], [4449600000000, -2640000000000]) (some (9, 3, 6)) (some (9, 3,
    6)) (.next ([-468000000000], [5208000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([-580800000000, -5280000000000], [5030400000000, 2640000000000]) (some (9, 3, 6)) (some (9, 3,
    6)) (.next ([-60000000000], [300000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([-3750000000000], [9750000000000]) (some (9, 3, 6)) (some (9, 4, 6)) (.next ([-300000000000],
    [750000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-4050000000000], [9990000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-3750000000000], [9240000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-4410000000000], [10035000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    fan23Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner3Part0 : FanWitness := (.next ([90000000000], [120000000000]) (some (5, 6, 2)) (some
    (5, 6, 2)) (.next ([1980000000000, 9000000000000], [3270000000000, -9000000000000]) (some (5, 6,
    2)) (some (5, 6, 3)) (.next ([1890000000000, 9000000000000], [3150000000000, -9000000000000])
    (some (5, 6, 3)) (some (5, 6, 3)) (.next ([990000000000], [4260000000000]) (some (5, 6, 3))
    (some (5, 6, 4)) (.next ([900000000000], [4140000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([330000000000, 9000000000000], [5535000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([0], [990000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0,
    -9000000000000], [4260000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-120000000000],
    [3960000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-135000000000], [3600000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-285000000000], [3885000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-660000000000], [5535000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-495000000000], [3975000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-660000000000], [4545000000000, -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-3270000000000, 9000000000000], [9000000000000]) (some (0, 6, 4)) (some (1, 6, 4)) (.next
    ([-4260000000000], [9000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-990000000000,
    -9000000000000], [1980000000000, 18000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next
    ([-4260000000000], [8010000000000, -9000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next
    ([-120000000000], [210000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-3270000000000,
    9000000000000], [5250000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-3150000000000,
    9000000000000], [5040000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4260000000000],
    [5250000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4140000000000], [5040000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-5535000000000, 0], [5865000000000, 9000000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.terminal (some (1, 6, 4)) (some (1, 2, 4)) (some (1, 6,
    4)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1260000000000, -9000000000000], [522000000000,
      9000000000000]) (some (3, 5, 2)) (some (4, 5, 2)) (.next ([1125000000000], [660000000000])
      (some (4, 5, 2)) (some (4, 5, 3)) (.next ([4827000000000], [3705000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([990000000000, 9000000000000], [990000000000, 9000000000000]) (some
      (4, 5, 3)) (some (4, 5, 3)) (.next ([3705000000000], [4170000000000]) (some (4, 5, 3)) (some
      (4, 5, 3)) (.next ([465000000000], [657000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([4035000000000, 9000000000000], [5955000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([3045000000000], [4965000000000, -9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([3045000000000], [5955000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([468000000000],
      [1782000000000]) (some (4, 5, 3)) (some (5, 5, 3)) (.next ([330000000000, 9000000000000],
      [1785000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next ([0], [990000000000, 9000000000000])
      (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-522000000000, -9000000000000], [1782000000000])
      (some (5, 5, 3)) (some (5, 5, 3)) (.next ([-660000000000], [1785000000000]) (some (5, 5, 3))
      (some (5, 5, 3)) (.next ([-3705000000000], [8532000000000]) (some (5, 5, 3)) (some (5, 5, 3))
      (.next ([-990000000000, -9000000000000], [1980000000000, 18000000000000]) (some (5, 2, 3))
      (some (5, 2, 3)) (.next ([-4170000000000], [7875000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([-657000000000], [1122000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-5955000000000, 0], [9990000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-4965000000000, 9000000000000], [8010000000000, -9000000000000]) (some (5, 2, 3)) (some (5,
      2, 3)) (.next ([-5955000000000], [9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-1782000000000], [2250000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1785000000000,
      0], [2115000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.terminal (some (5, 2,
      3)) (some (5, 2, 3)) (some (5, 2, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded16_0
    · exact excluded16_1
    · exact excluded16_2
    · exact excluded16_3
    · exact excluded16_4
    · exact excluded16_5
    · exact excluded16_6
    · exact excluded16_7
    · exact (hj rfl).elim
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded17_0 : ExcludedOn (model17.B 0 ++ [step17.q]) 9000000000000 (model17.caps 0)
    (model17.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([240000000000], [75000000000]) (some (5, 0, 1))
      (some (5, 1, 1)) fan17Owner4Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [705000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([5250000000000], [3048000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([5250000000000], [4830000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1782000000000], [4173000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5955000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-705000000000], [4830000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3048000000000], [8298000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([-4830000000000], [10080000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4173000000000], [5955000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded17_0
    · exact excluded17_1
    · exact excluded17_2
    · exact (hj rfl).elim
    · exact excluded17_4
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
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5850000000000, 9000000000000], [4050000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([990000000000, 9000000000000],
      [990000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4860000000000],
      [5040000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3870000000000, -9000000000000],
      [5040000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([-4050000000000, 9000000000000],
      [9900000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-990000000000, -9000000000000],
      [1980000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-5040000000000],
      [9900000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-5040000000000, 0],
      [8910000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2))
      (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded18_0
    · exact excluded18_1
    · exact excluded18_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5730000000000, 9000000000000], [4260000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([990000000000, 9000000000000],
      [990000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4740000000000],
      [5250000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3750000000000, -9000000000000],
      [5250000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0], [990000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([-4260000000000, 9000000000000],
      [9990000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-990000000000, -9000000000000],
      [1980000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-5250000000000],
      [9990000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-5250000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2))
      (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5334600000000, -2640000000000], [250800000000,
      5280000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([240000000000], [60000000000]) (some
      (8, 9, 5)) (some (8, 9, 5)) (.next ([6240000000000], [1695000000000]) (some (8, 9, 5)) (some
      (8, 9, 5)) (.next ([6000000000000], [1635000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
      ([6285000000000], [2010000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([5490000000000],
      [2145000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([450000000000], [300000000000])
      (some (8, 9, 5)) (some (8, 9, 5)) (.next ([290400000000, 2640000000000], [290400000000,
      2640000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([285000000000], [375000000000])
      (some (0, 9, 5)) (some (0, 9, 5)) (.next ([290400000000, 2640000000000], [758400000000,
      2640000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([1570800000000, 5280000000000],
      [4209600000000, -2640000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([1570800000000,
      5280000000000], [4719600000000, -2640000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next
      ([1458000000000], [4500000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([1458000000000],
      [5010000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([1280400000000, 2640000000000],
      [4790400000000, 2640000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([1270800000000,
      5280000000000], [4959600000000, -2640000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next
      ([1280400000000, 2640000000000], [5300400000000, 2640000000000]) (some (0, 9, 5)) (some (0, 9,
      5)) (.next ([1158000000000], [5250000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next
      ([135000000000], [660000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([910800000000,
      5280000000000], [5004600000000, -2640000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next
      ([980400000000, 2640000000000], [5540400000000, 2640000000000]) (some (0, 9, 5)) (some (0, 9,
      6)) fan20Owner0Part1)))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7635000000000], [375000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([1635000000000], [375000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([240000000000], [75000000000]) (some (4, 1, 5)) (some (4, 5, 5)) fan20Owner4Part0))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded20_6
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5160000000000, 9000000000000], [90000000000,
      -9000000000000]) (some (4, 6, 2)) (some (6, 6, 2)) (.next ([4050000000000, -9000000000000],
      [90000000000, 9000000000000]) (some (6, 6, 2)) (some (6, 6, 2)) (.next ([3060000000000],
      [210000000000]) (some (6, 6, 2)) (some (6, 6, 2)) (.next ([5250000000000], [750000000000])
      (some (6, 6, 2)) (some (6, 6, 2)) (.next ([4170000000000], [1080000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) (.next ([3180000000000, -9000000000000], [1080000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) (.next ([5250000000000], [3930000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      fan21Owner3Part0)))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([240000000000], [75000000000]) (some (5, 0, 1))
      (some (5, 1, 1)) (.next ([3135000000000], [1875000000000]) (some (5, 1, 1)) (some (5, 1, 1))
      (.next ([3060000000000], [2190000000000]) (some (5, 1, 1)) (some (5, 1, 2))
      fan22Owner4Part0))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5535000000000], [45000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([3705000000000], [420000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([4080000000000], [1875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([5535000000000], [4125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5955000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-45000000000], [5580000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-420000000000], [4125000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1875000000000], [5955000000000]) (some (0, 1, 2)) (some (0, 3, 2))
      (.next ([-4125000000000], [9660000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded22_4
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5334600000000, -2640000000000], [250800000000,
      5280000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([5030400000000, 2640000000000],
      [290400000000, 2640000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([4159200000000,
      -5280000000000], [290400000000, 2640000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
      ([4740000000000], [468000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([4449600000000,
      -2640000000000], [580800000000, 5280000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
      ([240000000000], [60000000000]) (some (8, 9, 5)) (some (9, 9, 5)) (.next ([6000000000000],
      [3750000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next ([450000000000], [300000000000])
      (some (9, 3, 5)) (some (9, 3, 5)) (.next ([5940000000000], [4050000000000]) (some (9, 3, 5))
      (some (9, 3, 5)) (.next ([5490000000000], [3750000000000]) (some (9, 3, 5)) (some (9, 3, 5))
      (.next ([5625000000000], [4410000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
      ([290400000000, 2640000000000], [290400000000, 2640000000000]) (some (9, 3, 5)) (some (9, 3,
      5)) (.next ([285000000000], [375000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
      ([290400000000, 2640000000000], [758400000000, 2640000000000]) (some (9, 3, 5)) (some (9, 3,
      5)) (.next ([1570800000000, 5280000000000], [4209600000000, -2640000000000]) (some (9, 3, 5))
      (some (9, 3, 5)) (.next ([1570800000000, 5280000000000], [4719600000000, -2640000000000])
      (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1458000000000], [4500000000000]) (some (9, 3, 5))
      (some (9, 3, 5)) (.next ([1458000000000], [5010000000000]) (some (9, 3, 5)) (some (9, 3, 5))
      (.next ([1280400000000, 2640000000000], [4790400000000, 2640000000000]) (some (9, 3, 5)) (some
      (9, 3, 5)) (.next ([1270800000000, 5280000000000], [4959600000000, -2640000000000]) (some (9,
      3, 5)) (some (9, 3, 5)) (.next ([1280400000000, 2640000000000], [5300400000000,
      2640000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1158000000000], [5250000000000])
      (some (9, 3, 5)) (some (9, 3, 5)) (.next ([135000000000], [660000000000]) (some (9, 3, 5))
      (some (9, 3, 5)) fan23Owner0Part1)))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4260000000000, -9000000000000], [0,
      9000000000000]) (some (4, 1, 2)) (some (5, 1, 2)) (.next ([3840000000000], [120000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3465000000000], [135000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([3600000000000], [285000000000]) (some (5, 1, 2)) (some (5, 6, 2))
      (.next ([4875000000000], [660000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([3480000000000], [495000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([3885000000000,
      -9000000000000], [660000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([5730000000000,
      9000000000000], [3270000000000, -9000000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([4740000000000], [4260000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([990000000000,
      9000000000000], [990000000000, 9000000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([3750000000000, -9000000000000], [4260000000000]) (some (5, 6, 2)) (some (5, 6, 2))
      fan23Owner3Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded23_3
    · exact (hj rfl).elim
    · exact excluded23_5
    · exact excluded23_6
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext110000120000
end ConwaySoifer.Simplified.Certificates
