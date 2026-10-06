/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint210000220000
import Mathlib.Tactic.FinCases

/-!
# Sint 210000 220000 2

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
namespace Sint210000220000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part0 : FanWitness := (.next ([-255000000000], [1635000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-352800000000, -4680000000000], [866400000000, 2340000000000]) (some
    (9, 3, 5)) (some (9, 3, 5)) (.next ([-1005000000000], [2010000000000]) (some (9, 3, 5)) (some
    (9, 3, 5)) (.next ([-5295000000000], [10275000000000]) (some (9, 3, 5)) (some (9, 4, 5)) (.next
    ([-5295000000000], [9900000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-5415000000000],
    [10065000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-607800000000, -4680000000000],
    [1121400000000, 2340000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-210000000000],
    [330000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-3408600000000, 2340000000000],
    [4766400000000, 2340000000000]) (some (9, 4, 5)) (some (9, 4, 6)) (.next ([-3525000000000],
    [4905000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-120000000000], [165000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-5178600000000, 2340000000000], [6866400000000,
    2340000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-5295000000000], [7005000000000])
    (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-2917200000000, 4680000000000], [3783600000000,
    -2340000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-5298600000000, 2340000000000],
    [6656400000000, 2340000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-5178600000000,
    2340000000000], [6491400000000, 2340000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-5295000000000], [6630000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-4275000000000],
    [5280000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-6161400000000, -2340000000000],
    [7357800000000, 4680000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-6281400000000,
    -2340000000000], [7147800000000, 4680000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-6161400000000, -2340000000000], [6982800000000, 4680000000000]) (some (9, 4, 6)) (some (9, 4,
    6)) (.next ([-1357800000000, -4680000000000], [1496400000000, 2340000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-6652800000000, -4680000000000], [6866400000000, 2340000000000]) (some
    (9, 4, 6)) (some (9, 4, 6)) (.next ([-6675000000000], [6750000000000]) (some (9, 4, 6)) (some
    (9, 4, 6)) (.terminal (some (9, 4, 6)) (some (9, 4, 6)) (some (9, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part1 : FanWitness := (.next ([1380000000000], [3525000000000]) (some (9, 2, 5))
    (some (9, 2, 5)) (.next ([45000000000], [120000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
    ([1687800000000, 4680000000000], [5178600000000, -2340000000000]) (some (9, 2, 5)) (some (9, 2,
    5)) (.next ([1710000000000], [5295000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
    ([866400000000, 2340000000000], [2917200000000, -4680000000000]) (some (9, 2, 5)) (some (9, 2,
    5)) (.next ([1357800000000, 4680000000000], [5298600000000, -2340000000000]) (some (9, 2, 5))
    (some (9, 2, 5)) (.next ([1312800000000, 4680000000000], [5178600000000, -2340000000000]) (some
    (9, 2, 5)) (some (9, 2, 5)) (.next ([1335000000000], [5295000000000]) (some (9, 2, 5)) (some (9,
    2, 5)) (.next ([1005000000000], [4275000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
    ([1196400000000, 2340000000000], [6161400000000, 2340000000000]) (some (9, 2, 5)) (some (9, 2,
    5)) (.next ([866400000000, 2340000000000], [6281400000000, 2340000000000]) (some (9, 2, 5))
    (some (9, 2, 5)) (.next ([821400000000, 2340000000000], [6161400000000, 2340000000000]) (some
    (9, 2, 5)) (some (9, 2, 5)) (.next ([138600000000, -2340000000000], [1357800000000,
    4680000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([213600000000, -2340000000000],
    [6652800000000, 4680000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([75000000000],
    [6675000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([0], [3270000000000]) (some (9, 2,
    5)) (some (9, 2, 5)) (.next ([-116400000000, -2340000000000], [6772800000000, 4680000000000])
    (some (9, 2, 5)) (some (9, 3, 5)) (.next ([-161400000000, -2340000000000], [6652800000000,
    4680000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-255000000000], [6795000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-300000000000], [6675000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-300000000000], [6300000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-116400000000, -2340000000000], [1612800000000, 4680000000000]) (some (9, 3, 5)) (some
    (9, 3, 5)) (.next ([-630000000000], [6420000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-675000000000], [6300000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    fan18Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner4Part0 : FanWitness := (.next ([3585000000000], [2445000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([2280000000000], [1875000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([2475000000000], [2055000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([2610000000000, -9000000000000], [2520000000000, 9000000000000]) (some (5, 1, 3)) (some (6, 1,
    3)) (.next ([2055000000000], [2130000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([2100000000000], [5100000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1845000000000],
    [5130000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([30000000000], [225000000000]) (some
    (6, 1, 3)) (some (6, 1, 3)) (.next ([0, 0], [1890000000000, 9000000000000]) (some (6, 1, 3))
    (some (6, 1, 4)) (.next ([-375000000000], [5100000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([-570000000000], [4725000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([-630000000000], [5130000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-600000000000],
    [4500000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-945000000000], [4920000000000])
    (some (6, 1, 4)) (some (6, 1, 5)) (.next ([-1890000000000, -9000000000000], [6420000000000,
    9000000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-945000000000], [2445000000000])
    (some (6, 1, 5)) (some (6, 1, 5)) (.next ([-2445000000000], [6030000000000]) (some (6, 1, 5))
    (some (6, 1, 5)) (.next ([-1875000000000], [4155000000000]) (some (6, 1, 5)) (some (6, 2, 5))
    (.next ([-2055000000000], [4530000000000]) (some (6, 2, 5)) (some (6, 3, 5)) (.next
    ([-2520000000000, -9000000000000], [5130000000000, 0]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-2130000000000], [4185000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-5100000000000],
    [7200000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-5130000000000], [6975000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-225000000000], [255000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.terminal (some (6, 3, 5)) (some (0, 3, 5)) (some (6, 3,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part0 : FanWitness := (.next ([-1278600000000, 2340000000000], [8741400000000,
    2340000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-255000000000], [1635000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-1395000000000], [8880000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([-1140000000000], [7245000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([-1278600000000, 2340000000000], [7267200000000, -4680000000000]) (some (9, 3, 5)) (some
    (9, 3, 5)) (.next ([-2145000000000], [9255000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-352800000000, -4680000000000], [866400000000, 2340000000000]) (some (9, 3, 5)) (some (9, 3,
    5)) (.next ([-1005000000000], [2010000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-607800000000, -4680000000000], [1121400000000, 2340000000000]) (some (9, 3, 5)) (some (9, 4,
    5)) (.next ([-210000000000], [330000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next
    ([-120000000000], [165000000000]) (some (9, 4, 5)) (some (9, 4, 6)) (.next ([-5178600000000,
    2340000000000], [6866400000000, 2340000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-5295000000000], [7005000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-5298600000000,
    2340000000000], [6656400000000, 2340000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-5178600000000, 2340000000000], [6491400000000, 2340000000000]) (some (9, 4, 6)) (some (9, 4,
    6)) (.next ([-5295000000000], [6630000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-6161400000000, -2340000000000], [7357800000000, 4680000000000]) (some (9, 4, 6)) (some (9, 4,
    6)) (.next ([-6281400000000, -2340000000000], [7147800000000, 4680000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-6161400000000, -2340000000000], [6982800000000, 4680000000000]) (some
    (9, 4, 6)) (some (9, 4, 6)) (.next ([-7770000000000], [8580000000000]) (some (9, 4, 6)) (some
    (9, 4, 6)) (.next ([-8145000000000], [8955000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-7935000000000], [8625000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-6652800000000,
    -4680000000000], [6866400000000, 2340000000000]) (some (9, 4, 6)) (some (9, 4, 9)) (.next
    ([-6675000000000], [6750000000000]) (some (9, 4, 9)) (some (9, 4, 9)) (.terminal (some (9, 4,
    9)) (some (9, 4, 9)) (some (9, 4, 9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part1 : FanWitness := (.next ([120000000000], [210000000000]) (some (9, 2, 5)) (some
    (9, 2, 5)) (.next ([45000000000], [120000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
    ([1687800000000, 4680000000000], [5178600000000, -2340000000000]) (some (9, 2, 5)) (some (9, 2,
    5)) (.next ([1710000000000], [5295000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
    ([1357800000000, 4680000000000], [5298600000000, -2340000000000]) (some (9, 2, 5)) (some (9, 2,
    5)) (.next ([1312800000000, 4680000000000], [5178600000000, -2340000000000]) (some (9, 2, 5))
    (some (9, 2, 5)) (.next ([1335000000000], [5295000000000]) (some (9, 2, 5)) (some (9, 2, 5))
    (.next ([1196400000000, 2340000000000], [6161400000000, 2340000000000]) (some (9, 2, 5)) (some
    (9, 2, 5)) (.next ([866400000000, 2340000000000], [6281400000000, 2340000000000]) (some (9, 2,
    5)) (some (9, 2, 5)) (.next ([821400000000, 2340000000000], [6161400000000, 2340000000000])
    (some (9, 2, 5)) (some (9, 2, 5)) (.next ([810000000000], [7770000000000]) (some (9, 2, 5))
    (some (9, 2, 5)) (.next ([810000000000], [8145000000000]) (some (9, 2, 5)) (some (9, 2, 5))
    (.next ([690000000000], [7935000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
    ([213600000000, -2340000000000], [6652800000000, 4680000000000]) (some (9, 2, 5)) (some (9, 2,
    5)) (.next ([75000000000], [6675000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([0, 0],
    [1474200000000, 7020000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([-116400000000,
    -2340000000000], [6772800000000, 4680000000000]) (some (9, 2, 5)) (some (9, 3, 5)) (.next
    ([-161400000000, -2340000000000], [6652800000000, 4680000000000]) (some (9, 3, 5)) (some (9, 3,
    5)) (.next ([-255000000000], [6795000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([-300000000000], [6675000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-300000000000],
    [6300000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-116400000000, -2340000000000],
    [1612800000000, 4680000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-630000000000],
    [6420000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([-675000000000], [6300000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) fan22Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner4Part0 : FanWitness := (.next ([2055000000000], [2130000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([2100000000000], [3750000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([2130000000000], [3975000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([750000000000], [1950000000000]) (some (6, 1, 3)) (some (6, 1, 6)) (.next ([30000000000],
    [225000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([750000000000], [6480000000000]) (some
    (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0], [1890000000000, 9000000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([-375000000000], [5100000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-570000000000], [4725000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-630000000000], [5130000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-600000000000],
    [4500000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1140000000000, -9000000000000],
    [8370000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1695000000000],
    [7980000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1890000000000, -9000000000000],
    [6420000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-945000000000],
    [2445000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2445000000000], [6030000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1875000000000], [4155000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-2520000000000, -9000000000000], [5130000000000, 0]) (some (0, 1, 6))
    (some (0, 3, 6)) (.next ([-2130000000000], [4185000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-3750000000000], [5850000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-3975000000000], [6105000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-1950000000000],
    [2700000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-225000000000], [255000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-6480000000000], [7230000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.terminal (some (0, 3, 6)) (some (0, 3, 6)) (some (0, 3,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner4Part0 : FanWitness := (.next ([2280000000000], [1875000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([4530000000000], [3945000000000]) (some (5, 6, 3)) (some (5, 6, 3))
    (.next ([2610000000000, -9000000000000], [2520000000000, 9000000000000]) (some (5, 6, 3)) (some
    (5, 6, 3)) (.next ([2055000000000], [2130000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
    ([945000000000], [1500000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([780000000000],
    [4320000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([30000000000], [225000000000]) (some
    (5, 6, 3)) (some (5, 6, 3)) (.next ([555000000000], [4575000000000]) (some (5, 6, 3)) (some (5,
    6, 4)) (.next ([0, 0], [1890000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([-375000000000], [5100000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-570000000000],
    [4725000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-630000000000], [5130000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-600000000000], [4500000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-1890000000000, -9000000000000], [6420000000000, 9000000000000]) (some
    (0, 6, 4)) (some (0, 6, 5)) (.next ([-945000000000], [2445000000000]) (some (0, 6, 5)) (some (0,
    6, 5)) (.next ([-2445000000000], [6030000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-1875000000000], [4155000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3945000000000],
    [8475000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2520000000000, -9000000000000],
    [5130000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2130000000000], [4185000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-1500000000000], [2445000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-4320000000000], [5100000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-225000000000], [255000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-4575000000000], [5130000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.terminal (some (0, 3,
    5)) (some (0, 3, 5)) (some (0, 3, 5)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5598000000000], [1542000000000, 9000000000000])
      (some (2, 4, 2)) (some (3, 4, 2)) (.next ([5865000000000], [1890000000000, 9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([5598000000000], [4122000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([5865000000000], [4470000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([267000000000], [348000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([348000000000], [5250000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [1890000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-1542000000000,
      -9000000000000], [7140000000000, 9000000000000]) (some (0, 4, 2)) (some (4, 4, 2)) (.next
      ([-1890000000000, -9000000000000], [7755000000000, 9000000000000]) (some (4, 4, 2)) (some (4,
      4, 2)) (.next ([-4122000000000], [9720000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([-4470000000000], [10335000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-348000000000], [615000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-5250000000000],
      [5598000000000]) (some (4, 1, 2)) (some (4, 2, 2)) (.terminal (some (4, 2, 2)) (some (4, 2,
      2)) (some (4, 2, 2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4470000000000], [4530000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([1695000000000], [4080000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1245000000000], [3225000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([390000000000], [4530000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [4080000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-4530000000000], [9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-4080000000000], [5775000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-3225000000000], [4470000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4530000000000], [4920000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 5 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7500000000000, 0], [945000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([3330000000000], [495000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2775000000000], [555000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([3270000000000, 0], [1890000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([3675000000000], [2385000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([1440000000000, -9000000000000], [2385000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([945000000000], [3285000000000]) (some (4, 1, 2)) (some (4, 1, 3))
      (.next ([945000000000], [6555000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0],
      [3270000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-945000000000, -9000000000000],
      [8445000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next ([-495000000000],
      [3825000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-555000000000], [3330000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-1890000000000, -9000000000000], [5160000000000,
      9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-2385000000000], [6060000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-2385000000000, -9000000000000], [3825000000000])
      (some (4, 2, 3)) (some (4, 2, 4)) (.next ([-3285000000000], [4230000000000]) (some (4, 2, 4))
      (some (4, 2, 4)) (.next ([-6555000000000], [7500000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6656400000000, 2340000000000], [116400000000,
      2340000000000]) (some (6, 9, 4)) (some (6, 9, 4)) (.next ([6491400000000, 2340000000000],
      [161400000000, 2340000000000]) (some (6, 9, 4)) (some (6, 9, 4)) (.next ([6540000000000],
      [255000000000]) (some (6, 9, 4)) (some (6, 9, 4)) (.next ([6375000000000], [300000000000])
      (some (6, 9, 4)) (some (6, 9, 4)) (.next ([6000000000000], [300000000000]) (some (6, 9, 4))
      (some (6, 9, 4)) (.next ([1496400000000, 2340000000000], [116400000000, 2340000000000]) (some
      (6, 9, 4)) (some (6, 9, 5)) (.next ([5790000000000], [630000000000]) (some (6, 9, 5)) (some
      (6, 9, 5)) (.next ([5625000000000], [675000000000]) (some (6, 9, 5)) (some (6, 9, 5)) (.next
      ([1380000000000], [255000000000]) (some (6, 9, 5)) (some (6, 9, 5)) (.next ([513600000000,
      -2340000000000], [352800000000, 4680000000000]) (some (6, 9, 5)) (some (6, 9, 5)) (.next
      ([1005000000000], [1005000000000]) (some (6, 9, 5)) (some (6, 9, 5)) (.next ([4980000000000],
      [5295000000000]) (some (6, 9, 5)) (some (6, 9, 5)) (.next ([4605000000000], [5295000000000])
      (some (6, 9, 5)) (some (6, 9, 5)) (.next ([4650000000000], [5415000000000]) (some (6, 9, 5))
      (some (6, 9, 5)) (.next ([513600000000, -2340000000000], [607800000000, 4680000000000]) (some
      (6, 9, 5)) (some (9, 9, 5)) (.next ([120000000000], [210000000000]) (some (9, 9, 5)) (some (9,
      9, 5)) (.next ([1357800000000, 4680000000000], [3408600000000, -2340000000000]) (some (9, 9,
      5)) (some (9, 9, 5)) fan18Owner0Part1)))))))))))))))))) (den := 9000000000000)
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3330000000000], [495000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([5100000000000], [1005000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([2775000000000], [555000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([3270000000000, 0], [1890000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([5100000000000], [4275000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1440000000000,
      -9000000000000], [2385000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([3210000000000, -9000000000000], [6165000000000, 9000000000000]) (some (4, 1, 2)) (some (4,
      1, 3)) (.next ([1770000000000], [3780000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([0], [3270000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next ([-495000000000],
      [3825000000000]) (some (4, 1, 4)) (some (4, 2, 4)) (.next ([-1005000000000], [6105000000000])
      (some (4, 2, 4)) (some (4, 2, 4)) (.next ([-555000000000], [3330000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1890000000000, -9000000000000], [5160000000000, 9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4275000000000], [9375000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2385000000000, -9000000000000], [3825000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-6165000000000, -9000000000000], [9375000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3780000000000], [5550000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3330000000000], [495000000000]) (some (3, 0, 4))
      (some (3, 4, 4)) (.next ([2775000000000], [555000000000]) (some (3, 4, 4)) (some (3, 4, 4))
      (.next ([3270000000000, 0], [1890000000000, 9000000000000]) (some (0, 4, 4)) (some (0, 4, 4))
      (.next ([1890000000000, 9000000000000], [3330000000000, -9000000000000]) (some (0, 4, 4))
      (some (0, 4, 4)) (.next ([0], [3270000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next
      ([-495000000000], [3825000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-555000000000],
      [3330000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1890000000000, -9000000000000],
      [5160000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3330000000000,
      9000000000000], [5220000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4, 3))
      (some (0, 4, 3)) (some (0, 4, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded19_6
    · exact excluded19_7
    · exact excluded19_8
    · exact (hj rfl).elim
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1890000000000, 9000000000000], [1890000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([3402000000000], [4110000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3402000000000], [6000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1512000000000, -9000000000000], [7890000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1890000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-1890000000000, -9000000000000],
      [3780000000000, 18000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-4110000000000,
      9000000000000], [7512000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-6000000000000], [9402000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7890000000000,
      -9000000000000], [9402000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
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
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3330000000000], [495000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([2775000000000], [555000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([5598000000000], [3000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([3270000000000, 0], [1890000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([3708000000000, -9000000000000], [3000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1440000000000, -9000000000000], [2385000000000, 9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([825000000000], [5268000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([270000000000], [8598000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [3270000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-495000000000], [3825000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-555000000000], [3330000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3000000000000], [8598000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1890000000000, -9000000000000], [5160000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3000000000000, 0], [6708000000000, -9000000000000]) (some (0, 2,
      4)) (some (0, 2, 4)) (.next ([-2385000000000, -9000000000000], [3825000000000]) (some (0, 2,
      4)) (some (0, 4, 4)) (.next ([-5268000000000], [6093000000000]) (some (0, 4, 4)) (some (0, 4,
      4)) (.next ([-8598000000000], [8868000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal
      (some (0, 4, 3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4725000000000], [375000000000]) (some (5, 0, 3))
      (some (5, 1, 3)) (.next ([4155000000000], [570000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([4500000000000], [630000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([3900000000000], [600000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3975000000000],
      [945000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4530000000000, 0], [1890000000000,
      9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1500000000000], [945000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) fan21Owner4Part0)))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6656400000000, 2340000000000], [116400000000,
      2340000000000]) (some (9, 9, 4)) (some (9, 9, 4)) (.next ([6491400000000, 2340000000000],
      [161400000000, 2340000000000]) (some (9, 9, 4)) (some (9, 9, 4)) (.next ([6540000000000],
      [255000000000]) (some (9, 9, 4)) (some (9, 9, 4)) (.next ([6375000000000], [300000000000])
      (some (9, 9, 4)) (some (9, 9, 4)) (.next ([6000000000000], [300000000000]) (some (9, 9, 4))
      (some (9, 9, 4)) (.next ([1496400000000, 2340000000000], [116400000000, 2340000000000]) (some
      (9, 9, 4)) (some (9, 9, 5)) (.next ([5790000000000], [630000000000]) (some (9, 9, 5)) (some
      (9, 9, 5)) (.next ([5625000000000], [675000000000]) (some (9, 9, 5)) (some (9, 1, 5)) (.next
      ([7462800000000, 4680000000000], [1278600000000, -2340000000000]) (some (9, 1, 5)) (some (9,
      1, 5)) (.next ([1380000000000], [255000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next
      ([7485000000000], [1395000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([6105000000000],
      [1140000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([5988600000000, -2340000000000],
      [1278600000000, -2340000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([7110000000000],
      [2145000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([513600000000, -2340000000000],
      [352800000000, 4680000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([1005000000000],
      [1005000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([513600000000, -2340000000000],
      [607800000000, 4680000000000]) (some (9, 1, 5)) (some (9, 2, 5))
      fan22Owner0Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4725000000000], [375000000000]) (some (6, 0, 3))
      (some (6, 1, 3)) (.next ([4155000000000], [570000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([4500000000000], [630000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([3900000000000], [600000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([7230000000000,
      0], [1140000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([6285000000000],
      [1695000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4530000000000, 0], [1890000000000,
      9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1500000000000], [945000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([3585000000000], [2445000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([2280000000000], [1875000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([2610000000000, -9000000000000], [2520000000000, 9000000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) fan22Owner4Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5775000000000], [750000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([2520000000000], [1455000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([3225000000000], [4005000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([2520000000000], [7230000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [6525000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-750000000000], [6525000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1455000000000], [3975000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-4005000000000], [7230000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-7230000000000], [9750000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
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
  apply ExclusionHint.sound (.pair 5 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4725000000000], [375000000000]) (some (5, 0, 3))
      (some (5, 6, 3)) (.next ([4155000000000], [570000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      (.next ([4500000000000], [630000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([3900000000000], [600000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([4530000000000,
      0], [1890000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1500000000000],
      [945000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([3585000000000], [2445000000000])
      (some (5, 6, 3)) (some (5, 6, 3)) fan23Owner4Part0)))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded23_4
    · exact (hj rfl).elim
    · exact excluded23_6
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint210000220000
end ConwaySoifer.Simplified.Certificates
