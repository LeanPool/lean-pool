/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext160000170000
import Mathlib.Tactic.FinCases

/-!
# Sext 160000 170000 2

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
namespace Sext160000170000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan17Owner0Part0 : FanWitness := (.next ([-1125000000000], [5205000000000]) (some (9, 4, 5))
    (some (9, 4, 5)) (.next ([-261600000000, 2490000000000], [1058400000000, 2490000000000]) (some
    (9, 4, 5)) (some (9, 4, 5)) (.next ([-375000000000], [1515000000000]) (some (9, 4, 5)) (some (9,
    4, 5)) (.next ([-1410000000000], [5010000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next
    ([-1148400000000, -2490000000000], [3951600000000, -2490000000000]) (some (9, 4, 5)) (some (9,
    4, 5)) (.next ([-1410000000000], [4350000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next
    ([-1546800000000, -4980000000000], [4748400000000, 2490000000000]) (some (9, 4, 5)) (some (9, 4,
    5)) (.next ([-136800000000, -4980000000000], [398400000000, 2490000000000]) (some (9, 4, 5))
    (some (9, 4, 5)) (.next ([-3390000000000], [7350000000000]) (some (9, 4, 5)) (some (9, 4, 6))
    (.next ([-4830000000000], [10350000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-773400000000, -2490000000000], [1651800000000, 4980000000000]) (some (9, 4, 6)) (some (9, 4,
    6)) (.next ([-1440000000000], [3000000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-398400000000, -2490000000000], [796800000000, 4980000000000]) (some (9, 4, 6)) (some (9, 4,
    6)) (.next ([-261600000000, 2490000000000], [398400000000, 2490000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-3750000000000], [5370000000000]) (some (9, 4, 6)) (some (9, 4, 7))
    (.next ([-1058400000000, -2490000000000], [1456800000000, 4980000000000]) (some (9, 4, 7)) (some
    (9, 4, 7)) (.next ([-855000000000], [1140000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-4148400000000, -2490000000000], [5506800000000, 4980000000000]) (some (9, 4, 7)) (some (9, 4,
    7)) (.next ([-4410000000000], [5370000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-4546800000000, -4980000000000], [5108400000000, 2490000000000]) (some (9, 4, 7)) (some (9, 4,
    7)) (.next ([-4410000000000], [4710000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-6270000000000], [6645000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-4148400000000,
    -2490000000000], [4311600000000, -2490000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-6750000000000], [6930000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.terminal (some (9, 4,
    7)) (some (9, 4, 7)) (some (9, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan17Owner0Part1 : FanWitness := (.next ([3960000000000], [3390000000000]) (some (9, 9, 4))
    (some (9, 9, 4)) (.next ([5520000000000], [4830000000000]) (some (9, 3, 4)) (some (9, 3, 4))
    (.next ([878400000000, 2490000000000], [773400000000, 2490000000000]) (some (9, 3, 4)) (some (9,
    3, 4)) (.next ([1560000000000], [1440000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next
    ([398400000000, 2490000000000], [398400000000, 2490000000000]) (some (9, 3, 4)) (some (9, 4, 4))
    (.next ([136800000000, 4980000000000], [261600000000, -2490000000000]) (some (9, 4, 4)) (some
    (9, 4, 4)) (.next ([1620000000000], [3750000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next
    ([398400000000, 2490000000000], [1058400000000, 2490000000000]) (some (9, 4, 4)) (some (9, 4,
    4)) (.next ([285000000000], [855000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next
    ([1358400000000, 2490000000000], [4148400000000, 2490000000000]) (some (9, 4, 4)) (some (9, 4,
    4)) (.next ([960000000000], [4410000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next
    ([561600000000, -2490000000000], [4546800000000, 4980000000000]) (some (9, 4, 4)) (some (9, 4,
    4)) (.next ([300000000000], [4410000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next
    ([375000000000], [6270000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next ([163200000000,
    -4980000000000], [4148400000000, 2490000000000]) (some (9, 4, 4)) (some (9, 4, 5)) (.next
    ([180000000000], [6750000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([0], [660000000000])
    (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-81600000000, 2490000000000], [7148400000000,
    2490000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-480000000000], [7410000000000])
    (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-351600000000, 2490000000000], [3553200000000,
    -4980000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-878400000000, -2490000000000],
    [7546800000000, 4980000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-1140000000000],
    [7410000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-1276800000000, -4980000000000],
    [7148400000000, 2490000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-750000000000],
    [3690000000000]) (some (9, 4, 5)) (some (9, 4, 5)) fan17Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan17Owner3Part0 : FanWitness := (.next ([4320000000000], [930000000000]) (some (4, 5, 2)) (some
    (4, 5, 2)) (.next ([3810000000000, -9000000000000], [870000000000, 9000000000000]) (some (4, 5,
    2)) (some (4, 5, 2)) (.next ([2880000000000, -9000000000000], [930000000000]) (some (4, 5, 2))
    (some (4, 5, 2)) (.next ([5790000000000, 9000000000000], [3960000000000, -9000000000000]) (some
    (4, 5, 2)) (some (4, 5, 2)) (.next ([1440000000000, 9000000000000], [1440000000000,
    9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([4350000000000], [5400000000000])
    (some (4, 5, 2)) (some (4, 5, 2)) (.next ([2010000000000, 9000000000000], [3240000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([2910000000000, -9000000000000],
    [5400000000000]) (some (4, 5, 2)) (some (4, 5, 3)) (.next ([570000000000], [4680000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([510000000000, 9000000000000], [5250000000000]) (some
    (4, 5, 3)) (some (4, 5, 3)) (.next ([30000000000], [4470000000000]) (some (4, 5, 3)) (some (4,
    5, 3)) (.next ([0], [1440000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([-720000000000], [4500000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-930000000000],
    [5250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-870000000000, -9000000000000],
    [4680000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-930000000000], [3810000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3960000000000, 9000000000000],
    [9750000000000]) (some (0, 5, 3)) (some (1, 5, 3)) (.next ([-1440000000000, -9000000000000],
    [2880000000000, 18000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-5400000000000],
    [9750000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-3240000000000, 9000000000000],
    [5250000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-5400000000000], [8310000000000,
    -9000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-4680000000000], [5250000000000])
    (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-5250000000000, 0], [5760000000000, 9000000000000])
    (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-4470000000000], [4500000000000]) (some (1, 5, 3))
    (some (1, 5, 3)) (.terminal (some (1, 5, 3)) (some (5, 5, 3)) (some (5, 5,
    3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part0 : FanWitness := (.next ([-375000000000], [1515000000000]) (some (9, 4, 5))
    (some (9, 4, 5)) (.next ([-2415000000000], [7605000000000]) (some (9, 4, 5)) (some (9, 4, 5))
    (.next ([-136800000000, -4980000000000], [398400000000, 2490000000000]) (some (9, 4, 5)) (some
    (9, 4, 5)) (.next ([-773400000000, -2490000000000], [1651800000000, 4980000000000]) (some (9, 4,
    5)) (some (9, 4, 6)) (.next ([-1440000000000], [3000000000000]) (some (9, 4, 6)) (some (9, 4,
    6)) (.next ([-398400000000, -2490000000000], [796800000000, 4980000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-261600000000, 2490000000000], [398400000000, 2490000000000]) (some
    (9, 4, 6)) (some (9, 4, 6)) (.next ([-3750000000000], [5370000000000]) (some (9, 4, 6)) (some
    (9, 4, 7)) (.next ([-1058400000000, -2490000000000], [1456800000000, 4980000000000]) (some (9,
    4, 7)) (some (9, 4, 7)) (.next ([-855000000000], [1140000000000]) (some (9, 4, 7)) (some (9, 4,
    7)) (.next ([-4148400000000, -2490000000000], [5506800000000, 4980000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) (.next ([-7500000000000], [9420000000000]) (some (9, 4, 7)) (some (9, 4, 7))
    (.next ([-4410000000000], [5370000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-7785000000000], [9225000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-6726600000000,
    2490000000000], [7768200000000, -4980000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-7921800000000, -4980000000000], [8963400000000, 2490000000000]) (some (9, 4, 7)) (some (9, 4,
    7)) (.next ([-4546800000000, -4980000000000], [5108400000000, 2490000000000]) (some (9, 4, 7))
    (some (9, 4, 7)) (.next ([-7125000000000], [7905000000000]) (some (9, 4, 7)) (some (9, 4, 7))
    (.next ([-7785000000000], [8565000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-7523400000000, -2490000000000], [8166600000000, -2490000000000]) (some (9, 4, 7)) (some (9,
    4, 7)) (.next ([-4410000000000], [4710000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-6270000000000], [6645000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-4148400000000,
    -2490000000000], [4311600000000, -2490000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-6750000000000], [6930000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.terminal (some (9, 4,
    7)) (some (9, 4, 7)) (some (9, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part1 : FanWitness := (.next ([398400000000, 2490000000000], [1058400000000,
    2490000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next ([285000000000], [855000000000]) (some
    (0, 9, 4)) (some (0, 9, 4)) (.next ([1358400000000, 2490000000000], [4148400000000,
    2490000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next ([1920000000000], [7500000000000])
    (some (0, 9, 4)) (some (0, 9, 4)) (.next ([960000000000], [4410000000000]) (some (0, 9, 4))
    (some (0, 9, 4)) (.next ([1440000000000], [7785000000000]) (some (0, 9, 4)) (some (0, 9, 4))
    (.next ([1041600000000, -2490000000000], [6726600000000, -2490000000000]) (some (0, 9, 4)) (some
    (0, 9, 4)) (.next ([1041600000000, -2490000000000], [7921800000000, 4980000000000]) (some (0, 9,
    4)) (some (0, 9, 4)) (.next ([561600000000, -2490000000000], [4546800000000, 4980000000000])
    (some (0, 9, 4)) (some (0, 9, 4)) (.next ([780000000000], [7125000000000]) (some (0, 9, 4))
    (some (0, 9, 4)) (.next ([780000000000], [7785000000000]) (some (0, 9, 4)) (some (0, 9, 4))
    (.next ([643200000000, -4980000000000], [7523400000000, 2490000000000]) (some (0, 9, 4)) (some
    (0, 9, 4)) (.next ([300000000000], [4410000000000]) (some (0, 9, 4)) (some (9, 9, 4)) (.next
    ([375000000000], [6270000000000]) (some (9, 9, 4)) (some (9, 9, 4)) (.next ([163200000000,
    -4980000000000], [4148400000000, 2490000000000]) (some (9, 9, 4)) (some (9, 9, 5)) (.next
    ([180000000000], [6750000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next ([0], [660000000000])
    (some (9, 9, 5)) (some (9, 9, 5)) (.next ([-81600000000, 2490000000000], [7148400000000,
    2490000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next ([-480000000000], [7410000000000])
    (some (9, 9, 5)) (some (9, 9, 5)) (.next ([-855000000000], [9045000000000]) (some (9, 9, 5))
    (some (9, 9, 5)) (.next ([-878400000000, -2490000000000], [7546800000000, 4980000000000]) (some
    (9, 4, 5)) (some (9, 4, 5)) (.next ([-1140000000000], [7410000000000]) (some (9, 4, 5)) (some
    (9, 4, 5)) (.next ([-1276800000000, -4980000000000], [7148400000000, 2490000000000]) (some (9,
    4, 5)) (some (9, 4, 5)) (.next ([-261600000000, 2490000000000], [1058400000000, 2490000000000])
    (some (9, 4, 5)) (some (9, 4, 5)) fan18Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner4Part0 : FanWitness := (.next ([4245000000000], [2310000000000]) (some (4, 5, 2))
    (some (4, 5, 2)) (.next ([2190000000000, 9000000000000], [3210000000000, -9000000000000]) (some
    (4, 5, 2)) (some (4, 5, 2)) (.next ([2010000000000, 9000000000000], [3240000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1440000000000, 9000000000000],
    [5175000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([30000000000], [150000000000]) (some
    (4, 5, 2)) (some (4, 5, 2)) (.next ([750000000000], [4650000000000]) (some (4, 5, 2)) (some (4,
    5, 3)) (.next ([1005000000000, 9000000000000], [7560000000000]) (some (4, 5, 3)) (some (4, 5,
    3)) (.next ([570000000000], [4680000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([225000000000], [4425000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([75000000000],
    [4605000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [5175000000000]) (some (4, 5,
    3)) (some (4, 5, 3)) (.next ([-435000000000], [7560000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-435000000000], [2385000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2160000000000], [6375000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2310000000000],
    [6555000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3210000000000, 9000000000000],
    [5400000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3240000000000, 9000000000000],
    [5250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5175000000000], [6615000000000,
    9000000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-150000000000], [180000000000]) (some
    (0, 5, 4)) (some (0, 5, 4)) (.next ([-4650000000000], [5400000000000]) (some (0, 5, 4)) (some
    (0, 5, 4)) (.next ([-7560000000000], [8565000000000, 9000000000000]) (some (0, 5, 4)) (some (0,
    5, 4)) (.next ([-4680000000000], [5250000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-4425000000000], [4650000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4605000000000],
    [4680000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5, 4)) (some (0, 5, 4))
    (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner4Part0 : FanWitness := (.next ([3120000000000], [375000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([2190000000000, 9000000000000], [3210000000000, -9000000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([2010000000000, 9000000000000], [3240000000000, -9000000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1440000000000, 9000000000000], [5175000000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([1815000000000, 9000000000000], [6705000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([30000000000], [150000000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([750000000000], [4650000000000]) (some (4, 1, 5)) (some (4,
    1, 5)) (.next ([570000000000], [4680000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([225000000000], [4425000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([375000000000],
    [8145000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([75000000000], [4605000000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [5175000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([-195000000000], [3465000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-375000000000], [3495000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3210000000000,
    9000000000000], [5400000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3240000000000,
    9000000000000], [5250000000000]) (some (0, 1, 5)) (some (0, 5, 5)) (.next ([-5175000000000],
    [6615000000000, 9000000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-6705000000000,
    9000000000000], [8520000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-150000000000],
    [180000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4650000000000], [5400000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4680000000000], [5250000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-4425000000000], [4650000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-8145000000000], [8520000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-4605000000000], [4680000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
    4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner4Part0 : FanWitness := (.next ([2190000000000, 9000000000000], [3210000000000,
    -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2010000000000, 9000000000000],
    [3240000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([900000000000],
    [2160000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1440000000000,
    9000000000000], [5175000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([900000000000],
    [3600000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([30000000000], [150000000000]) (some
    (4, 1, 2)) (some (4, 1, 2)) (.next ([750000000000], [4650000000000]) (some (4, 1, 2)) (some (4,
    1, 3)) (.next ([570000000000], [4680000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([225000000000], [4425000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([75000000000],
    [4605000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0], [5175000000000]) (some (4, 1,
    3)) (some (4, 1, 3)) (.next ([-150000000000], [4500000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-180000000000], [4350000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-4275000000000], [8775000000000]) (some (0, 1, 3)) (some (0, 1, 5)) (.next ([-3210000000000,
    9000000000000], [5400000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3240000000000,
    9000000000000], [5250000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2160000000000,
    9000000000000], [3060000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-5175000000000], [6615000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-3600000000000], [4500000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-150000000000],
    [180000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4650000000000], [5400000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4680000000000], [5250000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-4425000000000], [4650000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-4605000000000], [4680000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.terminal (some
    (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner3Part0 : FanWitness := (.next ([3810000000000, -9000000000000], [870000000000,
    9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([3060000000000, -9000000000000],
    [900000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([5715000000000, 9000000000000],
    [2160000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([4275000000000],
    [3600000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1440000000000, 9000000000000],
    [1440000000000, 9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([2835000000000,
    -9000000000000], [3600000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([2010000000000,
    9000000000000], [3240000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([1080000000000], [2625000000000]) (some (4, 5, 2)) (some (4, 5, 3)) (.next ([570000000000],
    [4680000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([540000000000, 9000000000000],
    [5400000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [1440000000000, 9000000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-150000000000], [3930000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-225000000000], [2700000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-900000000000], [5400000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-870000000000, -9000000000000], [4680000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-900000000000], [3960000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2160000000000, 9000000000000], [7875000000000]) (some (0, 5, 3)) (some (1, 5, 3)) (.next
    ([-3600000000000], [7875000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-1440000000000,
    -9000000000000], [2880000000000, 18000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next
    ([-3600000000000], [6435000000000, -9000000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next
    ([-3240000000000, 9000000000000], [5250000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next
    ([-2625000000000], [3705000000000]) (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-4680000000000],
    [5250000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-5400000000000, 0], [5940000000000,
    9000000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.terminal (some (1, 2, 3)) (some (1, 2, 3))
    (some (1, 2, 3)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5760000000000, 9000000000000], [3810000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1440000000000, 9000000000000],
      [1440000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4320000000000],
      [5250000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2880000000000, -9000000000000],
      [5250000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0], [1440000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([-3810000000000, 9000000000000],
      [9570000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-1440000000000,
      -9000000000000], [2880000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-5250000000000], [9570000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-5250000000000,
      0], [8130000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8430000000000], [495000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([3750000000000], [570000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4680000000000], [2310000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 4))
      (.next ([4680000000000], [3750000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([2010000000000, 9000000000000], [3240000000000, -9000000000000]) (some (3, 1, 4)) (some (3,
      1, 4)) (.next ([1440000000000, 9000000000000], [5175000000000]) (some (3, 1, 4)) (some (3, 1,
      4)) (.next ([570000000000], [4680000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([75000000000], [4605000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [5175000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-495000000000], [8925000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-570000000000], [4320000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-2310000000000, 9000000000000], [6990000000000, -9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3750000000000], [8430000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-3240000000000, 9000000000000], [5250000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5175000000000], [6615000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-4680000000000], [5250000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-4605000000000], [4680000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some
      (0, 1, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded16_4
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7066800000000, 4980000000000], [81600000000,
      -2490000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6930000000000], [480000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([3201600000000, -2490000000000], [351600000000,
      -2490000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6668400000000, 2490000000000],
      [878400000000, 2490000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6270000000000],
      [1140000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([5871600000000, -2490000000000],
      [1276800000000, 4980000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([2940000000000],
      [750000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([4080000000000], [1125000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([796800000000, 4980000000000], [261600000000,
      -2490000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([1140000000000], [375000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([3600000000000], [1410000000000]) (some (7, 9, 4))
      (some (7, 9, 4)) (.next ([2803200000000, -4980000000000], [1148400000000, 2490000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([2940000000000], [1410000000000]) (some (7, 9, 4))
      (some (7, 9, 4)) (.next ([3201600000000, -2490000000000], [1546800000000, 4980000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([261600000000, -2490000000000], [136800000000,
      4980000000000]) (some (7, 9, 4)) (some (9, 9, 4)) fan17Owner0Part1)))))))))))))))) (den :=
      9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3780000000000], [720000000000]) (some (3, 5, 5))
      (some (4, 5, 5)) fan17Owner3Part0)) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100
      (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7066800000000, 4980000000000], [81600000000,
      -2490000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6930000000000], [480000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([8190000000000], [855000000000]) (some (7, 9, 4))
      (some (7, 9, 4)) (.next ([6668400000000, 2490000000000], [878400000000, 2490000000000]) (some
      (7, 9, 4)) (some (7, 9, 4)) (.next ([6270000000000], [1140000000000]) (some (7, 9, 4)) (some
      (7, 9, 4)) (.next ([5871600000000, -2490000000000], [1276800000000, 4980000000000]) (some (7,
      9, 4)) (some (7, 9, 4)) (.next ([796800000000, 4980000000000], [261600000000, -2490000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([1140000000000], [375000000000]) (some (7, 9, 4))
      (some (7, 9, 4)) (.next ([5190000000000], [2415000000000]) (some (7, 9, 4)) (some (7, 9, 4))
      (.next ([261600000000, -2490000000000], [136800000000, 4980000000000]) (some (7, 9, 4)) (some
      (7, 9, 4)) (.next ([878400000000, 2490000000000], [773400000000, 2490000000000]) (some (7, 9,
      4)) (some (8, 9, 4)) (.next ([1560000000000], [1440000000000]) (some (8, 9, 4)) (some (8, 9,
      4)) (.next ([398400000000, 2490000000000], [398400000000, 2490000000000]) (some (8, 9, 4))
      (some (8, 9, 4)) (.next ([136800000000, 4980000000000], [261600000000, -2490000000000]) (some
      (8, 9, 4)) (some (8, 9, 4)) (.next ([1620000000000], [3750000000000]) (some (0, 9, 4)) (some
      (0, 9, 4)) fan18Owner0Part1)))))))))))))))) (den := 9000000000000)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7125000000000], [435000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([1950000000000], [435000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([4215000000000], [2160000000000]) (some (4, 1, 5)) (some (4, 5, 5))
      fan18Owner4Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded18_4
    · exact (hj rfl).elim
    · exact excluded18_6
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7935000000000, -9000000000000], [585000000000,
      9000000000000]) (some (3, 1, 5)) (some (4, 1, 5)) (.next ([4320000000000], [930000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([3810000000000, -9000000000000], [870000000000,
      9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2880000000000, -9000000000000],
      [930000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4125000000000], [3465000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1440000000000, 9000000000000], [1440000000000,
      9000000000000]) (some (4, 1, 5)) (some (4, 5, 5)) (.next ([2010000000000, 9000000000000],
      [3240000000000, -9000000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([2295000000000,
      9000000000000], [7080000000000, -9000000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next
      ([570000000000], [4680000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([510000000000,
      9000000000000], [5250000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([285000000000],
      [3840000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [1440000000000,
      9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-585000000000, -9000000000000],
      [8520000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-930000000000], [5250000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-870000000000, -9000000000000], [4680000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-930000000000], [3810000000000, -9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3465000000000], [7590000000000]) (some (0, 5, 3))
      (some (1, 5, 3)) (.next ([-1440000000000, -9000000000000], [2880000000000, 18000000000000])
      (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-3240000000000, 9000000000000], [5250000000000])
      (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-7080000000000, 9000000000000], [9375000000000])
      (some (1, 5, 3)) (some (1, 5, 3)) (.next ([-4680000000000], [5250000000000]) (some (1, 5, 3))
      (some (1, 5, 3)) (.next ([-5250000000000, 0], [5760000000000, 9000000000000]) (some (1, 5, 3))
      (some (1, 5, 3)) (.next ([-3840000000000], [4125000000000]) (some (1, 5, 3)) (some (1, 5, 3))
      (.terminal (some (1, 5, 3)) (some (1, 5, 3)) (some (1, 5, 3))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3270000000000], [195000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan19Owner4Part0)) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8145000000000], [480000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([4530000000000], [720000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([720000000000], [1215000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([2895000000000], [5010000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1875000000000],
      [6030000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([435000000000], [1440000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1680000000000], [6945000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([1155000000000], [4815000000000]) (some (5, 1, 2)) (some (5, 1, 5))
      (.next ([1440000000000, 9000000000000], [6465000000000, 0]) (some (5, 1, 5)) (some (5, 1, 5))
      (.next ([720000000000, 9000000000000], [5250000000000, 0]) (some (5, 1, 5)) (some (5, 1, 5))
      (.next ([960000000000, 9000000000000], [7185000000000, -9000000000000]) (some (5, 1, 5)) (some
      (5, 1, 5)) (.next ([0, 0], [1440000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([-480000000000], [8625000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
      ([-720000000000], [5250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1215000000000],
      [1935000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5010000000000], [7905000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6030000000000], [7905000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-1440000000000], [1875000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-6945000000000], [8625000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-4815000000000], [5970000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6465000000000,
      0], [7905000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5250000000000,
      0], [5970000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-7185000000000,
      9000000000000], [8145000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded19_1
    · exact excluded19_2
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
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4320000000000], [930000000000]) (some (3, 1, 2))
      (some (5, 1, 2)) (.next ([3810000000000, -9000000000000], [870000000000, 9000000000000]) (some
      (5, 1, 2)) (some (5, 1, 2)) (.next ([2880000000000, -9000000000000], [930000000000]) (some (5,
      1, 2)) (some (5, 1, 2)) (.next ([5250000000000], [2070000000000]) (some (5, 1, 2)) (some (5,
      1, 2)) (.next ([1440000000000, 9000000000000], [1200000000000, -9000000000000]) (some (5, 1,
      2)) (some (5, 1, 2)) (.next ([1440000000000, 9000000000000], [1440000000000, 9000000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2010000000000, 9000000000000], [3240000000000,
      -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1680000000000], [3570000000000])
      (some (5, 1, 2)) (some (5, 1, 3)) (.next ([570000000000], [4680000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([510000000000, 9000000000000], [5250000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([0], [1440000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([-930000000000], [5250000000000]) (some (5, 1, 3)) (some (5, 2, 3)) (.next
      ([-870000000000, -9000000000000], [4680000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-930000000000], [3810000000000, -9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-2070000000000], [7320000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1200000000000,
      9000000000000], [2640000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1440000000000,
      -9000000000000], [2880000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-3240000000000, 9000000000000], [5250000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-3570000000000], [5250000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-4680000000000], [5250000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-5250000000000,
      0], [5760000000000, 9000000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.terminal (some (1, 2,
      3)) (some (1, 2, 3)) (some (1, 2, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
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
    · exact excluded20_2
    · exact excluded20_3
    · exact excluded20_4
    · exact excluded20_5
    · exact excluded20_6
    · exact excluded20_7
    · exact (hj rfl).elim
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4350000000000], [150000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([4170000000000], [180000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([4500000000000], [4275000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      fan21Owner4Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5175000000000], [225000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([165000000000], [60000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([5400000000000], [4500000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1860000000000], [3540000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1125000000000],
      [5235000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([960000000000], [5175000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([225000000000], [4275000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([165000000000], [4500000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([0], [5235000000000]) (some (0, 1, 3)) (some (0, 4, 3)) (.next ([-225000000000],
      [5400000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-60000000000], [225000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-4500000000000], [9900000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-3540000000000], [5400000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-5235000000000], [6360000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-5175000000000], [6135000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-4275000000000], [4500000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-4500000000000], [4665000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded21_4
    · exact excluded21_5
    · exact excluded21_6
    · exact excluded21_7
    · exact excluded21_8
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3780000000000], [150000000000]) (some (3, 1, 2))
      (some (4, 1, 2)) (.next ([2475000000000], [225000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4500000000000], [900000000000]) (some (4, 1, 2)) (some (4, 5, 2))
      fan22Owner3Part0))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3780000000000], [150000000000]) (some (3, 1, 2))
      (some (4, 1, 2)) (.next ([4980000000000], [270000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4500000000000], [900000000000]) (some (4, 1, 2)) (some (4, 1, 5)) (.next
      ([3810000000000, -9000000000000], [870000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([3060000000000, -9000000000000], [900000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([4410000000000], [1440000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) (some (4, 1, 5)) (some
      (4, 1, 5)) (.next ([3510000000000], [5400000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([570000000000], [4680000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([540000000000,
      9000000000000], [5400000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0],
      [1440000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-150000000000],
      [3930000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-270000000000], [5250000000000])
      (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-900000000000], [5400000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-870000000000, -9000000000000], [4680000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-900000000000], [3960000000000, -9000000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-1440000000000, -9000000000000], [5850000000000, 9000000000000])
      (some (0, 2, 5)) (some (1, 2, 5)) (.next ([-1440000000000, -9000000000000], [2880000000000,
      18000000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-5400000000000], [8910000000000])
      (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-4680000000000], [5250000000000]) (some (1, 2, 5))
      (some (1, 2, 5)) (.next ([-5400000000000, 0], [5940000000000, 9000000000000]) (some (1, 2, 5))
      (some (1, 2, 5)) (.terminal (some (1, 2, 5)) (some (1, 2, 3)) (some (1, 2,
      5))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded23_3
    · exact excluded23_4
    · exact excluded23_5
    · exact excluded23_6
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext160000170000
end ConwaySoifer.Simplified.Certificates
