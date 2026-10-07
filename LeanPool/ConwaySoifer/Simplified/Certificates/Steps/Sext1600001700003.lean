/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext160000170000
import Mathlib.Tactic.FinCases

/-!
# Sext 160000 170000 3

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
def fan24Owner4Part0 : FanWitness := (.next ([570000000000], [4680000000000]) (some (5, 1, 6)) (some
    (5, 1, 6)) (.next ([225000000000], [4425000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([75000000000], [1800000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([45000000000],
    [1650000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([75000000000], [4605000000000]) (some
    (5, 1, 6)) (some (5, 1, 6)) (.next ([0], [5175000000000]) (some (5, 1, 6)) (some (5, 1, 6))
    (.next ([-525000000000], [8775000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-600000000000], [4170000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-750000000000],
    [4350000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1125000000000], [4725000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1575000000000], [6300000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-2160000000000, 9000000000000], [6810000000000, -9000000000000]) (some
    (0, 1, 6)) (some (0, 1, 6)) (.next ([-3600000000000], [8250000000000]) (some (0, 1, 6)) (some
    (0, 1, 6)) (.next ([-3210000000000, 9000000000000], [5400000000000]) (some (0, 1, 6)) (some (0,
    1, 6)) (.next ([-3240000000000, 9000000000000], [5250000000000]) (some (0, 1, 6)) (some (0, 1,
    6)) (.next ([-2475000000000], [3525000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-5175000000000], [6615000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-150000000000], [180000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-4650000000000],
    [5400000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-4680000000000], [5250000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-4425000000000], [4650000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-1800000000000], [1875000000000]) (some (0, 1, 6)) (some (0, 2, 6))
    (.next ([-1650000000000], [1695000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-4605000000000], [4680000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.terminal (some (0, 2,
    6)) (some (0, 2, 6)) (some (0, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner0Part0 : FanWitness := (.next ([-1140000000000], [7410000000000]) (some (9, 4, 5))
    (some (9, 4, 5)) (.next ([-660000000000], [3915000000000]) (some (9, 4, 5)) (some (9, 4, 5))
    (.next ([-180000000000], [1035000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next
    ([-1335000000000], [7230000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-660000000000],
    [3255000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-796800000000, -4980000000000],
    [3653400000000, 2490000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-375000000000],
    [1515000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-2295000000000], [7005000000000])
    (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-3735000000000], [10005000000000]) (some (9, 4, 5))
    (some (9, 4, 5)) (.next ([-195000000000], [480000000000]) (some (9, 4, 5)) (some (9, 4, 5))
    (.next ([-316800000000, -4980000000000], [773400000000, 2490000000000]) (some (9, 4, 5)) (some
    (9, 4, 6)) (.next ([-180000000000], [375000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next
    ([-398400000000, -2490000000000], [796800000000, 4980000000000]) (some (9, 4, 6)) (some (9, 4,
    6)) (.next ([-261600000000, 2490000000000], [398400000000, 2490000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([-1035000000000], [1515000000000]) (some (9, 4, 6)) (some (9, 4, 7))
    (.next ([-3750000000000], [5370000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-855000000000], [1140000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-4148400000000,
    -2490000000000], [5506800000000, 4980000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-4410000000000], [5370000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-2400000000000],
    [2775000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-4546800000000, -4980000000000],
    [5108400000000, 2490000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-4410000000000],
    [4710000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-6270000000000], [6645000000000])
    (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-1253400000000, -2490000000000], [1276800000000,
    4980000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.terminal (some (9, 4, 7)) (some (9, 4, 7))
    (some (9, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner0Part1 : FanWitness := (.next ([1140000000000], [375000000000]) (some (7, 9, 4)) (some
    (9, 9, 4)) (.next ([4710000000000], [2295000000000]) (some (9, 9, 4)) (some (9, 9, 4)) (.next
    ([6270000000000], [3735000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([285000000000],
    [195000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([456600000000, -2490000000000],
    [316800000000, 4980000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([195000000000],
    [180000000000]) (some (9, 3, 4)) (some (9, 3, 4)) (.next ([398400000000, 2490000000000],
    [398400000000, 2490000000000]) (some (9, 3, 4)) (some (9, 4, 4)) (.next ([136800000000,
    4980000000000], [261600000000, -2490000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next
    ([480000000000], [1035000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next ([1620000000000],
    [3750000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next ([285000000000], [855000000000]) (some
    (9, 4, 4)) (some (9, 4, 4)) (.next ([1358400000000, 2490000000000], [4148400000000,
    2490000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next ([960000000000], [4410000000000]) (some
    (9, 4, 4)) (some (9, 4, 4)) (.next ([375000000000], [2400000000000]) (some (9, 4, 4)) (some (9,
    4, 4)) (.next ([561600000000, -2490000000000], [4546800000000, 4980000000000]) (some (9, 4, 4))
    (some (9, 4, 4)) (.next ([300000000000], [4410000000000]) (some (9, 4, 4)) (some (9, 4, 4))
    (.next ([375000000000], [6270000000000]) (some (9, 4, 4)) (some (9, 4, 4)) (.next ([23400000000,
    2490000000000], [1253400000000, 2490000000000]) (some (9, 4, 4)) (some (9, 4, 5)) (.next ([0],
    [660000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-81600000000, 2490000000000],
    [7148400000000, 2490000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-480000000000],
    [7410000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-375000000000], [4110000000000])
    (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-878400000000, -2490000000000], [7546800000000,
    4980000000000]) (some (9, 4, 5)) (some (9, 4, 5)) (.next ([-398400000000, -2490000000000],
    [2856600000000, -2490000000000]) (some (9, 4, 5)) (some (9, 4, 5))
    fan25Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner3Part0 : FanWitness := (.next ([3255000000000], [5745000000000]) (some (5, 6, 3))
    (some (5, 6, 4)) (.next ([1815000000000, -9000000000000], [5745000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([30000000000], [150000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([750000000000], [4650000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([570000000000],
    [4680000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([540000000000, 9000000000000],
    [5400000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0], [1440000000000, 9000000000000])
    (some (5, 6, 4)) (some (5, 6, 4)) (.next ([-150000000000], [3930000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-690000000000, -9000000000000], [4650000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-870000000000, -9000000000000], [4680000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-900000000000], [3960000000000, -9000000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-1245000000000], [4845000000000]) (some (0, 6, 4)) (some (1, 6, 4))
    (.next ([-1065000000000], [3750000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next
    ([-1095000000000], [3600000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4305000000000,
    9000000000000], [9000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-1440000000000,
    -9000000000000], [2880000000000, 18000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next
    ([-3210000000000, 9000000000000], [5400000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next
    ([-3240000000000, 9000000000000], [5250000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next
    ([-5745000000000], [9000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-5745000000000],
    [7560000000000, -9000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-150000000000],
    [180000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4650000000000], [5400000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4680000000000], [5250000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-5400000000000, 0], [5940000000000, 9000000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.terminal (some (1, 6, 4)) (some (1, 6, 4)) (some (1, 6,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner3Part0 : FanWitness := (.next ([3405000000000, 0], [3435000000000, -9000000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2190000000000, 9000000000000], [3210000000000,
    -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2010000000000, 9000000000000],
    [3240000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1965000000000,
    -9000000000000], [6315000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([30000000000], [150000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([750000000000],
    [4650000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([570000000000], [4680000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([540000000000, 9000000000000], [5400000000000]) (some
    (5, 1, 6)) (some (5, 1, 6)) (.next ([0], [1440000000000, 9000000000000]) (some (5, 1, 6)) (some
    (5, 1, 6)) (.next ([-150000000000], [3930000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next
    ([-690000000000, -9000000000000], [4650000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-870000000000, -9000000000000], [4680000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1995000000000], [9375000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-900000000000],
    [3960000000000, -9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1845000000000],
    [5445000000000]) (some (0, 2, 6)) (some (1, 2, 6)) (.next ([-1995000000000], [5625000000000])
    (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-3435000000000, 9000000000000], [6840000000000,
    -9000000000000]) (some (1, 2, 6)) (some (1, 6, 6)) (.next ([-3210000000000, 9000000000000],
    [5400000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-3240000000000, 9000000000000],
    [5250000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-6315000000000, -9000000000000],
    [8280000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-150000000000], [180000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4650000000000], [5400000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-4680000000000], [5250000000000]) (some (1, 6, 4)) (some (1, 6, 4))
    (.next ([-5400000000000, 0], [5940000000000, 9000000000000]) (some (1, 6, 4)) (some (1, 6, 4))
    (.terminal (some (1, 6, 4)) (some (1, 6, 4)) (some (1, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner5Part0 : FanWitness := (.next ([2310000000000], [795000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([5175000000000], [1950000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([5175000000000, 9000000000000], [2385000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1,
    2)) (.next ([3735000000000], [3825000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
    ([720000000000], [1215000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1095000000000],
    [2730000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1875000000000], [6030000000000])
    (some (4, 1, 2)) (some (4, 1, 5)) (.next ([435000000000], [1440000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([1155000000000], [4815000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([1440000000000, 9000000000000], [6465000000000, 0]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([720000000000, 9000000000000], [5250000000000, 0]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([0, 0], [1440000000000, 9000000000000]) (some (4, 1, 5)) (some (0, 1, 5)) (.next
    ([-720000000000], [5250000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-795000000000],
    [3105000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1950000000000], [7125000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2385000000000, 9000000000000], [7560000000000, 0])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3825000000000], [7560000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-1215000000000], [1935000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-2730000000000], [3825000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-6030000000000], [7905000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1440000000000],
    [1875000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4815000000000], [5970000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6465000000000, 0], [7905000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5250000000000, 0], [5970000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner0Part0 : FanWitness := (.next ([-375000000000], [1515000000000]) (some (0, 9, 5))
    (some (0, 9, 5)) (.next ([-136800000000, -4980000000000], [398400000000, 2490000000000]) (some
    (0, 9, 5)) (some (0, 9, 5)) (.next ([-316800000000, -4980000000000], [773400000000,
    2490000000000]) (some (0, 9, 5)) (some (1, 9, 6)) (.next ([-180000000000], [375000000000]) (some
    (1, 9, 6)) (some (1, 9, 6)) (.next ([-398400000000, -2490000000000], [796800000000,
    4980000000000]) (some (1, 9, 6)) (some (2, 9, 6)) (.next ([-1770000000000], [3480000000000])
    (some (2, 9, 6)) (some (2, 9, 6)) (.next ([-4560000000000], [8415000000000]) (some (2, 4, 6))
    (some (2, 4, 6)) (.next ([-5040000000000], [8700000000000]) (some (2, 4, 6)) (some (2, 4, 6))
    (.next ([-3255000000000], [5550000000000]) (some (2, 4, 6)) (some (2, 4, 6)) (.next
    ([-5438400000000, -2490000000000], [8836800000000, 4980000000000]) (some (2, 4, 6)) (some (2, 4,
    6)) (.next ([-1920000000000], [3015000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next
    ([-3735000000000], [5835000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-5700000000000],
    [8700000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-1035000000000], [1515000000000])
    (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-4133400000000, -2490000000000], [5971800000000,
    4980000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-5700000000000], [8040000000000])
    (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-5520000000000], [7665000000000]) (some (2, 4, 7))
    (some (2, 4, 7)) (.next ([-855000000000], [1140000000000]) (some (2, 4, 7)) (some (9, 4, 7))
    (.next ([-4395000000000], [5835000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-4531800000000, -4980000000000], [5573400000000, 2490000000000]) (some (9, 4, 7)) (some (9, 4,
    7)) (.next ([-4395000000000], [5175000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next
    ([-4215000000000], [4800000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-6270000000000],
    [6645000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.next ([-1253400000000, -2490000000000],
    [1276800000000, 4980000000000]) (some (9, 4, 7)) (some (9, 4, 7)) (.terminal (some (9, 4, 7))
    (some (9, 4, 7)) (some (9, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner0Part1 : FanWitness := (.next ([2295000000000], [3255000000000]) (some (8, 9, 4))
    (some (8, 9, 4)) (.next ([3398400000000, 2490000000000], [5438400000000, 2490000000000]) (some
    (8, 9, 4)) (some (8, 9, 4)) (.next ([1095000000000], [1920000000000]) (some (0, 9, 4)) (some (0,
    9, 4)) (.next ([2100000000000], [3735000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next
    ([3000000000000], [5700000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next ([480000000000],
    [1035000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next ([1838400000000, 2490000000000],
    [4133400000000, 2490000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next ([2340000000000],
    [5700000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next ([2145000000000], [5520000000000])
    (some (0, 9, 4)) (some (0, 9, 4)) (.next ([285000000000], [855000000000]) (some (0, 9, 4)) (some
    (0, 9, 4)) (.next ([1440000000000], [4395000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next
    ([1041600000000, -2490000000000], [4531800000000, 4980000000000]) (some (0, 9, 4)) (some (0, 9,
    4)) (.next ([780000000000], [4395000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next
    ([585000000000], [4215000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next ([375000000000],
    [6270000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next ([23400000000, 2490000000000],
    [1253400000000, 2490000000000]) (some (0, 9, 4)) (some (0, 9, 5)) (.next ([0], [660000000000])
    (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-81600000000, 2490000000000], [7148400000000,
    2490000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-480000000000], [7410000000000])
    (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-878400000000, -2490000000000], [7546800000000,
    4980000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-1140000000000], [7410000000000])
    (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-180000000000], [1035000000000]) (some (0, 9, 5))
    (some (0, 9, 5)) (.next ([-1335000000000], [7230000000000]) (some (0, 9, 5)) (some (0, 9, 5))
    (.next ([-261600000000, 2490000000000], [1058400000000, 2490000000000]) (some (0, 9, 5)) (some
    (0, 9, 5)) fan28Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner3Part0 : FanWitness := (.next ([3060000000000, -9000000000000], [900000000000]) (some
    (6, 1, 3)) (some (6, 1, 3)) (.next ([5250000000000], [1815000000000]) (some (6, 1, 3)) (some (6,
    1, 3)) (.next ([1440000000000, 9000000000000], [945000000000, -9000000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) (some
    (6, 1, 3)) (some (6, 1, 3)) (.next ([2190000000000, 9000000000000], [3210000000000,
    -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2115000000000], [3285000000000])
    (some (6, 1, 3)) (some (6, 1, 3)) (.next ([30000000000], [150000000000]) (some (6, 1, 3)) (some
    (6, 1, 4)) (.next ([750000000000], [4650000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([570000000000], [4680000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([540000000000,
    9000000000000], [5400000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([0], [1440000000000,
    9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-150000000000], [3930000000000])
    (some (6, 1, 4)) (some (6, 2, 4)) (.next ([-690000000000, -9000000000000], [4650000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-870000000000, -9000000000000], [4680000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-900000000000], [3960000000000, -9000000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1815000000000], [7065000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-945000000000, 9000000000000], [2385000000000]) (some (6, 2, 4)) (some
    (6, 2, 4)) (.next ([-1440000000000, -9000000000000], [2880000000000, 18000000000000]) (some (6,
    2, 4)) (some (6, 2, 4)) (.next ([-3210000000000, 9000000000000], [5400000000000]) (some (6, 2,
    4)) (some (6, 2, 4)) (.next ([-3285000000000], [5400000000000]) (some (6, 2, 4)) (some (6, 2,
    4)) (.next ([-150000000000], [180000000000]) (some (1, 2, 4)) (some (1, 2, 4)) (.next
    ([-4650000000000], [5400000000000]) (some (1, 2, 4)) (some (1, 3, 4)) (.next ([-4680000000000],
    [5250000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-5400000000000, 0], [5940000000000,
    9000000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.terminal (some (1, 3, 4)) (some (1, 3, 4))
    (some (1, 3, 4)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5160000000000], [240000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([5790000000000, 9000000000000], [3960000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4350000000000], [5400000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([1440000000000, 9000000000000], [4590000000000, 0]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([0], [4590000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([-240000000000], [5400000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([-3960000000000,
      9000000000000], [9750000000000, 0]) (some (0, 3, 2)) (some (3, 3, 2)) (.next
      ([-5400000000000], [9750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4590000000000,
      0], [6030000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8250000000000], [525000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([3570000000000], [600000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([3600000000000], [750000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([3600000000000], [1125000000000]) (some (6, 1, 2)) (some (6, 1, 6)) (.next ([4725000000000],
      [1575000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next ([4650000000000], [2160000000000,
      -9000000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next ([4650000000000], [3600000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2190000000000, 9000000000000], [3210000000000,
      -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2010000000000, 9000000000000],
      [3240000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1050000000000],
      [2475000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1440000000000, 9000000000000],
      [5175000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([30000000000], [150000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([750000000000], [4650000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) fan24Owner4Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_8 : ExcludedOn (model24.B 8 ++ [step24.q]) 9000000000000 (model24.caps 8)
    (model24.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7066800000000, 4980000000000], [81600000000,
      -2490000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6930000000000], [480000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([3735000000000], [375000000000]) (some (7, 9, 4))
      (some (7, 9, 4)) (.next ([6668400000000, 2490000000000], [878400000000, 2490000000000]) (some
      (7, 9, 4)) (some (7, 9, 4)) (.next ([2458200000000, -4980000000000], [398400000000,
      2490000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6270000000000], [1140000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([3255000000000], [660000000000]) (some (7, 9, 4))
      (some (7, 9, 4)) (.next ([855000000000], [180000000000]) (some (7, 9, 4)) (some (7, 9, 4))
      (.next ([5895000000000], [1335000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next
      ([2595000000000], [660000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([2856600000000,
      -2490000000000], [796800000000, 4980000000000]) (some (7, 9, 4)) (some (7, 9, 4))
      fan25Owner0Part1)))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3780000000000], [150000000000]) (some (4, 1, 6))
      (some (5, 1, 6)) (.next ([3960000000000, -9000000000000], [690000000000, 9000000000000]) (some
      (5, 1, 6)) (some (5, 1, 6)) (.next ([3810000000000, -9000000000000], [870000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3060000000000, -9000000000000],
      [900000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3600000000000], [1245000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2685000000000], [1065000000000]) (some (5, 1, 6))
      (some (5, 6, 6)) (.next ([2505000000000], [1095000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      (.next ([4695000000000, 9000000000000], [4305000000000, -9000000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) (.next ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) (some
      (5, 6, 3)) (some (5, 6, 3)) (.next ([2190000000000, 9000000000000], [3210000000000,
      -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2010000000000, 9000000000000],
      [3240000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      fan25Owner3Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_9 : ExcludedOn (model25.B 9 ++ [step25.q]) 9000000000000 (model25.caps 9)
    (model25.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded25_5
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7035000000000, 9000000000000], [2685000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([5595000000000], [4125000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1440000000000, 9000000000000], [1440000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1440000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2685000000000, 9000000000000],
      [9720000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4125000000000], [9720000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1440000000000, -9000000000000], [2880000000000,
      18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0)) (some (3, 1,
      3)) (some (3, 1, 3))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3780000000000], [150000000000]) (some (4, 1, 6))
      (some (5, 1, 6)) (.next ([3960000000000, -9000000000000], [690000000000, 9000000000000]) (some
      (5, 1, 6)) (some (5, 1, 6)) (.next ([3810000000000, -9000000000000], [870000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([7380000000000], [1995000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3060000000000, -9000000000000], [900000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3600000000000], [1845000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([3630000000000], [1995000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan26Owner3Part0))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4530000000000], [720000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan27Owner5Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000], [1440000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([5265000000000], [3735000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([1440000000000, 9000000000000], [7560000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 9000000000000], [3825000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1440000000000, 9000000000000]) (some (3, 0,
      2)) (some (3, 0, 2)) (.next ([-1440000000000], [5265000000000]) (some (3, 0, 2)) (some (3, 1,
      2)) (.next ([-3735000000000, 9000000000000], [9000000000000, -9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-7560000000000, 9000000000000], [9000000000000, 0]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-3825000000000, 9000000000000], [3825000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_8 : ExcludedOn (model27.B 8 ++ [step27.q]) 9000000000000 (model27.caps 8)
    (model27.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded27_1
    · exact excluded27_2
    · exact excluded27_3
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7066800000000, 4980000000000], [81600000000,
      -2490000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6930000000000], [480000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6668400000000, 2490000000000], [878400000000,
      2490000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next ([6270000000000], [1140000000000])
      (some (7, 9, 4)) (some (7, 9, 4)) (.next ([855000000000], [180000000000]) (some (7, 9, 4))
      (some (7, 9, 4)) (.next ([5895000000000], [1335000000000]) (some (7, 9, 4)) (some (7, 9, 4))
      (.next ([796800000000, 4980000000000], [261600000000, -2490000000000]) (some (7, 9, 4)) (some
      (7, 9, 4)) (.next ([1140000000000], [375000000000]) (some (7, 9, 4)) (some (7, 9, 4)) (.next
      ([261600000000, -2490000000000], [136800000000, 4980000000000]) (some (7, 9, 4)) (some (7, 9,
      4)) (.next ([456600000000, -2490000000000], [316800000000, 4980000000000]) (some (7, 9, 4))
      (some (8, 9, 4)) (.next ([195000000000], [180000000000]) (some (8, 9, 4)) (some (8, 9, 4))
      (.next ([398400000000, 2490000000000], [398400000000, 2490000000000]) (some (8, 9, 4)) (some
      (8, 9, 4)) (.next ([1710000000000], [1770000000000]) (some (8, 9, 4)) (some (8, 9, 4)) (.next
      ([3855000000000], [4560000000000]) (some (8, 9, 4)) (some (8, 9, 4)) (.next ([3660000000000],
      [5040000000000]) (some (8, 9, 4)) (some (8, 9, 4)) fan28Owner0Part1)))))))))))))))) (den :=
      9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_7 : ExcludedOn (model28.B 7 ++ [step28.q]) 9000000000000 (model28.caps 7)
    (model28.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_8 : ExcludedOn (model28.B 8 ++ [step28.q]) 9000000000000 (model28.caps 8)
    (model28.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_9 : ExcludedOn (model28.B 9 ++ [step28.q]) 9000000000000 (model28.caps 9)
    (model28.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7665000000000], [375000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([375000000000], [75000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([6000000000000, 0], [2520000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([6000000000000], [3960000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1920000000000], [1665000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1845000000000],
      [2115000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1440000000000, 9000000000000],
      [6675000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1065000000000,
      9000000000000], [6600000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0,
      0], [1440000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-375000000000],
      [8040000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-75000000000], [450000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-2520000000000, 9000000000000], [8520000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-3960000000000], [9960000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1665000000000], [3585000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-2115000000000], [3960000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-6675000000000, 9000000000000], [8115000000000, 0]) (some (0, 1, 2)) (some (0, 1, 4))
      (.next ([-6600000000000, 9000000000000], [7665000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_1 : ExcludedOn (model29.B 1 ++ [step29.q]) 9000000000000 (model29.caps 1)
    (model29.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_2 : ExcludedOn (model29.B 2 ++ [step29.q]) 9000000000000 (model29.caps 2)
    (model29.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_3 : ExcludedOn (model29.B 3 ++ [step29.q]) 9000000000000 (model29.caps 3)
    (model29.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (359) (766) (76600) (.witnessedFan (.next ([3600000000000],
      [1125000000000]) (some (5, 0, 2)) (some (5, 1, 2)) (.next ([4725000000000], [1575000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1980000000000, -9000000000000], [1440000000000,
      9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1125000000000], [1020000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3420000000000], [5745000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([2295000000000], [4725000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([1440000000000, 9000000000000], [4305000000000, -9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([1440000000000, 9000000000000], [5175000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([570000000000], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([315000000000, 9000000000000], [3285000000000, -9000000000000]) (some (5, 1, 2)) (some
      (5, 1, 2)) (.next ([0], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([-1125000000000], [4725000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([-1575000000000], [6300000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-1440000000000,
      -9000000000000], [3420000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-1020000000000],
      [2145000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-5745000000000], [9165000000000])
      (some (5, 1, 2)) (some (5, 1, 3)) (.next ([-4725000000000], [7020000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([-4305000000000, 9000000000000], [5745000000000]) (some (5, 1, 3))
      (some (5, 1, 5)) (.next ([-5175000000000], [6615000000000, 9000000000000]) (some (5, 1, 5))
      (some (5, 1, 5)) (.next ([-5175000000000], [5745000000000]) (some (5, 1, 5)) (some (5, 1, 5))
      (.next ([-3285000000000, 9000000000000], [3600000000000]) (some (5, 1, 5)) (some (5, 2, 5))
      (.terminal (some (5, 2, 5)) (some (0, 2, 5)) (some (5, 2, 5)))))))))))))))))))))))))
      (.witnessedFan (.next ([3600000000000], [1125000000000]) (some (5, 0, 2)) (some (5, 1, 2))
      (.next ([4725000000000], [1575000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([1980000000000, -9000000000000], [1440000000000, 9000000000000]) (some (5, 1, 2)) (some (5,
      1, 2)) (.next ([1125000000000], [1020000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([3420000000000], [5745000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2295000000000],
      [4725000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1440000000000, 9000000000000],
      [4305000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1440000000000,
      9000000000000], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([315000000000,
      9000000000000], [3285000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([570000000000], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([0],
      [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-1125000000000], [4725000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-1575000000000], [6300000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([-1440000000000, -9000000000000], [3420000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([-1020000000000], [2145000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([-5745000000000], [9165000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next
      ([-4725000000000], [7020000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-4305000000000,
      9000000000000], [5745000000000]) (some (5, 1, 3)) (some (5, 1, 5)) (.next ([-5175000000000],
      [6615000000000, 9000000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([-3285000000000,
      9000000000000], [3600000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([-5175000000000],
      [5745000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.terminal (some (5, 1, 5)) (some (0, 2,
      5)) (some (5, 2, 5)))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_7 : ExcludedOn (model29.B 7 ++ [step29.q]) 9000000000000 (model29.caps 7)
    (model29.ord 7) 0 1 100 := by
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
    · exact excluded29_4
    · exact excluded29_5
    · exact excluded29_6
    · exact excluded29_7
    · exact (hj rfl).elim
    · exact excluded29_9
theorem next29 : model29.insert step29 = model30 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded30_0 : ExcludedOn (model30.B 0 ++ [step30.q]) 9000000000000 (model30.caps 0)
    (model30.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_1 : ExcludedOn (model30.B 1 ++ [step30.q]) 9000000000000 (model30.caps 1)
    (model30.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_2 : ExcludedOn (model30.B 2 ++ [step30.q]) 9000000000000 (model30.caps 2)
    (model30.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_3 : ExcludedOn (model30.B 3 ++ [step30.q]) 9000000000000 (model30.caps 3)
    (model30.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3780000000000], [150000000000]) (some (4, 1, 3))
      (some (6, 1, 3)) (.next ([3960000000000, -9000000000000], [690000000000, 9000000000000]) (some
      (6, 1, 3)) (some (6, 1, 3)) (.next ([3810000000000, -9000000000000], [870000000000,
      9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) fan30Owner3Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_4 : ExcludedOn (model30.B 4 ++ [step30.q]) 9000000000000 (model30.caps 4)
    (model30.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_7 : ExcludedOn (model30.B 7 ++ [step30.q]) 9000000000000 (model30.caps 7)
    (model30.ord 7) 0 1 100 := by
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
    · exact excluded30_5
    · exact excluded30_6
    · exact excluded30_7
    · exact (hj rfl).elim
    · exact excluded30_9
theorem next30 : model30.insert step30 = model31 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded31_0 : ExcludedOn (model31.B 0 ++ [step31.q]) 9000000000000 (model31.caps 0)
    (model31.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_1 : ExcludedOn (model31.B 1 ++ [step31.q]) 9000000000000 (model31.caps 1)
    (model31.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (359) (766) (76600) (.witnessedFan (.next ([3600000000000],
      [1125000000000]) (some (5, 0, 2)) (some (5, 1, 2)) (.next ([4725000000000], [1575000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2295000000000], [1305000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([3420000000000], [2325000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([1125000000000], [1020000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([3420000000000], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1440000000000,
      9000000000000], [4305000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([1440000000000, 9000000000000], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([570000000000], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([315000000000,
      9000000000000], [3285000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([0], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-1125000000000],
      [4725000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1575000000000], [6300000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1305000000000], [3600000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-2325000000000], [5745000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-1020000000000], [2145000000000]) (some (0, 1, 2)) (some (0, 1, 5)) (.next
      ([-5175000000000], [8595000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4305000000000,
      9000000000000], [5745000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5175000000000],
      [6615000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5175000000000],
      [5745000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3285000000000, 9000000000000],
      [3600000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2,
      5)) (some (0, 2, 5))))))))))))))))))))))))) (.witnessedFan (.next ([3600000000000],
      [1125000000000]) (some (5, 0, 2)) (some (5, 1, 2)) (.next ([4725000000000], [1575000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2295000000000], [1305000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([3420000000000], [2325000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([1125000000000], [1020000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([3420000000000], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1440000000000,
      9000000000000], [4305000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([1440000000000, 9000000000000], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([315000000000, 9000000000000], [3285000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1,
      2)) (.next ([570000000000], [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([0],
      [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([-1125000000000], [4725000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1575000000000], [6300000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1305000000000], [3600000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-2325000000000], [5745000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-1020000000000], [2145000000000]) (some (0, 1, 2)) (some (0, 1, 5)) (.next
      ([-5175000000000], [8595000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4305000000000,
      9000000000000], [5745000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5175000000000],
      [6615000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3285000000000,
      9000000000000], [3600000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5175000000000],
      [5745000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1, 5)) (some (0, 2,
      5)) (some (0, 2, 5)))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_6 : ExcludedOn (model31.B 6 ++ [step31.q]) 9000000000000 (model31.caps 6)
    (model31.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_7 : ExcludedOn (model31.B 7 ++ [step31.q]) 9000000000000 (model31.caps 7)
    (model31.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_8 : ExcludedOn (model31.B 8 ++ [step31.q]) 9000000000000 (model31.caps 8)
    (model31.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5580000000000], [3420000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([3195000000000], [2385000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1035000000000], [5580000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [5580000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3420000000000], [9000000000000])
      (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-2385000000000], [5580000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-5580000000000], [6615000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.terminal (some (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_9 : ExcludedOn (model31.B 9 ++ [step31.q]) 9000000000000 (model31.caps 9)
    (model31.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded31_4
    · exact excluded31_5
    · exact excluded31_6
    · exact excluded31_7
    · exact excluded31_8
    · exact excluded31_9
theorem next31 : model31.insert step31 = model32 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext160000170000
end ConwaySoifer.Simplified.Certificates
