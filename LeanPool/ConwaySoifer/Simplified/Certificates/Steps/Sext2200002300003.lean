/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext220000230000
import Mathlib.Tactic.FinCases

/-!
# Sext 220000 230000 3

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
namespace Sext220000230000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner3Part0 : FanWitness := (.next ([4500000000000], [4470000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([1980000000000, 9000000000000], [1980000000000, 9000000000000]) (some
    (6, 1, 4)) (some (6, 1, 4)) (.next ([1980000000000, 9000000000000], [2940000000000,
    -9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([1230000000000, 9000000000000],
    [4950000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([660000000000], [4215000000000])
    (some (6, 1, 4)) (some (6, 1, 4)) (.next ([450000000000], [4050000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([0], [1980000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([-75000000000], [3540000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([-450000000000], [3750000000000]) (some (6, 1, 4)) (some (6, 2, 4)) (.next ([-720000000000],
    [5670000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-750000000000], [4950000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-750000000000], [2970000000000, -9000000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1320000000000, -9000000000000], [4215000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1530000000000, -9000000000000], [4050000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-165000000000], [375000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-2235000000000, 9000000000000], [4875000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-2070000000000, 9000000000000], [4500000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-4260000000000], [9135000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-4470000000000], [8970000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-1980000000000, -9000000000000], [3960000000000, 18000000000000]) (some (6, 2, 4)) (some (6,
    2, 4)) (.next ([-2940000000000, 9000000000000], [4920000000000]) (some (6, 2, 4)) (some (6, 2,
    4)) (.next ([-4950000000000, 0], [6180000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2,
    4)) (.next ([-4215000000000], [4875000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-4050000000000], [4500000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.terminal (some (6, 2,
    4)) (some (6, 2, 4)) (some (6, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner0Part0 : FanWitness := (.next ([-4785000000000], [10335000000000]) (some (13, 5, 7))
    (some (13, 5, 7)) (.next ([-996000000000], [2115000000000]) (some (13, 5, 7)) (some (13, 5, 7))
    (.next ([-1048200000000, -2310000000000], [2096400000000, 4620000000000]) (some (13, 5, 7))
    (some (13, 5, 7)) (.next ([-420000000000], [834000000000]) (some (13, 5, 7)) (some (13, 5, 7))
    (.next ([-571800000000, 2310000000000], [1048200000000, 2310000000000]) (some (13, 5, 7)) (some
    (13, 5, 8)) (.next ([-571800000000, 2310000000000], [967200000000, 2310000000000]) (some (13, 5,
    8)) (some (13, 5, 8)) (.next ([-60000000000], [90000000000]) (some (13, 5, 8)) (some (13, 5, 8))
    (.next ([-120000000000], [165000000000]) (some (13, 5, 8)) (some (13, 5, 8)) (.next
    ([-201000000000], [246000000000]) (some (13, 5, 8)) (some (13, 5, 9)) (.next ([-1410000000000],
    [1695000000000]) (some (13, 5, 9)) (some (13, 5, 9)) (.next ([-3108600000000, 4620000000000],
    [3541800000000, -2310000000000]) (some (13, 5, 9)) (some (13, 5, 9)) (.next ([-5490000000000],
    [6195000000000]) (some (13, 5, 9)) (some (13, 5, 9)) (.next ([-5571000000000], [6276000000000])
    (some (13, 5, 9)) (some (13, 5, 9)) (.next ([-3090000000000], [3390000000000]) (some (13, 5, 9))
    (some (13, 5, 9)) (.next ([-1455000000000], [1575000000000]) (some (13, 5, 9)) (some (13, 5, 9))
    (.next ([-5745000000000], [6165000000000]) (some (13, 5, 9)) (some (13, 5, 9)) (.next
    ([-5826000000000], [6246000000000]) (some (13, 5, 9)) (some (13, 5, 9)) (.next
    ([-6315000000000], [6660000000000]) (some (13, 5, 9)) (some (13, 5, 9)) (.next
    ([-6405000000000], [6690000000000]) (some (13, 5, 9)) (some (13, 5, 9)) (.next
    ([-6480000000000], [6705000000000]) (some (13, 5, 9)) (some (13, 5, 9)) (.next
    ([-1455000000000], [1494000000000]) (some (13, 5, 9)) (some (13, 5, 9)) (.next
    ([-6570000000000], [6735000000000]) (some (13, 5, 9)) (some (13, 5, 9)) (.next
    ([-6561000000000], [6705000000000]) (some (13, 5, 9)) (some (13, 5, 9)) (.next
    ([-6651000000000], [6735000000000]) (some (13, 5, 9)) (some (13, 5, 9)) (.terminal (some (13, 5,
    9)) (some (13, 5, 9)) (some (13, 5, 9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner0Part1 : FanWitness := (.next ([-915000000000], [7110000000000]) (some (13, 5, 7))
    (some (13, 5, 7)) (.next ([-936000000000], [7020000000000]) (some (13, 5, 7)) (some (13, 5, 7))
    (.next ([-696000000000], [5205000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next
    ([-996000000000], [7110000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next ([-1035000000000],
    [7320000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next ([-534000000000], [3504000000000])
    (some (13, 5, 7)) (some (13, 5, 7)) (.next ([-1200000000000], [7365000000000]) (some (13, 5, 7))
    (some (13, 5, 7)) (.next ([-615000000000], [3585000000000]) (some (13, 5, 7)) (some (13, 5, 7))
    (.next ([-1281000000000], [7365000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next
    ([-735000000000], [3750000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next ([-1350000000000],
    [6600000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next ([-1331400000000, -4620000000000],
    [6448200000000, 2310000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next ([-1391400000000,
    -4620000000000], [6538200000000, 2310000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next
    ([-1110000000000], [4785000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next
    ([-1695000000000], [6945000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next
    ([-1155000000000], [4665000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next
    ([-1155000000000], [4584000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next ([-375000000000],
    [1035000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next ([-495000000000], [1200000000000])
    (some (13, 5, 7)) (some (13, 5, 7)) (.next ([-915000000000], [2115000000000]) (some (13, 5, 7))
    (some (13, 5, 7)) (.next ([-4440000000000], [9990000000000]) (some (13, 5, 7)) (some (13, 5, 7))
    (.next ([-4500000000000], [10080000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next
    ([-576000000000], [1281000000000]) (some (13, 5, 7)) (some (13, 5, 7)) (.next ([-420000000000],
    [915000000000]) (some (13, 5, 7)) (some (13, 5, 7)) fan25Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner0Part2 : FanWitness := (.next ([705000000000], [5571000000000]) (some (13, 4, 5))
    (some (13, 4, 5)) (.next ([300000000000], [3090000000000]) (some (13, 4, 5)) (some (13, 4, 5))
    (.next ([120000000000], [1455000000000]) (some (13, 4, 5)) (some (13, 4, 5)) (.next
    ([420000000000], [5745000000000]) (some (13, 4, 5)) (some (13, 4, 5)) (.next ([420000000000],
    [5826000000000]) (some (13, 4, 5)) (some (13, 4, 6)) (.next ([345000000000], [6315000000000])
    (some (13, 4, 6)) (some (13, 4, 6)) (.next ([285000000000], [6405000000000]) (some (13, 4, 6))
    (some (13, 4, 6)) (.next ([225000000000], [6480000000000]) (some (13, 4, 6)) (some (13, 4, 6))
    (.next ([39000000000], [1455000000000]) (some (13, 4, 6)) (some (13, 4, 6)) (.next
    ([165000000000], [6570000000000]) (some (13, 4, 6)) (some (13, 4, 6)) (.next ([144000000000],
    [6561000000000]) (some (13, 4, 6)) (some (13, 4, 6)) (.next ([84000000000], [6651000000000])
    (some (13, 4, 6)) (some (13, 4, 6)) (.next ([0], [81000000000]) (some (13, 4, 6)) (some (13, 4,
    6)) (.next ([-31800000000, 2310000000000], [1588200000000, 2310000000000]) (some (13, 4, 6))
    (some (13, 4, 7)) (.next ([-201000000000], [6906000000000]) (some (13, 4, 7)) (some (13, 4, 7))
    (.next ([-81000000000], [1701000000000]) (some (13, 4, 7)) (some (13, 4, 7)) (.next
    ([-81000000000], [1620000000000]) (some (13, 4, 7)) (some (13, 4, 7)) (.next ([-112800000000,
    2310000000000], [1588200000000, 2310000000000]) (some (13, 4, 7)) (some (13, 4, 7)) (.next
    ([-162000000000], [1701000000000]) (some (13, 4, 7)) (some (13, 4, 7)) (.next ([-690000000000],
    [6975000000000]) (some (13, 4, 7)) (some (13, 4, 7)) (.next ([-30000000000], [285000000000])
    (some (13, 4, 7)) (some (13, 4, 7)) (.next ([-750000000000], [7065000000000]) (some (13, 4, 7))
    (some (13, 5, 7)) (.next ([-615000000000], [5205000000000]) (some (13, 5, 7)) (some (13, 5, 7))
    (.next ([-855000000000], [7020000000000]) (some (13, 5, 7)) (some (13, 5, 7))
    fan25Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner0Part3 : FanWitness := (.next ([5146800000000, -2310000000000], [1391400000000,
    4620000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next ([3675000000000], [1110000000000])
    (some (10, 13, 5)) (some (10, 13, 5)) (.next ([5250000000000], [1695000000000]) (some (10, 13,
    5)) (some (10, 13, 5)) (.next ([3510000000000], [1155000000000]) (some (10, 13, 5)) (some (10,
    13, 5)) (.next ([3429000000000], [1155000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next
    ([660000000000], [375000000000]) (some (10, 13, 5)) (some (13, 13, 5)) (.next ([705000000000],
    [495000000000]) (some (13, 13, 5)) (some (13, 13, 5)) (.next ([1200000000000], [915000000000])
    (some (13, 13, 5)) (some (13, 13, 5)) (.next ([5550000000000], [4440000000000]) (some (13, 13,
    5)) (some (13, 13, 5)) (.next ([5580000000000], [4500000000000]) (some (13, 3, 5)) (some (13, 3,
    5)) (.next ([705000000000], [576000000000]) (some (13, 3, 5)) (some (13, 3, 5)) (.next
    ([495000000000], [420000000000]) (some (13, 3, 5)) (some (13, 3, 5)) (.next ([5550000000000],
    [4785000000000]) (some (13, 3, 5)) (some (13, 3, 5)) (.next ([1119000000000], [996000000000])
    (some (13, 3, 5)) (some (13, 3, 5)) (.next ([1048200000000, 2310000000000], [1048200000000,
    2310000000000]) (some (13, 3, 5)) (some (13, 3, 5)) (.next ([414000000000], [420000000000])
    (some (13, 3, 5)) (some (13, 3, 5)) (.next ([476400000000, 4620000000000], [571800000000,
    -2310000000000]) (some (13, 3, 5)) (some (13, 3, 5)) (.next ([395400000000, 4620000000000],
    [571800000000, -2310000000000]) (some (13, 3, 5)) (some (13, 3, 5)) (.next ([30000000000],
    [60000000000]) (some (13, 3, 5)) (some (13, 3, 5)) (.next ([45000000000], [120000000000]) (some
    (13, 3, 5)) (some (13, 4, 5)) (.next ([45000000000], [201000000000]) (some (13, 4, 5)) (some
    (13, 4, 5)) (.next ([285000000000], [1410000000000]) (some (13, 4, 5)) (some (13, 4, 5)) (.next
    ([433200000000, 2310000000000], [3108600000000, -4620000000000]) (some (13, 4, 5)) (some (13, 4,
    5)) (.next ([705000000000], [5490000000000]) (some (13, 4, 5)) (some (13, 4, 5))
    fan25Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner3Part0 : FanWitness := (.next ([4125000000000], [4950000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([2145000000000, -9000000000000], [4950000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([1230000000000, 9000000000000], [4950000000000]) (some (5, 6, 4)) (some
    (5, 6, 4)) (.next ([660000000000], [4215000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([450000000000], [4050000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0], [1980000000000,
    9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([-75000000000], [4200000000000]) (some
    (0, 6, 4)) (some (0, 6, 4)) (.next ([-75000000000], [3540000000000]) (some (0, 6, 4)) (some (0,
    6, 4)) (.next ([-450000000000], [3750000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-750000000000], [4950000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-735000000000],
    [4200000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-900000000000], [4575000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-750000000000], [2970000000000, -9000000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2970000000000, 9000000000000], [9075000000000])
    (some (0, 6, 4)) (some (1, 6, 4)) (.next ([-1530000000000, -9000000000000], [4050000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-165000000000], [375000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-2235000000000, 9000000000000], [4875000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-2070000000000, 9000000000000], [4500000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-1980000000000, -9000000000000], [3960000000000, 18000000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4950000000000], [9075000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-4950000000000], [7095000000000, -9000000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-4950000000000, 0], [6180000000000, 9000000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-4215000000000], [4875000000000]) (some (1, 6, 4)) (some (1, 6, 4))
    (.next ([-4050000000000], [4500000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.terminal (some
    (1, 6, 4)) (some (1, 6, 4)) (some (1, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner3Part0 : FanWitness := (.next ([4200000000000], [4950000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([1230000000000, 9000000000000], [4950000000000]) (some (5, 1, 6)) (some
    (5, 1, 6)) (.next ([900000000000], [4500000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([660000000000], [4215000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([735000000000],
    [4875000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([450000000000], [4050000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0], [1980000000000, 9000000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([-75000000000], [3540000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-450000000000], [3750000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next
    ([-750000000000], [4950000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-750000000000],
    [2970000000000, -9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1980000000000,
    -9000000000000], [6930000000000, 9000000000000]) (some (0, 2, 6)) (some (1, 2, 6)) (.next
    ([-1320000000000, -9000000000000], [4215000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next
    ([-1530000000000, -9000000000000], [4050000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next
    ([-165000000000], [375000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-2235000000000,
    9000000000000], [4875000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-2070000000000,
    9000000000000], [4500000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-1980000000000,
    -9000000000000], [3960000000000, 18000000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next
    ([-4950000000000], [9150000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-4950000000000,
    0], [6180000000000, 9000000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-4500000000000],
    [5400000000000]) (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-4215000000000], [4875000000000])
    (some (1, 2, 6)) (some (1, 2, 6)) (.next ([-4875000000000], [5610000000000]) (some (1, 2, 6))
    (some (1, 2, 6)) (.next ([-4050000000000], [4500000000000]) (some (1, 2, 6)) (some (1, 6, 6))
    (.terminal (some (1, 6, 6)) (some (1, 6, 4)) (some (1, 6, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner3Part0 : FanWitness := (.next ([3675000000000], [4950000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([1230000000000, 9000000000000], [4950000000000]) (some (5, 1, 6)) (some
    (5, 1, 6)) (.next ([1695000000000, -9000000000000], [6930000000000, 9000000000000]) (some (5, 1,
    6)) (some (5, 1, 6)) (.next ([660000000000], [4215000000000]) (some (5, 1, 6)) (some (5, 1, 6))
    (.next ([450000000000], [4050000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0],
    [1980000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-75000000000],
    [3540000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-450000000000], [3750000000000])
    (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-1275000000000], [9150000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-750000000000], [4950000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-825000000000], [5400000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1200000000000], [5610000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-750000000000],
    [2970000000000, -9000000000000]) (some (0, 2, 6)) (some (0, 6, 6)) (.next ([-1320000000000,
    -9000000000000], [4215000000000]) (some (0, 6, 6)) (some (1, 6, 6)) (.next ([-1530000000000,
    -9000000000000], [4050000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-165000000000],
    [375000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-2235000000000, 9000000000000],
    [4875000000000]) (some (1, 6, 6)) (some (1, 6, 4)) (.next ([-2070000000000, 9000000000000],
    [4500000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-1980000000000, -9000000000000],
    [3960000000000, 18000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4950000000000],
    [8625000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4950000000000, 0], [6180000000000,
    9000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-6930000000000, -9000000000000],
    [8625000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4215000000000], [4875000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4050000000000], [4500000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.terminal (some (1, 6, 4)) (some (1, 6, 4)) (some (1, 6,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner5Part0 : FanWitness := (.next ([4740000000000], [2040000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([4980000000000, 9000000000000], [2700000000000, -9000000000000]) (some
    (4, 1, 2)) (some (4, 1, 2)) (.next ([375000000000], [294000000000]) (some (4, 1, 2)) (some (4,
    1, 2)) (.next ([2244000000000], [2061000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
    ([1950000000000], [2730000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3000000000000],
    [4680000000000]) (some (4, 1, 2)) (some (4, 1, 5)) (.next ([2640000000000], [4830000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([900000000000], [1740000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([2265000000000], [4536000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([1980000000000, 9000000000000], [5730000000000, 0]) (some (4, 1, 5)) (some (0, 1, 5))
    (.next ([1605000000000, 9000000000000], [5436000000000, 0]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([0, 0], [1980000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-375000000000], [5436000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-2040000000000],
    [6780000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2700000000000, 9000000000000],
    [7680000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-294000000000], [669000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2061000000000], [4305000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-2730000000000], [4680000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-4680000000000], [7680000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-4830000000000], [7470000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1740000000000],
    [2640000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4536000000000], [6801000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5730000000000, 0], [7710000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5436000000000, 0], [7041000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner5Part0 : FanWitness := (.next ([5115000000000], [1665000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([5355000000000, 9000000000000], [2325000000000, -9000000000000]) (some
    (4, 1, 2)) (some (4, 1, 2)) (.next ([2244000000000], [1686000000000]) (some (4, 1, 2)) (some (4,
    1, 2)) (.next ([375000000000], [294000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
    ([1950000000000], [2355000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3375000000000],
    [4305000000000]) (some (4, 1, 2)) (some (4, 1, 5)) (.next ([2640000000000], [4830000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([900000000000], [1740000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([2265000000000], [4536000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([1980000000000, 9000000000000], [5730000000000, 0]) (some (4, 1, 5)) (some (0, 1, 5))
    (.next ([1605000000000, 9000000000000], [5436000000000, 0]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([0, 0], [1980000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-375000000000], [5436000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-1665000000000],
    [6780000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2325000000000, 9000000000000],
    [7680000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1686000000000], [3930000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-294000000000], [669000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-2355000000000], [4305000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-4305000000000], [7680000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-4830000000000], [7470000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1740000000000],
    [2640000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4536000000000], [6801000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5730000000000, 0], [7710000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5436000000000, 0], [7041000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner4Part0 : FanWitness := (.next ([2880000000000, 9000000000000], [2070000000000,
    -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4425000000000], [4035000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2055000000000, 9000000000000], [2895000000000,
    -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1980000000000, 9000000000000],
    [4410000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([900000000000], [4050000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([375000000000], [2070000000000, -9000000000000]) (some
    (5, 1, 3)) (some (5, 1, 3)) (.next ([540000000000], [3510000000000]) (some (4, 1, 3)) (some (4,
    1, 3)) (.next ([540000000000], [4335000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([375000000000], [4050000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([375000000000],
    [4575000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([75000000000], [4875000000000]) (some
    (4, 1, 3)) (some (4, 1, 3)) (.next ([0], [4410000000000]) (some (4, 1, 3)) (some (4, 1, 3))
    (.next ([-450000000000], [4575000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-2070000000000, 9000000000000], [4950000000000]) (some (0, 1, 3)) (some (0, 1, 5)) (.next
    ([-4035000000000], [8460000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2895000000000,
    9000000000000], [4950000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4410000000000],
    [6390000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4050000000000],
    [4950000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2070000000000, 9000000000000],
    [2445000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3510000000000],
    [4050000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4335000000000], [4875000000000])
    (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-4050000000000], [4425000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4575000000000], [4950000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-4875000000000], [4950000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some
    (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 13) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3465000000000], [75000000000]) (some (4, 6, 2))
      (some (6, 6, 2)) (.next ([3300000000000], [450000000000]) (some (6, 6, 2)) (some (6, 6, 2))
      (.next ([4950000000000], [720000000000]) (some (6, 6, 2)) (some (6, 6, 2)) (.next
      ([4200000000000], [750000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2220000000000,
      -9000000000000], [750000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2895000000000,
      -9000000000000], [1320000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([2520000000000, -9000000000000], [1530000000000, 9000000000000]) (some (6, 1, 2)) (some (6,
      1, 2)) (.next ([210000000000], [165000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([2640000000000, 9000000000000], [2235000000000, -9000000000000]) (some (6, 1, 2)) (some (6,
      1, 3)) (.next ([2430000000000, 9000000000000], [2070000000000, -9000000000000]) (some (6, 1,
      3)) (some (6, 1, 3)) (.next ([4875000000000], [4260000000000]) (some (6, 1, 3)) (some (6, 1,
      4)) fan24Owner3Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded24_6
    · exact excluded24_7
    · exact (hj rfl).elim
    · exact excluded24_9
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1556400000000, 4620000000000], [31800000000,
      -2310000000000]) (some (9, 13, 5)) (some (10, 13, 5)) (.next ([6705000000000], [201000000000])
      (some (10, 13, 5)) (some (10, 13, 5)) (.next ([1620000000000], [81000000000]) (some (10, 13,
      5)) (some (10, 13, 5)) (.next ([1539000000000], [81000000000]) (some (10, 13, 5)) (some (10,
      13, 5)) (.next ([1475400000000, 4620000000000], [112800000000, -2310000000000]) (some (10, 13,
      5)) (some (10, 13, 5)) (.next ([1539000000000], [162000000000]) (some (10, 13, 5)) (some (10,
      13, 5)) (.next ([6285000000000], [690000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next
      ([255000000000], [30000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next ([6315000000000],
      [750000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next ([4590000000000], [615000000000])
      (some (10, 13, 5)) (some (10, 13, 5)) (.next ([6165000000000], [855000000000]) (some (10, 13,
      5)) (some (10, 13, 5)) (.next ([6195000000000], [915000000000]) (some (10, 13, 5)) (some (10,
      13, 5)) (.next ([6084000000000], [936000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next
      ([4509000000000], [696000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next
      ([6114000000000], [996000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next
      ([6285000000000], [1035000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next
      ([2970000000000], [534000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next
      ([6165000000000], [1200000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next
      ([2970000000000], [615000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next
      ([6084000000000], [1281000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next
      ([3015000000000], [735000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next
      ([5250000000000], [1350000000000]) (some (10, 13, 5)) (some (10, 13, 5)) (.next
      ([5116800000000, -2310000000000], [1331400000000, 4620000000000]) (some (10, 13, 5)) (some
      (10, 13, 5)) fan25Owner0Part3))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [75000000000]) (some (4, 1, 6))
      (some (5, 1, 6)) (.next ([3465000000000], [75000000000]) (some (5, 1, 6)) (some (5, 6, 6))
      (.next ([3300000000000], [450000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next
      ([4200000000000], [750000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next ([3465000000000],
      [735000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next ([3675000000000], [900000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([2220000000000, -9000000000000], [750000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([6105000000000, 9000000000000], [2970000000000,
      -9000000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([2520000000000, -9000000000000],
      [1530000000000, 9000000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([210000000000],
      [165000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([2640000000000, 9000000000000],
      [2235000000000, -9000000000000]) (some (5, 6, 2)) (some (5, 6, 3)) (.next ([2430000000000,
      9000000000000], [2070000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([1980000000000, 9000000000000], [1980000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6,
      4)) fan25Owner3Part0)))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 3 13) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3465000000000], [75000000000]) (some (4, 1, 6))
      (some (5, 1, 6)) (.next ([3300000000000], [450000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([4200000000000], [750000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([2220000000000, -9000000000000], [750000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([4950000000000], [1980000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([2895000000000, -9000000000000], [1320000000000, 9000000000000]) (some (5, 1, 6)) (some (5,
      1, 6)) (.next ([2520000000000, -9000000000000], [1530000000000, 9000000000000]) (some (5, 1,
      6)) (some (5, 1, 6)) (.next ([210000000000], [165000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([2640000000000, 9000000000000], [2235000000000, -9000000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([2430000000000, 9000000000000], [2070000000000, -9000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1980000000000, 9000000000000], [1980000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) fan26Owner3Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem excluded27_0 : ExcludedOn (model27.B 0 ++ [step27.q]) 9000000000000 (model27.caps 0)
    (model27.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 13) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7305000000000, 9000000000000], [2070000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([5325000000000], [4050000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1980000000000, 9000000000000], [1980000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3345000000000, -9000000000000],
      [4050000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1980000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2070000000000, 9000000000000],
      [9375000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4050000000000], [9375000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1980000000000, -9000000000000], [3960000000000,
      18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4050000000000, 0],
      [7395000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0))
      (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3465000000000], [75000000000]) (some (4, 1, 6))
      (some (5, 1, 6)) (.next ([3300000000000], [450000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([7875000000000], [1275000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([4200000000000], [750000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4575000000000],
      [825000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4410000000000], [1200000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2220000000000, -9000000000000], [750000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2895000000000, -9000000000000], [1320000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2520000000000, -9000000000000],
      [1530000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([210000000000],
      [165000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2640000000000, 9000000000000],
      [2235000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2430000000000,
      9000000000000], [2070000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([1980000000000, 9000000000000], [1980000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1,
      6)) fan27Owner3Part0)))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5061000000000], [375000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan28Owner5Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4680000000000], [1320000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([6000000000000], [2340000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([1980000000000, 9000000000000], [7020000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([660000000000, 9000000000000], [4020000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1980000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1320000000000], [6000000000000])
      (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2340000000000, 9000000000000], [8340000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-7020000000000, 9000000000000],
      [9000000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4020000000000, 9000000000000],
      [4680000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5061000000000], [375000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan29Owner5Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4305000000000], [1320000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([5625000000000], [2715000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([1980000000000, 9000000000000], [7020000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([660000000000, 9000000000000], [3645000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1980000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1320000000000], [5625000000000])
      (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2715000000000, 9000000000000], [8340000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-7020000000000, 9000000000000],
      [9000000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3645000000000, 9000000000000],
      [4305000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded30_0 : ExcludedOn (model30.B 0 ++ [step30.q]) 9000000000000 (model30.caps 0)
    (model30.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 14) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded30_4 : ExcludedOn (model30.B 4 ++ [step30.q]) 9000000000000 (model30.caps 4)
    (model30.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4170000000000], [780000000000]) (some (5, 0, 2))
      (some (5, 1, 3)) (.next ([2880000000000, 9000000000000], [2070000000000, -9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4095000000000], [4410000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([2055000000000, 9000000000000], [2895000000000, -9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1980000000000, 9000000000000], [4410000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([900000000000], [4050000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([540000000000], [3510000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([540000000000], [4335000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([75000000000], [4875000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([45000000000],
      [4950000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0], [4410000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-780000000000], [4950000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-2070000000000, 9000000000000], [4950000000000]) (some (0, 1, 3)) (some (0, 1,
      5)) (.next ([-4410000000000], [8505000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-2895000000000, 9000000000000], [4950000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4410000000000], [6390000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4050000000000], [4950000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-3510000000000], [4050000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-4335000000000], [4875000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
      ([-4875000000000], [4950000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-4950000000000], [4995000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem excluded30_8 : ExcludedOn (model30.B 8 ++ [step30.q]) 9000000000000 (model30.caps 8)
    (model30.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4905000000000], [15000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([4065000000000], [30000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([4080000000000], [855000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([4905000000000], [4095000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [4935000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-15000000000], [4920000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-30000000000], [4095000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-855000000000], [4935000000000]) (some (0, 1, 2)) (some (0, 3, 2))
      (.next ([-4095000000000], [9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 2 14) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_1 : ExcludedOn (model31.B 1 ++ [step31.q]) 9000000000000 (model31.caps 1)
    (model31.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [450000000000]) (some (5, 0, 2))
      (some (5, 1, 3)) fan31Owner4Part0)) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4950000000000], [345000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([4080000000000], [855000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([4950000000000], [4425000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([15000000000], [4425000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [4935000000000]) (some (0, 1, 3)) (some (0, 3, 3)) (.next ([-345000000000], [5295000000000])
      (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-855000000000], [4935000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-4425000000000], [9375000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4425000000000], [4440000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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

end Sext220000230000
end ConwaySoifer.Simplified.Certificates
