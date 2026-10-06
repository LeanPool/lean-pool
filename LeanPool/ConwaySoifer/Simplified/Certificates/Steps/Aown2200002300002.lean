/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown220000230000
import Mathlib.Tactic.FinCases

/-!
# Aown 220000 230000 2

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
namespace Aown220000230000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part0 : FanWitness := (.next ([-5460000000000], [8460000000000]) (some (2, 8, 12))
    (some (2, 8, 12)) (.next ([-5145000000000], [7920000000000]) (some (2, 8, 12)) (some (2, 8, 12))
    (.next ([-1230000000000], [1890000000000]) (some (2, 8, 12)) (some (2, 8, 12)) (.next
    ([-4920000000000], [7461000000000]) (some (2, 8, 12)) (some (2, 8, 12)) (.next
    ([-1035000000000], [1515000000000]) (some (2, 8, 12)) (some (2, 8, 12)) (.next
    ([-6000000000000], [8775000000000]) (some (2, 8, 12)) (some (2, 8, 12)) (.next
    ([-4965000000000], [7260000000000]) (some (2, 8, 12)) (some (2, 8, 12)) (.next
    ([-1980000000000], [2835000000000]) (some (2, 8, 12)) (some (2, 8, 12)) (.next
    ([-6375000000000], [8955000000000]) (some (2, 8, 12)) (some (2, 8, 12)) (.next
    ([-1395000000000], [1935000000000]) (some (2, 8, 12)) (some (2, 8, 12)) (.next
    ([-6540000000000], [9000000000000]) (some (2, 8, 12)) (some (2, 8, 12)) (.next ([-120000000000],
    [165000000000]) (some (2, 8, 12)) (some (2, 8, 12)) (.next ([-5145000000000], [7065000000000])
    (some (2, 8, 12)) (some (3, 8, 12)) (.next ([-6621000000000], [9000000000000]) (some (3, 8, 12))
    (some (3, 8, 12)) (.next ([-1476000000000], [1935000000000]) (some (3, 8, 12)) (some (3, 8, 12))
    (.next ([-2355000000000], [3015000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-5379000000000], [6840000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next ([-201000000000],
    [246000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next ([-1080000000000], [1314000000000])
    (some (3, 8, 12)) (some (3, 8, 12)) (.next ([-1410000000000], [1695000000000]) (some (3, 8, 12))
    (some (3, 8, 12)) (.next ([-2601000000000], [3060000000000]) (some (3, 8, 12)) (some (3, 8, 12))
    (.next ([-1575000000000], [1740000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-1656000000000], [1740000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-1455000000000], [1494000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.terminal (some (3, 8,
    12)) (some (3, 8, 12)) (some (3, 8, 12)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part1 : FanWitness := (.next ([-180000000000], [660000000000]) (some (12, 7, 12))
    (some (12, 7, 12)) (.next ([-855000000000], [2835000000000]) (some (12, 7, 12)) (some (12, 7,
    12)) (.next ([-621000000000], [1935000000000]) (some (12, 7, 12)) (some (12, 7, 12)) (.next
    ([-375000000000], [1035000000000]) (some (12, 7, 12)) (some (12, 7, 12)) (.next
    ([-1035000000000], [2640000000000]) (some (12, 7, 12)) (some (12, 7, 12)) (.next
    ([-495000000000], [1200000000000]) (some (12, 7, 12)) (some (12, 7, 12)) (.next
    ([-225000000000], [540000000000]) (some (12, 7, 12)) (some (12, 7, 12)) (.next
    ([-1080000000000], [2520000000000]) (some (12, 7, 12)) (some (12, 7, 12)) (.next
    ([-1080000000000], [2439000000000]) (some (12, 7, 12)) (some (12, 7, 12)) (.next
    ([-576000000000], [1281000000000]) (some (12, 7, 12)) (some (12, 8, 12)) (.next
    ([-420000000000], [915000000000]) (some (12, 8, 12)) (some (12, 8, 12)) (.next ([-996000000000],
    [2115000000000]) (some (12, 8, 12)) (some (12, 8, 12)) (.next ([-225000000000], [459000000000])
    (some (12, 8, 12)) (some (12, 8, 12)) (.next ([-540000000000], [1080000000000]) (some (12, 8,
    12)) (some (12, 8, 12)) (.next ([-420000000000], [834000000000]) (some (12, 8, 12)) (some (12,
    8, 12)) (.next ([-195000000000], [375000000000]) (some (12, 8, 12)) (some (12, 8, 12)) (.next
    ([-621000000000], [1161000000000]) (some (12, 8, 12)) (some (12, 8, 12)) (.next
    ([-1161000000000], [2160000000000]) (some (12, 8, 12)) (some (12, 8, 12)) (.next
    ([-540000000000], [999000000000]) (some (12, 8, 12)) (some (12, 8, 12)) (.next ([-621000000000],
    [1080000000000]) (some (12, 8, 12)) (some (12, 8, 12)) (.next ([-315000000000], [540000000000])
    (some (12, 8, 12)) (some (12, 8, 12)) (.next ([-1521000000000], [2601000000000]) (some (12, 8,
    12)) (some (12, 8, 12)) (.next ([-396000000000], [621000000000]) (some (12, 8, 12)) (some (12,
    8, 12)) (.next ([-5340000000000], [8295000000000]) (some (12, 8, 12)) (some (12, 8, 12))
    fan18Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part2 : FanWitness := (.next ([540000000000], [1395000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([2460000000000], [6540000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([45000000000], [120000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([1920000000000], [5145000000000]) (some (12, 5, 8)) (some (12, 6, 8)) (.next ([2379000000000],
    [6621000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([459000000000], [1476000000000])
    (some (12, 6, 8)) (some (12, 6, 8)) (.next ([660000000000], [2355000000000]) (some (12, 6, 8))
    (some (12, 6, 8)) (.next ([1461000000000], [5379000000000]) (some (12, 6, 8)) (some (12, 6, 8))
    (.next ([45000000000], [201000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next
    ([234000000000], [1080000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([285000000000],
    [1410000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([459000000000], [2601000000000])
    (some (12, 6, 8)) (some (12, 6, 8)) (.next ([165000000000], [1575000000000]) (some (12, 6, 8))
    (some (12, 6, 8)) (.next ([84000000000], [1656000000000]) (some (12, 6, 8)) (some (12, 6, 8))
    (.next ([39000000000], [1455000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([0],
    [855000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([-60000000000], [7980000000000])
    (some (12, 6, 8)) (some (12, 7, 8)) (.next ([-81000000000], [1620000000000]) (some (12, 7, 8))
    (some (12, 7, 12)) (.next ([-162000000000], [1701000000000]) (some (12, 7, 12)) (some (12, 7,
    12)) (.next ([-375000000000], [3015000000000]) (some (12, 7, 12)) (some (12, 7, 12)) (.next
    ([-195000000000], [1230000000000]) (some (12, 7, 12)) (some (12, 7, 12)) (.next
    ([-540000000000], [3060000000000]) (some (12, 7, 12)) (some (12, 7, 12)) (.next
    ([-315000000000], [1395000000000]) (some (12, 7, 12)) (some (12, 7, 12)) (.next
    ([-396000000000], [1476000000000]) (some (12, 7, 12)) (some (12, 7, 12))
    fan18Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part3 : FanWitness := (.next ([705000000000], [576000000000]) (some (12, 4, 8)) (some
    (12, 4, 8)) (.next ([495000000000], [420000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([1119000000000], [996000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([234000000000],
    [225000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([540000000000], [540000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([414000000000], [420000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([180000000000], [195000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([540000000000], [621000000000]) (some (12, 4, 8)) (some (12, 5, 8)) (.next
    ([999000000000], [1161000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([459000000000],
    [540000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([459000000000], [621000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) (.next ([225000000000], [315000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([1080000000000], [1521000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([225000000000], [396000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([2955000000000], [5340000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([3000000000000],
    [5460000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([2775000000000], [5145000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) (.next ([660000000000], [1230000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([2541000000000], [4920000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([480000000000], [1035000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([2775000000000], [6000000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([2295000000000],
    [4965000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([855000000000], [1980000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) (.next ([2580000000000], [6375000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) fan18Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part0 : FanWitness := (.next ([-315000000000], [540000000000]) (some (13, 13, 9))
    (some (13, 13, 9)) (.next ([-1521000000000], [2601000000000]) (some (13, 13, 9)) (some (13, 13,
    9)) (.next ([-396000000000], [621000000000]) (some (13, 13, 9)) (some (13, 13, 9)) (.next
    ([-1230000000000], [1890000000000]) (some (13, 13, 9)) (some (13, 13, 9)) (.next
    ([-1035000000000], [1515000000000]) (some (13, 13, 9)) (some (13, 13, 9)) (.next
    ([-1980000000000], [2835000000000]) (some (13, 13, 9)) (some (13, 13, 9)) (.next
    ([-1395000000000], [1935000000000]) (some (13, 13, 9)) (some (13, 13, 9)) (.next
    ([-120000000000], [165000000000]) (some (13, 13, 9)) (some (13, 13, 9)) (.next
    ([-1125000000000], [1515000000000]) (some (13, 13, 9)) (some (13, 13, 9)) (.next
    ([-1476000000000], [1935000000000]) (some (13, 13, 9)) (some (13, 13, 9)) (.next
    ([-2355000000000], [3015000000000]) (some (13, 13, 9)) (some (13, 13, 9)) (.next
    ([-7260000000000], [9240000000000]) (some (13, 13, 9)) (some (13, 13, 9)) (.next
    ([-201000000000], [246000000000]) (some (13, 8, 9)) (some (13, 8, 9)) (.next ([-1080000000000],
    [1314000000000]) (some (13, 8, 9)) (some (13, 8, 9)) (.next ([-1410000000000], [1695000000000])
    (some (13, 8, 9)) (some (13, 8, 9)) (.next ([-2601000000000], [3060000000000]) (some (13, 8, 9))
    (some (13, 8, 9)) (.next ([-1500000000000], [1695000000000]) (some (13, 8, 9)) (some (13, 8, 9))
    (.next ([-1575000000000], [1740000000000]) (some (13, 8, 9)) (some (13, 8, 9)) (.next
    ([-6180000000000], [6801000000000]) (some (13, 8, 9)) (some (13, 8, 9)) (.next
    ([-6180000000000], [6720000000000]) (some (13, 8, 9)) (some (13, 8, 9)) (.next
    ([-6225000000000], [6600000000000]) (some (13, 8, 9)) (some (13, 8, 9)) (.next
    ([-1656000000000], [1740000000000]) (some (13, 8, 9)) (some (13, 8, 9)) (.next
    ([-1665000000000], [1740000000000]) (some (13, 8, 9)) (some (13, 8, 9)) (.next
    ([-1455000000000], [1494000000000]) (some (13, 8, 9)) (some (13, 8, 9)) (.terminal (some (13, 8,
    9)) (some (13, 8, 9)) (some (13, 8, 9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part1 : FanWitness := (.next ([-375000000000], [1035000000000]) (some (13, 13, 8))
    (some (13, 13, 8)) (.next ([-840000000000], [2160000000000]) (some (13, 13, 8)) (some (13, 13,
    8)) (.next ([-1035000000000], [2640000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next
    ([-270000000000], [660000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-495000000000],
    [1200000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-225000000000], [540000000000])
    (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-1080000000000], [2520000000000]) (some (13, 13,
    8)) (some (13, 13, 8)) (.next ([-1080000000000], [2439000000000]) (some (13, 13, 8)) (some (13,
    13, 8)) (.next ([-465000000000], [1035000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next
    ([-576000000000], [1281000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next
    ([-1005000000000], [2205000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next
    ([-420000000000], [915000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-996000000000],
    [2115000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-225000000000], [459000000000])
    (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-1086000000000], [2205000000000]) (some (13, 13,
    8)) (some (13, 13, 8)) (.next ([-540000000000], [1080000000000]) (some (13, 13, 8)) (some (13,
    13, 8)) (.next ([-420000000000], [834000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next
    ([-666000000000], [1281000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next
    ([-195000000000], [375000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-621000000000],
    [1161000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-1161000000000],
    [2160000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-1320000000000],
    [2445000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-540000000000], [999000000000])
    (some (13, 13, 8)) (some (13, 13, 9)) (.next ([-621000000000], [1080000000000]) (some (13, 13,
    9)) (some (13, 13, 9)) fan20Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part2 : FanWitness := (.next ([84000000000], [1656000000000]) (some (0, 13, 8)) (some
    (0, 13, 8)) (.next ([75000000000], [1665000000000]) (some (0, 13, 8)) (some (0, 13, 8)) (.next
    ([39000000000], [1455000000000]) (some (0, 13, 8)) (some (0, 13, 8)) (.next ([0],
    [855000000000]) (some (0, 13, 8)) (some (0, 13, 8)) (.next ([-81000000000], [1620000000000])
    (some (0, 13, 8)) (some (0, 13, 8)) (.next ([-465000000000], [8385000000000]) (some (0, 13, 8))
    (some (0, 13, 8)) (.next ([-621000000000], [8340000000000]) (some (0, 13, 8)) (some (0, 13, 8))
    (.next ([-540000000000], [6720000000000]) (some (0, 13, 8)) (some (0, 13, 8)) (.next
    ([-162000000000], [1701000000000]) (some (0, 13, 8)) (some (0, 13, 8)) (.next ([-660000000000],
    [6885000000000]) (some (0, 13, 8)) (some (0, 13, 8)) (.next ([-855000000000], [8115000000000])
    (some (0, 13, 8)) (some (0, 13, 8)) (.next ([-855000000000], [7260000000000]) (some (0, 13, 8))
    (some (0, 13, 8)) (.next ([-375000000000], [3015000000000]) (some (0, 13, 8)) (some (0, 13, 8))
    (.next ([-1035000000000], [7920000000000]) (some (0, 13, 8)) (some (0, 13, 8)) (.next
    ([-1080000000000], [7719000000000]) (some (0, 13, 8)) (some (0, 13, 8)) (.next ([-195000000000],
    [1230000000000]) (some (0, 13, 8)) (some (13, 13, 8)) (.next ([-540000000000], [3060000000000])
    (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-45000000000], [201000000000]) (some (13, 13, 8))
    (some (13, 13, 8)) (.next ([-315000000000], [1395000000000]) (some (13, 13, 8)) (some (13, 13,
    8)) (.next ([-465000000000], [1980000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next
    ([-396000000000], [1476000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next
    ([-180000000000], [660000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-855000000000],
    [2835000000000]) (some (13, 13, 8)) (some (13, 13, 8)) (.next ([-621000000000], [1935000000000])
    (some (13, 13, 8)) (some (13, 13, 8)) fan20Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part3 : FanWitness := (.next ([1125000000000], [1320000000000]) (some (12, 13, 8))
    (some (12, 13, 8)) (.next ([459000000000], [540000000000]) (some (12, 13, 8)) (some (12, 13, 8))
    (.next ([459000000000], [621000000000]) (some (12, 13, 8)) (some (12, 13, 8)) (.next
    ([225000000000], [315000000000]) (some (12, 13, 8)) (some (12, 13, 8)) (.next ([1080000000000],
    [1521000000000]) (some (12, 13, 8)) (some (12, 13, 8)) (.next ([225000000000], [396000000000])
    (some (12, 13, 8)) (some (12, 13, 8)) (.next ([660000000000], [1230000000000]) (some (12, 13,
    8)) (some (12, 13, 8)) (.next ([480000000000], [1035000000000]) (some (12, 13, 8)) (some (12,
    13, 8)) (.next ([855000000000], [1980000000000]) (some (12, 13, 8)) (some (12, 13, 8)) (.next
    ([540000000000], [1395000000000]) (some (12, 13, 8)) (some (12, 13, 8)) (.next ([45000000000],
    [120000000000]) (some (12, 13, 8)) (some (12, 13, 8)) (.next ([390000000000], [1125000000000])
    (some (12, 13, 8)) (some (12, 13, 8)) (.next ([459000000000], [1476000000000]) (some (12, 13,
    8)) (some (12, 13, 8)) (.next ([660000000000], [2355000000000]) (some (12, 13, 8)) (some (12,
    13, 8)) (.next ([1980000000000], [7260000000000]) (some (12, 13, 8)) (some (12, 13, 8)) (.next
    ([45000000000], [201000000000]) (some (12, 13, 8)) (some (12, 13, 8)) (.next ([234000000000],
    [1080000000000]) (some (0, 13, 8)) (some (0, 13, 8)) (.next ([285000000000], [1410000000000])
    (some (0, 13, 8)) (some (0, 13, 8)) (.next ([459000000000], [2601000000000]) (some (0, 13, 8))
    (some (0, 13, 8)) (.next ([195000000000], [1500000000000]) (some (0, 13, 8)) (some (0, 13, 8))
    (.next ([165000000000], [1575000000000]) (some (0, 13, 8)) (some (0, 13, 8)) (.next
    ([621000000000], [6180000000000]) (some (0, 13, 8)) (some (0, 13, 8)) (.next ([540000000000],
    [6180000000000]) (some (0, 13, 8)) (some (0, 13, 8)) (.next ([375000000000], [6225000000000])
    (some (0, 13, 8)) (some (0, 13, 8)) fan20Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part4 : FanWitness := (.next ([480000000000], [180000000000]) (some (10, 13, 8))
    (some (10, 13, 8)) (.next ([1980000000000], [855000000000]) (some (10, 13, 8)) (some (10, 13,
    8)) (.next ([1314000000000], [621000000000]) (some (10, 13, 8)) (some (10, 13, 8)) (.next
    ([660000000000], [375000000000]) (some (10, 13, 8)) (some (10, 13, 8)) (.next ([1320000000000],
    [840000000000]) (some (10, 13, 8)) (some (10, 13, 8)) (.next ([1605000000000], [1035000000000])
    (some (10, 13, 8)) (some (10, 13, 8)) (.next ([390000000000], [270000000000]) (some (10, 13, 8))
    (some (10, 13, 8)) (.next ([705000000000], [495000000000]) (some (10, 13, 8)) (some (10, 13, 8))
    (.next ([315000000000], [225000000000]) (some (10, 13, 8)) (some (10, 13, 8)) (.next
    ([1440000000000], [1080000000000]) (some (10, 13, 8)) (some (10, 13, 8)) (.next
    ([1359000000000], [1080000000000]) (some (10, 13, 8)) (some (10, 13, 8)) (.next ([570000000000],
    [465000000000]) (some (10, 13, 8)) (some (10, 13, 8)) (.next ([705000000000], [576000000000])
    (some (10, 13, 8)) (some (10, 13, 8)) (.next ([1200000000000], [1005000000000]) (some (10, 13,
    8)) (some (10, 13, 8)) (.next ([495000000000], [420000000000]) (some (10, 13, 8)) (some (10, 13,
    8)) (.next ([1119000000000], [996000000000]) (some (10, 13, 8)) (some (10, 13, 8)) (.next
    ([234000000000], [225000000000]) (some (10, 13, 8)) (some (10, 13, 8)) (.next ([1119000000000],
    [1086000000000]) (some (10, 13, 8)) (some (11, 13, 8)) (.next ([540000000000], [540000000000])
    (some (11, 13, 8)) (some (11, 13, 8)) (.next ([414000000000], [420000000000]) (some (11, 13, 8))
    (some (11, 13, 8)) (.next ([615000000000], [666000000000]) (some (11, 13, 8)) (some (11, 13, 8))
    (.next ([180000000000], [195000000000]) (some (11, 13, 8)) (some (11, 13, 8)) (.next
    ([540000000000], [621000000000]) (some (11, 13, 8)) (some (12, 13, 8)) (.next ([999000000000],
    [1161000000000]) (some (12, 13, 8)) (some (12, 13, 8)) fan20Owner0Part3))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner2Part0 : FanWitness := (.next ([7020000000000, -9000000000000], [1980000000000,
    9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5385000000000, 0], [1980000000000,
    9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2805000000000, -9000000000000],
    [1320000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([615000000000,
    -9000000000000], [375000000000, 0]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1815000000000],
    [1935000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([375000000000], [645000000000]) (some
    (0, 4, 1)) (some (0, 4, 1)) (.next ([1170000000000], [2955000000000]) (some (0, 4, 1)) (some (0,
    4, 2)) (.next ([2145000000000, -9000000000000], [6195000000000, 9000000000000]) (some (0, 4, 2))
    (some (0, 4, 2)) (.next ([1230000000000], [5175000000000]) (some (0, 4, 2)) (some (0, 4, 2))
    (.next ([855000000000], [4530000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
    ([855000000000, 0], [6165000000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next
    ([0, 0], [2835000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
    ([-1605000000000, -9000000000000], [8010000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4,
    3)) (.next ([-1980000000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 3)) (some (0, 4,
    3)) (.next ([-1980000000000, -9000000000000], [7365000000000, 9000000000000]) (some (0, 4, 3))
    (some (0, 4, 3)) (.next ([-1320000000000, -9000000000000], [4125000000000, 0]) (some (0, 4, 3))
    (some (0, 4, 3)) (.next ([-375000000000, 0], [990000000000, -9000000000000]) (some (0, 4, 3))
    (some (0, 4, 3)) (.next ([-1935000000000], [3750000000000]) (some (0, 4, 3)) (some (0, 4, 3))
    (.next ([-645000000000], [1020000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-2955000000000], [4125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6195000000000,
    -9000000000000], [8340000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5175000000000],
    [6405000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next ([-4530000000000], [5385000000000])
    (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-6165000000000, 9000000000000], [7020000000000,
    -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1, 0))
    (some (4, 1, 3)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([2265000000000, -9000000000000], [1980000000000,
      9000000000000]) (some (2, 0, 1)) (some (3, 0, 2)) (.next ([1980000000000, 9000000000000],
      [2775000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1980000000000,
      9000000000000], [5040000000000, -18000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([1980000000000, 9000000000000], [7020000000000, -9000000000000]) (some (3, 0, 2)) (some (3,
      0, 2)) (.next ([0, 0], [7020000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2))
      (.next ([-1980000000000, -9000000000000], [4245000000000]) (some (0, 0, 2)) (some (0, 0, 2))
      (.next ([-2775000000000, 9000000000000], [4755000000000, 0]) (some (0, 0, 2)) (some (0, 0, 2))
      (.next ([-5040000000000, 18000000000000], [7020000000000, -9000000000000]) (some (0, 0, 2))
      (some (0, 4, 2)) (.next ([-7020000000000, 9000000000000], [9000000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 1, 2)) (some (0, 4, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded16_2
    · exact excluded16_3
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
  apply ExclusionHint.sound (.pair 0 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1125000000000, 0], [195000000000,
      9000000000000]) none none (.next ([1980000000000, 9000000000000], [1980000000000,
      9000000000000]) none none (.next ([1980000000000, 9000000000000], [2775000000000,
      -9000000000000]) (some (4, 2, 4)) (some (4, 2, 4)) (.next ([1980000000000, 9000000000000],
      [4050000000000, -9000000000000]) (some (4, 2, 4)) (some (4, 2, 4)) (.next ([1785000000000],
      [4095000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([1785000000000], [5370000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([0], [6735000000000, 9000000000000]) (some (0, 2,
      4)) (some (0, 2, 4)) (.next ([-195000000000, -9000000000000], [1320000000000, 9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1980000000000, -9000000000000], [3960000000000,
      18000000000000]) (some (0, 2, 4)) (some (1, 2, 4)) (.next ([-2775000000000, 9000000000000],
      [4755000000000, 0]) (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-4050000000000, 9000000000000],
      [6030000000000, 0]) (some (1, 2, 4)) (some (1, 2, 4)) (.next ([-4095000000000],
      [5880000000000]) (some (1, 2, 4)) (some (2, 2, 4)) (.next ([-5370000000000], [7155000000000])
      (some (2, 2, 4)) none (.terminal none none none))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded17_4
    · exact excluded17_5
    · exact excluded17_6
    · exact (hj rfl).elim
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded18_0 : ExcludedOn (model18.B 0 ++ [step18.q]) 9000000000000 (model18.caps 0)
    (model18.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7920000000000], [60000000000]) (some (12, 3, 8))
      (some (12, 3, 8)) (.next ([1539000000000], [81000000000]) (some (12, 3, 8)) (some (12, 3, 8))
      (.next ([1539000000000], [162000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next
      ([2640000000000], [375000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next ([1035000000000],
      [195000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next ([2520000000000], [540000000000])
      (some (12, 3, 8)) (some (12, 3, 8)) (.next ([1080000000000], [315000000000]) (some (12, 3, 8))
      (some (12, 3, 8)) (.next ([1080000000000], [396000000000]) (some (12, 3, 8)) (some (12, 3, 8))
      (.next ([480000000000], [180000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next
      ([1980000000000], [855000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next ([1314000000000],
      [621000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next ([660000000000], [375000000000])
      (some (12, 3, 8)) (some (12, 3, 8)) (.next ([1605000000000], [1035000000000]) (some (12, 3,
      8)) (some (12, 3, 8)) (.next ([705000000000], [495000000000]) (some (12, 3, 8)) (some (12, 3,
      8)) (.next ([315000000000], [225000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next
      ([1440000000000], [1080000000000]) (some (12, 3, 8)) (some (12, 4, 8)) (.next
      ([1359000000000], [1080000000000]) (some (12, 4, 8)) (some (12, 4, 8))
      fan18Owner0Part3))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7485000000000, -9000000000000], [855000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6495000000000], [1470000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6360000000000, -9000000000000], [1515000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6405000000000, 0], [1605000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7020000000000, -9000000000000],
      [1980000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5385000000000, 0],
      [1980000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5850000000000],
      [2490000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([615000000000, -9000000000000],
      [375000000000, 0]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([375000000000], [645000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([375000000000], [6030000000000]) (some (0, 4, 1))
      (some (0, 4, 2)) (.next ([465000000000], [7875000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([0, 0], [1980000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-855000000000, -9000000000000], [8340000000000, 0]) (some (0, 4, 2)) (some (0, 4, 3)) (.next
      ([-1470000000000], [7965000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1515000000000,
      -9000000000000], [7875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1605000000000,
      -9000000000000], [8010000000000, 9000000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-1980000000000, -9000000000000], [9000000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-1980000000000, -9000000000000], [7365000000000, 9000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-2490000000000], [8340000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-375000000000, 0], [990000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-645000000000], [1020000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-6030000000000], [6405000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-7875000000000], [8340000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7875000000000], [660000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([3000000000000], [900000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([5895000000000, -9000000000000], [2640000000000, 9000000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([1980000000000, 9000000000000], [1980000000000,
      9000000000000]) (some (3, 0, 4)) (some (3, 4, 4)) (.next ([1080000000000], [1920000000000])
      (some (3, 4, 4)) (some (3, 4, 4)) (.next ([1260000000000], [5535000000000]) (some (3, 4, 4))
      (some (3, 4, 4)) (.next ([1320000000000, 9000000000000], [6555000000000, -9000000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([60000000000, 9000000000000], [1020000000000,
      -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([0], [1980000000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([-660000000000], [8535000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-900000000000, -9000000000000], [3900000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2640000000000, -9000000000000],
      [8535000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1980000000000, -9000000000000],
      [3960000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1920000000000],
      [3000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5535000000000], [6795000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-6555000000000, 9000000000000], [7875000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1020000000000, 9000000000000], [1080000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4,
      2))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([1539000000000], [81000000000]) (some (9, 13, 8))
      (some (9, 13, 8)) (.next ([7920000000000], [465000000000]) (some (9, 13, 8)) (some (9, 13, 8))
      (.next ([7719000000000], [621000000000]) (some (9, 13, 8)) (some (9, 13, 8)) (.next
      ([6180000000000], [540000000000]) (some (9, 13, 8)) (some (9, 13, 8)) (.next ([1539000000000],
      [162000000000]) (some (9, 13, 8)) (some (9, 13, 8)) (.next ([6225000000000], [660000000000])
      (some (9, 13, 8)) (some (9, 13, 8)) (.next ([7260000000000], [855000000000]) (some (9, 13, 8))
      (some (9, 13, 8)) (.next ([6405000000000], [855000000000]) (some (9, 13, 8)) (some (9, 13, 8))
      (.next ([2640000000000], [375000000000]) (some (9, 13, 8)) (some (9, 13, 8)) (.next
      ([6885000000000], [1035000000000]) (some (9, 13, 8)) (some (9, 13, 8)) (.next
      ([6639000000000], [1080000000000]) (some (9, 13, 8)) (some (9, 13, 8)) (.next
      ([1035000000000], [195000000000]) (some (9, 13, 8)) (some (9, 13, 8)) (.next ([2520000000000],
      [540000000000]) (some (9, 13, 8)) (some (9, 13, 8)) (.next ([156000000000], [45000000000])
      (some (9, 13, 8)) (some (9, 13, 8)) (.next ([1080000000000], [315000000000]) (some (9, 13, 8))
      (some (10, 13, 8)) (.next ([1515000000000], [465000000000]) (some (10, 13, 8)) (some (10, 13,
      8)) (.next ([1080000000000], [396000000000]) (some (10, 13, 8)) (some (10, 13, 8))
      fan20Owner0Part4))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded20_6
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7020000000000, -9000000000000], [690000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6030000000000], [1305000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([6405000000000, 0], [1605000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7020000000000, -9000000000000], [1980000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5730000000000, -9000000000000],
      [1980000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5385000000000, 0],
      [1980000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5385000000000],
      [2325000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([615000000000, -9000000000000],
      [375000000000, 0]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([375000000000], [645000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([375000000000], [6030000000000]) (some (0, 4, 1))
      (some (0, 4, 2)) (.next ([0, 0], [1980000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([-690000000000, -9000000000000], [7710000000000, 0]) (some (0, 4, 2)) (some (0, 4,
      3)) (.next ([-1305000000000], [7335000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-1605000000000, -9000000000000], [8010000000000, 9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-1980000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some
      (0, 1, 3)) (.next ([-1980000000000, -9000000000000], [7710000000000]) (some (0, 1, 3)) (some
      (0, 1, 3)) (.next ([-1980000000000, -9000000000000], [7365000000000, 9000000000000]) (some (0,
      1, 3)) (some (4, 1, 3)) (.next ([-2325000000000], [7710000000000]) (some (4, 1, 3)) (some (4,
      1, 3)) (.next ([-375000000000, 0], [990000000000, -9000000000000]) (some (4, 1, 3)) (some (4,
      1, 3)) (.next ([-645000000000], [1020000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-6030000000000], [6405000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7710000000000], [1290000000000]) (some (2, 0,
      4)) (some (3, 0, 4)) (.next ([3000000000000], [900000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([5730000000000, -9000000000000], [3270000000000, 9000000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([1980000000000, 9000000000000], [1980000000000,
      9000000000000]) (some (3, 0, 4)) (some (3, 4, 4)) (.next ([1080000000000], [1920000000000])
      (some (3, 4, 4)) (some (3, 4, 4)) (.next ([60000000000, 9000000000000], [1020000000000,
      -9000000000000]) (some (3, 4, 4)) (some (3, 4, 4)) (.next ([0], [1980000000000,
      9000000000000]) (some (3, 4, 4)) (some (3, 4, 2)) (.next ([-1290000000000], [9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-900000000000, -9000000000000], [3900000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3270000000000, -9000000000000],
      [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1980000000000, -9000000000000],
      [3960000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1920000000000],
      [3000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1020000000000, 9000000000000],
      [1080000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4,
      2)) (some (0, 4, 2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded21_1
    · exact excluded21_2
    · exact excluded21_3
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
  apply ExclusionHint.sound (.pair 0 13) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([2970000000000], [5175000000000]) (some (2, 0,
      1)) (some (4, 0, 2)) (.next ([1980000000000, 9000000000000], [4050000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1980000000000, 9000000000000], [7020000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([855000000000, 0], [6165000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0], [7020000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-5175000000000], [8145000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-4050000000000, 9000000000000], [6030000000000, 0])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-7020000000000, 9000000000000], [9000000000000, 0])
      (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-6165000000000, 9000000000000], [7020000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded22_3
    · exact excluded22_4
    · exact excluded22_5
    · exact excluded22_6
    · exact excluded22_7
    · exact excluded22_8
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1125000000000, 0], [195000000000,
      9000000000000]) none none (.next ([2805000000000, -9000000000000], [1320000000000,
      9000000000000]) none none (.next ([2640000000000, 9000000000000], [2145000000000,
      -9000000000000]) none none (.next ([4785000000000], [4095000000000]) none none (.next
      ([1980000000000, 9000000000000], [1980000000000, 9000000000000]) none none (.next
      ([1980000000000, 9000000000000], [2775000000000, -9000000000000]) none none (.next
      ([855000000000, 9000000000000], [1785000000000]) none none (.next ([1785000000000],
      [4095000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([0], [3000000000000]) (some (4, 2,
      3)) (some (4, 2, 3)) (.next ([-195000000000, -9000000000000], [1320000000000, 9000000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-1320000000000, -9000000000000], [4125000000000,
      0]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-2145000000000, 9000000000000],
      [4785000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-4095000000000], [8880000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-1980000000000, -9000000000000], [3960000000000,
      18000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-2775000000000, 9000000000000],
      [4755000000000, 0]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-1785000000000],
      [2640000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-4095000000000],
      [5880000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2, 3)) none
      none))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6405000000000, 0], [1605000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) fan23Owner2Part0)) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4050000000000], [735000000000]) (some (3, 0, 1))
      (some (3, 0, 2)) (.next ([6855000000000, 9000000000000], [2805000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([4875000000000], [4785000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1980000000000, 9000000000000], [5610000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([0, 0], [1980000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0,
      2)) (.next ([-735000000000], [4785000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next
      ([-2805000000000, 9000000000000], [9660000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next
      ([-4785000000000], [9660000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5610000000000,
      0], [7590000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded23_1
    · exact excluded23_2
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

end Aown220000230000
end ConwaySoifer.Simplified.Certificates
