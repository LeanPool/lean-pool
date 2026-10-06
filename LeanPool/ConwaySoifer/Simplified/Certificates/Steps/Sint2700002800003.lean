/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint270000280000
import Mathlib.Tactic.FinCases

/-!
# Sint 270000 280000 3

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
namespace Sint270000280000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner4Part0 : FanWitness := (.next ([825000000000], [4845000000000]) (some (7, 1, 3)) (some
    (7, 1, 3)) (.next ([750000000000], [5010000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
    ([0, 0], [2430000000000, 9000000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([0,
    -9000000000000], [3000000000000, 0]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([-360000000000],
    [4860000000000]) (some (7, 1, 3)) (some (7, 2, 3)) (.next ([-570000000000, 9000000000000],
    [5430000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([-150000000000], [1260000000000])
    (some (7, 2, 3)) (some (7, 2, 3)) (.next ([-1185000000000], [5175000000000]) (some (7, 2, 3))
    (some (7, 2, 4)) (.next ([-1035000000000], [3915000000000]) (some (7, 2, 4)) (some (7, 2, 4))
    (.next ([-1845000000000, -9000000000000], [5670000000000, 9000000000000]) (some (7, 2, 4)) (some
    (7, 2, 5)) (.next ([-1680000000000, -9000000000000], [5010000000000, 0]) (some (7, 2, 5)) (some
    (7, 2, 5)) (.next ([-1620000000000], [3825000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([-3000000000000], [7050000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-2580000000000,
    9000000000000], [5760000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-2430000000000,
    -9000000000000], [4860000000000, 18000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([-2430000000000, 9000000000000], [4500000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([-3000000000000], [5430000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-2790000000000,
    -9000000000000], [4860000000000, 0]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-5010000000000],
    [7380000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-4860000000000], [6120000000000])
    (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-1680000000000], [2010000000000]) (some (7, 2, 5))
    (some (7, 2, 5)) (.next ([-3240000000000], [3825000000000]) (some (7, 2, 5)) (some (7, 3, 5))
    (.next ([-4845000000000], [5670000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next
    ([-5010000000000], [5760000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.terminal (some (7, 3,
    5)) (some (0, 3, 5)) (some (7, 3, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner4Part0 : FanWitness := (.next ([1020000000000], [1980000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([1350000000000], [3660000000000]) (some (5, 6, 3)) (some (5, 6, 3))
    (.next ([330000000000], [1680000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
    ([855000000000], [5430000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([750000000000],
    [5010000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([90000000000], [4770000000000]) (some
    (5, 6, 3)) (some (5, 6, 3)) (.next ([0, 0], [2430000000000, 9000000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([0, -9000000000000], [3000000000000, 0]) (some (0, 6, 3)) (some (0, 6,
    3)) (.next ([-360000000000], [4860000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next
    ([-150000000000], [1260000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([-1155000000000],
    [5760000000000]) (some (0, 6, 3)) (some (0, 6, 4)) (.next ([-1005000000000], [4500000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-930000000000], [2790000000000]) (some (0, 6, 4))
    (some (0, 6, 5)) (.next ([-1680000000000, -9000000000000], [5010000000000, 0]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-2430000000000, -9000000000000], [6285000000000, 9000000000000]) (some
    (0, 6, 5)) (some (0, 6, 5)) (.next ([-4410000000000], [8265000000000]) (some (0, 6, 5)) (some
    (0, 6, 5)) (.next ([-3000000000000], [5430000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-2790000000000, -9000000000000], [4860000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-1980000000000], [3000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3660000000000],
    [5010000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1680000000000], [2010000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5430000000000], [6285000000000]) (some (0, 2, 5))
    (some (0, 3, 5)) (.next ([-5010000000000], [5760000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-4770000000000], [4860000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.terminal (some
    (0, 3, 5)) (some (0, 3, 5)) (some (0, 3, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner0Part0 : FanWitness := (.next ([-5175000000000], [7080000000000]) (some (14, 7, 11))
    (some (14, 7, 11)) (.next ([-6975000000000], [9495000000000]) (some (14, 7, 11)) (some (14, 7,
    11)) (.next ([-4635000000000], [6225000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-5250000000000], [6975000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-4920000000000], [6510000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-4605000000000], [6090000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-345000000000], [450000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-4890000000000], [6375000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-1755000000000], [2220000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-5758200000000, -2160000000000], [7241400000000, 4320000000000]) (some (14, 7, 11)) (some (14,
    7, 11)) (.next ([-5385000000000], [6765000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-5355000000000], [6630000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-5833200000000, -2160000000000], [7136400000000, 4320000000000]) (some (14, 7, 11)) (some (14,
    7, 11)) (.next ([-1590000000000], [1935000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-1680000000000], [1965000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-5968200000000, -2160000000000], [6926400000000, 4320000000000]) (some (14, 7, 11)) (some (14,
    7, 11)) (.next ([-5938200000000, -2160000000000], [6791400000000, 4320000000000]) (some (14, 7,
    11)) (some (14, 7, 11)) (.next ([-1631400000000, -4320000000000], [1798200000000,
    2160000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next ([-6360000000000], [6885000000000])
    (some (14, 7, 11)) (some (14, 7, 11)) (.next ([-6390000000000], [6825000000000]) (some (14, 7,
    11)) (some (14, 7, 11)) (.next ([-6435000000000], [6780000000000]) (some (14, 7, 11)) (some (14,
    7, 11)) (.next ([-6465000000000], [6720000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-1590000000000], [1650000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next
    ([-6390000000000], [6540000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.terminal (some (14,
    7, 11)) (some (14, 7, 11)) (some (14, 7, 11)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner0Part1 : FanWitness := (.next ([-210000000000], [465000000000]) (some (14, 5, 9))
    (some (14, 5, 9)) (.next ([-720000000000], [1560000000000]) (some (14, 5, 9)) (some (14, 5, 9))
    (.next ([-1125000000000], [2400000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-405000000000], [840000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-1215000000000],
    [2430000000000]) (some (14, 5, 9)) (some (14, 6, 9)) (.next ([-701400000000, -4320000000000],
    [1333200000000, 2160000000000]) (some (14, 6, 9)) (some (14, 6, 9)) (.next ([-1620000000000],
    [2865000000000]) (some (14, 6, 9)) (some (14, 6, 9)) (.next ([-105000000000], [180000000000])
    (some (14, 6, 9)) (some (14, 6, 9)) (.next ([-315000000000], [525000000000]) (some (14, 6, 9))
    (some (14, 6, 10)) (.next ([-210000000000], [345000000000]) (some (14, 6, 10)) (some (14, 6,
    10)) (.next ([-1500000000000], [2430000000000]) (some (14, 6, 10)) (some (14, 6, 11)) (.next
    ([-1380000000000], [2190000000000]) (some (14, 6, 11)) (some (14, 6, 11)) (.next
    ([-1470000000000], [2220000000000]) (some (14, 6, 11)) (some (14, 6, 11)) (.next
    ([-60000000000], [90000000000]) (some (14, 6, 11)) (some (14, 6, 11)) (.next ([-2085000000000],
    [3120000000000]) (some (14, 6, 11)) (some (14, 7, 11)) (.next ([-4425000000000],
    [6540000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next ([-6795000000000],
    [9945000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next ([-4710000000000],
    [6825000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next ([-2370000000000],
    [3405000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next ([-6870000000000],
    [9840000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next ([-4500000000000],
    [6435000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next ([-4785000000000],
    [6720000000000]) (some (14, 7, 11)) (some (14, 7, 11)) (.next ([-450000000000], [630000000000])
    (some (14, 7, 11)) (some (14, 7, 11)) (.next ([-7005000000000], [9630000000000]) (some (14, 7,
    11)) (some (14, 7, 11)) fan27Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner0Part2 : FanWitness := (.next ([-405000000000], [3405000000000]) (some (14, 14, 9))
    (some (14, 14, 9)) (.next ([-405000000000], [3120000000000]) (some (14, 5, 9)) (some (14, 5, 9))
    (.next ([-810000000000], [6195000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-840000000000], [6135000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-195000000000],
    [1380000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-435000000000], [3060000000000])
    (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-840000000000], [5850000000000]) (some (14, 5, 9))
    (some (14, 5, 9)) (.next ([-285000000000], [1965000000000]) (some (14, 5, 9)) (some (14, 5, 9))
    (.next ([-915000000000], [6165000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-945000000000], [6105000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-945000000000],
    [5820000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-255000000000], [1470000000000])
    (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-810000000000], [4245000000000]) (some (14, 5, 9))
    (some (14, 5, 9)) (.next ([-870000000000], [4335000000000]) (some (14, 5, 9)) (some (14, 5, 9))
    (.next ([-30000000000], [135000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-1155000000000], [4620000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-210000000000],
    [750000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-540000000000], [1755000000000])
    (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-375000000000], [1185000000000]) (some (14, 5, 9))
    (some (14, 5, 9)) (.next ([-435000000000], [1275000000000]) (some (14, 5, 9)) (some (14, 5, 9))
    (.next ([-840000000000], [2400000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-405000000000], [1125000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next ([-1036800000000,
    2160000000000], [2703600000000, -4320000000000]) (some (14, 5, 9)) (some (14, 5, 9)) (.next
    ([-416400000000, -4320000000000], [1048200000000, 2160000000000]) (some (14, 5, 9)) (some (14,
    5, 9)) fan27Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner0Part3 : FanWitness := (.next ([285000000000], [1680000000000]) (some (14, 14, 9))
    (some (14, 14, 9)) (.next ([958200000000, 2160000000000], [5968200000000, 2160000000000]) (some
    (14, 14, 9)) (some (14, 14, 9)) (.next ([853200000000, 2160000000000], [5938200000000,
    2160000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next ([166800000000, -2160000000000],
    [1631400000000, 4320000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next ([525000000000],
    [6360000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next ([435000000000], [6390000000000])
    (some (14, 14, 9)) (some (14, 14, 9)) (.next ([345000000000], [6435000000000]) (some (14, 14,
    9)) (some (14, 14, 9)) (.next ([255000000000], [6465000000000]) (some (14, 14, 9)) (some (14,
    14, 9)) (.next ([60000000000], [1590000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next
    ([150000000000], [6390000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next ([0],
    [1680000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next ([-30000000000], [6465000000000])
    (some (14, 14, 9)) (some (14, 14, 9)) (.next ([-90000000000], [6600000000000]) (some (14, 14,
    9)) (some (14, 14, 9)) (.next ([-105000000000], [6540000000000]) (some (14, 14, 9)) (some (14,
    14, 9)) (.next ([-195000000000], [6570000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next
    ([-285000000000], [5985000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next
    ([-315000000000], [5925000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next
    ([-315000000000], [5640000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next
    ([-375000000000], [6600000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next ([-118200000000,
    -2160000000000], [1916400000000, 4320000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next
    ([-480000000000], [6570000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next
    ([-465000000000], [6060000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next
    ([-495000000000], [6000000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next
    ([-495000000000], [5715000000000]) (some (14, 14, 9)) (some (14, 14, 9))
    fan27Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner0Part4 : FanWitness := (.next ([1035000000000], [2085000000000]) (some (12, 14, 9))
    (some (12, 14, 9)) (.next ([2115000000000], [4425000000000]) (some (12, 14, 9)) (some (12, 14,
    9)) (.next ([3150000000000], [6795000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next
    ([2115000000000], [4710000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next
    ([1035000000000], [2370000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next
    ([2970000000000], [6870000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next
    ([1935000000000], [4500000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next
    ([1935000000000], [4785000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next ([180000000000],
    [450000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next ([2625000000000], [7005000000000])
    (some (12, 14, 9)) (some (12, 14, 9)) (.next ([1905000000000], [5175000000000]) (some (12, 14,
    9)) (some (12, 14, 9)) (.next ([2520000000000], [6975000000000]) (some (12, 14, 9)) (some (12,
    14, 9)) (.next ([1590000000000], [4635000000000]) (some (12, 14, 9)) (some (14, 14, 9)) (.next
    ([1725000000000], [5250000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next
    ([1590000000000], [4920000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next
    ([1485000000000], [4605000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next ([105000000000],
    [345000000000]) (some (14, 14, 9)) (some (14, 14, 9)) (.next ([1485000000000], [4890000000000])
    (some (14, 14, 9)) (some (14, 14, 9)) (.next ([465000000000], [1755000000000]) (some (14, 14,
    9)) (some (14, 14, 9)) (.next ([1483200000000, 2160000000000], [5758200000000, 2160000000000])
    (some (14, 14, 9)) (some (14, 14, 9)) (.next ([1380000000000], [5385000000000]) (some (14, 14,
    9)) (some (14, 14, 9)) (.next ([1275000000000], [5355000000000]) (some (14, 14, 9)) (some (14,
    14, 9)) (.next ([1303200000000, 2160000000000], [5833200000000, 2160000000000]) (some (14, 14,
    9)) (some (14, 14, 9)) (.next ([345000000000], [1590000000000]) (some (14, 14, 9)) (some (14,
    14, 9)) fan27Owner0Part3))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner0Part5 : FanWitness := (.next ([105000000000], [30000000000]) (some (11, 14, 9)) (some
    (11, 14, 9)) (.next ([3465000000000], [1155000000000]) (some (11, 14, 9)) (some (12, 14, 9))
    (.next ([540000000000], [210000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next
    ([1215000000000], [540000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next ([810000000000],
    [375000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next ([840000000000], [435000000000])
    (some (12, 14, 9)) (some (12, 14, 9)) (.next ([1560000000000], [840000000000]) (some (12, 14,
    9)) (some (12, 14, 9)) (.next ([720000000000], [405000000000]) (some (12, 14, 9)) (some (12, 14,
    9)) (.next ([1666800000000, -2160000000000], [1036800000000, -2160000000000]) (some (12, 14, 9))
    (some (12, 14, 9)) (.next ([631800000000, -2160000000000], [416400000000, 4320000000000]) (some
    (12, 14, 9)) (some (12, 14, 9)) (.next ([255000000000], [210000000000]) (some (12, 14, 9)) (some
    (12, 14, 9)) (.next ([840000000000], [720000000000]) (some (12, 14, 9)) (some (12, 14, 9))
    (.next ([1275000000000], [1125000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next
    ([435000000000], [405000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next ([1215000000000],
    [1215000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next ([631800000000, -2160000000000],
    [701400000000, 4320000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next ([1245000000000],
    [1620000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next ([75000000000], [105000000000])
    (some (12, 14, 9)) (some (12, 14, 9)) (.next ([210000000000], [315000000000]) (some (12, 14, 9))
    (some (12, 14, 9)) (.next ([135000000000], [210000000000]) (some (12, 14, 9)) (some (12, 14, 9))
    (.next ([930000000000], [1500000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next
    ([810000000000], [1380000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next ([750000000000],
    [1470000000000]) (some (12, 14, 9)) (some (12, 14, 9)) (.next ([30000000000], [60000000000])
    (some (12, 14, 9)) (some (12, 14, 9)) fan27Owner0Part4))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner0Part6 : FanWitness := (.next ([6375000000000], [195000000000]) (some (11, 14, 8))
    (some (11, 14, 8)) (.next ([5700000000000], [285000000000]) (some (11, 14, 8)) (some (11, 14,
    8)) (.next ([5610000000000], [315000000000]) (some (11, 14, 8)) (some (11, 14, 8)) (.next
    ([5325000000000], [315000000000]) (some (11, 14, 8)) (some (11, 14, 8)) (.next ([6225000000000],
    [375000000000]) (some (11, 14, 8)) (some (11, 14, 9)) (.next ([1798200000000, 2160000000000],
    [118200000000, 2160000000000]) (some (11, 14, 9)) (some (11, 14, 9)) (.next ([6090000000000],
    [480000000000]) (some (11, 14, 9)) (some (11, 14, 9)) (.next ([5595000000000], [465000000000])
    (some (11, 14, 9)) (some (11, 14, 9)) (.next ([5505000000000], [495000000000]) (some (11, 14,
    9)) (some (11, 14, 9)) (.next ([5220000000000], [495000000000]) (some (11, 14, 9)) (some (11,
    14, 9)) (.next ([3000000000000], [405000000000]) (some (11, 14, 9)) (some (11, 14, 9)) (.next
    ([2715000000000], [405000000000]) (some (11, 14, 9)) (some (11, 14, 9)) (.next ([5385000000000],
    [810000000000]) (some (11, 14, 9)) (some (11, 14, 9)) (.next ([5295000000000], [840000000000])
    (some (11, 14, 9)) (some (11, 14, 9)) (.next ([1185000000000], [195000000000]) (some (11, 14,
    9)) (some (11, 14, 9)) (.next ([2625000000000], [435000000000]) (some (11, 14, 9)) (some (11,
    14, 9)) (.next ([5010000000000], [840000000000]) (some (11, 14, 9)) (some (11, 14, 9)) (.next
    ([1680000000000], [285000000000]) (some (11, 14, 9)) (some (11, 14, 9)) (.next ([5250000000000],
    [915000000000]) (some (11, 14, 9)) (some (11, 14, 9)) (.next ([5160000000000], [945000000000])
    (some (11, 14, 9)) (some (11, 14, 9)) (.next ([4875000000000], [945000000000]) (some (11, 14,
    9)) (some (11, 14, 9)) (.next ([1215000000000], [255000000000]) (some (11, 14, 9)) (some (11,
    14, 9)) (.next ([3435000000000], [810000000000]) (some (11, 14, 9)) (some (11, 14, 9)) (.next
    ([3465000000000], [870000000000]) (some (11, 14, 9)) (some (11, 14, 9))
    fan27Owner0Part5))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner4Part0 : FanWitness := (.next ([2070000000000, -9000000000000], [2790000000000,
    9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1860000000000], [2805000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1620000000000], [5130000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([540000000000], [1995000000000]) (some (5, 1, 6)) (some (5, 1, 6))
    (.next ([855000000000], [5430000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0],
    [2430000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-15000000000],
    [2805000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-375000000000], [7665000000000])
    (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-360000000000], [4860000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-270000000000], [2250000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-810000000000, -9000000000000], [5130000000000, 0]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-1275000000000], [6750000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1005000000000], [4500000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-930000000000],
    [2790000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2805000000000, -9000000000000],
    [7665000000000, 0]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-810000000000], [2130000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2430000000000, -9000000000000], [6285000000000,
    9000000000000]) (some (0, 2, 6)) (some (0, 3, 6)) (.next ([-3810000000000], [7290000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-3000000000000], [5430000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-2790000000000, -9000000000000], [4860000000000, 0]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-2805000000000], [4665000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-5130000000000], [6750000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-1995000000000], [2535000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-5430000000000],
    [6285000000000]) (some (0, 3, 5)) (some (0, 6, 5)) (.terminal (some (0, 6, 5)) (some (0, 6, 5))
    (some (0, 6, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner4Part0 : FanWitness := (.next ([1110000000000], [2580000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([1620000000000], [5130000000000]) (some (5, 1, 6)) (some (5, 1, 6))
    (.next ([855000000000], [5430000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([750000000000], [7440000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0],
    [2430000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, -9000000000000],
    [3000000000000, 0]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-360000000000], [4860000000000])
    (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-270000000000], [2250000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-810000000000, -9000000000000], [5130000000000, 0]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-1275000000000], [6750000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-1005000000000], [4500000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1680000000000, -9000000000000], [7440000000000, 0]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-930000000000], [2790000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-870000000000],
    [2310000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1680000000000], [4440000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-810000000000], [2130000000000]) (some (0, 2, 6))
    (some (0, 6, 6)) (.next ([-2430000000000, -9000000000000], [6285000000000, 9000000000000]) (some
    (0, 6, 6)) (some (0, 6, 6)) (.next ([-3585000000000], [8190000000000]) (some (0, 6, 6)) (some
    (0, 6, 6)) (.next ([-3000000000000], [5430000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-2790000000000, -9000000000000], [4860000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-2580000000000], [3690000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-5130000000000],
    [6750000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-5430000000000], [6285000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-7440000000000], [8190000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.terminal (some (0, 6, 5)) (some (0, 6, 5)) (some (0, 6,
    5)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 14) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 3)) (some (5, 1, 3)) (.next ([4500000000000], [360000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4860000000000, 9000000000000], [570000000000,
      -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1110000000000], [150000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3990000000000], [1185000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([2880000000000], [1035000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([3825000000000, 0], [1845000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([3330000000000, -9000000000000], [1680000000000, 9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([2205000000000], [1620000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([4050000000000], [3000000000000]) (some (5, 1, 3)) (some (7, 1, 3)) (.next
      ([3180000000000, 9000000000000], [2580000000000, -9000000000000]) (some (7, 1, 3)) (some (7,
      1, 3)) (.next ([2430000000000, 9000000000000], [2430000000000, 9000000000000]) (some (7, 1,
      3)) (some (7, 1, 3)) (.next ([2070000000000, 9000000000000], [2430000000000, -9000000000000])
      (some (7, 1, 3)) (some (7, 1, 3)) (.next ([2430000000000], [3000000000000]) (some (7, 1, 3))
      (some (7, 1, 3)) (.next ([2070000000000, -9000000000000], [2790000000000, 9000000000000])
      (some (7, 1, 3)) (some (7, 1, 3)) (.next ([2370000000000], [5010000000000]) (some (7, 1, 3))
      (some (7, 1, 3)) (.next ([1260000000000], [4860000000000]) (some (7, 1, 3)) (some (7, 1, 3))
      (.next ([330000000000], [1680000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
      ([585000000000], [3240000000000]) (some (7, 1, 3)) (some (7, 1, 3))
      fan24Owner4Part0)))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
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
  apply ExclusionHint.sound (.pair 9 14) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5001000000000], [2055000000000, 9000000000000])
      (some (2, 4, 2)) (some (3, 4, 2)) (.next ([5190000000000], [2430000000000, 9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([5001000000000], [4770000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([5190000000000], [5145000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([189000000000], [375000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([375000000000], [4626000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [2430000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-2055000000000,
      -9000000000000], [7056000000000, 9000000000000]) (some (0, 4, 2)) (some (4, 4, 2)) (.next
      ([-2430000000000, -9000000000000], [7620000000000, 9000000000000]) (some (4, 4, 2)) (some (4,
      4, 2)) (.next ([-4770000000000], [9771000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([-5145000000000], [10335000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-375000000000], [564000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-4626000000000],
      [5001000000000]) (some (4, 1, 2)) (some (4, 2, 2)) (.terminal (some (4, 2, 2)) (some (4, 2,
      2)) (some (4, 2, 2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5175000000000], [2205000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([5145000000000], [3855000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1620000000000], [2235000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1320000000000], [3825000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [7380000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2205000000000], [7380000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3855000000000], [9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-2235000000000], [3855000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-3825000000000], [5145000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_9 : ExcludedOn (model25.B 9 ++ [step25.q]) 9000000000000 (model25.caps 9)
    (model25.ord 9) 0 1 100 := by
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
  apply ExclusionHint.sound (.pair 9 14) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 3)) (some (5, 6, 3)) (.next ([4500000000000], [360000000000])
      (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1110000000000], [150000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) (.next ([4605000000000], [1155000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      (.next ([3495000000000], [1005000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([1860000000000], [930000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([3330000000000,
      -9000000000000], [1680000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([3855000000000, 0], [2430000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([3855000000000], [4410000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2430000000000],
      [3000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2070000000000, -9000000000000],
      [2790000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) fan26Owner4Part0))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded26_1
    · exact excluded26_2
    · exact excluded26_3
    · exact excluded26_4
    · exact (hj rfl).elim
    · exact excluded26_6
    · exact excluded26_7
    · exact excluded26_8
    · exact excluded26_9
theorem next26 : model26.insert step26 = model27 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded27_0 : ExcludedOn (model27.B 0 ++ [step27.q]) 9000000000000 (model27.caps 0)
    (model27.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6435000000000], [30000000000]) (some (11, 14,
      7)) (some (11, 14, 8)) (.next ([6510000000000], [90000000000]) (some (11, 14, 8)) (some (11,
      14, 8)) (.next ([6435000000000], [105000000000]) (some (11, 14, 8)) (some (11, 14, 8))
      fan27Owner0Part6))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4590000000000], [1890000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([5130000000000], [2250000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([4590000000000, 0], [2430000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([4050000000000, -9000000000000], [2430000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([2340000000000], [2790000000000]) (some (4, 1, 2)) (some (4, 1, 3))
      (.next ([900000000000], [1350000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([2700000000000, -9000000000000], [4680000000000, 9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([0], [4590000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1890000000000], [6480000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next
      ([-2250000000000], [7380000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2430000000000,
      -9000000000000], [7020000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-2430000000000, -9000000000000], [6480000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-2790000000000], [5130000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-1350000000000], [2250000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4680000000000,
      -9000000000000], [7380000000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6195000000000, -9000000000000], [1095000000000,
      9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([6525000000000], [2100000000000])
      (some (3, 0, 4)) (some (3, 4, 4)) (.next ([5961000000000], [2289000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([5001000000000], [2055000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([5190000000000], [2430000000000, 9000000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([189000000000], [375000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([1335000000000], [7290000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([375000000000], [4626000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [2430000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-1095000000000,
      -9000000000000], [7290000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2100000000000],
      [8625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2289000000000], [8250000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2055000000000, -9000000000000], [7056000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2430000000000, -9000000000000],
      [7620000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-375000000000],
      [564000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-7290000000000], [8625000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4626000000000], [5001000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4,
      2))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2790000000000], [15000000000]) (some (5, 0, 6))
      (some (5, 1, 6)) (.next ([7290000000000], [375000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([4500000000000], [360000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([1980000000000], [270000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4320000000000,
      -9000000000000], [810000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([5475000000000], [1275000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3495000000000],
      [1005000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1860000000000], [930000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4860000000000, -9000000000000], [2805000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1320000000000], [810000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3855000000000, 0], [2430000000000, 9000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3480000000000], [3810000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([2430000000000], [3000000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan28Owner4Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7665000000000], [1710000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([4590000000000], [1890000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([4590000000000, 0], [2430000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([4050000000000, -9000000000000], [2430000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([5235000000000, -9000000000000], [4140000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([1185000000000], [1710000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([2880000000000], [4785000000000]) (some (4, 1, 3)) (some (4, 1, 4))
      (.next ([0], [4590000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1710000000000],
      [9375000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1890000000000], [6480000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2430000000000, -9000000000000], [7020000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2430000000000, -9000000000000],
      [6480000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4140000000000, -9000000000000],
      [9375000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1710000000000], [2895000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4785000000000], [7665000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
      4))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 6)) (some (5, 1, 6)) (.next ([4500000000000], [360000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1980000000000], [270000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([4320000000000, -9000000000000], [810000000000, 9000000000000]) (some
      (5, 1, 6)) (some (5, 1, 6)) (.next ([5475000000000], [1275000000000]) (some (5, 1, 6)) (some
      (5, 1, 6)) (.next ([3495000000000], [1005000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([5760000000000, -9000000000000], [1680000000000, 9000000000000]) (some (5, 1, 6)) (some (5,
      1, 6)) (.next ([1860000000000], [930000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([1440000000000], [870000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2760000000000],
      [1680000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1320000000000], [810000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3855000000000, 0], [2430000000000, 9000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4605000000000], [3585000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([2430000000000], [3000000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([2070000000000, -9000000000000], [2790000000000, 9000000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) fan29Owner4Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7440000000000], [810000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([4590000000000], [1890000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4590000000000, 0], [2430000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4050000000000, -9000000000000], [2430000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([5010000000000, -9000000000000], [3240000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([960000000000], [810000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([3780000000000], [3660000000000]) (some (4, 1, 3)) (some (4, 1, 4))
      (.next ([0], [4590000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-810000000000],
      [8250000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1890000000000], [6480000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2430000000000, -9000000000000], [7020000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2430000000000, -9000000000000],
      [6480000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3240000000000, -9000000000000],
      [8250000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-810000000000], [1770000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3660000000000], [7440000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
      4))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded30_0 : ExcludedOn (model30.B 0 ++ [step30.q]) 9000000000000 (model30.caps 0)
    (model30.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 8 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_4 : ExcludedOn (model30.B 4 ++ [step30.q]) 9000000000000 (model30.caps 4)
    (model30.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6750000000000], [180000000000, 9000000000000])
      (some (0, 5, 2)) (some (0, 5, 3)) (.next ([4374000000000], [375000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([4626000000000], [1749000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([2250000000000, 0], [2070000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([2430000000000, 9000000000000], [2430000000000, 9000000000000]) (some (0, 1, 3)) (some
      (0, 1, 3)) (.next ([2001000000000], [2124000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1944000000000, -9000000000000], [2805000000000, 9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([2196000000000, -9000000000000], [4179000000000, 9000000000000]) (some (0, 1,
      3)) (some (0, 1, 3)) (.next ([681000000000, 9000000000000], [3945000000000, -9000000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([375000000000], [2376000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([0, 0], [2430000000000, 9000000000000]) (some (0, 1, 3)) (some (5, 1,
      3)) (.next ([-180000000000, -9000000000000], [6930000000000, 9000000000000]) (some (5, 1, 3))
      (some (5, 2, 3)) (.next ([-375000000000], [4749000000000]) (some (5, 2, 3)) (some (5, 2, 3))
      (.next ([-1749000000000], [6375000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-2070000000000, 9000000000000], [4320000000000, -9000000000000]) (some (5, 2, 3)) (some (5,
      2, 3)) (.next ([-2430000000000, -9000000000000], [4860000000000, 18000000000000]) (some (5, 2,
      3)) (some (5, 2, 3)) (.next ([-2124000000000], [4125000000000]) (some (5, 2, 3)) (some (5, 2,
      3)) (.next ([-2805000000000, -9000000000000], [4749000000000]) (some (5, 2, 3)) (some (5, 2,
      3)) (.next ([-4179000000000, -9000000000000], [6375000000000]) (some (5, 2, 3)) (some (5, 2,
      4)) (.next ([-3945000000000, 9000000000000], [4626000000000]) (some (5, 2, 4)) (some (5, 2,
      4)) (.next ([-2376000000000], [2751000000000]) (some (5, 2, 4)) (some (5, 2, 0)) (.terminal
      (some (5, 2, 0)) (some (5, 2, 0)) (some (5, 2, 0))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 8 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2070000000000, -9000000000000], [180000000000,
      9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next ([4590000000000], [1890000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4590000000000, 0], [2430000000000, 9000000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([4050000000000, -9000000000000], [2430000000000,
      9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2250000000000], [2250000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([1980000000000], [2250000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([2610000000000], [4140000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([2340000000000], [4500000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([360000000000], [1890000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([450000000000],
      [6750000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([180000000000, -9000000000000],
      [4140000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [4590000000000]) (some (0, 1,
      5)) (some (0, 1, 5)) (.next ([-180000000000, -9000000000000], [2250000000000]) (some (0, 1,
      5)) (some (0, 2, 5)) (.next ([-1890000000000], [6480000000000]) (some (0, 2, 5)) (some (0, 2,
      4)) (.next ([-2430000000000, -9000000000000], [7020000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2430000000000, -9000000000000], [6480000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2250000000000], [4500000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-2250000000000], [4230000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-4140000000000], [6750000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-4500000000000], [6840000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-1890000000000], [2250000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6750000000000], [7200000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4140000000000,
      0], [4320000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 5, 4)) (some (0, 5, 4))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem excluded31_9 : ExcludedOn (model31.B 9 ++ [step31.q]) 9000000000000 (model31.caps 9)
    (model31.ord 9) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded31_7
    · exact excluded31_8
    · exact excluded31_9
theorem next31 : model31.insert step31 = model32 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint270000280000
end ConwaySoifer.Simplified.Certificates
