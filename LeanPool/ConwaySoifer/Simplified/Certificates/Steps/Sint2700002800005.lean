/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint270000280000
import Mathlib.Tactic.FinCases

/-!
# Sint 270000 280000 5

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
def fan40Owner0Part0 : FanWitness := (.next ([-5385000000000], [7695000000000]) (some (12, 5, 10))
    (some (12, 6, 10)) (.next ([-1095000000000], [1560000000000]) (some (12, 6, 10)) (some (12, 6,
    10)) (.next ([-5355000000000], [7560000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-450000000000], [630000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-1035000000000], [1440000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-2310000000000], [3120000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-2400000000000], [3150000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-345000000000], [450000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6960000000000], [9075000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-5925000000000], [7635000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-7035000000000], [8970000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6000000000000], [7530000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-7170000000000], [8760000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-7140000000000], [8625000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6135000000000], [7320000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6105000000000], [7185000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-2685000000000], [3150000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-345000000000], [375000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6360000000000], [6885000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6390000000000], [6825000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6435000000000], [6780000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6465000000000], [6720000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-1935000000000], [1995000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6390000000000], [6540000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.terminal (some (12,
    6, 10)) (some (12, 6, 10)) (some (12, 6, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner0Part1 : FanWitness := (.next ([-975000000000], [3375000000000]) (some (0, 4, 8))
    (some (0, 4, 8)) (.next ([-1035000000000], [3465000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    (.next ([-375000000000], [1185000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([-375000000000], [1125000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-435000000000],
    [1275000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-1320000000000], [3750000000000])
    (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-405000000000], [1125000000000]) (some (0, 4, 8))
    (some (0, 4, 8)) (.next ([-465000000000], [1215000000000]) (some (0, 4, 8)) (some (0, 4, 8))
    (.next ([-720000000000], [1785000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next
    ([-720000000000], [1560000000000]) (some (0, 4, 8)) (some (12, 4, 8)) (.next ([-405000000000],
    [840000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([-1125000000000], [2310000000000])
    (some (12, 4, 8)) (some (12, 5, 8)) (.next ([-1185000000000], [2400000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([-750000000000], [1500000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([-1470000000000], [2685000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([-105000000000], [180000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-315000000000],
    [525000000000]) (some (12, 5, 8)) (some (12, 5, 9)) (.next ([-210000000000], [345000000000])
    (some (12, 5, 9)) (some (12, 5, 9)) (.next ([-750000000000], [1215000000000]) (some (12, 5, 9))
    (some (12, 5, 10)) (.next ([-750000000000], [1185000000000]) (some (12, 5, 10)) (some (12, 5,
    10)) (.next ([-810000000000], [1275000000000]) (some (12, 5, 10)) (some (12, 5, 10)) (.next
    ([-5175000000000], [8010000000000]) (some (12, 5, 10)) (some (12, 5, 10)) (.next
    ([-5250000000000], [7905000000000]) (some (12, 5, 10)) (some (12, 5, 10)) (.next
    ([-60000000000], [90000000000]) (some (12, 5, 10)) (some (12, 5, 10))
    fan40Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner0Part2 : FanWitness := (.next ([0], [2025000000000]) (some (0, 12, 8)) (some (0, 12,
    8)) (.next ([-30000000000], [6465000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([-90000000000], [6600000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-105000000000],
    [6540000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-195000000000], [6570000000000])
    (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-285000000000], [5985000000000]) (some (0, 12, 8))
    (some (0, 12, 8)) (.next ([-315000000000], [5925000000000]) (some (0, 12, 8)) (some (0, 12, 8))
    (.next ([-315000000000], [5640000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([-375000000000], [6600000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-480000000000],
    [6570000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-465000000000], [6060000000000])
    (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-495000000000], [6000000000000]) (some (0, 12, 8))
    (some (0, 12, 8)) (.next ([-495000000000], [5715000000000]) (some (0, 12, 8)) (some (0, 12, 8))
    (.next ([-285000000000], [2310000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([-810000000000], [6195000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-840000000000],
    [6135000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-840000000000], [5850000000000])
    (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-915000000000], [6165000000000]) (some (0, 12, 8))
    (some (0, 12, 8)) (.next ([-945000000000], [6105000000000]) (some (0, 12, 8)) (some (0, 12, 8))
    (.next ([-945000000000], [5820000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([-30000000000], [135000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-570000000000],
    [2535000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-570000000000], [2250000000000])
    (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-600000000000], [2190000000000]) (some (0, 4, 8))
    (some (0, 4, 8)) fan40Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner0Part3 : FanWitness := (.next ([2310000000000], [5385000000000]) (some (11, 12, 8))
    (some (11, 12, 8)) (.next ([465000000000], [1095000000000]) (some (11, 12, 8)) (some (11, 12,
    8)) (.next ([2205000000000], [5355000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next
    ([180000000000], [450000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([405000000000],
    [1035000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([810000000000], [2310000000000])
    (some (0, 12, 8)) (some (0, 12, 8)) (.next ([750000000000], [2400000000000]) (some (0, 12, 8))
    (some (0, 12, 8)) (.next ([105000000000], [345000000000]) (some (0, 12, 8)) (some (0, 12, 8))
    (.next ([2115000000000], [6960000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([1710000000000], [5925000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([1935000000000],
    [7035000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([1530000000000], [6000000000000])
    (some (0, 12, 8)) (some (0, 12, 8)) (.next ([1590000000000], [7170000000000]) (some (0, 12, 8))
    (some (0, 12, 8)) (.next ([1485000000000], [7140000000000]) (some (0, 12, 8)) (some (0, 12, 8))
    (.next ([1185000000000], [6135000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([1080000000000], [6105000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([465000000000],
    [2685000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([30000000000], [345000000000])
    (some (0, 12, 8)) (some (0, 12, 8)) (.next ([525000000000], [6360000000000]) (some (0, 12, 8))
    (some (0, 12, 8)) (.next ([435000000000], [6390000000000]) (some (0, 12, 8)) (some (0, 12, 8))
    (.next ([345000000000], [6435000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([255000000000], [6465000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([60000000000],
    [1935000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([150000000000], [6390000000000])
    (some (0, 12, 8)) (some (0, 12, 8)) fan40Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner0Part4 : FanWitness := (.next ([2400000000000], [975000000000]) (some (11, 12, 8))
    (some (11, 12, 8)) (.next ([2430000000000], [1035000000000]) (some (11, 12, 8)) (some (11, 12,
    8)) (.next ([810000000000], [375000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next
    ([750000000000], [375000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next ([840000000000],
    [435000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next ([2430000000000], [1320000000000])
    (some (11, 12, 8)) (some (11, 12, 8)) (.next ([720000000000], [405000000000]) (some (11, 12, 8))
    (some (11, 12, 8)) (.next ([750000000000], [465000000000]) (some (11, 12, 8)) (some (11, 12, 8))
    (.next ([1065000000000], [720000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next
    ([840000000000], [720000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next ([435000000000],
    [405000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next ([1185000000000], [1125000000000])
    (some (11, 12, 8)) (some (11, 12, 8)) (.next ([1215000000000], [1185000000000]) (some (11, 12,
    8)) (some (11, 12, 8)) (.next ([750000000000], [750000000000]) (some (11, 12, 8)) (some (11, 12,
    8)) (.next ([1215000000000], [1470000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next
    ([75000000000], [105000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next ([210000000000],
    [315000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next ([135000000000], [210000000000])
    (some (11, 12, 8)) (some (11, 12, 8)) (.next ([465000000000], [750000000000]) (some (11, 12, 8))
    (some (11, 12, 8)) (.next ([435000000000], [750000000000]) (some (11, 12, 8)) (some (11, 12, 8))
    (.next ([465000000000], [810000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next
    ([2835000000000], [5175000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next
    ([2655000000000], [5250000000000]) (some (11, 12, 8)) (some (11, 12, 8)) (.next ([30000000000],
    [60000000000]) (some (11, 12, 8)) (some (11, 12, 8)) fan40Owner0Part3))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner5Part0 : FanWitness := (.next ([6000000000000], [1215000000000]) (some (5, 1, 2))
    (some (5, 1, 3)) (.next ([4635000000000], [1845000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([4635000000000, 0], [2430000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([4050000000000, -9000000000000], [2430000000000, 9000000000000]) (some (5, 1, 3)) (some
    (5, 1, 3)) (.next ([735000000000], [480000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([3420000000000], [2580000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2250000000000],
    [2250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3570000000000, -9000000000000],
    [3645000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1980000000000],
    [2250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2385000000000], [4500000000000])
    (some (0, 1, 3)) (some (0, 1, 4)) (.next ([1500000000000], [3465000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([0], [4635000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-180000000000, -9000000000000], [2250000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next
    ([-1215000000000], [7215000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1845000000000],
    [6480000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2430000000000, -9000000000000],
    [7065000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2430000000000,
    -9000000000000], [6480000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-480000000000],
    [1215000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2580000000000], [6000000000000])
    (some (0, 2, 4)) (some (0, 2, 5)) (.next ([-2250000000000], [4500000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-3645000000000, -9000000000000], [7215000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-2250000000000], [4230000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-4500000000000], [6885000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-3465000000000], [4965000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
    5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner4Part0 : FanWitness := (.next ([645000000000], [645000000000]) (some (5, 1, 6)) (some
    (5, 1, 6)) (.next ([2430000000000], [4125000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([2265000000000], [4860000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1785000000000],
    [6000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1140000000000], [7290000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0], [2430000000000, 9000000000000]) (some (5, 1,
    6)) (some (5, 1, 6)) (.next ([0, -9000000000000], [4125000000000, 0]) (some (0, 1, 6)) (some (0,
    1, 6)) (.next ([-270000000000], [6555000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next
    ([-645000000000, -9000000000000], [6000000000000, 0]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1005000000000], [7125000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1290000000000,
    -9000000000000], [7290000000000, 0]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-165000000000],
    [735000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2145000000000], [7785000000000])
    (some (0, 2, 6)) (some (0, 3, 6)) (.next ([-645000000000], [1875000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-2430000000000, -9000000000000], [6285000000000, 9000000000000]) (some
    (0, 3, 6)) (some (0, 3, 6)) (.next ([-3435000000000], [8430000000000]) (some (0, 3, 6)) (some
    (0, 3, 6)) (.next ([-1290000000000], [3165000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-480000000000], [1140000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1125000000000],
    [2430000000000]) (some (0, 3, 5)) (some (0, 4, 5)) (.next ([-645000000000], [1290000000000])
    (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-4125000000000], [6555000000000]) (some (0, 4, 5))
    (some (0, 6, 5)) (.next ([-4860000000000], [7125000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-6000000000000], [7785000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-7290000000000], [8430000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.terminal (some (0, 6,
    5)) (some (0, 6, 5)) (some (0, 6, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner5Part0 : FanWitness := (.next ([2070000000000, -9000000000000], [180000000000,
    9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4635000000000], [1845000000000])
    (some (5, 1, 2)) (some (5, 1, 3)) (.next ([4635000000000, 0], [2430000000000, 9000000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4050000000000, -9000000000000], [2430000000000,
    9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4860000000000, -9000000000000],
    [3000000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([810000000000],
    [570000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4065000000000], [3225000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2250000000000], [2250000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([2790000000000], [2820000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([1980000000000], [2250000000000]) (some (0, 1, 3)) (some (0, 1, 5)) (.next
    ([2385000000000], [4500000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0],
    [4635000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-570000000000], [7860000000000])
    (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-180000000000, -9000000000000], [2250000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1845000000000], [6480000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-2430000000000, -9000000000000], [7065000000000, 9000000000000]) (some
    (0, 2, 5)) (some (0, 2, 5)) (.next ([-2430000000000, -9000000000000], [6480000000000]) (some (0,
    2, 5)) (some (0, 2, 5)) (.next ([-3000000000000, -9000000000000], [7860000000000]) (some (0, 2,
    5)) (some (0, 2, 5)) (.next ([-570000000000], [1380000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-3225000000000], [7290000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-2250000000000], [4500000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2820000000000],
    [5610000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2250000000000], [4230000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4500000000000], [6885000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner6Part0 : FanWitness := (.next ([540000000000], [3180000000000]) (some (6, 1, 3)) (some
    (6, 1, 3)) (.next ([720000000000, 9000000000000], [7140000000000, -9000000000000]) (some (6, 1,
    3)) (some (6, 1, 3)) (.next ([180000000000, 9000000000000], [3960000000000, -9000000000000])
    (some (6, 1, 3)) (some (6, 1, 3)) (.next ([15000000000], [486000000000]) (some (6, 1, 3)) (some
    (6, 1, 3)) (.next ([39000000000], [3195000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([0,
    0], [2430000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([-375000000000],
    [4749000000000]) (some (6, 1, 3)) (some (6, 2, 3)) (.next ([-234000000000], [1875000000000])
    (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-1710000000000], [9570000000000]) (some (6, 2, 3))
    (some (6, 2, 3)) (.next ([-1749000000000], [6375000000000]) (some (6, 2, 3)) (some (6, 2, 3))
    (.next ([-1335000000000], [4821000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
    ([-2250000000000], [6390000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-4140000000000,
    -9000000000000], [9570000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-2430000000000,
    -9000000000000], [4860000000000, 18000000000000]) (some (6, 2, 3)) (some (6, 2, 6)) (.next
    ([-2319000000000, 9000000000000], [4374000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next
    ([-2805000000000, -9000000000000], [4749000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next
    ([-4179000000000, -9000000000000], [6375000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next
    ([-4680000000000, -9000000000000], [6390000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next
    ([-3945000000000, 9000000000000], [4626000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next
    ([-3180000000000], [3720000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([-7140000000000,
    9000000000000], [7860000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3960000000000,
    9000000000000], [4140000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-486000000000],
    [501000000000]) (some (0, 2, 6)) (some (1, 2, 6)) (.next ([-3195000000000], [3234000000000])
    (some (1, 2, 6)) (some (1, 2, 6)) (.terminal (some (1, 2, 6)) (some (1, 2, 6)) (some (1, 2,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner3Part0 : FanWitness := (.next ([2730000000000], [3645000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([2730000000000], [4575000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([2625000000000], [4665000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([2625000000000], [5595000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([525000000000],
    [2100000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([300000000000, -9000000000000],
    [6075000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([195000000000,
    -9000000000000], [7095000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([0],
    [2430000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-330000000000],
    [5895000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-435000000000], [6915000000000])
    (some (6, 1, 4)) (some (6, 2, 4)) (.next ([-105000000000], [1020000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-810000000000], [3060000000000]) (some (6, 2, 4)) (some (6, 3, 4))
    (.next ([-2430000000000, -9000000000000], [7620000000000, 9000000000000]) (some (6, 3, 4)) (some
    (6, 3, 4)) (.next ([-930000000000], [2430000000000, 9000000000000]) (some (6, 3, 4)) (some (6,
    3, 4)) (.next ([-3060000000000], [7440000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([-1185000000000], [2730000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-1740000000000],
    [3060000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-3645000000000], [6375000000000])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-4575000000000], [7305000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([-4665000000000], [7290000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([-5595000000000], [8220000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([-2100000000000], [2625000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-6075000000000,
    -9000000000000], [6375000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-7095000000000,
    -9000000000000], [7290000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.terminal (some (0, 3, 4))
    (some (0, 3, 4)) (some (0, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan46Owner4Part0 : FanWitness := (.next ([3255000000000], [4125000000000]) (some (5, 1, 4))
    (some (5, 1, 4)) (.next ([3090000000000], [4860000000000]) (some (5, 1, 4)) (some (5, 1, 4))
    (.next ([2430000000000], [4125000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
    ([2265000000000], [4860000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([2610000000000],
    [6000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([1785000000000], [6000000000000])
    (some (5, 1, 4)) (some (5, 1, 4)) (.next ([825000000000], [3030000000000]) (some (5, 1, 4))
    (some (5, 1, 4)) (.next ([0, 0], [2430000000000, 9000000000000]) (some (5, 1, 4)) (some (6, 1,
    4)) (.next ([0, -9000000000000], [4125000000000, 0]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([-270000000000], [6555000000000]) (some (6, 1, 4)) (some (6, 2, 4)) (.next ([-645000000000,
    -9000000000000], [6000000000000, 0]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-1005000000000],
    [7125000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-165000000000], [735000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-2145000000000], [7785000000000]) (some (6, 2, 4))
    (some (6, 3, 4)) (.next ([-645000000000], [1875000000000]) (some (6, 3, 4)) (some (6, 3, 5))
    (.next ([-2430000000000, -9000000000000], [6285000000000, 9000000000000]) (some (6, 3, 5)) (some
    (6, 3, 5)) (.next ([-480000000000], [1140000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-4125000000000], [7380000000000]) (some (6, 3, 5)) (some (6, 4, 5)) (.next ([-4860000000000],
    [7950000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-4125000000000], [6555000000000])
    (some (6, 4, 5)) (some (6, 4, 5)) (.next ([-4860000000000], [7125000000000]) (some (6, 4, 5))
    (some (6, 4, 5)) (.next ([-6000000000000], [8610000000000]) (some (6, 4, 5)) (some (6, 4, 5))
    (.next ([-6000000000000], [7785000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.next
    ([-3030000000000], [3855000000000]) (some (6, 4, 5)) (some (6, 4, 5)) (.terminal (some (6, 4,
    5)) (some (0, 4, 5)) (some (6, 4, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan47Owner3Part0 : FanWitness := (.next ([5190000000000], [4020000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([810000000000], [960000000000]) (some (5, 6, 3)) (some (5, 6, 3))
    (.next ([2730000000000], [3645000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
    ([2625000000000], [4665000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([525000000000],
    [2100000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([300000000000, -9000000000000],
    [6075000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6, 4)) (.next ([195000000000,
    -9000000000000], [7095000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0],
    [2430000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([-330000000000],
    [5895000000000]) (some (0, 6, 4)) (some (6, 6, 4)) (.next ([-435000000000], [6915000000000])
    (some (6, 6, 4)) (some (6, 6, 4)) (.next ([-105000000000], [1020000000000]) (some (6, 6, 4))
    (some (6, 6, 4)) (.next ([-1395000000000], [8685000000000]) (some (6, 6, 4)) (some (6, 6, 4))
    (.next ([-1290000000000], [7665000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-810000000000], [3060000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-2430000000000,
    -9000000000000], [7620000000000, 9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-3060000000000], [7440000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-1185000000000],
    [2730000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-4020000000000], [9210000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-960000000000], [1770000000000]) (some (6, 3, 4))
    (some (6, 3, 4)) (.next ([-3645000000000], [6375000000000]) (some (6, 3, 4)) (some (6, 3, 4))
    (.next ([-4665000000000], [7290000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-2100000000000], [2625000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-6075000000000,
    -9000000000000], [6375000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-7095000000000,
    -9000000000000], [7290000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.terminal (some (6, 3, 4))
    (some (6, 3, 4)) (some (6, 3, 4)))))))))))))))))))))))))))

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6435000000000], [30000000000]) (some (10, 12,
      6)) (some (10, 12, 7)) (.next ([6510000000000], [90000000000]) (some (10, 12, 7)) (some (10,
      12, 7)) (.next ([6435000000000], [105000000000]) (some (10, 12, 7)) (some (10, 12, 7)) (.next
      ([6375000000000], [195000000000]) (some (10, 12, 7)) (some (10, 12, 7)) (.next
      ([5700000000000], [285000000000]) (some (10, 12, 7)) (some (10, 12, 7)) (.next
      ([5610000000000], [315000000000]) (some (10, 12, 7)) (some (10, 12, 7)) (.next
      ([5325000000000], [315000000000]) (some (10, 12, 7)) (some (10, 12, 7)) (.next
      ([6225000000000], [375000000000]) (some (10, 12, 7)) (some (10, 12, 8)) (.next
      ([6090000000000], [480000000000]) (some (10, 12, 8)) (some (10, 12, 8)) (.next
      ([5595000000000], [465000000000]) (some (10, 12, 8)) (some (10, 12, 8)) (.next
      ([5505000000000], [495000000000]) (some (10, 12, 8)) (some (10, 12, 8)) (.next
      ([5220000000000], [495000000000]) (some (10, 12, 8)) (some (10, 12, 8)) (.next
      ([2025000000000], [285000000000]) (some (10, 12, 8)) (some (10, 12, 8)) (.next
      ([5385000000000], [810000000000]) (some (10, 12, 8)) (some (10, 12, 8)) (.next
      ([5295000000000], [840000000000]) (some (10, 12, 8)) (some (10, 12, 8)) (.next
      ([5010000000000], [840000000000]) (some (10, 12, 8)) (some (10, 12, 8)) (.next
      ([5250000000000], [915000000000]) (some (10, 12, 8)) (some (10, 12, 8)) (.next
      ([5160000000000], [945000000000]) (some (10, 12, 8)) (some (10, 12, 8)) (.next
      ([4875000000000], [945000000000]) (some (10, 12, 8)) (some (10, 12, 8)) (.next
      ([105000000000], [30000000000]) (some (10, 12, 8)) (some (10, 12, 8)) (.next ([1965000000000],
      [570000000000]) (some (10, 12, 8)) (some (11, 12, 8)) (.next ([1680000000000], [570000000000])
      (some (11, 12, 8)) (some (11, 12, 8)) (.next ([1590000000000], [600000000000]) (some (11, 12,
      8)) (some (11, 12, 8)) fan40Owner0Part4))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2070000000000, -9000000000000], [180000000000,
      9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan40Owner5Part0)) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_9 : ExcludedOn (model40.B 9 ++ [step40.q]) 9000000000000 (model40.caps 9)
    (model40.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked40 : StepValid model40 9000000000000 step40 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded40_0
    · exact excluded40_1
    · exact excluded40_2
    · exact excluded40_3
    · exact (hj rfl).elim
    · exact excluded40_5
    · exact excluded40_6
    · exact excluded40_7
    · exact excluded40_8
    · exact excluded40_9
theorem next40 : model40.insert step40 = model41 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_4 : ExcludedOn (model41.B 4 ++ [step41.q]) 9000000000000 (model41.caps 4)
    (model41.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 6)) (some (5, 1, 6)) (.next ([6285000000000], [270000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([5355000000000, -9000000000000], [645000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([6120000000000], [1005000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([6000000000000, -9000000000000], [1290000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([570000000000], [165000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([5640000000000], [2145000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([1230000000000], [645000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([3855000000000, 0], [2430000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([4995000000000], [3435000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([1875000000000], [1290000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([660000000000],
      [480000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1305000000000], [1125000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) fan41Owner4Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7290000000000], [570000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan41Owner5Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4374000000000], [375000000000]) (some (6, 1, 2))
      (some (6, 1, 3)) (.next ([1641000000000], [234000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([7860000000000], [1710000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([4626000000000], [1749000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([3486000000000],
      [1335000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4140000000000], [2250000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([5430000000000, -9000000000000], [4140000000000,
      9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2430000000000, 9000000000000],
      [2430000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2055000000000,
      9000000000000], [2319000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([1944000000000, -9000000000000], [2805000000000, 9000000000000]) (some (6, 1, 3)) (some (6,
      1, 3)) (.next ([2196000000000, -9000000000000], [4179000000000, 9000000000000]) (some (6, 1,
      3)) (some (6, 1, 3)) (.next ([1710000000000, -9000000000000], [4680000000000, 9000000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([681000000000, 9000000000000], [3945000000000,
      -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) fan41Owner6Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_7 : ExcludedOn (model41.B 7 ++ [step41.q]) 9000000000000 (model41.caps 7)
    (model41.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_8 : ExcludedOn (model41.B 8 ++ [step41.q]) 9000000000000 (model41.caps 8)
    (model41.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_9 : ExcludedOn (model41.B 9 ++ [step41.q]) 9000000000000 (model41.caps 9)
    (model41.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked41 : StepValid model41 9000000000000 step41 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded41_1
    · exact excluded41_2
    · exact excluded41_3
    · exact excluded41_4
    · exact excluded41_5
    · exact excluded41_6
    · exact excluded41_7
    · exact excluded41_8
    · exact excluded41_9
theorem next41 : model41.insert step41 = model42 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded42_0 : ExcludedOn (model42.B 0 ++ [step42.q]) 9000000000000 (model42.caps 0)
    (model42.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_3 : ExcludedOn (model42.B 3 ++ [step42.q]) 9000000000000 (model42.caps 3)
    (model42.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_5 : ExcludedOn (model42.B 5 ++ [step42.q]) 9000000000000 (model42.caps 5)
    (model42.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (19) (28) (2800) (.witnessedFan (.next ([2070000000000,
      -9000000000000], [180000000000, 9000000000000]) (some (4, 0, 5)) (some (4, 5, 5)) (.next
      ([4500000000000], [540000000000]) (some (4, 5, 5)) (some (4, 5, 5)) (.next ([2430000000000,
      9000000000000], [360000000000, -9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([4635000000000], [1845000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([6480000000000],
      [2790000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([4635000000000, 0], [2430000000000,
      9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([4050000000000, -9000000000000],
      [2430000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2250000000000],
      [2250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1980000000000], [2250000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2385000000000], [4500000000000]) (some (0, 5, 3))
      (some (0, 5, 4)) (.next ([0], [4635000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-180000000000, -9000000000000], [2250000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-540000000000], [5040000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-360000000000,
      9000000000000], [2790000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1845000000000],
      [6480000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2790000000000], [9270000000000])
      (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2430000000000, -9000000000000], [7065000000000,
      9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2430000000000, -9000000000000],
      [6480000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2250000000000], [4500000000000])
      (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2250000000000], [4230000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-4500000000000], [6885000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.terminal (some (0, 5, 4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))
      (.witnessedFan (.next ([2430000000000, 9000000000000], [360000000000, -9000000000000]) (some
      (4, 0, 5)) (some (4, 5, 5)) (.next ([4500000000000], [540000000000]) (some (4, 5, 2)) (some
      (4, 5, 2)) (.next ([2070000000000, -9000000000000], [180000000000, 9000000000000]) (some (4,
      5, 2)) (some (4, 5, 2)) (.next ([4635000000000], [1845000000000]) (some (4, 5, 2)) (some (4,
      5, 3)) (.next ([6480000000000], [2790000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([4635000000000, 0], [2430000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([4050000000000, -9000000000000], [2430000000000, 9000000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([2250000000000], [2250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([1980000000000], [2250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2385000000000],
      [4500000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([0], [4635000000000]) (some (0, 5,
      4)) (some (0, 5, 4)) (.next ([-360000000000, 9000000000000], [2790000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-540000000000], [5040000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-180000000000, -9000000000000], [2250000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-1845000000000], [6480000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2790000000000], [9270000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2430000000000,
      -9000000000000], [7065000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2430000000000, -9000000000000], [6480000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2250000000000], [4500000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2250000000000], [4230000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-4500000000000], [6885000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
      4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_6 : ExcludedOn (model42.B 6 ++ [step42.q]) 9000000000000 (model42.caps 6)
    (model42.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_7 : ExcludedOn (model42.B 7 ++ [step42.q]) 9000000000000 (model42.caps 7)
    (model42.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_8 : ExcludedOn (model42.B 8 ++ [step42.q]) 9000000000000 (model42.caps 8)
    (model42.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked42 : StepValid model42 9000000000000 step42 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded42_0
    · exact excluded42_1
    · exact excluded42_2
    · exact excluded42_3
    · exact excluded42_4
    · exact excluded42_5
    · exact excluded42_6
    · exact excluded42_7
    · exact excluded42_8
    · exact (hj rfl).elim
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded43_0 : ExcludedOn (model43.B 0 ++ [step43.q]) 9000000000000 (model43.caps 0)
    (model43.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_2 : ExcludedOn (model43.B 2 ++ [step43.q]) 9000000000000 (model43.caps 2)
    (model43.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_3 : ExcludedOn (model43.B 3 ++ [step43.q]) 9000000000000 (model43.caps 3)
    (model43.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_4 : ExcludedOn (model43.B 4 ++ [step43.q]) 9000000000000 (model43.caps 4)
    (model43.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2070000000000, -9000000000000], [180000000000,
      9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next ([4635000000000], [1845000000000])
      (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4635000000000, 0], [2430000000000, 9000000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([4050000000000, -9000000000000], [2430000000000,
      9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([4635000000000], [3435000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2250000000000], [2250000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([1065000000000], [1185000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([3045000000000], [3435000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1980000000000], [2250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2385000000000],
      [4500000000000]) (some (0, 1, 3)) (some (0, 1, 4)) (.next ([0], [4635000000000]) (some (0, 1,
      4)) (some (0, 1, 4)) (.next ([-180000000000, -9000000000000], [2250000000000]) (some (0, 1,
      4)) (some (0, 5, 4)) (.next ([-1845000000000], [6480000000000]) (some (0, 5, 4)) (some (0, 5,
      4)) (.next ([-2430000000000, -9000000000000], [7065000000000, 9000000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-2430000000000, -9000000000000], [6480000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-3435000000000], [8070000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-2250000000000], [4500000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-1185000000000], [2250000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3435000000000], [6480000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2250000000000], [4230000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-4500000000000], [6885000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
      4)) (some (0, 5, 4)) (some (0, 5, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_7 : ExcludedOn (model43.B 7 ++ [step43.q]) 9000000000000 (model43.caps 7)
    (model43.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_8 : ExcludedOn (model43.B 8 ++ [step43.q]) 9000000000000 (model43.caps 8)
    (model43.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_9 : ExcludedOn (model43.B 9 ++ [step43.q]) 9000000000000 (model43.caps 9)
    (model43.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5175000000000], [390000000000]) (some (3, 0, 1))
      (some (3, 1, 2)) (.next ([2385000000000], [3825000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([3435000000000], [5565000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([645000000000], [2790000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [6210000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-390000000000], [5565000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3825000000000], [6210000000000]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([-5565000000000], [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-2790000000000], [3435000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some
      (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked43 : StepValid model43 9000000000000 step43 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded43_0
    · exact excluded43_1
    · exact excluded43_2
    · exact excluded43_3
    · exact excluded43_4
    · exact excluded43_5
    · exact (hj rfl).elim
    · exact excluded43_7
    · exact excluded43_8
    · exact excluded43_9
theorem next43 : model43.insert step43 = model44 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded44_0 : ExcludedOn (model44.B 0 ++ [step44.q]) 9000000000000 (model44.caps 0)
    (model44.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_2 : ExcludedOn (model44.B 2 ++ [step44.q]) 9000000000000 (model44.caps 2)
    (model44.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_3 : ExcludedOn (model44.B 3 ++ [step44.q]) 9000000000000 (model44.caps 3)
    (model44.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_4 : ExcludedOn (model44.B 4 ++ [step44.q]) 9000000000000 (model44.caps 4)
    (model44.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_5 : ExcludedOn (model44.B 5 ++ [step44.q]) 9000000000000 (model44.caps 5)
    (model44.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_6 : ExcludedOn (model44.B 6 ++ [step44.q]) 9000000000000 (model44.caps 6)
    (model44.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_7 : ExcludedOn (model44.B 7 ++ [step44.q]) 9000000000000 (model44.caps 7)
    (model44.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_8 : ExcludedOn (model44.B 8 ++ [step44.q]) 9000000000000 (model44.caps 8)
    (model44.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_9 : ExcludedOn (model44.B 9 ++ [step44.q]) 9000000000000 (model44.caps 9)
    (model44.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked44 : StepValid model44 9000000000000 step44 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded44_0
    · exact (hj rfl).elim
    · exact excluded44_2
    · exact excluded44_3
    · exact excluded44_4
    · exact excluded44_5
    · exact excluded44_6
    · exact excluded44_7
    · exact excluded44_8
    · exact excluded44_9
theorem next44 : model44.insert step44 = model45 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded45_0 : ExcludedOn (model45.B 0 ++ [step45.q]) 9000000000000 (model45.caps 0)
    (model45.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_1 : ExcludedOn (model45.B 1 ++ [step45.q]) 9000000000000 (model45.caps 1)
    (model45.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_2 : ExcludedOn (model45.B 2 ++ [step45.q]) 9000000000000 (model45.caps 2)
    (model45.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_3 : ExcludedOn (model45.B 3 ++ [step45.q]) 9000000000000 (model45.caps 3)
    (model45.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5565000000000], [330000000000]) (some (4, 0, 3))
      (some (6, 0, 3)) (.next ([6480000000000], [435000000000]) (some (6, 0, 3)) (some (6, 0, 3))
      (.next ([915000000000], [105000000000]) (some (6, 0, 3)) (some (6, 0, 3)) (.next
      ([2250000000000], [810000000000]) (some (6, 0, 3)) (some (6, 0, 3)) (.next ([5190000000000],
      [2430000000000, 9000000000000]) (some (6, 0, 3)) (some (6, 1, 3)) (.next ([1500000000000,
      9000000000000], [930000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4380000000000],
      [3060000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1545000000000], [1185000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1320000000000], [1740000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) fan45Owner3Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_4 : ExcludedOn (model45.B 4 ++ [step45.q]) 9000000000000 (model45.caps 4)
    (model45.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_5 : ExcludedOn (model45.B 5 ++ [step45.q]) 9000000000000 (model45.caps 5)
    (model45.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_6 : ExcludedOn (model45.B 6 ++ [step45.q]) 9000000000000 (model45.caps 6)
    (model45.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_7 : ExcludedOn (model45.B 7 ++ [step45.q]) 9000000000000 (model45.caps 7)
    (model45.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_9 : ExcludedOn (model45.B 9 ++ [step45.q]) 9000000000000 (model45.caps 9)
    (model45.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked45 : StepValid model45 9000000000000 step45 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded45_0
    · exact excluded45_1
    · exact excluded45_2
    · exact excluded45_3
    · exact excluded45_4
    · exact excluded45_5
    · exact excluded45_6
    · exact excluded45_7
    · exact (hj rfl).elim
    · exact excluded45_9
theorem next45 : model45.insert step45 = model46 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded46_0 : ExcludedOn (model46.B 0 ++ [step46.q]) 9000000000000 (model46.caps 0)
    (model46.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_1 : ExcludedOn (model46.B 1 ++ [step46.q]) 9000000000000 (model46.caps 1)
    (model46.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_2 : ExcludedOn (model46.B 2 ++ [step46.q]) 9000000000000 (model46.caps 2)
    (model46.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_3 : ExcludedOn (model46.B 3 ++ [step46.q]) 9000000000000 (model46.caps 3)
    (model46.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_4 : ExcludedOn (model46.B 4 ++ [step46.q]) 9000000000000 (model46.caps 4)
    (model46.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 4)) (some (5, 1, 4)) (.next ([6285000000000], [270000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([5355000000000, -9000000000000], [645000000000,
      9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([6120000000000], [1005000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([570000000000], [165000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([5640000000000], [2145000000000]) (some (5, 1, 4)) (some (5, 1, 4))
      (.next ([1230000000000], [645000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([3855000000000, 0], [2430000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([660000000000], [480000000000]) (some (5, 1, 4)) (some (5, 1, 4)) fan46Owner4Part0))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_5 : ExcludedOn (model46.B 5 ++ [step46.q]) 9000000000000 (model46.caps 5)
    (model46.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_6 : ExcludedOn (model46.B 6 ++ [step46.q]) 9000000000000 (model46.caps 6)
    (model46.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_7 : ExcludedOn (model46.B 7 ++ [step46.q]) 9000000000000 (model46.caps 7)
    (model46.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_9 : ExcludedOn (model46.B 9 ++ [step46.q]) 9000000000000 (model46.caps 9)
    (model46.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked46 : StepValid model46 9000000000000 step46 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded46_0
    · exact excluded46_1
    · exact excluded46_2
    · exact excluded46_3
    · exact excluded46_4
    · exact excluded46_5
    · exact excluded46_6
    · exact excluded46_7
    · exact (hj rfl).elim
    · exact excluded46_9
theorem next46 : model46.insert step46 = model47 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded47_0 : ExcludedOn (model47.B 0 ++ [step47.q]) 9000000000000 (model47.caps 0)
    (model47.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_1 : ExcludedOn (model47.B 1 ++ [step47.q]) 9000000000000 (model47.caps 1)
    (model47.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_2 : ExcludedOn (model47.B 2 ++ [step47.q]) 9000000000000 (model47.caps 2)
    (model47.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_3 : ExcludedOn (model47.B 3 ++ [step47.q]) 9000000000000 (model47.caps 3)
    (model47.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5565000000000], [330000000000]) (some (4, 6, 3))
      (some (5, 6, 3)) (.next ([6480000000000], [435000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      (.next ([915000000000], [105000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([7290000000000], [1395000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([6375000000000],
      [1290000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2250000000000], [810000000000])
      (some (5, 6, 3)) (some (5, 6, 3)) (.next ([5190000000000], [2430000000000, 9000000000000])
      (some (5, 6, 3)) (some (5, 6, 3)) (.next ([4380000000000], [3060000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) (.next ([1545000000000], [1185000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      fan47Owner3Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_5 : ExcludedOn (model47.B 5 ++ [step47.q]) 9000000000000 (model47.caps 5)
    (model47.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_6 : ExcludedOn (model47.B 6 ++ [step47.q]) 9000000000000 (model47.caps 6)
    (model47.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_7 : ExcludedOn (model47.B 7 ++ [step47.q]) 9000000000000 (model47.caps 7)
    (model47.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_8 : ExcludedOn (model47.B 8 ++ [step47.q]) 9000000000000 (model47.caps 8)
    (model47.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8070000000000], [105000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([3090000000000], [930000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([4020000000000], [4980000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([825000000000], [4155000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [8175000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-105000000000], [8175000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-930000000000], [4020000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-4980000000000], [9000000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-4155000000000], [4980000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some
      (0, 1, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_9 : ExcludedOn (model47.B 9 ++ [step47.q]) 9000000000000 (model47.caps 9)
    (model47.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked47 : StepValid model47 9000000000000 step47 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded47_0
    · exact excluded47_1
    · exact excluded47_2
    · exact excluded47_3
    · exact (hj rfl).elim
    · exact excluded47_5
    · exact excluded47_6
    · exact excluded47_7
    · exact excluded47_8
    · exact excluded47_9
theorem next47 : model47.insert step47 = model48 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint270000280000
end ConwaySoifer.Simplified.Certificates
