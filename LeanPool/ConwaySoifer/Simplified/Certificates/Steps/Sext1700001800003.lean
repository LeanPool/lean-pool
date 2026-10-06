/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext170000180000
import Mathlib.Tactic.FinCases

/-!
# Sext 170000 180000 3

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
namespace Sext170000180000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner3Part0 : FanWitness := (.next ([3000000000000, 0], [3960000000000, -9000000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1350000000000, -9000000000000], [2250000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3000000000000], [5490000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([1470000000000, -9000000000000], [7020000000000, 9000000000000]) (some
    (5, 1, 6)) (some (5, 1, 6)) (.next ([765000000000], [4125000000000]) (some (5, 1, 6)) (some (5,
    1, 6)) (.next ([510000000000, 9000000000000], [5010000000000]) (some (5, 1, 6)) (some (5, 1, 6))
    (.next ([0], [1530000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 2, 6)) (.next
    ([-120000000000], [3225000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-240000000000],
    [2115000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-720000000000, 9000000000000],
    [5130000000000]) (some (0, 2, 6)) (some (0, 3, 6)) (.next ([-765000000000, -9000000000000],
    [4125000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2010000000000], [9480000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2130000000000], [8370000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-1020000000000], [3480000000000, -9000000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-1890000000000], [6255000000000]) (some (0, 3, 6)) (some (1, 3, 6))
    (.next ([-2250000000000], [5130000000000]) (some (1, 3, 6)) (some (1, 6, 6)) (.next
    ([-1530000000000, -9000000000000], [3060000000000, 18000000000000]) (some (1, 6, 6)) (some (1,
    6, 6)) (.next ([-2595000000000, 9000000000000], [4890000000000]) (some (1, 6, 6)) (some (1, 6,
    6)) (.next ([-3960000000000, 9000000000000], [6960000000000, -9000000000000]) (some (1, 6, 6))
    (some (1, 6, 6)) (.next ([-2250000000000], [3600000000000, -9000000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-5490000000000], [8490000000000]) (some (1, 6, 4)) (some (1, 6, 4))
    (.next ([-7020000000000, -9000000000000], [8490000000000]) (some (1, 6, 4)) (some (1, 6, 4))
    (.next ([-4125000000000], [4890000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next
    ([-5010000000000, 0], [5520000000000, 9000000000000]) (some (1, 6, 4)) (some (1, 6, 4))
    (.terminal (some (1, 6, 4)) (some (1, 6, 4)) (some (1, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner5Part0 : FanWitness := (.next ([8055000000000], [615000000000]) (some (5, 1, 5)) (some
    (5, 1, 5)) (.next ([8085000000000, 9000000000000], [1095000000000, -9000000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([6555000000000], [2625000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([246000000000], [99000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([2010000000000], [5835000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([510000000000],
    [1500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1764000000000], [5736000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1530000000000, 9000000000000], [6345000000000, 0])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([555000000000], [2379000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([1284000000000, 9000000000000], [6246000000000, 0]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([210000000000], [2625000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([0, 0], [1530000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-246000000000], [6246000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-615000000000],
    [8670000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1095000000000, 9000000000000],
    [9180000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2625000000000], [9180000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-99000000000], [345000000000]) (some (0, 2, 5)) (some
    (0, 2, 5)) (.next ([-5835000000000], [7845000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1500000000000], [2010000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5736000000000],
    [7500000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6345000000000, 0], [7875000000000,
    9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2379000000000], [2934000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6246000000000, 0], [7530000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2625000000000], [2835000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 5, 5)) (some (0, 5,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner4Part0 : FanWitness := (.next ([105000000000], [156000000000]) (some (6, 1, 3)) (some
    (6, 1, 3)) (.next ([1710000000000, 9000000000000], [3165000000000, -9000000000000]) (some (6, 1,
    3)) (some (6, 1, 4)) (.next ([1530000000000, 9000000000000], [5121000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([999000000000], [5130000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([441000000000], [4590000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([180000000000], [4695000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([9000000000],
    [2871000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([0], [5121000000000]) (some (6, 1,
    4)) (some (6, 1, 4)) (.next ([-90000000000], [4680000000000]) (some (0, 1, 4)) (some (0, 1, 4))
    (.next ([-246000000000], [4941000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-99000000000], [1809000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-255000000000],
    [2070000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-711000000000], [5031000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-816000000000], [4875000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([-1350000000000, 9000000000000], [5130000000000]) (some (0, 1, 4))
    (some (0, 1, 6)) (.next ([-2880000000000], [5130000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-5121000000000], [9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-156000000000], [261000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-3165000000000,
    9000000000000], [4875000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-5121000000000],
    [6651000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-5130000000000],
    [6129000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-4590000000000], [5031000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-4695000000000], [4875000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-2871000000000], [2880000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.terminal (some (0, 1, 6)) (some (0, 2, 6)) (some (0, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner4Part0 : FanWitness := (.next ([1710000000000, 9000000000000], [3165000000000,
    -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1530000000000, 9000000000000],
    [5121000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([441000000000], [4590000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([180000000000], [4695000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([9000000000], [2871000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([0], [5121000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-90000000000],
    [4680000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-246000000000], [4941000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-99000000000], [1809000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-531000000000], [9090000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-285000000000], [4149000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-540000000000], [6219000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-441000000000],
    [4410000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-255000000000], [2070000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1350000000000, 9000000000000], [5130000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2439000000000, 9000000000000], [7029000000000,
    -9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-3969000000000], [8559000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2880000000000], [5130000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-156000000000], [261000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-3165000000000, 9000000000000], [4875000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-5121000000000], [6651000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-4590000000000], [5031000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-4695000000000], [4875000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2871000000000],
    [2880000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.terminal (some (0, 1, 6)) (some (0, 2, 6))
    (some (0, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner0Part0 : FanWitness := (.next ([-60000000000], [255000000000]) (some (8, 3, 6)) (some
    (8, 3, 6)) (.next ([-750000000000], [2925000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-1905000000000], [6810000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-1260000000000],
    [3810000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-3615000000000], [9615000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-3810000000000], [9555000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([-3870000000000], [9435000000000]) (some (8, 3, 6)) (some (8, 3, 6))
    (.next ([-180000000000], [435000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-375000000000], [765000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-900000000000],
    [1785000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-510000000000], [885000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-3375000000000], [5790000000000]) (some (8, 3, 6))
    (some (8, 3, 7)) (.next ([-1710000000000], [2805000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-120000000000], [180000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-4260000000000], [6165000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-1905000000000],
    [2745000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-1965000000000], [2625000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4635000000000], [5655000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-4260000000000], [4890000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-6180000000000], [6885000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-6120000000000], [6630000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-6000000000000],
    [6450000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-7065000000000], [7260000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-2535000000000], [2550000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.terminal (some (8, 3, 7)) (some (8, 3, 7)) (some (8, 3,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner0Part1 : FanWitness := (.next ([375000000000], [510000000000]) (some (8, 2, 4)) (some
    (8, 2, 4)) (.next ([2415000000000], [3375000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([1095000000000], [1710000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([60000000000],
    [120000000000]) (some (8, 2, 4)) (some (8, 3, 4)) (.next ([1905000000000], [4260000000000])
    (some (8, 3, 4)) (some (8, 3, 5)) (.next ([840000000000], [1905000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([660000000000], [1965000000000]) (some (8, 3, 5)) (some (8, 3, 5))
    (.next ([1020000000000], [4635000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next
    ([630000000000], [4260000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([705000000000],
    [6180000000000]) (some (8, 3, 5)) (some (8, 3, 5)) (.next ([510000000000], [6120000000000])
    (some (8, 3, 5)) (some (8, 3, 5)) (.next ([450000000000], [6000000000000]) (some (8, 3, 5))
    (some (8, 3, 5)) (.next ([195000000000], [7065000000000]) (some (8, 3, 5)) (some (8, 3, 6))
    (.next ([15000000000], [2535000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([0],
    [1275000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-60000000000], [6885000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-690000000000], [7440000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([-135000000000], [1395000000000]) (some (8, 3, 6)) (some (8, 3, 6))
    (.next ([-885000000000], [7380000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-945000000000], [7260000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-1080000000000],
    [7065000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-1275000000000], [7005000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-1335000000000], [6885000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([-885000000000], [4320000000000]) (some (8, 3, 6)) (some (8, 3, 6))
    fan30Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner3Part0 : FanWitness := (.next ([3435000000000], [5940000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([2040000000000], [4371000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([1530000000000, 9000000000000], [5121000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([555000000000], [3690000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([441000000000], [4590000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([9000000000],
    [2241000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0], [5121000000000]) (some (5, 6,
    4)) (some (5, 6, 4)) (.next ([-90000000000], [4680000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-99000000000], [2439000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-210000000000], [4380000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-720000000000,
    9000000000000], [5130000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1686000000000],
    [5940000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1350000000000], [4344000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2250000000000], [5130000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3900000000000], [8625000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-4410000000000, 9000000000000], [9375000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2550000000000], [4281000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1290000000000], [2040000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5940000000000],
    [9375000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4371000000000], [6411000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5121000000000, 0], [6651000000000, 9000000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3690000000000], [4245000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-4590000000000], [5031000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2241000000000], [2250000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.terminal (some
    (0, 6, 4)) (some (0, 6, 4)) (some (0, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner3Part0 : FanWitness := (.next ([2040000000000], [4371000000000]) (some (5, 0, 6))
    (some (5, 6, 6)) (.next ([1530000000000, 9000000000000], [5121000000000]) (some (5, 6, 6)) (some
    (5, 6, 6)) (.next ([1020000000000, 9000000000000], [7080000000000, -9000000000000]) (some (5, 6,
    6)) (some (5, 6, 6)) (.next ([780000000000], [6570000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([441000000000], [4590000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([9000000000],
    [2241000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0], [5121000000000]) (some (5, 6,
    4)) (some (5, 6, 4)) (.next ([-90000000000], [4680000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-99000000000], [2439000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-210000000000], [4380000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-510000000000],
    [8610000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-720000000000, 9000000000000],
    [5130000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-951000000000], [4020000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2250000000000], [5130000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3390000000000], [6360000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2550000000000], [4281000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1290000000000], [2040000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5631000000000],
    [8610000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4371000000000], [6411000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5121000000000, 0], [6651000000000, 9000000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-7080000000000, 9000000000000], [8100000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6570000000000], [7350000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-4590000000000], [5031000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2241000000000], [2250000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.terminal (some
    (0, 6, 4)) (some (0, 6, 4)) (some (0, 6, 4)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7530000000000, 9000000000000], [1980000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([6000000000000], [3510000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4470000000000, -9000000000000], [3510000000000, 0])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1530000000000, 9000000000000], [1530000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1530000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1980000000000, 9000000000000],
      [9510000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3510000000000], [9510000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3510000000000, 0], [7980000000000,
      -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1530000000000, -9000000000000],
      [3060000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 3)) (.terminal (some (3, 1, 3))
      (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3105000000000], [120000000000]) (some (4, 1, 6))
      (some (5, 1, 6)) (.next ([1875000000000], [240000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([4410000000000, 9000000000000], [720000000000, -9000000000000]) (some (5, 1, 6)) (some
      (5, 1, 6)) (.next ([3360000000000, -9000000000000], [765000000000, 9000000000000]) (some (5,
      1, 6)) (some (5, 1, 6)) (.next ([7470000000000], [2010000000000]) (some (5, 1, 6)) (some (5,
      1, 6)) (.next ([6240000000000], [2130000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([2460000000000, -9000000000000], [1020000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([4365000000000], [1890000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2880000000000],
      [2250000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1530000000000, 9000000000000],
      [1530000000000, 9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2295000000000,
      9000000000000], [2595000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan24Owner3Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded24_8 : ExcludedOn (model24.B 8 ++ [step24.q]) 9000000000000 (model24.caps 8)
    (model24.ord 8) 0 1 100 := by
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
    · exact (hj rfl).elim
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

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [246000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([5250000000000], [1710000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([246000000000], [99000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([3750000000000], [3720000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1224000000000],
      [2250000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1125000000000], [2595000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2010000000000], [5835000000000]) (some (4, 1, 2))
      (some (4, 1, 5)) (.next ([510000000000], [1500000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([1764000000000], [5736000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([1530000000000, 9000000000000], [6345000000000, 0]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([1284000000000, 9000000000000], [6246000000000, 0]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([0, 0], [1530000000000, 9000000000000]) (some (4, 1, 5)) (some (0, 1, 5)) (.next
      ([-246000000000], [6246000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-1710000000000],
      [6960000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-99000000000], [345000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3720000000000], [7470000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-2250000000000], [3474000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-2595000000000], [3720000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-5835000000000], [7845000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-1500000000000], [2010000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-5736000000000], [7500000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6345000000000,
      0], [7875000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6246000000000,
      0], [7530000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3720000000000], [1530000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([5250000000000], [3750000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([1530000000000, 9000000000000], [7470000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 9000000000000], [3720000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1530000000000, 9000000000000]) (some (3, 0,
      2)) (some (3, 0, 2)) (.next ([-1530000000000], [5250000000000]) (some (3, 0, 2)) (some (3, 1,
      2)) (.next ([-3750000000000, 9000000000000], [9000000000000, -9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-7470000000000, 9000000000000], [9000000000000, 0]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-3720000000000, 9000000000000], [3720000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded25_1
    · exact excluded25_2
    · exact excluded25_3
    · exact excluded25_4
    · exact excluded25_5
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1530000000000, 9000000000000], [1530000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2445000000000], [4845000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2445000000000], [6375000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([915000000000, -9000000000000], [7905000000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [1530000000000, 9000000000000]) none
      none (.next ([-1530000000000, -9000000000000], [3060000000000, 18000000000000]) none none
      (.next ([-4845000000000, 9000000000000], [7290000000000, -9000000000000]) (some (3, 3, 0))
      (some (3, 3, 0)) (.next ([-6375000000000], [8820000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-7905000000000, -9000000000000], [8820000000000, 0]) (some (3, 1, 0)) (some (3, 1,
      0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_2 : ExcludedOn (model26.B 2 ++ [step26.q]) 9000000000000 (model26.caps 2)
    (model26.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [246000000000]) (some (5, 0, 5))
      (some (5, 1, 5)) fan26Owner5Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1710000000000, 9000000000000], [915000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2445000000000], [4845000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1530000000000, 9000000000000],
      [7470000000000, -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([180000000000],
      [2445000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1530000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-915000000000, 9000000000000],
      [2625000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-4845000000000, 9000000000000],
      [7290000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7470000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2445000000000], [2625000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded26_1
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
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4590000000000], [90000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([4695000000000], [246000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([1710000000000], [99000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([1815000000000], [255000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([4320000000000],
      [711000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4059000000000], [816000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([3780000000000, 9000000000000], [1350000000000,
      -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2250000000000], [2880000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([3879000000000], [5121000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) fan27Owner4Part0)))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel)
      0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3870000000000], [9000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([3885000000000], [1245000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([5121000000000], [3879000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([6000000000], [5115000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5130000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-9000000000], [3879000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1245000000000], [5130000000000]) (some (0, 1, 2))
      (some (0, 3, 2)) (.next ([-3879000000000], [9000000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-5115000000000], [5121000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded27_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000], [255000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([6960000000000], [750000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([3195000000000], [750000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([2040000000000, 9000000000000], [1470000000000, -9000000000000]) (some (0, 4, 2)) (some (4,
      4, 2)) (.next ([2250000000000], [4200000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([1530000000000, 9000000000000], [3765000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([510000000000], [3000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([780000000000,
      9000000000000], [7710000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [3765000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-255000000000], [3255000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([-750000000000], [7710000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-750000000000], [3945000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-1470000000000, 9000000000000], [3510000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-4200000000000], [6450000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next
      ([-3765000000000, 0], [5295000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3000000000000], [3510000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-7710000000000,
      0], [8490000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded28_0
    · exact excluded28_1
    · exact excluded28_2
    · exact (hj rfl).elim
    · exact excluded28_4
    · exact excluded28_5
    · exact excluded28_6
    · exact excluded28_7
    · exact excluded28_8
    · exact excluded28_9
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded29_0 : ExcludedOn (model29.B 0 ++ [step29.q]) 9000000000000 (model29.caps 0)
    (model29.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_1 : ExcludedOn (model29.B 1 ++ [step29.q]) 9000000000000 (model29.caps 1)
    (model29.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_2 : ExcludedOn (model29.B 2 ++ [step29.q]) 9000000000000 (model29.caps 2)
    (model29.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000], [255000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([3900000000000], [2031000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([5940000000000, 9000000000000], [3501000000000, -9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([2040000000000, 9000000000000], [1470000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4410000000000], [5031000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1530000000000, 9000000000000], [3765000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([510000000000], [3000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([645000000000], [5031000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0],
      [3765000000000]) (some (0, 4, 2)) (some (4, 4, 2)) (.next ([-255000000000], [3255000000000])
      (some (4, 4, 2)) (some (4, 4, 3)) (.next ([-2031000000000], [5931000000000]) (some (4, 4, 3))
      (some (4, 4, 3)) (.next ([-3501000000000, 9000000000000], [9441000000000, 0]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-1470000000000, 9000000000000], [3510000000000, 0]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-5031000000000], [9441000000000]) (some (4, 1, 3)) (some (4, 2, 3))
      (.next ([-3765000000000, 0], [5295000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-3000000000000], [3510000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-5031000000000], [5676000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4590000000000], [90000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([4695000000000], [246000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([1710000000000], [99000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([8559000000000], [531000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([3864000000000],
      [285000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([5679000000000], [540000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([3969000000000], [441000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([1815000000000], [255000000000]) (some (6, 1, 3)) (some (6, 1, 6))
      (.next ([3780000000000, 9000000000000], [1350000000000, -9000000000000]) (some (6, 1, 6))
      (some (6, 1, 6)) (.next ([4590000000000], [2439000000000, -9000000000000]) (some (6, 1, 6))
      (some (6, 1, 6)) (.next ([4590000000000], [3969000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([2250000000000], [2880000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([105000000000], [156000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan29Owner4Part0)))))))))))))) (den := 9000000000000) (fuel := 12)
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
    · exact excluded29_0
    · exact excluded29_1
    · exact excluded29_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6825000000000], [60000000000]) (some (7, 8, 3))
      (some (7, 8, 3)) (.next ([6750000000000], [690000000000]) (some (7, 8, 3)) (some (7, 8, 3))
      (.next ([1260000000000], [135000000000]) (some (7, 8, 3)) (some (7, 8, 3)) (.next
      ([6495000000000], [885000000000]) (some (7, 8, 3)) (some (7, 8, 3)) (.next ([6315000000000],
      [945000000000]) (some (7, 8, 3)) (some (7, 8, 3)) (.next ([5985000000000], [1080000000000])
      (some (7, 8, 3)) (some (7, 8, 3)) (.next ([5730000000000], [1275000000000]) (some (7, 8, 3))
      (some (7, 8, 3)) (.next ([5550000000000], [1335000000000]) (some (7, 8, 3)) (some (7, 8, 3))
      (.next ([3435000000000], [885000000000]) (some (7, 8, 3)) (some (7, 8, 3)) (.next
      ([195000000000], [60000000000]) (some (7, 8, 3)) (some (7, 8, 3)) (.next ([2175000000000],
      [750000000000]) (some (7, 8, 3)) (some (7, 8, 4)) (.next ([4905000000000], [1905000000000])
      (some (7, 8, 4)) (some (7, 8, 4)) (.next ([2550000000000], [1260000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([6000000000000], [3615000000000]) (some (7, 2, 4)) (some (8, 2, 4))
      (.next ([5745000000000], [3810000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
      ([5565000000000], [3870000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([255000000000],
      [180000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([390000000000], [375000000000])
      (some (8, 2, 4)) (some (8, 2, 4)) (.next ([885000000000], [900000000000]) (some (8, 2, 4))
      (some (8, 2, 4)) fan30Owner0Part1)))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_1 : ExcludedOn (model30.B 1 ++ [step30.q]) 9000000000000 (model30.caps 1)
    (model30.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_2 : ExcludedOn (model30.B 2 ++ [step30.q]) 9000000000000 (model30.caps 2)
    (model30.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_3 : ExcludedOn (model30.B 3 ++ [step30.q]) 9000000000000 (model30.caps 3)
    (model30.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4590000000000], [90000000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([2340000000000], [99000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([4170000000000], [210000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([4410000000000, 9000000000000], [720000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 0,
      6)) (.next ([4254000000000], [1686000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([2994000000000], [1350000000000]) (some (5, 0, 6)) (some (5, 6, 6)) (.next ([2880000000000],
      [2250000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4725000000000], [3900000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4965000000000, 9000000000000], [4410000000000,
      -9000000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([1731000000000], [2550000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([750000000000], [1290000000000]) (some (5, 6, 2))
      (some (5, 6, 3)) fan30Owner3Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded30_5
    · exact excluded30_6
    · exact excluded30_7
    · exact excluded30_8
    · exact excluded30_9
theorem next30 : model30.insert step30 = model31 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded31_1 : ExcludedOn (model31.B 1 ++ [step31.q]) 9000000000000 (model31.caps 1)
    (model31.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7860000000000, -9000000000000], [630000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([1530000000000, 9000000000000],
      [1530000000000, 9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([2430000000000,
      9000000000000], [6960000000000, -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next
      ([900000000000], [8490000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [1530000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-630000000000,
      -9000000000000], [8490000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-1530000000000, -9000000000000], [3060000000000, 18000000000000]) (some (3, 1, 0)) (some (3,
      1, 0)) (.next ([-6960000000000, 9000000000000], [9390000000000]) (some (3, 1, 0)) (some (3, 1,
      0)) (.next ([-8490000000000], [9390000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal
      (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4980000000000], [120000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([3000000000000], [255000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([2040000000000, 9000000000000], [1470000000000, -9000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1530000000000, 9000000000000], [3765000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1920000000000, 9000000000000], [6570000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([510000000000], [3000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([390000000000], [8100000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([0], [3765000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-120000000000],
      [5100000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-255000000000], [3255000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1470000000000, 9000000000000], [3510000000000, 0])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3765000000000, 0], [5295000000000, 9000000000000])
      (some (0, 4, 3)) (some (4, 4, 3)) (.next ([-6570000000000, 9000000000000], [8490000000000, 0])
      (some (4, 4, 3)) (some (4, 4, 3)) (.next ([-3000000000000], [3510000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-8100000000000], [8490000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.terminal (some (4, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_3 : ExcludedOn (model31.B 3 ++ [step31.q]) 9000000000000 (model31.caps 3)
    (model31.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4590000000000], [90000000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([2340000000000], [99000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([4170000000000], [210000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([8100000000000], [510000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([4410000000000,
      9000000000000], [720000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([3069000000000], [951000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([2880000000000],
      [2250000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([2970000000000], [3390000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1731000000000], [2550000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([750000000000], [1290000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([2979000000000], [5631000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      fan31Owner3Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded31_1
    · exact excluded31_2
    · exact excluded31_3
    · exact excluded31_4
    · exact excluded31_5
    · exact excluded31_6
    · exact excluded31_7
    · exact excluded31_8
    · exact excluded31_9
theorem next31 : model31.insert step31 = model32 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext170000180000
end ConwaySoifer.Simplified.Certificates
