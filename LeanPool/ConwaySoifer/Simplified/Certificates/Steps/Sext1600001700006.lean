/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext160000170000
import Mathlib.Tactic.FinCases

/-!
# Sext 160000 170000 6

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
def fan48Owner4Part0 : FanWitness := (.next ([4725000000000], [1935000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([2250000000000], [1152000000000, -9000000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([2592000000000], [1593000000000]) (some (4, 1, 2)) (some (4, 1, 2))
    (.next ([4842000000000], [3285000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
    ([2250000000000], [2592000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1125000000000],
    [1710000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1440000000000, 9000000000000],
    [4995000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1440000000000,
    9000000000000], [5535000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([900000000000],
    [5535000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([315000000000, 9000000000000],
    [3285000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([117000000000],
    [1350000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [5535000000000]) (some (4, 1,
    2)) (some (4, 1, 2)) (.next ([-1125000000000], [4725000000000]) (some (0, 1, 2)) (some (0, 1,
    2)) (.next ([-1935000000000], [6660000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([-1152000000000, 9000000000000], [3402000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1,
    2)) (.next ([-1593000000000], [4185000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([-3285000000000], [8127000000000]) (some (0, 1, 2)) (some (0, 1, 5)) (.next ([-2592000000000],
    [4842000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1710000000000], [2835000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4995000000000, 9000000000000], [6435000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5535000000000], [6975000000000, 9000000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5535000000000], [6435000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-3285000000000, 9000000000000], [3600000000000]) (some (0, 1, 5))
    (some (0, 2, 5)) (.next ([-1350000000000], [1467000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner3Part0 : FanWitness := (.next ([318000000000], [1932000000000]) (some (6, 0, 7)) (some
    (6, 0, 7)) (.next ([1005000000000], [6408000000000]) (some (6, 0, 7)) (some (6, 1, 7)) (.next
    ([480000000000], [5250000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([0],
    [6090000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([-360000000000], [5610000000000])
    (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-435000000000], [6033000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([-810000000000, 9000000000000], [6408000000000]) (some (0, 1, 7)) (some
    (0, 1, 7)) (.next ([-678000000000], [3678000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([-375000000000], [1815000000000]) (some (0, 1, 7)) (some (0, 2, 7)) (.next ([-1995000000000],
    [5730000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-2250000000000], [6408000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-960000000000], [1965000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-1290000000000], [2250000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-3000000000000], [4770000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-3435000000000], [5355000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-6090000000000],
    [9345000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-5130000000000], [7380000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-435000000000], [585000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-5715000000000], [7530000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-1440000000000], [1815000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-6090000000000, 0], [7530000000000, 9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-1932000000000], [2250000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-6408000000000],
    [7413000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-5250000000000], [5730000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.terminal (some (0, 2, 7)) (some (0, 2, 5)) (some (0, 2,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan50Owner3Part0 : FanWitness := (.next ([0], [6090000000000]) (some (6, 1, 7)) (some (6, 1, 7))
    (.next ([-360000000000], [5610000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([-435000000000], [6033000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-810000000000,
    9000000000000], [6408000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-678000000000],
    [3678000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-2265000000000], [9345000000000])
    (some (0, 1, 7)) (some (0, 2, 7)) (.next ([-1815000000000, 9000000000000], [5640000000000,
    -9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-1815000000000], [5265000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2583000000000], [7413000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-2250000000000], [6408000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-1965000000000], [4830000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-3255000000000], [7080000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1905000000000],
    [3735000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1290000000000], [2250000000000])
    (some (0, 2, 5)) (some (0, 7, 5)) (.next ([-3000000000000], [4770000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-3435000000000], [5355000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-3810000000000, 9000000000000], [5730000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-5130000000000], [7380000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-435000000000], [585000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-5715000000000],
    [7530000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1440000000000], [1815000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-6090000000000, 0], [7530000000000, 9000000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1932000000000], [2250000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-5250000000000], [5730000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.terminal (some (0, 7, 5)) (some (0, 7, 5)) (some (0, 7, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan53Owner1Part0 : FanWitness := (.next ([2415000000000], [915000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([6540000000000], [3330000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([4125000000000], [2415000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2400000000000,
    9000000000000], [1935000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([1920000000000], [4140000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([1920000000000], [5580000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([960000000000], [3375000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([480000000000,
    9000000000000], [5250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([480000000000,
    -9000000000000], [7020000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0],
    [1440000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-480000000000,
    -9000000000000], [3375000000000, 0]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-960000000000],
    [5250000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-960000000000, 0], [3810000000000,
    -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-915000000000], [3330000000000])
    (some (0, 5, 0)) (some (0, 5, 0)) (.next ([-3330000000000], [9870000000000]) (some (0, 5, 0))
    none (.next ([-2415000000000], [6540000000000]) none none (.next ([-1935000000000,
    9000000000000], [4335000000000]) none none (.next ([-1440000000000, -9000000000000],
    [2880000000000, 18000000000000]) (some (5, 5, 0)) (some (5, 5, 0)) (.next ([-4140000000000,
    9000000000000], [6060000000000, -9000000000000]) (some (5, 5, 0)) (some (5, 5, 0)) (.next
    ([-5580000000000], [7500000000000]) (some (5, 2, 0)) (some (5, 2, 0)) (.next ([-3375000000000],
    [4335000000000]) (some (5, 2, 0)) (some (5, 2, 0)) (.next ([-5250000000000], [5730000000000,
    9000000000000]) (some (5, 2, 0)) (some (5, 2, 0)) (.next ([-7020000000000, -9000000000000],
    [7500000000000, 0]) (some (5, 2, 0)) (some (5, 2, 0)) (.terminal (some (5, 2, 0)) (some (5, 2,
    0)) (some (5, 2, 0)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan54Owner0Part0 : FanWitness := (.next ([-180000000000], [375000000000]) (some (1, 4, 7)) (some
    (1, 4, 7)) (.next ([-285000000000], [585000000000]) (some (1, 4, 7)) (some (1, 4, 8)) (.next
    ([-3840000000000], [7875000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-870000000000],
    [1620000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-3255000000000], [5550000000000])
    (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-855000000000], [1365000000000]) (some (1, 4, 8))
    (some (1, 4, 8)) (.next ([-1920000000000], [3015000000000]) (some (1, 4, 8)) (some (1, 4, 8))
    (.next ([-3735000000000], [5835000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next
    ([-135000000000], [210000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-690000000000],
    [1020000000000]) (some (1, 4, 8)) (some (2, 4, 8)) (.next ([-4110000000000], [6030000000000])
    (some (2, 4, 8)) (some (2, 5, 8)) (.next ([-1065000000000], [1440000000000]) (some (2, 5, 8))
    (some (2, 5, 8)) (.next ([-660000000000], [885000000000]) (some (2, 5, 8)) (some (2, 5, 8))
    (.next ([-855000000000], [1140000000000]) (some (2, 5, 8)) (some (2, 5, 8)) (.next
    ([-4395000000000], [5835000000000]) (some (2, 5, 8)) (some (2, 5, 8)) (.next ([-2025000000000],
    [2400000000000]) (some (2, 5, 8)) (some (2, 5, 8)) (.next ([-4695000000000], [5550000000000])
    (some (2, 5, 8)) (some (2, 5, 8)) (.next ([-2940000000000], [3345000000000]) (some (2, 5, 8))
    (some (2, 5, 8)) (.next ([-4620000000000], [5175000000000]) (some (2, 5, 8)) (some (2, 5, 8))
    (.next ([-4485000000000], [4965000000000]) (some (2, 5, 8)) (some (2, 5, 8)) (.next
    ([-870000000000], [960000000000]) (some (2, 5, 8)) (some (3, 5, 8)) (.next ([-6270000000000],
    [6645000000000]) (some (3, 5, 8)) (some (3, 5, 8)) (.next ([-1335000000000], [1380000000000])
    (some (3, 5, 8)) (some (3, 5, 8)) (.next ([-6750000000000], [6930000000000]) (some (3, 5, 8))
    (some (3, 10, 8)) (.terminal (some (3, 10, 8)) (some (3, 10, 8)) (some (3, 10,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan54Owner0Part1 : FanWitness := (.next ([-1020000000000], [7455000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([-1065000000000], [7710000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    (.next ([-1365000000000], [7635000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-1440000000000], [7500000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-1500000000000], [7740000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-75000000000],
    [375000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-930000000000], [4320000000000])
    (some (0, 4, 10)) (some (1, 4, 10)) (.next ([-375000000000], [1740000000000]) (some (1, 4, 10))
    (some (1, 4, 10)) (.next ([-285000000000], [1245000000000]) (some (1, 4, 10)) (some (1, 4, 10))
    (.next ([-2085000000000], [8040000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next
    ([-2385000000000], [7965000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next
    ([-2025000000000], [6645000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next
    ([-2220000000000], [7125000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-2460000000000],
    [7830000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-2400000000000], [7500000000000])
    (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-585000000000], [1815000000000]) (some (1, 4, 6))
    (some (1, 4, 6)) (.next ([-210000000000], [585000000000]) (some (1, 4, 6)) (some (1, 4, 6))
    (.next ([-2880000000000], [7785000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next
    ([-195000000000], [480000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-660000000000],
    [1545000000000]) (some (1, 4, 6)) (some (1, 4, 7)) (.next ([-3465000000000], [8085000000000])
    (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-375000000000], [855000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-480000000000], [1065000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-3765000000000], [8010000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    fan54Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan54Owner0Part2 : FanWitness := (.next ([2295000000000], [3255000000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([510000000000], [855000000000]) (some (0, 3, 10)) (some (0, 3, 10))
    (.next ([1095000000000], [1920000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([2100000000000], [3735000000000]) (some (0, 3, 10)) (some (0, 4, 10)) (.next ([75000000000],
    [135000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([330000000000], [690000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([1920000000000], [4110000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([375000000000], [1065000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    (.next ([225000000000], [660000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([285000000000], [855000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([1440000000000],
    [4395000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([375000000000], [2025000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([855000000000], [4695000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([405000000000], [2940000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    (.next ([555000000000], [4620000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([480000000000], [4485000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([90000000000],
    [870000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([375000000000], [6270000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([45000000000], [1335000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([180000000000], [6750000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    (.next ([0], [1440000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-480000000000],
    [7410000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-645000000000], [6600000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-840000000000], [7080000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) fan54Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan54Owner0Part3 : FanWitness := (.next ([6240000000000], [1500000000000]) (some (8, 3, 10))
    (some (8, 3, 10)) (.next ([300000000000], [75000000000]) (some (8, 3, 10)) (some (8, 3, 10))
    (.next ([3390000000000], [930000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
    ([1365000000000], [375000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([960000000000],
    [285000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([5955000000000], [2085000000000])
    (some (8, 3, 10)) (some (8, 3, 10)) (.next ([5580000000000], [2385000000000]) (some (8, 3, 10))
    (some (8, 3, 10)) (.next ([4620000000000], [2025000000000]) (some (8, 3, 10)) (some (8, 3, 10))
    (.next ([4905000000000], [2220000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
    ([5370000000000], [2460000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([5100000000000],
    [2400000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([1230000000000], [585000000000])
    (some (8, 3, 10)) (some (8, 3, 10)) (.next ([375000000000], [210000000000]) (some (8, 3, 10))
    (some (8, 3, 10)) (.next ([4905000000000], [2880000000000]) (some (8, 3, 10)) (some (8, 3, 10))
    (.next ([285000000000], [195000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
    ([885000000000], [660000000000]) (some (8, 3, 10)) (some (9, 3, 10)) (.next ([4620000000000],
    [3465000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([480000000000], [375000000000])
    (some (9, 3, 10)) (some (9, 3, 10)) (.next ([585000000000], [480000000000]) (some (9, 3, 10))
    (some (9, 3, 10)) (.next ([4245000000000], [3765000000000]) (some (9, 3, 10)) (some (9, 3, 10))
    (.next ([195000000000], [180000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next
    ([300000000000], [285000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([4035000000000],
    [3840000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([750000000000], [870000000000])
    (some (0, 3, 10)) (some (0, 3, 10)) fan54Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan55Owner1Part0 : FanWitness := (.next ([1440000000000, 9000000000000], [1440000000000,
    9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([1875000000000], [2805000000000,
    -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([1875000000000], [4245000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([1590000000000], [4290000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([960000000000], [3375000000000]) (some (0, 2, 4)) (some (6, 2, 4))
    (.next ([480000000000, 9000000000000], [5250000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([435000000000, -9000000000000], [5685000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2,
    4)) (.next ([0], [1440000000000, 9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-720000000000], [4965000000000]) (some (6, 2, 4)) (some (6, 2, 5)) (.next ([-960000000000],
    [5250000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-1440000000000, -9000000000000],
    [6840000000000, 0]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-960000000000, 0],
    [3810000000000, -9000000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-915000000000],
    [3330000000000]) (some (6, 2, 0)) (some (6, 2, 0)) (.next ([-960000000000], [3465000000000])
    (some (6, 2, 0)) (some (6, 2, 0)) (.next ([-3375000000000], [8535000000000]) (some (6, 2, 0))
    (some (6, 2, 0)) (.next ([-1935000000000, 9000000000000], [4335000000000]) (some (6, 2, 0))
    (some (6, 2, 0)) (.next ([-2460000000000], [5205000000000]) (some (6, 2, 0)) (some (6, 2, 0))
    (.next ([-1440000000000, -9000000000000], [2880000000000, 18000000000000]) (some (6, 2, 0))
    (some (6, 2, 0)) (.next ([-2805000000000, 9000000000000], [4680000000000, -9000000000000]) (some
    (6, 2, 0)) (some (6, 2, 0)) (.next ([-4245000000000], [6120000000000]) (some (6, 2, 0)) (some
    (6, 3, 0)) (.next ([-4290000000000], [5880000000000]) (some (6, 3, 0)) (some (6, 3, 0)) (.next
    ([-3375000000000], [4335000000000]) (some (6, 3, 0)) (some (6, 3, 0)) (.next ([-5250000000000],
    [5730000000000, 9000000000000]) (some (6, 3, 0)) (some (6, 3, 0)) (.next ([-5685000000000,
    -9000000000000], [6120000000000, 0]) (some (6, 3, 0)) (some (6, 3, 0)) (.terminal (some (6, 3,
    0)) (some (6, 3, 0)) (some (6, 3, 0)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan55Owner2Part0 : FanWitness := (.next ([6840000000000], [2160000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([1200000000000], [420000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([3405000000000], [1620000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([3360000000000, 9000000000000], [2385000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([2160000000000, 9000000000000], [1965000000000, -9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([2715000000000], [2880000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([1920000000000], [3825000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1095000000000], [4080000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1440000000000,
    9000000000000], [5745000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([720000000000],
    [3405000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1095000000000], [7905000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0], [3825000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-720000000000, 9000000000000], [7560000000000, -9000000000000]) (some (0, 5, 3))
    (some (0, 5, 4)) (.next ([-2160000000000], [9000000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-420000000000], [1620000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-1620000000000], [5025000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2385000000000,
    9000000000000], [5745000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1965000000000,
    9000000000000], [4125000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2880000000000],
    [5595000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3825000000000], [5745000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4080000000000], [5175000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-5745000000000, 0], [7185000000000, 9000000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-3405000000000], [4125000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-7905000000000], [9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some
    (0, 5, 4)) (some (5, 5, 0)) (some (5, 5, 4)))))))))))))))))))))))))))

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3600000000000], [1125000000000]) (some (5, 0,
      2)) (some (5, 1, 2)) fan48Owner4Part0)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_9 : ExcludedOn (model48.B 9 ++ [step48.q]) 9000000000000 (model48.caps 9)
    (model48.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked48 : StepValid model48 9000000000000 step48 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded48_0
    · exact excluded48_1
    · exact excluded48_2
    · exact (hj rfl).elim
    · exact excluded48_4
    · exact excluded48_5
    · exact excluded48_6
    · exact excluded48_7
    · exact excluded48_8
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded49_0 : ExcludedOn (model49.B 0 ++ [step49.q]) 9000000000000 (model49.caps 0)
    (model49.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_1 : ExcludedOn (model49.B 1 ++ [step49.q]) 9000000000000 (model49.caps 1)
    (model49.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_3 : ExcludedOn (model49.B 3 ++ [step49.q]) 9000000000000 (model49.caps 3)
    (model49.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [360000000000]) (some (5, 0, 2))
      (some (6, 0, 2)) (.next ([5598000000000], [435000000000]) (some (6, 0, 2)) (some (6, 0, 2))
      (.next ([5598000000000, 9000000000000], [810000000000, -9000000000000]) (some (6, 0, 2)) (some
      (6, 0, 2)) (.next ([3000000000000], [678000000000]) (some (6, 0, 2)) (some (6, 0, 2)) (.next
      ([1440000000000], [375000000000]) (some (6, 0, 2)) (some (6, 0, 2)) (.next ([3735000000000],
      [1995000000000]) (some (6, 0, 2)) (some (6, 0, 2)) (.next ([4158000000000], [2250000000000])
      (some (6, 0, 2)) (some (6, 0, 7)) (.next ([1005000000000], [960000000000]) (some (6, 0, 7))
      (some (6, 0, 7)) (.next ([960000000000], [1290000000000]) (some (6, 0, 7)) (some (6, 0, 7))
      (.next ([1770000000000], [3000000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
      ([1920000000000], [3435000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([3255000000000],
      [6090000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([2250000000000], [5130000000000])
      (some (6, 0, 7)) (some (6, 0, 7)) (.next ([150000000000], [435000000000]) (some (6, 0, 7))
      (some (6, 0, 7)) (.next ([1815000000000], [5715000000000]) (some (6, 0, 7)) (some (6, 0, 7))
      (.next ([375000000000], [1440000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
      ([1440000000000, 9000000000000], [6090000000000]) (some (6, 0, 7)) (some (6, 0, 7))
      fan49Owner3Part0)))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_4 : ExcludedOn (model49.B 4 ++ [step49.q]) 9000000000000 (model49.caps 4)
    (model49.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_6 : ExcludedOn (model49.B 6 ++ [step49.q]) 9000000000000 (model49.caps 6)
    (model49.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_7 : ExcludedOn (model49.B 7 ++ [step49.q]) 9000000000000 (model49.caps 7)
    (model49.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_8 : ExcludedOn (model49.B 8 ++ [step49.q]) 9000000000000 (model49.caps 8)
    (model49.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_9 : ExcludedOn (model49.B 9 ++ [step49.q]) 9000000000000 (model49.caps 9)
    (model49.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked49 : StepValid model49 9000000000000 step49 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded49_0
    · exact excluded49_1
    · exact (hj rfl).elim
    · exact excluded49_3
    · exact excluded49_4
    · exact excluded49_5
    · exact excluded49_6
    · exact excluded49_7
    · exact excluded49_8
    · exact excluded49_9
theorem next49 : model49.insert step49 = model50 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded50_0 : ExcludedOn (model50.B 0 ++ [step50.q]) 9000000000000 (model50.caps 0)
    (model50.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_1 : ExcludedOn (model50.B 1 ++ [step50.q]) 9000000000000 (model50.caps 1)
    (model50.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_3 : ExcludedOn (model50.B 3 ++ [step50.q]) 9000000000000 (model50.caps 3)
    (model50.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [360000000000]) (some (5, 0, 7))
      (some (6, 0, 7)) (.next ([5598000000000], [435000000000]) (some (6, 0, 7)) (some (6, 0, 7))
      (.next ([5598000000000, 9000000000000], [810000000000, -9000000000000]) (some (6, 0, 7)) (some
      (6, 0, 7)) (.next ([3000000000000], [678000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
      ([7080000000000], [2265000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([3825000000000,
      0], [1815000000000, -9000000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
      ([3450000000000], [1815000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([4830000000000],
      [2583000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([4158000000000], [2250000000000])
      (some (6, 0, 7)) (some (6, 0, 7)) (.next ([2865000000000], [1965000000000]) (some (6, 0, 7))
      (some (6, 0, 7)) (.next ([3825000000000], [3255000000000]) (some (6, 0, 7)) (some (6, 0, 7))
      (.next ([1830000000000], [1905000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
      ([960000000000], [1290000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([1770000000000],
      [3000000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([1920000000000], [3435000000000])
      (some (6, 0, 7)) (some (6, 0, 7)) (.next ([1920000000000, 9000000000000], [3810000000000,
      -9000000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([2250000000000], [5130000000000])
      (some (6, 0, 7)) (some (6, 0, 7)) (.next ([150000000000], [435000000000]) (some (6, 0, 7))
      (some (6, 0, 7)) (.next ([1815000000000], [5715000000000]) (some (6, 0, 7)) (some (6, 0, 7))
      (.next ([375000000000], [1440000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
      ([1440000000000, 9000000000000], [6090000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
      ([318000000000], [1932000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([480000000000],
      [5250000000000]) (some (6, 0, 7)) (some (6, 1, 7)) fan50Owner3Part0))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_4 : ExcludedOn (model50.B 4 ++ [step50.q]) 9000000000000 (model50.caps 4)
    (model50.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_5 : ExcludedOn (model50.B 5 ++ [step50.q]) 9000000000000 (model50.caps 5)
    (model50.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_6 : ExcludedOn (model50.B 6 ++ [step50.q]) 9000000000000 (model50.caps 6)
    (model50.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_7 : ExcludedOn (model50.B 7 ++ [step50.q]) 9000000000000 (model50.caps 7)
    (model50.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_8 : ExcludedOn (model50.B 8 ++ [step50.q]) 9000000000000 (model50.caps 8)
    (model50.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_9 : ExcludedOn (model50.B 9 ++ [step50.q]) 9000000000000 (model50.caps 9)
    (model50.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked50 : StepValid model50 9000000000000 step50 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded50_0
    · exact excluded50_1
    · exact (hj rfl).elim
    · exact excluded50_3
    · exact excluded50_4
    · exact excluded50_5
    · exact excluded50_6
    · exact excluded50_7
    · exact excluded50_8
    · exact excluded50_9
theorem next50 : model50.insert step50 = model51 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded51_0 : ExcludedOn (model51.B 0 ++ [step51.q]) 9000000000000 (model51.caps 0)
    (model51.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_1 : ExcludedOn (model51.B 1 ++ [step51.q]) 9000000000000 (model51.caps 1)
    (model51.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6600000000000], [1065000000000]) (some (4, 0,
      1)) (some (4, 0, 2)) (.next ([2895000000000, -9000000000000], [480000000000, 9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([2400000000000, 9000000000000], [1935000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1440000000000, 9000000000000],
      [1440000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([4665000000000,
      9000000000000], [5400000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3225000000000, 0],
      [3960000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3225000000000],
      [5400000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([960000000000], [3375000000000])
      (some (4, 1, 2)) (some (4, 1, 4)) (.next ([0], [1440000000000, 9000000000000]) (some (4, 1,
      4)) (some (4, 1, 4)) (.next ([-1065000000000], [7665000000000]) (some (4, 1, 4)) (some (4, 1,
      4)) (.next ([-480000000000, -9000000000000], [3375000000000, 0]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-1935000000000, 9000000000000], [4335000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-1440000000000, -9000000000000], [2880000000000, 18000000000000]) (some (0, 1,
      4)) (some (0, 1, 4)) (.next ([-5400000000000], [10065000000000, 9000000000000]) (some (0, 1,
      4)) (some (0, 1, 4)) (.next ([-3960000000000, 9000000000000], [7185000000000, -9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-5400000000000], [8625000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-3375000000000], [4335000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded51_2 : ExcludedOn (model51.B 2 ++ [step51.q]) 9000000000000 (model51.caps 2)
    (model51.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_3 : ExcludedOn (model51.B 3 ++ [step51.q]) 9000000000000 (model51.caps 3)
    (model51.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_4 : ExcludedOn (model51.B 4 ++ [step51.q]) 9000000000000 (model51.caps 4)
    (model51.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_5 : ExcludedOn (model51.B 5 ++ [step51.q]) 9000000000000 (model51.caps 5)
    (model51.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_6 : ExcludedOn (model51.B 6 ++ [step51.q]) 9000000000000 (model51.caps 6)
    (model51.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_8 : ExcludedOn (model51.B 8 ++ [step51.q]) 9000000000000 (model51.caps 8)
    (model51.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_9 : ExcludedOn (model51.B 9 ++ [step51.q]) 9000000000000 (model51.caps 9)
    (model51.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked51 : StepValid model51 9000000000000 step51 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded51_0
    · exact excluded51_1
    · exact excluded51_2
    · exact excluded51_3
    · exact excluded51_4
    · exact excluded51_5
    · exact excluded51_6
    · exact (hj rfl).elim
    · exact excluded51_8
    · exact excluded51_9
theorem next51 : model51.insert step51 = model52 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded52_0 : ExcludedOn (model52.B 0 ++ [step52.q]) 9000000000000 (model52.caps 0)
    (model52.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_2 : ExcludedOn (model52.B 2 ++ [step52.q]) 9000000000000 (model52.caps 2)
    (model52.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1200000000000], [420000000000]) (some (0, 0, 5))
      (some (0, 1, 5)) (.next ([3405000000000], [1620000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([3360000000000, 9000000000000], [2385000000000, -9000000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([2160000000000, 9000000000000], [1965000000000, -9000000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([4710000000000], [4785000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([1920000000000], [3825000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([960000000000, 0], [2310000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([1305000000000], [3165000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1440000000000, 9000000000000], [5745000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([720000000000], [3405000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([885000000000],
      [4785000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0], [3825000000000]) (some (0, 1,
      3)) (some (0, 5, 3)) (.next ([-420000000000], [1620000000000]) (some (0, 5, 3)) (some (0, 5,
      4)) (.next ([-1620000000000], [5025000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2385000000000, 9000000000000], [5745000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-1965000000000, 9000000000000], [4125000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-4785000000000], [9495000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3825000000000], [5745000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2310000000000,
      9000000000000], [3270000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3165000000000], [4470000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-5745000000000,
      0], [7185000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3405000000000], [4125000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-4785000000000], [5670000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
      4)) (some (0, 5, 0)) (some (0, 5, 4))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_3 : ExcludedOn (model52.B 3 ++ [step52.q]) 9000000000000 (model52.caps 3)
    (model52.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_4 : ExcludedOn (model52.B 4 ++ [step52.q]) 9000000000000 (model52.caps 4)
    (model52.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_5 : ExcludedOn (model52.B 5 ++ [step52.q]) 9000000000000 (model52.caps 5)
    (model52.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_6 : ExcludedOn (model52.B 6 ++ [step52.q]) 9000000000000 (model52.caps 6)
    (model52.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_7 : ExcludedOn (model52.B 7 ++ [step52.q]) 9000000000000 (model52.caps 7)
    (model52.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4185000000000], [150000000000]) (some (2, 4, 1))
      (some (3, 4, 2)) (.next ([5400000000000], [375000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([3960000000000, -9000000000000], [375000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([5250000000000], [3270000000000, -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([5250000000000], [4710000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([3810000000000, -9000000000000], [4710000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([1065000000000, 9000000000000], [4335000000000, -9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([0], [1440000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-150000000000], [4335000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-375000000000],
      [5775000000000]) (some (0, 4, 2)) (some (4, 4, 2)) (.next ([-375000000000, 0], [4335000000000,
      -9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-3270000000000, 9000000000000],
      [8520000000000, -9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-4710000000000],
      [9960000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-4710000000000, 0],
      [8520000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-4335000000000,
      9000000000000], [5400000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2))
      (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_8 : ExcludedOn (model52.B 8 ++ [step52.q]) 9000000000000 (model52.caps 8)
    (model52.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_9 : ExcludedOn (model52.B 9 ++ [step52.q]) 9000000000000 (model52.caps 9)
    (model52.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked52 : StepValid model52 9000000000000 step52 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded52_0
    · exact (hj rfl).elim
    · exact excluded52_2
    · exact excluded52_3
    · exact excluded52_4
    · exact excluded52_5
    · exact excluded52_6
    · exact excluded52_7
    · exact excluded52_8
    · exact excluded52_9
theorem next52 : model52.insert step52 = model53 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded53_1 : ExcludedOn (model53.B 1 ++ [step53.q]) 9000000000000 (model53.caps 1)
    (model53.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2895000000000, -9000000000000], [480000000000,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next ([4290000000000], [960000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2850000000000, -9000000000000], [960000000000, 0])
      (some (0, 5, 3)) (some (0, 5, 3)) fan53Owner1Part0))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded53_2 : ExcludedOn (model53.B 2 ++ [step53.q]) 9000000000000 (model53.caps 2)
    (model53.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_3 : ExcludedOn (model53.B 3 ++ [step53.q]) 9000000000000 (model53.caps 3)
    (model53.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_4 : ExcludedOn (model53.B 4 ++ [step53.q]) 9000000000000 (model53.caps 4)
    (model53.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_5 : ExcludedOn (model53.B 5 ++ [step53.q]) 9000000000000 (model53.caps 5)
    (model53.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_6 : ExcludedOn (model53.B 6 ++ [step53.q]) 9000000000000 (model53.caps 6)
    (model53.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2940000000000, 9000000000000], [480000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([1500000000000], [1920000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1920000000000], [4140000000000, -9000000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1440000000000, 9000000000000], [7560000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1440000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-480000000000, 9000000000000],
      [3420000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1920000000000], [3420000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4140000000000, 9000000000000], [6060000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7560000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_7 : ExcludedOn (model53.B 7 ++ [step53.q]) 9000000000000 (model53.caps 7)
    (model53.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_8 : ExcludedOn (model53.B 8 ++ [step53.q]) 9000000000000 (model53.caps 8)
    (model53.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_9 : ExcludedOn (model53.B 9 ++ [step53.q]) 9000000000000 (model53.caps 9)
    (model53.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked53 : StepValid model53 9000000000000 step53 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded53_1
    · exact excluded53_2
    · exact excluded53_3
    · exact excluded53_4
    · exact excluded53_5
    · exact excluded53_6
    · exact excluded53_7
    · exact excluded53_8
    · exact excluded53_9
theorem next53 : model53.insert step53 = model54 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded54_0 : ExcludedOn (model54.B 0 ++ [step54.q]) 9000000000000 (model54.caps 0)
    (model54.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6930000000000], [480000000000]) (some (8, 3,
      10)) (some (8, 3, 10)) (.next ([5955000000000], [645000000000]) (some (8, 3, 10)) (some (8, 3,
      10)) (.next ([6240000000000], [840000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
      ([6435000000000], [1020000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
      ([6645000000000], [1065000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
      ([6270000000000], [1365000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
      ([6060000000000], [1440000000000]) (some (8, 3, 10)) (some (8, 3, 10))
      fan54Owner0Part3))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded54_2 : ExcludedOn (model54.B 2 ++ [step54.q]) 9000000000000 (model54.caps 2)
    (model54.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_3 : ExcludedOn (model54.B 3 ++ [step54.q]) 9000000000000 (model54.caps 3)
    (model54.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_4 : ExcludedOn (model54.B 4 ++ [step54.q]) 9000000000000 (model54.caps 4)
    (model54.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_5 : ExcludedOn (model54.B 5 ++ [step54.q]) 9000000000000 (model54.caps 5)
    (model54.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_6 : ExcludedOn (model54.B 6 ++ [step54.q]) 9000000000000 (model54.caps 6)
    (model54.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4320000000000, 9000000000000], [435000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2880000000000], [1875000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1875000000000], [2805000000000, -9000000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1440000000000, 9000000000000], [7560000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1440000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-435000000000, 9000000000000],
      [4755000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1875000000000], [4755000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2805000000000, 9000000000000], [4680000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7560000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_7 : ExcludedOn (model54.B 7 ++ [step54.q]) 9000000000000 (model54.caps 7)
    (model54.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_8 : ExcludedOn (model54.B 8 ++ [step54.q]) 9000000000000 (model54.caps 8)
    (model54.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_9 : ExcludedOn (model54.B 9 ++ [step54.q]) 9000000000000 (model54.caps 9)
    (model54.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked54 : StepValid model54 9000000000000 step54 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded54_0
    · exact (hj rfl).elim
    · exact excluded54_2
    · exact excluded54_3
    · exact excluded54_4
    · exact excluded54_5
    · exact excluded54_6
    · exact excluded54_7
    · exact excluded54_8
    · exact excluded54_9
theorem next54 : model54.insert step54 = model55 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded55_1 : ExcludedOn (model55.B 1 ++ [step55.q]) 9000000000000 (model55.caps 1)
    (model55.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4245000000000], [720000000000]) (some (0, 6, 3))
      (some (0, 6, 4)) (.next ([4290000000000], [960000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([5400000000000, -9000000000000], [1440000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([2850000000000, -9000000000000], [960000000000, 0]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([2415000000000], [915000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([2505000000000], [960000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([5160000000000], [3375000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([2400000000000,
      9000000000000], [1935000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([2745000000000], [2460000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      fan55Owner1Part0)))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded55_2 : ExcludedOn (model55.B 2 ++ [step55.q]) 9000000000000 (model55.caps 2)
    (model55.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6840000000000, 0], [720000000000,
      -9000000000000]) (some (0, 5, 5)) (some (0, 5, 5)) fan55Owner2Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded55_3 : ExcludedOn (model55.B 3 ++ [step55.q]) 9000000000000 (model55.caps 3)
    (model55.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_4 : ExcludedOn (model55.B 4 ++ [step55.q]) 9000000000000 (model55.caps 4)
    (model55.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_5 : ExcludedOn (model55.B 5 ++ [step55.q]) 9000000000000 (model55.caps 5)
    (model55.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_6 : ExcludedOn (model55.B 6 ++ [step55.q]) 9000000000000 (model55.caps 6)
    (model55.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3600000000000, 9000000000000], [5400000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2160000000000], [6840000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1440000000000, 9000000000000], [5400000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1440000000000, 9000000000000],
      [7560000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [1440000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-5400000000000,
      9000000000000], [9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-6840000000000],
      [9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5400000000000, 9000000000000],
      [6840000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7560000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1,
      3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_7 : ExcludedOn (model55.B 7 ++ [step55.q]) 9000000000000 (model55.caps 7)
    (model55.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_8 : ExcludedOn (model55.B 8 ++ [step55.q]) 9000000000000 (model55.caps 8)
    (model55.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_9 : ExcludedOn (model55.B 9 ++ [step55.q]) 9000000000000 (model55.caps 9)
    (model55.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked55 : StepValid model55 9000000000000 step55 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded55_1
    · exact excluded55_2
    · exact excluded55_3
    · exact excluded55_4
    · exact excluded55_5
    · exact excluded55_6
    · exact excluded55_7
    · exact excluded55_8
    · exact excluded55_9
theorem next55 : model55.insert step55 = model56 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext160000170000
end ConwaySoifer.Simplified.Certificates
