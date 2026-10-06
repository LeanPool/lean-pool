/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown230000240000
import Mathlib.Tactic.FinCases

/-!
# Aown 230000 240000 3

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
namespace Aown230000240000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part0 : FanWitness := (.next ([-4815000000000], [6930000000000]) (some (1, 7, 10))
    (some (1, 7, 10)) (.next ([-930000000000], [1305000000000]) (some (1, 7, 10)) (some (1, 7, 10))
    (.next ([-3810000000000], [5235000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-4815000000000], [6615000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-4125000000000], [5550000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-2280000000000], [3030000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next ([-525000000000],
    [690000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next ([-5625000000000], [7269000000000])
    (some (1, 7, 10)) (some (1, 7, 10)) (.next ([-2370000000000], [3060000000000]) (some (1, 7, 10))
    (some (1, 7, 10)) (.next ([-1350000000000], [1725000000000]) (some (1, 7, 10)) (some (1, 7, 10))
    (.next ([-4785000000000], [5895000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-2784000000000], [3399000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-1440000000000], [1755000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-5925000000000], [7170000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-1065000000000], [1275000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-5190000000000], [5925000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-2685000000000], [3060000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-2685000000000], [3000000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next ([-375000000000],
    [405000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next ([-5400000000000], [5760000000000])
    (some (1, 7, 10)) (some (2, 7, 10)) (.next ([-6000000000000], [6339000000000]) (some (2, 7, 10))
    (some (2, 7, 10)) (.next ([-1350000000000], [1410000000000]) (some (2, 7, 10)) (some (2, 7, 10))
    (.next ([-5535000000000], [5610000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next
    ([-6315000000000], [6339000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.terminal (some (2, 7,
    10)) (some (2, 7, 10)) (some (2, 7, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part1 : FanWitness := (.next ([-1755000000000], [6240000000000]) (some (12, 7, 9))
    (some (12, 7, 9)) (.next ([-1815000000000], [6300000000000]) (some (12, 7, 9)) (some (12, 7, 9))
    (.next ([-345000000000], [1125000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next
    ([-315000000000], [975000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-165000000000],
    [375000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-660000000000], [1440000000000])
    (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-3060000000000], [6615000000000]) (some (12, 7, 9))
    (some (12, 7, 9)) (.next ([-315000000000], [660000000000]) (some (12, 7, 9)) (some (12, 7, 9))
    (.next ([-3375000000000], [6930000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next
    ([-375000000000], [750000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-2505000000000],
    [4860000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-150000000000], [285000000000])
    (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-1245000000000], [2280000000000]) (some (12, 7, 9))
    (some (12, 7, 9)) (.next ([-4035000000000], [7275000000000]) (some (1, 7, 9)) (some (1, 7, 9))
    (.next ([-210000000000], [375000000000]) (some (1, 7, 9)) (some (1, 7, 9)) (.next
    ([-930000000000], [1620000000000]) (some (1, 7, 9)) (some (1, 7, 9)) (.next ([-1620000000000],
    [2685000000000]) (some (1, 7, 9)) (some (1, 7, 9)) (.next ([-4440000000000], [7305000000000])
    (some (1, 7, 9)) (some (1, 7, 9)) (.next ([-690000000000], [1065000000000]) (some (1, 7, 9))
    (some (1, 7, 9)) (.next ([-4650000000000], [7140000000000]) (some (1, 7, 9)) (some (1, 7, 10))
    (.next ([-60000000000], [90000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-1065000000000], [1590000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-4785000000000], [6990000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-1995000000000], [2895000000000]) (some (1, 7, 10)) (some (1, 7, 10))
    fan24Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part2 : FanWitness := (.next ([75000000000], [5535000000000]) (some (12, 5, 9)) (some
    (12, 5, 9)) (.next ([24000000000], [6315000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next
    ([0], [1440000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next ([-15000000000],
    [5565000000000]) (some (12, 5, 9)) (some (12, 6, 9)) (.next ([-60000000000], [6300000000000])
    (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-375000000000], [6615000000000]) (some (12, 6, 9))
    (some (12, 6, 9)) (.next ([-330000000000], [5565000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    (.next ([-636000000000], [6660000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-1035000000000], [6960000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-1041000000000], [6690000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-765000000000],
    [4914000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-315000000000], [1755000000000])
    (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-135000000000], [750000000000]) (some (12, 6, 9))
    (some (12, 6, 9)) (.next ([-1251000000000], [6525000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    (.next ([-1440000000000], [6990000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-1386000000000], [6375000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-1065000000000], [4815000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-1416000000000], [6315000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-1416000000000], [6000000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-1650000000000], [6825000000000]) (some (12, 6, 9)) (some (12, 7, 9)) (.next ([-99000000000],
    [399000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-1785000000000], [6675000000000])
    (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-1815000000000], [6615000000000]) (some (12, 7, 9))
    (some (12, 7, 9)) (.next ([-285000000000], [1035000000000]) (some (12, 7, 9)) (some (12, 7, 9))
    fan24Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part3 : FanWitness := (.next ([2205000000000], [4785000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([900000000000], [1995000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([2115000000000], [4815000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([375000000000], [930000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([1425000000000],
    [3810000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([1800000000000], [4815000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) (.next ([1425000000000], [4125000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([750000000000], [2280000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([165000000000], [525000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([1644000000000], [5625000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([690000000000],
    [2370000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([375000000000], [1350000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) (.next ([1110000000000], [4785000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([615000000000], [2784000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([315000000000], [1440000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([1245000000000], [5925000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([210000000000],
    [1065000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([735000000000], [5190000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) (.next ([375000000000], [2685000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([315000000000], [2685000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([30000000000], [375000000000]) (some (12, 5, 8)) (some (12, 5, 9)) (.next
    ([360000000000], [5400000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next ([339000000000],
    [6000000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next ([60000000000], [1350000000000])
    (some (12, 5, 9)) (some (12, 5, 9)) fan24Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner0Part4 : FanWitness := (.next ([4800000000000], [1815000000000]) (some (10, 2, 8))
    (some (10, 2, 8)) (.next ([750000000000], [285000000000]) (some (10, 2, 8)) (some (10, 2, 8))
    (.next ([4485000000000], [1755000000000]) (some (10, 2, 8)) (some (10, 2, 8)) (.next
    ([4485000000000], [1815000000000]) (some (10, 2, 8)) (some (10, 2, 8)) (.next ([780000000000],
    [345000000000]) (some (10, 2, 8)) (some (10, 2, 8)) (.next ([660000000000], [315000000000])
    (some (10, 2, 8)) (some (10, 2, 8)) (.next ([210000000000], [165000000000]) (some (10, 2, 8))
    (some (10, 2, 8)) (.next ([780000000000], [660000000000]) (some (10, 2, 8)) (some (10, 3, 8))
    (.next ([3555000000000], [3060000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next
    ([345000000000], [315000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next ([3555000000000],
    [3375000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next ([375000000000], [375000000000])
    (some (10, 3, 8)) (some (10, 3, 8)) (.next ([2355000000000], [2505000000000]) (some (10, 3, 8))
    (some (10, 3, 8)) (.next ([135000000000], [150000000000]) (some (10, 3, 8)) (some (12, 3, 8))
    (.next ([1035000000000], [1245000000000]) (some (12, 3, 8)) (some (12, 4, 8)) (.next
    ([3240000000000], [4035000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([165000000000],
    [210000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([690000000000], [930000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([1065000000000], [1620000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([2865000000000], [4440000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([375000000000], [690000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([2490000000000], [4650000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([30000000000],
    [60000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([525000000000], [1065000000000])
    (some (12, 4, 8)) (some (12, 5, 8)) fan24Owner0Part3))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner2Part0 : FanWitness := (.next ([3750000000000], [2385000000000]) (some (0, 4, 2))
    (some (0, 4, 2)) (.next ([3555000000000], [2730000000000]) (some (0, 1, 2)) (some (0, 1, 2))
    (.next ([3555000000000, -9000000000000], [3105000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2))
    (.next ([150000000000], [195000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([1035000000000, -9000000000000], [2340000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1,
    2)) (.next ([2055000000000], [5070000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([1710000000000], [5220000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1065000000000],
    [3375000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([1335000000000, 0], [5595000000000,
    -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0], [3405000000000,
    9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, -9000000000000], [375000000000,
    0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1350000000000, -9000000000000], [8475000000000,
    9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1695000000000, -9000000000000],
    [8625000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2070000000000,
    -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-195000000000,
    -9000000000000], [720000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2385000000000],
    [6135000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2730000000000], [6285000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3105000000000, 0], [6660000000000, -9000000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-195000000000], [345000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-2340000000000, -9000000000000], [3375000000000]) (some (0, 1, 3))
    (some (0, 2, 3)) (.next ([-5070000000000], [7125000000000]) (some (0, 2, 3)) (some (4, 2, 3))
    (.next ([-5220000000000], [6930000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
    ([-3375000000000], [4440000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-5595000000000,
    9000000000000], [6930000000000, -9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal
    (some (4, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner2Part1 : FanWitness := (.next ([525000000000, -9000000000000], [195000000000,
    9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3750000000000], [2385000000000])
    (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3555000000000], [2730000000000]) (some (0, 1, 2))
    (some (0, 1, 2)) (.next ([3555000000000, -9000000000000], [3105000000000, 0]) (some (0, 1, 2))
    (some (0, 1, 2)) (.next ([150000000000], [195000000000]) (some (0, 1, 2)) (some (0, 1, 2))
    (.next ([2055000000000], [5070000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([1035000000000, -9000000000000], [2340000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1,
    2)) (.next ([1710000000000], [5220000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([1065000000000], [3375000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([1335000000000, 0],
    [5595000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
    [3405000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1350000000000,
    -9000000000000], [8475000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-1695000000000, -9000000000000], [8625000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1,
    3)) (.next ([-2070000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1,
    3)) (.next ([-195000000000, -9000000000000], [720000000000, 0]) (some (0, 1, 3)) (some (0, 1,
    3)) (.next ([-2385000000000], [6135000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-2730000000000], [6285000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3105000000000,
    0], [6660000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-195000000000],
    [345000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5070000000000], [7125000000000])
    (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2340000000000, -9000000000000], [3375000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5220000000000], [6930000000000]) (some (0, 2, 3))
    (some (4, 2, 3)) (.next ([-3375000000000], [4440000000000]) (some (4, 2, 3)) (some (4, 2, 3))
    (.next ([-5595000000000, 9000000000000], [6930000000000, -9000000000000]) (some (4, 2, 3)) (some
    (4, 2, 3)) (.terminal (some (4, 2, 3)) (some (4, 2, 0)) (some (4, 2,
    3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner2Part2 : FanWitness := (.next ([525000000000, -9000000000000], [195000000000,
    9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([3555000000000], [2730000000000])
    (some (0, 1, 2)) (some (0, 1, 2)) (.next ([3555000000000, -9000000000000], [3105000000000, 0])
    (some (0, 1, 2)) (some (0, 1, 2)) (.next ([150000000000], [195000000000]) (some (0, 1, 2)) (some
    (0, 1, 2)) (.next ([2055000000000], [5070000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([1035000000000, -9000000000000], [2340000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1,
    2)) (.next ([1710000000000], [5220000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([1065000000000], [3375000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([1335000000000, 0],
    [5595000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
    [3405000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1350000000000,
    -9000000000000], [8475000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-1695000000000, -9000000000000], [8625000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1,
    3)) (.next ([0, -9000000000000], [375000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-2070000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-2385000000000], [6135000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-195000000000,
    -9000000000000], [720000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2730000000000],
    [6285000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3105000000000, 0], [6660000000000,
    -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-195000000000], [345000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5070000000000], [7125000000000]) (some (0, 1, 3))
    (some (0, 2, 3)) (.next ([-2340000000000, -9000000000000], [3375000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([-5220000000000], [6930000000000]) (some (0, 2, 3)) (some (4, 2, 3))
    (.next ([-3375000000000], [4440000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
    ([-5595000000000, 9000000000000], [6930000000000, -9000000000000]) (some (4, 2, 3)) (some (4, 2,
    3)) (.terminal (some (4, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5550000000000], [15000000000]) (some (10, 2, 7))
      (some (10, 2, 7)) (.next ([6240000000000], [60000000000]) (some (10, 2, 7)) (some (10, 2, 7))
      (.next ([6240000000000], [375000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next
      ([5235000000000], [330000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next ([6024000000000],
      [636000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next ([5925000000000], [1035000000000])
      (some (10, 2, 7)) (some (10, 2, 7)) (.next ([5649000000000], [1041000000000]) (some (10, 2,
      7)) (some (10, 2, 7)) (.next ([4149000000000], [765000000000]) (some (10, 2, 7)) (some (10, 2,
      7)) (.next ([1440000000000], [315000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next
      ([615000000000], [135000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next ([5274000000000],
      [1251000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next ([5550000000000], [1440000000000])
      (some (10, 2, 7)) (some (10, 2, 7)) (.next ([4989000000000], [1386000000000]) (some (10, 2,
      7)) (some (10, 2, 7)) (.next ([3750000000000], [1065000000000]) (some (10, 2, 7)) (some (10,
      2, 7)) (.next ([4899000000000], [1416000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next
      ([4584000000000], [1416000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next
      ([5175000000000], [1650000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next ([300000000000],
      [99000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next ([4890000000000], [1785000000000])
      (some (10, 2, 7)) (some (10, 2, 8)) fan24Owner0Part4))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7005000000000], [1995000000000]) (some (3, 0,
      4)) (some (3, 1, 4)) (.next ([4920000000000, -9000000000000], [2070000000000, 9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([4935000000000, -9000000000000], [4065000000000,
      9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2070000000000, 9000000000000],
      [2070000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2070000000000,
      9000000000000], [4920000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([75000000000, 9000000000000], [6930000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1,
      4)) (.next ([15000000000], [1995000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0, 0],
      [2070000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-1995000000000],
      [9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2070000000000, -9000000000000],
      [6990000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-4065000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 4)) (some (0, 2, 4)) (.next
      ([-2070000000000, -9000000000000], [4140000000000, 18000000000000]) (some (0, 2, 4)) (some (0,
      2, 4)) (.next ([-4920000000000, 9000000000000], [6990000000000]) (some (0, 2, 4)) (some (0, 2,
      4)) (.next ([-6930000000000, 9000000000000], [7005000000000]) (some (0, 2, 4)) (some (0, 2,
      4)) (.next ([-1995000000000], [2010000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal
      (some (0, 2, 3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_8 : ExcludedOn (model24.B 8 ++ [step24.q]) 9000000000000 (model24.caps 8)
    (model24.ord 8) 0 1 100 := by
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

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7695000000000, 9000000000000], [1035000000000,
      -9000000000000]) none none (.next ([3555000000000, -9000000000000], [3105000000000, 0]) (some
      (3, 1, 2)) (some (3, 1, 2)) (.next ([2070000000000, 9000000000000], [2070000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2070000000000, 9000000000000],
      [2730000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([825000000000],
      [7905000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0], [6870000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1035000000000, 9000000000000],
      [8730000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3105000000000, 0],
      [6660000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2070000000000,
      -9000000000000], [4140000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2730000000000, 9000000000000], [4800000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-7905000000000], [8730000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) none none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (13) (19) (1900) (.witnessedFan (.next ([375000000000,
      -9000000000000], [0, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([7125000000000,
      0], [1350000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([6930000000000,
      0], [1695000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([6930000000000,
      -9000000000000], [2070000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([525000000000, -9000000000000], [195000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) fan25Owner2Part0)))))) (.split (31902) (43985) (46626) (4662600) (.witnessedFan (.next
      ([7125000000000, 0], [1350000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([6930000000000, 0], [1695000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([6930000000000, -9000000000000], [2070000000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) fan25Owner2Part1)))) (.witnessedFan (.next ([7125000000000, 0], [1350000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([6930000000000, 0], [1695000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([375000000000, -9000000000000], [0,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([6930000000000, -9000000000000],
      [2070000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3750000000000],
      [2385000000000]) (some (0, 4, 2)) (some (0, 4, 2)) fan25Owner2Part2)))))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [294000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([5601000000000], [1404000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([5601000000000], [2070000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([4935000000000, -9000000000000], [2070000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([2265000000000], [3630000000000]) (some (3, 0, 4)) (some (3, 1, 4))
      (.next ([3375000000000], [5895000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([1305000000000, -9000000000000], [7965000000000, 9000000000000]) (some (3, 1, 4)) (some (3,
      1, 4)) (.next ([0], [2070000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([-294000000000], [3669000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1404000000000],
      [7005000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2070000000000, -9000000000000],
      [7671000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2070000000000,
      -9000000000000], [7005000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3630000000000],
      [5895000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5895000000000], [9270000000000])
      (some (0, 1, 2)) (some (0, 4, 2)) (.next ([-7965000000000, -9000000000000], [9270000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4,
      2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([5820000000000, 9000000000000], [420000000000,
      -9000000000000]) none none (.next ([6240000000000], [1050000000000]) none none (.next
      ([2070000000000, 9000000000000], [2070000000000, 9000000000000]) none none (.next
      ([2070000000000, 9000000000000], [2730000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([1680000000000, -9000000000000], [2490000000000, 0]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([0], [6870000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-420000000000, 9000000000000], [6240000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-1050000000000], [7290000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2070000000000,
      -9000000000000], [4140000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2730000000000, 9000000000000], [4800000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2490000000000, 0], [4170000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_2 : ExcludedOn (model26.B 2 ++ [step26.q]) 9000000000000 (model26.caps 2)
    (model26.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([375000000000, -9000000000000], [0,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([6930000000000, -9000000000000],
      [2070000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([3825000000000],
      [1425000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1875000000000], [1770000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1680000000000], [2115000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([150000000000], [195000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([1680000000000, -9000000000000], [2490000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([2055000000000], [5070000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([1710000000000], [5220000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1335000000000,
      0], [5595000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([420000000000,
      -9000000000000], [4830000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0,
      0], [3405000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0,
      -9000000000000], [375000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2070000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1425000000000], [5250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1770000000000], [3645000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2115000000000], [3795000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-195000000000],
      [345000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2490000000000, 0], [4170000000000,
      -9000000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-5070000000000], [7125000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5220000000000], [6930000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([-5595000000000, 9000000000000], [6930000000000, -9000000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4830000000000, -9000000000000], [5250000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2, 3)) (some (4, 2, 0)) (some (4, 2,
      3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000, -9000000000000], [0,
      9000000000000]) (some (2, 0, 1)) (some (3, 0, 1)) (.next ([5601000000000], [1404000000000])
      (some (3, 0, 1)) (some (3, 4, 1)) (.next ([5601000000000], [2070000000000, 9000000000000])
      (some (3, 4, 1)) (some (3, 4, 2)) (.next ([4935000000000, -9000000000000], [2070000000000,
      9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1935000000000], [2070000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([2070000000000], [3000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([2601000000000], [5070000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([0], [2070000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0,
      -9000000000000], [3000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1404000000000],
      [7005000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2070000000000, -9000000000000],
      [7671000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2070000000000,
      -9000000000000], [7005000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2070000000000],
      [4005000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3000000000000], [5070000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5070000000000], [7671000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1,
      2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3930000000000], [60000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([4920000000000, -9000000000000], [2070000000000, 9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3000000000000], [1860000000000, -9000000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2070000000000, 9000000000000], [2070000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3000000000000], [3930000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2070000000000, 9000000000000], [4920000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([930000000000, -9000000000000],
      [6000000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [2070000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-60000000000],
      [3990000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2070000000000, -9000000000000],
      [6990000000000, 0]) (some (0, 1, 2)) (some (0, 1, 4)) (.next ([-1860000000000, 9000000000000],
      [4860000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-2070000000000,
      -9000000000000], [4140000000000, 18000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3930000000000], [6930000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4920000000000,
      9000000000000], [6990000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6000000000000,
      -9000000000000], [6930000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Aown230000240000
end ConwaySoifer.Simplified.Certificates
