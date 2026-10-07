/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown160000170000
import Mathlib.Tactic.FinCases

/-!
# Aown 160000 170000 2

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
namespace Aown160000170000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part0 : FanWitness := (.next ([-1533000000000], [4785000000000]) (some (0, 4, 10))
    (some (0, 5, 10)) (.next ([-3210000000000], [9660000000000]) (some (0, 5, 10)) (some (0, 5, 10))
    (.next ([-2160000000000], [6480000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-1677000000000], [4875000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next ([-3608400000000,
    -2490000000000], [9796800000000, 4980000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-2296800000000, -4980000000000], [6218400000000, 2490000000000]) (some (0, 5, 10)) (some (0,
    5, 10)) (.next ([-1931400000000, -2490000000000], [4921800000000, 4980000000000]) (some (0, 5,
    10)) (some (0, 5, 10)) (.next ([-3870000000000], [9660000000000]) (some (0, 5, 10)) (some (1, 5,
    10)) (.next ([-4006800000000, -4980000000000], [9398400000000, 2490000000000]) (some (1, 5, 10))
    (some (1, 5, 10)) (.next ([-2193000000000], [4785000000000]) (some (1, 5, 10)) (some (1, 5, 10))
    (.next ([-398400000000, -2490000000000], [796800000000, 4980000000000]) (some (1, 5, 10)) (some
    (1, 5, 10)) (.next ([-2329800000000, -4980000000000], [4523400000000, 2490000000000]) (some (1,
    5, 10)) (some (1, 5, 10)) (.next ([-1710000000000], [3180000000000]) (some (1, 5, 10)) (some (1,
    5, 10)) (.next ([-780000000000], [1440000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-1041600000000, 2490000000000], [1838400000000, 2490000000000]) (some (1, 5, 10)) (some (1, 5,
    10)) (.next ([-261600000000, 2490000000000], [398400000000, 2490000000000]) (some (1, 5, 10))
    (some (1, 5, 10)) (.next ([-1440000000000], [2100000000000]) (some (1, 5, 10)) (some (2, 5, 10))
    (.next ([-1058400000000, -2490000000000], [1456800000000, 4980000000000]) (some (2, 5, 10))
    (some (2, 5, 10)) (.next ([-796800000000, -4980000000000], [1058400000000, 2490000000000]) (some
    (2, 5, 10)) (some (2, 5, 10)) (.next ([-1770000000000], [2250000000000]) (some (2, 5, 10)) (some
    (2, 5, 10)) (.next ([-1838400000000, -2490000000000], [2236800000000, 4980000000000]) (some (2,
    5, 10)) (some (2, 10, 10)) (.next ([-930000000000], [990000000000]) (some (2, 10, 10)) (some (2,
    10, 10)) (.next ([-2625000000000], [2718000000000]) (some (2, 10, 10)) (some (2, 10, 10)) (.next
    ([-1695000000000], [1728000000000]) (some (2, 10, 10)) (some (2, 10, 10)) (.terminal (some (2,
    10, 10)) (some (2, 10, 10)) (some (2, 10, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part1 : FanWitness := (.next ([398400000000, 2490000000000], [1058400000000,
    2490000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([261600000000, -2490000000000],
    [796800000000, 4980000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([480000000000],
    [1770000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([398400000000, 2490000000000],
    [1838400000000, 2490000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([60000000000],
    [930000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([93000000000], [2625000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([33000000000], [1695000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([0, 0], [1195200000000, 7470000000000]) (some (0, 4, 10)) (some (0, 4,
    10)) (.next ([-60000000000], [4380000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-93000000000], [2685000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-780000000000],
    [6750000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-1041600000000, 2490000000000],
    [7148400000000, 2490000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-1101600000000,
    2490000000000], [6218400000000, 2490000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-398400000000, -2490000000000], [2236800000000, 4980000000000]) (some (0, 4, 10)) (some (0, 4,
    10)) (.next ([-1440000000000], [7410000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-873000000000], [4125000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-1500000000000],
    [6480000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-1770000000000], [7560000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-1838400000000, -2490000000000], [7546800000000,
    4980000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-2550000000000], [9000000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-2100000000000], [7410000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([-1898400000000, -2490000000000], [6616800000000, 4980000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-2811600000000, 2490000000000], [9398400000000,
    2490000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-2236800000000, -4980000000000],
    [7148400000000, 2490000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    fan18Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part2 : FanWitness := (.next ([5790000000000], [1770000000000]) (some (10, 2, 10))
    (some (10, 2, 10)) (.next ([5708400000000, 2490000000000], [1838400000000, 2490000000000]) (some
    (8, 2, 10)) (some (8, 2, 10)) (.next ([6450000000000], [2550000000000]) (some (8, 2, 10)) (some
    (8, 2, 10)) (.next ([5310000000000], [2100000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
    ([4718400000000, 2490000000000], [1898400000000, 2490000000000]) (some (8, 2, 10)) (some (8, 2,
    10)) (.next ([6586800000000, 4980000000000], [2811600000000, -2490000000000]) (some (8, 2, 10))
    (some (8, 2, 10)) (.next ([4911600000000, -2490000000000], [2236800000000, 4980000000000]) (some
    (8, 2, 10)) (some (8, 2, 10)) (.next ([3252000000000], [1533000000000]) (some (8, 2, 10)) (some
    (8, 2, 10)) (.next ([6450000000000], [3210000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
    ([4320000000000], [2160000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([3198000000000],
    [1677000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([6188400000000, 2490000000000],
    [3608400000000, 2490000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([3921600000000,
    -2490000000000], [2296800000000, 4980000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
    ([2990400000000, 2490000000000], [1931400000000, 2490000000000]) (some (8, 2, 10)) (some (8, 2,
    10)) (.next ([5790000000000], [3870000000000]) (some (8, 2, 10)) (some (8, 3, 10)) (.next
    ([5391600000000, -2490000000000], [4006800000000, 4980000000000]) (some (8, 3, 10)) (some (8, 3,
    10)) (.next ([2592000000000], [2193000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
    ([398400000000, 2490000000000], [398400000000, 2490000000000]) (some (8, 3, 10)) (some (8, 3,
    10)) (.next ([2193600000000, -2490000000000], [2329800000000, 4980000000000]) (some (8, 3, 10))
    (some (8, 3, 10)) (.next ([1470000000000], [1710000000000]) (some (8, 3, 10)) (some (8, 3, 10))
    (.next ([660000000000], [780000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next
    ([796800000000, 4980000000000], [1041600000000, -2490000000000]) (some (8, 3, 10)) (some (9, 3,
    10)) (.next ([136800000000, 4980000000000], [261600000000, -2490000000000]) (some (9, 3, 10))
    (some (9, 3, 10)) (.next ([660000000000], [1440000000000]) (some (0, 3, 10)) (some (0, 4, 10))
    fan18Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part0 : FanWitness := (.next ([-1533000000000], [4785000000000]) (some (0, 5, 11))
    (some (0, 5, 11)) (.next ([-2160000000000], [6480000000000]) (some (0, 5, 11)) (some (0, 5, 11))
    (.next ([-2296800000000, -4980000000000], [6218400000000, 2490000000000]) (some (0, 5, 11))
    (some (0, 5, 11)) (.next ([-1931400000000, -2490000000000], [4921800000000, 4980000000000])
    (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-930000000000], [2070000000000]) (some (0, 5, 11))
    (some (1, 5, 11)) (.next ([-2193000000000], [4785000000000]) (some (1, 5, 11)) (some (1, 5, 11))
    (.next ([-398400000000, -2490000000000], [796800000000, 4980000000000]) (some (1, 5, 11)) (some
    (1, 5, 11)) (.next ([-2329800000000, -4980000000000], [4523400000000, 2490000000000]) (some (1,
    5, 11)) (some (1, 5, 11)) (.next ([-780000000000], [1440000000000]) (some (1, 5, 11)) (some (1,
    5, 11)) (.next ([-1041600000000, 2490000000000], [1838400000000, 2490000000000]) (some (1, 5,
    11)) (some (1, 5, 11)) (.next ([-1080000000000], [1815000000000]) (some (1, 5, 11)) (some (1, 5,
    11)) (.next ([-1440000000000], [2100000000000]) (some (1, 5, 11)) (some (2, 11, 11)) (.next
    ([-2625000000000], [3798000000000]) (some (2, 11, 11)) (some (2, 11, 11)) (.next
    ([-1058400000000, -2490000000000], [1456800000000, 4980000000000]) (some (2, 11, 11)) (some (2,
    11, 11)) (.next ([-796800000000, -4980000000000], [1058400000000, 2490000000000]) (some (2, 11,
    11)) (some (2, 11, 11)) (.next ([-1838400000000, -2490000000000], [2236800000000,
    4980000000000]) (some (2, 11, 11)) (some (2, 11, 11)) (.next ([-5310000000000], [6390000000000])
    (some (2, 11, 11)) (some (2, 11, 11)) (.next ([-930000000000], [990000000000]) (some (2, 11,
    11)) (some (2, 11, 11)) (.next ([-6750000000000], [7050000000000]) (some (2, 11, 11)) (some (2,
    11, 11)) (.next ([-2625000000000], [2718000000000]) (some (2, 11, 11)) (some (2, 11, 11)) (.next
    ([-2745000000000], [2805000000000]) (some (2, 11, 11)) (some (2, 11, 11)) (.next
    ([-4440000000000], [4533000000000]) (some (2, 11, 7)) (some (2, 11, 7)) (.next
    ([-1695000000000], [1728000000000]) (some (2, 11, 7)) (some (2, 11, 7)) (.next ([-7148400000000,
    -2490000000000], [7186800000000, 4980000000000]) (some (2, 11, 7)) (some (2, 11, 8)) (.terminal
    (some (2, 11, 8)) (some (2, 11, 8)) (some (2, 11, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part1 : FanWitness := (.next ([38400000000, 2490000000000], [7148400000000,
    2490000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next ([0, 0], [1195200000000,
    7470000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next ([-60000000000], [4380000000000])
    (some (0, 4, 11)) (some (0, 4, 11)) (.next ([-93000000000], [2685000000000]) (some (0, 4, 11))
    (some (0, 4, 11)) (.next ([-360000000000], [7410000000000]) (some (0, 4, 11)) (some (0, 4, 11))
    (.next ([-780000000000], [8565000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next
    ([-758400000000, -2490000000000], [7546800000000, 4980000000000]) (some (0, 4, 11)) (some (0, 4,
    11)) (.next ([-1041600000000, 2490000000000], [8963400000000, 2490000000000]) (some (0, 4, 11))
    (some (0, 4, 11)) (.next ([-1020000000000], [7410000000000]) (some (0, 4, 11)) (some (0, 4, 11))
    (.next ([-1041600000000, 2490000000000], [7148400000000, 2490000000000]) (some (0, 4, 11)) (some
    (0, 4, 11)) (.next ([-1440000000000], [9225000000000]) (some (0, 4, 11)) (some (0, 4, 11))
    (.next ([-1156800000000, -4980000000000], [7148400000000, 2490000000000]) (some (0, 4, 11))
    (some (0, 4, 11)) (.next ([-1101600000000, 2490000000000], [6218400000000, 2490000000000]) (some
    (0, 4, 11)) (some (0, 5, 11)) (.next ([-398400000000, -2490000000000], [2236800000000,
    4980000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-1440000000000], [7410000000000])
    (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-1838400000000, -2490000000000], [9361800000000,
    4980000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-873000000000], [4125000000000])
    (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-2100000000000], [9225000000000]) (some (0, 5, 11))
    (some (0, 5, 11)) (.next ([-1500000000000], [6480000000000]) (some (0, 5, 11)) (some (0, 5, 11))
    (.next ([-1838400000000, -2490000000000], [7546800000000, 4980000000000]) (some (0, 5, 11))
    (some (0, 5, 11)) (.next ([-2236800000000, -4980000000000], [8963400000000, 2490000000000])
    (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-2100000000000], [7410000000000]) (some (0, 5, 11))
    (some (0, 5, 11)) (.next ([-1898400000000, -2490000000000], [6616800000000, 4980000000000])
    (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-2236800000000, -4980000000000], [7148400000000,
    2490000000000]) (some (0, 5, 11)) (some (0, 5, 11)) fan20Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part2 : FanWitness := (.next ([4911600000000, -2490000000000], [2236800000000,
    4980000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([3252000000000], [1533000000000])
    (some (9, 2, 11)) (some (9, 2, 11)) (.next ([4320000000000], [2160000000000]) (some (9, 2, 11))
    (some (9, 2, 11)) (.next ([3921600000000, -2490000000000], [2296800000000, 4980000000000]) (some
    (9, 2, 11)) (some (9, 2, 11)) (.next ([2990400000000, 2490000000000], [1931400000000,
    2490000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([1140000000000], [930000000000])
    (some (9, 2, 11)) (some (9, 3, 11)) (.next ([2592000000000], [2193000000000]) (some (9, 3, 11))
    (some (9, 3, 11)) (.next ([398400000000, 2490000000000], [398400000000, 2490000000000]) (some
    (9, 3, 11)) (some (9, 3, 11)) (.next ([2193600000000, -2490000000000], [2329800000000,
    4980000000000]) (some (9, 3, 11)) (some (9, 3, 11)) (.next ([660000000000], [780000000000])
    (some (9, 3, 11)) (some (9, 3, 11)) (.next ([796800000000, 4980000000000], [1041600000000,
    -2490000000000]) (some (9, 3, 11)) (some (10, 3, 11)) (.next ([735000000000], [1080000000000])
    (some (10, 3, 11)) (some (10, 3, 11)) (.next ([660000000000], [1440000000000]) (some (10, 3,
    11)) (some (0, 4, 11)) (.next ([1173000000000], [2625000000000]) (some (0, 4, 11)) (some (0, 4,
    11)) (.next ([398400000000, 2490000000000], [1058400000000, 2490000000000]) (some (0, 4, 11))
    (some (0, 4, 11)) (.next ([261600000000, -2490000000000], [796800000000, 4980000000000]) (some
    (0, 4, 11)) (some (0, 4, 11)) (.next ([398400000000, 2490000000000], [1838400000000,
    2490000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next ([1080000000000], [5310000000000])
    (some (0, 4, 11)) (some (0, 4, 11)) (.next ([60000000000], [930000000000]) (some (0, 4, 11))
    (some (0, 4, 11)) (.next ([300000000000], [6750000000000]) (some (0, 4, 11)) (some (0, 4, 11))
    (.next ([93000000000], [2625000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next
    ([60000000000], [2745000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next ([93000000000],
    [4440000000000]) (some (0, 4, 11)) (some (0, 4, 11)) (.next ([33000000000], [1695000000000])
    (some (0, 4, 11)) (some (0, 4, 11)) fan20Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part0 : FanWitness := (.next ([-3683400000000, -2490000000000], [9796800000000,
    4980000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next ([-1931400000000, -2490000000000],
    [4921800000000, 4980000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next ([-3945000000000],
    [9660000000000]) (some (0, 11, 6)) (some (1, 11, 6)) (.next ([-2610000000000], [6075000000000])
    (some (1, 11, 6)) (some (1, 11, 6)) (.next ([-4081800000000, -4980000000000], [9398400000000,
    2490000000000]) (some (1, 11, 6)) (some (1, 11, 6)) (.next ([-930000000000], [2070000000000])
    (some (1, 11, 6)) (some (1, 11, 6)) (.next ([-2193000000000], [4785000000000]) (some (1, 11, 6))
    (some (1, 11, 6)) (.next ([-398400000000, -2490000000000], [796800000000, 4980000000000]) (some
    (1, 11, 6)) (some (1, 11, 6)) (.next ([-3690000000000], [7155000000000]) (some (1, 11, 6)) (some
    (1, 11, 6)) (.next ([-780000000000], [1440000000000]) (some (1, 11, 6)) (some (1, 11, 6)) (.next
    ([-1041600000000, 2490000000000], [1838400000000, 2490000000000]) (some (1, 11, 6)) (some (1,
    11, 6)) (.next ([-261600000000, 2490000000000], [398400000000, 2490000000000]) (some (1, 11, 6))
    (some (1, 11, 6)) (.next ([-1440000000000], [2100000000000]) (some (1, 11, 6)) (some (2, 11, 6))
    (.next ([-2625000000000], [3798000000000]) (some (2, 11, 6)) (some (2, 11, 6)) (.next
    ([-1058400000000, -2490000000000], [1456800000000, 4980000000000]) (some (2, 11, 6)) (some (2,
    11, 6)) (.next ([-796800000000, -4980000000000], [1058400000000, 2490000000000]) (some (2, 11,
    6)) (some (2, 11, 6)) (.next ([-1838400000000, -2490000000000], [2236800000000, 4980000000000])
    (some (2, 11, 6)) (some (2, 11, 6)) (.next ([-5310000000000], [6390000000000]) (some (2, 11, 6))
    (some (2, 11, 6)) (.next ([-6408000000000], [7248000000000]) (some (2, 11, 6)) (some (2, 11, 6))
    (.next ([-930000000000], [990000000000]) (some (2, 11, 6)) (some (2, 11, 6)) (.next
    ([-6750000000000], [7050000000000]) (some (2, 11, 6)) (some (2, 11, 7)) (.next
    ([-2625000000000], [2718000000000]) (some (2, 11, 7)) (some (2, 11, 7)) (.next
    ([-1695000000000], [1728000000000]) (some (2, 11, 7)) (some (2, 11, 7)) (.next ([-7148400000000,
    -2490000000000], [7186800000000, 4980000000000]) (some (2, 11, 7)) (some (2, 11, 8)) (.terminal
    (some (2, 11, 8)) (some (2, 11, 8)) (some (2, 11, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part1 : FanWitness := (.next ([38400000000, 2490000000000], [7148400000000,
    2490000000000]) (some (0, 11, 5)) (some (0, 11, 5)) (.next ([0, 0], [1195200000000,
    7470000000000]) (some (0, 11, 5)) (some (0, 11, 5)) (.next ([-60000000000], [4380000000000])
    (some (0, 11, 5)) (some (0, 11, 6)) (.next ([-93000000000], [2685000000000]) (some (0, 11, 6))
    (some (0, 11, 6)) (.next ([-360000000000], [7410000000000]) (some (0, 11, 6)) (some (0, 11, 6))
    (.next ([-758400000000, -2490000000000], [7546800000000, 4980000000000]) (some (0, 11, 6)) (some
    (0, 11, 6)) (.next ([-780000000000], [6750000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next
    ([-1020000000000], [7410000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next ([-1041600000000,
    2490000000000], [7148400000000, 2490000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next
    ([-1156800000000, -4980000000000], [7148400000000, 2490000000000]) (some (0, 11, 6)) (some (0,
    11, 6)) (.next ([-1101600000000, 2490000000000], [6218400000000, 2490000000000]) (some (0, 11,
    6)) (some (0, 11, 6)) (.next ([-398400000000, -2490000000000], [2236800000000, 4980000000000])
    (some (0, 11, 6)) (some (0, 11, 6)) (.next ([-1440000000000], [7410000000000]) (some (0, 11, 6))
    (some (0, 11, 6)) (.next ([-1845000000000], [9000000000000]) (some (0, 11, 6)) (some (0, 11, 6))
    (.next ([-873000000000], [4125000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next
    ([-1500000000000], [6480000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next ([-1838400000000,
    -2490000000000], [7546800000000, 4980000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next
    ([-2100000000000], [7410000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next ([-1898400000000,
    -2490000000000], [6616800000000, 4980000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next
    ([-2236800000000, -4980000000000], [7148400000000, 2490000000000]) (some (0, 11, 6)) (some (0,
    11, 6)) (.next ([-1533000000000], [4785000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next
    ([-2160000000000], [6480000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next
    ([-3285000000000], [9660000000000]) (some (0, 11, 6)) (some (0, 11, 6)) (.next ([-2296800000000,
    -4980000000000], [6218400000000, 2490000000000]) (some (0, 11, 6)) (some (0, 11, 6))
    fan22Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part2 : FanWitness := (.next ([3921600000000, -2490000000000], [2296800000000,
    4980000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([6113400000000, 2490000000000],
    [3683400000000, 2490000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([2990400000000,
    2490000000000], [1931400000000, 2490000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
    ([5715000000000], [3945000000000]) (some (9, 2, 11)) (some (9, 3, 11)) (.next ([3465000000000],
    [2610000000000]) (some (9, 3, 11)) (some (9, 3, 11)) (.next ([5316600000000, -2490000000000],
    [4081800000000, 4980000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1140000000000],
    [930000000000]) (some (9, 3, 5)) (some (9, 11, 5)) (.next ([2592000000000], [2193000000000])
    (some (9, 11, 5)) (some (9, 11, 5)) (.next ([398400000000, 2490000000000], [398400000000,
    2490000000000]) (some (9, 11, 5)) (some (9, 11, 5)) (.next ([3465000000000], [3690000000000])
    (some (9, 11, 5)) (some (9, 11, 5)) (.next ([660000000000], [780000000000]) (some (9, 11, 5))
    (some (9, 11, 5)) (.next ([796800000000, 4980000000000], [1041600000000, -2490000000000]) (some
    (9, 11, 5)) (some (10, 11, 5)) (.next ([136800000000, 4980000000000], [261600000000,
    -2490000000000]) (some (10, 11, 5)) (some (10, 11, 5)) (.next ([660000000000], [1440000000000])
    (some (0, 11, 5)) (some (0, 11, 5)) (.next ([1173000000000], [2625000000000]) (some (0, 11, 5))
    (some (0, 11, 5)) (.next ([398400000000, 2490000000000], [1058400000000, 2490000000000]) (some
    (0, 11, 5)) (some (0, 11, 5)) (.next ([261600000000, -2490000000000], [796800000000,
    4980000000000]) (some (0, 11, 5)) (some (0, 11, 5)) (.next ([398400000000, 2490000000000],
    [1838400000000, 2490000000000]) (some (0, 11, 5)) (some (0, 11, 5)) (.next ([1080000000000],
    [5310000000000]) (some (0, 11, 5)) (some (0, 11, 5)) (.next ([840000000000], [6408000000000])
    (some (0, 11, 5)) (some (0, 11, 5)) (.next ([60000000000], [930000000000]) (some (0, 11, 5))
    (some (0, 11, 5)) (.next ([300000000000], [6750000000000]) (some (0, 11, 5)) (some (0, 11, 5))
    (.next ([93000000000], [2625000000000]) (some (0, 11, 5)) (some (0, 11, 5)) (.next
    ([33000000000], [1695000000000]) (some (0, 11, 5)) (some (0, 11, 5))
    fan22Owner0Part1))))))))))))))))))))))))

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2940000000000, 9000000000000], [1740000000000,
      -9000000000000]) none none (.next ([4680000000000], [3180000000000]) none none (.next
      ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) none none (.next
      ([1440000000000, 9000000000000], [3240000000000, -9000000000000]) none none (.next
      ([60000000000, -9000000000000], [3180000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-1740000000000, 9000000000000], [4680000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3180000000000], [7860000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1440000000000,
      -9000000000000], [2880000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3240000000000, 9000000000000], [4680000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) none none))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7605000000000, 0], [960000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7560000000000, -9000000000000],
      [1440000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3180000000000],
      [1035000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3285000000000, 0], [1440000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3180000000000], [4320000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1740000000000, -9000000000000], [5760000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([480000000000], [3840000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([480000000000], [7125000000000]) (some (0, 4, 1))
      (some (0, 4, 2)) (.next ([105000000000], [2700000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([60000000000, -9000000000000], [3180000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-960000000000, -9000000000000], [8565000000000, 9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1440000000000, -9000000000000], [9000000000000, 0]) (some (0, 1,
      3)) (some (0, 1, 3)) (.next ([-1035000000000], [4215000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-1440000000000, -9000000000000], [4725000000000, 9000000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-4320000000000], [7500000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-5760000000000, -9000000000000], [7500000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-3840000000000], [4320000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-7125000000000], [7605000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-2700000000000], [2805000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded16_1
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

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2250000000000, -9000000000000], [0,
      9000000000000]) none none (.next ([2880000000000, 9000000000000], [810000000000,
      -9000000000000]) none none (.next ([3690000000000], [3240000000000]) none none (.next
      ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) none none (.next
      ([1440000000000, 9000000000000], [3240000000000, -9000000000000]) none none (.next ([0],
      [6120000000000, 9000000000000]) none none (.next ([0, -9000000000000], [2250000000000, 0])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-810000000000, 9000000000000], [3690000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3240000000000], [6930000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-1440000000000, -9000000000000], [2880000000000, 18000000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3240000000000, 9000000000000], [4680000000000, 0])
      (some (3, 1, 2)) none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2250000000000, -9000000000000], [0,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7605000000000, 0], [960000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7560000000000, -9000000000000],
      [1440000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3285000000000, 0],
      [1440000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2250000000000],
      [2025000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2250000000000], [5310000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([480000000000], [3840000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([810000000000, -9000000000000], [6750000000000, 9000000000000]) (some
      (0, 4, 1)) (some (0, 4, 2)) (.next ([480000000000], [7125000000000]) (some (0, 4, 2)) (some
      (0, 4, 2)) (.next ([45000000000], [1770000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([0, 0], [1440000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0,
      -9000000000000], [2250000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-960000000000,
      -9000000000000], [8565000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1440000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-1440000000000, -9000000000000], [4725000000000, 9000000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-2025000000000], [4275000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-5310000000000], [7560000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-3840000000000], [4320000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6750000000000,
      -9000000000000], [7560000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-7125000000000],
      [7605000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next ([-1770000000000], [1815000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1, 0)) (some (4, 1,
      3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded17_1
    · exact excluded17_2
    · exact excluded17_3
    · exact excluded17_4
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4320000000000], [60000000000]) (some (10, 2,
      10)) (some (10, 2, 10)) (.next ([2592000000000], [93000000000]) (some (10, 2, 10)) (some (10,
      2, 10)) (.next ([5970000000000], [780000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([6106800000000, 4980000000000], [1041600000000, -2490000000000]) (some (10, 2, 10)) (some
      (10, 2, 10)) (.next ([5116800000000, 4980000000000], [1101600000000, -2490000000000]) (some
      (10, 2, 10)) (some (10, 2, 10)) (.next ([1838400000000, 2490000000000], [398400000000,
      2490000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([5970000000000],
      [1440000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([3252000000000],
      [873000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([4980000000000],
      [1500000000000]) (some (10, 2, 10)) (some (10, 2, 10)) fan18Owner0Part2)))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3210000000000], [1470000000000]) none none
      (.next ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) none none (.next
      ([1440000000000, 9000000000000], [3240000000000, -9000000000000]) none none (.next ([0, 0],
      [1770000000000, -9000000000000]) none none (.next ([-1470000000000], [4680000000000]) (some
      (3, 1, 2)) none (.next ([-1440000000000, -9000000000000], [2880000000000, 18000000000000])
      none none (.next ([-3240000000000, 9000000000000], [4680000000000, 0]) none none (.terminal
      none none none))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3210000000000], [3630000000000]) (some (2, 0,
      1)) (some (3, 0, 2)) (.next ([3210000000000], [5790000000000]) (some (3, 0, 2)) (some (3, 0,
      2)) (.next ([720000000000, -9000000000000], [1440000000000, 9000000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1770000000000, -9000000000000], [5790000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1440000000000, 9000000000000], [5400000000000, -9000000000000])
      (some (3, 0, 2)) (some (4, 0, 2)) (.next ([1440000000000, 9000000000000], [7560000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0], [7560000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-3630000000000], [6840000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-5790000000000], [9000000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([-1440000000000, -9000000000000], [2160000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([-5790000000000, 0], [7560000000000, -9000000000000]) (some (4, 0,
      2)) (some (4, 0, 2)) (.next ([-5400000000000, 9000000000000], [6840000000000, 0]) (some (4, 0,
      2)) (some (4, 0, 2)) (.next ([-7560000000000, 9000000000000], [9000000000000, 0]) (some (4, 0,
      2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (0, 1, 2)) (some (4, 1,
      2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded18_3
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
  apply ExclusionHint.sound (.witnessedFan (.next ([1800000000000, 9000000000000], [810000000000,
      -9000000000000]) none none (.next ([1440000000000, 9000000000000], [1440000000000,
      9000000000000]) none none (.next ([2610000000000], [4320000000000]) none none (.next
      ([1440000000000, 9000000000000], [3240000000000, -9000000000000]) none none (.next ([0],
      [6120000000000, 9000000000000]) none none (.next ([-810000000000, 9000000000000],
      [2610000000000]) none none (.next ([-1440000000000, -9000000000000], [2880000000000,
      18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4320000000000], [6930000000000])
      (some (3, 1, 2)) none (.next ([-3240000000000, 9000000000000], [4680000000000, 0]) none none
      (.terminal none none none))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7605000000000, 0], [960000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7560000000000, -9000000000000],
      [1440000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5790000000000, 0],
      [1440000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2250000000000],
      [600000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1170000000000, -9000000000000],
      [1080000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([735000000000],
      [1035000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([480000000000], [1335000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2250000000000], [6390000000000]) (some (0, 4, 1))
      (some (0, 4, 2)) (.next ([810000000000, -9000000000000], [7830000000000, 9000000000000]) (some
      (0, 4, 2)) (some (0, 4, 2)) (.next ([480000000000], [7125000000000]) (some (0, 4, 2)) (some
      (0, 4, 2)) (.next ([0, 0], [1440000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-960000000000, -9000000000000], [8565000000000, 9000000000000]) (some (0, 4, 2))
      (some (0, 4, 3)) (.next ([-1440000000000, -9000000000000], [9000000000000, 0]) (some (0, 4,
      3)) (some (0, 4, 3)) (.next ([-1440000000000, -9000000000000], [7230000000000, 9000000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-600000000000], [2850000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-1080000000000, -9000000000000], [2250000000000, 0]) (some (0, 4,
      3)) (some (0, 4, 3)) (.next ([-1035000000000], [1770000000000]) (some (0, 4, 3)) (some (0, 4,
      3)) (.next ([-1335000000000], [1815000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-6390000000000], [8640000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-7830000000000,
      -9000000000000], [8640000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-7125000000000],
      [7605000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1,
      0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8190000000000, 9000000000000], [1170000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([6750000000000], [2610000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([3735000000000], [2610000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1440000000000, 9000000000000], [3015000000000]) (some (3, 0, 2))
      (some (3, 0, 3)) (.next ([0, 0], [1440000000000, 9000000000000]) (some (3, 0, 3)) (some (3, 0,
      3)) (.next ([-1170000000000, 9000000000000], [9360000000000]) (some (3, 0, 3)) (some (3, 1,
      3)) (.next ([-2610000000000], [9360000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2610000000000], [6345000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3015000000000,
      0], [4455000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4320000000000], [60000000000]) (some (8, 2, 11))
      (some (8, 2, 11)) (.next ([2592000000000], [93000000000]) (some (8, 2, 11)) (some (8, 2, 11))
      (.next ([7050000000000], [360000000000]) (some (8, 2, 11)) (some (9, 2, 11)) (.next
      ([7785000000000], [780000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([6788400000000,
      2490000000000], [758400000000, 2490000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([7921800000000, 4980000000000], [1041600000000, -2490000000000]) (some (9, 2, 11)) (some (9,
      2, 11)) (.next ([6390000000000], [1020000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([6106800000000, 4980000000000], [1041600000000, -2490000000000]) (some (9, 2, 11)) (some (9,
      2, 11)) (.next ([7785000000000], [1440000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([5991600000000, -2490000000000], [1156800000000, 4980000000000]) (some (9, 2, 11)) (some (9,
      2, 11)) (.next ([5116800000000, 4980000000000], [1101600000000, -2490000000000]) (some (9, 2,
      11)) (some (9, 2, 11)) (.next ([1838400000000, 2490000000000], [398400000000, 2490000000000])
      (some (9, 2, 11)) (some (9, 2, 11)) (.next ([5970000000000], [1440000000000]) (some (9, 2,
      11)) (some (9, 2, 11)) (.next ([7523400000000, 2490000000000], [1838400000000, 2490000000000])
      (some (9, 2, 11)) (some (9, 2, 11)) (.next ([3252000000000], [873000000000]) (some (9, 2, 11))
      (some (9, 2, 11)) (.next ([7125000000000], [2100000000000]) (some (9, 2, 11)) (some (9, 2,
      11)) (.next ([4980000000000], [1500000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([5708400000000, 2490000000000], [1838400000000, 2490000000000]) (some (9, 2, 11)) (some (9,
      2, 11)) (.next ([6726600000000, -2490000000000], [2236800000000, 4980000000000]) (some (9, 2,
      11)) (some (9, 2, 11)) (.next ([5310000000000], [2100000000000]) (some (9, 2, 11)) (some (9,
      2, 11)) (.next ([4718400000000, 2490000000000], [1898400000000, 2490000000000]) (some (9, 2,
      11)) (some (9, 2, 11)) fan20Owner0Part2))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([435000000000, -9000000000000], [0,
      9000000000000]) none none (.next ([1440000000000, 9000000000000], [1440000000000,
      9000000000000]) none none (.next ([1875000000000], [3240000000000]) none none (.next
      ([1440000000000, 9000000000000], [3240000000000, -9000000000000]) none none (.next ([0],
      [6120000000000, 9000000000000]) none none (.next ([0, -9000000000000], [435000000000, 0]) none
      none (.next ([-1440000000000, -9000000000000], [2880000000000, 18000000000000]) none none
      (.next ([-3240000000000], [5115000000000]) none none (.next ([-3240000000000, 9000000000000],
      [4680000000000, 0]) none none (.terminal none none none))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([435000000000, -9000000000000], [0,
      9000000000000]) (some (2, 4, 1)) (some (3, 4, 2)) (.next ([720000000000, -9000000000000],
      [1440000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1875000000000],
      [5400000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1440000000000, 9000000000000],
      [5400000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1875000000000],
      [7560000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1440000000000, 9000000000000],
      [7560000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([435000000000,
      -9000000000000], [7560000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0, 0],
      [7560000000000, -9000000000000]) (some (3, 4, 2)) (some (4, 4, 2)) (.next ([0,
      -9000000000000], [435000000000, 0]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-1440000000000,
      -9000000000000], [2160000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-5400000000000],
      [7275000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-5400000000000, 9000000000000],
      [6840000000000, 0]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-7560000000000],
      [9435000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-7560000000000, 9000000000000],
      [9000000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-7560000000000, 0],
      [7995000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2))
      (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_9 : ExcludedOn (model20.B 9 ++ [step20.q]) 9000000000000 (model20.caps 9)
    (model20.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded20_3
    · exact excluded20_4
    · exact excluded20_5
    · exact excluded20_6
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6510000000000], [705000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([5760000000000, 0], [1185000000000, -9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([7200000000000, 9000000000000], [2625000000000, 0]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([5760000000000], [2625000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([1170000000000], [750000000000]) (some (0, 1, 4)) (some (0, 4, 4)) (.next
      ([1440000000000, 9000000000000], [1440000000000, 9000000000000]) (some (0, 4, 4)) (some (0, 4,
      4)) (.next ([690000000000, 9000000000000], [1920000000000, 0]) (some (0, 4, 4)) (some (0, 4,
      4)) (.next ([0, 0], [1440000000000, 9000000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next
      ([-705000000000], [7215000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-1185000000000,
      9000000000000], [6945000000000, -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-2625000000000, 0], [9825000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-2625000000000], [8385000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-750000000000],
      [1920000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1440000000000, -9000000000000],
      [2880000000000, 18000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-1920000000000,
      0], [2610000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      0)) (some (0, 4, 0)) (some (0, 4, 0))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 100 := by
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
    · exact excluded21_8
    · exact (hj rfl).elim
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4320000000000], [60000000000]) (some (8, 2, 11))
      (some (8, 2, 11)) (.next ([2592000000000], [93000000000]) (some (8, 2, 11)) (some (8, 2, 11))
      (.next ([7050000000000], [360000000000]) (some (8, 2, 11)) (some (9, 2, 11)) (.next
      ([6788400000000, 2490000000000], [758400000000, 2490000000000]) (some (9, 2, 11)) (some (9, 2,
      11)) (.next ([5970000000000], [780000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([6390000000000], [1020000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([6106800000000,
      4980000000000], [1041600000000, -2490000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([5991600000000, -2490000000000], [1156800000000, 4980000000000]) (some (9, 2, 11)) (some (9,
      2, 11)) (.next ([5116800000000, 4980000000000], [1101600000000, -2490000000000]) (some (9, 2,
      11)) (some (9, 2, 11)) (.next ([1838400000000, 2490000000000], [398400000000, 2490000000000])
      (some (9, 2, 11)) (some (9, 2, 11)) (.next ([5970000000000], [1440000000000]) (some (9, 2,
      11)) (some (9, 2, 11)) (.next ([7155000000000], [1845000000000]) (some (9, 2, 11)) (some (9,
      2, 11)) (.next ([3252000000000], [873000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([4980000000000], [1500000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([5708400000000,
      2490000000000], [1838400000000, 2490000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([5310000000000], [2100000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([4718400000000,
      2490000000000], [1898400000000, 2490000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([4911600000000, -2490000000000], [2236800000000, 4980000000000]) (some (9, 2, 11)) (some (9,
      2, 11)) (.next ([3252000000000], [1533000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([4320000000000], [2160000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([6375000000000], [3285000000000]) (some (9, 2, 11)) (some (9, 2, 11))
      fan22Owner0Part2))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded22_4
    · exact excluded22_5
    · exact (hj rfl).elim
    · exact excluded22_7
    · exact excluded22_8
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
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
    · exact excluded23_2
    · exact excluded23_3
    · exact excluded23_4
    · exact excluded23_5
    · exact excluded23_6
    · exact excluded23_7
    · exact (hj rfl).elim
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown160000170000
end ConwaySoifer.Simplified.Certificates
