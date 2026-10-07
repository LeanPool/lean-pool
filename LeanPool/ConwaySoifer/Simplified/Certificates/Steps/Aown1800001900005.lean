/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown180000190000
import Mathlib.Tactic.FinCases

/-!
# Aown 180000 190000 5

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
namespace Aown180000190000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner0Part0 : FanWitness := (.next ([-705000000000], [1080000000000]) (some (1, 6, 9))
    (some (1, 6, 9)) (.next ([-4950000000000], [7575000000000]) (some (1, 6, 9)) (some (1, 6, 9))
    (.next ([-5040000000000], [7665000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next
    ([-360000000000], [540000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-1620000000000],
    [2355000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-4140000000000], [6015000000000])
    (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-5130000000000], [7380000000000]) (some (1, 6, 9))
    (some (1, 6, 9)) (.next ([-5235000000000], [7485000000000]) (some (1, 6, 9)) (some (1, 6, 9))
    (.next ([-5130000000000], [7215000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next
    ([-915000000000], [1275000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-5415000000000],
    [7290000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-5415000000000], [7125000000000])
    (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-2625000000000], [3345000000000]) (some (1, 6, 9))
    (some (1, 6, 9)) (.next ([-1995000000000], [2535000000000]) (some (1, 6, 9)) (some (1, 6, 9))
    (.next ([-915000000000], [1110000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next
    ([-2790000000000], [3345000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-6570000000000],
    [7815000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-2160000000000], [2535000000000])
    (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-1290000000000], [1455000000000]) (some (1, 6, 9))
    (some (1, 6, 9)) (.next ([-2355000000000], [2625000000000]) (some (1, 6, 9)) (some (1, 6, 9))
    (.next ([-3570000000000], [3840000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next
    ([-2985000000000], [3165000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-3945000000000],
    [4125000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-6945000000000], [7110000000000])
    (some (1, 6, 9)) (some (1, 6, 9)) (.terminal (some (1, 6, 9)) (some (1, 6, 9)) (some (1, 6,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner0Part1 : FanWitness := (.next ([-2880000000000], [6750000000000]) (some (12, 6, 9))
    (some (12, 6, 9)) (.next ([-3375000000000], [7755000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    (.next ([-1965000000000], [4410000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-3540000000000], [7755000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-180000000000],
    [375000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-3735000000000], [7575000000000])
    (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-375000000000], [750000000000]) (some (12, 6, 9))
    (some (12, 6, 9)) (.next ([-3675000000000], [7215000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    (.next ([-195000000000], [375000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-3840000000000], [7380000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-2250000000000], [4320000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-3915000000000], [7380000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-1080000000000], [1995000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-3915000000000], [7215000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-3960000000000],
    [7125000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-4125000000000], [7290000000000])
    (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-705000000000], [1245000000000]) (some (1, 6, 9))
    (some (1, 6, 9)) (.next ([-1245000000000], [2160000000000]) (some (1, 6, 9)) (some (1, 6, 9))
    (.next ([-540000000000], [915000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next
    ([-4590000000000], [7755000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-1710000000000],
    [2805000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-4755000000000], [7755000000000])
    (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-1875000000000], [2970000000000]) (some (1, 6, 9))
    (some (1, 6, 9)) (.next ([-4875000000000], [7665000000000]) (some (1, 6, 9)) (some (1, 6, 9))
    fan43Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner0Part2 : FanWitness := (.next ([270000000000], [2355000000000]) (some (12, 4, 6))
    (some (12, 4, 6)) (.next ([270000000000], [3570000000000]) (some (12, 4, 6)) (some (12, 4, 7))
    (.next ([180000000000], [2985000000000]) (some (12, 4, 7)) (some (12, 4, 7)) (.next
    ([180000000000], [3945000000000]) (some (12, 4, 7)) (some (12, 4, 7)) (.next ([165000000000],
    [6945000000000]) (some (12, 4, 7)) (some (12, 4, 7)) (.next ([0], [1290000000000]) (some (12, 4,
    7)) (some (12, 4, 7)) (.next ([-90000000000], [1590000000000]) (some (12, 4, 7)) (some (12, 5,
    8)) (.next ([-195000000000], [3165000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([-750000000000], [7485000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-165000000000],
    [1455000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-360000000000], [3165000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-915000000000], [7485000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([-1110000000000], [7305000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([-750000000000], [4410000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([-1290000000000], [7110000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([-1290000000000], [6945000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([-1380000000000], [6840000000000]) (some (12, 5, 8)) (some (12, 6, 8)) (.next ([-90000000000],
    [375000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([-630000000000], [2430000000000])
    (some (12, 6, 8)) (some (12, 6, 9)) (.next ([-180000000000], [540000000000]) (some (12, 6, 9))
    (some (12, 6, 9)) (.next ([-2460000000000], [7215000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    (.next ([-2625000000000], [7380000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-2595000000000], [6840000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-375000000000],
    [915000000000]) (some (12, 6, 9)) (some (12, 6, 9)) fan43Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner0Part3 : FanWitness := (.next ([3165000000000], [4590000000000]) (some (12, 4, 6))
    (some (12, 4, 6)) (.next ([1095000000000], [1710000000000]) (some (12, 4, 6)) (some (12, 4, 6))
    (.next ([3000000000000], [4755000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next
    ([1095000000000], [1875000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next ([2790000000000],
    [4875000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next ([375000000000], [705000000000])
    (some (12, 4, 6)) (some (12, 4, 6)) (.next ([2625000000000], [4950000000000]) (some (12, 4, 6))
    (some (12, 4, 6)) (.next ([2625000000000], [5040000000000]) (some (12, 4, 6)) (some (12, 4, 6))
    (.next ([180000000000], [360000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next
    ([735000000000], [1620000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next ([1875000000000],
    [4140000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next ([2250000000000], [5130000000000])
    (some (12, 4, 6)) (some (12, 4, 6)) (.next ([2250000000000], [5235000000000]) (some (12, 4, 6))
    (some (12, 4, 6)) (.next ([2085000000000], [5130000000000]) (some (12, 4, 6)) (some (12, 4, 6))
    (.next ([360000000000], [915000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next
    ([1875000000000], [5415000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next ([1710000000000],
    [5415000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next ([720000000000], [2625000000000])
    (some (12, 4, 6)) (some (12, 4, 6)) (.next ([540000000000], [1995000000000]) (some (12, 4, 6))
    (some (12, 4, 6)) (.next ([195000000000], [915000000000]) (some (12, 4, 6)) (some (12, 4, 6))
    (.next ([555000000000], [2790000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next
    ([1245000000000], [6570000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next ([375000000000],
    [2160000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next ([165000000000], [1290000000000])
    (some (12, 4, 6)) (some (12, 4, 6)) fan43Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner0Part4 : FanWitness := (.next ([360000000000], [180000000000]) (some (9, 2, 6)) (some
    (9, 2, 6)) (.next ([4755000000000], [2460000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next
    ([4755000000000], [2625000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next ([4245000000000],
    [2595000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next ([540000000000], [375000000000]) (some
    (9, 2, 6)) (some (9, 2, 6)) (.next ([3870000000000], [2880000000000]) (some (9, 2, 6)) (some (9,
    2, 6)) (.next ([4380000000000], [3375000000000]) (some (9, 2, 6)) (some (12, 2, 6)) (.next
    ([2445000000000], [1965000000000]) (some (12, 2, 6)) (some (12, 2, 6)) (.next ([4215000000000],
    [3540000000000]) (some (12, 2, 6)) (some (12, 2, 6)) (.next ([195000000000], [180000000000])
    (some (12, 2, 6)) (some (12, 2, 6)) (.next ([3840000000000], [3735000000000]) (some (12, 2, 6))
    (some (12, 3, 6)) (.next ([375000000000], [375000000000]) (some (12, 3, 6)) (some (12, 3, 6))
    (.next ([3540000000000], [3675000000000]) (some (12, 3, 6)) (some (12, 3, 6)) (.next
    ([180000000000], [195000000000]) (some (12, 3, 6)) (some (12, 3, 6)) (.next ([3540000000000],
    [3840000000000]) (some (12, 3, 6)) (some (12, 4, 6)) (.next ([2070000000000], [2250000000000])
    (some (12, 4, 6)) (some (12, 4, 6)) (.next ([3465000000000], [3915000000000]) (some (12, 4, 6))
    (some (12, 4, 6)) (.next ([915000000000], [1080000000000]) (some (12, 4, 6)) (some (12, 4, 6))
    (.next ([3300000000000], [3915000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next
    ([3165000000000], [3960000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next ([3165000000000],
    [4125000000000]) (some (12, 4, 6)) (some (12, 4, 6)) (.next ([540000000000], [705000000000])
    (some (12, 4, 6)) (some (12, 4, 6)) (.next ([915000000000], [1245000000000]) (some (12, 4, 6))
    (some (12, 4, 6)) (.next ([375000000000], [540000000000]) (some (12, 4, 6)) (some (12, 4, 6))
    fan43Owner0Part3))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner2Part0 : FanWitness := (.next ([5925000000000, 0], [1620000000000, 9000000000000])
    (some (0, 5, 2)) (some (0, 5, 2)) (.next ([420000000000, -9000000000000], [120000000000,
    9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([120000000000], [90000000000]) (some
    (0, 5, 2)) (some (0, 5, 2)) (.next ([630000000000], [825000000000]) (some (0, 5, 2)) (some (0,
    5, 2)) (.next ([540000000000], [1035000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
    ([1620000000000], [7380000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next ([630000000000],
    [6750000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([540000000000], [6960000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([120000000000], [8460000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([0, 0], [1620000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2,
    3)) (.next ([0, -9000000000000], [9000000000000, 0]) (some (0, 2, 3)) (some (0, 2, 4)) (.next
    ([0, -9000000000000], [7380000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([0,
    -9000000000000], [630000000000, 0]) (some (0, 2, 4)) (some (5, 2, 4)) (.next ([-1455000000000],
    [9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-1620000000000, -9000000000000],
    [9000000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-1620000000000, -9000000000000],
    [7545000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-120000000000,
    -9000000000000], [540000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-90000000000],
    [210000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-825000000000], [1455000000000])
    (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-1035000000000], [1575000000000]) (some (5, 2, 4))
    (some (5, 2, 4)) (.next ([-7380000000000], [9000000000000]) (some (5, 2, 4)) (some (5, 2, 4))
    (.next ([-6750000000000], [7380000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
    ([-6960000000000], [7500000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-8460000000000],
    [8580000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.terminal (some (5, 2, 4)) (some (5, 2, 0))
    (some (5, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner4Part0 : FanWitness := (.next ([2430000000000], [1320000000000]) (some (3, 1, 5))
    (some (3, 1, 5)) (.next ([4215000000000], [2625000000000]) (some (3, 1, 5)) (some (3, 1, 5))
    (.next ([4185000000000], [4815000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next
    ([1620000000000, 9000000000000], [3195000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next
    ([1755000000000], [3495000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next ([1320000000000,
    9000000000000], [3630000000000, -9000000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next
    ([1125000000000], [4410000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next ([540000000000],
    [4215000000000, -9000000000000]) (some (3, 1, 5)) (some (3, 1, 5)) (.next ([540000000000],
    [5835000000000]) (some (3, 1, 5)) (some (4, 1, 5)) (.next ([0, 9000000000000], [7380000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [3195000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([-300000000000], [5250000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-1620000000000], [9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-2655000000000], [9030000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1320000000000],
    [3750000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2625000000000], [6840000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4815000000000], [9000000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-3195000000000], [4815000000000, 9000000000000]) (some (0, 1, 3))
    (some (0, 5, 3)) (.next ([-3495000000000], [5250000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-3630000000000, 9000000000000], [4950000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-4410000000000], [5535000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-4215000000000, 9000000000000], [4755000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-5835000000000], [6375000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-7380000000000, 9000000000000], [7380000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal
    (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner2Part0 : FanWitness := (.next ([4005000000000], [4365000000000]) (some (0, 2, 2))
    (some (0, 2, 2)) (.next ([4005000000000, -9000000000000], [4995000000000, 0]) (some (0, 2, 2))
    (some (0, 2, 2)) (.next ([630000000000], [825000000000]) (some (0, 2, 2)) (some (0, 2, 2))
    (.next ([540000000000], [1035000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next
    ([2550000000000], [4995000000000]) (some (0, 2, 2)) (some (0, 2, 3)) (.next ([1620000000000],
    [3375000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([630000000000], [6750000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([540000000000], [6960000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([0, 0], [1620000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2,
    3)) (.next ([0, -9000000000000], [3375000000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next ([0,
    -9000000000000], [630000000000, 0]) (some (0, 2, 4)) (some (5, 2, 4)) (.next ([-1620000000000,
    -9000000000000], [9000000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-1620000000000,
    -9000000000000], [7545000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
    ([-120000000000, -9000000000000], [540000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
    ([-90000000000], [210000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-4455000000000],
    [8580000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-4365000000000], [8370000000000])
    (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-4995000000000, 0], [9000000000000, -9000000000000])
    (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-825000000000], [1455000000000]) (some (5, 2, 4))
    (some (5, 2, 4)) (.next ([-1035000000000], [1575000000000]) (some (5, 2, 4)) (some (5, 2, 4))
    (.next ([-4995000000000], [7545000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
    ([-3375000000000], [4995000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-6750000000000],
    [7380000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-6960000000000], [7500000000000])
    (some (5, 2, 4)) (some (5, 2, 4)) (.terminal (some (5, 2, 4)) (some (5, 2, 0)) (some (5, 2,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner0Part0 : FanWitness := (.next ([-735000000000], [1305000000000]) (some (2, 7, 10))
    (some (2, 7, 10)) (.next ([-4125000000000], [7290000000000]) (some (2, 7, 10)) (some (2, 7, 10))
    (.next ([-540000000000], [930000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next
    ([-540000000000], [915000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-4590000000000],
    [7755000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-4755000000000], [7755000000000])
    (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-4305000000000], [6840000000000]) (some (2, 7, 10))
    (some (2, 7, 10)) (.next ([-4875000000000], [7665000000000]) (some (2, 7, 10)) (some (2, 7, 10))
    (.next ([-4950000000000], [7575000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next
    ([-5040000000000], [7665000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-360000000000],
    [540000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-2835000000000], [4245000000000])
    (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-5130000000000], [7380000000000]) (some (2, 7, 10))
    (some (2, 7, 10)) (.next ([-5235000000000], [7485000000000]) (some (2, 7, 10)) (some (2, 7, 10))
    (.next ([-2745000000000], [3870000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next
    ([-5130000000000], [7215000000000]) (some (2, 7, 0)) (some (2, 7, 0)) (.next ([-5415000000000],
    [7290000000000]) (some (2, 7, 0)) (some (2, 7, 0)) (.next ([-5415000000000], [7125000000000])
    (some (2, 7, 0)) (some (2, 7, 0)) (.next ([-5520000000000], [6840000000000]) (some (2, 7, 0))
    (some (2, 7, 0)) (.next ([-915000000000], [1110000000000]) (some (2, 7, 0)) (some (2, 7, 0))
    (.next ([-5805000000000], [6750000000000]) (some (2, 7, 0)) (some (2, 7, 0)) (.next
    ([-2355000000000], [2625000000000]) (some (2, 7, 0)) (some (2, 7, 0)) (.next ([-3570000000000],
    [3840000000000]) (some (2, 7, 0)) (some (2, 7, 0)) (.next ([-3945000000000], [4125000000000])
    (some (2, 7, 0)) (some (2, 7, 0)) (.terminal (some (2, 7, 0)) (some (2, 7, 0)) (some (2, 7,
    0)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner0Part1 : FanWitness := (.next ([-90000000000], [375000000000]) (some (1, 11, 9)) (some
    (1, 11, 9)) (.next ([-540000000000], [2220000000000]) (some (1, 11, 9)) (some (1, 11, 10))
    (.next ([-1620000000000], [6360000000000]) (some (1, 11, 10)) (some (1, 11, 10)) (.next
    ([-1680000000000], [6570000000000]) (some (1, 11, 10)) (some (1, 11, 10)) (.next
    ([-1995000000000], [6540000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-2565000000000], [7815000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-2160000000000], [6540000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next ([-180000000000],
    [540000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next ([-2625000000000], [7380000000000])
    (some (1, 7, 10)) (some (1, 7, 10)) (.next ([-375000000000], [915000000000]) (some (1, 7, 10))
    (some (1, 7, 10)) (.next ([-2925000000000], [6930000000000]) (some (1, 7, 10)) (some (1, 7, 10))
    (.next ([-3375000000000], [7755000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-3540000000000], [7755000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next ([-180000000000],
    [375000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next ([-375000000000], [765000000000])
    (some (1, 7, 10)) (some (1, 7, 10)) (.next ([-3735000000000], [7575000000000]) (some (1, 7, 10))
    (some (1, 7, 10)) (.next ([-915000000000], [1845000000000]) (some (1, 7, 10)) (some (1, 7, 10))
    (.next ([-375000000000], [750000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-2835000000000], [5460000000000]) (some (1, 7, 10)) (some (2, 7, 10)) (.next ([-195000000000],
    [375000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-3840000000000], [7380000000000])
    (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-3915000000000], [7380000000000]) (some (2, 7, 10))
    (some (2, 7, 10)) (.next ([-3915000000000], [7215000000000]) (some (2, 7, 10)) (some (2, 7, 10))
    (.next ([-915000000000], [1680000000000]) (some (2, 7, 10)) (some (2, 7, 10))
    fan45Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner0Part2 : FanWitness := (.next ([1410000000000], [2835000000000]) (some (0, 11, 7))
    (some (0, 11, 7)) (.next ([2250000000000], [5130000000000]) (some (0, 11, 7)) (some (0, 11, 7))
    (.next ([2250000000000], [5235000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([1125000000000], [2745000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([2085000000000],
    [5130000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([1875000000000], [5415000000000])
    (some (0, 11, 7)) (some (0, 11, 7)) (.next ([1710000000000], [5415000000000]) (some (0, 11, 7))
    (some (0, 11, 7)) (.next ([1320000000000], [5520000000000]) (some (0, 11, 7)) (some (0, 11, 7))
    (.next ([195000000000], [915000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([945000000000], [5805000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([270000000000],
    [2355000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([270000000000], [3570000000000])
    (some (0, 11, 7)) (some (0, 11, 8)) (.next ([180000000000], [3945000000000]) (some (0, 11, 8))
    (some (0, 11, 8)) (.next ([0], [1290000000000]) (some (0, 11, 8)) (some (0, 11, 8)) (.next
    ([-90000000000], [1590000000000]) (some (0, 11, 8)) (some (0, 11, 9)) (.next ([-750000000000],
    [7485000000000]) (some (0, 11, 9)) (some (0, 11, 9)) (.next ([-165000000000], [1455000000000])
    (some (0, 11, 9)) (some (0, 11, 9)) (.next ([-915000000000], [7485000000000]) (some (0, 11, 9))
    (some (0, 11, 9)) (.next ([-705000000000], [5250000000000]) (some (0, 11, 9)) (some (0, 11, 9))
    (.next ([-1110000000000], [7305000000000]) (some (0, 11, 9)) (some (1, 11, 9)) (.next
    ([-1080000000000], [6000000000000]) (some (1, 11, 9)) (some (1, 11, 9)) (.next
    ([-1290000000000], [7110000000000]) (some (1, 11, 9)) (some (1, 11, 9)) (.next
    ([-1290000000000], [6945000000000]) (some (1, 11, 9)) (some (1, 11, 9)) (.next
    ([-1245000000000], [6165000000000]) (some (1, 11, 9)) (some (1, 11, 9))
    fan45Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner0Part3 : FanWitness := (.next ([4380000000000], [3375000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.next ([4215000000000], [3540000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([195000000000], [180000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([390000000000], [375000000000]) (some (0, 3, 7)) (some (0, 4, 7)) (.next ([3840000000000],
    [3735000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([930000000000], [915000000000]) (some
    (0, 4, 7)) (some (0, 4, 7)) (.next ([375000000000], [375000000000]) (some (0, 4, 7)) (some (0,
    4, 7)) (.next ([2625000000000], [2835000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next
    ([180000000000], [195000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([3540000000000],
    [3840000000000]) (some (0, 4, 7)) (some (0, 5, 7)) (.next ([3465000000000], [3915000000000])
    (some (0, 5, 7)) (some (0, 5, 7)) (.next ([3300000000000], [3915000000000]) (some (0, 5, 7))
    (some (0, 5, 7)) (.next ([765000000000], [915000000000]) (some (0, 5, 7)) (some (0, 5, 7))
    (.next ([570000000000], [735000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next
    ([3165000000000], [4125000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next ([390000000000],
    [540000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next ([375000000000], [540000000000]) (some
    (0, 5, 7)) (some (0, 11, 7)) (.next ([3165000000000], [4590000000000]) (some (0, 11, 7)) (some
    (0, 11, 7)) (.next ([3000000000000], [4755000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next
    ([2535000000000], [4305000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([2790000000000],
    [4875000000000]) (some (0, 11, 7)) (some (0, 11, 7)) (.next ([2625000000000], [4950000000000])
    (some (0, 11, 7)) (some (0, 11, 7)) (.next ([2625000000000], [5040000000000]) (some (0, 11, 7))
    (some (0, 11, 7)) (.next ([180000000000], [360000000000]) (some (0, 11, 7)) (some (0, 11, 7))
    fan45Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner5Part0 : FanWitness := (.next ([3870000000000], [1380000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([4875000000000], [1935000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([3330000000000, 0], [1620000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 5))
    (.next ([1620000000000, -9000000000000], [885000000000]) (some (5, 1, 5)) (some (5, 1, 5))
    (.next ([4635000000000], [4365000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
    ([2445000000000], [4125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([1125000000000],
    [2700000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([765000000000], [2985000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([1305000000000], [7695000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([540000000000], [4710000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([0], [3330000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-315000000000,
    -9000000000000], [7695000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-885000000000],
    [4125000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1080000000000, -9000000000000],
    [4710000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1380000000000], [5250000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1935000000000], [6810000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-1620000000000, -9000000000000], [4950000000000, 9000000000000]) (some
    (0, 2, 5)) (some (0, 2, 5)) (.next ([-885000000000, 0], [2505000000000, -9000000000000]) (some
    (0, 2, 5)) (some (0, 2, 5)) (.next ([-4365000000000], [9000000000000]) (some (0, 2, 5)) (some
    (0, 3, 5)) (.next ([-4125000000000], [6570000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-2700000000000], [3825000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-2985000000000],
    [3750000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-7695000000000], [9000000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-4710000000000], [5250000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.terminal (some (0, 3, 5)) (some (0, 3, 5)) (some (0, 3,
    5)))))))))))))))))))))))))))

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6570000000000], [180000000000]) (some (2, 4, 1))
      (some (3, 4, 1)) (.next ([5820000000000], [750000000000]) (some (3, 4, 1)) (some (3, 4, 1))
      (.next ([2625000000000], [540000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next
      ([6000000000000], [1620000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([4950000000000, -9000000000000], [1800000000000, 9000000000000]) (some (3, 4, 2)) (some (3,
      4, 2)) (.next ([1005000000000, -9000000000000], [540000000000]) (some (3, 4, 2)) (some (3, 4,
      2)) (.next ([3405000000000], [2805000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [1620000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-180000000000],
      [6750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-750000000000], [6570000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-540000000000], [3165000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1620000000000, -9000000000000], [7620000000000, 9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1800000000000, -9000000000000], [6750000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-540000000000], [1545000000000, -9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2805000000000], [6210000000000]) (some (0, 1, 2))
      (some (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (4, 1, 2)) (some (4, 1,
      2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [1500000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([3165000000000], [6375000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1794000000000], [4665000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([84000000000], [3081000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [4665000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1500000000000], [6375000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6375000000000], [9540000000000]) (some (0, 1, 2))
      (some (0, 3, 2)) (.next ([-4665000000000], [6459000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3081000000000], [3165000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_9 : ExcludedOn (model40.B 9 ++ [step40.q]) 9000000000000 (model40.caps 9)
    (model40.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded41_0 : ExcludedOn (model41.B 0 ++ [step41.q]) 9000000000000 (model41.caps 0)
    (model41.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3240000000000], [885000000000]) (some (5, 0, 3))
      (some (5, 1, 3)) (.next ([5805000000000, 0], [1620000000000, 9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([3630000000000, -9000000000000], [1080000000000, 9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1620000000000, -9000000000000], [885000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4920000000000], [4125000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([1620000000000, 9000000000000], [1620000000000, 9000000000000]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([2160000000000, 9000000000000], [3090000000000,
      -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1125000000000], [2700000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1095000000000], [5250000000000]) (some (5, 1, 3))
      (some (5, 1, 4)) (.next ([735000000000, 9000000000000], [4125000000000, 0]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([540000000000], [4710000000000]) (some (5, 1, 4)) (some (5, 1, 4))
      (.next ([0, 0], [1620000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([-885000000000], [4125000000000]) (some (5, 1, 4)) (some (5, 2, 4)) (.next ([-1620000000000,
      -9000000000000], [7425000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-1080000000000, -9000000000000], [4710000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-885000000000, 0], [2505000000000, -9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-4125000000000], [9045000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next ([-1620000000000,
      -9000000000000], [3240000000000, 18000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-3090000000000, 9000000000000], [5250000000000, 0]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-2700000000000], [3825000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-5250000000000], [6345000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4125000000000,
      0], [4860000000000, 9000000000000]) (some (5, 3, 4)) (some (5, 3, 5)) (.next
      ([-4710000000000], [5250000000000]) (some (5, 3, 5)) (some (5, 3, 5)) (.terminal (some (5, 3,
      5)) (some (0, 3, 5)) (some (5, 3, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_7 : ExcludedOn (model41.B 7 ++ [step41.q]) 9000000000000 (model41.caps 7)
    (model41.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_8 : ExcludedOn (model41.B 8 ++ [step41.q]) 9000000000000 (model41.caps 8)
    (model41.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_9 : ExcludedOn (model41.B 9 ++ [step41.q]) 9000000000000 (model41.caps 9)
    (model41.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked41 : StepValid model41 9000000000000 step41 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded41_0
    · exact excluded41_1
    · exact excluded41_2
    · exact excluded41_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 6 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_3 : ExcludedOn (model42.B 3 ++ [step42.q]) 9000000000000 (model42.caps 3)
    (model42.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_6 : ExcludedOn (model42.B 6 ++ [step42.q]) 9000000000000 (model42.caps 6)
    (model42.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_7 : ExcludedOn (model42.B 7 ++ [step42.q]) 9000000000000 (model42.caps 7)
    (model42.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_8 : ExcludedOn (model42.B 8 ++ [step42.q]) 9000000000000 (model42.caps 8)
    (model42.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_9 : ExcludedOn (model42.B 9 ++ [step42.q]) 9000000000000 (model42.caps 9)
    (model42.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded42_6
    · exact excluded42_7
    · exact excluded42_8
    · exact excluded42_9
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded43_0 : ExcludedOn (model43.B 0 ++ [step43.q]) 9000000000000 (model43.caps 0)
    (model43.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1500000000000], [90000000000]) (some (9, 1, 6))
      (some (9, 2, 6)) (.next ([2970000000000], [195000000000]) (some (9, 2, 6)) (some (9, 2, 6))
      (.next ([6735000000000], [750000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next
      ([1290000000000], [165000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next ([2805000000000],
      [360000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next ([6570000000000], [915000000000])
      (some (9, 2, 6)) (some (9, 2, 6)) (.next ([6195000000000], [1110000000000]) (some (9, 2, 6))
      (some (9, 2, 6)) (.next ([3660000000000], [750000000000]) (some (9, 2, 6)) (some (9, 2, 6))
      (.next ([5820000000000], [1290000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next
      ([5655000000000], [1290000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next ([5460000000000],
      [1380000000000]) (some (9, 2, 6)) (some (9, 2, 6)) (.next ([285000000000], [90000000000])
      (some (9, 2, 6)) (some (9, 2, 6)) (.next ([1800000000000], [630000000000]) (some (9, 2, 6))
      (some (9, 2, 6)) fan43Owner0Part4))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_2 : ExcludedOn (model43.B 2 ++ [step43.q]) 9000000000000 (model43.caps 2)
    (model43.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([9000000000000, -9000000000000], [0,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([7380000000000, -9000000000000], [0,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([630000000000, -9000000000000], [0,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([7545000000000], [1455000000000])
      (some (0, 5, 2)) (some (0, 5, 2)) (.next ([7380000000000, -9000000000000], [1620000000000,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) fan43Owner2Part0)))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_4 : ExcludedOn (model43.B 4 ++ [step43.q]) 9000000000000 (model43.caps 4)
    (model43.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4950000000000], [300000000000]) (some (3, 0, 5))
      (some (3, 1, 5)) (.next ([7380000000000], [1620000000000]) (some (3, 1, 5)) (some (3, 1, 5))
      (.next ([6375000000000], [2655000000000]) (some (3, 1, 5)) (some (3, 1, 5))
      fan43Owner4Part0)))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_6 : ExcludedOn (model43.B 6 ++ [step43.q]) 9000000000000 (model43.caps 6)
    (model43.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_7 : ExcludedOn (model43.B 7 ++ [step43.q]) 9000000000000 (model43.caps 7)
    (model43.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_8 : ExcludedOn (model43.B 8 ++ [step43.q]) 9000000000000 (model43.caps 8)
    (model43.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_9 : ExcludedOn (model43.B 9 ++ [step43.q]) 9000000000000 (model43.caps 9)
    (model43.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded43_4
    · exact excluded43_5
    · exact excluded43_6
    · exact excluded43_7
    · exact excluded43_8
    · exact excluded43_9
theorem next43 : model43.insert step43 = model44 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded44_1 : ExcludedOn (model44.B 1 ++ [step44.q]) 9000000000000 (model44.caps 1)
    (model44.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_2 : ExcludedOn (model44.B 2 ++ [step44.q]) 9000000000000 (model44.caps 2)
    (model44.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000, -9000000000000], [0,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([630000000000, -9000000000000], [0,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([7380000000000, -9000000000000],
      [1620000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([5925000000000, 0],
      [1620000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([420000000000,
      -9000000000000], [120000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
      ([120000000000], [90000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([4125000000000],
      [4455000000000]) (some (0, 5, 2)) (some (0, 5, 2)) fan44Owner2Part0)))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_3 : ExcludedOn (model44.B 3 ++ [step44.q]) 9000000000000 (model44.caps 3)
    (model44.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [1380000000000]) (some (2, 0,
      1)) (some (3, 0, 4)) (.next ([6000000000000], [1620000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([5760000000000, -9000000000000], [1620000000000, 9000000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([1995000000000], [1380000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([3375000000000], [4005000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1755000000000, -9000000000000], [5625000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([0], [1620000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([-1380000000000], [7380000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-1620000000000, -9000000000000], [7620000000000, 9000000000000]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([-1620000000000, -9000000000000], [7380000000000]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([-1380000000000], [3375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-4005000000000], [7380000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5625000000000,
      -9000000000000], [7380000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_4 : ExcludedOn (model44.B 4 ++ [step44.q]) 9000000000000 (model44.caps 4)
    (model44.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_5 : ExcludedOn (model44.B 5 ++ [step44.q]) 9000000000000 (model44.caps 5)
    (model44.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_6 : ExcludedOn (model44.B 6 ++ [step44.q]) 9000000000000 (model44.caps 6)
    (model44.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_7 : ExcludedOn (model44.B 7 ++ [step44.q]) 9000000000000 (model44.caps 7)
    (model44.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_8 : ExcludedOn (model44.B 8 ++ [step44.q]) 9000000000000 (model44.caps 8)
    (model44.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_9 : ExcludedOn (model44.B 9 ++ [step44.q]) 9000000000000 (model44.caps 9)
    (model44.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked44 : StepValid model44 9000000000000 step44 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded44_1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([1500000000000], [90000000000]) (some (0, 2, 7))
      (some (0, 3, 7)) (.next ([6735000000000], [750000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([1290000000000], [165000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
      ([6570000000000], [915000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([4545000000000],
      [705000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([6195000000000], [1110000000000])
      (some (0, 3, 7)) (some (0, 3, 7)) (.next ([4920000000000], [1080000000000]) (some (0, 3, 7))
      (some (0, 3, 7)) (.next ([5820000000000], [1290000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([5655000000000], [1290000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
      ([4920000000000], [1245000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([285000000000],
      [90000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([1680000000000], [540000000000])
      (some (0, 3, 7)) (some (0, 3, 7)) (.next ([4740000000000], [1620000000000]) (some (0, 3, 7))
      (some (0, 3, 7)) (.next ([4890000000000], [1680000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([4545000000000], [1995000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
      ([5250000000000], [2565000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([4380000000000],
      [2160000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([360000000000], [180000000000])
      (some (0, 3, 7)) (some (0, 3, 7)) (.next ([4755000000000], [2625000000000]) (some (0, 3, 7))
      (some (0, 3, 7)) (.next ([540000000000], [375000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([4005000000000], [2925000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      fan45Owner0Part3))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_1 : ExcludedOn (model45.B 1 ++ [step45.q]) 9000000000000 (model45.caps 1)
    (model45.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_2 : ExcludedOn (model45.B 2 ++ [step45.q]) 9000000000000 (model45.caps 2)
    (model45.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_3 : ExcludedOn (model45.B 3 ++ [step45.q]) 9000000000000 (model45.caps 3)
    (model45.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_4 : ExcludedOn (model45.B 4 ++ [step45.q]) 9000000000000 (model45.caps 4)
    (model45.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_5 : ExcludedOn (model45.B 5 ++ [step45.q]) 9000000000000 (model45.caps 5)
    (model45.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7380000000000, -9000000000000], [315000000000,
      9000000000000]) (some (5, 0, 3)) (some (5, 1, 3)) (.next ([3240000000000], [885000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3630000000000, -9000000000000], [1080000000000,
      9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) fan45Owner5Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_7 : ExcludedOn (model45.B 7 ++ [step45.q]) 9000000000000 (model45.caps 7)
    (model45.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_8 : ExcludedOn (model45.B 8 ++ [step45.q]) 9000000000000 (model45.caps 8)
    (model45.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_9 : ExcludedOn (model45.B 9 ++ [step45.q]) 9000000000000 (model45.caps 9)
    (model45.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded45_7
    · exact excluded45_8
    · exact excluded45_9
theorem next45 : model45.insert step45 = model46 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded46_1 : ExcludedOn (model46.B 1 ++ [step46.q]) 9000000000000 (model46.caps 1)
    (model46.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1080000000000, 0], [120000000000,
      9000000000000]) (some (3, 4, 2)) (some (3, 4, 3)) (.next ([2040000000000], [1920000000000])
      (some (3, 4, 3)) (some (3, 4, 3)) (.next ([1620000000000, 9000000000000], [1620000000000,
      9000000000000]) (some (3, 4, 3)) (some (3, 4, 3)) (.next ([1920000000000, -9000000000000],
      [3120000000000, 9000000000000]) (some (3, 4, 3)) none (.next ([3540000000000],
      [6210000000000]) none none (.next ([1620000000000, 9000000000000], [3090000000000,
      -9000000000000]) none none (.next ([540000000000, 9000000000000], [1500000000000]) none none
      (.next ([1500000000000], [4290000000000]) none none (.next ([120000000000, 9000000000000],
      [3420000000000, -9000000000000]) (some (4, 4, 3)) (some (4, 4, 3)) (.next ([0],
      [6330000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-120000000000,
      -9000000000000], [1200000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-1920000000000], [3960000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-1620000000000,
      -9000000000000], [3240000000000, 18000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3120000000000, -9000000000000], [5040000000000, 0]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-6210000000000], [9750000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3090000000000, 9000000000000], [4710000000000, 0]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-1500000000000], [2040000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-4290000000000], [5790000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-3420000000000,
      9000000000000], [3540000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2, 3))
      (some (4, 2, 3)) (some (4, 2, 3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_2 : ExcludedOn (model46.B 2 ++ [step46.q]) 9000000000000 (model46.caps 2)
    (model46.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_3 : ExcludedOn (model46.B 3 ++ [step46.q]) 9000000000000 (model46.caps 3)
    (model46.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_4 : ExcludedOn (model46.B 4 ++ [step46.q]) 9000000000000 (model46.caps 4)
    (model46.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_5 : ExcludedOn (model46.B 5 ++ [step46.q]) 9000000000000 (model46.caps 5)
    (model46.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_6 : ExcludedOn (model46.B 6 ++ [step46.q]) 9000000000000 (model46.caps 6)
    (model46.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5580000000000, 9000000000000], [1920000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([3960000000000], [3540000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1710000000000], [1830000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([1905000000000], [5790000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([1620000000000, 9000000000000], [5790000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([1620000000000, 9000000000000], [6075000000000, -9000000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([195000000000], [3960000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([0], [7695000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1920000000000,
      9000000000000], [7500000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-3540000000000],
      [7500000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1830000000000], [3540000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5790000000000], [7695000000000]) (some (0, 2, 3))
      (some (0, 2, 4)) (.next ([-5790000000000, 0], [7410000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-6075000000000, 9000000000000], [7695000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-3960000000000], [4155000000000]) (some (0, 2, 4)) (some (1, 2, 4))
      (.terminal (some (1, 2, 0)) (some (1, 2, 0)) (some (1, 2, 0))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_7 : ExcludedOn (model46.B 7 ++ [step46.q]) 9000000000000 (model46.caps 7)
    (model46.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_8 : ExcludedOn (model46.B 8 ++ [step46.q]) 9000000000000 (model46.caps 8)
    (model46.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_9 : ExcludedOn (model46.B 9 ++ [step46.q]) 9000000000000 (model46.caps 9)
    (model46.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked46 : StepValid model46 9000000000000 step46 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded46_1
    · exact excluded46_2
    · exact excluded46_3
    · exact excluded46_4
    · exact excluded46_5
    · exact excluded46_6
    · exact excluded46_7
    · exact excluded46_8
    · exact excluded46_9
theorem next46 : model46.insert step46 = model47 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown180000190000
end ConwaySoifer.Simplified.Certificates
