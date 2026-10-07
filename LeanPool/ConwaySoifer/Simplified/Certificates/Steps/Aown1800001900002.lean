/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown180000190000
import Mathlib.Tactic.FinCases

/-!
# Aown 180000 190000 2

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
def fan19Owner0Part0 : FanWitness := (.next ([-375000000000], [750000000000]) (some (0, 6, 10))
    (some (0, 6, 10)) (.next ([-4875000000000], [9735000000000]) (some (0, 6, 10)) (some (1, 6, 10))
    (.next ([-195000000000], [375000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-2865000000000], [5490000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-5055000000000], [9540000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-2865000000000], [5325000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-5055000000000], [9375000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-2190000000000], [4050000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-4140000000000], [7380000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-1950000000000], [3330000000000]) (some (1, 6, 10)) (some (1, 10, 10)) (.next
    ([-540000000000], [915000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-1710000000000], [2805000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-1875000000000], [2970000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-1440000000000], [2250000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-360000000000], [540000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next ([-915000000000],
    [1275000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next ([-2625000000000],
    [3345000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next ([-1995000000000],
    [2535000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next ([-915000000000], [1110000000000])
    (some (1, 10, 10)) (some (1, 10, 10)) (.next ([-2790000000000], [3345000000000]) (some (1, 10,
    10)) (some (1, 10, 10)) (.next ([-2160000000000], [2535000000000]) (some (1, 10, 10)) (some (1,
    10, 10)) (.next ([-1290000000000], [1455000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-2520000000000], [2820000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-2985000000000], [3165000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.terminal (some (1,
    10, 10)) (some (1, 10, 10)) (some (1, 10, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part1 : FanWitness := (.next ([300000000000], [2520000000000]) (some (9, 4, 10))
    (some (9, 4, 10)) (.next ([180000000000], [2985000000000]) (some (9, 4, 10)) (some (9, 4, 10))
    (.next ([0], [1290000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next ([-195000000000],
    [3165000000000]) (some (0, 4, 10)) (some (0, 5, 10)) (.next ([-165000000000], [1455000000000])
    (some (0, 5, 10)) (some (0, 5, 10)) (.next ([-360000000000], [3165000000000]) (some (0, 5, 10))
    (some (0, 5, 10)) (.next ([-375000000000], [2535000000000]) (some (0, 5, 10)) (some (0, 5, 10))
    (.next ([-540000000000], [2535000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-1410000000000], [5325000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-1575000000000], [5490000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-1890000000000], [6570000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next ([-735000000000],
    [2355000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next ([-180000000000], [540000000000])
    (some (0, 5, 10)) (some (0, 5, 10)) (.next ([-3600000000000], [9375000000000]) (some (0, 5, 10))
    (some (0, 5, 10)) (.next ([-3765000000000], [9540000000000]) (some (0, 5, 10)) (some (0, 5, 10))
    (.next ([-2325000000000], [5865000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-375000000000], [915000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next ([-915000000000],
    [2160000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next ([-2490000000000], [5865000000000])
    (some (0, 5, 10)) (some (0, 5, 10)) (.next ([-4515000000000], [9915000000000]) (some (0, 5, 10))
    (some (0, 5, 10)) (.next ([-915000000000], [1995000000000]) (some (0, 5, 10)) (some (0, 5, 10))
    (.next ([-4680000000000], [9915000000000]) (some (0, 5, 10)) (some (0, 6, 10)) (.next
    ([-2685000000000], [5685000000000]) (some (0, 6, 10)) (some (0, 6, 10)) (.next ([-180000000000],
    [375000000000]) (some (0, 6, 10)) (some (0, 6, 10)) fan19Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part2 : FanWitness := (.next ([3000000000000], [2685000000000]) (some (8, 2, 10))
    (some (8, 2, 10)) (.next ([195000000000], [180000000000]) (some (8, 2, 10)) (some (8, 2, 10))
    (.next ([375000000000], [375000000000]) (some (8, 2, 10)) (some (8, 3, 10)) (.next
    ([4860000000000], [4875000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([180000000000],
    [195000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([2625000000000], [2865000000000])
    (some (8, 3, 10)) (some (8, 4, 10)) (.next ([4485000000000], [5055000000000]) (some (8, 4, 10))
    (some (8, 4, 10)) (.next ([2460000000000], [2865000000000]) (some (8, 4, 10)) (some (8, 4, 10))
    (.next ([4320000000000], [5055000000000]) (some (8, 4, 10)) (some (8, 4, 10)) (.next
    ([1860000000000], [2190000000000]) (some (8, 4, 10)) (some (8, 4, 10)) (.next ([3240000000000],
    [4140000000000]) (some (8, 4, 10)) (some (8, 4, 10)) (.next ([1380000000000], [1950000000000])
    (some (8, 4, 10)) (some (8, 4, 10)) (.next ([375000000000], [540000000000]) (some (8, 4, 10))
    (some (8, 4, 10)) (.next ([1095000000000], [1710000000000]) (some (8, 4, 10)) (some (8, 4, 10))
    (.next ([1095000000000], [1875000000000]) (some (8, 4, 10)) (some (9, 4, 10)) (.next
    ([810000000000], [1440000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next ([180000000000],
    [360000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next ([360000000000], [915000000000])
    (some (9, 4, 10)) (some (9, 4, 10)) (.next ([720000000000], [2625000000000]) (some (9, 4, 10))
    (some (9, 4, 10)) (.next ([540000000000], [1995000000000]) (some (9, 4, 10)) (some (9, 4, 10))
    (.next ([195000000000], [915000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next
    ([555000000000], [2790000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next ([375000000000],
    [2160000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next ([165000000000], [1290000000000])
    (some (9, 4, 10)) (some (9, 4, 10)) fan19Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner0Part0 : FanWitness := (.next ([-375000000000], [915000000000]) (some (0, 6, 10))
    (some (0, 6, 10)) (.next ([-3990000000000], [9540000000000]) (some (0, 6, 10)) (some (0, 6, 10))
    (.next ([-2490000000000], [5865000000000]) (some (0, 6, 10)) (some (0, 6, 10)) (.next
    ([-3990000000000], [9375000000000]) (some (0, 6, 10)) (some (0, 6, 10)) (.next
    ([-2685000000000], [5685000000000]) (some (0, 6, 10)) (some (0, 6, 10)) (.next ([-180000000000],
    [375000000000]) (some (0, 6, 10)) (some (0, 6, 10)) (.next ([-375000000000], [750000000000])
    (some (0, 6, 10)) (some (0, 6, 10)) (.next ([-195000000000], [375000000000]) (some (0, 6, 10))
    (some (1, 6, 10)) (.next ([-2865000000000], [5490000000000]) (some (1, 6, 10)) (some (1, 6, 10))
    (.next ([-2865000000000], [5325000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-1380000000000], [2430000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next ([-540000000000],
    [915000000000]) (some (1, 6, 10)) (some (1, 10, 10)) (.next ([-1710000000000], [2805000000000])
    (some (1, 10, 10)) (some (1, 10, 10)) (.next ([-1875000000000], [2970000000000]) (some (1, 10,
    10)) (some (1, 10, 10)) (.next ([-360000000000], [540000000000]) (some (1, 10, 10)) (some (1,
    10, 10)) (.next ([-915000000000], [1275000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-2625000000000], [3345000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-915000000000], [1110000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-2790000000000], [3345000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-1620000000000], [1875000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-4140000000000], [4695000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-1290000000000], [1455000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-2520000000000], [2820000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.next
    ([-2985000000000], [3165000000000]) (some (1, 10, 10)) (some (1, 10, 10)) (.terminal (some (1,
    10, 10)) (some (1, 10, 10)) (some (1, 10, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner0Part1 : FanWitness := (.next ([300000000000], [2520000000000]) (some (9, 4, 10))
    (some (9, 4, 10)) (.next ([180000000000], [2985000000000]) (some (9, 4, 10)) (some (9, 4, 10))
    (.next ([0], [1290000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next ([-195000000000],
    [3165000000000]) (some (0, 4, 10)) (some (0, 5, 10)) (.next ([-165000000000], [1455000000000])
    (some (0, 5, 10)) (some (0, 5, 10)) (.next ([-360000000000], [3165000000000]) (some (0, 5, 10))
    (some (0, 5, 10)) (.next ([-825000000000], [6570000000000]) (some (0, 5, 10)) (some (0, 5, 10))
    (.next ([-1155000000000], [6945000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-1320000000000], [7110000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-1410000000000], [5325000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-2535000000000], [9375000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-2070000000000], [7485000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-1125000000000], [4050000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-2700000000000], [9540000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-1575000000000], [5490000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-2235000000000], [7485000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-2430000000000], [7305000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next ([-180000000000],
    [540000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next ([-3450000000000], [9915000000000])
    (some (0, 5, 10)) (some (0, 5, 10)) (.next ([-3615000000000], [9915000000000]) (some (0, 5, 10))
    (some (0, 5, 10)) (.next ([-2610000000000], [7110000000000]) (some (0, 5, 10)) (some (0, 5, 10))
    (.next ([-2610000000000], [6945000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-3810000000000], [9735000000000]) (some (0, 5, 10)) (some (0, 6, 10)) (.next
    ([-2325000000000], [5865000000000]) (some (0, 6, 10)) (some (0, 6, 10))
    fan21Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner0Part2 : FanWitness := (.next ([5925000000000], [3810000000000]) (some (8, 2, 10))
    (some (8, 2, 10)) (.next ([3540000000000], [2325000000000]) (some (8, 2, 10)) (some (8, 2, 10))
    (.next ([540000000000], [375000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
    ([5550000000000], [3990000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([3375000000000],
    [2490000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([5385000000000], [3990000000000])
    (some (8, 2, 10)) (some (8, 2, 10)) (.next ([3000000000000], [2685000000000]) (some (8, 2, 10))
    (some (8, 2, 10)) (.next ([195000000000], [180000000000]) (some (8, 2, 10)) (some (8, 2, 10))
    (.next ([375000000000], [375000000000]) (some (8, 2, 10)) (some (8, 3, 10)) (.next
    ([180000000000], [195000000000]) (some (8, 3, 10)) (some (8, 3, 10)) (.next ([2625000000000],
    [2865000000000]) (some (8, 3, 10)) (some (8, 4, 10)) (.next ([2460000000000], [2865000000000])
    (some (8, 4, 10)) (some (8, 4, 10)) (.next ([1050000000000], [1380000000000]) (some (8, 4, 10))
    (some (8, 4, 10)) (.next ([375000000000], [540000000000]) (some (8, 4, 10)) (some (8, 4, 10))
    (.next ([1095000000000], [1710000000000]) (some (8, 4, 10)) (some (8, 4, 10)) (.next
    ([1095000000000], [1875000000000]) (some (8, 4, 10)) (some (9, 4, 10)) (.next ([180000000000],
    [360000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next ([360000000000], [915000000000])
    (some (9, 4, 10)) (some (9, 4, 10)) (.next ([720000000000], [2625000000000]) (some (9, 4, 10))
    (some (9, 4, 10)) (.next ([195000000000], [915000000000]) (some (9, 4, 10)) (some (9, 4, 10))
    (.next ([555000000000], [2790000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next
    ([255000000000], [1620000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next ([555000000000],
    [4140000000000]) (some (9, 4, 10)) (some (9, 4, 10)) (.next ([165000000000], [1290000000000])
    (some (9, 4, 10)) (some (9, 4, 10)) fan21Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner0Part0 : FanWitness := (.next ([-375000000000], [750000000000]) (some (0, 6, 11))
    (some (0, 6, 11)) (.next ([-1620000000000], [3195000000000]) (some (0, 6, 11)) (some (1, 6, 11))
    (.next ([-195000000000], [375000000000]) (some (1, 6, 11)) (some (1, 6, 11)) (.next
    ([-2865000000000], [5490000000000]) (some (1, 6, 11)) (some (1, 6, 11)) (.next
    ([-2865000000000], [5325000000000]) (some (1, 6, 11)) (some (1, 6, 11)) (.next ([-540000000000],
    [915000000000]) (some (1, 6, 11)) (some (1, 6, 11)) (.next ([-1710000000000], [2805000000000])
    (some (1, 6, 11)) (some (1, 6, 11)) (.next ([-1875000000000], [2970000000000]) (some (1, 6, 11))
    (some (1, 6, 11)) (.next ([-360000000000], [540000000000]) (some (1, 6, 11)) (some (1, 6, 11))
    (.next ([-4140000000000], [6015000000000]) (some (1, 6, 11)) (some (1, 6, 11)) (.next
    ([-1245000000000], [1800000000000]) (some (1, 6, 11)) (some (1, 6, 11)) (.next ([-915000000000],
    [1275000000000]) (some (1, 6, 11)) (some (1, 11, 11)) (.next ([-2625000000000], [3345000000000])
    (some (1, 11, 11)) (some (1, 11, 11)) (.next ([-915000000000], [1110000000000]) (some (1, 11,
    11)) (some (1, 11, 11)) (.next ([-2790000000000], [3345000000000]) (some (1, 11, 11)) (some (1,
    11, 11)) (.next ([-1620000000000], [1875000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-4140000000000], [4695000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-1290000000000], [1455000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-2520000000000], [2820000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-5940000000000], [6570000000000]) (some (1, 11, 11)) (some (1, 11, 11)) (.next
    ([-3420000000000], [3750000000000]) (some (1, 11, 9)) (some (1, 11, 9)) (.next
    ([-2985000000000], [3165000000000]) (some (1, 11, 9)) (some (1, 11, 9)) (.next
    ([-1800000000000], [1875000000000]) (some (1, 11, 9)) (some (1, 11, 9)) (.next
    ([-6945000000000], [7110000000000]) (some (1, 11, 9)) (some (1, 11, 9)) (.terminal (some (1, 11,
    9)) (some (1, 11, 9)) (some (1, 11, 9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner0Part1 : FanWitness := (.next ([-1245000000000], [8910000000000]) (some (0, 5, 11))
    (some (0, 5, 11)) (.next ([-1110000000000], [7305000000000]) (some (0, 5, 11)) (some (0, 5, 11))
    (.next ([-1155000000000], [6945000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next
    ([-1290000000000], [7110000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next
    ([-1320000000000], [7110000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next
    ([-1290000000000], [6945000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next
    ([-1995000000000], [9285000000000]) (some (0, 5, 11)) (some (0, 6, 11)) (.next
    ([-2160000000000], [9285000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next
    ([-2355000000000], [9105000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next
    ([-1410000000000], [5325000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next
    ([-2070000000000], [7485000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next
    ([-2535000000000], [8910000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next
    ([-1575000000000], [5490000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next
    ([-2535000000000], [8745000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next
    ([-2235000000000], [7485000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next
    ([-2430000000000], [7305000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next ([-180000000000],
    [540000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next ([-2610000000000], [7110000000000])
    (some (0, 6, 11)) (some (0, 6, 11)) (.next ([-2610000000000], [6945000000000]) (some (0, 6, 11))
    (some (0, 6, 11)) (.next ([-2325000000000], [5865000000000]) (some (0, 6, 11)) (some (0, 6, 11))
    (.next ([-375000000000], [915000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next
    ([-2490000000000], [5865000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next
    ([-2685000000000], [5685000000000]) (some (0, 6, 11)) (some (0, 6, 11)) (.next ([-180000000000],
    [375000000000]) (some (0, 6, 11)) (some (0, 6, 11)) fan23Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner0Part2 : FanWitness := (.next ([1095000000000], [1875000000000]) (some (9, 4, 11))
    (some (10, 4, 11)) (.next ([180000000000], [360000000000]) (some (10, 4, 11)) (some (10, 4, 11))
    (.next ([1875000000000], [4140000000000]) (some (10, 4, 11)) (some (10, 4, 11)) (.next
    ([555000000000], [1245000000000]) (some (10, 4, 11)) (some (10, 4, 11)) (.next ([360000000000],
    [915000000000]) (some (10, 4, 11)) (some (10, 4, 11)) (.next ([720000000000], [2625000000000])
    (some (10, 4, 11)) (some (10, 4, 11)) (.next ([195000000000], [915000000000]) (some (10, 4, 11))
    (some (10, 4, 11)) (.next ([555000000000], [2790000000000]) (some (10, 4, 11)) (some (10, 4,
    11)) (.next ([255000000000], [1620000000000]) (some (10, 4, 11)) (some (10, 4, 11)) (.next
    ([555000000000], [4140000000000]) (some (10, 4, 11)) (some (10, 4, 11)) (.next ([165000000000],
    [1290000000000]) (some (10, 4, 11)) (some (10, 4, 11)) (.next ([300000000000], [2520000000000])
    (some (10, 4, 11)) (some (10, 4, 11)) (.next ([630000000000], [5940000000000]) (some (10, 4,
    11)) (some (10, 4, 11)) (.next ([330000000000], [3420000000000]) (some (10, 4, 11)) (some (10,
    4, 11)) (.next ([180000000000], [2985000000000]) (some (10, 4, 11)) (some (10, 4, 11)) (.next
    ([75000000000], [1800000000000]) (some (10, 4, 11)) (some (10, 4, 11)) (.next ([165000000000],
    [6945000000000]) (some (10, 4, 11)) (some (10, 4, 11)) (.next ([0], [1290000000000]) (some (10,
    4, 11)) (some (10, 4, 11)) (.next ([-195000000000], [3165000000000]) (some (0, 4, 11)) (some (0,
    5, 11)) (.next ([-750000000000], [7485000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next
    ([-165000000000], [1455000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-360000000000],
    [3165000000000]) (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-915000000000], [7485000000000])
    (some (0, 5, 11)) (some (0, 5, 11)) (.next ([-1080000000000], [8745000000000]) (some (0, 5, 11))
    (some (0, 5, 11)) fan23Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner0Part3 : FanWitness := (.next ([7125000000000], [2160000000000]) (some (9, 2, 11))
    (some (9, 2, 11)) (.next ([6750000000000], [2355000000000]) (some (9, 2, 11)) (some (9, 2, 11))
    (.next ([3915000000000], [1410000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
    ([5415000000000], [2070000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([6375000000000],
    [2535000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([3915000000000], [1575000000000])
    (some (9, 2, 11)) (some (9, 2, 11)) (.next ([6210000000000], [2535000000000]) (some (9, 2, 11))
    (some (9, 2, 11)) (.next ([5250000000000], [2235000000000]) (some (9, 2, 11)) (some (9, 2, 11))
    (.next ([4875000000000], [2430000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
    ([360000000000], [180000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([4500000000000],
    [2610000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([4335000000000], [2610000000000])
    (some (9, 2, 11)) (some (9, 2, 11)) (.next ([3540000000000], [2325000000000]) (some (9, 2, 11))
    (some (9, 2, 11)) (.next ([540000000000], [375000000000]) (some (9, 2, 11)) (some (9, 2, 11))
    (.next ([3375000000000], [2490000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
    ([3000000000000], [2685000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([195000000000],
    [180000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([375000000000], [375000000000])
    (some (9, 2, 11)) (some (9, 3, 11)) (.next ([1575000000000], [1620000000000]) (some (9, 3, 11))
    (some (9, 3, 11)) (.next ([180000000000], [195000000000]) (some (9, 3, 11)) (some (9, 3, 11))
    (.next ([2625000000000], [2865000000000]) (some (9, 3, 11)) (some (9, 4, 11)) (.next
    ([2460000000000], [2865000000000]) (some (9, 4, 11)) (some (9, 4, 11)) (.next ([375000000000],
    [540000000000]) (some (9, 4, 11)) (some (9, 4, 11)) (.next ([1095000000000], [1710000000000])
    (some (9, 4, 11)) (some (9, 4, 11)) fan23Owner0Part2))))))))))))))))))))))))

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6570000000000], [180000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7500000000000, 0], [1080000000000, 9000000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7380000000000, -9000000000000], [1620000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([4950000000000, -9000000000000], [1800000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3459000000000, 0], [1620000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([3279000000000], [3291000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([540000000000], [3501000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([750000000000], [6030000000000]) (some (0, 4, 1)) (some (0, 4, 2))
      (.next ([630000000000, -9000000000000], [6570000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([540000000000], [6960000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0, 0],
      [1620000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-180000000000],
      [6750000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-1080000000000, -9000000000000],
      [8580000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1620000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1800000000000, -9000000000000], [6750000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1620000000000, -9000000000000], [5079000000000, 9000000000000]) (some (0, 1, 3)) (some (4,
      1, 3)) (.next ([-3291000000000], [6570000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-3501000000000], [4041000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-6030000000000], [6780000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-6570000000000,
      0], [7200000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-6960000000000], [7500000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5760000000000], [1485000000000, 9000000000000])
      (some (2, 0, 4)) (some (3, 0, 4)) (.next ([5955000000000], [1620000000000, 9000000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([6750000000000], [2430000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([195000000000], [135000000000]) (some (3, 0, 4)) (some (3, 0, 4))
      (.next ([5130000000000, -9000000000000], [4050000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 0, 4)) (.next ([3525000000000], [3225000000000]) (some (3, 0, 4)) (some (3, 4, 4))
      (.next ([3195000000000], [3420000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([135000000000], [5625000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [1620000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-1485000000000,
      -9000000000000], [7245000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1620000000000, -9000000000000], [7575000000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([-2430000000000], [9180000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-135000000000], [330000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4050000000000,
      -9000000000000], [9180000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3225000000000],
      [6750000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3420000000000], [6615000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5625000000000], [5760000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4,
      2))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded17_0 : ExcludedOn (model17.B 0 ++ [step17.q]) 9000000000000 (model17.caps 0)
    (model17.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_9 : ExcludedOn (model17.B 9 ++ [step17.q]) 9000000000000 (model17.caps 9)
    (model17.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2370000000000, 0], [5760000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 1, 2)) (.next ([2370000000000], [7380000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([750000000000, -9000000000000], [7380000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1620000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 1, 3)) (.next ([-5760000000000, 9000000000000], [8130000000000, -9000000000000])
      (some (3, 1, 3)) (some (3, 1, 3)) (.next ([-7380000000000], [9750000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-7380000000000], [8130000000000, -9000000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded17_6
    · exact excluded17_7
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [2760000000000]) none none
      (.next ([3570000000000, 9000000000000], [2430000000000, -9000000000000]) none none (.next
      ([1620000000000, 9000000000000], [1620000000000, 9000000000000]) none none (.next
      ([1620000000000, 9000000000000], [3090000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([330000000000, -9000000000000], [4050000000000, 0]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([0], [6330000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2760000000000], [8760000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2430000000000,
      9000000000000], [6000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1620000000000,
      -9000000000000], [3240000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3090000000000, 9000000000000], [4710000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4050000000000, 0], [4380000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7500000000000, 0], [1080000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7380000000000, -9000000000000],
      [1620000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([420000000000,
      -9000000000000], [120000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next
      ([4050000000000], [3000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2430000000000,
      -9000000000000], [4620000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next
      ([540000000000], [3501000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([450000000000],
      [3510000000000]) (some (0, 4, 1)) (some (0, 4, 2)) (.next ([459000000000], [3591000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([540000000000], [6960000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([0, 0], [1620000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-1080000000000, -9000000000000], [8580000000000, 9000000000000]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([-1620000000000, -9000000000000], [9000000000000, 0]) (some (0, 1,
      3)) (some (0, 1, 3)) (.next ([-120000000000, -9000000000000], [540000000000, 0]) (some (0, 1,
      3)) (some (0, 1, 3)) (.next ([-3000000000000], [7050000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-4620000000000, -9000000000000], [7050000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([-3501000000000], [4041000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-3510000000000], [3960000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-3591000000000], [4050000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-6960000000000], [7500000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded18_1
    · exact excluded18_2
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

theorem excluded19_0 : ExcludedOn (model19.B 0 ++ [step19.q]) 9000000000000 (model19.caps 0)
    (model19.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2970000000000], [195000000000]) (some (10, 1,
      10)) (some (10, 2, 10)) (.next ([1290000000000], [165000000000]) (some (10, 2, 10)) (some (10,
      2, 10)) (.next ([2805000000000], [360000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([2160000000000], [375000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([1995000000000], [540000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([3915000000000], [1410000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([3915000000000], [1575000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([4680000000000], [1890000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([1620000000000], [735000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([360000000000],
      [180000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([5775000000000], [3600000000000])
      (some (8, 2, 10)) (some (8, 2, 10)) (.next ([5775000000000], [3765000000000]) (some (8, 2,
      10)) (some (8, 2, 10)) (.next ([3540000000000], [2325000000000]) (some (8, 2, 10)) (some (8,
      2, 10)) (.next ([540000000000], [375000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([1245000000000], [915000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([3375000000000],
      [2490000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([5400000000000], [4515000000000])
      (some (8, 2, 10)) (some (8, 2, 10)) (.next ([1080000000000], [915000000000]) (some (8, 2, 10))
      (some (8, 2, 10)) (.next ([5235000000000], [4680000000000]) (some (8, 2, 10)) (some (8, 2,
      10)) fan19Owner0Part2))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4140000000000], [570000000000]) none none (.next
      ([1620000000000, 9000000000000], [1620000000000, 9000000000000]) none none (.next
      ([1620000000000, 9000000000000], [3090000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([1620000000000, 9000000000000], [4140000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([0, 0], [2520000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-570000000000], [4710000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1620000000000,
      -9000000000000], [3240000000000, 18000000000000]) (some (3, 1, 2)) none (.next
      ([-3090000000000, 9000000000000], [4710000000000, 0]) none none (.next ([-4140000000000],
      [5760000000000, 9000000000000]) none none (.terminal none none none))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4140000000000], [2430000000000]) (some (2, 0,
      1)) (some (3, 0, 2)) (.next ([4140000000000], [4860000000000]) (some (3, 0, 2)) (some (3, 0,
      2)) (.next ([2520000000000, -9000000000000], [4860000000000]) (some (3, 0, 2)) (some (3, 0,
      2)) (.next ([810000000000, -9000000000000], [1620000000000, 9000000000000]) (some (3, 0, 2))
      (some (4, 0, 2)) (.next ([1620000000000, 9000000000000], [4950000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1620000000000, 9000000000000], [7380000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0], [7380000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2430000000000], [6570000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-4860000000000], [9000000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([-4860000000000, 0], [7380000000000, -9000000000000]) (some (4, 0,
      2)) (some (4, 0, 2)) (.next ([-1620000000000, -9000000000000], [2430000000000]) (some (4, 0,
      2)) (some (4, 0, 2)) (.next ([-4950000000000, 9000000000000], [6570000000000, 0]) (some (4, 0,
      2)) (some (4, 0, 2)) (.next ([-7380000000000, 9000000000000], [9000000000000, 0]) (some (4, 0,
      2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (0, 1, 2)) (some (4, 1,
      2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
    · exact excluded19_0
    · exact excluded19_1
    · exact (hj rfl).elim
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

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3315000000000, 9000000000000], [810000000000,
      -9000000000000]) none none (.next ([4125000000000], [3015000000000]) none none (.next
      ([1620000000000, 9000000000000], [1620000000000, 9000000000000]) none none (.next
      ([1620000000000, 9000000000000], [3090000000000, -9000000000000]) none none (.next
      ([75000000000, -9000000000000], [2430000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-810000000000, 9000000000000], [4125000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3015000000000], [7140000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1620000000000,
      -9000000000000], [3240000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3090000000000, 9000000000000], [4710000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.terminal (some (3, 1, 2)) none none))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (5) (6) (600) (.witnessedFan (.next ([2430000000000],
      [15000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7500000000000, 0], [1080000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([7380000000000, -9000000000000],
      [1620000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([4860000000000, 0],
      [1620000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2430000000000],
      [4875000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([540000000000], [2100000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([810000000000, -9000000000000], [6495000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 2)) (.next ([195000000000], [1890000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([540000000000], [6960000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([75000000000, -9000000000000], [2430000000000, 0]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([0, 0], [1620000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.next ([-15000000000], [2445000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next
      ([-1080000000000, -9000000000000], [8580000000000, 9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-1620000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some
      (0, 1, 3)) (.next ([-1620000000000, -9000000000000], [6480000000000, 9000000000000]) (some (0,
      1, 3)) (some (0, 1, 3)) (.next ([-4875000000000], [7305000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-2100000000000], [2640000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-6495000000000, -9000000000000], [7305000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1890000000000], [2085000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-6960000000000], [7500000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2430000000000,
      0], [2505000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3))))))))))))))))))))))))) (.witnessedFan (.next
      ([2505000000000, -9000000000000], [-75000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4,
      1)) (.next ([7500000000000, 0], [1080000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4,
      1)) (.next ([7380000000000, -9000000000000], [1620000000000, 9000000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([4860000000000, 0], [1620000000000, 9000000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([420000000000, -9000000000000], [120000000000, 9000000000000]) (some
      (0, 4, 1)) (some (0, 4, 1)) (.next ([2430000000000], [4875000000000]) (some (0, 4, 1)) (some
      (0, 4, 1)) (.next ([540000000000], [2100000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next
      ([810000000000, -9000000000000], [6495000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4,
      2)) (.next ([195000000000], [1890000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([540000000000], [6960000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0, 0],
      [1620000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([75000000000,
      -9000000000000], [2430000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next
      ([-1080000000000, -9000000000000], [8580000000000, 9000000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-1620000000000, -9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some
      (0, 1, 3)) (.next ([-1620000000000, -9000000000000], [6480000000000, 9000000000000]) (some (0,
      1, 3)) (some (0, 1, 3)) (.next ([-120000000000, -9000000000000], [540000000000, 0]) (some (0,
      1, 3)) (some (0, 1, 3)) (.next ([-4875000000000], [7305000000000]) (some (0, 1, 3)) (some (0,
      1, 3)) (.next ([-2100000000000], [2640000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-6495000000000, -9000000000000], [7305000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-1890000000000], [2085000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.next
      ([-6960000000000], [7500000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1,
      3)) (some (4, 1, 0)) (some (4, 1, 3)))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded20_1
    · exact excluded20_2
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
  apply ExclusionHint.sound (.witnessedFan (.next ([2970000000000], [195000000000]) (some (10, 1,
      10)) (some (10, 2, 10)) (.next ([1290000000000], [165000000000]) (some (10, 2, 10)) (some (10,
      2, 10)) (.next ([2805000000000], [360000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([5745000000000], [825000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([5790000000000], [1155000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([5790000000000], [1320000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([3915000000000], [1410000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([6840000000000], [2535000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([5415000000000], [2070000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([2925000000000], [1125000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([6840000000000], [2700000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([3915000000000], [1575000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([5250000000000], [2235000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next
      ([4875000000000], [2430000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([360000000000],
      [180000000000]) (some (8, 2, 10)) (some (8, 2, 10)) (.next ([6465000000000], [3450000000000])
      (some (8, 2, 10)) (some (8, 2, 10)) (.next ([6300000000000], [3615000000000]) (some (8, 2,
      10)) (some (8, 2, 10)) (.next ([4500000000000], [2610000000000]) (some (8, 2, 10)) (some (8,
      2, 10)) (.next ([4335000000000], [2610000000000]) (some (8, 2, 10)) (some (8, 2, 10))
      fan21Owner0Part2))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3075000000000], [1635000000000]) none none
      (.next ([1620000000000, 9000000000000], [1620000000000, 9000000000000]) none none (.next
      ([1620000000000, 9000000000000], [3090000000000, -9000000000000]) none none (.next ([0, 0],
      [1455000000000, -9000000000000]) none none (.next ([-1635000000000], [4710000000000]) (some
      (3, 1, 2)) none (.next ([-1620000000000, -9000000000000], [3240000000000, 18000000000000])
      none none (.next ([-3090000000000, 9000000000000], [4710000000000, 0]) none none (.terminal
      none none none))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3075000000000], [3495000000000]) (some (2, 0,
      1)) (some (3, 0, 2)) (.next ([3075000000000], [5925000000000]) (some (3, 0, 2)) (some (3, 0,
      2)) (.next ([810000000000, -9000000000000], [1620000000000, 9000000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1620000000000, 9000000000000], [4950000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1455000000000, -9000000000000], [5925000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [7380000000000, -9000000000000]) (some (3,
      0, 2)) (some (4, 0, 2)) (.next ([-3495000000000], [6570000000000]) (some (4, 0, 2)) (some (4,
      0, 2)) (.next ([-5925000000000], [9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-1620000000000, -9000000000000], [2430000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-4950000000000, 9000000000000], [6570000000000, 0]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-5925000000000, 0], [7380000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 1, 2))
      (.terminal (some (4, 1, 2)) (some (0, 1, 2)) (some (4, 1, 2))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded21_0
    · exact excluded21_1
    · exact (hj rfl).elim
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

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1995000000000, 9000000000000], [810000000000,
      -9000000000000]) none none (.next ([1620000000000, 9000000000000], [1620000000000,
      9000000000000]) none none (.next ([1185000000000, -9000000000000], [1245000000000,
      9000000000000]) none none (.next ([2805000000000], [4335000000000]) none none (.next
      ([1620000000000, 9000000000000], [3090000000000, -9000000000000]) none none (.next ([0],
      [6330000000000, 9000000000000]) none none (.next ([-810000000000, 9000000000000],
      [2805000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1620000000000, -9000000000000],
      [3240000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1245000000000,
      -9000000000000], [2430000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4335000000000], [7140000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3090000000000,
      9000000000000], [4710000000000, 0]) (some (3, 1, 2)) none (.terminal none none
      none))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2430000000000], [270000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7500000000000, 0], [1080000000000, 9000000000000]) (some (0, 4, 1))
      (some (0, 4, 1)) (.next ([7380000000000, -9000000000000], [1620000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([5925000000000, 0], [1620000000000, 9000000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([420000000000, -9000000000000], [120000000000,
      9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([1185000000000, -9000000000000],
      [1245000000000, 9000000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([765000000000],
      [1125000000000]) (some (0, 4, 1)) (some (0, 4, 1)) (.next ([540000000000], [1035000000000])
      (some (0, 4, 1)) (some (0, 4, 1)) (.next ([2430000000000], [6195000000000]) (some (0, 4, 1))
      (some (0, 4, 2)) (.next ([810000000000, -9000000000000], [7815000000000, 9000000000000]) (some
      (0, 4, 2)) (some (0, 4, 2)) (.next ([540000000000], [6960000000000]) (some (0, 4, 2)) (some
      (0, 4, 2)) (.next ([0, 0], [1620000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-270000000000], [2700000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next
      ([-1080000000000, -9000000000000], [8580000000000, 9000000000000]) (some (0, 4, 3)) (some (0,
      4, 3)) (.next ([-1620000000000, -9000000000000], [9000000000000, 0]) (some (0, 4, 3)) (some
      (0, 4, 3)) (.next ([-1620000000000, -9000000000000], [7545000000000, 9000000000000]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-120000000000, -9000000000000], [540000000000, 0]) (some (0,
      4, 3)) (some (0, 4, 3)) (.next ([-1245000000000, -9000000000000], [2430000000000, 0]) (some
      (0, 4, 3)) (some (0, 4, 3)) (.next ([-1125000000000], [1890000000000]) (some (0, 4, 3)) (some
      (0, 4, 3)) (.next ([-1035000000000], [1575000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-6195000000000], [8625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-7815000000000,
      -9000000000000], [8625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-6960000000000],
      [7500000000000]) (some (0, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1,
      0)) (some (4, 1, 3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([8190000000000, 9000000000000], [1185000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([6570000000000], [2805000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([3111000000000], [2805000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([1620000000000, 9000000000000], [3459000000000]) (some (3, 0, 2))
      (some (3, 0, 3)) (.next ([0, 0], [1620000000000, 9000000000000]) (some (3, 0, 3)) (some (3, 0,
      3)) (.next ([-1185000000000, 9000000000000], [9375000000000]) (some (3, 0, 3)) (some (3, 1,
      3)) (.next ([-2805000000000], [9375000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2805000000000], [5916000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3459000000000,
      0], [5079000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded22_1
    · exact excluded22_2
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

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2970000000000], [195000000000]) (some (9, 1,
      11)) (some (9, 2, 11)) (.next ([6735000000000], [750000000000]) (some (9, 2, 11)) (some (9, 2,
      11)) (.next ([1290000000000], [165000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([2805000000000], [360000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([6570000000000],
      [915000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next ([7665000000000], [1080000000000])
      (some (9, 2, 11)) (some (9, 2, 11)) (.next ([7665000000000], [1245000000000]) (some (9, 2,
      11)) (some (9, 2, 11)) (.next ([6195000000000], [1110000000000]) (some (9, 2, 11)) (some (9,
      2, 11)) (.next ([5790000000000], [1155000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([5820000000000], [1290000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([5790000000000], [1320000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([5655000000000], [1290000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([7290000000000], [1995000000000]) (some (9, 2, 11)) (some (9, 2, 11))
      fan23Owner0Part3))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([630000000000, -9000000000000], [0,
      9000000000000]) none none (.next ([1620000000000, 9000000000000], [1620000000000,
      9000000000000]) none none (.next ([2250000000000], [3090000000000]) none none (.next
      ([1620000000000, 9000000000000], [3090000000000, -9000000000000]) none none (.next
      ([990000000000, 9000000000000], [2250000000000]) none none (.next ([0], [6330000000000,
      9000000000000]) none none (.next ([0, -9000000000000], [630000000000, 0]) none none (.next
      ([-1620000000000, -9000000000000], [3240000000000, 18000000000000]) none none (.next
      ([-3090000000000], [5340000000000]) none none (.next ([-3090000000000, 9000000000000],
      [4710000000000, 0]) none none (.next ([-2250000000000], [3240000000000, 9000000000000]) none
      none (.terminal none none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([630000000000, -9000000000000], [0,
      9000000000000]) (some (2, 4, 1)) (some (3, 4, 2)) (.next ([810000000000, -9000000000000],
      [1620000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1620000000000,
      9000000000000], [4950000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([2250000000000], [7380000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1620000000000,
      9000000000000], [7380000000000, -9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([630000000000, -9000000000000], [7380000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([0, 0], [7380000000000, -9000000000000]) (some (3, 4, 2)) (some (4, 4, 2)) (.next ([0,
      -9000000000000], [630000000000, 0]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-1620000000000,
      -9000000000000], [2430000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-4950000000000,
      9000000000000], [6570000000000, 0]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-7380000000000], [9630000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-7380000000000,
      9000000000000], [9000000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-7380000000000,
      0], [8010000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1,
      2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded23_0
    · exact excluded23_1
    · exact (hj rfl).elim
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

end Aown180000190000
end ConwaySoifer.Simplified.Certificates
