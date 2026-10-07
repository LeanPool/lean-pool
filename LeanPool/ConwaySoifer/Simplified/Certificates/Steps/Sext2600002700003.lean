/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext260000270000
import Mathlib.Tactic.FinCases

/-!
# Sext 260000 270000 3

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
namespace Sext260000270000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner4Part0 : FanWitness := (.next ([462000000000], [4125000000000]) (some (5, 1, 3)) (some
    (5, 1, 3)) (.next ([375000000000], [4413000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([330000000000], [5865000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 9000000000000],
    [3000000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0], [3990000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-990000000000], [6330000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-465000000000], [2337000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-468000000000], [2250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-1875000000000], [6195000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1320000000000],
    [3657000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3327000000000], [8202000000000])
    (some (0, 1, 3)) (some (0, 1, 6)) (.next ([-2073000000000, 9000000000000], [4788000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2340000000000], [5340000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-3990000000000], [6330000000000, 9000000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-855000000000], [1320000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-1788000000000], [2715000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-1872000000000, 9000000000000], [2535000000000, -9000000000000]) (some (0, 1, 6)) (some (0, 1,
    6)) (.next ([-3615000000000], [4413000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-4212000000000], [4875000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-3855000000000,
    9000000000000], [4320000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4125000000000],
    [4587000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4413000000000], [4788000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-5865000000000], [6195000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-3000000000000, 9000000000000], [3000000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.terminal (some (0, 2, 6)) (some (0, 2, 6)) (some (0, 2,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner2Part0 : FanWitness := (.next ([4035000000000, -9000000000000], [645000000000,
    9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1320000000000], [360000000000]) (some
    (0, 1, 3)) (some (0, 1, 3)) (.next ([4680000000000], [2070000000000]) (some (0, 1, 3)) (some (0,
    1, 3)) (.next ([4035000000000, 9000000000000], [2340000000000, -9000000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([2715000000000, 9000000000000], [1980000000000, -9000000000000]) (some
    (0, 1, 3)) (some (0, 1, 3)) (.next ([2355000000000, -9000000000000], [1965000000000,
    9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2340000000000, -9000000000000],
    [2070000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2340000000000, 9000000000000],
    [2340000000000, 9000000000000]) (some (0, 1, 3)) (some (5, 1, 3)) (.next ([1695000000000],
    [4680000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([375000000000], [4320000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([270000000000, 9000000000000], [6750000000000, 0])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 0], [2340000000000, 9000000000000]) (some (5, 1,
    3)) (some (5, 1, 3)) (.next ([-375000000000], [2985000000000]) (some (5, 1, 3)) (some (5, 1, 4))
    (.next ([-645000000000, -9000000000000], [4680000000000]) (some (5, 1, 4)) (some (5, 1, 4))
    (.next ([-360000000000], [1680000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
    ([-2070000000000], [6750000000000]) (some (5, 1, 4)) (some (5, 2, 4)) (.next ([-2340000000000,
    9000000000000], [6375000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-1980000000000,
    9000000000000], [4695000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-1965000000000,
    -9000000000000], [4320000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next ([-2070000000000, 0],
    [4410000000000, -9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-2340000000000,
    -9000000000000], [4680000000000, 18000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
    ([-4680000000000], [6375000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4320000000000],
    [4695000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-6750000000000, 0], [7020000000000,
    9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.terminal (some (5, 3, 4)) (some (5, 3, 0))
    (some (5, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner2Part0 : FanWitness := (.next ([4500000000000], [2340000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([4035000000000, 9000000000000], [2340000000000, -9000000000000]) (some
    (0, 1, 3)) (some (0, 1, 3)) (.next ([2715000000000, 9000000000000], [1980000000000,
    -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2355000000000, -9000000000000],
    [1965000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2340000000000,
    9000000000000], [2340000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([1980000000000], [2145000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([2160000000000,
    -9000000000000], [2340000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1695000000000],
    [4680000000000]) (some (0, 1, 3)) (some (5, 1, 3)) (.next ([375000000000], [4320000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 9000000000000], [6840000000000, 0]) (some (5, 1,
    3)) (some (5, 1, 3)) (.next ([0, 0], [2340000000000, 9000000000000]) (some (5, 1, 3)) (some (5,
    1, 3)) (.next ([-645000000000, -9000000000000], [4680000000000]) (some (5, 1, 3)) (some (5, 1,
    4)) (.next ([-465000000000], [2805000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
    ([-360000000000], [1680000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([-2340000000000],
    [6840000000000]) (some (5, 1, 4)) (some (5, 2, 4)) (.next ([-2340000000000, 9000000000000],
    [6375000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-1980000000000, 9000000000000],
    [4695000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-1965000000000, -9000000000000],
    [4320000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next ([-2340000000000, -9000000000000],
    [4680000000000, 18000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-2145000000000],
    [4125000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-2340000000000, 0], [4500000000000,
    -9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4680000000000], [6375000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4320000000000], [4695000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.next ([-6840000000000, 0], [6840000000000, 9000000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.terminal (some (5, 3, 4)) (some (5, 3, 0)) (some (5, 3,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner3Part0 : FanWitness := (.next ([0, -9000000000000], [4500000000000, 9000000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-270000000000, -9000000000000], [4590000000000,
    9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-600000000000, -9000000000000],
    [7260000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-663000000000], [4788000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-663000000000], [2448000000000, -9000000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-765000000000], [2505000000000]) (some (0, 7, 5))
    (some (1, 7, 5)) (.next ([-2385000000000], [6597000000000]) (some (1, 7, 5)) (some (1, 7, 5))
    (.next ([-2448000000000], [6285000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next
    ([-2760000000000], [6660000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-2940000000000],
    [6930000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-2718000000000], [6375000000000])
    (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-2160000000000], [4500000000000]) (some (1, 7, 5))
    (some (1, 7, 5)) (.next ([-1995000000000], [4155000000000]) (some (1, 7, 5)) (some (1, 7, 5))
    (.next ([-2175000000000], [4425000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next
    ([-2340000000000, -9000000000000], [4680000000000, 18000000000000]) (some (1, 7, 5)) (some (1,
    7, 5)) (.next ([-2250000000000], [4320000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next
    ([-4920000000000, 9000000000000], [9000000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next
    ([-4155000000000, 9000000000000], [6495000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next
    ([-180000000000], [270000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-4125000000000],
    [5832000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-4788000000000, 0], [6465000000000,
    9000000000000]) (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-7260000000000], [9000000000000])
    (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-2160000000000, 9000000000000], [2340000000000])
    (some (1, 7, 5)) (some (1, 7, 5)) (.next ([-1980000000000, 9000000000000], [2070000000000])
    (some (1, 7, 5)) (some (1, 7, 5)) (.terminal (some (1, 7, 5)) (some (1, 7, 5)) (some (1, 7,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner3Part1 : FanWitness := (.next ([4320000000000], [270000000000, 9000000000000]) (some
    (6, 1, 7)) (some (6, 1, 7)) (.next ([6660000000000, -9000000000000], [600000000000,
    9000000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([4125000000000], [663000000000]) (some
    (6, 1, 7)) (some (6, 1, 7)) (.next ([1785000000000, -9000000000000], [663000000000]) (some (6,
    1, 7)) (some (6, 1, 7)) (.next ([1740000000000], [765000000000]) (some (6, 1, 7)) (some (6, 1,
    7)) (.next ([4212000000000], [2385000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
    ([3837000000000], [2448000000000]) (some (6, 1, 2)) (some (6, 7, 2)) (.next ([3900000000000],
    [2760000000000]) (some (6, 7, 2)) (some (6, 7, 2)) (.next ([3990000000000], [2940000000000])
    (some (6, 7, 2)) (some (6, 7, 2)) (.next ([3657000000000], [2718000000000]) (some (6, 7, 2))
    (some (6, 7, 2)) (.next ([2340000000000], [2160000000000]) (some (6, 7, 2)) (some (6, 7, 2))
    (.next ([2160000000000], [1995000000000]) (some (6, 7, 2)) (some (6, 7, 2)) (.next
    ([2250000000000], [2175000000000]) (some (6, 7, 2)) (some (6, 7, 3)) (.next ([2340000000000,
    9000000000000], [2340000000000, 9000000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next
    ([2070000000000], [2250000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([4080000000000,
    9000000000000], [4920000000000, -9000000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next
    ([2340000000000, 9000000000000], [4155000000000, -9000000000000]) (some (6, 7, 3)) (some (6, 7,
    3)) (.next ([90000000000], [180000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next
    ([1707000000000], [4125000000000]) (some (6, 7, 3)) (some (6, 7, 4)) (.next ([1677000000000,
    9000000000000], [4788000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1740000000000],
    [7260000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([180000000000, 9000000000000],
    [2160000000000, -9000000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([90000000000,
    9000000000000], [1980000000000, -9000000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([0],
    [2340000000000, 9000000000000]) (some (6, 7, 4)) (some (6, 7, 5))
    fan27Owner3Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner4Part0 : FanWitness := (.next ([798000000000], [3615000000000]) (some (5, 1, 6)) (some
    (5, 1, 6)) (.next ([465000000000, 9000000000000], [3855000000000, -9000000000000]) (some (5, 1,
    6)) (some (5, 1, 6)) (.next ([375000000000], [4413000000000]) (some (5, 1, 6)) (some (5, 1, 6))
    (.next ([330000000000], [5865000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0,
    9000000000000], [3000000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0],
    [3990000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-375000000000], [2847000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-990000000000], [6330000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-468000000000], [2250000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-1875000000000], [6195000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-1065000000000], [2940000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2073000000000,
    9000000000000], [4788000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2340000000000],
    [5340000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1920000000000], [4260000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3990000000000], [7260000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-3990000000000], [6330000000000, 9000000000000]) (some (0, 1, 3))
    (some (0, 6, 3)) (.next ([-855000000000], [1320000000000]) (some (0, 6, 3)) (some (0, 6, 3))
    (.next ([-1788000000000], [2715000000000]) (some (0, 6, 3)) (some (0, 6, 4)) (.next
    ([-4920000000000, 9000000000000], [7260000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-3615000000000], [4413000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3855000000000,
    9000000000000], [4320000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4413000000000],
    [4788000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5865000000000], [6195000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3000000000000, 9000000000000], [3000000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.terminal (some (0, 6, 4)) (some (0, 6, 5)) (some (0, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner3Part0 : FanWitness := (.next ([0], [2340000000000, 9000000000000]) (some (7, 2, 4))
    (some (7, 2, 5)) (.next ([0, -9000000000000], [4500000000000, 9000000000000]) (some (7, 2, 5))
    (some (7, 2, 5)) (.next ([-270000000000, -9000000000000], [4590000000000, 9000000000000]) (some
    (7, 2, 5)) (some (7, 2, 5)) (.next ([-810000000000], [7305000000000]) (some (7, 2, 5)) (some (7,
    2, 5)) (.next ([-663000000000], [4788000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([-663000000000], [2448000000000, -9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([-1473000000000], [4788000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-810000000000],
    [2340000000000, 9000000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-2340000000000,
    -9000000000000], [6495000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-2448000000000],
    [6285000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-2718000000000], [6375000000000])
    (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-2160000000000], [4500000000000]) (some (1, 2, 5))
    (some (1, 2, 5)) (.next ([-1995000000000], [4155000000000]) (some (1, 2, 5)) (some (1, 2, 5))
    (.next ([-2175000000000], [4425000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next
    ([-2340000000000, -9000000000000], [4680000000000, 18000000000000]) (some (1, 2, 5)) (some (1,
    2, 5)) (.next ([-2250000000000], [4320000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next
    ([-2970000000000], [5310000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-3060000000000],
    [5130000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-4155000000000, 9000000000000],
    [6495000000000]) (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-180000000000], [270000000000])
    (some (1, 2, 5)) (some (1, 2, 5)) (.next ([-4125000000000], [5832000000000]) (some (1, 2, 5))
    (some (1, 2, 5)) (.next ([-4788000000000, 0], [6465000000000, 9000000000000]) (some (1, 2, 5))
    (some (1, 2, 5)) (.next ([-2160000000000, 9000000000000], [2340000000000]) (some (1, 2, 5))
    (some (1, 2, 5)) (.next ([-1980000000000, 9000000000000], [2070000000000]) (some (1, 2, 5))
    (some (1, 2, 5)) (.terminal (some (1, 2, 5)) (some (1, 2, 5)) (some (1, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner4Part0 : FanWitness := (.next ([927000000000], [1788000000000]) (some (6, 1, 3)) (some
    (6, 1, 3)) (.next ([798000000000], [3615000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([465000000000, 9000000000000], [3855000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1,
    3)) (.next ([375000000000], [4413000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([330000000000], [5865000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([0, 9000000000000],
    [3000000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([0], [3990000000000])
    (some (6, 1, 3)) (some (6, 1, 3)) (.next ([-93000000000], [4788000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-990000000000], [6330000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-468000000000], [2250000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-1875000000000], [6195000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1020000000000],
    [3000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2073000000000, 9000000000000],
    [4788000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1875000000000], [4320000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2340000000000], [5340000000000]) (some (0, 1, 3))
    (some (0, 1, 6)) (.next ([-3990000000000], [8310000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-3990000000000], [6330000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-855000000000], [1320000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-1788000000000], [2715000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-3615000000000],
    [4413000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-3855000000000, 9000000000000],
    [4320000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-4413000000000], [4788000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-5865000000000], [6195000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-3000000000000, 9000000000000], [3000000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.terminal (some (0, 2, 6)) (some (0, 2, 6)) (some (0, 2,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner3Part0 : FanWitness := (.next ([2340000000000, 9000000000000], [4680000000000]) (some
    (5, 6, 2)) (some (5, 6, 2)) (.next ([90000000000], [180000000000]) (some (5, 6, 2)) (some (5, 6,
    2)) (.next ([1815000000000], [4680000000000]) (some (5, 6, 2)) (some (5, 6, 3)) (.next
    ([180000000000, 9000000000000], [2160000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6,
    3)) (.next ([90000000000, 9000000000000], [1980000000000, -9000000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([195000000000], [4590000000000]) (some (5, 6, 3)) (some (5, 6, 4))
    (.next ([0], [4680000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([-165000000000],
    [2535000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1785000000000, 9000000000000],
    [6660000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2340000000000], [6840000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2610000000000], [6930000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([-2160000000000], [4500000000000]) (some (0, 1, 4)) (some (0, 1, 4))
    (.next ([-1995000000000], [4155000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-2175000000000], [4425000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2145000000000],
    [4125000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2250000000000], [4320000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-4125000000000], [6660000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([-4155000000000, 9000000000000], [6495000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([-4680000000000, 0], [7020000000000, 9000000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([-180000000000], [270000000000]) (some (0, 1, 4)) (some (0, 1, 4))
    (.next ([-4680000000000], [6495000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-2160000000000, 9000000000000], [2340000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-1980000000000, 9000000000000], [2070000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-4590000000000], [4785000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1,
    4)) (some (0, 1, 4)) (some (0, 1, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner2Part0 : FanWitness := (.next ([1320000000000], [360000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([4035000000000, 9000000000000], [2340000000000, -9000000000000]) (some (0, 5,
    3)) (some (0, 5, 3)) (.next ([2715000000000, 9000000000000], [1980000000000, -9000000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2355000000000, -9000000000000], [1965000000000,
    9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2340000000000, 9000000000000],
    [2340000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([3510000000000,
    9000000000000], [5535000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1695000000000], [4680000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([795000000000],
    [3555000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1170000000000], [7875000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([375000000000], [4320000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([0, 0], [2340000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-645000000000, -9000000000000], [4680000000000]) (some (0, 5, 3)) (some (0, 5, 4))
    (.next ([-1170000000000, -9000000000000], [7875000000000]) (some (0, 5, 4)) (some (1, 5, 4))
    (.next ([-525000000000], [3195000000000]) (some (1, 5, 4)) (some (1, 5, 4)) (.next
    ([-360000000000], [1680000000000]) (some (1, 5, 4)) (some (5, 5, 4)) (.next ([-2340000000000,
    9000000000000], [6375000000000, 0]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-1980000000000,
    9000000000000], [4695000000000, 0]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-1965000000000,
    -9000000000000], [4320000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-2340000000000,
    -9000000000000], [4680000000000, 18000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next
    ([-5535000000000, 9000000000000], [9045000000000, 0]) (some (5, 5, 4)) (some (5, 5, 4)) (.next
    ([-4680000000000], [6375000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-3555000000000],
    [4350000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-7875000000000], [9045000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4320000000000], [4695000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.terminal (some (5, 3, 4)) (some (5, 3, 0)) (some (5, 3,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner3Part0 : FanWitness := (.next ([1815000000000], [4680000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([180000000000, 9000000000000], [2160000000000, -9000000000000]) (some
    (5, 6, 3)) (some (5, 6, 3)) (.next ([90000000000, 9000000000000], [1980000000000,
    -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([45000000000], [1335000000000]) (some
    (5, 6, 3)) (some (5, 6, 4)) (.next ([45000000000], [7830000000000]) (some (5, 6, 4)) (some (5,
    6, 4)) (.next ([0], [4680000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([-2340000000000],
    [6840000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2610000000000], [6930000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2160000000000], [4500000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-1995000000000], [4155000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2175000000000], [4425000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-2250000000000], [4320000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4635000000000],
    [7830000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3330000000000], [5535000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3510000000000], [5805000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-4155000000000, 9000000000000], [6495000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-4680000000000, 0], [7020000000000, 9000000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-180000000000], [270000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-5490000000000, 9000000000000], [7875000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-4680000000000], [6495000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-2160000000000, 9000000000000], [2340000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1980000000000, 9000000000000], [2070000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1335000000000], [1380000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-7830000000000],
    [7875000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.terminal (some (0, 6, 4)) (some (0, 6, 4))
    (some (0, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner4Part0 : FanWitness := (.next ([798000000000], [3615000000000]) (some (5, 1, 6)) (some
    (5, 1, 6)) (.next ([1215000000000, 9000000000000], [6615000000000, -9000000000000]) (some (5, 1,
    6)) (some (5, 1, 6)) (.next ([465000000000, 9000000000000], [3855000000000, -9000000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([375000000000], [4413000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([330000000000], [5865000000000]) (some (5, 1, 6)) (some (5, 1, 6))
    (.next ([135000000000], [6330000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0],
    [3990000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-1125000000000], [8955000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-468000000000], [2250000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-663000000000], [2715000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-1875000000000], [6195000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-1500000000000], [4542000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2340000000000],
    [6465000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-195000000000], [465000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-5115000000000], [8955000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-3990000000000], [6330000000000, 9000000000000]) (some (0, 1, 6))
    (some (0, 6, 6)) (.next ([-2490000000000], [3705000000000]) (some (0, 6, 6)) (some (0, 6, 6))
    (.next ([-2760000000000], [3510000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-3615000000000], [4413000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6615000000000,
    9000000000000], [7830000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3855000000000,
    9000000000000], [4320000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4413000000000],
    [4788000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5865000000000], [6195000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6330000000000], [6465000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.terminal (some (0, 6, 4)) (some (0, 6, 5)) (some (0, 6,
    4)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5340000000000], [990000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([1872000000000], [465000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([1782000000000], [468000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([4320000000000], [1875000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([2337000000000],
      [1320000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4875000000000], [3327000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2715000000000, 9000000000000], [2073000000000,
      -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([3000000000000], [2340000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2340000000000, 9000000000000], [3990000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([465000000000], [855000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([927000000000], [1788000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([663000000000], [1872000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([798000000000], [3615000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([663000000000], [4212000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([465000000000,
      9000000000000], [3855000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      fan24Owner4Part0)))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4788000000000], [4875000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([483000000000], [4680000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([288000000000], [4500000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([108000000000], [4875000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [4680000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-4875000000000], [9663000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-4680000000000], [5163000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-4500000000000], [4788000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4875000000000], [4983000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2610000000000], [375000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) fan25Owner2Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded25_4
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
  apply ExclusionHint.sound (.pair 3 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_2 : ExcludedOn (model26.B 2 ++ [step26.q]) 9000000000000 (model26.caps 2)
    (model26.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4035000000000, -9000000000000], [645000000000,
      9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2340000000000], [465000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1320000000000], [360000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) fan26Owner2Part0)))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded26_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [0, 9000000000000]) (some (5, 1,
      7)) (some (6, 1, 7)) fan27Owner3Part1)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2472000000000], [375000000000]) (some (5, 0, 6))
      (some (5, 1, 6)) (.next ([5340000000000], [990000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([1782000000000], [468000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([4320000000000], [1875000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1875000000000],
      [1065000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2715000000000, 9000000000000],
      [2073000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3000000000000],
      [2340000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2340000000000], [1920000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3270000000000], [3990000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([2340000000000, 9000000000000], [3990000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([465000000000], [855000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([927000000000], [1788000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([2340000000000, 9000000000000], [4920000000000, -9000000000000]) (some (5, 1, 6)) (some (5,
      1, 6)) fan27Owner4Part0)))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4788000000000], [375000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([7260000000000], [1740000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([375000000000], [147000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([2340000000000, 9000000000000], [5310000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([1965000000000, 9000000000000], [5163000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([2097000000000], [6528000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1950000000000],
      [7050000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([600000000000, 9000000000000],
      [6660000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-375000000000],
      [5163000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1740000000000], [9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-147000000000], [522000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-5310000000000, 0], [7650000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-5163000000000, 0], [7128000000000, 9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-6528000000000], [8625000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-7050000000000], [9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-6660000000000, 9000000000000], [7260000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded28_0 : ExcludedOn (model28.B 0 ++ [step28.q]) 9000000000000 (model28.caps 0)
    (model28.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [0, 9000000000000]) (some (5, 1,
      2)) (some (7, 1, 2)) (.next ([4320000000000], [270000000000, 9000000000000]) (some (7, 1, 2))
      (some (7, 1, 2)) (.next ([6495000000000], [810000000000]) (some (7, 1, 2)) (some (7, 1, 2))
      (.next ([4125000000000], [663000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next
      ([1785000000000, -9000000000000], [663000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next
      ([3315000000000], [1473000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([1530000000000,
      9000000000000], [810000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([4155000000000,
      -9000000000000], [2340000000000, 9000000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next
      ([3837000000000], [2448000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([3657000000000],
      [2718000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([2340000000000], [2160000000000])
      (some (7, 1, 2)) (some (7, 1, 2)) (.next ([2160000000000], [1995000000000]) (some (7, 1, 2))
      (some (7, 1, 2)) (.next ([2250000000000], [2175000000000]) (some (7, 1, 2)) (some (7, 1, 3))
      (.next ([2340000000000, 9000000000000], [2340000000000, 9000000000000]) (some (7, 1, 3)) (some
      (7, 1, 3)) (.next ([2070000000000], [2250000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
      ([2340000000000], [2970000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([2070000000000],
      [3060000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([2340000000000, 9000000000000],
      [4155000000000, -9000000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([90000000000],
      [180000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([1707000000000], [4125000000000])
      (some (7, 1, 3)) (some (7, 1, 4)) (.next ([1677000000000, 9000000000000], [4788000000000])
      (some (7, 1, 4)) (some (7, 2, 4)) (.next ([180000000000, 9000000000000], [2160000000000,
      -9000000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([90000000000, 9000000000000],
      [1980000000000, -9000000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      fan28Owner3Part0)))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded28_3
    · exact excluded28_4
    · exact excluded28_5
    · exact excluded28_6
    · exact excluded28_7
    · exact (hj rfl).elim
    · exact excluded28_9
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded29_0 : ExcludedOn (model29.B 0 ++ [step29.q]) 9000000000000 (model29.caps 0)
    (model29.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_1 : ExcludedOn (model29.B 1 ++ [step29.q]) 9000000000000 (model29.caps 1)
    (model29.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_2 : ExcludedOn (model29.B 2 ++ [step29.q]) 9000000000000 (model29.caps 2)
    (model29.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4695000000000], [93000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([5340000000000], [990000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([1782000000000], [468000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([4320000000000], [1875000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([1980000000000],
      [1020000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2715000000000, 9000000000000],
      [2073000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([2445000000000],
      [1875000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([3000000000000], [2340000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4320000000000], [3990000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([2340000000000, 9000000000000], [3990000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([465000000000], [855000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      fan29Owner4Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3870000000000], [810000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([4680000000000], [4320000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([3510000000000], [4680000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [4680000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-810000000000], [4680000000000])
      (some (0, 1, 2)) (some (0, 3, 2)) (.next ([-4320000000000], [9000000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([-4680000000000], [8190000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.terminal (some (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_1 : ExcludedOn (model30.B 1 ++ [step30.q]) 9000000000000 (model30.caps 1)
    (model30.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_2 : ExcludedOn (model30.B 2 ++ [step30.q]) 9000000000000 (model30.caps 2)
    (model30.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_3 : ExcludedOn (model30.B 3 ++ [step30.q]) 9000000000000 (model30.caps 3)
    (model30.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2370000000000], [165000000000]) (some (4, 0, 1))
      (some (5, 0, 1)) (.next ([4875000000000, 9000000000000], [1785000000000, -9000000000000])
      (some (5, 0, 1)) (some (5, 0, 1)) (.next ([4500000000000], [2340000000000]) (some (5, 0, 1))
      (some (5, 0, 1)) (.next ([4320000000000], [2610000000000]) (some (5, 0, 1)) (some (5, 0, 1))
      (.next ([2340000000000], [2160000000000]) (some (5, 0, 1)) (some (5, 0, 1)) (.next
      ([2160000000000], [1995000000000]) (some (5, 0, 1)) (some (5, 0, 1)) (.next ([2250000000000],
      [2175000000000]) (some (5, 0, 1)) (some (5, 0, 2)) (.next ([1980000000000], [2145000000000])
      (some (5, 0, 2)) (some (5, 0, 2)) (.next ([2070000000000], [2250000000000]) (some (5, 0, 2))
      (some (5, 6, 2)) (.next ([2535000000000], [4125000000000]) (some (5, 6, 2)) (some (5, 6, 2))
      (.next ([2340000000000, 9000000000000], [4155000000000, -9000000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) fan30Owner3Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4035000000000, -9000000000000], [645000000000,
      9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([6705000000000, -9000000000000],
      [1170000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2670000000000],
      [525000000000]) (some (0, 5, 3)) (some (0, 5, 3)) fan31Owner2Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_3 : ExcludedOn (model31.B 3 ++ [step31.q]) 9000000000000 (model31.caps 3)
    (model31.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [2340000000000]) (some (4, 0,
      6)) (some (5, 0, 6)) (.next ([4320000000000], [2610000000000]) (some (5, 0, 6)) (some (5, 0,
      6)) (.next ([2340000000000], [2160000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([2160000000000], [1995000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([2250000000000],
      [2175000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([2070000000000], [2250000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3195000000000], [4635000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([2205000000000], [3330000000000]) (some (5, 0, 6)) (some (5, 6, 6))
      (.next ([2295000000000], [3510000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([2340000000000, 9000000000000], [4155000000000, -9000000000000]) (some (5, 6, 2)) (some (5,
      6, 2)) (.next ([2340000000000, 9000000000000], [4680000000000]) (some (5, 6, 2)) (some (5, 6,
      2)) (.next ([90000000000], [180000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([2385000000000, 9000000000000], [5490000000000, -9000000000000]) (some (5, 6, 2)) (some (5,
      6, 3)) fan31Owner3Part0)))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7830000000000], [1125000000000]) (some (5, 0,
      6)) (some (5, 1, 6)) (.next ([1782000000000], [468000000000]) (some (5, 1, 6)) (some (5, 1,
      6)) (.next ([2052000000000], [663000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([4320000000000], [1875000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([3042000000000],
      [1500000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4125000000000], [2340000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([270000000000], [195000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([3840000000000], [5115000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([2340000000000, 9000000000000], [3990000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([1215000000000], [2490000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([750000000000], [2760000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan31Owner4Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Sext260000270000
end ConwaySoifer.Simplified.Certificates
