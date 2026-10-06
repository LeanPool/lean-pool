/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint330000340000
import Mathlib.Tactic.FinCases

/-!
# Sint 330000 340000 4

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
namespace Sint330000340000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner6Part0 : FanWitness := (.next ([3096000000000], [585000000000]) (some (4, 5, 3)) (some
    (4, 5, 3)) (.next ([4245000000000], [1875000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([5625000000000], [2691000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([3960000000000], [2250000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([2970000000000,
    9000000000000], [2970000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([1095000000000, 9000000000000], [3150000000000, -9000000000000]) (some (4, 5, 3)) (some (4, 5,
    3)) (.next ([90000000000], [285000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([1275000000000, -9000000000000], [4845000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([990000000000, -9000000000000], [5220000000000, 9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([279000000000, 0], [2376000000000, -9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([279000000000], [5346000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([0, 0], [2970000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-495000000000], [3966000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-585000000000],
    [3681000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1875000000000], [6120000000000])
    (some (0, 2, 3)) (some (5, 2, 3)) (.next ([-2691000000000, -9000000000000], [8316000000000,
    9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2250000000000], [6210000000000])
    (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2970000000000, -9000000000000], [5940000000000,
    18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-3150000000000, 9000000000000],
    [4245000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-285000000000], [375000000000])
    (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-4845000000000, -9000000000000], [6120000000000])
    (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-5220000000000, -9000000000000], [6210000000000])
    (some (5, 2, 3)) (some (5, 2, 4)) (.next ([-2376000000000, 9000000000000], [2655000000000,
    -9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-5346000000000], [5625000000000])
    (some (5, 2, 4)) (some (5, 2, 4)) (.terminal (some (5, 2, 4)) (some (5, 2, 4)) (some (5, 2,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner3Part0 : FanWitness := (.next ([2970000000000], [1155000000000]) (some (4, 0, 5))
    (some (4, 0, 5)) (.next ([750000000000], [405000000000]) (some (4, 0, 5)) (some (4, 0, 5))
    (.next ([4545000000000], [2580000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next
    ([3060000000000], [1815000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4545000000000],
    [3375000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([2265000000000], [1815000000000])
    (some (4, 1, 3)) (some (4, 1, 3)) (.next ([3390000000000], [3330000000000]) (some (4, 1, 3))
    (some (4, 1, 3)) (.next ([3390000000000], [4125000000000]) (some (4, 1, 3)) (some (4, 1, 3))
    (.next ([1500000000000], [4860000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([795000000000], [3750000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([750000000000],
    [4455000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0], [3375000000000]) (some (4, 1,
    3)) (some (4, 5, 3)) (.next ([-1485000000000], [6360000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-1155000000000], [4125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-405000000000], [1155000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2580000000000],
    [7125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1815000000000], [4875000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3375000000000], [7920000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-1815000000000], [4080000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-3330000000000], [6720000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-4125000000000], [7515000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4860000000000],
    [6360000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3750000000000], [4545000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4455000000000], [5205000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5,
    3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner0Part0 : FanWitness := (.next ([-735000000000], [1485000000000]) (some (1, 9, 8))
    (some (1, 9, 8)) (.next ([-2640000000000], [5250000000000]) (some (1, 9, 8)) (some (1, 9, 8))
    (.next ([-1575000000000], [3090000000000]) (some (1, 9, 8)) (some (1, 9, 8)) (.next
    ([-375000000000], [735000000000]) (some (1, 9, 8)) (some (9, 9, 8)) (.next ([-1890000000000],
    [3375000000000]) (some (9, 9, 8)) (some (9, 9, 8)) (.next ([-3375000000000], [5610000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-1860000000000], [3060000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-1155000000000], [1890000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.next ([-4146000000000], [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-4521000000000], [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-4710000000000],
    [6375000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5249400000000, -1980000000000],
    [6652800000000, 3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-921600000000,
    1980000000000], [1103400000000, 1980000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-5624400000000, -1980000000000], [6652800000000, 3960000000000]) (some (9, 5, 8)) (some (9, 5,
    8)) (.next ([-4125000000000], [4875000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-5721000000000], [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5813400000000,
    -1980000000000], [6556800000000, 3960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-7236000000000], [7986000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-6096000000000],
    [6471000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-7611000000000], [7986000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-2041800000000, -3960000000000], [2138400000000,
    1980000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-6285000000000], [6375000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-7800000000000], [7890000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-6081000000000], [6096000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.terminal (some (9, 5, 8)) (some (9, 5, 8)) (some (9, 5, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner0Part1 : FanWitness := (.next ([743400000000, 1980000000000], [5813400000000,
    1980000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([750000000000], [7236000000000]) (some
    (0, 9, 6)) (some (0, 9, 6)) (.next ([375000000000], [6096000000000]) (some (0, 9, 6)) (some (0,
    9, 6)) (.next ([375000000000], [7611000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next
    ([96600000000, -1980000000000], [2041800000000, 3960000000000]) (some (0, 9, 6)) (some (0, 9,
    6)) (.next ([90000000000], [6285000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next
    ([90000000000], [7800000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([15000000000],
    [6081000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([0], [1575000000000]) (some (0, 9,
    6)) (some (0, 9, 6)) (.next ([-360000000000], [6456000000000]) (some (0, 9, 6)) (some (0, 9, 7))
    (.next ([-645000000000], [6645000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next
    ([-471000000000], [3861000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-735000000000],
    [5346000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-96000000000], [660000000000]) (some
    (0, 9, 7)) (some (0, 9, 7)) (.next ([-375000000000], [2310000000000]) (some (0, 9, 7)) (some (0,
    9, 7)) (.next ([-1110000000000], [5721000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next
    ([-375000000000], [1860000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-846000000000],
    [3861000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-1395000000000], [5910000000000])
    (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-1035000000000], [3765000000000]) (some (0, 9, 7))
    (some (0, 9, 7)) (.next ([-1065000000000], [3675000000000]) (some (0, 9, 7)) (some (0, 9, 7))
    (.next ([-653400000000, -1980000000000], [1986600000000, -1980000000000]) (some (0, 9, 7)) (some
    (1, 9, 7)) (.next ([-2640000000000], [6765000000000]) (some (1, 9, 7)) (some (1, 9, 8)) (.next
    ([-556800000000, -3960000000000], [1388400000000, 1980000000000]) (some (1, 9, 8)) (some (1, 9,
    8)) fan37Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner0Part2 : FanWitness := (.next ([1485000000000], [375000000000]) (some (8, 9, 6)) (some
    (8, 9, 6)) (.next ([3015000000000], [846000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([4515000000000], [1395000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2730000000000],
    [1035000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2610000000000], [1065000000000])
    (some (0, 9, 6)) (some (0, 9, 6)) (.next ([1333200000000, -3960000000000], [653400000000,
    1980000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([4125000000000], [2640000000000])
    (some (0, 9, 6)) (some (0, 9, 6)) (.next ([831600000000, -1980000000000], [556800000000,
    3960000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([750000000000], [735000000000]) (some
    (0, 9, 6)) (some (0, 9, 6)) (.next ([2610000000000], [2640000000000]) (some (0, 9, 6)) (some (0,
    9, 6)) (.next ([1515000000000], [1575000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next
    ([360000000000], [375000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([1485000000000],
    [1890000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([2235000000000], [3375000000000])
    (some (0, 9, 6)) (some (0, 9, 6)) (.next ([1200000000000], [1860000000000]) (some (0, 9, 6))
    (some (0, 9, 6)) (.next ([735000000000], [1155000000000]) (some (0, 9, 6)) (some (0, 9, 6))
    (.next ([2325000000000], [4146000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next
    ([1950000000000], [4521000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([1665000000000],
    [4710000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([1403400000000, 1980000000000],
    [5249400000000, 1980000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([181800000000,
    3960000000000], [921600000000, -1980000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next
    ([1028400000000, 1980000000000], [5624400000000, 1980000000000]) (some (0, 9, 6)) (some (0, 9,
    6)) (.next ([750000000000], [4125000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next
    ([750000000000], [5721000000000]) (some (0, 9, 6)) (some (0, 9, 6))
    fan37Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner4Part0 : FanWitness := (.next ([-360000000000], [3330000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-735000000000], [6360000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-375000000000], [3030000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-990000000000], [6375000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-855000000000],
    [4260000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-1290000000000], [5250000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-990000000000], [3960000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-1320000000000], [5070000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-1395000000000], [4395000000000]) (some (0, 2, 7)) (some (0, 7, 7)) (.next
    ([-2955000000000], [9000000000000]) (some (0, 7, 7)) (some (0, 7, 7)) (.next ([-2100000000000],
    [4740000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-3375000000000], [6780000000000])
    (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-3030000000000], [6030000000000]) (some (0, 7, 6))
    (some (0, 7, 6)) (.next ([-960000000000], [1740000000000]) (some (0, 7, 6)) (some (0, 7, 6))
    (.next ([-1770000000000], [3000000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next
    ([-1980000000000], [3105000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-1290000000000],
    [1875000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-4395000000000], [6375000000000])
    (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-6360000000000], [9000000000000]) (some (0, 7, 6))
    (some (0, 7, 6)) (.next ([-5250000000000], [7365000000000]) (some (0, 7, 6)) (some (0, 7, 6))
    (.next ([-1020000000000], [1365000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next
    ([-1965000000000], [2625000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-3375000000000],
    [4260000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-6030000000000], [6405000000000])
    (some (0, 7, 6)) (some (0, 7, 6)) (.terminal (some (0, 7, 6)) (some (0, 7, 6)) (some (0, 7,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner4Part1 : FanWitness := (.next ([2655000000000], [375000000000]) (some (6, 1, 7)) (some
    (6, 1, 7)) (.next ([5385000000000], [990000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([3405000000000], [855000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3960000000000],
    [1290000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([2970000000000], [990000000000])
    (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3750000000000], [1320000000000]) (some (6, 1, 7))
    (some (6, 1, 7)) (.next ([3000000000000], [1395000000000]) (some (6, 1, 7)) (some (6, 1, 7))
    (.next ([6045000000000], [2955000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([2640000000000], [2100000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3405000000000],
    [3375000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3000000000000], [3030000000000])
    (some (6, 1, 7)) (some (6, 1, 7)) (.next ([780000000000], [960000000000]) (some (6, 1, 7)) (some
    (6, 1, 7)) (.next ([1230000000000], [1770000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([1125000000000], [1980000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([585000000000],
    [1290000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([1980000000000], [4395000000000])
    (some (6, 1, 7)) (some (6, 2, 7)) (.next ([2640000000000], [6360000000000]) (some (6, 2, 7))
    (some (6, 2, 7)) (.next ([2115000000000], [5250000000000]) (some (6, 2, 7)) (some (6, 2, 7))
    (.next ([345000000000], [1020000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([660000000000], [1965000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([885000000000],
    [3375000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([375000000000], [6030000000000])
    (some (6, 2, 7)) (some (6, 2, 7)) (.next ([0], [3375000000000]) (some (6, 2, 7)) (some (6, 2,
    7)) (.next ([-135000000000], [2115000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    fan37Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner6Part0 : FanWitness := (.next ([2115000000000], [765000000000]) (some (5, 1, 3)) (some
    (5, 1, 3)) (.next ([6360000000000], [2640000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([4245000000000], [1875000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3960000000000],
    [2250000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2970000000000, 9000000000000],
    [2970000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3390000000000,
    -9000000000000], [5610000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([1095000000000, 9000000000000], [3150000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([90000000000], [285000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([1275000000000, -9000000000000], [4845000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([990000000000, -9000000000000], [5220000000000, 9000000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([330000000000, 9000000000000], [6030000000000, -9000000000000]) (some
    (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 0], [2970000000000, 9000000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([-390000000000], [2790000000000]) (some (5, 1, 3)) (some (5, 2, 3))
    (.next ([-765000000000], [2880000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
    ([-2640000000000], [9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1875000000000],
    [6120000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2250000000000], [6210000000000])
    (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2970000000000, -9000000000000], [5940000000000,
    18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-5610000000000, -9000000000000],
    [9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-3150000000000, 9000000000000],
    [4245000000000]) (some (5, 2, 3)) (some (5, 2, 5)) (.next ([-285000000000], [375000000000])
    (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-4845000000000, -9000000000000], [6120000000000])
    (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-5220000000000, -9000000000000], [6210000000000])
    (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-6030000000000, 9000000000000], [6360000000000])
    (some (5, 2, 5)) (some (5, 2, 5)) (.terminal (some (1, 2, 5)) (some (1, 2, 5)) (some (1, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan38Owner6Part0 : FanWitness := (.next ([4245000000000], [1875000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([3960000000000], [2250000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([4455000000000, -9000000000000], [3795000000000, 9000000000000]) (some (5, 1, 3)) (some
    (5, 1, 3)) (.next ([2970000000000, 9000000000000], [2970000000000, 9000000000000]) (some (5, 1,
    3)) (some (5, 1, 3)) (.next ([1425000000000], [2040000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([1050000000000], [2130000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([2145000000000, 9000000000000], [5280000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([1095000000000, 9000000000000], [3150000000000, -9000000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([90000000000], [285000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([1275000000000, -9000000000000], [4845000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([990000000000, -9000000000000], [5220000000000, 9000000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([0, 0], [2970000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([-825000000000], [8250000000000]) (some (5, 1, 3)) (some (5, 2, 3)) (.next
    ([-1875000000000], [6120000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2250000000000],
    [6210000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-3795000000000, -9000000000000],
    [8250000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2970000000000, -9000000000000],
    [5940000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 5)) (.next ([-2040000000000],
    [3465000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-2130000000000], [3180000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5280000000000, 9000000000000], [7425000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3150000000000, 9000000000000], [4245000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-285000000000], [375000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4845000000000, -9000000000000], [6120000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-5220000000000, -9000000000000], [6210000000000]) (some (0, 2, 5))
    (some (1, 2, 5)) (.terminal (some (1, 2, 5)) (some (1, 2, 5)) (some (1, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan39Owner3Part0 : FanWitness := (.next ([7170000000000], [1035000000000]) (some (4, 5, 3))
    (some (4, 5, 3)) (.next ([2970000000000], [1155000000000]) (some (4, 5, 3)) (some (4, 5, 3))
    (.next ([750000000000], [405000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([4545000000000], [2580000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([4545000000000],
    [3375000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([3390000000000], [3330000000000])
    (some (4, 5, 3)) (some (4, 5, 3)) (.next ([3390000000000], [4125000000000]) (some (4, 5, 3))
    (some (4, 5, 3)) (.next ([3420000000000], [5580000000000]) (some (4, 5, 3)) (some (4, 5, 3))
    (.next ([795000000000], [3750000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
    ([450000000000], [4425000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([45000000000],
    [5580000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [3375000000000]) (some (4, 5,
    3)) (some (4, 5, 3)) (.next ([-1035000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-1035000000000], [8205000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-1155000000000], [4125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-405000000000],
    [1155000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2580000000000], [7125000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3375000000000], [7920000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-3330000000000], [6720000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-4125000000000], [7515000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-5580000000000], [9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3750000000000],
    [4545000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4425000000000], [4875000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5580000000000], [5625000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.terminal (some (0, 5, 3)) (some (5, 5, 3)) (some (5, 5,
    3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan39Owner4Part0 : FanWitness := (.next ([0], [3375000000000]) (some (6, 2, 7)) (some (6, 2, 7))
    (.next ([-135000000000], [2115000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-375000000000], [3030000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-450000000000],
    [3000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-990000000000], [6375000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-855000000000], [4260000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-1290000000000], [5250000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-990000000000], [3960000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-1395000000000], [4395000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-2175000000000],
    [5580000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-795000000000], [1980000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3375000000000], [6780000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-3030000000000], [6030000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-960000000000], [1740000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1770000000000], [3000000000000]) (some (0, 2, 6)) (some (0, 3, 6)) (.next ([-3375000000000],
    [5580000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-1980000000000], [3105000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-1290000000000], [1875000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-4395000000000], [6375000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-5250000000000], [7365000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-1020000000000], [1365000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-3375000000000],
    [4260000000000]) (some (0, 3, 6)) (some (0, 4, 6)) (.next ([-3960000000000], [4290000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-6030000000000], [6405000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.terminal (some (0, 4, 6)) (some (0, 4, 6)) (some (0, 4,
    6)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3471000000000], [495000000000]) (some (4, 5, 2))
      (some (4, 5, 3)) fan32Owner6Part0)) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100
      (by decide +kernel)
  decide +kernel

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2745000000000, -9000000000000], [2970000000000,
      9000000000000]) (some (3, 0, 1)) (some (3, 1, 2)) (.next ([3654000000000], [5625000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([684000000000, -9000000000000], [5625000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([90000000000], [3564000000000]) (some (3, 1, 2))
      (some (3, 1, 3)) (.next ([0], [5715000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-2970000000000, -9000000000000], [5715000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-5625000000000], [9279000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-5625000000000], [6309000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-3564000000000], [3654000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked32 : StepValid model32 9000000000000 step32 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded32_0
    · exact excluded32_1
    · exact excluded32_2
    · exact excluded32_3
    · exact excluded32_4
    · exact (hj rfl).elim
    · exact excluded32_6
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2970000000000], [1155000000000]) (some (3, 5,
      2)) (some (4, 5, 3)) (.next ([750000000000], [405000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([4545000000000], [2580000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([4545000000000], [3375000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([3390000000000],
      [3330000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([4545000000000], [4800000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([3390000000000], [4125000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([4545000000000], [5595000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([1155000000000], [1470000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([795000000000], [3750000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0],
      [3375000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-1155000000000], [4125000000000])
      (some (0, 5, 3)) (some (5, 5, 3)) (.next ([-405000000000], [1155000000000]) (some (5, 5, 3))
      (some (5, 5, 3)) (.next ([-2580000000000], [7125000000000]) (some (5, 5, 3)) (some (5, 5, 3))
      (.next ([-3375000000000], [7920000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-3330000000000], [6720000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-4800000000000], [9345000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-4125000000000], [7515000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-5595000000000], [10140000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-1470000000000], [2625000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-3750000000000], [4545000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.terminal (some (5, 2,
      3)) (some (5, 2, 3)) (some (5, 2, 3))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4545000000000], [2745000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([5595000000000], [3405000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1710000000000], [1695000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1140000000000], [4455000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [7290000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2745000000000], [7290000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3405000000000], [9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1695000000000], [3405000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-4455000000000], [5595000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked33 : StepValid model33 9000000000000 step33 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded33_0
    · exact excluded33_1
    · exact excluded33_2
    · exact excluded33_3
    · exact (hj rfl).elim
    · exact excluded33_5
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [279000000000]) (some (4, 0, 3))
      (some (4, 1, 3)) (.next ([3750000000000], [1200000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([5040000000000, 0], [1680000000000, 9000000000000]) (some (4, 1, 3)) (some (5, 1, 3))
      (.next ([4761000000000], [2364000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([4110000000000], [2130000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4110000000000,
      0], [2970000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3270000000000,
      -9000000000000], [2970000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([2586000000000], [3375000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([360000000000],
      [930000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next ([1290000000000], [3750000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0], [4110000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-279000000000], [3654000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next
      ([-1200000000000], [4950000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1680000000000,
      -9000000000000], [6720000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-2364000000000], [7125000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-2130000000000], [6240000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2970000000000,
      -9000000000000], [7080000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-2970000000000, -9000000000000], [6240000000000]) (some (0, 2, 4)) (some (0, 3, 4)) (.next
      ([-3375000000000], [5961000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-930000000000],
      [1290000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-3750000000000], [5040000000000])
      (some (0, 3, 4)) (some (0, 3, 4)) (.terminal (some (0, 3, 4)) (some (0, 3, 4)) (some (0, 3,
      4))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_8 : ExcludedOn (model34.B 8 ++ [step34.q]) 9000000000000 (model34.caps 8)
    (model34.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_9 : ExcludedOn (model34.B 9 ++ [step34.q]) 9000000000000 (model34.caps 9)
    (model34.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked34 : StepValid model34 9000000000000 step34 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded34_0
    · exact excluded34_1
    · exact excluded34_2
    · exact excluded34_3
    · exact (hj rfl).elim
    · exact excluded34_5
    · exact excluded34_6
    · exact excluded34_7
    · exact excluded34_8
    · exact excluded34_9
theorem next34 : model34.insert step34 = model35 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded35_0 : ExcludedOn (model35.B 0 ++ [step35.q]) 9000000000000 (model35.caps 0)
    (model35.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2970000000000], [240000000000]) (some (4, 0, 3))
      (some (4, 1, 3)) (.next ([3375000000000], [279000000000]) (some (4, 1, 3)) (some (5, 1, 3))
      (.next ([5721000000000], [624000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([4110000000000], [2130000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4110000000000,
      0], [2970000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3270000000000,
      -9000000000000], [2970000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([3030000000000], [2970000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2586000000000],
      [3375000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1140000000000], [1890000000000])
      (some (5, 1, 3)) (some (5, 1, 4)) (.next ([60000000000, -9000000000000], [5940000000000,
      9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-240000000000], [3210000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-279000000000], [3654000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-624000000000], [6345000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-2130000000000], [6240000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-2970000000000, -9000000000000], [7080000000000, 9000000000000]) (some (0, 2, 4)) (some (0,
      2, 4)) (.next ([-2970000000000, -9000000000000], [6240000000000]) (some (0, 2, 4)) (some (0,
      3, 4)) (.next ([-2970000000000], [6000000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
      ([-3375000000000], [5961000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
      ([-1890000000000], [3030000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.terminal (some (0, 3,
      4)) (some (0, 3, 4)) (some (0, 3, 4))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_7 : ExcludedOn (model35.B 7 ++ [step35.q]) 9000000000000 (model35.caps 7)
    (model35.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_8 : ExcludedOn (model35.B 8 ++ [step35.q]) 9000000000000 (model35.caps 8)
    (model35.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_9 : ExcludedOn (model35.B 9 ++ [step35.q]) 9000000000000 (model35.caps 9)
    (model35.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked35 : StepValid model35 9000000000000 step35 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded35_0
    · exact excluded35_1
    · exact excluded35_2
    · exact excluded35_3
    · exact (hj rfl).elim
    · exact excluded35_5
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4545000000000, -9000000000000], [330000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([6030000000000, -9000000000000],
      [2970000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2640000000000],
      [4875000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1155000000000, -9000000000000],
      [7515000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0], [2970000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-330000000000, -9000000000000],
      [4875000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-2970000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-4875000000000],
      [7515000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-7515000000000, 0],
      [8670000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2))
      (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [1485000000000]) (some (3, 0,
      5)) (some (4, 0, 5)) fan36Owner3Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked36 : StepValid model36 9000000000000 step36 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded36_1
    · exact excluded36_2
    · exact excluded36_3
    · exact excluded36_4
    · exact excluded36_5
    · exact excluded36_6
    · exact excluded36_7
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6096000000000], [360000000000]) (some (8, 9, 5))
      (some (8, 9, 5)) (.next ([6000000000000], [645000000000]) (some (8, 9, 5)) (some (8, 9, 5))
      (.next ([3390000000000], [471000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
      ([4611000000000], [735000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([564000000000],
      [96000000000]) (some (8, 9, 5)) (some (8, 9, 6)) (.next ([1935000000000], [375000000000])
      (some (8, 9, 6)) (some (8, 9, 6)) (.next ([4611000000000], [1110000000000]) (some (8, 9, 6))
      (some (8, 9, 6)) fan37Owner0Part2)))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1980000000000], [135000000000]) (some (6, 0, 7))
      (some (6, 1, 7)) (.next ([2970000000000], [360000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([5625000000000], [735000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      fan37Owner4Part1))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2400000000000], [390000000000]) (some (5, 1, 2))
      (some (5, 1, 3)) fan37Owner6Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_8 : ExcludedOn (model37.B 8 ++ [step37.q]) 9000000000000 (model37.caps 8)
    (model37.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked37 : StepValid model37 9000000000000 step37 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded37_0
    · exact excluded37_1
    · exact excluded37_2
    · exact excluded37_3
    · exact excluded37_4
    · exact (hj rfl).elim
    · exact excluded37_6
    · exact excluded37_7
    · exact excluded37_8
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [279000000000]) (some (5, 0, 3))
      (some (5, 1, 3)) (.next ([5205000000000, -9000000000000], [2220000000000, 9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4110000000000], [2250000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([4521000000000], [2625000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([4860000000000], [3315000000000]) (some (5, 1, 3)) (some (5, 1, 5)) (.next
      ([4110000000000, 0], [2970000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([3390000000000, -9000000000000], [2970000000000, 9000000000000]) (some (0, 1, 5)) (some (0,
      1, 5)) (.next ([3831000000000], [3654000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([2706000000000], [3375000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([750000000000],
      [1065000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([750000000000], [7425000000000])
      (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [4110000000000]) (some (0, 1, 5)) (some (0, 1,
      5)) (.next ([-279000000000], [3654000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
      ([-2220000000000, -9000000000000], [7425000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-2250000000000], [6360000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-2625000000000], [7146000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-3315000000000], [8175000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2970000000000,
      -9000000000000], [7080000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-2970000000000, -9000000000000], [6360000000000]) (some (0, 2, 5)) (some (0, 3, 5)) (.next
      ([-3654000000000], [7485000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
      ([-3375000000000], [6081000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
      ([-1065000000000], [1815000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
      ([-7425000000000], [8175000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.terminal (some (0, 3,
      5)) (some (0, 3, 5)) (some (0, 3, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7425000000000], [825000000000]) (some (5, 1, 2))
      (some (5, 1, 3)) fan38Owner6Part0)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_8 : ExcludedOn (model38.B 8 ++ [step38.q]) 9000000000000 (model38.caps 8)
    (model38.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_9 : ExcludedOn (model38.B 9 ++ [step38.q]) 9000000000000 (model38.caps 9)
    (model38.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked38 : StepValid model38 9000000000000 step38 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded38_1
    · exact excluded38_2
    · exact excluded38_3
    · exact excluded38_4
    · exact excluded38_5
    · exact excluded38_6
    · exact excluded38_7
    · exact excluded38_8
    · exact excluded38_9
theorem next38 : model38.insert step38 = model39 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7965000000000], [1035000000000]) (some (3, 5,
      5)) (some (4, 5, 5)) fan39Owner3Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1980000000000], [135000000000]) (some (6, 0, 4))
      (some (6, 1, 4)) (.next ([2655000000000], [375000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([2550000000000], [450000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
      ([5385000000000], [990000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3405000000000],
      [855000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3960000000000], [1290000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2970000000000], [990000000000]) (some (6, 1, 4))
      (some (6, 1, 4)) (.next ([3000000000000], [1395000000000]) (some (6, 1, 4)) (some (6, 1, 4))
      (.next ([3405000000000], [2175000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
      ([1185000000000], [795000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3405000000000],
      [3375000000000]) (some (6, 1, 4)) (some (6, 1, 7)) (.next ([3000000000000], [3030000000000])
      (some (6, 1, 7)) (some (6, 1, 7)) (.next ([780000000000], [960000000000]) (some (6, 1, 7))
      (some (6, 1, 7)) (.next ([1230000000000], [1770000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([2205000000000], [3375000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
      ([1125000000000], [1980000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([585000000000],
      [1290000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([1980000000000], [4395000000000])
      (some (6, 1, 7)) (some (6, 2, 7)) (.next ([2115000000000], [5250000000000]) (some (6, 2, 7))
      (some (6, 2, 7)) (.next ([345000000000], [1020000000000]) (some (6, 2, 7)) (some (6, 2, 7))
      (.next ([885000000000], [3375000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([330000000000], [3960000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([375000000000],
      [6030000000000]) (some (6, 2, 7)) (some (6, 2, 7)) fan39Owner4Part0))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [279000000000]) (some (5, 0, 3))
      (some (5, 1, 3)) (.next ([2640000000000], [780000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([4110000000000], [2250000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([5580000000000], [3420000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4110000000000,
      0], [2970000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3390000000000,
      -9000000000000], [2970000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([3831000000000], [3654000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2706000000000],
      [3375000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2610000000000, -9000000000000],
      [6390000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next ([1926000000000],
      [6795000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([690000000000], [4890000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([0], [4110000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-279000000000], [3654000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next
      ([-780000000000], [3420000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2250000000000],
      [6360000000000]) (some (0, 2, 4)) (some (0, 2, 5)) (.next ([-3420000000000], [9000000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2970000000000, -9000000000000], [7080000000000,
      9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2970000000000, -9000000000000],
      [6360000000000]) (some (0, 2, 5)) (some (0, 3, 5)) (.next ([-3654000000000], [7485000000000])
      (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3375000000000], [6081000000000]) (some (0, 3, 5))
      (some (0, 3, 5)) (.next ([-6390000000000, -9000000000000], [9000000000000]) (some (0, 3, 5))
      (some (0, 3, 5)) (.next ([-6795000000000], [8721000000000]) (some (0, 3, 5)) (some (0, 3, 5))
      (.next ([-4890000000000], [5580000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.terminal (some
      (0, 3, 5)) (some (0, 3, 5)) (some (0, 3, 5))))))))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_8 : ExcludedOn (model39.B 8 ++ [step39.q]) 9000000000000 (model39.caps 8)
    (model39.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_9 : ExcludedOn (model39.B 9 ++ [step39.q]) 9000000000000 (model39.caps 9)
    (model39.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked39 : StepValid model39 9000000000000 step39 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded39_1
    · exact excluded39_2
    · exact excluded39_3
    · exact excluded39_4
    · exact excluded39_5
    · exact excluded39_6
    · exact excluded39_7
    · exact excluded39_8
    · exact excluded39_9
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint330000340000
end ConwaySoifer.Simplified.Certificates
