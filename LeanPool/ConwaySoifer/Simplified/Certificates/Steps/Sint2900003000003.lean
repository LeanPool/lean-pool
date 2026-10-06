/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint290000300000
import Mathlib.Tactic.FinCases

/-!
# Sint 290000 300000 3

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
namespace Sint290000300000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner6Part0 : FanWitness := (.next ([4452000000000], [5250000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([1662000000000, 9000000000000], [2640000000000, -9000000000000]) (some
    (5, 6, 3)) (some (5, 6, 3)) (.next ([3525000000000], [6390000000000]) (some (5, 6, 3)) (some (5,
    6, 3)) (.next ([3510000000000], [6390000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
    ([1692000000000, -9000000000000], [3558000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6,
    3)) (.next ([1905000000000, -9000000000000], [4485000000000, 9000000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([1890000000000, -9000000000000], [4500000000000, 9000000000000]) (some
    (5, 6, 3)) (some (5, 6, 3)) (.next ([213000000000], [927000000000]) (some (5, 6, 3)) (some (5,
    6, 3)) (.next ([198000000000], [942000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([0],
    [15000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([-948000000000], [5250000000000]) (some
    (0, 6, 3)) (some (0, 6, 3)) (.next ([-1875000000000], [6390000000000]) (some (0, 6, 3)) (some
    (0, 6, 3)) (.next ([-1890000000000], [6390000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next
    ([-2610000000000, -9000000000000], [5400000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next
    ([-2610000000000, -9000000000000], [5220000000000, 18000000000000]) (some (0, 6, 3)) (some (0,
    6, 3)) (.next ([-5250000000000], [9702000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next
    ([-2640000000000, 9000000000000], [4302000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next
    ([-6390000000000], [9915000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([-6390000000000],
    [9900000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([-3558000000000, -9000000000000],
    [5250000000000]) (some (0, 6, 3)) (some (6, 6, 3)) (.next ([-4485000000000, -9000000000000],
    [6390000000000]) (some (6, 6, 3)) (some (6, 6, 4)) (.next ([-4500000000000, -9000000000000],
    [6390000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([-927000000000], [1140000000000])
    (some (6, 6, 4)) (some (6, 6, 4)) (.next ([-942000000000], [1140000000000]) (some (6, 6, 4))
    (some (6, 6, 5)) (.terminal (some (6, 6, 5)) (some (6, 2, 5)) (some (6, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner4Part0 : FanWitness := (.next ([-1260000000000], [3480000000000]) (some (10, 4, 8))
    (some (10, 4, 8)) (.next ([-2640000000000], [7095000000000]) (some (10, 4, 8)) (some (10, 4, 8))
    (.next ([-300000000000], [780000000000]) (some (10, 4, 8)) (some (10, 4, 8)) (.next
    ([-2265000000000], [5745000000000]) (some (10, 4, 8)) (some (10, 5, 8)) (.next
    ([-3000000000000], [7365000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-948000000000],
    [2223000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-933000000000], [2058000000000])
    (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-3780000000000], [7845000000000]) (some (10, 5, 8))
    (some (10, 5, 8)) (.next ([-2475000000000], [5100000000000]) (some (10, 5, 8)) (some (10, 5, 8))
    (.next ([-843000000000], [1698000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next
    ([-2640000000000], [5250000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next
    ([-3000000000000], [5520000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next
    ([-2640000000000], [4665000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next
    ([-4698000000000], [8220000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-543000000000],
    [918000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-1335000000000], [2220000000000])
    (some (10, 5, 8)) (some (10, 6, 8)) (.next ([-3780000000000], [6000000000000]) (some (10, 6, 8))
    (some (10, 6, 8)) (.next ([-4665000000000], [6510000000000]) (some (10, 6, 8)) (some (10, 6, 8))
    (.next ([-4698000000000], [6375000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-4725000000000], [5730000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-4875000000000], [5715000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-3105000000000], [3480000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-5145000000000], [5625000000000]) (some (10, 6, 8)) (some (10, 6, 8)) (.next
    ([-5100000000000], [5235000000000, 9000000000000]) (some (10, 6, 8)) (some (10, 6, 8))
    (.terminal (some (10, 6, 8)) (some (0, 6, 8)) (some (10, 6, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner4Part1 : FanWitness := (.next ([375000000000], [3105000000000]) (some (10, 1, 6))
    (some (10, 1, 6)) (.next ([480000000000], [5145000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([135000000000, 9000000000000], [5100000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([-30000000000, 9000000000000], [5250000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([-15000000000], [2475000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
    ([-30000000000], [2640000000000]) (some (10, 1, 6)) (some (10, 2, 6)) (.next ([-33000000000],
    [1710000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next ([-120000000000], [3000000000000])
    (some (10, 2, 6)) (some (10, 2, 7)) (.next ([-300000000000], [5625000000000]) (some (10, 2, 7))
    (some (10, 2, 7)) (.next ([-390000000000, 9000000000000], [5520000000000]) (some (10, 2, 7))
    (some (10, 2, 7)) (.next ([-15000000000], [165000000000]) (some (10, 2, 7)) (some (10, 2, 7))
    (.next ([-420000000000], [3780000000000]) (some (10, 2, 7)) (some (10, 3, 7)) (.next
    ([-435000000000], [2625000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-1170000000000,
    9000000000000], [6000000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-105000000000],
    [525000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-1218000000000], [6000000000000])
    (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-963000000000], [4698000000000]) (some (10, 3, 7))
    (some (10, 3, 7)) (.next ([-585000000000], [2610000000000]) (some (10, 3, 7)) (some (10, 3, 7))
    (.next ([-90000000000], [360000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([-1185000000000], [4290000000000]) (some (10, 3, 7)) (some (10, 4, 7)) (.next ([-765000000000,
    -9000000000000], [2610000000000, 9000000000000]) (some (10, 4, 7)) (some (10, 4, 8)) (.next
    ([-855000000000], [2520000000000]) (some (10, 4, 8)) (some (10, 4, 8)) (.next ([-390000000000],
    [1140000000000]) (some (10, 4, 8)) (some (10, 4, 8)) (.next ([-2475000000000], [6945000000000])
    (some (10, 4, 8)) (some (10, 4, 8)) fan25Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner4Part2 : FanWitness := (.next ([1665000000000], [855000000000]) (some (8, 1, 6)) (some
    (8, 1, 6)) (.next ([750000000000], [390000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next
    ([4470000000000], [2475000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next ([2220000000000],
    [1260000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next ([4455000000000], [2640000000000])
    (some (8, 1, 6)) (some (10, 1, 6)) (.next ([480000000000], [300000000000]) (some (10, 1, 6))
    (some (10, 1, 6)) (.next ([3480000000000], [2265000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([4365000000000], [3000000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
    ([1275000000000], [948000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([1125000000000],
    [933000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([4065000000000], [3780000000000])
    (some (10, 1, 6)) (some (10, 1, 6)) (.next ([2625000000000], [2475000000000]) (some (10, 1, 6))
    (some (10, 1, 6)) (.next ([855000000000], [843000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([2610000000000], [2640000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
    ([2520000000000], [3000000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([2025000000000],
    [2640000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([3522000000000], [4698000000000])
    (some (10, 1, 6)) (some (10, 1, 6)) (.next ([375000000000], [543000000000]) (some (10, 1, 6))
    (some (10, 1, 6)) (.next ([885000000000], [1335000000000]) (some (10, 1, 6)) (some (10, 1, 6))
    (.next ([2220000000000], [3780000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next
    ([1845000000000], [4665000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([1677000000000],
    [4698000000000]) (some (10, 1, 6)) (some (10, 1, 6)) (.next ([1005000000000], [4725000000000])
    (some (10, 1, 6)) (some (10, 1, 6)) (.next ([840000000000], [4875000000000]) (some (10, 1, 6))
    (some (10, 1, 6)) fan25Owner4Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner4Part0 : FanWitness := (.next ([-855000000000], [2520000000000]) (some (0, 9, 8))
    (some (0, 9, 8)) (.next ([-390000000000], [1140000000000]) (some (0, 9, 8)) (some (0, 9, 8))
    (.next ([-300000000000], [780000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next
    ([-948000000000], [2223000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-2760000000000],
    [6345000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-933000000000], [2058000000000])
    (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-2475000000000], [5100000000000]) (some (0, 9, 8))
    (some (0, 9, 8)) (.next ([-843000000000], [1698000000000]) (some (0, 9, 8)) (some (0, 9, 8))
    (.next ([-2640000000000], [5250000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next
    ([-3000000000000], [5520000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-4680000000000],
    [8265000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-543000000000], [918000000000])
    (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-2760000000000], [4665000000000]) (some (0, 9, 8))
    (some (0, 9, 8)) (.next ([-1335000000000], [2220000000000]) (some (0, 9, 8)) (some (0, 9, 8))
    (.next ([-3780000000000], [6000000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next
    ([-3003000000000], [4698000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-2460000000000],
    [3780000000000]) (some (0, 6, 8)) (some (0, 6, 8)) (.next ([-2160000000000], [3000000000000])
    (some (0, 6, 8)) (some (0, 6, 8)) (.next ([-4698000000000], [6375000000000]) (some (0, 6, 8))
    (some (0, 6, 8)) (.next ([-2070000000000], [2640000000000]) (some (0, 6, 8)) (some (0, 6, 8))
    (.next ([-5100000000000], [6210000000000]) (some (0, 6, 8)) (some (0, 6, 8)) (.next
    ([-2055000000000], [2475000000000]) (some (0, 6, 8)) (some (0, 6, 8)) (.next ([-5250000000000],
    [6195000000000]) (some (0, 6, 8)) (some (0, 6, 8)) (.next ([-5520000000000], [6105000000000])
    (some (0, 6, 8)) (some (0, 6, 8)) (.terminal (some (0, 6, 8)) (some (0, 6, 8)) (some (0, 6,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner4Part1 : FanWitness := (.next ([840000000000], [2160000000000]) (some (8, 9, 6)) (some
    (8, 9, 6)) (.next ([1677000000000], [4698000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([570000000000], [2070000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([1110000000000],
    [5100000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([420000000000], [2055000000000])
    (some (8, 9, 6)) (some (8, 9, 6)) (.next ([945000000000], [5250000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([585000000000], [5520000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([0], [2760000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([-15000000000],
    [4680000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([-33000000000], [1710000000000])
    (some (0, 9, 6)) (some (0, 9, 6)) (.next ([-195000000000], [6000000000000]) (some (0, 9, 6))
    (some (0, 9, 7)) (.next ([-135000000000], [2475000000000]) (some (0, 9, 7)) (some (0, 9, 7))
    (.next ([-150000000000], [2640000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next
    ([-240000000000], [3000000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-15000000000],
    [165000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-540000000000], [3780000000000])
    (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-435000000000], [2625000000000]) (some (0, 9, 7))
    (some (0, 9, 7)) (.next ([-1113000000000], [6375000000000]) (some (0, 9, 7)) (some (0, 9, 7))
    (.next ([-105000000000], [525000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next
    ([-585000000000], [2610000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-1083000000000],
    [4698000000000]) (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-1080000000000], [4665000000000])
    (some (0, 9, 7)) (some (0, 9, 7)) (.next ([-90000000000], [360000000000]) (some (0, 9, 7)) (some
    (0, 9, 8)) (.next ([-405000000000], [1305000000000]) (some (0, 9, 8)) (some (0, 9, 8))
    fan28Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner4Part2 : FanWitness := (.next ([5262000000000], [1113000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([420000000000], [105000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([2025000000000], [585000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([3615000000000], [1083000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([3585000000000],
    [1080000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([270000000000], [90000000000]) (some
    (8, 9, 6)) (some (8, 9, 6)) (.next ([900000000000], [405000000000]) (some (8, 9, 6)) (some (8,
    9, 6)) (.next ([1665000000000], [855000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([750000000000], [390000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([480000000000],
    [300000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([1275000000000], [948000000000]) (some
    (8, 9, 6)) (some (8, 9, 6)) (.next ([3585000000000], [2760000000000]) (some (8, 9, 6)) (some (8,
    9, 6)) (.next ([1125000000000], [933000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([2625000000000], [2475000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([855000000000],
    [843000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2610000000000], [2640000000000])
    (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2520000000000], [3000000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([3585000000000], [4680000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    (.next ([375000000000], [543000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
    ([1905000000000], [2760000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([885000000000],
    [1335000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2220000000000], [3780000000000])
    (some (8, 9, 6)) (some (8, 9, 6)) (.next ([1695000000000], [3003000000000]) (some (8, 9, 6))
    (some (8, 9, 6)) (.next ([1320000000000], [2460000000000]) (some (8, 9, 6)) (some (8, 9, 6))
    fan28Owner4Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner5Part0 : FanWitness := (.next ([5670000000000, -9000000000000], [1890000000000,
    9000000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([4155000000000], [1890000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4320000000000], [2085000000000]) (some (5, 1, 3))
    (some (5, 1, 5)) (.next ([2610000000000], [1515000000000]) (some (5, 1, 5)) (some (5, 1, 5))
    (.next ([4320000000000, 0], [2610000000000, 9000000000000]) (some (5, 1, 5)) (some (5, 1, 5))
    (.next ([5040000000000], [3240000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
    ([3795000000000, -9000000000000], [2610000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([2280000000000], [2610000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([2805000000000], [4125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([720000000000],
    [1155000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([720000000000], [7560000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [4320000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([0, -9000000000000], [1515000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-1890000000000, -9000000000000], [7560000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1890000000000], [6045000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2085000000000],
    [6405000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1515000000000], [4125000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2610000000000, -9000000000000], [6930000000000,
    9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3240000000000], [8280000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2610000000000, -9000000000000], [6405000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2610000000000], [4890000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4125000000000], [6930000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-1155000000000], [1875000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-7560000000000], [8280000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
    5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner6Part0 : FanWitness := (.next ([1692000000000, -9000000000000], [3558000000000,
    9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1905000000000, -9000000000000],
    [4485000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1890000000000,
    -9000000000000], [4500000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([1890000000000, 9000000000000], [5670000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1,
    3)) (.next ([213000000000], [927000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([198000000000], [942000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([228000000000],
    [3030000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([0], [15000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([-720000000000], [8280000000000]) (some (6, 1, 3)) (some (6, 2, 3))
    (.next ([-948000000000], [5250000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next
    ([-1875000000000], [6390000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-1890000000000],
    [6390000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-3330000000000, -9000000000000],
    [8280000000000]) (some (6, 2, 3)) (some (6, 2, 3)) (.next ([-2610000000000, -9000000000000],
    [5220000000000, 18000000000000]) (some (6, 2, 3)) (some (6, 2, 6)) (.next ([-2640000000000,
    9000000000000], [4302000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([-1890000000000],
    [3060000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.next ([-1890000000000], [3045000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3558000000000, -9000000000000], [5250000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4485000000000, -9000000000000], [6390000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4500000000000, -9000000000000], [6390000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-5670000000000, 9000000000000], [7560000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-927000000000], [1140000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-942000000000], [1140000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-3030000000000], [3258000000000]) (some (0, 2, 6)) (some (1, 2, 6)) (.terminal (some
    (1, 2, 6)) (some (1, 2, 6)) (some (1, 2, 6)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4302000000000], [948000000000]) (some (5, 6, 2))
      (some (5, 6, 3)) (.next ([4515000000000], [1875000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      (.next ([4500000000000], [1890000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([2790000000000, -9000000000000], [2610000000000, 9000000000000]) (some (5, 6, 3)) (some (5,
      6, 3)) (.next ([2610000000000, 9000000000000], [2610000000000, 9000000000000]) (some (5, 6,
      3)) (some (5, 6, 3)) fan24Owner6Part0)))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded24_8
    · exact (hj rfl).elim
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2460000000000], [15000000000]) (some (8, 0, 6))
      (some (8, 1, 6)) (.next ([2610000000000], [30000000000]) (some (8, 1, 6)) (some (8, 1, 6))
      (.next ([1677000000000], [33000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next
      ([2880000000000], [120000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next ([5325000000000],
      [300000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next ([5130000000000, 9000000000000],
      [390000000000, -9000000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next ([150000000000],
      [15000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next ([3360000000000], [420000000000])
      (some (8, 1, 6)) (some (8, 1, 6)) (.next ([2190000000000], [435000000000]) (some (8, 1, 6))
      (some (8, 1, 6)) (.next ([4830000000000, 9000000000000], [1170000000000, -9000000000000])
      (some (8, 1, 6)) (some (8, 1, 6)) (.next ([420000000000], [105000000000]) (some (8, 1, 6))
      (some (8, 1, 6)) (.next ([4782000000000], [1218000000000]) (some (8, 1, 6)) (some (8, 1, 6))
      (.next ([3735000000000], [963000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next
      ([2025000000000], [585000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next ([270000000000],
      [90000000000]) (some (8, 1, 6)) (some (8, 1, 6)) (.next ([3105000000000], [1185000000000])
      (some (8, 1, 6)) (some (8, 1, 6)) (.next ([1845000000000], [765000000000, 9000000000000])
      (some (8, 1, 6)) (some (8, 1, 6)) fan25Owner4Part2))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
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
    · exact excluded25_0
    · exact excluded25_1
    · exact excluded25_2
    · exact excluded25_3
    · exact excluded25_4
    · exact excluded25_5
    · exact excluded25_6
    · exact excluded25_7
    · exact (hj rfl).elim
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4935000000000], [2220000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([5415000000000], [3585000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1845000000000], [1740000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1350000000000], [4065000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [7155000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2220000000000], [7155000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3585000000000], [9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1740000000000], [3585000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-4065000000000], [5415000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6240000000000], [165000000000]) (some (4, 0, 2))
      (some (4, 1, 3)) (.next ([6240000000000, 0], [2610000000000, 9000000000000]) (some (4, 1, 3))
      (some (5, 1, 3)) (.next ([2610000000000], [1515000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([3795000000000, -9000000000000], [2610000000000, 9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([4725000000000], [4125000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([2655000000000, 0], [2610000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([2280000000000], [2610000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([2655000000000], [3750000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next ([1140000000000],
      [4125000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([0], [2655000000000]) (some (5, 1,
      4)) (some (5, 1, 4)) (.next ([-165000000000], [6405000000000]) (some (5, 1, 4)) (some (5, 2,
      4)) (.next ([-2610000000000, -9000000000000], [8850000000000, 9000000000000]) (some (5, 2, 4))
      (some (5, 2, 4)) (.next ([-1515000000000], [4125000000000]) (some (5, 2, 4)) (some (5, 2, 4))
      (.next ([-2610000000000, -9000000000000], [6405000000000]) (some (5, 2, 4)) (some (5, 2, 4))
      (.next ([-4125000000000], [8850000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-2610000000000, -9000000000000], [5265000000000, 9000000000000]) (some (5, 2, 4)) (some (5,
      2, 4)) (.next ([-2610000000000], [4890000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-3750000000000], [6405000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-4125000000000], [5265000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.terminal (some (5, 2,
      4)) (some (0, 2, 4)) (some (5, 2, 4))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded28_0 : ExcludedOn (model28.B 0 ++ [step28.q]) 9000000000000 (model28.caps 0)
    (model28.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4665000000000], [15000000000]) (some (8, 0, 6))
      (some (8, 9, 6)) (.next ([1677000000000], [33000000000]) (some (8, 9, 6)) (some (8, 9, 6))
      (.next ([5805000000000], [195000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next
      ([2340000000000], [135000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2490000000000],
      [150000000000]) (some (8, 9, 6)) (some (8, 9, 6)) (.next ([2760000000000], [240000000000])
      (some (8, 9, 6)) (some (8, 9, 6)) (.next ([150000000000], [15000000000]) (some (8, 9, 6))
      (some (8, 9, 6)) (.next ([3240000000000], [540000000000]) (some (8, 9, 6)) (some (8, 9, 6))
      (.next ([2190000000000], [435000000000]) (some (8, 9, 6)) (some (8, 9, 6))
      fan28Owner4Part2)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded28_0
    · exact excluded28_1
    · exact excluded28_2
    · exact excluded28_3
    · exact excluded28_4
    · exact (hj rfl).elim
    · exact excluded28_6
    · exact excluded28_7
    · exact excluded28_8
    · exact excluded28_9
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded29_0 : ExcludedOn (model29.B 0 ++ [step29.q]) 9000000000000 (model29.caps 0)
    (model29.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2895000000000], [30000000000]) (some (4, 0, 2))
      (some (4, 1, 3)) (.next ([4860000000000], [645000000000]) (some (4, 1, 3)) (some (5, 1, 3))
      (.next ([4320000000000], [2085000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([2610000000000], [1515000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4320000000000,
      0], [2610000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3795000000000,
      -9000000000000], [2610000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([3480000000000], [2895000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2280000000000],
      [2610000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1425000000000], [2055000000000])
      (some (5, 1, 3)) (some (5, 1, 4)) (.next ([2805000000000], [4125000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([870000000000, -9000000000000], [5505000000000, 9000000000000]) (some
      (0, 1, 4)) (some (0, 1, 4)) (.next ([0], [4320000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-30000000000], [2925000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next
      ([-645000000000], [5505000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2085000000000],
      [6405000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1515000000000], [4125000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2610000000000, -9000000000000], [6930000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2610000000000, -9000000000000],
      [6405000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2895000000000], [6375000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2610000000000], [4890000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2055000000000], [3480000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-4125000000000], [6930000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-5505000000000, -9000000000000], [6375000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded29_0
    · exact excluded29_1
    · exact excluded29_2
    · exact excluded29_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2640000000000], [15000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([4875000000000], [375000000000]) (some (4, 1, 2)) (some (5, 1, 3))
      (.next ([4320000000000], [2085000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([2610000000000], [1515000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4320000000000,
      0], [2610000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3750000000000],
      [2640000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2280000000000], [2610000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1680000000000], [2070000000000]) (some (5, 1, 3))
      (some (5, 1, 4)) (.next ([2805000000000], [4125000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([1140000000000, -9000000000000], [5250000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([0], [4320000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-15000000000], [2655000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-375000000000],
      [5250000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2085000000000], [6405000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1515000000000], [4125000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2610000000000, -9000000000000], [6930000000000, 9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2640000000000], [6390000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-2610000000000], [4890000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-2070000000000], [3750000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-4125000000000], [6930000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-5250000000000,
      -9000000000000], [6390000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_3 : ExcludedOn (model31.B 3 ++ [step31.q]) 9000000000000 (model31.caps 3)
    (model31.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1515000000000, -9000000000000], [0,
      9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan31Owner5Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_6 : ExcludedOn (model31.B 6 ++ [step31.q]) 9000000000000 (model31.caps 6)
    (model31.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7560000000000], [720000000000]) (some (6, 1, 2))
      (some (6, 1, 3)) (.next ([4302000000000], [948000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([4515000000000], [1875000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([4500000000000], [1890000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([4950000000000,
      -9000000000000], [3330000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
      ([2610000000000, 9000000000000], [2610000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1,
      3)) (.next ([1662000000000, 9000000000000], [2640000000000, -9000000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([1170000000000], [1890000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([1155000000000], [1890000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      fan31Owner6Part0)))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
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

end Sint290000300000
end ConwaySoifer.Simplified.Certificates
