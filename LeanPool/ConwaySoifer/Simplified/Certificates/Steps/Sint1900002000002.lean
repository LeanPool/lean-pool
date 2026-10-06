/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint190000200000
import Mathlib.Tactic.FinCases

/-!
# Sint 190000 200000 2

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
namespace Sint190000200000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner4Part0 : FanWitness := (.next ([0, 0], [1710000000000, 9000000000000]) (some (6, 7,
    3)) (some (6, 7, 3)) (.next ([-390000000000], [3645000000000]) (some (0, 7, 3)) (some (0, 7, 4))
    (.next ([-570000000000], [5070000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
    ([-450000000000], [3270000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-450000000000],
    [2895000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-1410000000000, 9000000000000],
    [8250000000000]) (some (0, 7, 4)) (some (0, 7, 5)) (.next ([-1005000000000], [5130000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1380000000000], [5130000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-3120000000000], [8250000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-2280000000000, -9000000000000], [5070000000000, 0]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-3120000000000, 0], [6540000000000, -9000000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-1710000000000, -9000000000000], [3420000000000, 18000000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-2715000000000, -9000000000000], [5130000000000, 0]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-3090000000000, -9000000000000], [5130000000000, 0]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-3750000000000], [5700000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-4125000000000], [6135000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-4500000000000], [6510000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2115000000000,
    9000000000000], [2970000000000, -9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-3360000000000, 9000000000000], [4500000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-3825000000000], [4680000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-7395000000000],
    [8955000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-375000000000], [435000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3420000000000, 9000000000000], [3750000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-750000000000], [810000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.terminal (some (0, 7, 5)) (some (0, 7, 5)) (some (0, 7,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan17Owner4Part0 : FanWitness := (.next ([330000000000, 9000000000000], [3420000000000,
    -9000000000000]) (some (6, 7, 2)) (some (6, 7, 3)) (.next ([60000000000], [750000000000]) (some
    (6, 7, 3)) (some (6, 7, 3)) (.next ([0, 0], [1710000000000, 9000000000000]) (some (6, 7, 3))
    (some (6, 7, 3)) (.next ([-390000000000], [3645000000000]) (some (0, 7, 3)) (some (0, 7, 4))
    (.next ([-570000000000], [5070000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
    ([-450000000000], [3270000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-450000000000],
    [2895000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-1665000000000, 9000000000000],
    [8505000000000]) (some (0, 7, 4)) (some (0, 7, 5)) (.next ([-1005000000000], [5130000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1380000000000], [5130000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-3375000000000], [8505000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-2280000000000, -9000000000000], [5070000000000, 0]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-1710000000000, -9000000000000], [3420000000000, 18000000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-2715000000000, -9000000000000], [5130000000000, 0]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-3090000000000, -9000000000000], [5130000000000, 0]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-4005000000000], [5700000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-2115000000000, 9000000000000], [2970000000000, -9000000000000]) (some (0, 7, 5)) (some
    (0, 7, 5)) (.next ([-4380000000000], [6135000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-4755000000000], [6510000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3825000000000],
    [4680000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-7650000000000], [8955000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-375000000000], [435000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-3420000000000, 9000000000000], [3750000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-750000000000], [810000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.terminal (some (0, 7, 5)) (some (0, 7, 5)) (some (0, 7, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part0 : FanWitness := (.next ([-375000000000], [6375000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-510000000000], [6570000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-570000000000], [6630000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-195000000000], [1515000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-375000000000],
    [945000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-342000000000, -4800000000000],
    [831000000000, 2400000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-945000000000],
    [1890000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-5430000000000], [10275000000000])
    (some (8, 3, 7)) (some (8, 4, 7)) (.next ([-5625000000000], [10335000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-5685000000000], [10335000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-135000000000], [195000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-3330000000000], [4650000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-3525000000000],
    [4845000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-195000000000], [255000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-2988000000000, 4800000000000], [3819000000000,
    -2400000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5625000000000], [7005000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5685000000000], [7005000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-4275000000000], [5220000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-6261000000000, -2400000000000], [7287000000000, 4800000000000]) (some (8, 4, 7)) (some
    (8, 4, 7)) (.next ([-6456000000000, -2400000000000], [7347000000000, 4800000000000]) (some (8,
    4, 7)) (some (8, 4, 7)) (.next ([-6516000000000, -2400000000000], [7347000000000,
    4800000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-1287000000000, -4800000000000],
    [1401000000000, 2400000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6750000000000],
    [6945000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6945000000000], [7005000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.terminal (some (8, 4, 7)) (some (8, 4, 7)) (some (8, 4,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part1 : FanWitness := (.next ([1320000000000], [195000000000]) (some (7, 8, 5)) (some
    (7, 8, 5)) (.next ([570000000000], [375000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next
    ([489000000000, -2400000000000], [342000000000, 4800000000000]) (some (7, 8, 5)) (some (7, 8,
    5)) (.next ([945000000000], [945000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next
    ([4845000000000], [5430000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([4710000000000],
    [5625000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([4650000000000], [5685000000000])
    (some (7, 8, 5)) (some (7, 8, 5)) (.next ([60000000000], [135000000000]) (some (7, 8, 5)) (some
    (8, 8, 5)) (.next ([1320000000000], [3330000000000]) (some (8, 8, 5)) (some (8, 8, 6)) (.next
    ([1320000000000], [3525000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([60000000000],
    [195000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([831000000000, 2400000000000],
    [2988000000000, -4800000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1380000000000],
    [5625000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1320000000000], [5685000000000])
    (some (8, 2, 6)) (some (8, 2, 6)) (.next ([945000000000], [4275000000000]) (some (8, 2, 6))
    (some (8, 2, 6)) (.next ([1026000000000, 2400000000000], [6261000000000, 2400000000000]) (some
    (8, 2, 6)) (some (8, 2, 6)) (.next ([891000000000, 2400000000000], [6456000000000,
    2400000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([831000000000, 2400000000000],
    [6516000000000, 2400000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([114000000000,
    -2400000000000], [1287000000000, 4800000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
    ([195000000000], [6750000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([60000000000],
    [6945000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([0], [1320000000000]) (some (8, 2,
    6)) (some (8, 2, 6)) (.next ([-135000000000], [6945000000000]) (some (8, 2, 6)) (some (8, 3, 7))
    (.next ([-195000000000], [7005000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    fan19Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner5Part0 : FanWitness := (.next ([2985000000000], [135000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([3375000000000], [495000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([3120000000000], [750000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([3735000000000, 0],
    [1710000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([5329800000000],
    [3078000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([3619800000000, -9000000000000],
    [3078000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([1665000000000, -9000000000000],
    [2205000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([1410000000000,
    -9000000000000], [2460000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([792000000000], [5032800000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([792000000000],
    [5287800000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([657000000000], [8407800000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [3735000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([-135000000000], [3375000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-135000000000], [3120000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-495000000000],
    [3870000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-750000000000], [3870000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1710000000000, -9000000000000], [5445000000000,
    9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3078000000000], [8407800000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3078000000000, 0], [6697800000000, -9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2205000000000, -9000000000000], [3870000000000])
    (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-2460000000000, -9000000000000], [3870000000000])
    (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-5032800000000], [5824800000000]) (some (0, 5, 5))
    (some (0, 5, 5)) (.next ([-5287800000000], [6079800000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-8407800000000], [9064800000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some
    (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner4Part0 : FanWitness := (.next ([3015000000000, -9000000000000], [2085000000000,
    9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2415000000000, -9000000000000],
    [2715000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2040000000000,
    -9000000000000], [3090000000000, 9000000000000]) (some (5, 1, 2)) (some (6, 1, 2)) (.next
    ([1875000000000], [5100000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([1245000000000],
    [5130000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([870000000000], [5130000000000])
    (some (6, 1, 2)) (some (6, 1, 2)) (.next ([30000000000], [600000000000]) (some (6, 1, 2)) (some
    (6, 1, 2)) (.next ([30000000000], [975000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([0,
    0], [1710000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([-147000000000],
    [4725000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([-177000000000], [4125000000000])
    (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-177000000000], [3750000000000]) (some (6, 1, 4))
    (some (6, 1, 4)) (.next ([-375000000000], [5100000000000]) (some (6, 1, 4)) (some (6, 1, 5))
    (.next ([-1005000000000], [5130000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next
    ([-1710000000000, -9000000000000], [6663000000000, 9000000000000]) (some (6, 1, 5)) (some (6, 1,
    5)) (.next ([-1380000000000], [5130000000000]) (some (6, 1, 5)) (some (6, 1, 5)) (.next
    ([-2085000000000, -9000000000000], [5100000000000, 0]) (some (6, 1, 5)) (some (6, 1, 5)) (.next
    ([-2715000000000, -9000000000000], [5130000000000, 0]) (some (6, 1, 5)) (some (6, 2, 5)) (.next
    ([-3090000000000, -9000000000000], [5130000000000, 0]) (some (6, 2, 5)) (some (6, 2, 5)) (.next
    ([-5100000000000], [6975000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-5130000000000],
    [6375000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-5130000000000], [6000000000000])
    (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-600000000000], [630000000000]) (some (6, 2, 5))
    (some (6, 2, 5)) (.next ([-975000000000], [1005000000000]) (some (6, 2, 5)) (some (6, 2, 5))
    (.terminal (some (6, 2, 5)) (some (0, 2, 5)) (some (6, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part0 : FanWitness := (.next ([-570000000000], [6630000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-798000000000, 4800000000000], [8004000000000, -2400000000000]) (some
    (8, 3, 7)) (some (8, 3, 7)) (.next ([-195000000000], [1515000000000]) (some (8, 3, 7)) (some (8,
    3, 7)) (.next ([-1140000000000], [8835000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-1335000000000], [9030000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-1140000000000],
    [7515000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-2085000000000], [9405000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-375000000000], [945000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-342000000000, -4800000000000], [831000000000, 2400000000000]) (some
    (8, 3, 7)) (some (8, 3, 7)) (.next ([-945000000000], [1890000000000]) (some (8, 3, 7)) (some (8,
    3, 7)) (.next ([-537000000000, -4800000000000], [1026000000000, 2400000000000]) (some (8, 3, 7))
    (some (8, 4, 7)) (.next ([-135000000000], [195000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-195000000000], [255000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-5430000000000], [6945000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5625000000000],
    [7005000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5685000000000], [7005000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6261000000000, -2400000000000], [7287000000000,
    4800000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6456000000000, -2400000000000],
    [7347000000000, 4800000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6516000000000,
    -2400000000000], [7347000000000, 4800000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-8085000000000], [9030000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-8145000000000],
    [8895000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-8145000000000], [8835000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6750000000000], [6945000000000]) (some (8, 4, 7))
    (some (8, 4, 8)) (.next ([-6945000000000], [7005000000000]) (some (8, 4, 8)) (some (8, 4, 8))
    (.terminal (some (8, 4, 8)) (some (8, 4, 8)) (some (8, 4, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part1 : FanWitness := (.next ([6375000000000], [1140000000000]) (some (8, 1, 5))
    (some (8, 1, 5)) (.next ([7320000000000], [2085000000000]) (some (8, 1, 5)) (some (8, 1, 5))
    (.next ([570000000000], [375000000000]) (some (8, 1, 5)) (some (8, 1, 5)) (.next ([489000000000,
    -2400000000000], [342000000000, 4800000000000]) (some (8, 1, 5)) (some (8, 1, 5)) (.next
    ([945000000000], [945000000000]) (some (8, 1, 5)) (some (8, 2, 5)) (.next ([489000000000,
    -2400000000000], [537000000000, 4800000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([60000000000], [135000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([60000000000],
    [195000000000]) (some (8, 2, 5)) (some (8, 2, 6)) (.next ([1515000000000], [5430000000000])
    (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1380000000000], [5625000000000]) (some (8, 2, 6))
    (some (8, 2, 6)) (.next ([1320000000000], [5685000000000]) (some (8, 2, 6)) (some (8, 2, 6))
    (.next ([1026000000000, 2400000000000], [6261000000000, 2400000000000]) (some (8, 2, 6)) (some
    (8, 2, 6)) (.next ([891000000000, 2400000000000], [6456000000000, 2400000000000]) (some (8, 2,
    6)) (some (8, 2, 6)) (.next ([831000000000, 2400000000000], [6516000000000, 2400000000000])
    (some (8, 2, 6)) (some (8, 2, 6)) (.next ([945000000000], [8085000000000]) (some (8, 2, 6))
    (some (8, 2, 6)) (.next ([750000000000], [8145000000000]) (some (8, 2, 6)) (some (8, 2, 6))
    (.next ([690000000000], [8145000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
    ([195000000000], [6750000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([60000000000],
    [6945000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([0], [1320000000000]) (some (8, 2,
    6)) (some (8, 2, 6)) (.next ([-135000000000], [6945000000000]) (some (8, 2, 6)) (some (8, 3, 7))
    (.next ([-195000000000], [7005000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-375000000000], [6375000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-510000000000],
    [6570000000000]) (some (8, 3, 7)) (some (8, 3, 7)) fan22Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner4Part0 : FanWitness := (.next ([2190000000000], [4185000000000]) (some (6, 1, 2))
    (some (6, 1, 2)) (.next ([540000000000], [1797000000000]) (some (6, 1, 2)) (some (6, 1, 6))
    (.next ([540000000000], [6750000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([30000000000], [600000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([30000000000],
    [975000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0], [1710000000000,
    9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-147000000000], [4725000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-177000000000], [4125000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-177000000000], [3750000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-375000000000], [5100000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-1170000000000, -9000000000000], [8460000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1,
    6)) (.next ([-1005000000000], [5130000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-1710000000000, -9000000000000], [6663000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1,
    6)) (.next ([-1380000000000], [5130000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-2085000000000, -9000000000000], [5100000000000, 0]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-2715000000000, -9000000000000], [5130000000000, 0]) (some (0, 1, 6)) (some (0, 2, 6)) (.next
    ([-3210000000000], [5370000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3090000000000,
    -9000000000000], [5130000000000, 0]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3585000000000],
    [5745000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4185000000000], [6375000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1797000000000], [2337000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-6750000000000], [7290000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-600000000000], [630000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-975000000000], [1005000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.terminal (some (0, 2, 6))
    (some (0, 2, 6)) (some (0, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner4Part0 : FanWitness := (.next ([4953000000000], [3870000000000]) (some (5, 6, 2))
    (some (5, 6, 2)) (.next ([2415000000000, -9000000000000], [2715000000000, 9000000000000]) (some
    (5, 6, 2)) (some (5, 6, 2)) (.next ([2040000000000, -9000000000000], [3090000000000,
    9000000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([855000000000], [4245000000000]) (some
    (5, 6, 2)) (some (5, 6, 2)) (.next ([255000000000], [4875000000000]) (some (5, 6, 2)) (some (5,
    6, 2)) (.next ([30000000000], [600000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
    ([30000000000], [975000000000]) (some (5, 6, 2)) (some (5, 6, 3)) (.next ([0, 0],
    [1710000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([-120000000000],
    [5250000000000]) (some (0, 6, 3)) (some (0, 6, 4)) (.next ([-147000000000], [4725000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-177000000000], [4125000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-177000000000], [3750000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-375000000000], [5100000000000]) (some (0, 6, 4)) (some (0, 6, 5)) (.next
    ([-1005000000000], [5130000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-1710000000000,
    -9000000000000], [6663000000000, 9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-1380000000000], [5130000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2085000000000,
    -9000000000000], [5100000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3870000000000],
    [8823000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2715000000000, -9000000000000],
    [5130000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3090000000000, -9000000000000],
    [5130000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4245000000000], [5100000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4875000000000], [5130000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-600000000000], [630000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-975000000000], [1005000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0,
    2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3255000000000], [390000000000]) (some (5, 0, 7))
      (some (5, 1, 7)) (.next ([4500000000000], [570000000000]) (some (5, 1, 7)) (some (5, 1, 7))
      (.next ([2820000000000], [450000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next
      ([2445000000000], [450000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next ([6840000000000,
      9000000000000], [1410000000000, -9000000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next
      ([4125000000000], [1005000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next ([3750000000000],
      [1380000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next ([5130000000000], [3120000000000])
      (some (5, 1, 7)) (some (5, 1, 7)) (.next ([2790000000000, -9000000000000], [2280000000000,
      9000000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next ([3420000000000, -9000000000000],
      [3120000000000, 0]) (some (5, 1, 7)) (some (5, 1, 7)) (.next ([1710000000000, 9000000000000],
      [1710000000000, 9000000000000]) (some (5, 1, 7)) (some (5, 7, 7)) (.next ([2415000000000,
      -9000000000000], [2715000000000, 9000000000000]) (some (5, 7, 7)) (some (5, 7, 7)) (.next
      ([2040000000000, -9000000000000], [3090000000000, 9000000000000]) (some (5, 7, 7)) (some (5,
      7, 7)) (.next ([1950000000000], [3750000000000]) (some (5, 7, 7)) (some (5, 7, 7)) (.next
      ([2010000000000], [4125000000000]) (some (5, 7, 2)) (some (5, 7, 2)) (.next ([2010000000000],
      [4500000000000]) (some (5, 7, 2)) (some (5, 7, 2)) (.next ([855000000000], [2115000000000,
      -9000000000000]) (some (5, 7, 2)) (some (5, 7, 2)) (.next ([1140000000000, 9000000000000],
      [3360000000000, -9000000000000]) (some (5, 7, 2)) (some (6, 7, 2)) (.next ([855000000000],
      [3825000000000]) (some (6, 7, 2)) (some (6, 7, 2)) (.next ([1560000000000], [7395000000000])
      (some (6, 7, 2)) (some (6, 7, 2)) (.next ([60000000000], [375000000000]) (some (6, 7, 2))
      (some (6, 7, 2)) (.next ([330000000000, 9000000000000], [3420000000000, -9000000000000]) (some
      (6, 7, 2)) (some (6, 7, 3)) (.next ([60000000000], [750000000000]) (some (6, 7, 3)) (some (6,
      7, 3)) fan16Owner4Part0)))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1710000000000, 9000000000000], [1710000000000,
      9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([3870000000000, 0], [4170000000000,
      -9000000000000]) (some (3, 3, 2)) (some (3, 3, 2)) (.next ([3870000000000], [5880000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2160000000000, -9000000000000], [7590000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1710000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1710000000000, -9000000000000],
      [3420000000000, 18000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-4170000000000,
      9000000000000], [8040000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-5880000000000], [9750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-7590000000000,
      -9000000000000], [9750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded16_0
    · exact excluded16_1
    · exact excluded16_2
    · exact excluded16_3
    · exact excluded16_4
    · exact (hj rfl).elim
    · exact excluded16_6
    · exact excluded16_7
    · exact excluded16_8
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded17_0 : ExcludedOn (model17.B 0 ++ [step17.q]) 9000000000000 (model17.caps 0)
    (model17.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3255000000000], [390000000000]) (some (5, 0, 7))
      (some (5, 1, 7)) (.next ([4500000000000], [570000000000]) (some (5, 1, 7)) (some (5, 1, 7))
      (.next ([2820000000000], [450000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next
      ([2445000000000], [450000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next ([6840000000000,
      9000000000000], [1665000000000, -9000000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next
      ([4125000000000], [1005000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next ([3750000000000],
      [1380000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next ([5130000000000], [3375000000000])
      (some (5, 1, 7)) (some (5, 1, 7)) (.next ([2790000000000, -9000000000000], [2280000000000,
      9000000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next ([1710000000000, 9000000000000],
      [1710000000000, 9000000000000]) (some (5, 1, 7)) (some (5, 1, 7)) (.next ([2415000000000,
      -9000000000000], [2715000000000, 9000000000000]) (some (5, 1, 7)) (some (5, 7, 7)) (.next
      ([2040000000000, -9000000000000], [3090000000000, 9000000000000]) (some (5, 7, 7)) (some (5,
      7, 7)) (.next ([1695000000000], [4005000000000]) (some (5, 7, 7)) (some (5, 7, 7)) (.next
      ([855000000000], [2115000000000, -9000000000000]) (some (5, 7, 2)) (some (5, 7, 2)) (.next
      ([1755000000000], [4380000000000]) (some (5, 7, 2)) (some (6, 7, 2)) (.next ([1755000000000],
      [4755000000000]) (some (6, 7, 2)) (some (6, 7, 2)) (.next ([855000000000], [3825000000000])
      (some (6, 7, 2)) (some (6, 7, 2)) (.next ([1305000000000], [7650000000000]) (some (6, 7, 2))
      (some (6, 7, 2)) (.next ([60000000000], [375000000000]) (some (6, 7, 2)) (some (6, 7, 2))
      fan17Owner4Part0)))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1710000000000, 9000000000000], [1710000000000,
      9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([3870000000000], [5625000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2160000000000, -9000000000000], [7335000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1710000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1710000000000, -9000000000000],
      [3420000000000, 18000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-5625000000000],
      [9495000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-7335000000000, -9000000000000],
      [9495000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      3)) (some (3, 1, 3))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded18_0 : ExcludedOn (model18.B 0 ++ [step18.q]) 9000000000000 (model18.caps 0)
    (model18.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5580000000000], [960000000000, 9000000000000])
      (some (2, 4, 2)) (some (3, 4, 2)) (.next ([6105000000000], [1710000000000, 9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([5580000000000], [3297000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([6105000000000], [4047000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([525000000000], [750000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([750000000000], [4830000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [1710000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-960000000000,
      -9000000000000], [6540000000000, 9000000000000]) (some (0, 4, 2)) (some (4, 4, 2)) (.next
      ([-1710000000000, -9000000000000], [7815000000000, 9000000000000]) (some (4, 4, 2)) (some (4,
      4, 2)) (.next ([-3297000000000], [8877000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([-4047000000000], [10152000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-750000000000], [1275000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-4830000000000],
      [5580000000000]) (some (4, 1, 2)) (some (4, 2, 2)) (.terminal (some (4, 2, 2)) (some (4, 2,
      2)) (some (4, 2, 2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4680000000000], [273000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([4047000000000], [4953000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([1665000000000], [4320000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1032000000000], [3015000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [4320000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-273000000000], [4953000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4953000000000], [9000000000000]) (some (0, 1, 2))
      (some (0, 3, 2)) (.next ([-4320000000000], [5985000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3015000000000], [4047000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded18_2
    · exact excluded18_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6810000000000], [135000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([6810000000000], [195000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      (.next ([6000000000000], [375000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([6060000000000], [510000000000]) (some (7, 8, 4)) (some (7, 8, 5)) (.next ([6060000000000],
      [570000000000]) (some (7, 8, 5)) (some (7, 8, 5)) fan19Owner0Part1)))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3240000000000], [135000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([2985000000000], [135000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([5100000000000], [540000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([3375000000000], [495000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3120000000000],
      [750000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3735000000000, 0], [1710000000000,
      9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([5100000000000], [4275000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1665000000000, -9000000000000], [2205000000000,
      9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1980000000000], [3525000000000])
      (some (5, 1, 2)) (some (5, 1, 3)) (.next ([1725000000000], [3780000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([0], [3735000000000]) (some (5, 1, 3)) (some (5, 1, 5)) (.next
      ([-135000000000], [3375000000000]) (some (5, 1, 5)) (some (5, 2, 5)) (.next ([-135000000000],
      [3120000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-540000000000], [5640000000000])
      (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-495000000000], [3870000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-750000000000], [3870000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-1710000000000, -9000000000000], [5445000000000, 9000000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-4275000000000], [9375000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-2205000000000, -9000000000000], [3870000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-3525000000000], [5505000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-3780000000000], [5505000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded19_0
    · exact excluded19_1
    · exact excluded19_2
    · exact excluded19_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 5 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1710000000000, 9000000000000], [1710000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([3670200000000], [4212000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3670200000000], [5922000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1960200000000, -9000000000000], [7632000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1710000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-1710000000000, -9000000000000],
      [3420000000000, 18000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-4212000000000,
      9000000000000], [7882200000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-5922000000000], [9592200000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7632000000000,
      -9000000000000], [9592200000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3240000000000], [135000000000]) (some (3, 0, 5))
      (some (4, 1, 5)) fan20Owner5Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded20_0
    · exact excluded20_1
    · exact excluded20_2
    · exact excluded20_3
    · exact excluded20_4
    · exact excluded20_5
    · exact (hj rfl).elim
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4578000000000], [147000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([3948000000000], [177000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([3573000000000], [177000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([4725000000000], [375000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4125000000000],
      [1005000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4953000000000, 0], [1710000000000,
      9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3750000000000], [1380000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) fan21Owner4Part0)))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
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
    · exact excluded21_2
    · exact excluded21_3
    · exact excluded21_4
    · exact excluded21_5
    · exact excluded21_6
    · exact excluded21_7
    · exact (hj rfl).elim
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6810000000000], [135000000000]) (some (8, 8, 4))
      (some (8, 8, 4)) (.next ([6810000000000], [195000000000]) (some (8, 8, 4)) (some (8, 8, 4))
      (.next ([6000000000000], [375000000000]) (some (8, 8, 4)) (some (8, 8, 4)) (.next
      ([6060000000000], [510000000000]) (some (8, 8, 4)) (some (8, 8, 5)) (.next ([6060000000000],
      [570000000000]) (some (8, 8, 5)) (some (8, 8, 5)) (.next ([7206000000000, 2400000000000],
      [798000000000, -4800000000000]) (some (8, 8, 5)) (some (8, 8, 5)) (.next ([1320000000000],
      [195000000000]) (some (8, 1, 5)) (some (8, 1, 5)) (.next ([7695000000000], [1140000000000])
      (some (8, 1, 5)) (some (8, 1, 5)) (.next ([7695000000000], [1335000000000]) (some (8, 1, 5))
      (some (8, 1, 5)) fan22Owner0Part1)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4578000000000], [147000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([3948000000000], [177000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([3573000000000], [177000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([4725000000000], [375000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([7290000000000,
      0], [1170000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([4125000000000],
      [1005000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([4953000000000, 0], [1710000000000,
      9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([3750000000000], [1380000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([3015000000000, -9000000000000], [2085000000000,
      9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2415000000000, -9000000000000],
      [2715000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2160000000000],
      [3210000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2040000000000, -9000000000000],
      [3090000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2160000000000],
      [3585000000000]) (some (6, 1, 2)) (some (6, 1, 2)) fan22Owner4Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5985000000000], [765000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([2250000000000], [1305000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([2790000000000], [4500000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([2250000000000], [7290000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [6750000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-765000000000], [6750000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1305000000000], [3555000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-4500000000000], [7290000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-7290000000000], [9540000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded22_0
    · exact excluded22_1
    · exact excluded22_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 5 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5130000000000], [120000000000]) (some (5, 0, 2))
      (some (5, 6, 2)) (.next ([4578000000000], [147000000000]) (some (5, 6, 2)) (some (5, 6, 2))
      (.next ([3948000000000], [177000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([3573000000000], [177000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4725000000000],
      [375000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4125000000000], [1005000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4953000000000, 0], [1710000000000, 9000000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([3750000000000], [1380000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([3015000000000, -9000000000000], [2085000000000, 9000000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) fan23Owner4Part0)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded23_2
    · exact excluded23_3
    · exact excluded23_4
    · exact (hj rfl).elim
    · exact excluded23_6
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint190000200000
end ConwaySoifer.Simplified.Certificates
