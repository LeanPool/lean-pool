/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint190000200000
import Mathlib.Tactic.FinCases

/-!
# Sint 190000 200000 1

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
def fan10Owner0Part0 : FanWitness := (.next ([-570000000000], [6630000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-195000000000], [1515000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-375000000000], [945000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-4425000000000], [10245000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4620000000000],
    [10305000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-4680000000000], [10305000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-945000000000], [1890000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-537000000000, -4800000000000], [1026000000000, 2400000000000]) (some
    (8, 3, 7)) (some (8, 4, 7)) (.next ([-3300000000000], [5625000000000]) (some (8, 4, 7)) (some
    (8, 4, 7)) (.next ([-3495000000000], [5820000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-2958000000000, 4800000000000], [4794000000000, -2400000000000]) (some (8, 4, 7)) (some (8, 4,
    7)) (.next ([-4245000000000], [6195000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-135000000000], [195000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-195000000000],
    [255000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-3300000000000], [4305000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5430000000000], [6945000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-5625000000000], [7005000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-5685000000000], [7005000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-6261000000000, -2400000000000], [7287000000000, 4800000000000]) (some (8, 4, 7)) (some (8, 4,
    7)) (.next ([-6456000000000, -2400000000000], [7347000000000, 4800000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-6516000000000, -2400000000000], [7347000000000, 4800000000000]) (some
    (8, 4, 7)) (some (8, 4, 7)) (.next ([-1287000000000, -4800000000000], [1401000000000,
    2400000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6750000000000], [6945000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6945000000000], [7005000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.terminal (some (8, 4, 7)) (some (8, 4, 7)) (some (8, 4,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan10Owner0Part1 : FanWitness := (.next ([5625000000000], [4680000000000]) (some (7, 8, 5))
    (some (7, 8, 5)) (.next ([945000000000], [945000000000]) (some (7, 8, 5)) (some (8, 8, 5))
    (.next ([489000000000, -2400000000000], [537000000000, 4800000000000]) (some (8, 8, 5)) (some
    (8, 8, 5)) (.next ([2325000000000], [3300000000000]) (some (8, 8, 5)) (some (8, 8, 5)) (.next
    ([2325000000000], [3495000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([1836000000000,
    2400000000000], [2958000000000, -4800000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([1950000000000], [4245000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([60000000000],
    [135000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([60000000000], [195000000000]) (some
    (8, 2, 5)) (some (8, 2, 6)) (.next ([1005000000000], [3300000000000]) (some (8, 2, 6)) (some (8,
    2, 6)) (.next ([1515000000000], [5430000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
    ([1380000000000], [5625000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1320000000000],
    [5685000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1026000000000, 2400000000000],
    [6261000000000, 2400000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([891000000000,
    2400000000000], [6456000000000, 2400000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
    ([831000000000, 2400000000000], [6516000000000, 2400000000000]) (some (8, 2, 6)) (some (8, 2,
    6)) (.next ([114000000000, -2400000000000], [1287000000000, 4800000000000]) (some (8, 2, 6))
    (some (8, 2, 6)) (.next ([195000000000], [6750000000000]) (some (8, 2, 6)) (some (8, 2, 6))
    (.next ([60000000000], [6945000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([0],
    [1320000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([-135000000000], [6945000000000])
    (some (8, 2, 6)) (some (8, 3, 7)) (.next ([-195000000000], [7005000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-375000000000], [6375000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-510000000000], [6570000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    fan10Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan11Owner0Part0 : FanWitness := (.next ([-195000000000], [1515000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-375000000000], [945000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-342000000000, -4800000000000], [831000000000, 2400000000000]) (some (8, 3, 7)) (some
    (8, 3, 7)) (.next ([-4800000000000], [10245000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-4995000000000], [10305000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-5055000000000],
    [10305000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-945000000000], [1890000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-537000000000, -4800000000000], [1026000000000,
    2400000000000]) (some (8, 3, 7)) (some (8, 4, 7)) (.next ([-3300000000000], [5250000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-3495000000000], [5445000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-2958000000000, 4800000000000], [4419000000000, -2400000000000]) (some
    (8, 4, 7)) (some (8, 4, 7)) (.next ([-135000000000], [195000000000]) (some (8, 4, 7)) (some (8,
    4, 7)) (.next ([-4245000000000], [5820000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-195000000000], [255000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5430000000000],
    [6945000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5625000000000], [7005000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5685000000000], [7005000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-3300000000000], [3930000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-6261000000000, -2400000000000], [7287000000000, 4800000000000]) (some (8, 4, 7)) (some
    (8, 4, 7)) (.next ([-6456000000000, -2400000000000], [7347000000000, 4800000000000]) (some (8,
    4, 7)) (some (8, 4, 7)) (.next ([-6516000000000, -2400000000000], [7347000000000,
    4800000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-1287000000000, -4800000000000],
    [1401000000000, 2400000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6750000000000],
    [6945000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6945000000000], [7005000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.terminal (some (8, 4, 7)) (some (8, 4, 7)) (some (8, 4,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan11Owner0Part1 : FanWitness := (.next ([945000000000], [945000000000]) (some (7, 8, 5)) (some
    (8, 8, 5)) (.next ([489000000000, -2400000000000], [537000000000, 4800000000000]) (some (8, 8,
    5)) (some (8, 8, 5)) (.next ([1950000000000], [3300000000000]) (some (8, 8, 5)) (some (8, 8, 5))
    (.next ([1950000000000], [3495000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([1461000000000, 2400000000000], [2958000000000, -4800000000000]) (some (8, 2, 5)) (some (8, 2,
    5)) (.next ([60000000000], [135000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([1575000000000], [4245000000000]) (some (8, 2, 5)) (some (8, 2, 6)) (.next ([60000000000],
    [195000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1515000000000], [5430000000000])
    (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1380000000000], [5625000000000]) (some (8, 2, 6))
    (some (8, 2, 6)) (.next ([1320000000000], [5685000000000]) (some (8, 2, 6)) (some (8, 2, 6))
    (.next ([630000000000], [3300000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
    ([1026000000000, 2400000000000], [6261000000000, 2400000000000]) (some (8, 2, 6)) (some (8, 2,
    6)) (.next ([891000000000, 2400000000000], [6456000000000, 2400000000000]) (some (8, 2, 6))
    (some (8, 2, 6)) (.next ([831000000000, 2400000000000], [6516000000000, 2400000000000]) (some
    (8, 2, 6)) (some (8, 2, 6)) (.next ([114000000000, -2400000000000], [1287000000000,
    4800000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([195000000000], [6750000000000]) (some
    (8, 2, 6)) (some (8, 2, 6)) (.next ([60000000000], [6945000000000]) (some (8, 2, 6)) (some (8,
    2, 6)) (.next ([0], [1320000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([-135000000000],
    [6945000000000]) (some (8, 2, 6)) (some (8, 3, 7)) (.next ([-195000000000], [7005000000000])
    (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-375000000000], [6375000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-510000000000], [6570000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-570000000000], [6630000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    fan11Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner0Part0 : FanWitness := (.next ([-195000000000], [1515000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-375000000000], [945000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-342000000000, -4800000000000], [831000000000, 2400000000000]) (some (8, 3, 7)) (some
    (8, 3, 7)) (.next ([-945000000000], [1890000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-5235000000000], [10305000000000]) (some (8, 3, 7)) (some (8, 4, 7)) (.next ([-5430000000000],
    [10365000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5490000000000], [10365000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-489000000000, 2400000000000], [831000000000,
    2400000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-3360000000000], [4875000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-135000000000], [195000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-3555000000000], [5070000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-3018000000000, 4800000000000], [4044000000000, -2400000000000]) (some (8, 4, 7)) (some
    (8, 4, 7)) (.next ([-195000000000], [255000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-5430000000000], [6945000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-4305000000000],
    [5445000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5625000000000], [7005000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5685000000000], [7005000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-6261000000000, -2400000000000], [7287000000000, 4800000000000]) (some
    (8, 4, 7)) (some (8, 4, 7)) (.next ([-6456000000000, -2400000000000], [7347000000000,
    4800000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6516000000000, -2400000000000],
    [7347000000000, 4800000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-1287000000000,
    -4800000000000], [1401000000000, 2400000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-3360000000000], [3555000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6750000000000],
    [6945000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-6945000000000], [7005000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.terminal (some (8, 4, 7)) (some (8, 4, 7)) (some (8, 4,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner0Part1 : FanWitness := (.next ([4875000000000], [5490000000000]) (some (7, 8, 5))
    (some (7, 8, 5)) (.next ([342000000000, 4800000000000], [489000000000, -2400000000000]) (some
    (7, 8, 5)) (some (8, 8, 5)) (.next ([1515000000000], [3360000000000]) (some (8, 8, 5)) (some (8,
    8, 5)) (.next ([60000000000], [135000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([1515000000000], [3555000000000]) (some (8, 2, 5)) (some (8, 2, 6)) (.next ([1026000000000,
    2400000000000], [3018000000000, -4800000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
    ([60000000000], [195000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1515000000000],
    [5430000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1140000000000], [4305000000000])
    (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1380000000000], [5625000000000]) (some (8, 2, 6))
    (some (8, 2, 6)) (.next ([1320000000000], [5685000000000]) (some (8, 2, 6)) (some (8, 2, 6))
    (.next ([1026000000000, 2400000000000], [6261000000000, 2400000000000]) (some (8, 2, 6)) (some
    (8, 2, 6)) (.next ([891000000000, 2400000000000], [6456000000000, 2400000000000]) (some (8, 2,
    6)) (some (8, 2, 6)) (.next ([831000000000, 2400000000000], [6516000000000, 2400000000000])
    (some (8, 2, 6)) (some (8, 2, 6)) (.next ([114000000000, -2400000000000], [1287000000000,
    4800000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([195000000000], [3360000000000]) (some
    (8, 2, 6)) (some (8, 2, 6)) (.next ([195000000000], [6750000000000]) (some (8, 2, 6)) (some (8,
    2, 6)) (.next ([60000000000], [6945000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([0],
    [1320000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([-135000000000], [6945000000000])
    (some (8, 2, 6)) (some (8, 3, 7)) (.next ([-195000000000], [7005000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-375000000000], [6375000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-510000000000], [6570000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-570000000000], [6630000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    fan12Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part0 : FanWitness := (.next ([-570000000000], [6630000000000]) (some (8, 3, 7))
    (some (8, 3, 7)) (.next ([-195000000000], [1515000000000]) (some (8, 3, 7)) (some (8, 3, 7))
    (.next ([-2475000000000], [7875000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-2964000000000, 2400000000000], [8706000000000, 2400000000000]) (some (0, 3, 7)) (some (0, 3,
    7)) (.next ([-1545000000000], [3990000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-375000000000], [945000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-3795000000000],
    [9195000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-1605000000000], [3855000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-1605000000000], [3795000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.next ([-3990000000000], [9195000000000]) (some (0, 3, 7)) (some (0, 3, 8))
    (.next ([-4365000000000], [8820000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next
    ([-945000000000], [1890000000000]) (some (0, 3, 8)) (some (0, 3, 8)) (.next ([-537000000000,
    -4800000000000], [1026000000000, 2400000000000]) (some (0, 3, 8)) (some (0, 4, 8)) (.next
    ([-135000000000], [195000000000]) (some (0, 4, 8)) (some (0, 4, 8)) (.next ([-195000000000],
    [255000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-5430000000000], [6945000000000])
    (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-5625000000000], [7005000000000]) (some (1, 4, 8))
    (some (1, 4, 8)) (.next ([-5685000000000], [7005000000000]) (some (1, 4, 8)) (some (1, 4, 8))
    (.next ([-6261000000000, -2400000000000], [7287000000000, 4800000000000]) (some (1, 4, 8)) (some
    (1, 4, 8)) (.next ([-6456000000000, -2400000000000], [7347000000000, 4800000000000]) (some (1,
    4, 8)) (some (1, 4, 8)) (.next ([-6516000000000, -2400000000000], [7347000000000,
    4800000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-1287000000000, -4800000000000],
    [1401000000000, 2400000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-6750000000000],
    [6945000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-6945000000000], [7005000000000])
    (some (1, 4, 8)) (some (1, 4, 8)) (.terminal (some (1, 4, 8)) (some (1, 4, 8)) (some (1, 4,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan13Owner0Part1 : FanWitness := (.next ([570000000000], [375000000000]) (some (8, 1, 5)) (some
    (8, 1, 5)) (.next ([5400000000000], [3795000000000]) (some (8, 1, 5)) (some (8, 1, 5)) (.next
    ([2250000000000], [1605000000000]) (some (8, 1, 5)) (some (8, 1, 5)) (.next ([2190000000000],
    [1605000000000]) (some (8, 1, 5)) (some (8, 1, 5)) (.next ([5205000000000], [3990000000000])
    (some (8, 1, 5)) (some (8, 1, 5)) (.next ([4455000000000], [4365000000000]) (some (8, 1, 5))
    (some (8, 2, 5)) (.next ([945000000000], [945000000000]) (some (8, 2, 5)) (some (8, 2, 5))
    (.next ([489000000000, -2400000000000], [537000000000, 4800000000000]) (some (8, 2, 5)) (some
    (8, 2, 5)) (.next ([60000000000], [135000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([60000000000], [195000000000]) (some (8, 2, 5)) (some (8, 2, 6)) (.next ([1515000000000],
    [5430000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1380000000000], [5625000000000])
    (some (8, 2, 6)) (some (8, 2, 6)) (.next ([1320000000000], [5685000000000]) (some (8, 2, 6))
    (some (8, 2, 6)) (.next ([1026000000000, 2400000000000], [6261000000000, 2400000000000]) (some
    (8, 2, 6)) (some (8, 2, 6)) (.next ([891000000000, 2400000000000], [6456000000000,
    2400000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([831000000000, 2400000000000],
    [6516000000000, 2400000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([114000000000,
    -2400000000000], [1287000000000, 4800000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
    ([195000000000], [6750000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([60000000000],
    [6945000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([0], [1320000000000]) (some (8, 2,
    6)) (some (8, 2, 6)) (.next ([-135000000000], [6945000000000]) (some (8, 2, 6)) (some (8, 3, 7))
    (.next ([-195000000000], [7005000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next
    ([-375000000000], [6375000000000]) (some (8, 3, 7)) (some (8, 3, 7)) (.next ([-510000000000],
    [6570000000000]) (some (8, 3, 7)) (some (8, 3, 7)) fan13Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan14Owner4Part0 : FanWitness := (.next ([60000000000], [375000000000]) (some (7, 1, 2)) (some
    (7, 1, 2)) (.next ([330000000000, 9000000000000], [3420000000000, -9000000000000]) (some (7, 1,
    2)) (some (7, 1, 3)) (.next ([60000000000], [750000000000]) (some (7, 1, 3)) (some (7, 1, 3))
    (.next ([0, 0], [1710000000000, 9000000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
    ([-390000000000], [3645000000000]) (some (7, 1, 3)) (some (7, 1, 4)) (.next ([-570000000000],
    [5070000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-450000000000], [3270000000000])
    (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-450000000000], [2895000000000]) (some (7, 1, 4))
    (some (7, 1, 4)) (.next ([-1005000000000], [5130000000000]) (some (7, 1, 4)) (some (7, 1, 5))
    (.next ([-1380000000000], [5130000000000]) (some (7, 1, 5)) (some (7, 1, 5)) (.next
    ([-1710000000000, -9000000000000], [4680000000000]) (some (7, 1, 5)) (some (7, 1, 5)) (.next
    ([-2280000000000, -9000000000000], [5070000000000, 0]) (some (7, 1, 5)) (some (7, 1, 5)) (.next
    ([-1710000000000, -9000000000000], [3420000000000, 18000000000000]) (some (7, 1, 5)) (some (7,
    2, 5)) (.next ([-2715000000000, -9000000000000], [5130000000000, 0]) (some (7, 2, 5)) (some (7,
    2, 5)) (.next ([-5070000000000], [9180000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next
    ([-5130000000000], [8805000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-5130000000000],
    [8430000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-2115000000000, 9000000000000],
    [2970000000000, -9000000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-3360000000000,
    9000000000000], [4500000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-3825000000000],
    [4680000000000]) (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-4680000000000], [5535000000000])
    (some (7, 2, 5)) (some (7, 2, 5)) (.next ([-375000000000], [435000000000]) (some (7, 2, 5))
    (some (7, 2, 7)) (.next ([-3420000000000, 9000000000000], [3750000000000]) (some (7, 2, 7))
    (some (7, 2, 7)) (.next ([-750000000000], [810000000000]) (some (7, 2, 7)) (some (7, 2, 7))
    (.terminal (some (7, 2, 7)) (some (0, 2, 7)) (some (7, 2, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan15Owner4Part0 : FanWitness := (.next ([330000000000, 9000000000000], [3420000000000,
    -9000000000000]) (some (6, 7, 2)) (some (6, 7, 3)) (.next ([60000000000], [750000000000]) (some
    (6, 7, 3)) (some (6, 7, 3)) (.next ([0, 0], [1710000000000, 9000000000000]) (some (6, 7, 3))
    (some (6, 7, 3)) (.next ([-390000000000], [3645000000000]) (some (0, 7, 3)) (some (0, 7, 4))
    (.next ([-570000000000], [5070000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
    ([-765000000000], [5835000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-450000000000],
    [3270000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-450000000000], [2895000000000])
    (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-1140000000000], [6270000000000]) (some (0, 7, 4))
    (some (0, 7, 5)) (.next ([-1005000000000], [5130000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-1515000000000], [6645000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-1380000000000], [5130000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2280000000000,
    -9000000000000], [5070000000000, 0]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4410000000000],
    [9090000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1710000000000, -9000000000000],
    [3420000000000, 18000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2715000000000,
    -9000000000000], [5130000000000, 0]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3090000000000,
    -9000000000000], [5130000000000, 0]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2115000000000,
    9000000000000], [2970000000000, -9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-3360000000000, 9000000000000], [4500000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-5265000000000], [6975000000000, 9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-3825000000000], [4680000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-375000000000],
    [435000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3420000000000, 9000000000000],
    [3750000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-750000000000], [810000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.terminal (some (0, 7, 5)) (some (0, 7, 5)) (some (0, 7,
    5)))))))))))))))))))))))))))

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_4 : ExcludedOn (model8.B 4 ++ [step8.q]) 9000000000000 (model8.caps 4) (model8.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_9 : ExcludedOn (model8.B 9 ++ [step8.q]) 9000000000000 (model8.caps 9) (model8.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked8 : StepValid model8 9000000000000 step8 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded8_0
    · exact excluded8_1
    · exact excluded8_2
    · exact excluded8_3
    · exact excluded8_4
    · exact excluded8_5
    · exact excluded8_6
    · exact excluded8_7
    · exact (hj rfl).elim
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_0 : ExcludedOn (model9.B 0 ++ [step9.q]) 9000000000000 (model9.caps 0) (model9.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_8 : ExcludedOn (model9.B 8 ++ [step9.q]) 9000000000000 (model9.caps 8) (model9.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4275000000000, -9000000000000], [1710000000000,
      9000000000000]) (some (0, 0, 3)) (some (0, 1, 3)) (.next ([5175000000000], [4680000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3465000000000, -9000000000000], [4680000000000, 0])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1305000000000], [3870000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([0, 0], [1710000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3,
      2)) (.next ([-1710000000000, -9000000000000], [5985000000000, 0]) (some (0, 3, 2)) (some (0,
      3, 2)) (.next ([-4680000000000], [9855000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([-4680000000000, 0], [8145000000000, -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-3870000000000], [5175000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_9 : ExcludedOn (model9.B 9 ++ [step9.q]) 9000000000000 (model9.caps 9) (model9.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked9 : StepValid model9 9000000000000 step9 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded9_0
    · exact excluded9_1
    · exact excluded9_2
    · exact excluded9_3
    · exact (hj rfl).elim
    · exact excluded9_5
    · exact excluded9_6
    · exact excluded9_7
    · exact excluded9_8
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_0 : ExcludedOn (model10.B 0 ++ [step10.q]) 9000000000000 (model10.caps 0)
    (model10.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6810000000000], [135000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([6810000000000], [195000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      (.next ([6000000000000], [375000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([6060000000000], [510000000000]) (some (7, 8, 4)) (some (7, 8, 5)) (.next ([6060000000000],
      [570000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([1320000000000], [195000000000])
      (some (7, 8, 5)) (some (7, 8, 5)) (.next ([570000000000], [375000000000]) (some (7, 8, 5))
      (some (7, 8, 5)) (.next ([5820000000000], [4425000000000]) (some (7, 8, 5)) (some (7, 8, 5))
      (.next ([5685000000000], [4620000000000]) (some (7, 8, 5)) (some (7, 8, 5))
      fan10Owner0Part1)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_9 : ExcludedOn (model10.B 9 ++ [step10.q]) 9000000000000 (model10.caps 9)
    (model10.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked10 : StepValid model10 9000000000000 step10 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded10_0
    · exact excluded10_1
    · exact excluded10_2
    · exact excluded10_3
    · exact (hj rfl).elim
    · exact excluded10_5
    · exact excluded10_6
    · exact excluded10_7
    · exact excluded10_8
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_0 : ExcludedOn (model11.B 0 ++ [step11.q]) 9000000000000 (model11.caps 0)
    (model11.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6810000000000], [135000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([6810000000000], [195000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      (.next ([6000000000000], [375000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([6060000000000], [510000000000]) (some (7, 8, 4)) (some (7, 8, 5)) (.next ([6060000000000],
      [570000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([1320000000000], [195000000000])
      (some (7, 8, 5)) (some (7, 8, 5)) (.next ([570000000000], [375000000000]) (some (7, 8, 5))
      (some (7, 8, 5)) (.next ([489000000000, -2400000000000], [342000000000, 4800000000000]) (some
      (7, 8, 5)) (some (7, 8, 5)) (.next ([5445000000000], [4800000000000]) (some (7, 8, 5)) (some
      (7, 8, 5)) (.next ([5310000000000], [4995000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next
      ([5250000000000], [5055000000000]) (some (7, 8, 5)) (some (7, 8, 5))
      fan11Owner0Part1)))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_3 : ExcludedOn (model11.B 3 ++ [step11.q]) 9000000000000 (model11.caps 3)
    (model11.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5130000000000, 0], [3165000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([5130000000000], [4875000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1710000000000, 9000000000000], [1710000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3420000000000, -9000000000000],
      [6585000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [1710000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-3165000000000,
      9000000000000], [8295000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 2, 3)) (.next
      ([-4875000000000], [10005000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-1710000000000, -9000000000000], [3420000000000, 18000000000000]) (some (0, 2, 3)) (some (0,
      2, 3)) (.next ([-6585000000000, -9000000000000], [10005000000000]) (some (0, 2, 3)) (some (0,
      2, 3)) (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_8 : ExcludedOn (model11.B 8 ++ [step11.q]) 9000000000000 (model11.caps 8)
    (model11.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_9 : ExcludedOn (model11.B 9 ++ [step11.q]) 9000000000000 (model11.caps 9)
    (model11.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked11 : StepValid model11 9000000000000 step11 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded11_0
    · exact excluded11_1
    · exact excluded11_2
    · exact excluded11_3
    · exact (hj rfl).elim
    · exact excluded11_5
    · exact excluded11_6
    · exact excluded11_7
    · exact excluded11_8
    · exact excluded11_9
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_0 : ExcludedOn (model12.B 0 ++ [step12.q]) 9000000000000 (model12.caps 0)
    (model12.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6810000000000], [135000000000]) (some (7, 8, 4))
      (some (7, 8, 4)) (.next ([6810000000000], [195000000000]) (some (7, 8, 4)) (some (7, 8, 4))
      (.next ([6000000000000], [375000000000]) (some (7, 8, 4)) (some (7, 8, 4)) (.next
      ([6060000000000], [510000000000]) (some (7, 8, 4)) (some (7, 8, 5)) (.next ([6060000000000],
      [570000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([1320000000000], [195000000000])
      (some (7, 8, 5)) (some (7, 8, 5)) (.next ([570000000000], [375000000000]) (some (7, 8, 5))
      (some (7, 8, 5)) (.next ([489000000000, -2400000000000], [342000000000, 4800000000000]) (some
      (7, 8, 5)) (some (7, 8, 5)) (.next ([945000000000], [945000000000]) (some (7, 8, 5)) (some (7,
      8, 5)) (.next ([5070000000000], [5235000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next
      ([4935000000000], [5430000000000]) (some (7, 8, 5)) (some (7, 8, 5))
      fan12Owner0Part1)))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_3 : ExcludedOn (model12.B 3 ++ [step12.q]) 9000000000000 (model12.caps 3)
    (model12.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5070000000000, 0], [2790000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([5070000000000], [4500000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1710000000000, 9000000000000], [1710000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([3360000000000, -9000000000000],
      [6210000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [1710000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-2790000000000,
      9000000000000], [7860000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 2, 3)) (.next
      ([-4500000000000], [9570000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1710000000000,
      -9000000000000], [3420000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-6210000000000, -9000000000000], [9570000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_8 : ExcludedOn (model12.B 8 ++ [step12.q]) 9000000000000 (model12.caps 8)
    (model12.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_9 : ExcludedOn (model12.B 9 ++ [step12.q]) 9000000000000 (model12.caps 9)
    (model12.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked12 : StepValid model12 9000000000000 step12 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded12_0
    · exact excluded12_1
    · exact excluded12_2
    · exact excluded12_3
    · exact (hj rfl).elim
    · exact excluded12_5
    · exact excluded12_6
    · exact excluded12_7
    · exact excluded12_8
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_0 : ExcludedOn (model13.B 0 ++ [step13.q]) 9000000000000 (model13.caps 0)
    (model13.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6810000000000], [135000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([6810000000000], [195000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([6000000000000], [375000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([6060000000000], [510000000000]) (some (8, 1, 4)) (some (8, 1, 5)) (.next ([6060000000000],
      [570000000000]) (some (8, 1, 5)) (some (8, 1, 5)) (.next ([1320000000000], [195000000000])
      (some (8, 1, 5)) (some (8, 1, 5)) (.next ([5400000000000], [2475000000000]) (some (8, 1, 5))
      (some (8, 1, 5)) (.next ([5742000000000, 4800000000000], [2964000000000, -2400000000000])
      (some (8, 1, 5)) (some (8, 1, 5)) (.next ([2445000000000], [1545000000000]) (some (8, 1, 5))
      (some (8, 1, 5)) fan13Owner0Part1)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_6 : ExcludedOn (model13.B 6 ++ [step13.q]) 9000000000000 (model13.caps 6)
    (model13.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_7 : ExcludedOn (model13.B 7 ++ [step13.q]) 9000000000000 (model13.caps 7)
    (model13.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_8 : ExcludedOn (model13.B 8 ++ [step13.q]) 9000000000000 (model13.caps 8)
    (model13.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_9 : ExcludedOn (model13.B 9 ++ [step13.q]) 9000000000000 (model13.caps 9)
    (model13.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked13 : StepValid model13 9000000000000 step13 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded13_0
    · exact excluded13_1
    · exact excluded13_2
    · exact (hj rfl).elim
    · exact excluded13_4
    · exact excluded13_5
    · exact excluded13_6
    · exact excluded13_7
    · exact excluded13_8
    · exact excluded13_9
theorem next13 : model13.insert step13 = model14 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded14_0 : ExcludedOn (model14.B 0 ++ [step14.q]) 9000000000000 (model14.caps 0)
    (model14.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_3 : ExcludedOn (model14.B 3 ++ [step14.q]) 9000000000000 (model14.caps 3)
    (model14.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3255000000000], [390000000000]) (some (7, 0, 2))
      (some (7, 1, 2)) (.next ([4500000000000], [570000000000]) (some (7, 1, 2)) (some (7, 1, 2))
      (.next ([2820000000000], [450000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next
      ([2445000000000], [450000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([4125000000000],
      [1005000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([3750000000000], [1380000000000])
      (some (7, 1, 2)) (some (7, 1, 2)) (.next ([2970000000000, -9000000000000], [1710000000000,
      9000000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([2790000000000, -9000000000000],
      [2280000000000, 9000000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([1710000000000,
      9000000000000], [1710000000000, 9000000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next
      ([2415000000000, -9000000000000], [2715000000000, 9000000000000]) (some (7, 1, 2)) (some (7,
      1, 2)) (.next ([4110000000000], [5070000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next
      ([3675000000000], [5130000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([3300000000000],
      [5130000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([855000000000], [2115000000000,
      -9000000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([1140000000000, 9000000000000],
      [3360000000000, -9000000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([855000000000],
      [3825000000000]) (some (7, 1, 2)) (some (7, 1, 2)) (.next ([855000000000], [4680000000000])
      (some (7, 1, 2)) (some (7, 1, 2)) fan14Owner4Part0)))))))))))))))))) (den := 9000000000000)
      (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_7 : ExcludedOn (model14.B 7 ++ [step14.q]) 9000000000000 (model14.caps 7)
    (model14.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_9 : ExcludedOn (model14.B 9 ++ [step14.q]) 9000000000000 (model14.caps 9)
    (model14.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked14 : StepValid model14 9000000000000 step14 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded14_0
    · exact excluded14_1
    · exact excluded14_2
    · exact excluded14_3
    · exact excluded14_4
    · exact excluded14_5
    · exact excluded14_6
    · exact excluded14_7
    · exact (hj rfl).elim
    · exact excluded14_9
theorem next14 : model14.insert step14 = model15 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded15_0 : ExcludedOn (model15.B 0 ++ [step15.q]) 9000000000000 (model15.caps 0)
    (model15.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_1 : ExcludedOn (model15.B 1 ++ [step15.q]) 9000000000000 (model15.caps 1)
    (model15.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_2 : ExcludedOn (model15.B 2 ++ [step15.q]) 9000000000000 (model15.caps 2)
    (model15.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_3 : ExcludedOn (model15.B 3 ++ [step15.q]) 9000000000000 (model15.caps 3)
    (model15.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3255000000000], [390000000000]) (some (5, 0, 7))
      (some (5, 7, 7)) (.next ([4500000000000], [570000000000]) (some (5, 7, 7)) (some (5, 7, 7))
      (.next ([5070000000000], [765000000000]) (some (5, 7, 7)) (some (5, 7, 7)) (.next
      ([2820000000000], [450000000000]) (some (5, 7, 2)) (some (5, 7, 2)) (.next ([2445000000000],
      [450000000000]) (some (5, 7, 2)) (some (5, 7, 2)) (.next ([5130000000000], [1140000000000])
      (some (5, 7, 2)) (some (5, 7, 2)) (.next ([4125000000000], [1005000000000]) (some (5, 7, 2))
      (some (5, 7, 2)) (.next ([5130000000000], [1515000000000]) (some (5, 7, 2)) (some (5, 7, 2))
      (.next ([3750000000000], [1380000000000]) (some (5, 7, 2)) (some (5, 7, 2)) (.next
      ([2790000000000, -9000000000000], [2280000000000, 9000000000000]) (some (5, 7, 2)) (some (5,
      7, 2)) (.next ([4680000000000], [4410000000000]) (some (5, 7, 2)) (some (5, 7, 2)) (.next
      ([1710000000000, 9000000000000], [1710000000000, 9000000000000]) (some (5, 7, 2)) (some (5, 7,
      2)) (.next ([2415000000000, -9000000000000], [2715000000000, 9000000000000]) (some (5, 7, 2))
      (some (5, 7, 2)) (.next ([2040000000000, -9000000000000], [3090000000000, 9000000000000])
      (some (5, 7, 2)) (some (5, 7, 2)) (.next ([855000000000], [2115000000000, -9000000000000])
      (some (5, 7, 2)) (some (5, 7, 2)) (.next ([1140000000000, 9000000000000], [3360000000000,
      -9000000000000]) (some (5, 7, 2)) (some (6, 7, 2)) (.next ([1710000000000, 9000000000000],
      [5265000000000]) (some (6, 7, 2)) (some (6, 7, 2)) (.next ([855000000000], [3825000000000])
      (some (6, 7, 2)) (some (6, 7, 2)) (.next ([60000000000], [375000000000]) (some (6, 7, 2))
      (some (6, 7, 2)) fan15Owner4Part0)))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_7 : ExcludedOn (model15.B 7 ++ [step15.q]) 9000000000000 (model15.caps 7)
    (model15.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_8 : ExcludedOn (model15.B 8 ++ [step15.q]) 9000000000000 (model15.caps 8)
    (model15.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded15_9 : ExcludedOn (model15.B 9 ++ [step15.q]) 9000000000000 (model15.caps 9)
    (model15.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked15 : StepValid model15 9000000000000 step15 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded15_0
    · exact excluded15_1
    · exact excluded15_2
    · exact excluded15_3
    · exact excluded15_4
    · exact (hj rfl).elim
    · exact excluded15_6
    · exact excluded15_7
    · exact excluded15_8
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint190000200000
end ConwaySoifer.Simplified.Certificates
