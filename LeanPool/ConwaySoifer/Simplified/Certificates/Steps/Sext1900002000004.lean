/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext190000200000
import Mathlib.Tactic.FinCases

/-!
# Sext 190000 200000 4

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
namespace Sext190000200000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner3Part0 : FanWitness := (.next ([855000000000], [4072500000000]) (some (5, 0, 6)) (some
    (5, 0, 6)) (.next ([630000000000], [4500000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
    ([427500000000], [4275000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([375000000000],
    [4725000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([202500000000], [4245000000000])
    (some (5, 0, 6)) (some (5, 0, 6)) (.next ([105000000000], [2542500000000]) (some (5, 0, 6))
    (some (5, 0, 6)) (.next ([0], [4500000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
    ([-30000000000], [4755000000000]) (some (0, 0, 6)) (some (0, 1, 6)) (.next ([-30000000000],
    [255000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-4275000000000], [9202500000000])
    (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-2220000000000], [4380000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-2790000000000, 9000000000000], [5130000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-2445000000000], [4350000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-3015000000000, 9000000000000], [5100000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-4380000000000], [6660000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1530000000000], [2280000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2362500000000,
    9000000000000], [3217500000000, -9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-5130000000000, 0], [6840000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-4072500000000], [4927500000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4500000000000],
    [5130000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4275000000000], [4702500000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4725000000000], [5100000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-4245000000000], [4447500000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-2542500000000], [2647500000000]) (some (0, 2, 4)) (some (0, 6, 4)) (.terminal (some
    (0, 6, 4)) (some (0, 6, 4)) (some (0, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part0 : FanWitness := (.next ([-180000000000], [570000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([-3453000000000], [9435000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([-3648000000000], [9375000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([-375000000000], [945000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-180000000000],
    [375000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-375000000000], [750000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-195000000000], [375000000000]) (some (10, 3, 5))
    (some (10, 3, 6)) (.next ([-3090000000000], [5745000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-570000000000], [945000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-3840000000000], [6120000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-4035000000000], [6120000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-390000000000],
    [570000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-2085000000000], [2970000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-4230000000000], [5940000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-4410000000000], [5745000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-2280000000000], [2910000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-4410000000000], [5550000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-945000000000],
    [1140000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-4035000000000], [4800000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1320000000000], [1515000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-2133000000000], [2430000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-6060000000000], [6630000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-6000000000000], [6375000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-6810000000000], [7005000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.terminal (some (10, 3,
    6)) (some (10, 3, 6)) (some (10, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part1 : FanWitness := (.next ([297000000000], [2133000000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([570000000000], [6060000000000]) (some (10, 3, 4)) (some (10, 3, 4))
    (.next ([375000000000], [6000000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([195000000000], [6810000000000]) (some (10, 3, 4)) (some (10, 3, 5)) (.next ([0],
    [195000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-195000000000], [6945000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-375000000000], [7200000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([-570000000000], [7140000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([-750000000000], [7380000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([-945000000000], [7380000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-195000000000],
    [1515000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-945000000000], [7320000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-1140000000000], [7320000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([-648000000000], [4023000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([-195000000000], [1140000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([-453000000000], [2508000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-1320000000000],
    [7005000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-1368000000000], [6465000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-1515000000000], [6945000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([-60000000000], [255000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([-648000000000], [2703000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([-843000000000], [3078000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-1023000000000],
    [3648000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-1023000000000], [3453000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) fan33Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part2 : FanWitness := (.next ([2055000000000], [648000000000]) (some (7, 2, 3)) (some
    (7, 2, 4)) (.next ([2235000000000], [843000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
    ([2625000000000], [1023000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([2430000000000],
    [1023000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([390000000000], [180000000000]) (some
    (7, 2, 4)) (some (10, 2, 4)) (.next ([5982000000000], [3453000000000]) (some (10, 2, 4)) (some
    (10, 2, 4)) (.next ([5727000000000], [3648000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
    ([570000000000], [375000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([195000000000],
    [180000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([375000000000], [375000000000])
    (some (10, 2, 4)) (some (10, 2, 4)) (.next ([180000000000], [195000000000]) (some (10, 2, 4))
    (some (10, 2, 4)) (.next ([2655000000000], [3090000000000]) (some (10, 2, 4)) (some (10, 2, 4))
    (.next ([375000000000], [570000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
    ([2280000000000], [3840000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([2085000000000],
    [4035000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([180000000000], [390000000000])
    (some (10, 2, 4)) (some (10, 2, 4)) (.next ([885000000000], [2085000000000]) (some (10, 2, 4))
    (some (10, 2, 4)) (.next ([1710000000000], [4230000000000]) (some (10, 2, 4)) (some (10, 3, 4))
    (.next ([1335000000000], [4410000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([630000000000], [2280000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([1140000000000],
    [4410000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([195000000000], [945000000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([765000000000], [4035000000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([195000000000], [1320000000000]) (some (10, 3, 4)) (some (10, 3, 4))
    fan33Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner3Part0 : FanWitness := (.next ([2280000000000], [4380000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([3078000000000], [6000000000000]) (some (5, 6, 3)) (some (5, 6, 3))
    (.next ([750000000000], [1530000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
    ([1710000000000, 9000000000000], [5130000000000]) (some (5, 6, 3)) (some (5, 6, 4)) (.next
    ([630000000000], [4500000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([375000000000],
    [4725000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0], [4500000000000]) (some (5, 6,
    4)) (some (5, 6, 4)) (.next ([-30000000000], [4755000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-30000000000], [255000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1275000000000], [3978000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2052000000000],
    [6000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1500000000000], [3948000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3720000000000], [8328000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-4290000000000, 9000000000000], [9078000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-2220000000000], [4380000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2790000000000, 9000000000000], [5130000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2445000000000], [4350000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-3015000000000, 9000000000000], [5100000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-4380000000000], [6660000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6000000000000],
    [9078000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1530000000000], [2280000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5130000000000, 0], [6840000000000, 9000000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4500000000000], [5130000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-4725000000000], [5100000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.terminal (some (0, 6, 4)) (some (0, 6, 4)) (some (0, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner0Part0 : FanWitness := (.next ([-195000000000], [375000000000]) (some (10, 3, 5))
    (some (10, 3, 6)) (.next ([-3090000000000], [5745000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-570000000000], [945000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-3840000000000], [6120000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-4035000000000], [6120000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-390000000000],
    [570000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-2085000000000], [2970000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-4230000000000], [5940000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-4410000000000], [5745000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-7110000000000], [9195000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-2280000000000], [2910000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-4410000000000], [5550000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-945000000000],
    [1140000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-4035000000000], [4800000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-6165000000000], [7305000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-7485000000000], [8820000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-7485000000000], [8625000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1320000000000], [1515000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-7305000000000], [8250000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-6915000000000], [7680000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-7110000000000], [7875000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-6060000000000], [6630000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-6000000000000], [6375000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-6810000000000], [7005000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.terminal (some (10, 3,
    6)) (some (10, 3, 6)) (some (10, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner0Part1 : FanWitness := (.next ([765000000000], [7110000000000]) (some (9, 10, 4))
    (some (9, 10, 4)) (.next ([570000000000], [6060000000000]) (some (9, 10, 4)) (some (10, 10, 4))
    (.next ([375000000000], [6000000000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next
    ([195000000000], [6810000000000]) (some (10, 10, 4)) (some (10, 10, 5)) (.next ([0],
    [195000000000]) (some (10, 10, 5)) (some (10, 10, 5)) (.next ([-195000000000], [6945000000000])
    (some (10, 10, 5)) (some (10, 10, 5)) (.next ([-375000000000], [7200000000000]) (some (10, 10,
    5)) (some (10, 10, 5)) (.next ([-480000000000], [8625000000000]) (some (10, 10, 5)) (some (10,
    10, 5)) (.next ([-570000000000], [7140000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([-735000000000], [8820000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-750000000000],
    [7380000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-945000000000], [7380000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-195000000000], [1515000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([-945000000000], [7320000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([-1140000000000], [7320000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([-195000000000], [1140000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-1320000000000],
    [7005000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-1365000000000], [6540000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-1515000000000], [6945000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([-60000000000], [255000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([-180000000000], [570000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([-375000000000], [945000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-180000000000],
    [375000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-375000000000], [750000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) fan34Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner0Part2 : FanWitness := (.next ([390000000000], [180000000000]) (some (7, 10, 3)) (some
    (7, 10, 4)) (.next ([570000000000], [375000000000]) (some (7, 10, 4)) (some (7, 10, 4)) (.next
    ([195000000000], [180000000000]) (some (7, 10, 4)) (some (7, 10, 4)) (.next ([375000000000],
    [375000000000]) (some (7, 10, 4)) (some (8, 10, 4)) (.next ([180000000000], [195000000000])
    (some (8, 10, 4)) (some (8, 10, 4)) (.next ([2655000000000], [3090000000000]) (some (8, 10, 4))
    (some (9, 10, 4)) (.next ([375000000000], [570000000000]) (some (9, 10, 4)) (some (9, 10, 4))
    (.next ([2280000000000], [3840000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next
    ([2085000000000], [4035000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([180000000000],
    [390000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([885000000000], [2085000000000])
    (some (9, 10, 4)) (some (9, 10, 4)) (.next ([1710000000000], [4230000000000]) (some (9, 10, 4))
    (some (9, 10, 4)) (.next ([1335000000000], [4410000000000]) (some (9, 10, 4)) (some (9, 10, 4))
    (.next ([2085000000000], [7110000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next
    ([630000000000], [2280000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([1140000000000],
    [4410000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([195000000000], [945000000000])
    (some (9, 10, 4)) (some (9, 10, 4)) (.next ([765000000000], [4035000000000]) (some (9, 10, 4))
    (some (9, 10, 4)) (.next ([1140000000000], [6165000000000]) (some (9, 10, 4)) (some (9, 10, 4))
    (.next ([1335000000000], [7485000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next
    ([1140000000000], [7485000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([195000000000],
    [1320000000000]) (some (9, 10, 4)) (some (9, 10, 4)) (.next ([945000000000], [7305000000000])
    (some (9, 10, 4)) (some (9, 10, 4)) (.next ([765000000000], [6915000000000]) (some (9, 10, 4))
    (some (9, 10, 4)) fan34Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner0Part0 : FanWitness := (.next ([-375000000000], [945000000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([-180000000000], [375000000000]) (some (0, 3, 10)) (some (0, 3, 10))
    (.next ([-375000000000], [750000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-195000000000], [375000000000]) (some (0, 3, 10)) (some (1, 3, 10)) (.next ([-3090000000000],
    [5745000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-570000000000], [945000000000])
    (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-3840000000000], [6120000000000]) (some (1, 3, 10))
    (some (1, 3, 10)) (.next ([-4035000000000], [6120000000000]) (some (1, 3, 10)) (some (1, 3, 10))
    (.next ([-390000000000], [570000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-2085000000000], [2970000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-4230000000000], [5940000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-4410000000000], [5745000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-5925000000000], [7632000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-2280000000000], [2910000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-4410000000000], [5550000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-945000000000],
    [1140000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-4035000000000], [4800000000000])
    (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-1320000000000], [1515000000000]) (some (1, 3, 10))
    (some (2, 3, 10)) (.next ([-6060000000000], [6630000000000]) (some (2, 3, 10)) (some (2, 3, 10))
    (.next ([-6000000000000], [6375000000000]) (some (2, 3, 10)) (some (2, 3, 10)) (.next
    ([-5352000000000], [5547000000000]) (some (2, 3, 10)) (some (2, 3, 10)) (.next
    ([-5547000000000], [5742000000000]) (some (2, 3, 6)) (some (2, 3, 6)) (.next ([-6810000000000],
    [7005000000000]) (some (2, 3, 6)) (some (2, 3, 6)) (.next ([-5922000000000], [5937000000000])
    (some (2, 3, 6)) (some (2, 3, 6)) (.terminal (some (2, 3, 6)) (some (2, 3, 6)) (some (2, 3,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner0Part1 : FanWitness := (.next ([195000000000], [5352000000000]) (some (9, 3, 10))
    (some (9, 3, 10)) (.next ([195000000000], [5547000000000]) (some (9, 3, 10)) (some (9, 3, 10))
    (.next ([195000000000], [6810000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next
    ([15000000000], [5922000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([0],
    [195000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([-195000000000], [6945000000000])
    (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-180000000000], [6297000000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([-180000000000], [4977000000000]) (some (0, 3, 10)) (some (0, 3, 10))
    (.next ([-375000000000], [7200000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-375000000000], [6492000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-570000000000],
    [7140000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-750000000000], [7380000000000])
    (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-945000000000], [7380000000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([-195000000000], [1515000000000]) (some (0, 3, 10)) (some (0, 3, 10))
    (.next ([-945000000000], [7320000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-1140000000000], [7320000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-1125000000000], [6867000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-195000000000],
    [1140000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-1203000000000], [6555000000000])
    (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-1263000000000], [6810000000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([-1320000000000], [7005000000000]) (some (0, 3, 10)) (some (0, 3, 10))
    (.next ([-1515000000000], [6945000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-60000000000], [255000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-180000000000],
    [570000000000]) (some (0, 3, 10)) (some (0, 3, 10)) fan35Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner0Part2 : FanWitness := (.next ([5685000000000], [1320000000000]) (some (7, 2, 3))
    (some (7, 2, 10)) (.next ([5430000000000], [1515000000000]) (some (7, 2, 10)) (some (7, 2, 10))
    (.next ([195000000000], [60000000000]) (some (7, 2, 10)) (some (7, 2, 10)) (.next
    ([390000000000], [180000000000]) (some (7, 2, 10)) (some (7, 2, 10)) (.next ([570000000000],
    [375000000000]) (some (7, 2, 10)) (some (7, 2, 10)) (.next ([195000000000], [180000000000])
    (some (7, 2, 10)) (some (7, 2, 10)) (.next ([375000000000], [375000000000]) (some (7, 2, 10))
    (some (8, 2, 10)) (.next ([180000000000], [195000000000]) (some (8, 2, 10)) (some (8, 2, 10))
    (.next ([2655000000000], [3090000000000]) (some (8, 2, 10)) (some (9, 2, 10)) (.next
    ([375000000000], [570000000000]) (some (9, 2, 10)) (some (9, 2, 10)) (.next ([2280000000000],
    [3840000000000]) (some (9, 2, 10)) (some (9, 2, 10)) (.next ([2085000000000], [4035000000000])
    (some (9, 2, 10)) (some (9, 2, 10)) (.next ([180000000000], [390000000000]) (some (9, 2, 10))
    (some (9, 2, 10)) (.next ([885000000000], [2085000000000]) (some (9, 2, 10)) (some (9, 2, 10))
    (.next ([1710000000000], [4230000000000]) (some (9, 2, 10)) (some (9, 3, 10)) (.next
    ([1335000000000], [4410000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([1707000000000],
    [5925000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([630000000000], [2280000000000])
    (some (9, 3, 10)) (some (9, 3, 10)) (.next ([1140000000000], [4410000000000]) (some (9, 3, 10))
    (some (9, 3, 10)) (.next ([195000000000], [945000000000]) (some (9, 3, 10)) (some (9, 3, 10))
    (.next ([765000000000], [4035000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next
    ([195000000000], [1320000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([570000000000],
    [6060000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([375000000000], [6000000000000])
    (some (9, 3, 10)) (some (9, 3, 10)) fan35Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner2Part0 : FanWitness := (.next ([4072500000000], [855000000000]) (some (0, 1, 5)) (some
    (0, 1, 5)) (.next ([7395000000000], [1849500000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([2565000000000], [949500000000]) (some (0, 1, 5)) (some (0, 5, 5)) (.next ([577500000000],
    [277500000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([2268000000000, 9000000000000],
    [1710000000000, -9000000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([3078000000000, 0],
    [3462000000000, -9000000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.next ([3078000000000],
    [5172000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1710000000000, 9000000000000],
    [4350000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([855000000000, 9000000000000],
    [4927500000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([558000000000], [3420000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0], [4350000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-372000000000], [3792000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next
    ([-1272000000000], [9522000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-900000000000],
    [5730000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-855000000000], [4927500000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1849500000000], [9244500000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-949500000000], [3514500000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-277500000000], [855000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-1710000000000, 9000000000000], [3978000000000, 0]) (some (0, 5, 4)) (some (1, 5, 4)) (.next
    ([-3462000000000, 9000000000000], [6540000000000, -9000000000000]) (some (1, 5, 4)) (some (1, 5,
    4)) (.next ([-5172000000000], [8250000000000]) (some (1, 5, 4)) (some (1, 5, 4)) (.next
    ([-4350000000000, 0], [6060000000000, 9000000000000]) (some (1, 5, 4)) (some (1, 5, 4)) (.next
    ([-4927500000000, 0], [5782500000000, 9000000000000]) (some (1, 5, 4)) (some (1, 5, 4)) (.next
    ([-3420000000000], [3978000000000]) (some (1, 5, 4)) (some (1, 5, 4)) (.terminal (some (1, 5,
    4)) (some (1, 5, 0)) (some (1, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner3Part0 : FanWitness := (.next ([1905000000000], [2445000000000]) (some (6, 0, 2))
    (some (6, 0, 2)) (.next ([2085000000000, 9000000000000], [3015000000000, -9000000000000]) (some
    (6, 0, 2)) (some (6, 0, 3)) (.next ([2280000000000], [4380000000000]) (some (6, 0, 3)) (some (6,
    0, 3)) (.next ([750000000000], [1530000000000]) (some (6, 0, 3)) (some (6, 0, 3)) (.next
    ([1710000000000, 9000000000000], [5130000000000]) (some (6, 0, 3)) (some (6, 0, 4)) (.next
    ([630000000000], [4500000000000]) (some (6, 0, 4)) (some (6, 0, 4)) (.next ([375000000000],
    [4725000000000]) (some (6, 0, 4)) (some (6, 0, 4)) (.next ([0], [4500000000000]) (some (6, 0,
    4)) (some (6, 0, 4)) (.next ([-30000000000], [4755000000000]) (some (6, 0, 4)) (some (6, 1, 4))
    (.next ([-150000000000], [4710000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([-30000000000], [255000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-900000000000, 0],
    [4890000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 2, 4)) (.next ([-900000000000],
    [3180000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-2550000000000], [6780000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-2805000000000], [7005000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-2220000000000], [4380000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-2790000000000, 9000000000000], [5130000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-2445000000000], [4350000000000]) (some (6, 2, 4)) (some (0, 2, 4)) (.next
    ([-3015000000000, 9000000000000], [5100000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-4380000000000], [6660000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1530000000000],
    [2280000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-5130000000000, 0], [6840000000000,
    9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4500000000000], [5130000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4725000000000], [5100000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2,
    4)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4725000000000], [30000000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([225000000000], [30000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([4927500000000], [4275000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([2160000000000], [2220000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([2340000000000,
      9000000000000], [2790000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([1905000000000], [2445000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([2085000000000,
      9000000000000], [3015000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([2280000000000], [4380000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([750000000000],
      [1530000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([855000000000, 0], [2362500000000,
      -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1710000000000, 9000000000000],
      [5130000000000]) (some (5, 0, 6)) (some (5, 0, 6)) fan32Owner3Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded32_3
    · exact excluded32_4
    · exact excluded32_5
    · exact excluded32_6
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6750000000000], [195000000000]) (some (6, 10,
      3)) (some (7, 10, 3)) (.next ([6825000000000], [375000000000]) (some (7, 10, 3)) (some (7, 10,
      3)) (.next ([6570000000000], [570000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next
      ([6630000000000], [750000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next ([6435000000000],
      [945000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next ([1320000000000], [195000000000])
      (some (7, 10, 3)) (some (7, 10, 3)) (.next ([6375000000000], [945000000000]) (some (7, 10, 3))
      (some (7, 10, 3)) (.next ([6180000000000], [1140000000000]) (some (7, 10, 3)) (some (7, 10,
      3)) (.next ([3375000000000], [648000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next
      ([945000000000], [195000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next ([2055000000000],
      [453000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next ([5685000000000], [1320000000000])
      (some (7, 10, 3)) (some (7, 10, 3)) (.next ([5097000000000], [1368000000000]) (some (7, 10,
      3)) (some (7, 10, 3)) (.next ([5430000000000], [1515000000000]) (some (7, 2, 3)) (some (7, 2,
      3)) (.next ([195000000000], [60000000000]) (some (7, 2, 3)) (some (7, 2, 3))
      fan33Owner0Part2))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4725000000000], [30000000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([225000000000], [30000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([2703000000000], [1275000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([3948000000000], [2052000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next ([2448000000000],
      [1500000000000]) (some (5, 0, 2)) (some (5, 6, 2)) (.next ([4608000000000], [3720000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([4788000000000, 9000000000000], [4290000000000,
      -9000000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([2160000000000], [2220000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([2340000000000, 9000000000000], [2790000000000,
      -9000000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([1905000000000], [2445000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([2085000000000, 9000000000000], [3015000000000,
      -9000000000000]) (some (5, 6, 2)) (some (5, 6, 3)) fan33Owner3Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6750000000000], [195000000000]) (some (6, 10,
      3)) (some (7, 10, 3)) (.next ([6825000000000], [375000000000]) (some (7, 10, 3)) (some (7, 10,
      3)) (.next ([8145000000000], [480000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next
      ([6570000000000], [570000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next ([8085000000000],
      [735000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next ([6630000000000], [750000000000])
      (some (7, 10, 3)) (some (7, 10, 3)) (.next ([6435000000000], [945000000000]) (some (7, 10, 3))
      (some (7, 10, 3)) (.next ([1320000000000], [195000000000]) (some (7, 10, 3)) (some (7, 10, 3))
      (.next ([6375000000000], [945000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next
      ([6180000000000], [1140000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next ([945000000000],
      [195000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next ([5685000000000], [1320000000000])
      (some (7, 10, 3)) (some (7, 10, 3)) (.next ([5175000000000], [1365000000000]) (some (7, 10,
      3)) (some (7, 10, 3)) (.next ([5430000000000], [1515000000000]) (some (7, 10, 3)) (some (7,
      10, 3)) (.next ([195000000000], [60000000000]) (some (7, 10, 3)) (some (7, 10, 3))
      fan34Owner0Part2))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6540000000000], [750000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([5172000000000], [1290000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([1500000000000], [750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([1788000000000, 9000000000000], [4212000000000, -9000000000000]) (some (3, 1, 2)) (some (3,
      4, 2)) (.next ([1710000000000, 9000000000000], [5040000000000]) (some (3, 4, 2)) (some (3, 4,
      2)) (.next ([960000000000], [4962000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([960000000000, 9000000000000], [7290000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([78000000000], [5922000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [5040000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-750000000000], [7290000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1290000000000], [6462000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-750000000000], [2250000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-4212000000000, 9000000000000], [6000000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-5040000000000], [6750000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 3))
      (.next ([-4962000000000], [5922000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-7290000000000], [8250000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-5922000000000], [6000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded34_4
    · exact (hj rfl).elim
    · exact excluded34_6
    · exact excluded34_7
    · exact excluded34_8
    · exact excluded34_9
theorem next34 : model34.insert step34 = model35 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded35_0 : ExcludedOn (model35.B 0 ++ [step35.q]) 9000000000000 (model35.caps 0)
    (model35.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6750000000000], [195000000000]) (some (6, 2, 3))
      (some (7, 2, 3)) (.next ([6117000000000], [180000000000]) (some (7, 2, 3)) (some (7, 2, 3))
      (.next ([4797000000000], [180000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next
      ([6825000000000], [375000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([6117000000000],
      [375000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([6570000000000], [570000000000])
      (some (7, 2, 3)) (some (7, 2, 3)) (.next ([6630000000000], [750000000000]) (some (7, 2, 3))
      (some (7, 2, 3)) (.next ([6435000000000], [945000000000]) (some (7, 2, 3)) (some (7, 2, 3))
      (.next ([1320000000000], [195000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next
      ([6375000000000], [945000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([6180000000000],
      [1140000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([5742000000000], [1125000000000])
      (some (7, 2, 3)) (some (7, 2, 3)) (.next ([945000000000], [195000000000]) (some (7, 2, 3))
      (some (7, 2, 3)) (.next ([5352000000000], [1203000000000]) (some (7, 2, 3)) (some (7, 2, 3))
      (.next ([5547000000000], [1263000000000]) (some (7, 2, 3)) (some (7, 2, 3))
      fan35Owner0Part2))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3420000000000], [372000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([8250000000000], [1272000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([4830000000000], [900000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      fan35Owner2Part0)))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7632000000000, 9000000000000], [2118000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2460000000000, 9000000000000],
      [1368000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([5922000000000],
      [3828000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1710000000000, 9000000000000],
      [7290000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [1710000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-2118000000000,
      9000000000000], [9750000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1368000000000,
      9000000000000], [3828000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3828000000000],
      [9750000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-7290000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1,
      3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded35_2
    · exact excluded35_3
    · exact excluded35_4
    · exact excluded35_5
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1665000000000, -9000000000000], [1710000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([3453000000000], [5922000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1788000000000, 9000000000000], [4212000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1710000000000, 9000000000000],
      [5040000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([960000000000], [4962000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([78000000000], [5922000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([0], [5040000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-1710000000000, -9000000000000], [3375000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-5922000000000], [9375000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-4212000000000,
      9000000000000], [6000000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next ([-5040000000000],
      [6750000000000, 9000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-4962000000000],
      [5922000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-5922000000000], [6000000000000])
      (some (4, 1, 4)) (some (4, 2, 4)) (.terminal (some (4, 2, 4)) (some (0, 2, 4)) (some (4, 2,
      4))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked36 : StepValid model36 9000000000000 step36 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded36_0
    · exact excluded36_1
    · exact excluded36_2
    · exact excluded36_3
    · exact excluded36_4
    · exact excluded36_5
    · exact excluded36_6
    · exact excluded36_7
    · exact (hj rfl).elim
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4725000000000], [30000000000]) (some (4, 0, 2))
      (some (5, 0, 2)) (.next ([4560000000000], [150000000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([225000000000], [30000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next
      ([3990000000000, 9000000000000], [900000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next
      ([2280000000000], [900000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next ([4230000000000],
      [2550000000000]) (some (5, 0, 2)) (some (6, 0, 2)) (.next ([4200000000000], [2805000000000])
      (some (6, 0, 2)) (some (6, 0, 2)) (.next ([2160000000000], [2220000000000]) (some (6, 0, 2))
      (some (6, 0, 2)) (.next ([2340000000000, 9000000000000], [2790000000000, -9000000000000])
      (some (6, 0, 2)) (some (6, 0, 2)) fan37Owner3Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded37_5
    · exact excluded37_6
    · exact excluded37_7
    · exact (hj rfl).elim
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded38_0 : ExcludedOn (model38.B 0 ++ [step38.q]) 9000000000000 (model38.caps 0)
    (model38.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3408000000000], [2592000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([3330000000000], [5040000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([1788000000000, 9000000000000], [4212000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1710000000000, 9000000000000], [5040000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([960000000000], [4962000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([78000000000], [5922000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [5040000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-2592000000000], [6000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5040000000000], [8370000000000]) (some (0, 1, 2))
      (some (0, 1, 4)) (.next ([-4212000000000, 9000000000000], [6000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5040000000000], [6750000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-4962000000000], [5922000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-5922000000000], [6000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_8 : ExcludedOn (model38.B 8 ++ [step38.q]) 9000000000000 (model38.caps 8)
    (model38.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4410000000000], [1215000000000]) (some (0, 0,
      4)) (some (0, 1, 4)) (.next ([5670000000000], [3330000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([2490000000000], [2280000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([900000000000], [1410000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1080000000000],
      [4590000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1095000000000], [4725000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([900000000000], [5820000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([45000000000], [3330000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([0], [5625000000000]) (some (0, 1, 2)) (some (0, 4, 2)) (.next ([-1215000000000],
      [5625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3330000000000], [9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2280000000000], [4770000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-1410000000000], [2310000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([-4590000000000], [5670000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next
      ([-4725000000000], [5820000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-5820000000000], [6720000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3330000000000], [3375000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_9 : ExcludedOn (model38.B 9 ++ [step38.q]) 9000000000000 (model38.caps 9)
    (model38.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked38 : StepValid model38 9000000000000 step38 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded38_0
    · exact excluded38_1
    · exact excluded38_2
    · exact (hj rfl).elim
    · exact excluded38_4
    · exact excluded38_5
    · exact excluded38_6
    · exact excluded38_7
    · exact excluded38_8
    · exact excluded38_9
theorem next38 : model38.insert step38 = model39 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded39_0 : ExcludedOn (model39.B 0 ++ [step39.q]) 9000000000000 (model39.caps 0)
    (model39.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3228000000000], [1647000000000]) (some (4, 0,
      2)) (some (4, 1, 2)) (.next ([4275000000000], [3915000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([1125000000000], [1440000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([1788000000000, 9000000000000], [4212000000000, -9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1125000000000], [3150000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1710000000000, 9000000000000], [5040000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([960000000000], [4962000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([78000000000], [5922000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [5040000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1647000000000], [4875000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3915000000000], [8190000000000]) (some (0, 1, 2))
      (some (0, 1, 4)) (.next ([-1440000000000, 9000000000000], [2565000000000, -9000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-4212000000000, 9000000000000], [6000000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3150000000000], [4275000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5040000000000], [6750000000000, 9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-4962000000000], [5922000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-5922000000000], [6000000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_8 : ExcludedOn (model39.B 8 ++ [step39.q]) 9000000000000 (model39.caps 8)
    (model39.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4410000000000], [1215000000000]) (some (0, 0,
      4)) (some (0, 1, 4)) (.next ([5850000000000], [4275000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([900000000000], [1410000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([1545000000000], [3405000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1095000000000],
      [4725000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([900000000000], [5820000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([225000000000], [4275000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([135000000000], [5715000000000]) (some (0, 1, 2)) (some (0, 4, 2))
      (.next ([0], [5625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1215000000000],
      [5625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4275000000000], [10125000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1410000000000], [2310000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-3405000000000], [4950000000000]) (some (0, 4, 2)) (some (0, 4, 3))
      (.next ([-4725000000000], [5820000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-5820000000000], [6720000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-4275000000000], [4500000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-5715000000000], [5850000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_9 : ExcludedOn (model39.B 9 ++ [step39.q]) 9000000000000 (model39.caps 9)
    (model39.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked39 : StepValid model39 9000000000000 step39 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded39_0
    · exact excluded39_1
    · exact excluded39_2
    · exact (hj rfl).elim
    · exact excluded39_4
    · exact excluded39_5
    · exact excluded39_6
    · exact excluded39_7
    · exact excluded39_8
    · exact excluded39_9
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext190000200000
end ConwaySoifer.Simplified.Certificates
