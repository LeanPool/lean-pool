/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext190000200000
import Mathlib.Tactic.FinCases

/-!
# Sext 190000 200000 5

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
def fan40Owner3Part0 : FanWitness := (.next ([2280000000000], [4920000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([1710000000000, 9000000000000], [5670000000000]) (some (5, 6, 3)) (some
    (5, 6, 4)) (.next ([1155000000000], [5100000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([180000000000], [945000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([585000000000,
    9000000000000], [5850000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([375000000000],
    [4725000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0], [5670000000000]) (some (5, 6,
    4)) (some (5, 6, 4)) (.next ([-570000000000], [5295000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-720000000000], [6540000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1290000000000, 9000000000000], [7290000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1125000000000], [5850000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-435000000000],
    [1875000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3000000000000], [7290000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1380000000000], [3000000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-2190000000000], [3915000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2445000000000], [4350000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-3015000000000, 9000000000000], [5100000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-1530000000000], [2280000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4920000000000],
    [7200000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-5670000000000, 0], [7380000000000,
    9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-5100000000000], [6255000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-945000000000], [1125000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-5850000000000, 0], [6435000000000, 9000000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-4725000000000], [5100000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.terminal (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner3Part0 : FanWitness := (.next ([2745000000000], [5850000000000]) (some (5, 0, 6))
    (some (5, 0, 6)) (.next ([2280000000000], [4920000000000]) (some (5, 0, 6)) (some (5, 0, 6))
    (.next ([1710000000000, 9000000000000], [5670000000000]) (some (5, 0, 6)) (some (5, 0, 6))
    (.next ([1155000000000], [5100000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
    ([180000000000], [945000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([585000000000,
    9000000000000], [5850000000000]) (some (5, 0, 6)) (some (5, 1, 6)) (.next ([375000000000],
    [4725000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0], [5670000000000]) (some (5, 1,
    6)) (some (5, 1, 6)) (.next ([-570000000000], [5295000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-855000000000], [5100000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-750000000000], [4350000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1125000000000],
    [5850000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-750000000000], [2340000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2445000000000], [4350000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-3015000000000, 9000000000000], [5100000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-5670000000000], [9540000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-1530000000000], [2280000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-5850000000000], [8595000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4920000000000],
    [7200000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-5670000000000, 0], [7380000000000,
    9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-5100000000000], [6255000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-945000000000], [1125000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-5850000000000, 0], [6435000000000, 9000000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-4725000000000], [5100000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.terminal (some (0, 2, 6)) (some (0, 2, 4)) (some (0, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner2Part0 : FanWitness := (.next ([3420000000000], [1152000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([2565000000000], [949500000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([4290000000000], [1710000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([2268000000000, 9000000000000], [1710000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([5130000000000, 9000000000000], [4290000000000, -9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([2862000000000], [2580000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([3420000000000], [6000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1710000000000, 9000000000000], [5130000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([855000000000, 9000000000000], [4927500000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([558000000000], [3420000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0],
    [5130000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-652500000000], [5145000000000])
    (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-855000000000], [4927500000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-202500000000], [1057500000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-1152000000000], [4572000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-949500000000], [3514500000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1710000000000],
    [6000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1710000000000, 9000000000000],
    [3978000000000, 0]) (some (0, 5, 4)) (some (5, 5, 4)) (.next ([-4290000000000, 9000000000000],
    [9420000000000, 0]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-2580000000000], [5442000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-6000000000000], [9420000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.next ([-5130000000000, 0], [6840000000000, 9000000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.next ([-4927500000000, 0], [5782500000000, 9000000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.next ([-3420000000000], [3978000000000]) (some (5, 3, 4)) (some (5, 3, 4))
    (.terminal (some (5, 3, 4)) (some (5, 3, 0)) (some (5, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner4Part0 : FanWitness := (.next ([5580000000000], [1290000000000, -9000000000000]) (some
    (5, 1, 2)) (some (5, 1, 5)) (.next ([4710000000000], [2040000000000]) (some (4, 1, 5)) (some (4,
    1, 5)) (.next ([2580000000000], [1290000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([5580000000000], [3000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([3000000000000],
    [1710000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1788000000000], [1212000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1788000000000, 9000000000000], [4212000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1710000000000, 9000000000000],
    [5040000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([960000000000], [4962000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([540000000000], [8040000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([0, 9000000000000], [3000000000000, -9000000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([0], [5040000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([-420000000000], [3078000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1290000000000,
    9000000000000], [6870000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-2040000000000], [6750000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1290000000000],
    [3870000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3000000000000], [8580000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1710000000000], [4710000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-1212000000000], [3000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-4212000000000, 9000000000000], [6000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-5040000000000], [6750000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-4962000000000], [5922000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-8040000000000], [8580000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-3000000000000,
    9000000000000], [3000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5))
    (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner0Part0 : FanWitness := (.next ([-2865000000000], [8670000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([-765000000000], [2295000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([-945000000000], [2670000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
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
    (.next ([-1350000000000], [1725000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-2280000000000], [2910000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-4410000000000], [5550000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-945000000000],
    [1140000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-4035000000000], [4800000000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1320000000000], [1515000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-6060000000000], [6630000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-6000000000000], [6375000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-6810000000000], [7005000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.terminal (some (10, 3,
    6)) (some (10, 3, 6)) (some (10, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner0Part1 : FanWitness := (.next ([195000000000], [1320000000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([570000000000], [6060000000000]) (some (10, 3, 4)) (some (10, 3, 4))
    (.next ([375000000000], [6000000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([195000000000], [6810000000000]) (some (10, 3, 4)) (some (10, 3, 5)) (.next ([0],
    [195000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-195000000000], [6945000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-375000000000], [7200000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([-570000000000], [7140000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([-585000000000], [5760000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([-750000000000], [7380000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-945000000000],
    [7380000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-195000000000], [1515000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-945000000000], [7320000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([-1140000000000], [7320000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([-195000000000], [1140000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([-570000000000], [3240000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-1320000000000],
    [7005000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-375000000000], [1725000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-1515000000000], [6945000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([-60000000000], [255000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([-570000000000], [1920000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([-2670000000000], [8730000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-180000000000],
    [570000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-945000000000], [2865000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) fan43Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner0Part2 : FanWitness := (.next ([1350000000000], [570000000000]) (some (7, 2, 3)) (some
    (7, 2, 4)) (.next ([6060000000000], [2670000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
    ([390000000000], [180000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([1920000000000],
    [945000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([5805000000000], [2865000000000])
    (some (7, 2, 4)) (some (7, 2, 4)) (.next ([1530000000000], [765000000000]) (some (7, 2, 4))
    (some (7, 2, 4)) (.next ([1725000000000], [945000000000]) (some (7, 2, 4)) (some (7, 2, 4))
    (.next ([570000000000], [375000000000]) (some (7, 2, 4)) (some (10, 2, 4)) (.next
    ([195000000000], [180000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([375000000000],
    [375000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([180000000000], [195000000000])
    (some (10, 2, 4)) (some (10, 2, 4)) (.next ([2655000000000], [3090000000000]) (some (10, 2, 4))
    (some (10, 2, 4)) (.next ([375000000000], [570000000000]) (some (10, 2, 4)) (some (10, 2, 4))
    (.next ([2280000000000], [3840000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
    ([2085000000000], [4035000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([180000000000],
    [390000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([885000000000], [2085000000000])
    (some (10, 2, 4)) (some (10, 2, 4)) (.next ([1710000000000], [4230000000000]) (some (10, 2, 4))
    (some (10, 3, 4)) (.next ([1335000000000], [4410000000000]) (some (10, 3, 4)) (some (10, 3, 4))
    (.next ([375000000000], [1350000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([630000000000], [2280000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([1140000000000],
    [4410000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([195000000000], [945000000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([765000000000], [4035000000000]) (some (10, 3, 4))
    (some (10, 3, 4)) fan43Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner3Part0 : FanWitness := (.next ([180000000000], [945000000000]) (some (5, 6, 4)) (some
    (5, 6, 4)) (.next ([585000000000, 9000000000000], [5850000000000]) (some (5, 6, 4)) (some (5, 6,
    4)) (.next ([420000000000], [5580000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([330000000000], [5250000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([150000000000],
    [4305000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0], [5670000000000]) (some (5, 6,
    4)) (some (5, 6, 4)) (.next ([-1125000000000], [5850000000000]) (some (0, 6, 4)) (some (0, 6,
    4)) (.next ([-1125000000000], [3000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-2430000000000], [5580000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3375000000000],
    [6705000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4425000000000], [8250000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4995000000000, 9000000000000], [9000000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3300000000000], [5250000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3870000000000, 9000000000000], [6000000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-1530000000000], [2280000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-4920000000000], [7200000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-6705000000000], [9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5670000000000,
    0], [7380000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5100000000000],
    [6255000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-945000000000], [1125000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5850000000000, 0], [6435000000000, 9000000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5580000000000], [6000000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-5250000000000], [5580000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-4305000000000], [4455000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.terminal (some
    (0, 6, 4)) (some (0, 6, 4)) (some (0, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner5Part0 : FanWitness := (.next ([900000000000], [480000000000]) (some (4, 1, 2)) (some
    (4, 1, 2)) (.next ([1665000000000], [1560000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
    ([3165000000000], [4125000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2460000000000],
    [5355000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([750000000000], [1710000000000])
    (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1185000000000], [2940000000000]) (some (4, 1, 2))
    (some (4, 1, 2)) (.next ([1560000000000], [4875000000000]) (some (4, 1, 2)) (some (4, 1, 5))
    (.next ([1710000000000, 9000000000000], [6105000000000, 0]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([810000000000, 9000000000000], [5625000000000, 0]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([0, 9000000000000], [750000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([0, 0], [1710000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-900000000000], [5625000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-1665000000000],
    [6540000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2415000000000, 9000000000000],
    [7290000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-480000000000], [1380000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1560000000000], [3225000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4125000000000], [7290000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-5355000000000], [7815000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1710000000000], [2460000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2940000000000],
    [4125000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4875000000000], [6435000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6105000000000, 0], [7815000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5625000000000, 0], [6435000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-750000000000, 9000000000000], [750000000000, 0])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan46Owner5Part0 : FanWitness := (.next ([1665000000000], [810000000000]) (some (4, 1, 2)) (some
    (4, 1, 2)) (.next ([900000000000], [480000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
    ([3915000000000], [3375000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1185000000000],
    [2190000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2460000000000], [5355000000000])
    (some (4, 1, 2)) (some (4, 1, 5)) (.next ([750000000000], [1710000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([1560000000000], [4875000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([1710000000000, 9000000000000], [6105000000000, 0]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([810000000000, 9000000000000], [5625000000000, 0]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([0, 9000000000000], [750000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([0, 0], [1710000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-915000000000], [6540000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-900000000000],
    [5625000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1665000000000, 9000000000000],
    [7290000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-810000000000], [2475000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-480000000000], [1380000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-3375000000000], [7290000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-2190000000000], [3375000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-5355000000000], [7815000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1710000000000],
    [2460000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4875000000000], [6435000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6105000000000, 0], [7815000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5625000000000, 0], [6435000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-750000000000, 9000000000000], [750000000000, 0])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4725000000000], [570000000000]) (some (4, 0, 2))
      (some (5, 0, 2)) (.next ([5820000000000], [720000000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([6000000000000, 9000000000000], [1290000000000, -9000000000000]) (some (5, 0, 2))
      (some (5, 0, 2)) (.next ([4725000000000], [1125000000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([1440000000000], [435000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next
      ([4290000000000], [3000000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next ([1620000000000],
      [1380000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next ([1725000000000], [2190000000000])
      (some (5, 0, 2)) (some (5, 6, 2)) (.next ([1905000000000], [2445000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([2085000000000, 9000000000000], [3015000000000, -9000000000000])
      (some (5, 6, 2)) (some (5, 6, 3)) (.next ([750000000000], [1530000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) fan40Owner3Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4725000000000], [570000000000]) (some (4, 0, 2))
      (some (5, 0, 2)) (.next ([4245000000000], [855000000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([3600000000000], [750000000000]) (some (5, 0, 2)) (some (5, 0, 6)) (.next
      ([4725000000000], [1125000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1590000000000],
      [750000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1905000000000], [2445000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([2085000000000, 9000000000000], [3015000000000,
      -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3870000000000], [5670000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([750000000000], [1530000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) fan41Owner3Part0)))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_4 : ExcludedOn (model41.B 4 ++ [step41.q]) 9000000000000 (model41.caps 4)
    (model41.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_7 : ExcludedOn (model41.B 7 ++ [step41.q]) 9000000000000 (model41.caps 7)
    (model41.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_8 : ExcludedOn (model41.B 8 ++ [step41.q]) 9000000000000 (model41.caps 8)
    (model41.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded41_3
    · exact excluded41_4
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
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4492500000000], [652500000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([4072500000000], [855000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([855000000000], [202500000000]) (some (0, 5, 3)) (some (0, 5, 3)) fan42Owner2Part0))))
      (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2658000000000], [420000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan42Owner4Part0)) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100
      (by decide +kernel)
  decide +kernel

theorem excluded42_5 : ExcludedOn (model42.B 5 ++ [step42.q]) 9000000000000 (model42.caps 5)
    (model42.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_6 : ExcludedOn (model42.B 6 ++ [step42.q]) 9000000000000 (model42.caps 6)
    (model42.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_7 : ExcludedOn (model42.B 7 ++ [step42.q]) 9000000000000 (model42.caps 7)
    (model42.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_8 : ExcludedOn (model42.B 8 ++ [step42.q]) 9000000000000 (model42.caps 8)
    (model42.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded42_4
    · exact excluded42_5
    · exact excluded42_6
    · exact excluded42_7
    · exact excluded42_8
    · exact excluded42_9
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded43_0 : ExcludedOn (model43.B 0 ++ [step43.q]) 9000000000000 (model43.caps 0)
    (model43.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6750000000000], [195000000000]) (some (6, 10,
      3)) (some (7, 10, 3)) (.next ([6825000000000], [375000000000]) (some (7, 10, 3)) (some (7, 10,
      3)) (.next ([6570000000000], [570000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next
      ([5175000000000], [585000000000]) (some (7, 10, 3)) (some (7, 10, 3)) (.next ([6630000000000],
      [750000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([6435000000000], [945000000000])
      (some (7, 2, 3)) (some (7, 2, 3)) (.next ([1320000000000], [195000000000]) (some (7, 2, 3))
      (some (7, 2, 3)) (.next ([6375000000000], [945000000000]) (some (7, 2, 3)) (some (7, 2, 3))
      (.next ([6180000000000], [1140000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next
      ([945000000000], [195000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([2670000000000],
      [570000000000]) (some (7, 2, 3)) (some (7, 2, 3)) (.next ([5685000000000], [1320000000000])
      (some (7, 2, 3)) (some (7, 2, 3)) (.next ([1350000000000], [375000000000]) (some (7, 2, 3))
      (some (7, 2, 3)) (.next ([5430000000000], [1515000000000]) (some (7, 2, 3)) (some (7, 2, 3))
      (.next ([195000000000], [60000000000]) (some (7, 2, 3)) (some (7, 2, 3))
      fan43Owner0Part2))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_2 : ExcludedOn (model43.B 2 ++ [step43.q]) 9000000000000 (model43.caps 2)
    (model43.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_3 : ExcludedOn (model43.B 3 ++ [step43.q]) 9000000000000 (model43.caps 3)
    (model43.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4725000000000], [1125000000000]) (some (4, 0,
      6)) (some (5, 0, 6)) (.next ([1875000000000], [1125000000000]) (some (5, 0, 6)) (some (5, 0,
      6)) (.next ([3150000000000], [2430000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next
      ([3330000000000], [3375000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next ([3825000000000],
      [4425000000000]) (some (5, 0, 2)) (some (5, 6, 2)) (.next ([4005000000000, 9000000000000],
      [4995000000000, -9000000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([1950000000000],
      [3300000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([2130000000000, 9000000000000],
      [3870000000000, -9000000000000]) (some (5, 6, 2)) (some (5, 6, 3)) (.next ([750000000000],
      [1530000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2280000000000], [4920000000000])
      (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2295000000000], [6705000000000]) (some (5, 6, 3))
      (some (5, 6, 4)) (.next ([1710000000000, 9000000000000], [5670000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([1155000000000], [5100000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      fan43Owner3Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6705000000000, 0], [585000000000,
      -9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) (.next ([5955000000000], [585000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4725000000000], [900000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([6705000000000], [2295000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([900000000000], [480000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([2460000000000], [5355000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([750000000000],
      [1710000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1560000000000], [4875000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1710000000000, 9000000000000], [6105000000000, 0])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1080000000000], [7020000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([600000000000], [8400000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([0, 0], [1710000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 5)) (.next
      ([-585000000000, 9000000000000], [7290000000000, -9000000000000]) (some (5, 1, 5)) (some (5,
      2, 5)) (.next ([-585000000000], [6540000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-900000000000], [5625000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2295000000000],
      [9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-480000000000], [1380000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5355000000000], [7815000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-1710000000000], [2460000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-4875000000000], [6435000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-6105000000000, 0], [7815000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-7020000000000], [8100000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-8400000000000], [9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_6 : ExcludedOn (model43.B 6 ++ [step43.q]) 9000000000000 (model43.caps 6)
    (model43.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_7 : ExcludedOn (model43.B 7 ++ [step43.q]) 9000000000000 (model43.caps 7)
    (model43.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_8 : ExcludedOn (model43.B 8 ++ [step43.q]) 9000000000000 (model43.caps 8)
    (model43.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded43_3
    · exact (hj rfl).elim
    · exact excluded43_5
    · exact excluded43_6
    · exact excluded43_7
    · exact excluded43_8
    · exact excluded43_9
theorem next43 : model43.insert step43 = model44 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded44_0 : ExcludedOn (model44.B 0 ++ [step44.q]) 9000000000000 (model44.caps 0)
    (model44.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_1 : ExcludedOn (model44.B 1 ++ [step44.q]) 9000000000000 (model44.caps 1)
    (model44.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2118000000000, -9000000000000], [960000000000,
      9000000000000]) (some (4, 4, 1)) (some (4, 4, 2)) (.next ([6210000000000, 9000000000000],
      [3420000000000, -9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([1710000000000,
      9000000000000], [1710000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([4500000000000], [5130000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2790000000000,
      -9000000000000], [5130000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([750000000000],
      [3078000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [1710000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-960000000000, -9000000000000],
      [3078000000000, 0]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([-3420000000000, 9000000000000],
      [9630000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-1710000000000, -9000000000000],
      [3420000000000, 18000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-5130000000000],
      [9630000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-5130000000000, 0],
      [7920000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-3078000000000],
      [3828000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.terminal (some (4, 1, 4)) (some (4, 1,
      4)) (some (4, 1, 4))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_3 : ExcludedOn (model44.B 3 ++ [step44.q]) 9000000000000 (model44.caps 3)
    (model44.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_7 : ExcludedOn (model44.B 7 ++ [step44.q]) 9000000000000 (model44.caps 7)
    (model44.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_8 : ExcludedOn (model44.B 8 ++ [step44.q]) 9000000000000 (model44.caps 8)
    (model44.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded44_0
    · exact excluded44_1
    · exact (hj rfl).elim
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

theorem excluded45_1 : ExcludedOn (model45.B 1 ++ [step45.q]) 9000000000000 (model45.caps 1)
    (model45.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_2 : ExcludedOn (model45.B 2 ++ [step45.q]) 9000000000000 (model45.caps 2)
    (model45.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_3 : ExcludedOn (model45.B 3 ++ [step45.q]) 9000000000000 (model45.caps 3)
    (model45.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_4 : ExcludedOn (model45.B 4 ++ [step45.q]) 9000000000000 (model45.caps 4)
    (model45.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_5 : ExcludedOn (model45.B 5 ++ [step45.q]) 9000000000000 (model45.caps 5)
    (model45.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4725000000000], [900000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([4875000000000], [1665000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([4875000000000, 9000000000000], [2415000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) fan45Owner5Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_6 : ExcludedOn (model45.B 6 ++ [step45.q]) 9000000000000 (model45.caps 6)
    (model45.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [1710000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([5835000000000], [3165000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([1710000000000, 9000000000000], [7290000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 9000000000000], [4125000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1710000000000, 9000000000000]) (some (3, 0,
      2)) (some (3, 0, 2)) (.next ([-1710000000000], [5835000000000]) (some (3, 0, 2)) (some (3, 1,
      2)) (.next ([-3165000000000, 9000000000000], [9000000000000, -9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-7290000000000, 9000000000000], [9000000000000, 0]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-4125000000000, 9000000000000], [4125000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_7 : ExcludedOn (model45.B 7 ++ [step45.q]) 9000000000000 (model45.caps 7)
    (model45.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_8 : ExcludedOn (model45.B 8 ++ [step45.q]) 9000000000000 (model45.caps 8)
    (model45.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded45_1
    · exact excluded45_2
    · exact excluded45_3
    · exact excluded45_4
    · exact excluded45_5
    · exact excluded45_6
    · exact excluded45_7
    · exact excluded45_8
    · exact excluded45_9
theorem next45 : model45.insert step45 = model46 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded46_1 : ExcludedOn (model46.B 1 ++ [step46.q]) 9000000000000 (model46.caps 1)
    (model46.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_2 : ExcludedOn (model46.B 2 ++ [step46.q]) 9000000000000 (model46.caps 2)
    (model46.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_3 : ExcludedOn (model46.B 3 ++ [step46.q]) 9000000000000 (model46.caps 3)
    (model46.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_4 : ExcludedOn (model46.B 4 ++ [step46.q]) 9000000000000 (model46.caps 4)
    (model46.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_5 : ExcludedOn (model46.B 5 ++ [step46.q]) 9000000000000 (model46.caps 5)
    (model46.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [915000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([4725000000000], [900000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5625000000000, 9000000000000], [1665000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) fan46Owner5Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_6 : ExcludedOn (model46.B 6 ++ [step46.q]) 9000000000000 (model46.caps 6)
    (model46.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [1710000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([5085000000000], [3915000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([1710000000000, 9000000000000], [7290000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 9000000000000], [3375000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1710000000000, 9000000000000]) (some (3, 0,
      2)) (some (3, 0, 2)) (.next ([-1710000000000], [5085000000000]) (some (3, 0, 2)) (some (3, 1,
      2)) (.next ([-3915000000000, 9000000000000], [9000000000000, -9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-7290000000000, 9000000000000], [9000000000000, 0]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-3375000000000, 9000000000000], [3375000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded46_7 : ExcludedOn (model46.B 7 ++ [step46.q]) 9000000000000 (model46.caps 7)
    (model46.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded46_8 : ExcludedOn (model46.B 8 ++ [step46.q]) 9000000000000 (model46.caps 8)
    (model46.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded47_0 : ExcludedOn (model47.B 0 ++ [step47.q]) 9000000000000 (model47.caps 0)
    (model47.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 11) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_1 : ExcludedOn (model47.B 1 ++ [step47.q]) 9000000000000 (model47.caps 1)
    (model47.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6498000000000], [1002000000000]) (some (4, 0,
      1)) (some (4, 0, 2)) (.next ([2118000000000, -9000000000000], [960000000000, 9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([3420000000000, 0], [3120000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 1, 2)) (.next ([5130000000000, 9000000000000], [4830000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1710000000000, 9000000000000], [1710000000000,
      9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3420000000000], [4830000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([750000000000], [3078000000000]) (some (4, 1, 2))
      (some (4, 1, 4)) (.next ([0], [1710000000000, 9000000000000]) (some (4, 1, 4)) (some (4, 1,
      4)) (.next ([-1002000000000], [7500000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next
      ([-960000000000, -9000000000000], [3078000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-3120000000000, 9000000000000], [6540000000000, -9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([-4830000000000], [9960000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-1710000000000, -9000000000000], [3420000000000, 18000000000000]) (some (0, 1,
      4)) (some (0, 1, 4)) (.next ([-4830000000000], [8250000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-3078000000000], [3828000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal
      (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_2 : ExcludedOn (model47.B 2 ++ [step47.q]) 9000000000000 (model47.caps 2)
    (model47.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2460000000000, -9000000000000], [960000000000,
      9000000000000]) (some (0, 0, 4)) (some (0, 1, 4)) (.next ([4800000000000], [3750000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([2340000000000, 9000000000000], [2790000000000,
      -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1710000000000, 9000000000000],
      [5130000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([750000000000], [3420000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([630000000000], [4500000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([750000000000], [8550000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([0], [4500000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-960000000000,
      -9000000000000], [3420000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-3750000000000], [8550000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2790000000000,
      9000000000000], [5130000000000, 0]) (some (0, 1, 4)) (some (0, 4, 4)) (.next ([-5130000000000,
      0], [6840000000000, 9000000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next
      ([-3420000000000], [4170000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next
      ([-4500000000000], [5130000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-8550000000000], [9300000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded47_3 : ExcludedOn (model47.B 3 ++ [step47.q]) 9000000000000 (model47.caps 3)
    (model47.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_4 : ExcludedOn (model47.B 4 ++ [step47.q]) 9000000000000 (model47.caps 4)
    (model47.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_5 : ExcludedOn (model47.B 5 ++ [step47.q]) 9000000000000 (model47.caps 5)
    (model47.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_6 : ExcludedOn (model47.B 6 ++ [step47.q]) 9000000000000 (model47.caps 6)
    (model47.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_8 : ExcludedOn (model47.B 8 ++ [step47.q]) 9000000000000 (model47.caps 8)
    (model47.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded47_9 : ExcludedOn (model47.B 9 ++ [step47.q]) 9000000000000 (model47.caps 9)
    (model47.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked47 : StepValid model47 9000000000000 step47 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded47_0
    · exact excluded47_1
    · exact excluded47_2
    · exact excluded47_3
    · exact excluded47_4
    · exact excluded47_5
    · exact excluded47_6
    · exact (hj rfl).elim
    · exact excluded47_8
    · exact excluded47_9
theorem next47 : model47.insert step47 = model48 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext190000200000
end ConwaySoifer.Simplified.Certificates
