/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext320000330000
import Mathlib.Tactic.FinCases

/-!
# Sext 320000 330000 2

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
namespace Sext320000330000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part0 : FanWitness := (.next ([-90000000000], [285000000000]) (some (9, 5, 7)) (some
    (9, 5, 7)) (.next ([-2400000000000], [6585000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next
    ([-165000000000], [375000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-1380000000000],
    [2880000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-4620000000000], [9495000000000])
    (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-4695000000000], [9585000000000]) (some (9, 5, 7))
    (some (9, 5, 7)) (.next ([-4530000000000], [9210000000000]) (some (9, 5, 7)) (some (9, 5, 7))
    (.next ([-690000000000], [1380000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next
    ([-5295000000000], [10170000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-750000000000],
    [1440000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-4125000000000], [5370000000000])
    (some (9, 5, 7)) (some (9, 5, 8)) (.next ([-4185000000000], [5430000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-4410000000000], [5565000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.next ([-4470000000000], [5625000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-765000000000], [960000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-4500000000000],
    [5580000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-2895000000000], [3585000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-4560000000000], [5640000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-75000000000], [90000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next
    ([-5085000000000], [5565000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5145000000000],
    [5625000000000]) (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5625000000000], [6120000000000])
    (some (9, 5, 8)) (some (9, 5, 8)) (.next ([-5910000000000], [6315000000000]) (some (9, 5, 8))
    (some (9, 5, 8)) (.next ([-6000000000000], [6330000000000]) (some (9, 5, 8)) (some (9, 5, 8))
    (.terminal (some (9, 5, 8)) (some (9, 5, 8)) (some (9, 5, 8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part1 : FanWitness := (.next ([1080000000000], [4500000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([690000000000], [2895000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([1080000000000], [4560000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([15000000000], [75000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([480000000000],
    [5085000000000]) (some (9, 3, 5)) (some (9, 4, 5)) (.next ([480000000000], [5145000000000])
    (some (9, 4, 5)) (some (9, 4, 6)) (.next ([495000000000], [5625000000000]) (some (9, 4, 6))
    (some (9, 4, 6)) (.next ([405000000000], [5910000000000]) (some (9, 4, 6)) (some (9, 4, 6))
    (.next ([330000000000], [6000000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([0],
    [2190000000000]) (some (9, 4, 6)) (some (9, 4, 6)) (.next ([-15000000000], [600000000000]) (some
    (9, 4, 6)) (some (9, 4, 7)) (.next ([-60000000000], [2190000000000]) (some (9, 4, 7)) (some (9,
    5, 7)) (.next ([-270000000000], [6585000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next
    ([-690000000000], [5775000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-750000000000],
    [5775000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-945000000000], [6315000000000])
    (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-1035000000000], [6600000000000]) (some (9, 5, 7))
    (some (9, 5, 7)) (.next ([-1110000000000], [6690000000000]) (some (9, 5, 7)) (some (9, 5, 7))
    (.next ([-690000000000], [3585000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next
    ([-1710000000000], [7275000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-1440000000000],
    [5025000000000]) (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-1635000000000], [5625000000000])
    (some (9, 5, 7)) (some (9, 5, 7)) (.next ([-1725000000000], [5910000000000]) (some (9, 5, 7))
    (some (9, 5, 7)) (.next ([-1800000000000], [6000000000000]) (some (9, 5, 7)) (some (9, 5, 7))
    fan18Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part2 : FanWitness := (.next ([5370000000000], [945000000000]) (some (8, 9, 5)) (some
    (8, 9, 5)) (.next ([5565000000000], [1035000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
    ([5580000000000], [1110000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([2895000000000],
    [690000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([5565000000000], [1710000000000])
    (some (8, 9, 5)) (some (8, 9, 5)) (.next ([3585000000000], [1440000000000]) (some (8, 9, 5))
    (some (8, 9, 5)) (.next ([3990000000000], [1635000000000]) (some (8, 9, 5)) (some (9, 9, 5))
    (.next ([4185000000000], [1725000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next
    ([4200000000000], [1800000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next ([195000000000],
    [90000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next ([4185000000000], [2400000000000]) (some
    (9, 9, 5)) (some (9, 9, 5)) (.next ([210000000000], [165000000000]) (some (9, 9, 5)) (some (9,
    9, 5)) (.next ([1500000000000], [1380000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next
    ([4875000000000], [4620000000000]) (some (9, 9, 5)) (some (9, 9, 5)) (.next ([4890000000000],
    [4695000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([4680000000000], [4530000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([690000000000], [690000000000]) (some (9, 3, 5)) (some
    (9, 3, 5)) (.next ([4875000000000], [5295000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([690000000000], [750000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1245000000000],
    [4125000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1245000000000], [4185000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1155000000000], [4410000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([1155000000000], [4470000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([195000000000], [765000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    fan18Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner0Part0 : FanWitness := (.next ([-2400000000000], [6585000000000]) (some (0, 5, 9))
    (some (0, 5, 9)) (.next ([-165000000000], [375000000000]) (some (0, 5, 9)) (some (0, 5, 9))
    (.next ([-1380000000000], [2880000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next
    ([-690000000000], [1380000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-750000000000],
    [1440000000000]) (some (0, 5, 9)) (some (1, 5, 9)) (.next ([-2685000000000], [4125000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-2745000000000], [4185000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-6870000000000], [9555000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-7155000000000], [9750000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-7245000000000], [9765000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4125000000000],
    [5370000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4185000000000], [5430000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4410000000000], [5565000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-4470000000000], [5625000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-765000000000], [960000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-7830000000000], [9750000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4500000000000],
    [5580000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4560000000000], [5640000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-75000000000], [90000000000]) (some (1, 5, 9)) (some
    (1, 5, 9)) (.next ([-5085000000000], [5565000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-5145000000000], [5625000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5625000000000],
    [6120000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5910000000000], [6315000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-6000000000000], [6330000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.terminal (some (1, 5, 9)) (some (1, 5, 9)) (some (1, 5,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner0Part1 : FanWitness := (.next ([1920000000000], [7830000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([1080000000000], [4500000000000]) (some (9, 3, 5)) (some (9, 3, 9))
    (.next ([1080000000000], [4560000000000]) (some (9, 3, 9)) (some (9, 3, 9)) (.next
    ([15000000000], [75000000000]) (some (9, 3, 9)) (some (9, 3, 9)) (.next ([480000000000],
    [5085000000000]) (some (9, 3, 9)) (some (9, 4, 9)) (.next ([480000000000], [5145000000000])
    (some (9, 4, 9)) (some (9, 4, 9)) (.next ([495000000000], [5625000000000]) (some (9, 4, 9))
    (some (9, 4, 9)) (.next ([405000000000], [5910000000000]) (some (9, 4, 9)) (some (9, 4, 9))
    (.next ([330000000000], [6000000000000]) (some (9, 4, 9)) (some (9, 4, 9)) (.next ([0],
    [2190000000000]) (some (9, 4, 9)) (some (9, 4, 9)) (.next ([-15000000000], [600000000000]) (some
    (9, 4, 9)) (some (9, 4, 9)) (.next ([-60000000000], [2190000000000]) (some (9, 4, 9)) (some (9,
    5, 9)) (.next ([-270000000000], [6585000000000]) (some (9, 5, 9)) (some (9, 5, 9)) (.next
    ([-555000000000], [4185000000000]) (some (9, 5, 9)) (some (9, 5, 9)) (.next ([-945000000000],
    [6315000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-1035000000000], [6600000000000])
    (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-1110000000000], [6690000000000]) (some (0, 5, 9))
    (some (0, 5, 9)) (.next ([-1245000000000], [5565000000000]) (some (0, 5, 9)) (some (0, 5, 9))
    (.next ([-1710000000000], [7275000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next
    ([-1635000000000], [5625000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-1725000000000],
    [5910000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-1800000000000], [6000000000000])
    (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-90000000000], [285000000000]) (some (0, 5, 9)) (some
    (0, 5, 9)) (.next ([-1245000000000], [3435000000000]) (some (0, 5, 9)) (some (0, 5, 9))
    fan21Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner0Part2 : FanWitness := (.next ([5565000000000], [1035000000000]) (some (9, 1, 5))
    (some (9, 1, 5)) (.next ([5580000000000], [1110000000000]) (some (9, 1, 5)) (some (9, 1, 5))
    (.next ([4320000000000], [1245000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next
    ([5565000000000], [1710000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([3990000000000],
    [1635000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([4185000000000], [1725000000000])
    (some (9, 1, 5)) (some (9, 2, 5)) (.next ([4200000000000], [1800000000000]) (some (9, 2, 5))
    (some (9, 2, 5)) (.next ([195000000000], [90000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next
    ([2190000000000], [1245000000000]) (some (9, 2, 5)) (some (9, 3, 5)) (.next ([4185000000000],
    [2400000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([210000000000], [165000000000]) (some
    (9, 3, 5)) (some (9, 3, 5)) (.next ([1500000000000], [1380000000000]) (some (9, 3, 5)) (some (9,
    3, 5)) (.next ([690000000000], [690000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([690000000000], [750000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1440000000000],
    [2685000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1440000000000], [2745000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([2685000000000], [6870000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([2595000000000], [7155000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([2520000000000], [7245000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([1245000000000], [4125000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1245000000000],
    [4185000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1155000000000], [4410000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1155000000000], [4470000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([195000000000], [765000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    fan21Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part0 : FanWitness := (.next ([-2400000000000], [6585000000000]) (some (0, 5, 9))
    (some (0, 5, 9)) (.next ([-165000000000], [375000000000]) (some (0, 5, 9)) (some (0, 5, 9))
    (.next ([-1380000000000], [2880000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next
    ([-690000000000], [1380000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-750000000000],
    [1440000000000]) (some (0, 5, 9)) (some (1, 5, 9)) (.next ([-5160000000000], [9840000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5445000000000], [10035000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-5535000000000], [10050000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-6120000000000], [10035000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-4125000000000], [5370000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4185000000000],
    [5430000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4410000000000], [5565000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4470000000000], [5625000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-765000000000], [960000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-4500000000000], [5580000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-4560000000000], [5640000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-75000000000],
    [90000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-3720000000000], [4185000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5085000000000], [5565000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-5145000000000], [5625000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-5625000000000], [6120000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-5850000000000], [6315000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5910000000000],
    [6315000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-6000000000000], [6330000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.terminal (some (1, 5, 9)) (some (1, 5, 9)) (some (1, 5,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part1 : FanWitness := (.next ([1080000000000], [4500000000000]) (some (0, 3, 9))
    (some (0, 3, 9)) (.next ([1080000000000], [4560000000000]) (some (0, 3, 9)) (some (0, 3, 9))
    (.next ([15000000000], [75000000000]) (some (0, 3, 9)) (some (0, 3, 9)) (.next ([465000000000],
    [3720000000000]) (some (0, 3, 9)) (some (0, 4, 9)) (.next ([480000000000], [5085000000000])
    (some (0, 4, 9)) (some (0, 4, 9)) (.next ([480000000000], [5145000000000]) (some (0, 4, 9))
    (some (0, 4, 9)) (.next ([495000000000], [5625000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    (.next ([465000000000], [5850000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next
    ([405000000000], [5910000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([330000000000],
    [6000000000000]) (some (0, 4, 9)) (some (0, 4, 9)) (.next ([0], [2190000000000]) (some (0, 4,
    9)) (some (0, 4, 9)) (.next ([-15000000000], [600000000000]) (some (0, 4, 9)) (some (0, 4, 9))
    (.next ([-60000000000], [2190000000000]) (some (0, 4, 9)) (some (0, 5, 9)) (.next
    ([-270000000000], [6585000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-945000000000],
    [6315000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-1035000000000], [6600000000000])
    (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-1110000000000], [6690000000000]) (some (0, 5, 9))
    (some (0, 5, 9)) (.next ([-975000000000], [4410000000000]) (some (0, 5, 9)) (some (0, 5, 9))
    (.next ([-1035000000000], [4470000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next
    ([-1710000000000], [7275000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-1635000000000],
    [5625000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-1725000000000], [5910000000000])
    (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-1800000000000], [6000000000000]) (some (0, 5, 9))
    (some (0, 5, 9)) (.next ([-90000000000], [285000000000]) (some (0, 5, 9)) (some (0, 5, 9))
    fan22Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part2 : FanWitness := (.next ([5370000000000], [945000000000]) (some (9, 1, 5)) (some
    (9, 1, 5)) (.next ([5565000000000], [1035000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next
    ([5580000000000], [1110000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([3435000000000],
    [975000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([3435000000000], [1035000000000])
    (some (9, 1, 5)) (some (9, 1, 5)) (.next ([5565000000000], [1710000000000]) (some (9, 1, 5))
    (some (9, 1, 5)) (.next ([3990000000000], [1635000000000]) (some (9, 1, 5)) (some (9, 1, 5))
    (.next ([4185000000000], [1725000000000]) (some (9, 1, 5)) (some (9, 2, 5)) (.next
    ([4200000000000], [1800000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([195000000000],
    [90000000000]) (some (9, 2, 5)) (some (9, 2, 5)) (.next ([4185000000000], [2400000000000]) (some
    (9, 2, 5)) (some (9, 3, 5)) (.next ([210000000000], [165000000000]) (some (9, 3, 5)) (some (9,
    3, 5)) (.next ([1500000000000], [1380000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([690000000000], [690000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([690000000000],
    [750000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([4680000000000], [5160000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([4590000000000], [5445000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([4515000000000], [5535000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([3915000000000], [6120000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([1245000000000], [4125000000000]) (some (9, 3, 5)) (some (9, 3, 9)) (.next ([1245000000000],
    [4185000000000]) (some (9, 3, 9)) (some (9, 3, 9)) (.next ([1155000000000], [4410000000000])
    (some (9, 3, 9)) (some (9, 3, 9)) (.next ([1155000000000], [4470000000000]) (some (9, 3, 9))
    (some (9, 3, 9)) (.next ([195000000000], [765000000000]) (some (0, 3, 9)) (some (0, 3, 9))
    fan22Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner4Part0 : FanWitness := (.next ([4635000000000], [4665000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([2880000000000, 9000000000000], [3495000000000]) (some (6, 1, 3)) (some
    (6, 1, 3)) (.next ([2250000000000], [2934000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([684000000000], [936000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1755000000000,
    -9000000000000], [2880000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([2385000000000], [6120000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1170000000000],
    [3495000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1701000000000], [5184000000000])
    (some (6, 1, 3)) (some (6, 1, 3)) (.next ([519000000000], [2415000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([375000000000], [5745000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([0], [3495000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([-1245000000000],
    [6429000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([-795000000000], [2250000000000])
    (some (6, 1, 3)) (some (6, 1, 3)) (.next ([-2250000000000], [6120000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([-4665000000000], [9300000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([-3495000000000], [6375000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([-2934000000000], [5184000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([-936000000000], [1620000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([-2880000000000,
    -9000000000000], [4635000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([-6120000000000],
    [8505000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-3495000000000], [4665000000000])
    (some (6, 1, 4)) (some (6, 1, 4)) (.next ([-5184000000000], [6885000000000]) (some (6, 1, 4))
    (some (6, 2, 4)) (.next ([-2415000000000], [2934000000000]) (some (6, 2, 4)) (some (6, 2, 6))
    (.next ([-5745000000000], [6120000000000]) (some (6, 2, 6)) (some (6, 2, 6)) (.terminal (some
    (6, 2, 6)) (some (0, 2, 6)) (some (6, 2, 6)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([750000000000], [90000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([3840000000000], [750000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([5505000000000], [4680000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([4755000000000], [4590000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2880000000000,
      9000000000000], [4680000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2130000000000,
      9000000000000], [4590000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0, 0],
      [2880000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-90000000000],
      [840000000000]) (some (4, 1, 2)) (some (4, 2, 2)) (.next ([-750000000000], [4590000000000])
      (some (4, 2, 2)) (some (4, 2, 3)) (.next ([-4680000000000], [10185000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-4590000000000], [9345000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-4680000000000, 0], [7560000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 4))
      (.next ([-4590000000000, 0], [6720000000000, 9000000000000]) (some (4, 2, 4)) (some (4, 2, 4))
      (.terminal (some (4, 2, 4)) (some (0, 2, 4)) (some (4, 2, 4))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 3 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3870000000000, -9000000000000], [0,
      9000000000000]) (some (2, 0, 1)) (some (3, 0, 1)) (.next ([5760000000000, 9000000000000],
      [990000000000, -9000000000000]) (some (3, 0, 1)) (some (3, 4, 1)) (.next ([2295000000000],
      [585000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([3285000000000, -9000000000000],
      [2880000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2880000000000,
      9000000000000], [2880000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next
      ([2880000000000, 9000000000000], [3285000000000, -9000000000000]) (some (3, 4, 1)) (some (3,
      4, 1)) (.next ([2880000000000], [3870000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next
      ([0], [2880000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0,
      -9000000000000], [3870000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-990000000000,
      9000000000000], [6750000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-585000000000],
      [2880000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2880000000000, -9000000000000],
      [6165000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2880000000000, -9000000000000],
      [5760000000000, 18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3285000000000,
      9000000000000], [6165000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3870000000000],
      [6750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([585000000000], [15000000000]) (some (8, 9, 5))
      (some (8, 9, 5)) (.next ([2130000000000], [60000000000]) (some (8, 9, 5)) (some (8, 9, 5))
      (.next ([6315000000000], [270000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next
      ([5085000000000], [690000000000]) (some (8, 9, 5)) (some (8, 9, 5)) (.next ([5025000000000],
      [750000000000]) (some (8, 9, 5)) (some (8, 9, 5)) fan18Owner0Part2)))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7215000000000, 9000000000000], [1785000000000,
      -9000000000000]) (some (2, 4, 1)) (some (3, 4, 1)) (.next ([3285000000000, -9000000000000],
      [2880000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2880000000000,
      9000000000000], [2880000000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next
      ([4335000000000], [4665000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1500000000000],
      [2835000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([1455000000000, -9000000000000],
      [4665000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0], [2880000000000,
      9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-1785000000000, 9000000000000],
      [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2880000000000, -9000000000000],
      [6165000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2880000000000, -9000000000000],
      [5760000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4665000000000],
      [9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2835000000000], [4335000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4665000000000], [6120000000000, -9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (4, 1, 2)) (some (4, 1,
      2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_9 : ExcludedOn (model18.B 9 ++ [step18.q]) 9000000000000 (model18.caps 9)
    (model18.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6045000000000], [120000000000]) (some (2, 0, 1))
      (some (3, 0, 1)) (.next ([6045000000000], [2880000000000, 9000000000000]) (some (3, 0, 1))
      (some (3, 0, 4)) (.next ([3285000000000, -9000000000000], [2880000000000, 9000000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2880000000000, 9000000000000], [2880000000000,
      9000000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([2880000000000, 9000000000000],
      [3285000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [2880000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-120000000000],
      [6165000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2880000000000, -9000000000000],
      [8925000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2880000000000,
      -9000000000000], [6165000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2880000000000,
      -9000000000000], [5760000000000, 18000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-3285000000000, 9000000000000], [6165000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 2)) (some (0, 1, 4))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_9 : ExcludedOn (model19.B 9 ++ [step19.q]) 9000000000000 (model19.caps 9)
    (model19.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3870000000000], [2880000000000]) (some (2, 0,
      4)) (some (3, 0, 4)) (.next ([3285000000000, -9000000000000], [2880000000000, 9000000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2880000000000, 9000000000000], [2880000000000,
      9000000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([2880000000000, 9000000000000],
      [3285000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([585000000000],
      [2295000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([990000000000, -9000000000000],
      [5760000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0, 9000000000000],
      [3870000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [2880000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2880000000000],
      [6750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2880000000000, -9000000000000],
      [6165000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2880000000000, -9000000000000],
      [5760000000000, 18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3285000000000,
      9000000000000], [6165000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2295000000000],
      [2880000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5760000000000, -9000000000000],
      [6750000000000]) (some (0, 1, 2)) (some (0, 4, 2)) (.next ([-3870000000000, 9000000000000],
      [3870000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4,
      2)) (some (0, 4, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([585000000000], [15000000000]) (some (9, 1, 5))
      (some (9, 1, 5)) (.next ([2130000000000], [60000000000]) (some (9, 1, 5)) (some (9, 1, 5))
      (.next ([6315000000000], [270000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next
      ([3630000000000], [555000000000]) (some (9, 1, 5)) (some (9, 1, 5)) (.next ([5370000000000],
      [945000000000]) (some (9, 1, 5)) (some (9, 1, 5)) fan21Owner0Part2)))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [2880000000000]) (some (2, 0,
      4)) (some (3, 0, 4)) (.next ([3285000000000, -9000000000000], [2880000000000, 9000000000000])
      (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2880000000000, 9000000000000], [2880000000000,
      9000000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([2880000000000, 9000000000000],
      [3285000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([840000000000],
      [2040000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([1245000000000, -9000000000000],
      [5760000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0, 9000000000000],
      [4125000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [2880000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2880000000000],
      [7005000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2880000000000, -9000000000000],
      [6165000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2880000000000, -9000000000000],
      [5760000000000, 18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3285000000000,
      9000000000000], [6165000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2040000000000],
      [2880000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5760000000000, -9000000000000],
      [7005000000000]) (some (0, 1, 2)) (some (0, 4, 2)) (.next ([-4125000000000, 9000000000000],
      [4125000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4,
      2)) (some (0, 4, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_9 : ExcludedOn (model21.B 9 ++ [step21.q]) 9000000000000 (model21.caps 9)
    (model21.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([585000000000], [15000000000]) (some (9, 1, 5))
      (some (9, 1, 5)) (.next ([2130000000000], [60000000000]) (some (9, 1, 5)) (some (9, 1, 5))
      (.next ([6315000000000], [270000000000]) (some (9, 1, 5)) (some (9, 1, 5))
      fan22Owner0Part2)))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8040000000000, 9000000000000], [1245000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([5160000000000], [4125000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2880000000000, 9000000000000], [2880000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2280000000000, -9000000000000],
      [4125000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [2880000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1245000000000, 9000000000000],
      [9285000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4125000000000], [9285000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2880000000000, -9000000000000], [5760000000000,
      18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4125000000000, 0],
      [6405000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0))
      (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3840000000000, 0], [1995000000000,
      -9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([3285000000000, -9000000000000],
      [2880000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([2880000000000,
      9000000000000], [2880000000000, 9000000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next
      ([2880000000000, 9000000000000], [3285000000000, -9000000000000]) (some (3, 1, 4)) (some (3,
      1, 4)) (.next ([3840000000000], [4875000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([960000000000, -9000000000000], [7755000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1,
      4)) (.next ([0], [2880000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([-1995000000000, 9000000000000], [5835000000000, -9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([-2880000000000, -9000000000000], [6165000000000]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([-2880000000000, -9000000000000], [5760000000000, 18000000000000]) (some (0, 1,
      2)) (some (0, 4, 2)) (.next ([-3285000000000, 9000000000000], [6165000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([-4875000000000], [8715000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([-7755000000000, -9000000000000], [8715000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5184000000000], [1245000000000]) (some (6, 0,
      2)) (some (6, 1, 2)) (.next ([1455000000000], [795000000000]) (some (6, 1, 2)) (some (6, 1,
      2)) (.next ([3870000000000], [2250000000000]) (some (6, 1, 2)) (some (6, 1, 3))
      fan23Owner4Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Sext320000330000
end ConwaySoifer.Simplified.Certificates
