/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint320000330000
import Mathlib.Tactic.FinCases

/-!
# Sint 320000 330000 3

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
namespace Sint320000330000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner4Part0 : FanWitness := (.next ([-990000000000, 9000000000000], [6120000000000]) (some
    (8, 2, 5)) (some (8, 2, 5)) (.next ([-519000000000], [2934000000000]) (some (8, 2, 5)) (some (8,
    2, 5)) (.next ([-705000000000], [3870000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
    ([-1305000000000], [5685000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([-1800000000000,
    9000000000000], [6180000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([-1290000000000],
    [4170000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([-1455000000000], [4680000000000])
    (some (8, 2, 5)) (some (8, 2, 6)) (.next ([-2250000000000], [6819000000000]) (some (8, 2, 6))
    (some (8, 2, 6)) (.next ([-1245000000000], [3375000000000]) (some (8, 2, 6)) (some (8, 2, 6))
    (.next ([-2460000000000], [5835000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next
    ([-684000000000], [1620000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([-2250000000000],
    [5184000000000]) (some (8, 2, 6)) (some (8, 3, 6)) (.next ([-3870000000000], [7755000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-1434000000000], [2430000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([-4680000000000], [7815000000000]) (some (8, 3, 6)) (some (8, 3, 6))
    (.next ([-3870000000000], [6120000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-2955000000000], [4665000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-1455000000000],
    [2250000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-4665000000000], [6300000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([-4680000000000], [6180000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([-4689000000000], [5814000000000]) (some (8, 3, 6)) (some (8, 3, 6))
    (.next ([-2880000000000], [3375000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-5184000000000], [5814000000000, 9000000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-750000000000], [810000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.terminal (some (8, 3, 7))
    (some (0, 4, 7)) (some (8, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner4Part1 : FanWitness := (.next ([4380000000000, 9000000000000], [1800000000000,
    -9000000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([2880000000000], [1290000000000])
    (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3225000000000], [1455000000000]) (some (7, 1, 4))
    (some (7, 1, 4)) (.next ([4569000000000], [2250000000000]) (some (7, 1, 4)) (some (7, 1, 4))
    (.next ([2130000000000], [1245000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([3375000000000], [2460000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([936000000000],
    [684000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([2934000000000], [2250000000000])
    (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3885000000000], [3870000000000]) (some (7, 1, 4))
    (some (8, 1, 4)) (.next ([996000000000], [1434000000000]) (some (8, 1, 4)) (some (8, 1, 4))
    (.next ([3135000000000], [4680000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
    ([2250000000000], [3870000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([1710000000000],
    [2955000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([795000000000], [1455000000000])
    (some (8, 1, 4)) (some (8, 1, 4)) (.next ([1635000000000], [4665000000000]) (some (8, 1, 4))
    (some (8, 1, 4)) (.next ([1500000000000], [4680000000000]) (some (8, 1, 4)) (some (8, 1, 4))
    (.next ([1125000000000], [4689000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
    ([495000000000], [2880000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([630000000000,
    9000000000000], [5184000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([60000000000],
    [750000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([0], [2955000000000]) (some (8, 1, 4))
    (some (8, 1, 4)) (.next ([-21000000000], [2250000000000]) (some (8, 1, 4)) (some (8, 1, 4))
    (.next ([-15000000000], [1515000000000]) (some (8, 1, 4)) (some (8, 2, 4)) (.next
    ([-495000000000], [5625000000000]) (some (8, 2, 4)) (some (8, 2, 5))
    fan25Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner4Part0 : FanWitness := (.next ([0], [2955000000000]) (some (7, 1, 7)) (some (7, 1, 7))
    (.next ([-21000000000], [2250000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([-15000000000], [1515000000000]) (some (0, 1, 7)) (some (0, 2, 7)) (.next ([-375000000000],
    [6120000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-519000000000], [2934000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-705000000000], [3870000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-1185000000000], [6180000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-1170000000000], [4665000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-1455000000000], [4680000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-2955000000000],
    [9000000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-684000000000], [1620000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-2250000000000], [5184000000000]) (some (0, 2, 7))
    (some (0, 3, 7)) (.next ([-2955000000000], [6450000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-5184000000000], [8979000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-1434000000000], [2430000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-3870000000000],
    [6120000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-2955000000000], [4665000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-1455000000000], [2250000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.next ([-6120000000000], [8295000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-4680000000000], [6180000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-4665000000000], [6045000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-5184000000000],
    [6429000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-6180000000000], [7545000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-750000000000], [810000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.terminal (some (0, 3, 7)) (some (0, 4, 7)) (some (0, 4,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner0Part0 : FanWitness := (.next ([-195000000000], [960000000000]) (some (8, 2, 4)) (some
    (8, 2, 4)) (.next ([-1155000000000], [5625000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([-1245000000000], [5430000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-1740000000000],
    [6810000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-3180000000000], [9690000000000])
    (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-690000000000], [1440000000000]) (some (8, 2, 4))
    (some (8, 2, 4)) (.next ([-690000000000], [1380000000000]) (some (8, 2, 4)) (some (8, 3, 4))
    (.next ([-210000000000], [375000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next
    ([-4185000000000], [6585000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([-195000000000],
    [285000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([-4200000000000], [6000000000000])
    (some (8, 3, 4)) (some (8, 3, 4)) (.next ([-4185000000000], [5910000000000]) (some (8, 3, 4))
    (some (8, 3, 4)) (.next ([-3990000000000], [5625000000000]) (some (8, 3, 4)) (some (8, 3, 4))
    (.next ([-5565000000000], [7275000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next
    ([-5580000000000], [6690000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([-5565000000000],
    [6600000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([-5370000000000], [6315000000000])
    (some (8, 3, 4)) (some (8, 3, 4)) (.next ([-7365000000000], [8445000000000]) (some (8, 3, 4))
    (some (8, 3, 4)) (.next ([-7650000000000], [8535000000000]) (some (8, 3, 4)) (some (8, 3, 4))
    (.next ([-7740000000000], [8610000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next
    ([-8325000000000], [9210000000000]) (some (8, 3, 4)) (some (8, 3, 4)) (.next ([-6315000000000],
    [6585000000000]) (some (8, 3, 4)) (some (8, 3, 8)) (.next ([-2130000000000], [2190000000000])
    (some (8, 3, 8)) (some (8, 3, 8)) (.next ([-585000000000], [600000000000]) (some (8, 3, 8))
    (some (8, 3, 8)) (.terminal (some (8, 3, 8)) (some (8, 3, 8)) (some (8, 3,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner0Part1 : FanWitness := (.next ([90000000000], [195000000000]) (some (8, 2, 4)) (some
    (8, 2, 4)) (.next ([1800000000000], [4200000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([1725000000000], [4185000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1635000000000],
    [3990000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1710000000000], [5565000000000])
    (some (8, 2, 4)) (some (8, 2, 4)) (.next ([1110000000000], [5580000000000]) (some (8, 2, 4))
    (some (8, 2, 4)) (.next ([1035000000000], [5565000000000]) (some (8, 2, 4)) (some (8, 2, 4))
    (.next ([945000000000], [5370000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([1080000000000], [7365000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([885000000000],
    [7650000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([870000000000], [7740000000000])
    (some (8, 2, 4)) (some (8, 2, 4)) (.next ([885000000000], [8325000000000]) (some (8, 2, 4))
    (some (8, 2, 4)) (.next ([270000000000], [6315000000000]) (some (8, 2, 4)) (some (8, 2, 4))
    (.next ([60000000000], [2130000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([15000000000],
    [585000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([0], [2130000000000]) (some (8, 2, 4))
    (some (8, 2, 4)) (.next ([-330000000000], [6330000000000]) (some (8, 2, 4)) (some (8, 2, 4))
    (.next ([-405000000000], [6315000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([-495000000000], [6120000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-480000000000],
    [5625000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-1050000000000], [7500000000000])
    (some (8, 2, 4)) (some (8, 2, 4)) (.next ([-15000000000], [90000000000]) (some (8, 2, 4)) (some
    (8, 2, 4)) (.next ([-1080000000000], [5640000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next
    ([-1740000000000], [8940000000000]) (some (8, 2, 4)) (some (8, 2, 4))
    fan28Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner4Part0 : FanWitness := (.next ([-15000000000], [1515000000000]) (some (0, 1, 7)) (some
    (0, 2, 7)) (.next ([-375000000000], [6120000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-519000000000], [2934000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-705000000000],
    [3870000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-1185000000000], [6180000000000])
    (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-1170000000000], [4665000000000]) (some (0, 2, 7))
    (some (0, 2, 7)) (.next ([-2205000000000], [8715000000000]) (some (0, 2, 7)) (some (0, 2, 7))
    (.next ([-1455000000000], [4680000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next
    ([-684000000000], [1620000000000]) (some (0, 2, 7)) (some (0, 2, 7)) (.next ([-2250000000000],
    [5184000000000]) (some (0, 2, 7)) (some (0, 3, 7)) (.next ([-2955000000000], [6450000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-4434000000000], [8694000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.next ([-1434000000000], [2430000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-3870000000000], [6120000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-2955000000000], [4665000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-1455000000000],
    [2250000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-5370000000000], [8010000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-3915000000000], [5760000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.next ([-5430000000000], [7260000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-2265000000000], [3015000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-4680000000000], [6180000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-5184000000000],
    [6429000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-5760000000000], [6510000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-750000000000], [810000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.terminal (some (0, 3, 7)) (some (0, 4, 7)) (some (0, 4,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner4Part1 : FanWitness := (.next ([2415000000000], [519000000000]) (some (7, 1, 4)) (some
    (7, 1, 4)) (.next ([3165000000000], [705000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([4995000000000], [1185000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3495000000000],
    [1170000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([6510000000000], [2205000000000])
    (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3225000000000], [1455000000000]) (some (7, 1, 4))
    (some (7, 1, 4)) (.next ([936000000000], [684000000000]) (some (7, 1, 4)) (some (7, 1, 4))
    (.next ([2934000000000], [2250000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([3495000000000], [2955000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([4260000000000],
    [4434000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([996000000000], [1434000000000])
    (some (7, 1, 4)) (some (7, 1, 4)) (.next ([2250000000000], [3870000000000]) (some (7, 1, 4))
    (some (7, 1, 4)) (.next ([1710000000000], [2955000000000]) (some (7, 1, 4)) (some (7, 1, 4))
    (.next ([795000000000], [1455000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([2640000000000], [5370000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([1845000000000],
    [3915000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([1830000000000], [5430000000000])
    (some (7, 1, 4)) (some (7, 1, 4)) (.next ([750000000000], [2265000000000]) (some (7, 1, 4))
    (some (7, 1, 7)) (.next ([1500000000000], [4680000000000]) (some (6, 1, 7)) (some (6, 1, 7))
    (.next ([1245000000000], [5184000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([750000000000], [5760000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([60000000000],
    [750000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([0], [2955000000000]) (some (6, 1, 7))
    (some (6, 1, 7)) (.next ([-21000000000], [2250000000000]) (some (0, 1, 7)) (some (0, 1, 7))
    fan28Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner3Part0 : FanWitness := (.next ([4590000000000], [2205000000000]) (some (4, 0, 5))
    (some (4, 0, 5)) (.next ([4680000000000], [2955000000000]) (some (4, 0, 5)) (some (4, 0, 5))
    (.next ([3840000000000], [2490000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([3930000000000], [3240000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([3840000000000],
    [5250000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([285000000000], [465000000000]) (some
    (4, 0, 5)) (some (4, 0, 5)) (.next ([750000000000], [3840000000000]) (some (4, 0, 5)) (some (4,
    1, 5)) (.next ([90000000000], [750000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([885000000000], [8205000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([600000000000],
    [7740000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [2955000000000]) (some (4, 1,
    5)) (some (4, 5, 5)) (.next ([-570000000000], [4410000000000]) (some (0, 5, 5)) (some (0, 5, 5))
    (.next ([-750000000000], [3240000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-1410000000000], [4500000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2205000000000],
    [6795000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2955000000000], [7635000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2490000000000], [6330000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-3240000000000], [7170000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-5250000000000], [9090000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-465000000000], [750000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3840000000000],
    [4590000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-750000000000], [840000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-8205000000000], [9090000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-7740000000000], [8340000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner6Part0 : FanWitness := (.next ([441000000000, 0], [2304000000000, -9000000000000])
    (some (0, 7, 4)) (some (0, 7, 4)) (.next ([441000000000], [5184000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([30000000000], [1965000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([0, 0], [2880000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-135000000000], [3684000000000]) (some (0, 2, 4)) (some (0, 3, 4)) (.next ([-285000000000],
    [4125000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-285000000000], [2940000000000])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-495000000000], [3429000000000]) (some (0, 3, 4))
    (some (0, 3, 4)) (.next ([-459000000000], [2244000000000]) (some (0, 3, 4)) (some (7, 3, 4))
    (.next ([-1635000000000], [5760000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
    ([-2439000000000, -9000000000000], [8064000000000, 9000000000000]) (some (7, 3, 4)) (some (7, 3,
    4)) (.next ([-1980000000000, -9000000000000], [5820000000000, 9000000000000]) (some (7, 3, 4))
    (some (7, 3, 4)) (.next ([-2250000000000], [6120000000000]) (some (7, 3, 4)) (some (7, 3, 4))
    (.next ([-255000000000], [615000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
    ([-2880000000000, -9000000000000], [5760000000000, 18000000000000]) (some (7, 3, 4)) (some (7,
    3, 4)) (.next ([-1920000000000], [3225000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
    ([-2880000000000, 9000000000000], [4125000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
    ([-2940000000000], [3840000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-2280000000000],
    [2970000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-4515000000000, -9000000000000],
    [5760000000000]) (some (7, 3, 4)) (some (7, 3, 5)) (.next ([-3240000000000, 9000000000000],
    [3870000000000]) (some (7, 3, 5)) (some (7, 3, 5)) (.next ([-2304000000000, 9000000000000],
    [2745000000000, -9000000000000]) (some (7, 3, 5)) (some (7, 3, 6)) (.next ([-5184000000000],
    [5625000000000]) (some (7, 3, 6)) (some (7, 3, 6)) (.next ([-1965000000000], [1995000000000])
    (some (7, 3, 6)) (some (7, 3, 6)) (.terminal (some (7, 3, 6)) (some (7, 3, 6)) (some (7, 3,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner6Part0 : FanWitness := (.next ([30000000000], [1965000000000]) (some (0, 2, 4)) (some
    (0, 2, 4)) (.next ([0, 0], [2880000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-150000000000], [3765000000000]) (some (0, 2, 4)) (some (0, 3, 4)) (.next
    ([-285000000000], [4125000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-285000000000],
    [2940000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-510000000000], [3510000000000])
    (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-540000000000], [2310000000000]) (some (0, 3, 4))
    (some (7, 3, 4)) (.next ([-1635000000000], [5760000000000]) (some (7, 3, 4)) (some (7, 3, 4))
    (.next ([-1245000000000, 9000000000000], [3840000000000]) (some (7, 3, 4)) (some (7, 3, 4))
    (.next ([-1980000000000, -9000000000000], [5820000000000, 9000000000000]) (some (7, 3, 4)) (some
    (7, 3, 4)) (.next ([-2250000000000], [6120000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
    ([-255000000000], [615000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-2880000000000,
    -9000000000000], [5760000000000, 18000000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
    ([-1920000000000], [3225000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-2880000000000,
    9000000000000], [4125000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-3480000000000],
    [4965000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-2940000000000], [3840000000000])
    (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-2280000000000], [2970000000000]) (some (7, 3, 4))
    (some (7, 3, 4)) (.next ([-4515000000000, -9000000000000], [5760000000000]) (some (7, 3, 4))
    (some (7, 3, 5)) (.next ([-3240000000000, 9000000000000], [3870000000000]) (some (7, 3, 5))
    (some (7, 3, 5)) (.next ([-5130000000000, -9000000000000], [6120000000000]) (some (7, 3, 5))
    (some (7, 3, 6)) (.next ([-2370000000000, 9000000000000], [2730000000000, -9000000000000]) (some
    (7, 3, 6)) (some (7, 3, 6)) (.next ([-5250000000000], [5610000000000]) (some (7, 3, 6)) (some
    (7, 3, 6)) (.next ([-1965000000000], [1995000000000]) (some (7, 3, 6)) (some (7, 3, 6))
    (.terminal (some (7, 3, 6)) (some (7, 3, 6)) (some (7, 3, 6)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5160000000000], [900000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([2280000000000, -9000000000000], [900000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([3285000000000, -9000000000000], [2880000000000, 9000000000000])
      (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2880000000000, 9000000000000], [2880000000000,
      9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2880000000000, 9000000000000],
      [3285000000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([1980000000000,
      9000000000000], [6060000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([105000000000],
      [5160000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0, 0], [2880000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-900000000000], [6060000000000])
      (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-900000000000, 0], [3180000000000, -9000000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2880000000000, -9000000000000], [6165000000000])
      (some (0, 2, 3)) (some (0, 4, 3)) (.next ([-2880000000000, -9000000000000], [5760000000000,
      18000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-3285000000000, 9000000000000],
      [6165000000000, 0]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-6060000000000, 0],
      [8040000000000, 9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-5160000000000],
      [5265000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4, 3)) (some (0, 4,
      3)) (some (0, 4, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
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

theorem excluded24_9 : ExcludedOn (model24.B 9 ++ [step24.q]) 9000000000000 (model24.caps 9)
    (model24.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1800000000000, -9000000000000], [450000000000,
      9000000000000]) (some (4, 0, 1)) (some (4, 1, 2)) (.next ([3630000000000], [1590000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([6060000000000], [3840000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([2430000000000], [2250000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([2610000000000, -9000000000000], [2880000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([3180000000000, -9000000000000], [3840000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([1650000000000], [4410000000000]) (some (4, 1, 2)) (some (4, 1, 4))
      (.next ([810000000000], [2430000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [5490000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-450000000000, -9000000000000],
      [2250000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1590000000000], [5220000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-3840000000000], [9900000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-2250000000000], [4680000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-2880000000000, -9000000000000], [5490000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-3840000000000], [7020000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-4410000000000], [6060000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-2430000000000], [3240000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1,
      4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded24_7
    · exact excluded24_8
    · exact excluded24_9
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([2229000000000], [21000000000]) (some (7, 0, 4))
      (some (7, 1, 4)) (.next ([1500000000000], [15000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([5130000000000], [495000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([5130000000000, 9000000000000], [990000000000, -9000000000000]) (some (7, 1, 4)) (some (7, 1,
      4)) (.next ([2415000000000], [519000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([3165000000000], [705000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([4380000000000],
      [1305000000000]) (some (7, 1, 4)) (some (7, 1, 4)) fan25Owner4Part1))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
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
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4590000000000], [2130000000000, 9000000000000])
      (some (2, 4, 2)) (some (3, 4, 2)) (.next ([4680000000000], [2880000000000, 9000000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([4590000000000], [4755000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([4680000000000], [5505000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([750000000000], [3840000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([90000000000], [750000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0], [2880000000000,
      9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-2130000000000, -9000000000000],
      [6720000000000, 9000000000000]) (some (0, 4, 2)) (some (4, 4, 2)) (.next ([-2880000000000,
      -9000000000000], [7560000000000, 9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([-4755000000000], [9345000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([-5505000000000], [10185000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-3840000000000], [4590000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-750000000000],
      [840000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (4, 2, 2))
      (some (4, 2, 2))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4680000000000], [2685000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([5505000000000], [3495000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1635000000000], [1860000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1185000000000], [4320000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [7365000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2685000000000], [7365000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3495000000000], [9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-1860000000000], [3495000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-4320000000000], [5505000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2229000000000], [21000000000]) (some (7, 0, 4))
      (some (7, 1, 4)) (.next ([1500000000000], [15000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([5745000000000], [375000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([2415000000000], [519000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3165000000000],
      [705000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([4995000000000], [1185000000000])
      (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3495000000000], [1170000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([3225000000000], [1455000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([6045000000000], [2955000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([936000000000], [684000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([2934000000000],
      [2250000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3495000000000], [2955000000000])
      (some (7, 1, 4)) (some (7, 1, 4)) (.next ([3795000000000], [5184000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([996000000000], [1434000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([2250000000000], [3870000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([1710000000000], [2955000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([795000000000],
      [1455000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([2175000000000], [6120000000000])
      (some (7, 1, 4)) (some (7, 1, 4)) (.next ([1500000000000], [4680000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([1380000000000], [4665000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([1245000000000], [5184000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([1365000000000], [6180000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([60000000000],
      [750000000000]) (some (7, 1, 4)) (some (7, 1, 7)) fan27Owner4Part0))))))))))))))))))))))))
      (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_8 : ExcludedOn (model27.B 8 ++ [step27.q]) 9000000000000 (model27.caps 8)
    (model27.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2955000000000], [1365000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([4680000000000], [2685000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([2955000000000], [6045000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1635000000000], [4410000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [7365000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1365000000000], [4320000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2685000000000], [7365000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-6045000000000], [9000000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-4410000000000], [6045000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some
      (0, 1, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded27_0
    · exact excluded27_1
    · exact excluded27_2
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [330000000000]) (some (8, 8, 3))
      (some (8, 8, 3)) (.next ([5910000000000], [405000000000]) (some (8, 8, 3)) (some (8, 8, 3))
      (.next ([5625000000000], [495000000000]) (some (8, 8, 3)) (some (8, 8, 3)) (.next
      ([5145000000000], [480000000000]) (some (8, 8, 3)) (some (8, 8, 3)) (.next ([6450000000000],
      [1050000000000]) (some (8, 8, 3)) (some (8, 8, 4)) (.next ([75000000000], [15000000000]) (some
      (8, 1, 4)) (some (8, 1, 4)) (.next ([4560000000000], [1080000000000]) (some (8, 1, 4)) (some
      (8, 1, 4)) (.next ([7200000000000], [1740000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([765000000000], [195000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([4470000000000],
      [1155000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next ([4185000000000], [1245000000000])
      (some (8, 1, 4)) (some (8, 1, 4)) (.next ([5070000000000], [1740000000000]) (some (8, 1, 4))
      (some (8, 1, 4)) (.next ([6510000000000], [3180000000000]) (some (8, 1, 4)) (some (8, 1, 4))
      (.next ([750000000000], [690000000000]) (some (8, 1, 4)) (some (8, 1, 4)) (.next
      ([690000000000], [690000000000]) (some (8, 1, 4)) (some (8, 2, 4)) (.next ([165000000000],
      [210000000000]) (some (8, 2, 4)) (some (8, 2, 4)) (.next ([2400000000000], [4185000000000])
      (some (8, 2, 4)) (some (8, 2, 4)) fan28Owner0Part1)))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2229000000000], [21000000000]) (some (7, 0, 4))
      (some (7, 1, 4)) (.next ([1500000000000], [15000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([5745000000000], [375000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      fan28Owner4Part1)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_7 : ExcludedOn (model28.B 7 ++ [step28.q]) 9000000000000 (model28.caps 7)
    (model28.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_8 : ExcludedOn (model28.B 8 ++ [step28.q]) 9000000000000 (model28.caps 8)
    (model28.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3240000000000], [1830000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([4680000000000], [2685000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([2385000000000], [4125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([3240000000000], [6510000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [7365000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1830000000000], [5070000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2685000000000], [7365000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-4125000000000], [6510000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-6510000000000], [9750000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded28_4
    · exact excluded28_5
    · exact excluded28_6
    · exact excluded28_7
    · exact excluded28_8
    · exact excluded28_9
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded29_1 : ExcludedOn (model29.B 1 ++ [step29.q]) 9000000000000 (model29.caps 1)
    (model29.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8040000000000, 9000000000000], [870000000000,
      -9000000000000]) none none (.next ([5160000000000], [3750000000000]) none none (.next
      ([2880000000000, 9000000000000], [2880000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([2280000000000, -9000000000000], [3750000000000, 0]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([0, 0], [2880000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-870000000000, 9000000000000], [8910000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-3750000000000], [8910000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2880000000000,
      -9000000000000], [5760000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-3750000000000, 0], [6030000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.terminal (some (3, 1, 0)) none none))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_2 : ExcludedOn (model29.B 2 ++ [step29.q]) 9000000000000 (model29.caps 2)
    (model29.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3750000000000], [90000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([6120000000000, -9000000000000], [2880000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2280000000000, -9000000000000], [3750000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([870000000000, -9000000000000], [2970000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [2880000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-90000000000], [3840000000000])
      (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-2880000000000, -9000000000000], [9000000000000,
      0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3750000000000, 0], [6030000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2970000000000, -9000000000000],
      [3840000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_3 : ExcludedOn (model29.B 3 ++ [step29.q]) 9000000000000 (model29.caps 3)
    (model29.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3840000000000], [570000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) (.next ([2490000000000], [750000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      (.next ([3090000000000], [1410000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      fan29Owner3Part0)))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_7 : ExcludedOn (model29.B 7 ++ [step29.q]) 9000000000000 (model29.caps 7)
    (model29.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_8 : ExcludedOn (model29.B 8 ++ [step29.q]) 9000000000000 (model29.caps 8)
    (model29.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded29_1
    · exact excluded29_2
    · exact excluded29_3
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_4 : ExcludedOn (model30.B 4 ++ [step30.q]) 9000000000000 (model30.caps 4)
    (model30.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3549000000000], [135000000000]) (some (6, 7, 3))
      (some (6, 7, 4)) (.next ([3840000000000], [285000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([2655000000000], [285000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([2934000000000], [495000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1785000000000],
      [459000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([4125000000000], [1635000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([5625000000000], [2439000000000, 9000000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3840000000000], [1980000000000, 9000000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3870000000000], [2250000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([360000000000], [255000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([2880000000000, 9000000000000], [2880000000000, 9000000000000]) (some (0, 7, 4)) (some
      (0, 7, 4)) (.next ([1305000000000], [1920000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([1245000000000, 9000000000000], [2880000000000, -9000000000000]) (some (0, 7, 4)) (some (0,
      7, 4)) (.next ([900000000000], [2940000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([690000000000], [2280000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([1245000000000,
      -9000000000000], [4515000000000, 9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([630000000000, 9000000000000], [3240000000000, -9000000000000]) (some (0, 7, 4)) (some (0, 7,
      4)) fan30Owner6Part0)))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3816000000000], [135000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([1800000000000, -9000000000000], [450000000000, 9000000000000]) (some
      (4, 1, 2)) (some (4, 1, 2)) (.next ([2430000000000], [2250000000000]) (some (4, 1, 2)) (some
      (4, 1, 2)) (.next ([2610000000000, -9000000000000], [2880000000000, 9000000000000]) (some (4,
      1, 2)) (some (4, 1, 2)) (.next ([3816000000000], [5625000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([1386000000000], [3375000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([810000000000], [2430000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([936000000000,
      -9000000000000], [5625000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [5490000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next ([-135000000000], [3951000000000])
      (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-450000000000, -9000000000000], [2250000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2250000000000], [4680000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-2880000000000, -9000000000000], [5490000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5625000000000], [9441000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-3375000000000], [4761000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-2430000000000], [3240000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-5625000000000], [6561000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded30_4
    · exact (hj rfl).elim
    · exact excluded30_6
    · exact excluded30_7
    · exact excluded30_8
    · exact excluded30_9
theorem next30 : model30.insert step30 = model31 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded31_0 : ExcludedOn (model31.B 0 ++ [step31.q]) 9000000000000 (model31.caps 0)
    (model31.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_1 : ExcludedOn (model31.B 1 ++ [step31.q]) 9000000000000 (model31.caps 1)
    (model31.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_3 : ExcludedOn (model31.B 3 ++ [step31.q]) 9000000000000 (model31.caps 3)
    (model31.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_6 : ExcludedOn (model31.B 6 ++ [step31.q]) 9000000000000 (model31.caps 6)
    (model31.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3615000000000], [150000000000]) (some (6, 7, 3))
      (some (6, 7, 4)) (.next ([3840000000000], [285000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([2655000000000], [285000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([3000000000000], [510000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1770000000000],
      [540000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([4125000000000], [1635000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([2595000000000, 9000000000000], [1245000000000,
      -9000000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3840000000000], [1980000000000,
      9000000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([3870000000000], [2250000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([360000000000], [255000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([2880000000000, 9000000000000], [2880000000000, 9000000000000]) (some
      (0, 7, 4)) (some (0, 7, 4)) (.next ([1305000000000], [1920000000000]) (some (0, 7, 4)) (some
      (0, 7, 4)) (.next ([1245000000000, 9000000000000], [2880000000000, -9000000000000]) (some (0,
      7, 4)) (some (0, 7, 4)) (.next ([1485000000000], [3480000000000]) (some (0, 7, 4)) (some (0,
      7, 4)) (.next ([900000000000], [2940000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([690000000000], [2280000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([1245000000000,
      -9000000000000], [4515000000000, 9000000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
      ([630000000000, 9000000000000], [3240000000000, -9000000000000]) (some (0, 7, 4)) (some (0, 7,
      4)) (.next ([990000000000, -9000000000000], [5130000000000, 9000000000000]) (some (0, 7, 4))
      (some (0, 7, 4)) (.next ([360000000000, 0], [2370000000000, -9000000000000]) (some (0, 7, 4))
      (some (0, 7, 4)) (.next ([360000000000], [5250000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      fan31Owner6Part0))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3750000000000], [120000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([1800000000000, -9000000000000], [450000000000, 9000000000000]) (some
      (4, 1, 2)) (some (4, 1, 2)) (.next ([2430000000000], [2250000000000]) (some (4, 1, 2)) (some
      (4, 1, 2)) (.next ([2610000000000, -9000000000000], [2880000000000, 9000000000000]) (some (4,
      1, 2)) (some (4, 1, 2)) (.next ([3750000000000], [5610000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([1320000000000], [3360000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([810000000000], [2430000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([870000000000,
      -9000000000000], [5610000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0],
      [5490000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next ([-120000000000], [3870000000000])
      (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-450000000000, -9000000000000], [2250000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2250000000000], [4680000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-2880000000000, -9000000000000], [5490000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-5610000000000], [9360000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-3360000000000], [4680000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-2430000000000], [3240000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-5610000000000], [6480000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked31 : StepValid model31 9000000000000 step31 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded31_0
    · exact excluded31_1
    · exact excluded31_2
    · exact excluded31_3
    · exact excluded31_4
    · exact (hj rfl).elim
    · exact excluded31_6
    · exact excluded31_7
    · exact excluded31_8
    · exact excluded31_9
theorem next31 : model31.insert step31 = model32 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint320000330000
end ConwaySoifer.Simplified.Certificates
