/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint320000330000
import Mathlib.Tactic.FinCases

/-!
# Sint 320000 330000 5

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
def fan40Owner0Part0 : FanWitness := (.next ([960000000000], [7434000000000]) (some (0, 6, 4)) (some
    (0, 6, 4)) (.next ([270000000000], [6315000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([60000000000], [2130000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([90000000000],
    [7719000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-480000000000], [5625000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-105000000000], [1170000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-600000000000], [6600000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-1350000000000], [5910000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-795000000000], [2610000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-750000000000],
    [1869000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-690000000000], [1440000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1809000000000], [3249000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-4500000000000], [7380000000000]) (some (0, 3, 4)) (some (0, 3, 4))
    (.next ([-1119000000000], [1809000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next
    ([-1920000000000], [2934000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-2235000000000],
    [3360000000000]) (some (0, 3, 4)) (some (6, 3, 4)) (.next ([-585000000000], [870000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-4785000000000], [6795000000000]) (some (6, 3, 4))
    (some (6, 3, 5)) (.next ([-5565000000000], [7275000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-5850000000000], [6690000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-7434000000000], [8394000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-6315000000000],
    [6585000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-2130000000000], [2190000000000])
    (some (6, 3, 5)) (some (6, 3, 5)) (.next ([-7719000000000], [7809000000000]) (some (6, 3, 5))
    (some (6, 3, 5)) (.terminal (some (6, 3, 5)) (some (6, 3, 5)) (some (6, 3,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner4Part0 : FanWitness := (.next ([-1455000000000], [4680000000000]) (some (0, 2, 8))
    (some (0, 8, 8)) (.next ([-1050000000000], [3240000000000]) (some (0, 8, 8)) (some (0, 8, 8))
    (.next ([-2946000000000], [9000000000000]) (some (0, 8, 8)) (some (0, 8, 8)) (.next
    ([-1626000000000], [4185000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-1080000000000],
    [2445000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-2625000000000], [5865000000000])
    (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-2955000000000], [6450000000000]) (some (0, 8, 7))
    (some (0, 8, 7)) (.next ([-2070000000000], [3690000000000]) (some (0, 8, 7)) (some (0, 8, 7))
    (.next ([-4500000000000], [7815000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next
    ([-1305000000000], [2250000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-2955000000000],
    [4815000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-1761000000000], [2820000000000])
    (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-2820000000000], [4500000000000]) (some (0, 8, 7))
    (some (0, 8, 7)) (.next ([-3870000000000], [6120000000000]) (some (0, 8, 7)) (some (0, 8, 7))
    (.next ([-6441000000000], [9000000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next
    ([-4680000000000], [6180000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-990000000000],
    [1245000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-1740000000000], [2055000000000])
    (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-5865000000000], [6735000000000]) (some (0, 8, 7))
    (some (0, 8, 7)) (.next ([-2571000000000], [2880000000000]) (some (0, 8, 7)) (some (0, 8, 7))
    (.next ([-2625000000000], [2910000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next
    ([-1365000000000], [1500000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-750000000000],
    [810000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-4320000000000], [4635000000000])
    (some (0, 8, 7)) (some (0, 8, 7)) (.terminal (some (0, 8, 7)) (some (0, 8, 7)) (some (0, 8,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner4Part1 : FanWitness := (.next ([1860000000000], [2955000000000]) (some (7, 2, 8))
    (some (7, 2, 8)) (.next ([1059000000000], [1761000000000]) (some (7, 2, 8)) (some (7, 2, 8))
    (.next ([1680000000000], [2820000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
    ([2250000000000], [3870000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([2559000000000],
    [6441000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([1500000000000], [4680000000000])
    (some (7, 2, 8)) (some (7, 2, 8)) (.next ([255000000000], [990000000000]) (some (7, 2, 8)) (some
    (7, 2, 8)) (.next ([315000000000], [1740000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
    ([870000000000], [5865000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([309000000000],
    [2571000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([285000000000], [2625000000000])
    (some (7, 2, 8)) (some (7, 2, 8)) (.next ([135000000000], [1365000000000]) (some (7, 2, 8))
    (some (7, 2, 8)) (.next ([60000000000], [750000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
    ([315000000000], [4320000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([0],
    [2955000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([-180000000000], [4500000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-375000000000], [6120000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([-396000000000], [6441000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    (.next ([-180000000000], [1545000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next
    ([-681000000000], [3816000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-705000000000],
    [3870000000000]) (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-1185000000000], [6180000000000])
    (some (0, 2, 8)) (some (0, 2, 8)) (.next ([-1320000000000], [4815000000000]) (some (0, 2, 8))
    (some (0, 2, 8)) (.next ([-1761000000000], [6261000000000]) (some (0, 2, 8)) (some (0, 2, 8))
    fan40Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner6Part0 : FanWitness := (.next ([0, 0], [2880000000000, 9000000000000]) (some (7, 2,
    4)) (some (7, 2, 4)) (.next ([-285000000000], [4125000000000]) (some (7, 2, 4)) (some (7, 3, 4))
    (.next ([-285000000000], [2940000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
    ([-309000000000], [2880000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-1635000000000],
    [5760000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-2559000000000], [9000000000000])
    (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-924000000000], [3240000000000]) (some (7, 3, 4))
    (some (7, 3, 4)) (.next ([-1245000000000, 9000000000000], [3840000000000]) (some (7, 3, 4))
    (some (7, 3, 4)) (.next ([-1980000000000, -9000000000000], [5820000000000, 9000000000000]) (some
    (7, 3, 4)) (some (7, 3, 4)) (.next ([-2250000000000], [6120000000000]) (some (7, 3, 4)) (some
    (7, 3, 4)) (.next ([-255000000000], [615000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
    ([-2274000000000], [4875000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-2880000000000,
    -9000000000000], [5760000000000, 18000000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
    ([-1920000000000], [3225000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-5439000000000,
    -9000000000000], [9000000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([-2880000000000,
    9000000000000], [4125000000000]) (some (7, 3, 4)) (some (7, 3, 7)) (.next ([-2940000000000],
    [3840000000000]) (some (7, 3, 7)) (some (7, 3, 7)) (.next ([-2280000000000], [2970000000000])
    (some (7, 3, 7)) (some (7, 3, 7)) (.next ([-4515000000000, -9000000000000], [5760000000000])
    (some (7, 3, 7)) (some (7, 3, 7)) (.next ([-3240000000000, 9000000000000], [3870000000000])
    (some (7, 3, 7)) (some (7, 3, 7)) (.next ([-5130000000000, -9000000000000], [6120000000000])
    (some (7, 3, 7)) (some (7, 3, 7)) (.next ([-5160000000000], [5541000000000]) (some (7, 3, 7))
    (some (7, 3, 7)) (.next ([-6120000000000, 9000000000000], [6441000000000]) (some (1, 3, 7))
    (some (1, 3, 7)) (.next ([-1965000000000], [1995000000000]) (some (1, 3, 7)) (some (1, 3, 7))
    (.terminal (some (1, 3, 7)) (some (1, 3, 7)) (some (1, 3, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner3Part0 : FanWitness := (.next ([861000000000], [264000000000]) (some (4, 0, 5)) (some
    (4, 0, 5)) (.next ([2691000000000], [1125000000000]) (some (4, 0, 5)) (some (4, 1, 5)) (.next
    ([3066000000000], [1410000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4590000000000],
    [2205000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4680000000000], [2955000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([3465000000000], [3066000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([3555000000000], [3816000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([3816000000000], [5250000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([750000000000], [3840000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([90000000000],
    [750000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([861000000000], [8205000000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [2955000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([-570000000000], [4386000000000]) (some (0, 1, 5)) (some (0, 5, 5)) (.next
    ([-264000000000], [1125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1125000000000],
    [3816000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1410000000000], [4476000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2205000000000], [6795000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-2955000000000], [7635000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-3066000000000], [6531000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-3816000000000], [7371000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5250000000000],
    [9066000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3840000000000], [4590000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-750000000000], [840000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-8205000000000], [9066000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.terminal (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner5Part0 : FanWitness := (.next ([2595000000000], [1155000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([4380000000000], [2061000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([2580000000000], [1236000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([4380000000000, 0], [2880000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([510000000000, -9000000000000], [360000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([4020000000000], [3750000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([3939000000000],
    [3816000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([2691000000000], [3390000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([2625000000000], [3375000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([0], [4380000000000]) (some (0, 6, 4)) (some (0, 6, 5)) (.next
    ([-360000000000], [3750000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-795000000000],
    [7236000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-441000000000], [3816000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-15000000000], [81000000000]) (some (0, 6, 5)) (some
    (0, 6, 5)) (.next ([-795000000000, 0], [2880000000000, 9000000000000]) (some (0, 6, 5)) (some
    (0, 6, 5)) (.next ([-1155000000000], [3750000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-2061000000000], [6441000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1236000000000],
    [3816000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2880000000000, -9000000000000],
    [7260000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-360000000000, 0],
    [870000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3750000000000],
    [7770000000000]) (some (0, 2, 5)) (some (0, 3, 5)) (.next ([-3816000000000], [7755000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3390000000000], [6081000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-3375000000000], [6000000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.terminal (some (0, 3, 5)) (some (0, 3, 5)) (some (0, 3, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner0Part0 : FanWitness := (.next ([705000000000], [4350000000000]) (some (0, 6, 4)) (some
    (0, 6, 4)) (.next ([816000000000], [5874000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([270000000000], [6315000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([60000000000],
    [2130000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-480000000000], [5625000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-105000000000], [1170000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-624000000000], [6624000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-1470000000000], [9555000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1374000000000], [5934000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2364000000000],
    [9864000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-990000000000], [3930000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-795000000000], [2610000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-690000000000], [1440000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-1740000000000], [3240000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-4500000000000], [7380000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-585000000000],
    [894000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2235000000000], [3360000000000])
    (some (0, 6, 4)) (some (0, 6, 5)) (.next ([-4809000000000], [6795000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-5565000000000], [7275000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-3180000000000], [3990000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-4350000000000], [5055000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-5874000000000],
    [6690000000000]) (some (0, 6, 5)) (some (6, 6, 5)) (.next ([-6315000000000], [6585000000000])
    (some (6, 6, 5)) (some (6, 6, 5)) (.next ([-2130000000000], [2190000000000]) (some (6, 6, 5))
    (some (6, 6, 5)) (.terminal (some (6, 6, 5)) (some (6, 6, 5)) (some (6, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan43Owner5Part0 : FanWitness := (.next ([4380000000000, 0], [2880000000000, 9000000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([510000000000, -9000000000000], [360000000000]) (some
    (0, 1, 6)) (some (0, 1, 6)) (.next ([4020000000000], [3750000000000]) (some (0, 1, 6)) (some (0,
    1, 6)) (.next ([3939000000000], [3816000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([2691000000000], [3390000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([2625000000000],
    [3375000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([2430000000000], [4320000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([60000000000], [6750000000000]) (some (0, 1, 6)) (some
    (0, 1, 6)) (.next ([0], [4380000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-360000000000], [3750000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-450000000000,
    -9000000000000], [4320000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-309000000000],
    [2430000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-15000000000], [81000000000]) (some
    (0, 2, 5)) (some (0, 2, 5)) (.next ([-960000000000], [3960000000000]) (some (0, 2, 5)) (some (0,
    2, 5)) (.next ([-945000000000], [3879000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-2061000000000], [6441000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2880000000000,
    -9000000000000], [7260000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-360000000000, 0], [870000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-3750000000000], [7770000000000]) (some (0, 2, 5)) (some (0, 3, 5)) (.next ([-3816000000000],
    [7755000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3390000000000], [6081000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3375000000000], [6000000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-4320000000000], [6750000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-6750000000000], [6810000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.terminal (some
    (0, 3, 5)) (some (0, 3, 5)) (some (0, 3, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan44Owner6Part0 : FanWitness := (.next ([2880000000000, 9000000000000], [2880000000000,
    9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([1335000000000], [3840000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([900000000000], [2940000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([960000000000, -9000000000000], [3165000000000, 9000000000000]) (some
    (0, 6, 4)) (some (0, 6, 4)) (.next ([1440000000000, -9000000000000], [5130000000000,
    9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([690000000000], [2730000000000]) (some
    (0, 6, 4)) (some (0, 6, 4)) (.next ([480000000000], [1965000000000]) (some (0, 6, 4)) (some (0,
    6, 4)) (.next ([630000000000, 9000000000000], [3690000000000, -9000000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([0, 0], [2880000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6,
    4)) (.next ([-285000000000], [4125000000000]) (some (0, 2, 4)) (some (0, 3, 4)) (.next
    ([-285000000000], [2940000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-1110000000000],
    [4320000000000]) (some (0, 3, 4)) (some (0, 3, 4)) (.next ([-1245000000000, 9000000000000],
    [3840000000000]) (some (0, 3, 4)) (some (6, 3, 4)) (.next ([-2250000000000], [6570000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-2880000000000, -9000000000000], [8340000000000,
    9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-900000000000], [2520000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-2880000000000, -9000000000000], [5760000000000,
    18000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-3840000000000], [5175000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-2940000000000], [3840000000000]) (some (6, 3, 4))
    (some (6, 3, 4)) (.next ([-3165000000000, -9000000000000], [4125000000000]) (some (6, 3, 4))
    (some (6, 3, 4)) (.next ([-5130000000000, -9000000000000], [6570000000000]) (some (6, 3, 4))
    (some (6, 3, 5)) (.next ([-2730000000000], [3420000000000]) (some (6, 3, 5)) (some (6, 3, 5))
    (.next ([-1965000000000], [2445000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-3690000000000, 9000000000000], [4320000000000]) (some (6, 3, 0)) (some (6, 3, 0)) (.terminal
    (some (6, 3, 0)) (some (6, 3, 0)) (some (6, 3, 0)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner4Part0 : FanWitness := (.next ([-1455000000000], [4680000000000]) (some (0, 8, 6))
    (some (0, 8, 7)) (.next ([-1050000000000], [3240000000000]) (some (0, 8, 7)) (some (0, 8, 7))
    (.next ([-1080000000000], [2445000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next
    ([-2625000000000], [5865000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-2955000000000],
    [6450000000000]) (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-1320000000000], [2625000000000])
    (some (0, 8, 7)) (some (0, 8, 7)) (.next ([-2070000000000], [3690000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.next ([-4560000000000], [8055000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-4500000000000], [7815000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-1305000000000], [2250000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-2310000000000],
    [3870000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-2955000000000], [4815000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-2820000000000], [4500000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.next ([-3870000000000], [6120000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-3060000000000], [4680000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-4680000000000], [6180000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-990000000000],
    [1245000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-1740000000000], [2055000000000])
    (some (0, 3, 7)) (some (0, 4, 7)) (.next ([-5865000000000], [6735000000000]) (some (0, 4, 7))
    (some (0, 4, 7)) (.next ([-2625000000000], [2910000000000]) (some (0, 4, 7)) (some (0, 4, 7))
    (.next ([-1365000000000], [1500000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next
    ([-750000000000], [810000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-4320000000000],
    [4635000000000]) (some (0, 4, 7)) (some (0, 5, 7)) (.next ([-4560000000000], [4815000000000])
    (some (0, 5, 7)) (some (0, 5, 7)) (.terminal (some (0, 5, 7)) (some (0, 5, 7)) (some (0, 5,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan45Owner4Part1 : FanWitness := (.next ([3315000000000], [4500000000000]) (some (7, 8, 5))
    (some (7, 8, 5)) (.next ([945000000000], [1305000000000]) (some (7, 8, 5)) (some (7, 8, 5))
    (.next ([1560000000000], [2310000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next
    ([1860000000000], [2955000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([1680000000000],
    [2820000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([2250000000000], [3870000000000])
    (some (7, 8, 5)) (some (7, 8, 5)) (.next ([1620000000000], [3060000000000]) (some (7, 8, 5))
    (some (7, 8, 5)) (.next ([1500000000000], [4680000000000]) (some (7, 8, 5)) (some (7, 8, 5))
    (.next ([255000000000], [990000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next
    ([315000000000], [1740000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([870000000000],
    [5865000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([285000000000], [2625000000000])
    (some (7, 8, 5)) (some (7, 8, 5)) (.next ([135000000000], [1365000000000]) (some (7, 8, 5))
    (some (7, 8, 5)) (.next ([60000000000], [750000000000]) (some (7, 8, 5)) (some (7, 8, 6)) (.next
    ([315000000000], [4320000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([255000000000],
    [4560000000000]) (some (7, 8, 6)) (some (7, 8, 6)) (.next ([0], [2955000000000]) (some (7, 8,
    6)) (some (7, 8, 6)) (.next ([-180000000000], [4500000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-375000000000], [6120000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-180000000000], [1545000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-705000000000],
    [3870000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1185000000000], [6180000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-60000000000], [240000000000]) (some (0, 8, 6)) (some
    (0, 8, 6)) (.next ([-1320000000000], [4815000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    fan45Owner4Part0))))))))))))))))))))))))

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5145000000000], [480000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) (.next ([1065000000000], [105000000000]) (some (5, 6, 3)) (some (5, 6, 4))
      (.next ([6000000000000], [600000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([4560000000000], [1350000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1815000000000],
      [795000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1119000000000], [750000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) (.next ([750000000000], [690000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([1440000000000], [1809000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      (.next ([2880000000000], [4500000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([690000000000], [1119000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1014000000000],
      [1920000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1125000000000], [2235000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) (.next ([285000000000], [585000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([2010000000000], [4785000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      (.next ([1710000000000], [5565000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([840000000000], [5850000000000]) (some (0, 6, 4)) (some (0, 6, 4))
      fan40Owner0Part0))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4320000000000], [180000000000]) (some (7, 0, 8))
      (some (7, 1, 8)) (.next ([5745000000000], [375000000000]) (some (7, 1, 8)) (some (7, 1, 8))
      (.next ([6045000000000], [396000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next
      ([1365000000000], [180000000000]) (some (7, 1, 8)) (some (7, 1, 8)) (.next ([3135000000000],
      [681000000000]) (some (7, 1, 8)) (some (7, 2, 8)) (.next ([3165000000000], [705000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([4995000000000], [1185000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([3495000000000], [1320000000000]) (some (7, 2, 8)) (some (7, 2, 8))
      (.next ([4500000000000], [1761000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([3225000000000], [1455000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([2190000000000],
      [1050000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([6054000000000], [2946000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([2559000000000], [1626000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) (.next ([1365000000000], [1080000000000]) (some (7, 2, 8)) (some (7, 2, 8))
      (.next ([3240000000000], [2625000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next
      ([3495000000000], [2955000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([1620000000000],
      [2070000000000]) (some (7, 2, 8)) (some (7, 2, 8)) (.next ([3315000000000], [4500000000000])
      (some (7, 2, 8)) (some (7, 2, 8)) (.next ([945000000000], [1305000000000]) (some (7, 2, 8))
      (some (7, 2, 8)) fan40Owner4Part1)))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3840000000000], [285000000000]) (some (7, 1, 3))
      (some (7, 2, 4)) (.next ([2655000000000], [285000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      (.next ([2571000000000], [309000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([4125000000000], [1635000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([6441000000000],
      [2559000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([2316000000000], [924000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([2595000000000, 9000000000000], [1245000000000,
      -9000000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([3840000000000], [1980000000000,
      9000000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next ([3870000000000], [2250000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([360000000000], [255000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([2601000000000], [2274000000000]) (some (7, 2, 4)) (some (7, 2, 4))
      (.next ([2880000000000, 9000000000000], [2880000000000, 9000000000000]) (some (7, 2, 4)) (some
      (7, 2, 4)) (.next ([1305000000000], [1920000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([3561000000000, -9000000000000], [5439000000000, 9000000000000]) (some (7, 2, 4)) (some (7,
      2, 4)) (.next ([1245000000000, 9000000000000], [2880000000000, -9000000000000]) (some (7, 2,
      4)) (some (7, 2, 4)) (.next ([900000000000], [2940000000000]) (some (7, 2, 4)) (some (7, 2,
      4)) (.next ([690000000000], [2280000000000]) (some (7, 2, 4)) (some (7, 2, 4)) (.next
      ([1245000000000, -9000000000000], [4515000000000, 9000000000000]) (some (7, 2, 4)) (some (7,
      2, 4)) (.next ([630000000000, 9000000000000], [3240000000000, -9000000000000]) (some (7, 2,
      4)) (some (7, 2, 4)) (.next ([990000000000, -9000000000000], [5130000000000, 9000000000000])
      (some (7, 2, 4)) (some (7, 2, 4)) (.next ([381000000000], [5160000000000]) (some (7, 2, 4))
      (some (7, 2, 4)) (.next ([321000000000, 9000000000000], [6120000000000, -9000000000000]) (some
      (7, 2, 4)) (some (7, 2, 4)) (.next ([30000000000], [1965000000000]) (some (7, 2, 4)) (some (7,
      2, 4)) fan40Owner6Part0)))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_9 : ExcludedOn (model40.B 9 ++ [step40.q]) 9000000000000 (model40.caps 9)
    (model40.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded40_4
    · exact (hj rfl).elim
    · exact excluded40_6
    · exact excluded40_7
    · exact excluded40_8
    · exact excluded40_9
theorem next40 : model40.insert step40 = model41 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8124000000000], [810000000000]) none none (.next
      ([5184000000000], [3750000000000]) none none (.next ([2940000000000, 0], [2880000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2304000000000, -9000000000000],
      [3750000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [2880000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-810000000000], [8934000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3750000000000], [8934000000000]) (some (3, 1, 0))
      (some (3, 1, 0)) (.next ([-2880000000000, -9000000000000], [5820000000000, 9000000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-3750000000000, 0], [6054000000000,
      -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0)) none
      none))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3750000000000], [66000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([6120000000000, -9000000000000], [2880000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2304000000000, -9000000000000], [3750000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([870000000000, -9000000000000], [2946000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [2880000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-66000000000], [3816000000000])
      (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-2880000000000, -9000000000000], [9000000000000,
      0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3750000000000, 0], [6054000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2946000000000, -9000000000000],
      [3816000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3816000000000], [570000000000]) (some (3, 0, 5))
      (some (4, 0, 5)) fan41Owner3Part0)) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100
      (by decide +kernel)
  decide +kernel

theorem excluded41_4 : ExcludedOn (model41.B 4 ++ [step41.q]) 9000000000000 (model41.caps 4)
    (model41.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_7 : ExcludedOn (model41.B 7 ++ [step41.q]) 9000000000000 (model41.caps 7)
    (model41.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_8 : ExcludedOn (model41.B 8 ++ [step41.q]) 9000000000000 (model41.caps 8)
    (model41.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded41_1
    · exact excluded41_2
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
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_3 : ExcludedOn (model42.B 3 ++ [step42.q]) 9000000000000 (model42.caps 3)
    (model42.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_5 : ExcludedOn (model42.B 5 ++ [step42.q]) 9000000000000 (model42.caps 5)
    (model42.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3390000000000], [360000000000]) (some (5, 0, 3))
      (some (5, 6, 3)) (.next ([6441000000000], [795000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      (.next ([3375000000000], [441000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([66000000000], [15000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2085000000000,
      9000000000000], [795000000000]) (some (5, 6, 3)) (some (5, 6, 4)) fan42Owner5Part0)))))) (den
      := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_6 : ExcludedOn (model42.B 6 ++ [step42.q]) 9000000000000 (model42.caps 6)
    (model42.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_7 : ExcludedOn (model42.B 7 ++ [step42.q]) 9000000000000 (model42.caps 7)
    (model42.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_8 : ExcludedOn (model42.B 8 ++ [step42.q]) 9000000000000 (model42.caps 8)
    (model42.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded42_3
    · exact excluded42_4
    · exact excluded42_5
    · exact excluded42_6
    · exact excluded42_7
    · exact excluded42_8
    · exact (hj rfl).elim
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded43_0 : ExcludedOn (model43.B 0 ++ [step43.q]) 9000000000000 (model43.caps 0)
    (model43.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5145000000000], [480000000000]) (some (5, 6, 6))
      (some (5, 6, 6)) (.next ([1065000000000], [105000000000]) (some (5, 6, 6)) (some (5, 6, 6))
      (.next ([6000000000000], [624000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next
      ([8085000000000], [1470000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next ([4560000000000],
      [1374000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([7500000000000], [2364000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) (.next ([2940000000000], [990000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([1815000000000], [795000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      (.next ([750000000000], [690000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([1500000000000], [1740000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([2880000000000],
      [4500000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([309000000000], [585000000000])
      (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1125000000000], [2235000000000]) (some (5, 6, 4))
      (some (5, 6, 4)) (.next ([1986000000000], [4809000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      (.next ([1710000000000], [5565000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([810000000000], [3180000000000]) (some (0, 6, 4)) (some (0, 6, 4))
      fan43Owner0Part0))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_2 : ExcludedOn (model43.B 2 ++ [step43.q]) 9000000000000 (model43.caps 2)
    (model43.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_3 : ExcludedOn (model43.B 3 ++ [step43.q]) 9000000000000 (model43.caps 3)
    (model43.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_4 : ExcludedOn (model43.B 4 ++ [step43.q]) 9000000000000 (model43.caps 4)
    (model43.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3390000000000], [360000000000]) (some (5, 0, 3))
      (some (5, 1, 3)) (.next ([3870000000000, -9000000000000], [450000000000, 9000000000000]) (some
      (5, 1, 3)) (some (5, 1, 3)) (.next ([2121000000000], [309000000000]) (some (5, 1, 3)) (some
      (5, 1, 3)) (.next ([66000000000], [15000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([3000000000000], [960000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next ([2934000000000],
      [945000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([4380000000000], [2061000000000])
      (some (5, 1, 4)) (some (5, 1, 6)) fan43Owner5Part0)))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_7 : ExcludedOn (model43.B 7 ++ [step43.q]) 9000000000000 (model43.caps 7)
    (model43.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_8 : ExcludedOn (model43.B 8 ++ [step43.q]) 9000000000000 (model43.caps 8)
    (model43.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_9 : ExcludedOn (model43.B 9 ++ [step43.q]) 9000000000000 (model43.caps 9)
    (model43.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded43_4
    · exact excluded43_5
    · exact (hj rfl).elim
    · exact excluded43_7
    · exact excluded43_8
    · exact excluded43_9
theorem next43 : model43.insert step43 = model44 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded44_0 : ExcludedOn (model44.B 0 ++ [step44.q]) 9000000000000 (model44.caps 0)
    (model44.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_1 : ExcludedOn (model44.B 1 ++ [step44.q]) 9000000000000 (model44.caps 1)
    (model44.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_2 : ExcludedOn (model44.B 2 ++ [step44.q]) 9000000000000 (model44.caps 2)
    (model44.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_3 : ExcludedOn (model44.B 3 ++ [step44.q]) 9000000000000 (model44.caps 3)
    (model44.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_4 : ExcludedOn (model44.B 4 ++ [step44.q]) 9000000000000 (model44.caps 4)
    (model44.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_6 : ExcludedOn (model44.B 6 ++ [step44.q]) 9000000000000 (model44.caps 6)
    (model44.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3840000000000], [285000000000]) (some (0, 6, 3))
      (some (0, 6, 4)) (.next ([2655000000000], [285000000000]) (some (0, 6, 4)) (some (0, 6, 4))
      (.next ([3210000000000], [1110000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([2595000000000, 9000000000000], [1245000000000, -9000000000000]) (some (0, 6, 4)) (some (0,
      6, 4)) (.next ([4320000000000], [2250000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([5460000000000], [2880000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
      ([1620000000000], [900000000000]) (some (0, 6, 4)) (some (0, 6, 4)) fan44Owner6Part0))))))))
      (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded44_7 : ExcludedOn (model44.B 7 ++ [step44.q]) 9000000000000 (model44.caps 7)
    (model44.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_8 : ExcludedOn (model44.B 8 ++ [step44.q]) 9000000000000 (model44.caps 8)
    (model44.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded44_9 : ExcludedOn (model44.B 9 ++ [step44.q]) 9000000000000 (model44.caps 9)
    (model44.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1800000000000, -9000000000000], [450000000000,
      9000000000000]) (some (4, 0, 1)) (some (4, 1, 2)) (.next ([5325000000000, -9000000000000],
      [2880000000000, 9000000000000]) (some (4, 1, 2)) (some (0, 1, 2)) (.next ([3525000000000],
      [2430000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([2430000000000], [2250000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([3540000000000], [5460000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([1110000000000], [3210000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([660000000000, -9000000000000], [5460000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([0], [8205000000000]) (some (0, 1, 2)) (some (0, 1, 4)) (.next ([-450000000000,
      -9000000000000], [2250000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2880000000000,
      -9000000000000], [8205000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2430000000000],
      [5955000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2250000000000], [4680000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-5460000000000], [9000000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([-3210000000000], [4320000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([-5460000000000], [6120000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded44_2
    · exact excluded44_3
    · exact excluded44_4
    · exact (hj rfl).elim
    · exact excluded44_6
    · exact excluded44_7
    · exact excluded44_8
    · exact excluded44_9
theorem next44 : model44.insert step44 = model45 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded45_1 : ExcludedOn (model45.B 1 ++ [step45.q]) 9000000000000 (model45.caps 1)
    (model45.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_2 : ExcludedOn (model45.B 2 ++ [step45.q]) 9000000000000 (model45.caps 2)
    (model45.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_3 : ExcludedOn (model45.B 3 ++ [step45.q]) 9000000000000 (model45.caps 3)
    (model45.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_4 : ExcludedOn (model45.B 4 ++ [step45.q]) 9000000000000 (model45.caps 4)
    (model45.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4320000000000], [180000000000]) (some (7, 0, 5))
      (some (7, 8, 5)) (.next ([5745000000000], [375000000000]) (some (7, 8, 5)) (some (7, 8, 5))
      (.next ([1365000000000], [180000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next
      ([3165000000000], [705000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([4995000000000],
      [1185000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([180000000000], [60000000000])
      (some (7, 8, 5)) (some (7, 8, 5)) (.next ([3495000000000], [1320000000000]) (some (7, 8, 5))
      (some (7, 8, 5)) (.next ([3225000000000], [1455000000000]) (some (7, 8, 5)) (some (7, 8, 5))
      (.next ([2190000000000], [1050000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next
      ([1365000000000], [1080000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([3240000000000],
      [2625000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([3495000000000], [2955000000000])
      (some (7, 8, 5)) (some (7, 8, 5)) (.next ([1305000000000], [1320000000000]) (some (7, 8, 5))
      (some (7, 8, 5)) (.next ([1620000000000], [2070000000000]) (some (7, 8, 5)) (some (7, 8, 5))
      (.next ([3495000000000], [4560000000000]) (some (7, 8, 5)) (some (7, 8, 5))
      fan45Owner4Part1)))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_5 : ExcludedOn (model45.B 5 ++ [step45.q]) 9000000000000 (model45.caps 5)
    (model45.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [441000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([4440000000000], [2001000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4380000000000], [2061000000000]) (some (4, 1, 2)) (some (5, 1, 2)) (.next
      ([276000000000], [165000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4440000000000],
      [3540000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([4380000000000], [3540000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3999000000000], [3816000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([3939000000000], [3816000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([2901000000000], [3540000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([2625000000000], [3375000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0],
      [4380000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next ([-441000000000], [3816000000000])
      (some (5, 1, 4)) (some (5, 2, 4)) (.next ([-2001000000000], [6441000000000]) (some (5, 2, 4))
      (some (5, 2, 4)) (.next ([-2061000000000], [6441000000000]) (some (5, 2, 4)) (some (5, 2, 4))
      (.next ([-165000000000], [441000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-3540000000000], [7980000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-3540000000000], [7920000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-3816000000000], [7815000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-3816000000000], [7755000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-3540000000000], [6441000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-3375000000000], [6000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.terminal (some (5, 2,
      4)) (some (0, 2, 4)) (some (5, 2, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded45_6 : ExcludedOn (model45.B 6 ++ [step45.q]) 9000000000000 (model45.caps 6)
    (model45.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_7 : ExcludedOn (model45.B 7 ++ [step45.q]) 9000000000000 (model45.caps 7)
    (model45.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_8 : ExcludedOn (model45.B 8 ++ [step45.q]) 9000000000000 (model45.caps 8)
    (model45.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded45_9 : ExcludedOn (model45.B 9 ++ [step45.q]) 9000000000000 (model45.caps 9)
    (model45.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Sint320000330000
end ConwaySoifer.Simplified.Certificates
