/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext180000190000
import Mathlib.Tactic.FinCases

/-!
# Sext 180000 190000 7

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
namespace Sext180000190000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan56Owner3Part0 : FanWitness := (.next ([885000000000], [3810000000000]) (some (6, 0, 3)) (some
    (6, 1, 3)) (.next ([870000000000], [4320000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([375000000000], [4305000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([375000000000],
    [4950000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([0, 9000000000000], [2250000000000,
    -9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([0], [5955000000000]) (some (6, 1,
    3)) (some (6, 1, 4)) (.next ([-630000000000], [5580000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([-810000000000], [4080000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([-1080000000000], [3075000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1245000000000],
    [3195000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-2310000000000], [5760000000000])
    (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1620000000000], [3870000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-1875000000000, 0], [4305000000000, 9000000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-3000000000000], [6570000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-3705000000000], [7575000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-3330000000000, 9000000000000], [5325000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-1875000000000], [2685000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-5955000000000,
    0], [7575000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2385000000000],
    [3000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3810000000000], [4695000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4320000000000], [5190000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-4305000000000], [4680000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-4950000000000], [5325000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-2250000000000, 9000000000000], [2250000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal
    (some (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan58Owner3Part0 : FanWitness := (.next ([2430000000000], [6000000000000]) (some (5, 0, 3))
    (some (5, 0, 6)) (.next ([1620000000000, 9000000000000], [6000000000000]) (some (5, 0, 6)) (some
    (5, 0, 6)) (.next ([570000000000], [2430000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
    ([870000000000], [4320000000000]) (some (5, 0, 6)) (some (5, 1, 6)) (.next ([375000000000],
    [4950000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 9000000000000], [2250000000000,
    -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0], [6000000000000]) (some (5, 1,
    6)) (some (5, 1, 6)) (.next ([-570000000000], [6570000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-675000000000], [5625000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-1380000000000, 9000000000000], [6570000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-1080000000000], [3075000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1245000000000],
    [3195000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1620000000000], [3870000000000])
    (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-3000000000000], [6570000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-2520000000000], [5325000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-3750000000000], [7620000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-3330000000000, 9000000000000], [5325000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1440000000000], [2250000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-6000000000000],
    [8430000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-6000000000000, 0], [7620000000000,
    9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2430000000000], [3000000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4320000000000], [5190000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-4950000000000], [5325000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-2250000000000, 9000000000000], [2250000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.terminal (some (0, 2, 6)) (some (0, 2, 4)) (some (0, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan59Owner4Part0 : FanWitness := (.next ([3240000000000], [630000000000, -9000000000000]) (some
    (5, 1, 2)) (some (5, 1, 2)) (.next ([5490000000000], [1935000000000]) (some (4, 1, 2)) (some (4,
    1, 2)) (.next ([4875000000000], [1920000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
    ([3255000000000], [1620000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2250000000000],
    [1260000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3240000000000], [2250000000000])
    (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1620000000000], [1875000000000]) (some (4, 1, 2))
    (some (4, 1, 2)) (.next ([1620000000000, 9000000000000], [5130000000000, -9000000000000]) (some
    (4, 1, 2)) (some (4, 1, 2)) (.next ([1620000000000, 9000000000000], [5175000000000]) (some (4,
    1, 2)) (some (4, 1, 2)) (.next ([1575000000000], [5175000000000]) (some (4, 1, 2)) (some (4, 1,
    2)) (.next ([0, 9000000000000], [3255000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1,
    2)) (.next ([0], [5175000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-15000000000],
    [630000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-630000000000, 9000000000000],
    [3870000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1935000000000],
    [7425000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1920000000000], [6795000000000])
    (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1620000000000], [4875000000000]) (some (0, 1, 2))
    (some (0, 1, 2)) (.next ([-1260000000000], [3510000000000]) (some (0, 1, 2)) (some (0, 1, 2))
    (.next ([-2250000000000], [5490000000000]) (some (0, 1, 2)) (some (0, 1, 5)) (.next
    ([-1875000000000], [3495000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5130000000000,
    9000000000000], [6750000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5175000000000],
    [6795000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5175000000000],
    [6750000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3255000000000, 9000000000000],
    [3255000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5))
    (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan61Owner3Part0 : FanWitness := (.next ([1755000000000], [5625000000000]) (some (5, 0, 3))
    (some (5, 6, 3)) (.next ([750000000000], [2490000000000]) (some (5, 6, 3)) (some (5, 6, 3))
    (.next ([1620000000000, 9000000000000], [6000000000000]) (some (5, 6, 3)) (some (5, 6, 3))
    (.next ([375000000000], [4950000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([0,
    9000000000000], [3000000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([0],
    [6000000000000]) (some (5, 6, 3)) (some (5, 6, 4)) (.next ([-675000000000], [5625000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-330000000000], [2325000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-1005000000000], [4380000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-675000000000], [2055000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1620000000000], [4620000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3000000000000],
    [7620000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1425000000000], [3135000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3240000000000], [6750000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-4005000000000, 9000000000000], [7380000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3330000000000, 9000000000000], [5325000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3750000000000], [5130000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-1755000000000], [2385000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-4245000000000], [5625000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5625000000000],
    [7380000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2490000000000], [3240000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6000000000000, 0], [7620000000000, 9000000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4950000000000], [5325000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3000000000000, 9000000000000], [3000000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.terminal (some (0, 6, 4)) (some (0, 6, 4)) (some (0, 6,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan62Owner3Part0 : FanWitness := (.next ([1620000000000, 9000000000000], [6000000000000]) (some
    (5, 6, 3)) (some (5, 6, 3)) (.next ([375000000000], [4950000000000]) (some (5, 6, 3)) (some (5,
    6, 3)) (.next ([540000000000], [7710000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
    ([165000000000], [2760000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([0, 9000000000000],
    [3000000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([0], [6000000000000])
    (some (5, 6, 3)) (some (5, 6, 4)) (.next ([-675000000000], [5625000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-330000000000], [2325000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-1620000000000, 9000000000000], [6750000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-1620000000000], [4620000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-3000000000000], [7620000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1425000000000],
    [3135000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3240000000000], [6750000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3090000000000], [5250000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3330000000000, 9000000000000], [5325000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-2970000000000], [4470000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-5460000000000], [7710000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-3750000000000], [5130000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2490000000000],
    [3240000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6000000000000, 0], [7620000000000,
    9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4950000000000], [5325000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-7710000000000], [8250000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-2760000000000], [2925000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-3000000000000, 9000000000000], [3000000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.terminal (some (0, 6, 4)) (some (0, 6, 4)) (some (0, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan62Owner4Part0 : FanWitness := (.next ([5625000000000], [1620000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([960000000000], [750000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([870000000000], [1215000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([495000000000], [1125000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2535000000000],
    [5925000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1620000000000, 9000000000000],
    [5130000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1620000000000,
    9000000000000], [5175000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1575000000000],
    [5175000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([870000000000, 9000000000000],
    [6840000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([450000000000],
    [6795000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 9000000000000], [5625000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [5175000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([-750000000000], [8460000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-1620000000000], [7245000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-750000000000], [1710000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1215000000000],
    [2085000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1125000000000], [1620000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5925000000000], [8460000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-5130000000000, 9000000000000], [6750000000000]) (some (0, 1, 3))
    (some (0, 5, 3)) (.next ([-5175000000000], [6795000000000, 9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-5175000000000], [6750000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-6840000000000, 9000000000000], [7710000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-6795000000000], [7245000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-5625000000000, 9000000000000], [5625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal
    (some (0, 5, 3)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan63Owner0Part0 : FanWitness := (.next ([-4125000000000], [6480000000000]) (some (1, 5, 10))
    (some (1, 5, 10)) (.next ([-3795000000000], [5790000000000]) (some (1, 5, 10)) (some (1, 5, 10))
    (.next ([-2190000000000], [3315000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-360000000000], [540000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next ([-4500000000000],
    [6660000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next ([-4665000000000], [6660000000000])
    (some (1, 5, 10)) (some (1, 5, 10)) (.next ([-1290000000000], [1725000000000]) (some (1, 5, 10))
    (some (1, 5, 10)) (.next ([-7605000000000], [9660000000000]) (some (1, 5, 10)) (some (1, 5, 10))
    (.next ([-7695000000000], [9555000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-4545000000000], [5625000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-1290000000000], [1560000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-5415000000000], [6495000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-1995000000000], [2355000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-1455000000000], [1665000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-2190000000000], [2445000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-4065000000000], [4500000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-6105000000000], [6645000000000]) (some (1, 5, 10)) (some (2, 5, 10)) (.next
    ([-4935000000000], [5370000000000]) (some (2, 5, 10)) (some (2, 5, 10)) (.next
    ([-2805000000000], [2970000000000]) (some (2, 5, 10)) (some (2, 5, 10)) (.next
    ([-6195000000000], [6540000000000]) (some (2, 5, 10)) (some (2, 5, 10)) (.next
    ([-6480000000000], [6840000000000]) (some (2, 5, 10)) (some (2, 5, 10)) (.next
    ([-6570000000000], [6735000000000]) (some (2, 5, 10)) (some (2, 5, 10)) (.next
    ([-6855000000000], [7020000000000]) (some (2, 5, 10)) (some (2, 5, 10)) (.next
    ([-1275000000000], [1290000000000]) (some (2, 5, 10)) (some (2, 5, 10)) (.terminal (some (2, 5,
    10)) (some (2, 5, 10)) (some (2, 5, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan63Owner0Part1 : FanWitness := (.next ([-1110000000000], [7860000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([-165000000000], [1080000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    (.next ([-165000000000], [915000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-1560000000000], [7290000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-585000000000],
    [2640000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-1755000000000], [7380000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-750000000000], [2640000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([-1125000000000], [2820000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    (.next ([-480000000000], [1125000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-915000000000], [2100000000000]) (some (0, 4, 10)) (some (1, 4, 10)) (.next ([-180000000000],
    [375000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next ([-1500000000000], [3015000000000])
    (some (1, 4, 10)) (some (1, 4, 10)) (.next ([-375000000000], [750000000000]) (some (1, 4, 10))
    (some (1, 4, 10)) (.next ([-4380000000000], [8430000000000]) (some (1, 4, 10)) (some (1, 4, 10))
    (.next ([-195000000000], [375000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next
    ([-2880000000000], [5415000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next ([-105000000000],
    [195000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next ([-5250000000000], [9300000000000])
    (some (1, 4, 10)) (some (1, 5, 10)) (.next ([-1110000000000], [1920000000000]) (some (1, 5, 10))
    (some (1, 5, 10)) (.next ([-3255000000000], [5610000000000]) (some (1, 5, 10)) (some (1, 5, 10))
    (.next ([-540000000000], [915000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-3750000000000], [6285000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-1995000000000], [3225000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-3630000000000], [5790000000000]) (some (1, 5, 10)) (some (1, 5, 10))
    fan63Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan63Owner0Part2 : FanWitness := (.next ([1995000000000], [4665000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([435000000000], [1290000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([2055000000000], [7605000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([1860000000000], [7695000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([1080000000000],
    [4545000000000]) (some (10, 3, 5)) (some (10, 3, 10)) (.next ([270000000000], [1290000000000])
    (some (10, 3, 10)) (some (10, 3, 10)) (.next ([1080000000000], [5415000000000]) (some (10, 3,
    10)) (some (10, 3, 10)) (.next ([360000000000], [1995000000000]) (some (10, 3, 10)) (some (10,
    3, 10)) (.next ([210000000000], [1455000000000]) (some (10, 3, 10)) (some (10, 4, 10)) (.next
    ([255000000000], [2190000000000]) (some (10, 4, 10)) (some (10, 4, 10)) (.next ([435000000000],
    [4065000000000]) (some (10, 4, 10)) (some (10, 4, 10)) (.next ([540000000000], [6105000000000])
    (some (10, 4, 10)) (some (10, 4, 10)) (.next ([435000000000], [4935000000000]) (some (10, 4,
    10)) (some (10, 4, 10)) (.next ([165000000000], [2805000000000]) (some (10, 4, 10)) (some (10,
    4, 10)) (.next ([345000000000], [6195000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([360000000000], [6480000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([165000000000],
    [6570000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([165000000000], [6855000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([15000000000], [1275000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([0], [870000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-30000000000], [6945000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-195000000000],
    [7110000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-315000000000], [3930000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-915000000000], [7770000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) fan63Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan63Owner0Part3 : FanWitness := (.next ([5625000000000], [1755000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([1890000000000], [750000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([1695000000000], [1125000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([645000000000], [480000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([1185000000000],
    [915000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([195000000000], [180000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([1515000000000], [1500000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([375000000000], [375000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([4050000000000], [4380000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([180000000000], [195000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([2535000000000],
    [2880000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([90000000000], [105000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([4050000000000], [5250000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([810000000000], [1110000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([2355000000000], [3255000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([375000000000], [540000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([2535000000000],
    [3750000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([1230000000000], [1995000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([2160000000000], [3630000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([2355000000000], [4125000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([1995000000000], [3795000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([1125000000000], [2190000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([180000000000],
    [360000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([2160000000000], [4500000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) fan63Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan63Owner3Part0 : FanWitness := (.next ([1620000000000, 9000000000000], [6000000000000]) (some
    (5, 0, 6)) (some (5, 1, 6)) (.next ([375000000000], [4950000000000]) (some (5, 1, 6)) (some (5,
    1, 6)) (.next ([120000000000], [2805000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0,
    9000000000000], [3000000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0],
    [6000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-555000000000], [8430000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-675000000000], [5625000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-810000000000, 9000000000000], [6255000000000, -9000000000000]) (some
    (0, 1, 6)) (some (0, 1, 6)) (.next ([-330000000000], [2325000000000]) (some (0, 1, 4)) (some (0,
    1, 4)) (.next ([-1305000000000], [5940000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-1620000000000, 9000000000000], [6750000000000]) (some (0, 1, 4)) (some (0, 6, 4)) (.next
    ([-810000000000], [3255000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2430000000000],
    [7875000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1620000000000], [4620000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3000000000000], [7620000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-1425000000000], [3135000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-3240000000000], [6750000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-3330000000000, 9000000000000], [5325000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-3750000000000], [5130000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2490000000000],
    [3240000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6000000000000, 0], [7620000000000,
    9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4950000000000], [5325000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2805000000000], [2925000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3000000000000, 9000000000000], [3000000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.terminal (some (0, 6, 4)) (some (0, 6, 4)) (some (0, 6,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan63Owner3Part1 : FanWitness := (.next ([1620000000000, 9000000000000], [6000000000000]) (some
    (5, 0, 6)) (some (5, 1, 6)) (.next ([375000000000], [4950000000000]) (some (5, 1, 6)) (some (5,
    1, 6)) (.next ([120000000000], [2805000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0,
    9000000000000], [3000000000000, -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0],
    [6000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-555000000000], [8430000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-810000000000, 9000000000000], [6255000000000,
    -9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-675000000000], [5625000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-330000000000], [2325000000000]) (some (0, 1, 4))
    (some (0, 1, 4)) (.next ([-1305000000000], [5940000000000]) (some (0, 1, 4)) (some (0, 1, 4))
    (.next ([-1620000000000, 9000000000000], [6750000000000]) (some (0, 1, 4)) (some (0, 6, 4))
    (.next ([-810000000000], [3255000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-2430000000000], [7875000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1620000000000],
    [4620000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3000000000000], [7620000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1425000000000], [3135000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3240000000000], [6750000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-3330000000000, 9000000000000], [5325000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-3750000000000], [5130000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-2490000000000], [3240000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6000000000000,
    0], [7620000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4950000000000],
    [5325000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2805000000000], [2925000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3000000000000, 9000000000000], [3000000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.terminal (some (0, 6, 4)) (some (0, 6, 4)) (some (0, 6,
    4)))))))))))))))))))))))))))

theorem excluded56_0 : ExcludedOn (model56.B 0 ++ [step56.q]) 9000000000000 (model56.caps 0)
    (model56.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_1 : ExcludedOn (model56.B 1 ++ [step56.q]) 9000000000000 (model56.caps 1)
    (model56.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_2 : ExcludedOn (model56.B 2 ++ [step56.q]) 9000000000000 (model56.caps 2)
    (model56.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_3 : ExcludedOn (model56.B 3 ++ [step56.q]) 9000000000000 (model56.caps 3)
    (model56.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4950000000000], [630000000000]) (some (4, 0, 2))
      (some (5, 0, 2)) (.next ([3270000000000], [810000000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([1995000000000], [1080000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next
      ([1950000000000], [1245000000000]) (some (5, 0, 2)) (some (5, 0, 3)) (.next ([3450000000000],
      [2310000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([2250000000000], [1620000000000])
      (some (5, 0, 3)) (some (5, 0, 3)) (.next ([2430000000000, 9000000000000], [1875000000000])
      (some (5, 0, 3)) (some (5, 0, 3)) (.next ([3570000000000], [3000000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([3870000000000], [3705000000000]) (some (5, 0, 3)) (some (5, 0, 3))
      (.next ([1995000000000, 9000000000000], [3330000000000, -9000000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([810000000000], [1875000000000]) (some (5, 0, 3)) (some (5, 0, 3))
      (.next ([1620000000000, 9000000000000], [5955000000000]) (some (5, 0, 3)) (some (6, 0, 3))
      (.next ([615000000000], [2385000000000]) (some (6, 0, 3)) (some (6, 0, 3))
      fan56Owner3Part0)))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded56_4 : ExcludedOn (model56.B 4 ++ [step56.q]) 9000000000000 (model56.caps 4)
    (model56.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_5 : ExcludedOn (model56.B 5 ++ [step56.q]) 9000000000000 (model56.caps 5)
    (model56.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_6 : ExcludedOn (model56.B 6 ++ [step56.q]) 9000000000000 (model56.caps 6)
    (model56.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_7 : ExcludedOn (model56.B 7 ++ [step56.q]) 9000000000000 (model56.caps 7)
    (model56.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_9 : ExcludedOn (model56.B 9 ++ [step56.q]) 9000000000000 (model56.caps 9)
    (model56.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked56 : StepValid model56 9000000000000 step56 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded56_0
    · exact excluded56_1
    · exact excluded56_2
    · exact excluded56_3
    · exact excluded56_4
    · exact excluded56_5
    · exact excluded56_6
    · exact excluded56_7
    · exact (hj rfl).elim
    · exact excluded56_9
theorem next56 : model56.insert step56 = model57 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded57_0 : ExcludedOn (model57.B 0 ++ [step57.q]) 9000000000000 (model57.caps 0)
    (model57.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_1 : ExcludedOn (model57.B 1 ++ [step57.q]) 9000000000000 (model57.caps 1)
    (model57.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_2 : ExcludedOn (model57.B 2 ++ [step57.q]) 9000000000000 (model57.caps 2)
    (model57.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_4 : ExcludedOn (model57.B 4 ++ [step57.q]) 9000000000000 (model57.caps 4)
    (model57.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [1920000000000]) (some (5, 0,
      2)) (some (5, 1, 2)) (.next ([3255000000000], [1620000000000]) (some (5, 1, 2)) (some (5, 1,
      2)) (.next ([1620000000000], [1875000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([3000000000000], [3750000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1380000000000],
      [1875000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3000000000000], [5175000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1620000000000, 9000000000000], [5130000000000,
      -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1620000000000, 9000000000000],
      [5175000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1575000000000], [5175000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([0, 9000000000000], [3255000000000, -9000000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([0], [5175000000000]) (some (5, 1, 2)) (some (5, 1,
      2)) (.next ([-1920000000000], [6795000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-1620000000000], [4875000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-1875000000000], [3495000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3750000000000], [6750000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next
      ([-1875000000000], [3255000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-5175000000000], [8175000000000]) (some (0, 1, 3)) (some (0, 1, 5)) (.next ([-5130000000000,
      9000000000000], [6750000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5175000000000],
      [6795000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5175000000000],
      [6750000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-3255000000000, 9000000000000],
      [3255000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2,
      5)) (some (0, 2, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded57_5 : ExcludedOn (model57.B 5 ++ [step57.q]) 9000000000000 (model57.caps 5)
    (model57.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_6 : ExcludedOn (model57.B 6 ++ [step57.q]) 9000000000000 (model57.caps 6)
    (model57.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_7 : ExcludedOn (model57.B 7 ++ [step57.q]) 9000000000000 (model57.caps 7)
    (model57.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_8 : ExcludedOn (model57.B 8 ++ [step57.q]) 9000000000000 (model57.caps 8)
    (model57.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2865000000000], [135000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([3315000000000], [810000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([6000000000000], [3000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([3780000000000], [2220000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([2055000000000],
      [4260000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([465000000000], [1410000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1875000000000], [6315000000000]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([645000000000], [6135000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([0], [6135000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-135000000000],
      [3000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-810000000000], [4125000000000])
      (some (0, 1, 3)) (some (0, 4, 3)) (.next ([-3000000000000], [9000000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-2220000000000], [6000000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-4260000000000], [6315000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-1410000000000], [1875000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-6315000000000], [8190000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-6135000000000], [6780000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded57_9 : ExcludedOn (model57.B 9 ++ [step57.q]) 9000000000000 (model57.caps 9)
    (model57.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked57 : StepValid model57 9000000000000 step57 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded57_0
    · exact excluded57_1
    · exact excluded57_2
    · exact (hj rfl).elim
    · exact excluded57_4
    · exact excluded57_5
    · exact excluded57_6
    · exact excluded57_7
    · exact excluded57_8
    · exact excluded57_9
theorem next57 : model57.insert step57 = model58 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded58_0 : ExcludedOn (model58.B 0 ++ [step58.q]) 9000000000000 (model58.caps 0)
    (model58.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_1 : ExcludedOn (model58.B 1 ++ [step58.q]) 9000000000000 (model58.caps 1)
    (model58.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_3 : ExcludedOn (model58.B 3 ++ [step58.q]) 9000000000000 (model58.caps 3)
    (model58.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [570000000000]) (some (4, 0, 2))
      (some (5, 0, 2)) (.next ([4950000000000], [675000000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([5190000000000, 9000000000000], [1380000000000, -9000000000000]) (some (5, 0, 2))
      (some (5, 0, 2)) (.next ([1995000000000], [1080000000000]) (some (5, 0, 2)) (some (5, 0, 2))
      (.next ([1950000000000], [1245000000000]) (some (5, 0, 2)) (some (5, 0, 3)) (.next
      ([2250000000000], [1620000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([3570000000000],
      [3000000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([2805000000000], [2520000000000])
      (some (5, 0, 3)) (some (5, 0, 3)) (.next ([3870000000000], [3750000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([1995000000000, 9000000000000], [3330000000000, -9000000000000])
      (some (5, 0, 3)) (some (5, 0, 3)) (.next ([810000000000], [1440000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) fan58Owner3Part0)))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded58_4 : ExcludedOn (model58.B 4 ++ [step58.q]) 9000000000000 (model58.caps 4)
    (model58.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_5 : ExcludedOn (model58.B 5 ++ [step58.q]) 9000000000000 (model58.caps 5)
    (model58.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_6 : ExcludedOn (model58.B 6 ++ [step58.q]) 9000000000000 (model58.caps 6)
    (model58.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_7 : ExcludedOn (model58.B 7 ++ [step58.q]) 9000000000000 (model58.caps 7)
    (model58.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_8 : ExcludedOn (model58.B 8 ++ [step58.q]) 9000000000000 (model58.caps 8)
    (model58.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_9 : ExcludedOn (model58.B 9 ++ [step58.q]) 9000000000000 (model58.caps 9)
    (model58.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked58 : StepValid model58 9000000000000 step58 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded58_0
    · exact excluded58_1
    · exact (hj rfl).elim
    · exact excluded58_3
    · exact excluded58_4
    · exact excluded58_5
    · exact excluded58_6
    · exact excluded58_7
    · exact excluded58_8
    · exact excluded58_9
theorem next58 : model58.insert step58 = model59 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded59_0 : ExcludedOn (model59.B 0 ++ [step59.q]) 9000000000000 (model59.caps 0)
    (model59.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_1 : ExcludedOn (model59.B 1 ++ [step59.q]) 9000000000000 (model59.caps 1)
    (model59.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_2 : ExcludedOn (model59.B 2 ++ [step59.q]) 9000000000000 (model59.caps 2)
    (model59.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_4 : ExcludedOn (model59.B 4 ++ [step59.q]) 9000000000000 (model59.caps 4)
    (model59.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([615000000000], [15000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan59Owner4Part0)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded59_5 : ExcludedOn (model59.B 5 ++ [step59.q]) 9000000000000 (model59.caps 5)
    (model59.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_6 : ExcludedOn (model59.B 6 ++ [step59.q]) 9000000000000 (model59.caps 6)
    (model59.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_7 : ExcludedOn (model59.B 7 ++ [step59.q]) 9000000000000 (model59.caps 7)
    (model59.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_8 : ExcludedOn (model59.B 8 ++ [step59.q]) 9000000000000 (model59.caps 8)
    (model59.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_9 : ExcludedOn (model59.B 9 ++ [step59.q]) 9000000000000 (model59.caps 9)
    (model59.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked59 : StepValid model59 9000000000000 step59 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded59_0
    · exact excluded59_1
    · exact excluded59_2
    · exact (hj rfl).elim
    · exact excluded59_4
    · exact excluded59_5
    · exact excluded59_6
    · exact excluded59_7
    · exact excluded59_8
    · exact excluded59_9
theorem next59 : model59.insert step59 = model60 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded60_0 : ExcludedOn (model60.B 0 ++ [step60.q]) 9000000000000 (model60.caps 0)
    (model60.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_1 : ExcludedOn (model60.B 1 ++ [step60.q]) 9000000000000 (model60.caps 1)
    (model60.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_2 : ExcludedOn (model60.B 2 ++ [step60.q]) 9000000000000 (model60.caps 2)
    (model60.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000, 9000000000000], [1380000000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4950000000000], [1245000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4380000000000], [3000000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1950000000000], [2055000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([1995000000000, 9000000000000], [3330000000000, -9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([810000000000], [2190000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([1620000000000, 9000000000000], [6570000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([375000000000], [4950000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [6570000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1380000000000, 9000000000000],
      [7380000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-1245000000000],
      [6195000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3000000000000], [7380000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2055000000000], [4005000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-3330000000000, 9000000000000], [5325000000000, 0]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-2190000000000], [3000000000000]) (some (0, 1, 3)) (some (0, 2, 3))
      (.next ([-6570000000000, 0], [8190000000000, 9000000000000]) (some (0, 2, 3)) (some (4, 2, 3))
      (.next ([-4950000000000], [5325000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some
      (4, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded60_4 : ExcludedOn (model60.B 4 ++ [step60.q]) 9000000000000 (model60.caps 4)
    (model60.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_5 : ExcludedOn (model60.B 5 ++ [step60.q]) 9000000000000 (model60.caps 5)
    (model60.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_6 : ExcludedOn (model60.B 6 ++ [step60.q]) 9000000000000 (model60.caps 6)
    (model60.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_7 : ExcludedOn (model60.B 7 ++ [step60.q]) 9000000000000 (model60.caps 7)
    (model60.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_8 : ExcludedOn (model60.B 8 ++ [step60.q]) 9000000000000 (model60.caps 8)
    (model60.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_9 : ExcludedOn (model60.B 9 ++ [step60.q]) 9000000000000 (model60.caps 9)
    (model60.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked60 : StepValid model60 9000000000000 step60 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded60_0
    · exact excluded60_1
    · exact excluded60_2
    · exact (hj rfl).elim
    · exact excluded60_4
    · exact excluded60_5
    · exact excluded60_6
    · exact excluded60_7
    · exact excluded60_8
    · exact excluded60_9
theorem next60 : model60.insert step60 = model61 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded61_0 : ExcludedOn (model61.B 0 ++ [step61.q]) 9000000000000 (model61.caps 0)
    (model61.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_1 : ExcludedOn (model61.B 1 ++ [step61.q]) 9000000000000 (model61.caps 1)
    (model61.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_2 : ExcludedOn (model61.B 2 ++ [step61.q]) 9000000000000 (model61.caps 2)
    (model61.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_3 : ExcludedOn (model61.B 3 ++ [step61.q]) 9000000000000 (model61.caps 3)
    (model61.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4950000000000], [675000000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([1995000000000], [330000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([3375000000000], [1005000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([1380000000000], [675000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([3000000000000],
      [1620000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([4620000000000], [3000000000000])
      (some (5, 0, 3)) (some (5, 0, 3)) (.next ([1710000000000], [1425000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([3510000000000], [3240000000000]) (some (5, 0, 3)) (some (5, 0, 3))
      (.next ([3375000000000, 9000000000000], [4005000000000, -9000000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([1995000000000, 9000000000000], [3330000000000, -9000000000000])
      (some (5, 0, 3)) (some (5, 0, 3)) (.next ([1380000000000], [3750000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([630000000000], [1755000000000]) (some (5, 0, 3)) (some (5, 0, 3))
      (.next ([1380000000000], [4245000000000]) (some (5, 0, 3)) (some (5, 0, 3))
      fan61Owner3Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded61_5 : ExcludedOn (model61.B 5 ++ [step61.q]) 9000000000000 (model61.caps 5)
    (model61.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_6 : ExcludedOn (model61.B 6 ++ [step61.q]) 9000000000000 (model61.caps 6)
    (model61.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_7 : ExcludedOn (model61.B 7 ++ [step61.q]) 9000000000000 (model61.caps 7)
    (model61.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_8 : ExcludedOn (model61.B 8 ++ [step61.q]) 9000000000000 (model61.caps 8)
    (model61.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_9 : ExcludedOn (model61.B 9 ++ [step61.q]) 9000000000000 (model61.caps 9)
    (model61.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked61 : StepValid model61 9000000000000 step61 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded61_0
    · exact excluded61_1
    · exact excluded61_2
    · exact excluded61_3
    · exact (hj rfl).elim
    · exact excluded61_5
    · exact excluded61_6
    · exact excluded61_7
    · exact excluded61_8
    · exact excluded61_9
theorem next61 : model61.insert step61 = model62 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded62_1 : ExcludedOn (model62.B 1 ++ [step62.q]) 9000000000000 (model62.caps 1)
    (model62.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_2 : ExcludedOn (model62.B 2 ++ [step62.q]) 9000000000000 (model62.caps 2)
    (model62.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4950000000000], [1245000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([1995000000000, 9000000000000], [3330000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2970000000000], [5280000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([2910000000000, 9000000000000], [6630000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([915000000000], [3300000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1620000000000, 9000000000000], [6570000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1290000000000], [8250000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([375000000000], [4950000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0],
      [6570000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1245000000000], [6195000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-3330000000000, 9000000000000], [5325000000000, 0])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([-5280000000000], [8250000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-6630000000000, 9000000000000], [9540000000000, 0]) (some (0, 4, 3))
      (some (4, 4, 3)) (.next ([-3300000000000], [4215000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-6570000000000, 0], [8190000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-8250000000000], [9540000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-4950000000000], [5325000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded62_3 : ExcludedOn (model62.B 3 ++ [step62.q]) 9000000000000 (model62.caps 3)
    (model62.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4950000000000], [675000000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([1995000000000], [330000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([5130000000000, 9000000000000], [1620000000000, -9000000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([3000000000000], [1620000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([4620000000000], [3000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([1710000000000], [1425000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3510000000000],
      [3240000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([2160000000000], [3090000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1995000000000, 9000000000000], [3330000000000,
      -9000000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next ([1500000000000], [2970000000000])
      (some (5, 0, 3)) (some (5, 0, 3)) (.next ([2250000000000], [5460000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([1380000000000], [3750000000000]) (some (5, 0, 3)) (some (5, 6, 3))
      (.next ([750000000000], [2490000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      fan62Owner3Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded62_4 : ExcludedOn (model62.B 4 ++ [step62.q]) 9000000000000 (model62.caps 4)
    (model62.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7710000000000], [750000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan62Owner4Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded62_5 : ExcludedOn (model62.B 5 ++ [step62.q]) 9000000000000 (model62.caps 5)
    (model62.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_6 : ExcludedOn (model62.B 6 ++ [step62.q]) 9000000000000 (model62.caps 6)
    (model62.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_7 : ExcludedOn (model62.B 7 ++ [step62.q]) 9000000000000 (model62.caps 7)
    (model62.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_8 : ExcludedOn (model62.B 8 ++ [step62.q]) 9000000000000 (model62.caps 8)
    (model62.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_9 : ExcludedOn (model62.B 9 ++ [step62.q]) 9000000000000 (model62.caps 9)
    (model62.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked62 : StepValid model62 9000000000000 step62 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded62_1
    · exact excluded62_2
    · exact excluded62_3
    · exact excluded62_4
    · exact excluded62_5
    · exact excluded62_6
    · exact excluded62_7
    · exact excluded62_8
    · exact excluded62_9
theorem next62 : model62.insert step62 = model63 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded63_0 : ExcludedOn (model63.B 0 ++ [step63.q]) 9000000000000 (model63.caps 0)
    (model63.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6915000000000], [30000000000]) (some (10, 2, 5))
      (some (10, 3, 5)) (.next ([6915000000000], [195000000000]) (some (10, 3, 5)) (some (10, 3, 5))
      (.next ([3615000000000], [315000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
      ([6855000000000], [915000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([6750000000000],
      [1110000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([915000000000], [165000000000])
      (some (10, 3, 5)) (some (10, 3, 5)) (.next ([750000000000], [165000000000]) (some (10, 3, 5))
      (some (10, 3, 5)) (.next ([5730000000000], [1560000000000]) (some (10, 3, 5)) (some (10, 3,
      5)) (.next ([2055000000000], [585000000000]) (some (10, 3, 5)) (some (10, 3, 5))
      fan63Owner0Part3))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded63_1 : ExcludedOn (model63.B 1 ++ [step63.q]) 9000000000000 (model63.caps 1)
    (model63.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3015000000000, -9000000000000], [810000000000,
      9000000000000]) (some (4, 4, 1)) (some (4, 4, 2)) (.next ([2430000000000, 9000000000000],
      [2205000000000, -9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([5175000000000,
      9000000000000], [4950000000000, -9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([2745000000000], [2745000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([3555000000000],
      [6570000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1935000000000, -9000000000000],
      [6570000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([810000000000], [3825000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [1620000000000, 9000000000000]) (some (4, 1,
      2)) (some (4, 1, 2)) (.next ([-810000000000, -9000000000000], [3825000000000, 0]) (some (4, 1,
      2)) (some (4, 1, 3)) (.next ([-2205000000000, 9000000000000], [4635000000000]) (some (4, 1,
      3)) (some (4, 1, 3)) (.next ([-4950000000000, 9000000000000], [10125000000000]) (some (4, 1,
      3)) (some (4, 1, 3)) (.next ([-2745000000000], [5490000000000]) (some (4, 1, 3)) (some (4, 1,
      3)) (.next ([-6570000000000], [10125000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-6570000000000, 0], [8505000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-3825000000000], [4635000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.terminal (some
      (4, 1, 4)) (some (4, 1, 4)) (some (4, 1, 4))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded63_3 : ExcludedOn (model63.B 3 ++ [step63.q]) 9000000000000 (model63.caps 3)
    (model63.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (3) (4) (400) (.witnessedFan (.next ([7875000000000],
      [555000000000]) (some (4, 0, 6)) (some (5, 0, 6)) (.next ([4950000000000], [675000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([5445000000000, 0], [810000000000, -9000000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1995000000000], [330000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([4635000000000], [1305000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([5130000000000, 9000000000000], [1620000000000, -9000000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([2445000000000], [810000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([5445000000000], [2430000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([3000000000000], [1620000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([4620000000000],
      [3000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1710000000000], [1425000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3510000000000], [3240000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([1995000000000, 9000000000000], [3330000000000, -9000000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1380000000000], [3750000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([750000000000], [2490000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      fan63Owner3Part0)))))))))))))))) (.witnessedFan (.next ([7875000000000], [555000000000]) (some
      (4, 0, 6)) (some (5, 0, 6)) (.next ([5445000000000, 0], [810000000000, -9000000000000]) (some
      (5, 0, 6)) (some (5, 0, 6)) (.next ([4950000000000], [675000000000]) (some (5, 0, 6)) (some
      (5, 0, 6)) (.next ([1995000000000], [330000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([4635000000000], [1305000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([5130000000000,
      9000000000000], [1620000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([2445000000000], [810000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([5445000000000],
      [2430000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3000000000000], [1620000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([4620000000000], [3000000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([1710000000000], [1425000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([3510000000000], [3240000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([1995000000000, 9000000000000], [3330000000000, -9000000000000]) (some (5, 0, 6)) (some (5,
      0, 6)) (.next ([1380000000000], [3750000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([750000000000], [2490000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      fan63Owner3Part1))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded63_4 : ExcludedOn (model63.B 4 ++ [step63.q]) 9000000000000 (model63.caps 4)
    (model63.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_5 : ExcludedOn (model63.B 5 ++ [step63.q]) 9000000000000 (model63.caps 5)
    (model63.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_6 : ExcludedOn (model63.B 6 ++ [step63.q]) 9000000000000 (model63.caps 6)
    (model63.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_7 : ExcludedOn (model63.B 7 ++ [step63.q]) 9000000000000 (model63.caps 7)
    (model63.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_8 : ExcludedOn (model63.B 8 ++ [step63.q]) 9000000000000 (model63.caps 8)
    (model63.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_9 : ExcludedOn (model63.B 9 ++ [step63.q]) 9000000000000 (model63.caps 9)
    (model63.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked63 : StepValid model63 9000000000000 step63 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded63_0
    · exact excluded63_1
    · exact (hj rfl).elim
    · exact excluded63_3
    · exact excluded63_4
    · exact excluded63_5
    · exact excluded63_6
    · exact excluded63_7
    · exact excluded63_8
    · exact excluded63_9
theorem next63 : model63.insert step63 = model64 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext180000190000
end ConwaySoifer.Simplified.Certificates
