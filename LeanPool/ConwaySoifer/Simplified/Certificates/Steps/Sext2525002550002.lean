/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext252500255000
import Mathlib.Tactic.FinCases

/-!
# Sext 252500 255000 2

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
namespace Sext252500255000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part0 : FanWitness := (.next ([-1481250000000], [6731250000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-1481250000000], [6345000000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-1511250000000], [6045750000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1125000000000], [4148250000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1893750000000], [6768750000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1893750000000], [6382500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-750000000000],
    [2272500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1886250000000], [5670750000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1511250000000], [4534500000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-1886250000000], [5284500000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-375000000000], [750000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-5254500000000], [10129500000000]) (some (10, 3, 6)) (some (10, 3, 7)) (.next
    ([-5667000000000], [10167000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([-761250000000], [1136250000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-1511250000000],
    [1897500000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-5208750000000], [6000000000000])
    (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-5595000000000], [6386250000000]) (some (10, 3, 7))
    (some (10, 3, 7)) (.next ([-375000000000], [412500000000]) (some (10, 3, 7)) (some (10, 3, 7))
    (.next ([-5246250000000], [5625000000000]) (some (10, 3, 7)) (some (10, 4, 7)) (.next
    ([-5632500000000], [6011250000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6345000000000], [6761250000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6731250000000], [6761250000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-3773250000000], [3784500000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6382500000000], [6386250000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.terminal (some (10, 4,
    7)) (some (10, 4, 7)) (some (10, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner0Part1 : FanWitness := (.next ([3398250000000], [1886250000000]) (some (8, 10, 4))
    (some (8, 10, 4)) (.next ([375000000000], [375000000000]) (some (8, 10, 4)) (some (10, 10, 4))
    (.next ([4875000000000], [5254500000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next
    ([4500000000000], [5667000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([375000000000],
    [761250000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([386250000000], [1511250000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([791250000000], [5208750000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([791250000000], [5595000000000]) (some (10, 3, 4)) (some (10, 3, 4))
    (.next ([37500000000], [375000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([378750000000], [5246250000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([378750000000],
    [5632500000000]) (some (10, 3, 4)) (some (10, 3, 5)) (.next ([416250000000], [6345000000000])
    (some (10, 3, 5)) (some (10, 3, 5)) (.next ([30000000000], [6731250000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([11250000000], [3773250000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([3750000000], [6382500000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([0],
    [1897500000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-382500000000], [6768750000000])
    (some (10, 3, 5)) (some (10, 3, 6)) (.next ([-375000000000], [3773250000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-720000000000], [7106250000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-1106250000000], [7106250000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1132500000000], [7143750000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1125000000000], [6045750000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-386250000000],
    [1897500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1518750000000], [7143750000000])
    (some (10, 3, 6)) (some (10, 3, 6)) fan19Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part0 : FanWitness := (.next ([-386250000000], [1897500000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-1518750000000], [7143750000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-1481250000000], [6731250000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1481250000000], [6345000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1893750000000], [6768750000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-1893750000000], [6382500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-750000000000],
    [2272500000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-3720000000000], [10060500000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-4132500000000], [10098000000000]) (some (10, 3,
    6)) (some (10, 3, 6)) (.next ([-375000000000], [750000000000]) (some (10, 3, 6)) (some (10, 3,
    6)) (.next ([-2238750000000], [3715500000000]) (some (10, 3, 6)) (some (10, 3, 7)) (.next
    ([-761250000000], [1136250000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-2238750000000],
    [3329250000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-1511250000000], [1897500000000])
    (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-5208750000000], [6000000000000]) (some (10, 3, 7))
    (some (10, 3, 7)) (.next ([-5595000000000], [6386250000000]) (some (10, 3, 7)) (some (10, 3, 7))
    (.next ([-2613750000000], [2954250000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([-375000000000], [412500000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([-4511250000000],
    [4851750000000]) (some (10, 3, 7)) (some (10, 4, 7)) (.next ([-5246250000000], [5625000000000])
    (some (10, 4, 7)) (some (10, 4, 7)) (.next ([-5632500000000], [6011250000000]) (some (10, 4, 7))
    (some (10, 4, 7)) (.next ([-6345000000000], [6761250000000]) (some (10, 4, 7)) (some (10, 4, 7))
    (.next ([-6731250000000], [6761250000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([-6382500000000], [6386250000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.terminal (some (10, 4,
    7)) (some (10, 4, 7)) (some (10, 4, 7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner0Part1 : FanWitness := (.next ([375000000000], [375000000000]) (some (10, 3, 4)) (some
    (10, 3, 4)) (.next ([1476750000000], [2238750000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([375000000000], [761250000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([1090500000000],
    [2238750000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([386250000000], [1511250000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([791250000000], [5208750000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([791250000000], [5595000000000]) (some (10, 3, 4)) (some (10, 3, 4))
    (.next ([340500000000], [2613750000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([37500000000], [375000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([340500000000],
    [4511250000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([378750000000], [5246250000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([378750000000], [5632500000000]) (some (10, 3, 4))
    (some (10, 3, 5)) (.next ([416250000000], [6345000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([30000000000], [6731250000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
    ([3750000000], [6382500000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([0],
    [1897500000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([-45750000000], [4511250000000])
    (some (10, 3, 5)) (some (10, 3, 6)) (.next ([-45750000000], [3000000000000]) (some (10, 3, 6))
    (some (10, 3, 6)) (.next ([-382500000000], [6768750000000]) (some (10, 3, 6)) (some (10, 3, 6))
    (.next ([-720000000000], [7106250000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next
    ([-420750000000], [4136250000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-420750000000],
    [3750000000000]) (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1106250000000], [7106250000000])
    (some (10, 3, 6)) (some (10, 3, 6)) (.next ([-1132500000000], [7143750000000]) (some (10, 3, 6))
    (some (10, 3, 6)) fan20Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner0Part0 : FanWitness := (.next ([-1518750000000], [7143750000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([-1481250000000], [6731250000000]) (some (0, 3, 10)) (some (0, 3, 10))
    (.next ([-1140000000000], [4886250000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-1481250000000], [6345000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-753750000000],
    [2988750000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-1893750000000], [6768750000000])
    (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-1893750000000], [6382500000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([-750000000000], [2272500000000]) (some (0, 3, 10)) (some (0, 3, 10))
    (.next ([-1140000000000], [2988750000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-375000000000], [750000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-1890000000000],
    [3363750000000]) (some (0, 3, 10)) (some (1, 3, 10)) (.next ([-2276250000000], [3750000000000])
    (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-761250000000], [1136250000000]) (some (1, 3, 10))
    (some (1, 3, 10)) (.next ([-7485000000000], [9750000000000]) (some (1, 3, 10)) (some (1, 3, 10))
    (.next ([-1511250000000], [1897500000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-7522500000000], [9375000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-5208750000000], [6000000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-5595000000000], [6386250000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-375000000000],
    [412500000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-5246250000000], [5625000000000])
    (some (1, 3, 10)) (some (1, 4, 10)) (.next ([-5632500000000], [6011250000000]) (some (1, 4, 10))
    (some (1, 4, 10)) (.next ([-6345000000000], [6761250000000]) (some (1, 4, 10)) (some (1, 4, 10))
    (.next ([-6731250000000], [6761250000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next
    ([-6382500000000], [6386250000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.terminal (some (1, 4,
    10)) (some (1, 4, 10)) (some (1, 4, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner0Part1 : FanWitness := (.next ([375000000000], [375000000000]) (some (10, 3, 4)) (some
    (10, 3, 4)) (.next ([1473750000000], [1890000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
    ([1473750000000], [2276250000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([375000000000],
    [761250000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([2265000000000], [7485000000000])
    (some (10, 3, 4)) (some (10, 3, 4)) (.next ([386250000000], [1511250000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([1852500000000], [7522500000000]) (some (10, 3, 4)) (some (10, 3, 4))
    (.next ([791250000000], [5208750000000]) (some (10, 3, 4)) (some (10, 3, 10)) (.next
    ([791250000000], [5595000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next ([37500000000],
    [375000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next ([378750000000], [5246250000000])
    (some (10, 3, 10)) (some (10, 3, 10)) (.next ([378750000000], [5632500000000]) (some (10, 3,
    10)) (some (10, 3, 10)) (.next ([416250000000], [6345000000000]) (some (10, 3, 10)) (some (10,
    3, 10)) (.next ([30000000000], [6731250000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next
    ([3750000000], [6382500000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next ([0],
    [1897500000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next ([-382500000000], [6768750000000])
    (some (10, 3, 10)) (some (10, 3, 10)) (.next ([-378750000000], [3750000000000]) (some (10, 3,
    10)) (some (10, 3, 10)) (.next ([-720000000000], [7106250000000]) (some (0, 3, 10)) (some (0, 3,
    10)) (.next ([-378750000000], [3363750000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-1106250000000], [7106250000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-1132500000000], [7143750000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-753750000000],
    [4500000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-386250000000], [1897500000000])
    (some (0, 3, 10)) (some (0, 3, 10)) fan21Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part0 : FanWitness := (.next ([-1518750000000], [7143750000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([-1481250000000], [6731250000000]) (some (0, 3, 10)) (some (0, 3, 10))
    (.next ([-1481250000000], [6345000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-1893750000000], [6768750000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-1170750000000], [4125000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-1893750000000], [6382500000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-750000000000],
    [2272500000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-375000000000], [750000000000])
    (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-6379500000000], [10125000000000]) (some (0, 3,
    10)) (some (1, 3, 10)) (.next ([-6417000000000], [9750000000000]) (some (1, 3, 10)) (some (1, 3,
    10)) (.next ([-761250000000], [1136250000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-1511250000000], [1897500000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-3738750000000], [4465500000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-4125000000000], [4851750000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-5208750000000], [6000000000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-5595000000000], [6386250000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next
    ([-3363750000000], [3715500000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-375000000000],
    [412500000000]) (some (1, 3, 10)) (some (1, 3, 10)) (.next ([-5246250000000], [5625000000000])
    (some (1, 3, 10)) (some (1, 4, 10)) (.next ([-4875000000000], [5226750000000]) (some (1, 4, 10))
    (some (1, 4, 10)) (.next ([-5632500000000], [6011250000000]) (some (1, 4, 10)) (some (1, 4, 10))
    (.next ([-6345000000000], [6761250000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next
    ([-6731250000000], [6761250000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next
    ([-6382500000000], [6386250000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.terminal (some (1, 4,
    10)) (some (1, 4, 10)) (some (1, 4, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner0Part1 : FanWitness := (.next ([3333000000000], [6417000000000]) (some (10, 3, 4))
    (some (10, 3, 4)) (.next ([375000000000], [761250000000]) (some (10, 3, 4)) (some (10, 3, 10))
    (.next ([386250000000], [1511250000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next
    ([726750000000], [3738750000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next ([726750000000],
    [4125000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([791250000000], [5208750000000])
    (some (9, 3, 10)) (some (9, 3, 10)) (.next ([791250000000], [5595000000000]) (some (9, 3, 10))
    (some (9, 3, 10)) (.next ([351750000000], [3363750000000]) (some (9, 3, 10)) (some (9, 3, 10))
    (.next ([37500000000], [375000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next
    ([378750000000], [5246250000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([351750000000],
    [4875000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([378750000000], [5632500000000])
    (some (9, 3, 10)) (some (9, 3, 10)) (.next ([416250000000], [6345000000000]) (some (9, 3, 10))
    (some (9, 3, 10)) (.next ([30000000000], [6731250000000]) (some (9, 3, 10)) (some (9, 3, 10))
    (.next ([3750000000], [6382500000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([0],
    [1897500000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([-34500000000], [5261250000000])
    (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-34500000000], [3363750000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([-382500000000], [6768750000000]) (some (0, 3, 10)) (some (0, 3, 10))
    (.next ([-720000000000], [7106250000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-1106250000000], [7106250000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([-1132500000000], [7143750000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-386250000000],
    [1897500000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([-784500000000], [3738750000000])
    (some (0, 3, 10)) (some (0, 3, 10)) fan22Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner4Part0 : FanWitness := (.next ([-49500000000], [6049500000000]) (some (7, 1, 4)) (some
    (7, 1, 4)) (.next ([-715500000000], [5625000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([-1140000000000], [6412500000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-352500000000],
    [1909500000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-750000000000], [2659500000000])
    (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-1909500000000], [6000000000000]) (some (7, 1, 4))
    (some (7, 1, 4)) (.next ([-1818000000000, 9000000000000], [4840500000000]) (some (7, 1, 4))
    (some (7, 1, 4)) (.next ([-2272500000000], [5272500000000]) (some (7, 1, 4)) (some (7, 1, 4))
    (.next ([-4090500000000], [9055500000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([-2272500000000, -9000000000000], [4215000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([-1840500000000], [3022500000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-5625000000000],
    [9124500000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-4140000000000], [6412500000000,
    9000000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-727500000000], [1090500000000])
    (some (7, 1, 4)) (some (7, 1, 4)) (.next ([-3352500000000, 9000000000000], [4909500000000])
    (some (7, 1, 4)) (some (7, 1, 5)) (.next ([-819000000000], [1194000000000]) (some (7, 1, 5))
    (some (7, 1, 5)) (.next ([-6000000000000], [8305500000000]) (some (7, 1, 5)) (some (7, 1, 5))
    (.next ([-5272500000000], [7215000000000]) (some (7, 1, 5)) (some (7, 1, 5)) (.next
    ([-3390000000000], [4090500000000]) (some (7, 1, 5)) (some (7, 1, 7)) (.next ([-4090500000000],
    [4840500000000]) (some (7, 1, 7)) (some (7, 2, 7)) (.next ([-4855500000000], [5625000000000])
    (some (7, 2, 7)) (some (7, 2, 7)) (.next ([-3727500000000, 9000000000000], [4090500000000])
    (some (7, 2, 7)) (some (7, 2, 7)) (.next ([-1465500000000], [1534500000000]) (some (7, 2, 7))
    (some (7, 2, 7)) (.next ([-3000000000000, 9000000000000], [3000000000000]) (some (7, 2, 7))
    (some (7, 3, 7)) (.terminal (some (7, 3, 7)) (some (0, 3, 7)) (some (7, 3,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner4Part1 : FanWitness := (.next ([4909500000000], [715500000000]) (some (7, 1, 3)) (some
    (7, 1, 3)) (.next ([5272500000000], [1140000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
    ([1557000000000], [352500000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([1909500000000],
    [750000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([4090500000000], [1909500000000])
    (some (7, 1, 3)) (some (7, 1, 3)) (.next ([3022500000000, 9000000000000], [1818000000000,
    -9000000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([3000000000000], [2272500000000])
    (some (7, 1, 3)) (some (7, 1, 3)) (.next ([4965000000000], [4090500000000]) (some (7, 1, 3))
    (some (7, 1, 3)) (.next ([1942500000000, -9000000000000], [2272500000000, 9000000000000]) (some
    (7, 1, 3)) (some (7, 1, 3)) (.next ([1182000000000], [1840500000000]) (some (7, 1, 3)) (some (7,
    1, 3)) (.next ([3499500000000], [5625000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
    ([2272500000000, 9000000000000], [4140000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
    ([363000000000], [727500000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([1557000000000,
    9000000000000], [3352500000000, -9000000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next
    ([375000000000], [819000000000]) (some (7, 1, 3)) (some (7, 1, 3)) (.next ([2305500000000],
    [6000000000000]) (some (7, 1, 3)) (some (7, 1, 4)) (.next ([1942500000000], [5272500000000])
    (some (7, 1, 4)) (some (7, 1, 4)) (.next ([700500000000], [3390000000000]) (some (7, 1, 4))
    (some (7, 1, 4)) (.next ([750000000000], [4090500000000]) (some (7, 1, 4)) (some (7, 1, 4))
    (.next ([769500000000], [4855500000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
    ([363000000000, 9000000000000], [3727500000000, -9000000000000]) (some (7, 1, 4)) (some (7, 1,
    4)) (.next ([69000000000], [1465500000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([0,
    9000000000000], [3000000000000, -9000000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([0],
    [4140000000000]) (some (7, 1, 4)) (some (7, 1, 4)) fan23Owner4Part0))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded16_3 : ExcludedOn (model16.B 3 ++ [step16.q]) 9000000000000 (model16.caps 3)
    (model16.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3585000000000], [142500000000]) (some (2, 4, 1))
      (some (3, 4, 1)) (.next ([6000000000000, 9000000000000], [727500000000, -9000000000000]) (some
      (3, 4, 1)) (some (3, 4, 1)) (.next ([4312500000000, -9000000000000], [2272500000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([3727500000000], [3000000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2272500000000, 9000000000000], [2272500000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2272500000000, 9000000000000],
      [4312500000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1455000000000,
      -9000000000000], [3000000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([0],
      [2272500000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-142500000000],
      [3727500000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-727500000000, 9000000000000],
      [6727500000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2272500000000, -9000000000000],
      [6585000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3000000000000], [6727500000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2272500000000, -9000000000000], [4545000000000,
      18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4312500000000, 9000000000000],
      [6585000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3000000000000], [4455000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (4, 1,
      2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded16_9 : ExcludedOn (model16.B 9 ++ [step16.q]) 9000000000000 (model16.caps 9)
    (model16.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked16 : StepValid model16 9000000000000 step16 0 1 400 := by
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
    (model17.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded17_3 : ExcludedOn (model17.B 3 ++ [step17.q]) 9000000000000 (model17.caps 3)
    (model17.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2494500000000], [505500000000]) (some (2, 4, 1))
      (some (3, 4, 1)) (.next ([5272500000000, 9000000000000], [1818000000000, -9000000000000])
      (some (3, 4, 1)) (some (3, 4, 1)) (.next ([4312500000000, -9000000000000], [2272500000000,
      9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2272500000000, 9000000000000],
      [2272500000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([3000000000000],
      [4090500000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2272500000000, 9000000000000],
      [4312500000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([727500000000,
      -9000000000000], [4090500000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([0],
      [2272500000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-505500000000],
      [3000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1818000000000, 9000000000000],
      [7090500000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2272500000000, -9000000000000],
      [6585000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2272500000000, -9000000000000],
      [4545000000000, 18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4090500000000],
      [7090500000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4312500000000, 9000000000000],
      [6585000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4090500000000], [4818000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (4, 1,
      2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded17_9 : ExcludedOn (model17.B 9 ++ [step17.q]) 9000000000000 (model17.caps 9)
    (model17.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked17 : StepValid model17 9000000000000 step17 0 1 400 := by
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
    (model18.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.pair 3 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded18_5 : ExcludedOn (model18.B 5 ++ [step18.q]) 9000000000000 (model18.caps 5)
    (model18.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4909500000000], [375000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([375000000000], [160500000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4860000000000], [5445000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([4485000000000], [5284500000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2272500000000,
      9000000000000], [5445000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1897500000000,
      9000000000000], [5284500000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0, 0],
      [2272500000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-375000000000],
      [5284500000000]) (some (4, 1, 2)) (some (4, 2, 2)) (.next ([-160500000000], [535500000000])
      (some (4, 2, 2)) (some (4, 2, 2)) (.next ([-5445000000000], [10305000000000]) (some (4, 2, 2))
      (some (4, 2, 3)) (.next ([-5284500000000], [9769500000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-5445000000000, 0], [7717500000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 4))
      (.next ([-5284500000000, 0], [7182000000000, 9000000000000]) (some (4, 2, 4)) (some (4, 2, 4))
      (.terminal (some (4, 2, 4)) (some (0, 2, 4)) (some (4, 2, 4))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded18_9 : ExcludedOn (model18.B 9 ++ [step18.q]) 9000000000000 (model18.caps 9)
    (model18.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked18 : StepValid model18 9000000000000 step18 0 1 400 := by
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
    (model19.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6386250000000], [382500000000]) (some (7, 10,
      4)) (some (8, 10, 4)) (.next ([3398250000000], [375000000000]) (some (8, 10, 4)) (some (8, 10,
      4)) (.next ([6386250000000], [720000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([6000000000000], [1106250000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([6011250000000], [1132500000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([4920750000000], [1125000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([1511250000000], [386250000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([5625000000000],
      [1518750000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([5250000000000], [1481250000000])
      (some (8, 10, 4)) (some (8, 10, 4)) (.next ([4863750000000], [1481250000000]) (some (8, 10,
      4)) (some (8, 10, 4)) (.next ([4534500000000], [1511250000000]) (some (8, 10, 4)) (some (8,
      10, 4)) (.next ([3023250000000], [1125000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([4875000000000], [1893750000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([4488750000000], [1893750000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([1522500000000], [750000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([3784500000000],
      [1886250000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([3023250000000], [1511250000000])
      (some (8, 10, 4)) (some (8, 10, 4)) fan19Owner0Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7182000000000, 9000000000000], [2568000000000,
      -9000000000000]) (some (2, 4, 1)) (some (3, 4, 1)) (.next ([4312500000000, -9000000000000],
      [2272500000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([4909500000000],
      [4840500000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2272500000000, 9000000000000],
      [2272500000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1744500000000],
      [3165000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2637000000000, -9000000000000],
      [4840500000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2272500000000, 9000000000000],
      [4312500000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([0],
      [2272500000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([-2568000000000,
      9000000000000], [9750000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2272500000000,
      -9000000000000], [6585000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4840500000000],
      [9750000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2272500000000, -9000000000000],
      [4545000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-3165000000000],
      [4909500000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4840500000000], [7477500000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4312500000000, 9000000000000],
      [6585000000000]) (some (0, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1, 2)) (some (4, 1,
      2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded19_9 : ExcludedOn (model19.B 9 ++ [step19.q]) 9000000000000 (model19.caps 9)
    (model19.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked19 : StepValid model19 9000000000000 step19 0 1 400 := by
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
    (model20.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4465500000000], [45750000000]) (some (7, 10, 4))
      (some (8, 10, 4)) (.next ([2954250000000], [45750000000]) (some (8, 10, 4)) (some (8, 10, 4))
      (.next ([6386250000000], [382500000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next
      ([6386250000000], [720000000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([3715500000000],
      [420750000000]) (some (8, 10, 4)) (some (8, 10, 4)) (.next ([3329250000000], [420750000000])
      (some (8, 10, 4)) (some (8, 10, 4)) (.next ([6000000000000], [1106250000000]) (some (8, 10,
      4)) (some (10, 10, 4)) (.next ([6011250000000], [1132500000000]) (some (10, 10, 4)) (some (10,
      10, 4)) (.next ([1511250000000], [386250000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next
      ([5625000000000], [1518750000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next
      ([5250000000000], [1481250000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next
      ([4863750000000], [1481250000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next
      ([4875000000000], [1893750000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next
      ([4488750000000], [1893750000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next
      ([1522500000000], [750000000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next
      ([6340500000000], [3720000000000]) (some (10, 10, 4)) (some (10, 10, 4)) (.next
      ([5965500000000], [4132500000000]) (some (10, 3, 4)) (some (10, 3, 4))
      fan20Owner0Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5647500000000, 9000000000000], [2637000000000,
      -9000000000000]) (some (2, 4, 1)) (some (3, 4, 1)) (.next ([4312500000000, -9000000000000],
      [2272500000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2272500000000,
      9000000000000], [2272500000000, 9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next
      ([1675500000000], [1699500000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([3375000000000],
      [4909500000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([2272500000000, 9000000000000],
      [4312500000000, -9000000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([1102500000000,
      -9000000000000], [4909500000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([0],
      [2272500000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-2637000000000,
      9000000000000], [8284500000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2272500000000,
      -9000000000000], [6585000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-2272500000000,
      -9000000000000], [4545000000000, 18000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1699500000000], [3375000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4909500000000], [8284500000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4312500000000,
      9000000000000], [6585000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4909500000000],
      [6012000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2))
      (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded20_8 : ExcludedOn (model20.B 8 ++ [step20.q]) 9000000000000 (model20.caps 8)
    (model20.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded20_9 : ExcludedOn (model20.B 9 ++ [step20.q]) 9000000000000 (model20.caps 9)
    (model20.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked20 : StepValid model20 9000000000000 step20 0 1 400 := by
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
    · exact (hj rfl).elim
    · exact excluded20_5
    · exact excluded20_6
    · exact excluded20_7
    · exact excluded20_8
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6386250000000], [382500000000]) (some (10, 1,
      4)) (some (10, 2, 4)) (.next ([3371250000000], [378750000000]) (some (10, 2, 4)) (some (10, 2,
      4)) (.next ([6386250000000], [720000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
      ([2985000000000], [378750000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([6000000000000],
      [1106250000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([6011250000000], [1132500000000])
      (some (10, 2, 4)) (some (10, 2, 4)) (.next ([3746250000000], [753750000000]) (some (10, 2, 4))
      (some (10, 2, 4)) (.next ([1511250000000], [386250000000]) (some (10, 2, 4)) (some (10, 2, 4))
      (.next ([5625000000000], [1518750000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
      ([5250000000000], [1481250000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
      ([3746250000000], [1140000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
      ([4863750000000], [1481250000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
      ([2235000000000], [753750000000]) (some (10, 2, 4)) (some (10, 3, 4)) (.next ([4875000000000],
      [1893750000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([4488750000000], [1893750000000])
      (some (10, 3, 4)) (some (10, 3, 4)) (.next ([1522500000000], [750000000000]) (some (10, 3, 4))
      (some (10, 3, 4)) (.next ([1848750000000], [1140000000000]) (some (10, 3, 4)) (some (10, 3,
      4)) fan21Owner0Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000, 0], [337500000000,
      -9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([4312500000000, -9000000000000],
      [2272500000000, 9000000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([4875000000000],
      [2610000000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([2272500000000, 9000000000000],
      [2272500000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2272500000000,
      9000000000000], [4312500000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([900000000000], [1710000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [2272500000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([-337500000000,
      9000000000000], [5212500000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-2272500000000, -9000000000000], [6585000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2610000000000], [7485000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2272500000000,
      -9000000000000], [4545000000000, 18000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-4312500000000, 9000000000000], [6585000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-1710000000000], [2610000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded21_4 : ExcludedOn (model21.B 4 ++ [step21.q]) 9000000000000 (model21.caps 4)
    (model21.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded21_9 : ExcludedOn (model21.B 9 ++ [step21.q]) 9000000000000 (model21.caps 9)
    (model21.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked21 : StepValid model21 9000000000000 step21 0 1 400 := by
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
    (model22.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5226750000000], [34500000000]) (some (10, 1, 4))
      (some (10, 2, 4)) (.next ([3329250000000], [34500000000]) (some (10, 2, 4)) (some (10, 2, 4))
      (.next ([6386250000000], [382500000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
      ([6386250000000], [720000000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([6000000000000],
      [1106250000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next ([6011250000000], [1132500000000])
      (some (10, 2, 4)) (some (10, 2, 4)) (.next ([1511250000000], [386250000000]) (some (10, 2, 4))
      (some (10, 2, 4)) (.next ([2954250000000], [784500000000]) (some (10, 2, 4)) (some (10, 2, 4))
      (.next ([5625000000000], [1518750000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
      ([5250000000000], [1481250000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
      ([4863750000000], [1481250000000]) (some (10, 2, 4)) (some (10, 2, 4)) (.next
      ([4875000000000], [1893750000000]) (some (10, 2, 4)) (some (10, 3, 4)) (.next
      ([2954250000000], [1170750000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
      ([4488750000000], [1893750000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next
      ([1522500000000], [750000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([375000000000],
      [375000000000]) (some (10, 3, 4)) (some (10, 3, 4)) (.next ([3745500000000], [6379500000000])
      (some (10, 3, 4)) (some (10, 3, 4)) fan22Owner0Part1)))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6772500000000, 9000000000000], [2637000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([2272500000000, 9000000000000],
      [2272500000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4500000000000],
      [4909500000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([2227500000000, -9000000000000],
      [4909500000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [2272500000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2637000000000, 9000000000000],
      [9409500000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2272500000000, -9000000000000],
      [4545000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4909500000000],
      [9409500000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4909500000000, 0],
      [7137000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1, 0))
      (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000, 0], [1818000000000,
      -9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([4312500000000, -9000000000000],
      [2272500000000, 9000000000000]) (some (3, 0, 4)) (some (3, 0, 4)) (.next ([4500000000000],
      [4090500000000]) (some (3, 0, 4)) (some (3, 1, 4)) (.next ([2272500000000, 9000000000000],
      [2272500000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2005500000000],
      [2085000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2272500000000, 9000000000000],
      [4312500000000, -9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([2227500000000,
      -9000000000000], [6363000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([0], [2272500000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([-1818000000000, 9000000000000], [6318000000000, -9000000000000]) (some (0, 1, 4)) (some (0,
      1, 4)) (.next ([-2272500000000, -9000000000000], [6585000000000]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([-4090500000000], [8590500000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-2272500000000, -9000000000000], [4545000000000, 18000000000000]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([-2085000000000], [4090500000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-4312500000000, 9000000000000], [6585000000000]) (some (0, 1, 2)) (some (0, 4, 2)) (.next
      ([-6363000000000, -9000000000000], [8590500000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded22_4 : ExcludedOn (model22.B 4 ++ [step22.q]) 9000000000000 (model22.caps 4)
    (model22.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded22_9 : ExcludedOn (model22.B 9 ++ [step22.q]) 9000000000000 (model22.caps 9)
    (model22.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked22 : StepValid model22 9000000000000 step22 0 1 400 := by
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
    (model23.ord 0) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded23_2 : ExcludedOn (model23.B 2 ++ [step23.q]) 9000000000000 (model23.caps 2)
    (model23.ord 2) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 400 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 400 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [49500000000]) (some (7, 0, 3))
      (some (7, 1, 3)) fan23Owner4Part1)) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 400 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem excluded23_9 : ExcludedOn (model23.B 9 ++ [step23.q]) 9000000000000 (model23.caps 9)
    (model23.ord 9) 0 1 400 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      400 (by decide +kernel)
  decide +kernel

theorem checked23 : StepValid model23 9000000000000 step23 0 1 400 := by
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

end Sext252500255000
end ConwaySoifer.Simplified.Certificates
