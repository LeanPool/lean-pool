/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint140000150000
import Mathlib.Tactic.FinCases

/-!
# Sint 140000 150000 3

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
namespace Sint140000150000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner0Part0 : FanWitness := (.next ([-930000000000], [9045000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-630000000000], [6000000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-840000000000], [7875000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-705000000000], [6165000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-705000000000],
    [5955000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-795000000000], [6165000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-960000000000], [5670000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-1590000000000], [9375000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-1125000000000], [5835000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-1455000000000], [6375000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-1545000000000],
    [6375000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-1875000000000], [6045000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-330000000000], [750000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-330000000000], [660000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-540000000000], [915000000000]) (some (8, 4, 7)) (some (8, 5, 7)) (.next
    ([-540000000000], [750000000000]) (some (8, 5, 7)) (some (8, 5, 7)) (.next ([-6300000000000],
    [8415000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next ([-6300000000000], [8250000000000])
    (some (8, 5, 0)) (some (8, 5, 0)) (.next ([-5760000000000], [7500000000000]) (some (8, 5, 0))
    (some (8, 5, 0)) (.next ([-4920000000000], [5460000000000]) (some (8, 5, 0)) (some (8, 5, 8))
    (.next ([-1080000000000], [1170000000000]) (some (8, 5, 8)) (some (8, 5, 8)) (.next
    ([-5085000000000], [5460000000000]) (some (8, 5, 8)) (some (8, 5, 8)) (.next ([-5580000000000],
    [5790000000000]) (some (8, 5, 8)) (some (8, 5, 8)) (.next ([-5745000000000], [5790000000000])
    (some (8, 5, 8)) (some (8, 5, 8)) (.terminal (some (8, 5, 8)) (some (8, 5, 8)) (some (8, 5,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner0Part1 : FanWitness := (.next ([4710000000000], [960000000000]) (some (8, 2, 5)) (some
    (8, 2, 5)) (.next ([7785000000000], [1590000000000]) (some (8, 2, 5)) (some (8, 2, 6)) (.next
    ([4710000000000], [1125000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([4920000000000],
    [1455000000000]) (some (8, 2, 6)) (some (8, 2, 6)) (.next ([4830000000000], [1545000000000])
    (some (8, 2, 6)) (some (8, 2, 6)) (.next ([4170000000000], [1875000000000]) (some (8, 2, 6))
    (some (8, 2, 6)) (.next ([420000000000], [330000000000]) (some (8, 2, 6)) (some (8, 2, 6))
    (.next ([330000000000], [330000000000]) (some (8, 2, 6)) (some (8, 3, 6)) (.next
    ([375000000000], [540000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([210000000000],
    [540000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([2115000000000], [6300000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([1950000000000], [6300000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([1740000000000], [5760000000000]) (some (8, 3, 6)) (some (8, 3, 6))
    (.next ([540000000000], [4920000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([90000000000], [1080000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([375000000000],
    [5085000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([210000000000], [5580000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([45000000000], [5745000000000]) (some (8, 3, 6)) (some
    (8, 3, 6)) (.next ([0], [1080000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-510000000000], [8205000000000]) (some (8, 3, 6)) (some (8, 4, 7)) (.next ([-375000000000],
    [5295000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-90000000000], [1170000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-540000000000], [6000000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-840000000000], [8955000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    fan28Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner4Part0 : FanWitness := (.next ([3000000000000], [420000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([5415000000000, 0], [885000000000, 9000000000000]) (some (5, 1, 2)) (some (5,
    1, 2)) (.next ([5505000000000, 0], [1260000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1,
    2)) (.next ([4320000000000], [2625000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([1740000000000, -9000000000000], [1680000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1,
    5)) (.next ([1995000000000], [2625000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
    ([2085000000000], [3000000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([90000000000],
    [375000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([375000000000], [1860000000000]) (some
    (5, 1, 5)) (some (5, 1, 5)) (.next ([375000000000], [5040000000000]) (some (4, 1, 5)) (some (4,
    1, 5)) (.next ([375000000000], [7365000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0,
    0], [1260000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-885000000000,
    -9000000000000], [8625000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-420000000000], [3420000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-885000000000,
    -9000000000000], [6300000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-1260000000000, -9000000000000], [6765000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([-2625000000000], [6945000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-1680000000000, -9000000000000], [3420000000000, 0]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-2625000000000], [4620000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-3000000000000],
    [5085000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-375000000000], [465000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1860000000000], [2235000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-5040000000000], [5415000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-7365000000000], [7740000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some
    (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner0Part0 : FanWitness := (.next ([-705000000000], [5955000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-795000000000], [6165000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-960000000000], [5670000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-1125000000000], [5835000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-1455000000000],
    [6375000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-1545000000000], [6375000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-1875000000000], [6045000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-330000000000], [750000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-4665000000000], [10080000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-4830000000000], [10080000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-330000000000],
    [660000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-5040000000000], [9540000000000])
    (some (8, 4, 7)) (some (8, 5, 7)) (.next ([-540000000000], [915000000000]) (some (8, 5, 7))
    (some (8, 5, 7)) (.next ([-540000000000], [750000000000]) (some (8, 5, 7)) (some (8, 5, 7))
    (.next ([-4620000000000], [5955000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next
    ([-4710000000000], [6045000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next ([-4290000000000],
    [5205000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next ([-5370000000000], [6375000000000])
    (some (8, 5, 0)) (some (8, 5, 0)) (.next ([-4920000000000], [5460000000000]) (some (8, 5, 0))
    (some (8, 5, 0)) (.next ([-1080000000000], [1170000000000]) (some (8, 5, 0)) (some (8, 5, 0))
    (.next ([-5085000000000], [5460000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next
    ([-4620000000000], [4875000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next ([-5580000000000],
    [5790000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next ([-5745000000000], [5790000000000])
    (some (8, 5, 0)) (some (8, 5, 0)) (.terminal (some (8, 5, 0)) (some (8, 5, 0)) (some (8, 5,
    0)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan29Owner0Part1 : FanWitness := (.next ([4170000000000], [1875000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([420000000000], [330000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([5415000000000], [4665000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([5250000000000], [4830000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([330000000000],
    [330000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([4500000000000], [5040000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([375000000000], [540000000000]) (some (0, 8, 6)) (some
    (8, 8, 6)) (.next ([210000000000], [540000000000]) (some (8, 8, 6)) (some (8, 8, 6)) (.next
    ([1335000000000], [4620000000000]) (some (8, 8, 6)) (some (8, 8, 6)) (.next ([1335000000000],
    [4710000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([915000000000], [4290000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([1005000000000], [5370000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([540000000000], [4920000000000]) (some (8, 3, 6)) (some (8, 3, 6))
    (.next ([90000000000], [1080000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([375000000000], [5085000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([255000000000],
    [4620000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([210000000000], [5580000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([45000000000], [5745000000000]) (some (8, 3, 6)) (some
    (8, 3, 6)) (.next ([0], [1080000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-375000000000], [5295000000000]) (some (8, 3, 6)) (some (8, 4, 7)) (.next ([-90000000000],
    [1170000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-540000000000], [6000000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-630000000000], [6000000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-705000000000], [6165000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    fan29Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner0Part0 : FanWitness := (.next ([-705000000000], [5955000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-795000000000], [6165000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-960000000000], [5670000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-1125000000000], [5835000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-1455000000000],
    [6375000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-1545000000000], [6375000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-1875000000000], [6045000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-330000000000], [750000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    (.next ([-4620000000000], [10035000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next
    ([-4785000000000], [10035000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-330000000000],
    [660000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-4995000000000], [9495000000000])
    (some (8, 4, 7)) (some (8, 5, 7)) (.next ([-540000000000], [915000000000]) (some (8, 5, 7))
    (some (8, 5, 7)) (.next ([-540000000000], [750000000000]) (some (8, 5, 7)) (some (8, 5, 7))
    (.next ([-4575000000000], [5955000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next
    ([-4665000000000], [6045000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next ([-4245000000000],
    [5205000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next ([-5325000000000], [6375000000000])
    (some (8, 5, 0)) (some (8, 5, 0)) (.next ([-4920000000000], [5460000000000]) (some (8, 5, 0))
    (some (8, 5, 0)) (.next ([-1080000000000], [1170000000000]) (some (8, 5, 0)) (some (8, 5, 0))
    (.next ([-5085000000000], [5460000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next
    ([-4575000000000], [4875000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next ([-5580000000000],
    [5790000000000]) (some (8, 5, 0)) (some (8, 5, 0)) (.next ([-5745000000000], [5790000000000])
    (some (8, 5, 0)) (some (8, 5, 0)) (.terminal (some (8, 5, 0)) (some (8, 5, 0)) (some (8, 5,
    0)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan30Owner0Part1 : FanWitness := (.next ([4170000000000], [1875000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([420000000000], [330000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([5415000000000], [4620000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([5250000000000], [4785000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([330000000000],
    [330000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([4500000000000], [4995000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([375000000000], [540000000000]) (some (0, 8, 6)) (some
    (8, 8, 6)) (.next ([210000000000], [540000000000]) (some (8, 8, 6)) (some (8, 8, 6)) (.next
    ([1380000000000], [4575000000000]) (some (8, 8, 6)) (some (8, 8, 6)) (.next ([1380000000000],
    [4665000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([960000000000], [4245000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([1050000000000], [5325000000000]) (some (8, 3, 6))
    (some (8, 3, 6)) (.next ([540000000000], [4920000000000]) (some (8, 3, 6)) (some (8, 3, 6))
    (.next ([90000000000], [1080000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([375000000000], [5085000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([300000000000],
    [4575000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next ([210000000000], [5580000000000])
    (some (8, 3, 6)) (some (8, 3, 6)) (.next ([45000000000], [5745000000000]) (some (8, 3, 6)) (some
    (8, 3, 6)) (.next ([0], [1080000000000]) (some (8, 3, 6)) (some (8, 3, 6)) (.next
    ([-375000000000], [5295000000000]) (some (8, 3, 6)) (some (8, 4, 7)) (.next ([-90000000000],
    [1170000000000]) (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-540000000000], [6000000000000])
    (some (8, 4, 7)) (some (8, 4, 7)) (.next ([-630000000000], [6000000000000]) (some (8, 4, 7))
    (some (8, 4, 7)) (.next ([-705000000000], [6165000000000]) (some (8, 4, 7)) (some (8, 4, 7))
    fan30Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner4Part0 : FanWitness := (.next ([2115000000000, -9000000000000], [1845000000000,
    9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2115000000000, -9000000000000],
    [1890000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1455000000000],
    [3000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1410000000000], [3000000000000])
    (some (5, 6, 3)) (some (5, 6, 3)) (.next ([1545000000000], [3375000000000]) (some (5, 6, 3))
    (some (5, 6, 4)) (.next ([1500000000000], [3375000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([90000000000], [375000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([375000000000],
    [5040000000000]) (some (5, 6, 4)) (some (5, 6, 5)) (.next ([0, 0], [1260000000000,
    9000000000000]) (some (5, 6, 5)) (some (5, 6, 5)) (.next ([-510000000000], [4515000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-510000000000], [4470000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-885000000000, -9000000000000], [6300000000000, 9000000000000]) (some
    (0, 6, 5)) (some (0, 6, 5)) (.next ([-630000000000], [4005000000000]) (some (0, 6, 5)) (some (0,
    6, 5)) (.next ([-1260000000000, -9000000000000], [6765000000000, 9000000000000]) (some (0, 6,
    5)) (some (0, 6, 5)) (.next ([-3510000000000], [8925000000000]) (some (0, 6, 5)) (some (0, 6,
    5)) (.next ([-3885000000000], [9390000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-1845000000000, -9000000000000], [3960000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-1890000000000, -9000000000000], [4005000000000, 0]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-3000000000000], [4455000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3000000000000],
    [4410000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3375000000000], [4920000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3375000000000], [4875000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.next ([-375000000000], [465000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-5040000000000], [5415000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.terminal (some
    (0, 6, 5)) (some (0, 6, 5)) (some (0, 6, 5)))))))))))))))))))))))))))

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6510000000000, 9000000000000], [2700000000000,
      -9000000000000]) (some (3, 3, 1)) none (.next ([5250000000000], [3960000000000]) none none
      (.next ([1260000000000, 9000000000000], [1260000000000, 9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-2700000000000, 9000000000000], [9210000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-3960000000000], [9210000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-1260000000000, -9000000000000], [2520000000000, 18000000000000]) (some (3, 1, 0)) (some (3,
      1, 0)) (.terminal (some (3, 1, 0)) (some (3, 1, 3)) (some (3, 1, 3))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7740000000000, -9000000000000], [1260000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2700000000000, -9000000000000],
      [1050000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3990000000000,
      -9000000000000], [3960000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([210000000000],
      [3750000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1260000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-1050000000000,
      -9000000000000], [3750000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3960000000000,
      0], [7950000000000, -9000000000000]) (some (0, 1, 2)) (some (3, 1, 2)) (.next
      ([-3750000000000], [3960000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6732000000000], [1260000000000, 9000000000000])
      (some (3, 0, 5)) (some (4, 0, 5)) (.next ([6357000000000], [1440000000000]) (some (4, 0, 5))
      (some (4, 0, 5)) (.next ([6102000000000], [1530000000000]) (some (4, 0, 5)) (some (4, 0, 5))
      (.next ([1065000000000], [375000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
      ([900000000000], [630000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1692000000000],
      [2058000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([3750000000000], [5040000000000])
      (some (4, 0, 3)) (some (4, 0, 3)) (.next ([90000000000], [165000000000]) (some (4, 0, 3))
      (some (4, 0, 3)) (.next ([2490000000000, -9000000000000], [6300000000000, 9000000000000])
      (some (4, 1, 3)) (some (4, 2, 3)) (.next ([2220000000000], [5940000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([0], [1260000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 5,
      3)) (.next ([-1260000000000, -9000000000000], [7992000000000, 9000000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-1440000000000], [7797000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-1530000000000], [7632000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-375000000000], [1440000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-630000000000],
      [1530000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2058000000000], [3750000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5040000000000], [8790000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([-165000000000], [255000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-6300000000000, -9000000000000], [8790000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-5940000000000], [8160000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some
      (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3))))))))))))))))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded24_1
    · exact excluded24_2
    · exact excluded24_3
    · exact excluded24_4
    · exact excluded24_5
    · exact excluded24_6
    · exact excluded24_7
    · exact excluded24_8
    · exact excluded24_9
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1260000000000, 9000000000000], [1260000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2295000000000], [5865000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2295000000000], [7125000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1035000000000, -9000000000000], [8385000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-1260000000000, -9000000000000],
      [2520000000000, 18000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-5865000000000,
      9000000000000], [8160000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-7125000000000], [9420000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8385000000000,
      -9000000000000], [9420000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8415000000000], [165000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([2250000000000], [420000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([6705000000000], [1875000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([5445000000000, -9000000000000], [1875000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([1290000000000], [960000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([990000000000,
      -9000000000000], [1680000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([795000000000], [6330000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [1710000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-165000000000], [8580000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-420000000000], [2670000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1875000000000], [8580000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1875000000000, 0], [7320000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2,
      4)) (.next ([-960000000000], [2250000000000]) (some (0, 2, 4)) (some (0, 4, 4)) (.next
      ([-1680000000000, -9000000000000], [2670000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next
      ([-6330000000000], [7125000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.terminal (some (0, 4,
      3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1260000000000, 9000000000000], [1260000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2265000000000], [5850000000000,
      -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([2265000000000], [7110000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1005000000000, -9000000000000], [8370000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [1260000000000,
      9000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-1260000000000, -9000000000000],
      [2520000000000, 18000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next ([-5850000000000,
      9000000000000], [8115000000000, -9000000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-7110000000000], [9375000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-8370000000000,
      -9000000000000], [9375000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0)) (.terminal (some (3, 1,
      0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_2 : ExcludedOn (model26.B 2 ++ [step26.q]) 9000000000000 (model26.caps 2)
    (model26.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8445000000000], [180000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([2250000000000], [420000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([6735000000000], [1890000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([5475000000000, -9000000000000], [1890000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([1290000000000], [960000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([990000000000,
      -9000000000000], [1680000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([780000000000], [6375000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0],
      [1710000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-180000000000], [8625000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-420000000000], [2670000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-1890000000000], [8625000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1890000000000, 0], [7365000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2,
      4)) (.next ([-960000000000], [2250000000000]) (some (0, 2, 4)) (some (0, 4, 4)) (.next
      ([-1680000000000, -9000000000000], [2670000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next
      ([-6375000000000], [7155000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.terminal (some (0, 4,
      3)) (some (0, 4, 3)) (some (0, 4, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact excluded26_4
    · exact excluded26_5
    · exact (hj rfl).elim
    · exact excluded26_7
    · exact excluded26_8
    · exact excluded26_9
theorem next26 : model26.insert step26 = model27 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded27_0 : ExcludedOn (model27.B 0 ++ [step27.q]) 9000000000000 (model27.caps 0)
    (model27.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000], [420000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([5415000000000, 0], [885000000000, 9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([5505000000000, 0], [1260000000000, 9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([5640000000000], [3420000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([1740000000000, -9000000000000], [1680000000000, 9000000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([1995000000000], [2625000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([2085000000000], [3000000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next
      ([90000000000], [375000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1020000000000],
      [5415000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next ([555000000000], [5505000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([375000000000], [5040000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([0, 0], [1260000000000, 9000000000000]) (some (5, 1, 4)) (some (5, 1,
      4)) (.next ([-420000000000], [3420000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next
      ([-885000000000, -9000000000000], [6300000000000, 9000000000000]) (some (5, 1, 4)) (some (5,
      1, 4)) (.next ([-1260000000000, -9000000000000], [6765000000000, 9000000000000]) (some (5, 1,
      4)) (some (5, 1, 4)) (.next ([-3420000000000], [9060000000000]) (some (5, 1, 4)) (some (5, 1,
      4)) (.next ([-1680000000000, -9000000000000], [3420000000000, 0]) (some (5, 1, 4)) (some (5,
      1, 4)) (.next ([-2625000000000], [4620000000000]) (some (5, 1, 4)) (some (5, 2, 4)) (.next
      ([-3000000000000], [5085000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-375000000000],
      [465000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-5415000000000], [6435000000000])
      (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-5505000000000], [6060000000000]) (some (5, 2, 4))
      (some (5, 2, 4)) (.next ([-5040000000000], [5415000000000]) (some (5, 2, 4)) (some (5, 2, 5))
      (.terminal (some (5, 2, 5)) (some (0, 2, 5)) (some (5, 2, 5))))))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
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
    · exact excluded27_4
    · exact excluded27_5
    · exact excluded27_6
    · exact excluded27_7
    · exact (hj rfl).elim
    · exact excluded27_9
theorem next27 : model27.insert step27 = model28 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded28_0 : ExcludedOn (model28.B 0 ++ [step28.q]) 9000000000000 (model28.caps 0)
    (model28.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7695000000000], [510000000000]) (some (8, 8, 5))
      (some (8, 8, 5)) (.next ([4920000000000], [375000000000]) (some (8, 2, 5)) (some (8, 2, 5))
      (.next ([1080000000000], [90000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
      ([5460000000000], [540000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([8115000000000],
      [840000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([8115000000000], [930000000000])
      (some (8, 2, 5)) (some (8, 2, 5)) (.next ([5370000000000], [630000000000]) (some (8, 2, 5))
      (some (8, 2, 5)) (.next ([7035000000000], [840000000000]) (some (8, 2, 5)) (some (8, 2, 5))
      (.next ([5460000000000], [705000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next
      ([5250000000000], [705000000000]) (some (8, 2, 5)) (some (8, 2, 5)) (.next ([5370000000000],
      [795000000000]) (some (8, 2, 5)) (some (8, 2, 5)) fan28Owner0Part1)))))))))))) (den :=
      9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([7740000000000, 0], [885000000000,
      9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan28Owner4Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_7 : ExcludedOn (model28.B 7 ++ [step28.q]) 9000000000000 (model28.caps 7)
    (model28.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_8 : ExcludedOn (model28.B 8 ++ [step28.q]) 9000000000000 (model28.caps 8)
    (model28.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6435000000000], [1305000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([1635000000000], [1008000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([3792000000000], [2940000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1635000000000], [7740000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [2940000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1305000000000], [7740000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1008000000000], [2643000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([-2940000000000], [6732000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-7740000000000], [9375000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem excluded29_0 : ExcludedOn (model29.B 0 ++ [step29.q]) 9000000000000 (model29.caps 0)
    (model29.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4920000000000], [375000000000]) (some (0, 8, 5))
      (some (0, 8, 5)) (.next ([1080000000000], [90000000000]) (some (0, 8, 5)) (some (0, 8, 5))
      (.next ([5460000000000], [540000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next
      ([5370000000000], [630000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([5460000000000],
      [705000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([5250000000000], [705000000000])
      (some (0, 8, 5)) (some (0, 8, 5)) (.next ([5370000000000], [795000000000]) (some (0, 8, 5))
      (some (0, 8, 5)) (.next ([4710000000000], [960000000000]) (some (0, 8, 5)) (some (0, 8, 5))
      (.next ([4710000000000], [1125000000000]) (some (0, 8, 5)) (some (0, 8, 6)) (.next
      ([4920000000000], [1455000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([4830000000000],
      [1545000000000]) (some (0, 8, 6)) (some (0, 8, 6)) fan29Owner0Part1)))))))))))) (den :=
      9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2250000000000], [420000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([1290000000000], [960000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3960000000000], [3915000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([3960000000000], [5625000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([990000000000,
      -9000000000000], [1680000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([2700000000000, -9000000000000], [6885000000000, 9000000000000]) (some (4, 1, 2)) (some (4,
      1, 3)) (.next ([1710000000000], [5205000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([0], [1710000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next ([-420000000000],
      [2670000000000]) (some (4, 1, 4)) (some (4, 2, 4)) (.next ([-960000000000], [2250000000000])
      (some (4, 2, 4)) (some (4, 2, 4)) (.next ([-3915000000000], [7875000000000]) (some (4, 2, 4))
      (some (4, 2, 4)) (.next ([-5625000000000], [9585000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1680000000000, -9000000000000], [2670000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-6885000000000, -9000000000000], [9585000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-5205000000000], [6915000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4920000000000], [375000000000]) (some (0, 8, 5))
      (some (0, 8, 5)) (.next ([1080000000000], [90000000000]) (some (0, 8, 5)) (some (0, 8, 5))
      (.next ([5460000000000], [540000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next
      ([5370000000000], [630000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([5460000000000],
      [705000000000]) (some (0, 8, 5)) (some (0, 8, 5)) (.next ([5250000000000], [705000000000])
      (some (0, 8, 5)) (some (0, 8, 5)) (.next ([5370000000000], [795000000000]) (some (0, 8, 5))
      (some (0, 8, 5)) (.next ([4710000000000], [960000000000]) (some (0, 8, 5)) (some (0, 8, 5))
      (.next ([4710000000000], [1125000000000]) (some (0, 8, 5)) (some (0, 8, 6)) (.next
      ([4920000000000], [1455000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([4830000000000],
      [1545000000000]) (some (0, 8, 6)) (some (0, 8, 6)) fan30Owner0Part1)))))))))))) (den :=
      9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2250000000000], [420000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([1290000000000], [960000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4005000000000], [3915000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([4005000000000], [5625000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([990000000000,
      -9000000000000], [1680000000000, 9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([2745000000000, -9000000000000], [6885000000000, 9000000000000]) (some (4, 1, 2)) (some (4,
      1, 3)) (.next ([1755000000000], [5205000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([0], [1710000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next ([-420000000000],
      [2670000000000]) (some (4, 1, 4)) (some (4, 2, 4)) (.next ([-960000000000], [2250000000000])
      (some (4, 2, 4)) (some (4, 2, 4)) (.next ([-3915000000000], [7920000000000]) (some (4, 2, 4))
      (some (4, 2, 4)) (.next ([-5625000000000], [9630000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1680000000000, -9000000000000], [2670000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-6885000000000, -9000000000000], [9630000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-5205000000000], [6960000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some
      (0, 2, 4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded31_0 : ExcludedOn (model31.B 0 ++ [step31.q]) 9000000000000 (model31.caps 0)
    (model31.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4005000000000], [510000000000]) (some (5, 0, 6))
      (some (5, 6, 6)) (.next ([3960000000000], [510000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      (.next ([5415000000000, 0], [885000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      (.next ([3375000000000], [630000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([5505000000000, 0], [1260000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next
      ([5415000000000], [3510000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([5505000000000],
      [3885000000000]) (some (5, 6, 3)) (some (5, 6, 3)) fan31Owner4Part0)))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_6 : ExcludedOn (model31.B 6 ++ [step31.q]) 9000000000000 (model31.caps 6)
    (model31.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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

end Sint140000150000
end ConwaySoifer.Simplified.Certificates
